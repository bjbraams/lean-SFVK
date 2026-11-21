/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.Spheres.Addition
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.LinearAlgebra.DFinsupp
import TauCeti.LinearAlgebra.Dimension.DirectSum

/-!
# Branching of spherical harmonics from `ℝ^{m+1}` to `ℝᵐ`

For `h` harmonic of degree `k` on `ℝᵐ`, the polynomial
`|x|^{l-k} ω_{m+1+2k,l-k}(x_{m+1}/|x|) h(x₁, …, x_m)` is harmonic of degree `l` on `ℝ^{m+1}`; the
harmonics of degree `l` on `ℝ^{m+1}` are the direct sum of these images over `k ≤ l`, and the
branching map multiplies `L²` norms by an explicit constant. Iterating gives the
Gel'fand–Tsetlin basis of Vilenkin–Klimyk. The dimensions are obtained from Tau Ceti's
Fischer decomposition and the Pascal recurrence for multiset coefficients. The Laplacian
comparison uses Tau Ceti's product rule with the squared radius. The highest power of the last
coordinate in each branch gives independence. Tau Ceti's dimension formula for a sum of
independent subspaces then gives spanning.

Sources: Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2, §9.3.1
(1)–(5), pp. 44–46 (the orthonormal basis of `L²(S^{n-1})` built from Gegenbauer polynomials);
Wawrzyńczyk, *Group Representations and Special Functions*, (9.2.9), p. 330.
-/

public noncomputable section

open MeasureTheory

namespace SFVK.Spheres

namespace BranchingLaplacian

open MvPolynomial

private theorem pderiv_last_rename_castSucc {m : ℕ} (h : MvPolynomial (Fin m) ℝ) :
    pderiv (Fin.last m) (rename Fin.castSucc h) = 0 := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [pderiv_X_of_ne (Fin.castSucc_ne_last i), hp]

private theorem laplacian_rename_castSucc {m : ℕ} (h : MvPolynomial (Fin m) ℝ) :
    laplacian (rename Fin.castSucc h) = rename Fin.castSucc (laplacian h) := by
  simp only [laplacian_apply, map_sum, Fin.sum_univ_castSucc,
    pderiv_rename (Fin.castSucc_injective m), pderiv_last_rename_castSucc, map_zero, add_zero]

private theorem laplacian_X_pow_mul {σ : Type*} [Fintype σ] [DecidableEq σ]
    (i : σ) {h : MvPolynomial σ ℝ} (hh : laplacian h = 0) (hi : pderiv i h = 0) (j : ℕ) :
    laplacian (X i ^ j * h) = (j : MvPolynomial σ ℝ) *
      ((j - 1 : ℕ) : MvPolynomial σ ℝ) * X i ^ (j - 2) * h := by
  have hderiv (x : σ) : pderiv x (X i ^ j : MvPolynomial σ ℝ) =
      if x = i then (j : MvPolynomial σ ℝ) * X i ^ (j - 1) else 0 := by
    rw [pderiv_pow]
    by_cases hx : x = i
    · simp [hx]
    · rw [pderiv_X_of_ne (Ne.symm hx), mul_zero, ite_eq_right hx]
  rw [laplacian_mul, hh, mul_zero, add_zero]
  have cross : ∑ x, pderiv x (X i ^ j) * pderiv x h = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x = i
    · simp [hx, hi]
    · rw [hderiv, ite_eq_right hx, zero_mul]
  rw [cross, mul_zero, add_zero, laplacian_apply]
  simp_rw [hderiv]
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl, pderiv_mul, (pderiv i).map_natCast, zero_mul, zero_add, pderiv_pow,
      pderiv_X_self, mul_one, Nat.sub_sub]
    ring
  · intro x _ hx
    rw [ite_eq_right hx, map_zero]
  · simp

private theorem laplacian_normSq_pow_mul_general {σ : Type*} [Fintype σ]
    {h : MvPolynomial σ ℝ} {d : ℕ} (hh : h.IsHomogeneous d) (a : ℕ) :
    laplacian (normSq σ ℝ ^ a * h) = normSq σ ℝ ^ a * laplacian h +
      (2 * a * (2 * d + Fintype.card σ + 2 * (a - 1))) • (normSq σ ℝ ^ (a - 1) * h) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hdeg : (normSq σ ℝ ^ a * h).IsHomogeneous (2 * a + d) :=
      ((isHomogeneous_normSq σ ℝ).pow a).mul hh
    rw [pow_succ', mul_assoc, laplacian_normSq_mul hdeg, ih]
    cases a with
    | zero =>
      simp only [pow_zero, one_mul, Nat.mul_zero, add_zero,
        Nat.zero_add, Nat.mul_one, Nat.sub_self, nsmul_eq_mul, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat]
      ring
    | succ a =>
      simp only [mul_add, nsmul_eq_mul, Nat.succ_sub_one, Nat.cast_add,
        Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      rw [pow_succ' (normSq σ ℝ) a]
      ring

private theorem laplacian_radial_mul_coordinate_pow {σ : Type*} [Fintype σ] [DecidableEq σ]
    (i : σ) {h : MvPolynomial σ ℝ} {k : ℕ} (hh : h.IsHomogeneous k)
    (hl : laplacian h = 0) (hi : pderiv i h = 0) (a j : ℕ) :
    laplacian (normSq σ ℝ ^ a * X i ^ j * h) =
      (((2 * a * (2 * j + (Fintype.card σ + 2 * k) + 2 * (a - 1)) : ℕ) :
          MvPolynomial σ ℝ) * normSq σ ℝ ^ (a - 1) * X i ^ j +
        (j : MvPolynomial σ ℝ) * ((j - 1 : ℕ) : MvPolynomial σ ℝ) *
          normSq σ ℝ ^ a * X i ^ (j - 2)) * h := by
  have hdeg := ((isHomogeneous_X ℝ i).pow j).mul hh
  simp only [one_mul] at hdeg
  rw [mul_assoc, laplacian_normSq_pow_mul_general hdeg, laplacian_X_pow_mul i hl hi]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

private theorem linearForm_single {n : ℕ} (i : Fin n) :
    linearForm (EuclideanSpace.single i (1 : ℝ)) = X i := by
  classical
  rw [linearForm_def, Finset.sum_eq_single i]
  · simp
  · intro j _ h
    simp [EuclideanSpace.single, h]
  · simp

private theorem laplacian_C_mul {σ : Type*} [Fintype σ] (c : ℝ) (p : MvPolynomial σ ℝ) :
    laplacian (C c * p) = C c * laplacian p := by
  simp only [C_mul', map_smul]

end BranchingLaplacian

open BranchingLaplacian MvPolynomial in
set_option maxHeartbeats 1000000 in
/-- **Branching harmonics are harmonic.** For `m ≥ 1`, `k ≤ l` and `h ∈ H_k(ℝᵐ)`,
`branchHarmonic m l k h ∈ H_l(ℝ^{m+1})`. -/
theorem branchHarmonic_mem_harmonicSubmodule {m l k : ℕ} (hm : 1 ≤ m) (hkl : k ≤ l)
    {h : MvPolynomial (Fin m) ℝ} (hh : h ∈ MvPolynomial.harmonicSubmodule (Fin m) ℝ k) :
    branchHarmonic m l k h ∈ MvPolynomial.harmonicSubmodule (Fin (m + 1)) ℝ l := by
  let d := l - k
  let N := m + 1 + 2 * k
  let P := zonalPolynomial N d
  let H := rename (R := ℝ) Fin.castSucc h
  let a : Fin (m + 1) := Fin.last m
  let b : Fin N := Fin.castAdd (2 * k) a
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hhdeg : H.IsHomogeneous k := (mem_harmonicSubmodule_iff.mp hh).1.rename_isHomogeneous
  have hhLap : laplacian H = 0 := by
    rw [show H = _ from rfl, laplacian_rename_castSucc, (mem_harmonicSubmodule_iff.mp hh).2,
      map_zero]
  have hhp : pderiv a H = 0 := pderiv_last_rename_castSucc h
  rw [mem_harmonicSubmodule_iff, branchHarmonic_apply]
  change (branchFactor m l k * H).IsHomogeneous l ∧ laplacian (branchFactor m l k * H) = 0
  constructor
  · have hfactor : (branchFactor m l k).IsHomogeneous d := by
      rw [branchFactor_def]
      refine IsHomogeneous.sum _ _ _ fun j hj => ?_
      split_ifs with hpar
      · have hdegree : 0 + 1 * j + 2 * ((d - j) / 2) = d := by
          obtain ⟨r, hr⟩ := hpar
          have := Finset.mem_range.mp hj
          omega
        have he := ((isHomogeneous_C (Fin (m + 1)) (P.coeff j)).mul
          ((isHomogeneous_X ℝ a).pow j)).mul
            ((isHomogeneous_normSq (Fin (m + 1)) ℝ).pow ((d - j) / 2))
        rw [hdegree] at he
        exact he
      · exact isHomogeneous_zero _ _ _
    have he := hfactor.mul hhdeg
    rwa [show d + k = l from Nat.sub_add_cancel hkl] at he
  · let f : Fin N → MvPolynomial (Fin (m + 1)) ℝ := Fin.addCases X fun _ => 0
    let F : MvPolynomial (Fin N) ℝ →ₐ[ℝ] MvPolynomial (Fin (m + 1)) ℝ :=
      MvPolynomial.aeval f
    have hF (i : Fin (m + 1)) : F (X (Fin.castAdd (2 * k) i)) = X i := by
      simp only [F, aeval_X, f, Fin.addCases_left]
    have hFzero (i : Fin (2 * k)) : F (X (Fin.natAdd (m + 1) i)) = 0 := by
      simp only [F, aeval_X, f, Fin.addCases_right]
    have hFnorm : F (normSq (Fin N) ℝ) = normSq (Fin (m + 1)) ℝ := by
      rw [normSq_def, map_sum, Fin.sum_univ_add, normSq_def]
      simp [hF, hFzero]
    let e : EuclideanSpace ℝ (Fin N) := EuclideanSpace.single b 1
    have he : ‖e‖ = 1 := by simp [e]
    have heLap := (mem_harmonicSubmodule_iff.mp
      (zonalHarmonic_mem_harmonicSubmodule hN d he)).2
    have hOne : laplacian (1 : MvPolynomial (Fin N) ℝ) = 0 := by
      rw [← map_one (C : ℝ →+* MvPolynomial (Fin N) ℝ), laplacian_C]
    have hFC (c : ℝ) : F (C c) = C c := by
      exact aeval_C f c
    have hhCompare : laplacian (branchFactor m l k * H) =
        F (laplacian (zonalHarmonic N d e)) * H := by
      rw [branchFactor_def, zonalHarmonic_def, linearForm_single]
      simp only [d, N]
      simp only [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hpar
      · have hleft (c : ℝ) (r : ℕ) :
            laplacian (C c * X a ^ j * normSq (Fin (m + 1)) ℝ ^ r * H) =
              C c * laplacian (normSq (Fin (m + 1)) ℝ ^ r * X a ^ j * H) := by
          rw [show C c * X a ^ j * normSq (Fin (m + 1)) ℝ ^ r * H =
            C c * (normSq (Fin (m + 1)) ℝ ^ r * X a ^ j * H) by ring, laplacian_C_mul]
        have hright (c : ℝ) (r : ℕ) :
            laplacian (C c * X b ^ j * normSq (Fin (m + 1 + 2 * k)) ℝ ^ r) =
              C c * laplacian (normSq (Fin (m + 1 + 2 * k)) ℝ ^ r * X b ^ j * 1) := by
          rw [show C c * X b ^ j * normSq (Fin (m + 1 + 2 * k)) ℝ ^ r =
            C c * (normSq (Fin (m + 1 + 2 * k)) ℝ ^ r * X b ^ j * 1) by ring, laplacian_C_mul]
        rw [hleft, hright, laplacian_radial_mul_coordinate_pow a hhdeg hhLap hhp,
          laplacian_radial_mul_coordinate_pow b (isHomogeneous_one _ _) hOne (by simp)]
        simp only [Fintype.card_fin, mul_zero, add_zero, map_mul, hFC,
          map_add, map_pow, map_natCast, mul_one, b, hF, hFnorm, N]
        ring
      · simp
    rw [hhCompare, heLap, map_zero, zero_mul]

namespace BranchingCoordinates

open Polynomial

private noncomputable def lastVariableEquiv (m : ℕ) :
    MvPolynomial (Fin (m + 1)) ℝ ≃ₐ[ℝ] (MvPolynomial (Fin m) ℝ)[X] :=
  (MvPolynomial.renameEquiv ℝ finSuccEquivLast).trans (MvPolynomial.optionEquivLeft ℝ (Fin m))

private theorem lastVariableEquiv_rename (m : ℕ) (h : MvPolynomial (Fin m) ℝ) :
    lastVariableEquiv m (MvPolynomial.rename Fin.castSucc h) = C h := by
  induction h using MvPolynomial.induction_on with
  | C a =>
    simp [lastVariableEquiv, MvPolynomial.optionEquivLeft_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, MvPolynomial.rename_X]
    have hi : lastVariableEquiv m (MvPolynomial.X (Fin.castSucc i)) = C (MvPolynomial.X i) := by
      simp [lastVariableEquiv, finSuccEquivLast_castSucc]
    rw [hi, map_mul]

private theorem lastVariableEquiv_normSq (m : ℕ) :
    lastVariableEquiv m (MvPolynomial.normSq (Fin (m + 1)) ℝ) =
      X ^ 2 + C (MvPolynomial.normSq (Fin m) ℝ) := by
  rw [MvPolynomial.normSq_def, MvPolynomial.normSq_def, map_sum, map_sum, Fin.sum_univ_castSucc]
  simp [lastVariableEquiv, finSuccEquivLast_castSucc, finSuccEquivLast_last, add_comm]

private theorem isMonicOfDegree_lastVariableEquiv_branchFactor {m : ℕ} (hm : 1 ≤ m) (l k : ℕ) :
    IsMonicOfDegree (lastVariableEquiv m (branchFactor m l k)) (l - k) := by
  let R := MvPolynomial (Fin m) ℝ
  let d := l - k
  let n := m + 1 + 2 * k
  let p := zonalPolynomial n d
  let B : R[X] := X ^ 2 + C (MvPolynomial.normSq (Fin m) ℝ)
  have hB : IsMonicOfDegree B 2 :=
    (isMonicOfDegree_X_pow R 2).add_right (by simp)
  have hC (c : ℝ) : lastVariableEquiv m (MvPolynomial.C c) = C (MvPolynomial.C c) := by
    simp [lastVariableEquiv, MvPolynomial.optionEquivLeft_C]
  have hX : lastVariableEquiv m (MvPolynomial.X (Fin.last m)) = X := by
    simp [lastVariableEquiv, finSuccEquivLast_last]
  rw [branchFactor_def]
  change IsMonicOfDegree
    (lastVariableEquiv m (∑ j ∈ Finset.range (d + 1), if Even (d - j) then
      MvPolynomial.C (p.coeff j) * MvPolynomial.X (Fin.last m) ^ j *
        MvPolynomial.normSq (Fin (m + 1)) ℝ ^ ((d - j) / 2) else 0)) d
  simp only [map_sum, apply_ite (lastVariableEquiv m), map_zero, map_mul, map_pow, hC, hX,
    lastVariableEquiv_normSq]
  rw [isMonicOfDegree_iff]
  have hstep (j : ℕ) (hj : j ∈ Finset.range (d + 1)) (hpar : Even (d - j)) :
      IsMonicOfDegree ((X : R[X]) ^ j * B ^ ((d - j) / 2)) d := by
    have he : j + 2 * ((d - j) / 2) = d := by
      rcases hpar with ⟨a, ha⟩
      have := Finset.mem_range.mp hj
      omega
    have hprod := (isMonicOfDegree_X_pow R j).mul (hB.pow ((d - j) / 2))
    rwa [he] at hprod
  constructor
  · refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    split_ifs with hpar
    · rw [mul_assoc]
      exact (natDegree_C_mul_le _ _).trans (hstep j hj hpar).natDegree_eq.le
    · simp
  · rw [← lcoeff_apply, map_sum]
    simp only [lcoeff_apply]
    have hs : ∑ j ∈ Finset.range (d + 1), p.coeff j = 1 := by
      conv_rhs => rw [← zonalPolynomial_eval_one n d]
      have he := congrArg (Polynomial.eval 1) p.as_sum_range_C_mul_X_pow
      simpa only [show p.natDegree = d from natDegree_zonalPolynomial (by dsimp [n]; omega) d,
        Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, one_pow, mul_one] using he.symm
    rw [← map_one (MvPolynomial.C : ℝ →+* R), ← hs, map_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    split_ifs with hpar
    · rw [mul_assoc, coeff_C_mul, (isMonicOfDegree_iff _ _).mp (hstep j hj hpar) |>.2, mul_one]
    · rw [coeff_zero, coeff_zonalPolynomial_eq_zero_of_not_even
        (by dsimp [n]; omega) (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hpar, map_zero]

private theorem coeff_lastVariableEquiv_branchHarmonic {m : ℕ} (hm : 1 ≤ m) (l k : ℕ)
    (h : MvPolynomial (Fin m) ℝ) :
    (lastVariableEquiv m (branchHarmonic m l k h)).coeff (l - k) = h := by
  rw [branchHarmonic_apply, map_mul, lastVariableEquiv_rename, coeff_mul_C,
    (isMonicOfDegree_iff _ _).mp (isMonicOfDegree_lastVariableEquiv_branchFactor hm l k) |>.2,
    one_mul]

private theorem coeff_lastVariableEquiv_branchHarmonic_eq_zero {m : ℕ} (hm : 1 ≤ m) (l k : ℕ)
    (h : MvPolynomial (Fin m) ℝ) {j : ℕ} (hj : l - k < j) :
    (lastVariableEquiv m (branchHarmonic m l k h)).coeff j = 0 := by
  rw [branchHarmonic_apply, map_mul, lastVariableEquiv_rename, coeff_mul_C,
    coeff_eq_zero_of_natDegree_lt, zero_mul]
  rw [(isMonicOfDegree_lastVariableEquiv_branchFactor hm l k).natDegree_eq]
  exact hj

private theorem branchHarmonic_injective {m : ℕ} (hm : 1 ≤ m) (l k : ℕ) :
    Function.Injective (branchHarmonic m l k) := by
  intro h₁ h₂ he
  have h := congrArg (fun f => (lastVariableEquiv m f).coeff (l - k)) he
  simpa only [coeff_lastVariableEquiv_branchHarmonic hm] using h

end BranchingCoordinates

open BranchingCoordinates Polynomial in
/-- **Branching decomposition, independence.** For `m ≥ 1` the images of the `H_k(ℝᵐ)`, `k ≤ l`,
are independent. -/
theorem iSupIndep_map_branchHarmonic {m : ℕ} (hm : 1 ≤ m) (l : ℕ) :
    iSupIndep fun k : Fin (l + 1) =>
      (MvPolynomial.harmonicSubmodule (Fin m) ℝ k).map (branchHarmonic m l k) := by
  classical
  let S := fun k : Fin (l + 1) =>
    (MvPolynomial.harmonicSubmodule (Fin m) ℝ k).map (branchHarmonic m l k)
  change iSupIndep S
  apply iSupIndep_of_dfinsupp_lsum_injective
  let L : (Π₀ k, S k) →ₗ[ℝ] MvPolynomial (Fin (m + 1)) ℝ :=
    DFinsupp.lsum ℕ fun i => (S i).subtype
  change Function.Injective L
  suffices hker : ∀ v, L v = 0 → v = 0 by
    intro v w hvw
    have he : L (v - w) = 0 := (map_sub L.toAddMonoidHom v w).trans (sub_eq_zero.mpr hvw)
    exact sub_eq_zero.mp (hker (v - w) he)
  intro v hv
  by_contra hne
  have hs : v.support.Nonempty := by
    by_contra! hempty
    exact hne (DFinsupp.support_eq_empty.mp hempty)
  let k := v.support.min' hs
  have hk : k ∈ v.support := Finset.min'_mem _ _
  have hkv : v k ≠ 0 := (DFinsupp.mem_support_toFun v k).mp hk
  have hk0 : (v k : MvPolynomial (Fin (m + 1)) ℝ) ≠ 0 := by simpa using hkv
  unfold L at hv
  have hl := congrArg (fun f => (lastVariableEquiv m f).coeff (l - k)) hv
  simp only [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, DFinsupp.sum,
    LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply, map_sum,
    map_zero, coeff_zero] at hl
  rw [← lcoeff_apply, map_sum] at hl
  simp only [lcoeff_apply] at hl
  rw [Finset.sum_eq_single k] at hl
  · obtain ⟨h, -, he⟩ := (v k).property
    rw [← he, coeff_lastVariableEquiv_branchHarmonic hm] at hl
    exact hk0 (by rw [← he, hl, map_zero])
  · intro j hj hjk
    have hlt : k < j := lt_of_le_of_ne (Finset.min'_le _ _ hj) hjk.symm
    obtain ⟨h, -, he⟩ := (v j).property
    rw [← he, coeff_lastVariableEquiv_branchHarmonic_eq_zero hm]
    have hkj : k.val < j.val := hlt
    have hjl := j.isLt
    omega
  · exact fun hn => (hn hk).elim

namespace BranchingDimensions

/-- The constant harmonics have dimension one. -/
private theorem finrank_harmonicSubmodule_constant (m : ℕ) :
    Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin m) ℝ 0) = 1 := by
  rw [MvPolynomial.finrank_harmonicSubmodule_of_le_one (by decide : 0 ≤ 1)]
  simp

/-- The linear harmonics have dimension equal to the number of variables. -/
private theorem finrank_harmonicSubmodule_linear (m : ℕ) :
    Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin m) ℝ 1) = m := by
  rw [MvPolynomial.finrank_harmonicSubmodule_of_le_one (by decide : 1 ≤ 1)]
  simp

/-- The multiset coefficient inequality from the Fischer decomposition. -/
private theorem multichoose_le_multichoose_add_two {m : ℕ} (hm : 1 ≤ m) (l : ℕ) :
    m.multichoose l ≤ m.multichoose (l + 2) := by
  let nonempty : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have h := MvPolynomial.finrank_harmonicSubmodule_add_finrank (σ := Fin m) (K := ℝ) l
  rw [TauCeti.finrank_homogeneousSubmodule_eq_multichoose,
    TauCeti.finrank_homogeneousSubmodule_eq_multichoose, Fintype.card_fin] at h
  omega

/-- The Pascal recurrence for the dimension of harmonics. -/
private theorem finrank_harmonicSubmodule_succ_add_one {m : ℕ} (hm : 1 ≤ m) (l : ℕ) :
    Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (m + 1)) ℝ (l + 1)) =
      Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin m) ℝ (l + 1)) +
        Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (m + 1)) ℝ l) := by
  rcases l with _ | _ | l
  · simp [finrank_harmonicSubmodule_linear, finrank_harmonicSubmodule_constant]
  · change Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (m + 1)) ℝ (0 + 2)) =
      Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin m) ℝ (0 + 2)) +
        Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (m + 1)) ℝ 1)
    simp only [MvPolynomial.finrank_harmonicSubmodule_add_two, Fintype.card_fin,
      finrank_harmonicSubmodule_linear]
    change (m + 1).multichoose 2 - (m + 1).multichoose 0 =
      m.multichoose 2 - m.multichoose 0 + (m + 1)
    have h := Nat.multichoose_succ_succ m 1
    change (m + 1).multichoose 2 = m.multichoose 2 + (m + 1).multichoose 1 at h
    rw [Nat.multichoose_one_right] at h
    have hm2 := multichoose_le_multichoose_add_two hm 0
    simp only [Nat.multichoose_zero_right, zero_add] at hm2 ⊢
    omega
  · change Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (m + 1)) ℝ ((l + 1) + 2)) =
      Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin m) ℝ ((l + 1) + 2)) +
        Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (m + 1)) ℝ (l + 2))
    simp only [MvPolynomial.finrank_harmonicSubmodule_add_two, Fintype.card_fin]
    have h1 : (m + 1).multichoose ((l + 1) + 2) =
        m.multichoose ((l + 1) + 2) + (m + 1).multichoose (l + 2) :=
      Nat.multichoose_succ_succ m (l + 2)
    have h2 := Nat.multichoose_succ_succ m l
    have h3 := multichoose_le_multichoose_add_two hm (l + 1)
    have h4 := multichoose_le_multichoose_add_two (show 1 ≤ m + 1 by omega) l
    omega

end BranchingDimensions

open BranchingDimensions in
/-- **Branching dimension.** `dim H_l(ℝ^{m+1}) = ∑_{k ≤ l} dim H_k(ℝᵐ)` for `m ≥ 1`. -/
theorem finrank_harmonicSubmodule_succ {m : ℕ} (hm : 1 ≤ m) (l : ℕ) :
    Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (m + 1)) ℝ l) =
      ∑ k ∈ Finset.range (l + 1),
        Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin m) ℝ k) := by
  induction l with
  | zero => simp [finrank_harmonicSubmodule_constant]
  | succ l ih =>
    rw [finrank_harmonicSubmodule_succ_add_one hm, Finset.sum_range_succ, ← ih, add_comm]

open BranchingCoordinates in
/-- **Branching decomposition, spanning.** For `m ≥ 1`, `H_l(ℝ^{m+1})` is the sum over `k ≤ l`
of the images of `H_k(ℝᵐ)` under the branching maps. -/
theorem harmonicSubmodule_eq_iSup_map_branchHarmonic {m : ℕ} (hm : 1 ≤ m) (l : ℕ) :
    MvPolynomial.harmonicSubmodule (Fin (m + 1)) ℝ l =
      ⨆ k : Fin (l + 1),
        (MvPolynomial.harmonicSubmodule (Fin m) ℝ k).map (branchHarmonic m l k) := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · refine iSup_le fun k _ h => ?_
    obtain ⟨p, hp, rfl⟩ := h
    exact branchHarmonic_mem_harmonicSubmodule hm (Nat.le_of_lt_succ k.isLt) hp
  · rw [TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep (iSupIndep_map_branchHarmonic hm l),
      finrank_harmonicSubmodule_succ hm, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun k _ =>
      (Submodule.equivMapOfInjective _ (branchHarmonic_injective hm l k) _).finrank_eq.symm
/-- **Branching norm.** For `m ≥ 1`, `k ≤ l` and `h ∈ H_k(ℝᵐ)`, the `L²` norm of
`branchHarmonic m l k h` on `S^m` is `κ` times that of `h` on `S^{m-1}`, with
`κ = c_{m+1}/(c_{m+1+2k} dim H_{l-k}(ℝ^{m+1+2k}))`. -/
theorem integral_sphereEval_branchHarmonic_sq {m l k : ℕ} (hm : 1 ≤ m) (hkl : k ≤ l)
    {h : MvPolynomial (Fin m) ℝ} (hh : h ∈ MvPolynomial.harmonicSubmodule (Fin m) ℝ k) :
    ∫ x : Sphere (m + 1), MvPolynomial.sphereEval (branchHarmonic m l k h) x ^ 2
        ∂sphereMeasure (m + 1) =
      polarConstant (m + 1) / (polarConstant (m + 1 + 2 * k) *
          Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (m + 1 + 2 * k)) ℝ (l - k))) *
        ∫ y : Sphere m, MvPolynomial.sphereEval h y ^ 2 ∂sphereMeasure m := by
  sorry

end SFVK.Spheres
