/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU2.Basic.Coordinates
import SFVK.SU2.Basic.MatrixElements
import SFVK.SU2.UnitaryModel
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import TauCeti.RepresentationTheory.Compact.SchurOrthogonality
import TauCeti.Topology.Algebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import SFVKMathlib.Analysis.Complex.EulerPhases

/-!
# Euler coordinates on `SU(2)`: covering and Haar measure

The Euler coordinates of `SFVK.SU2.Basic.Coordinates` cover `SU(2)` with the middle angle in
`[0, π]`, are bijective on the open-middle-angle box onto the matrices with two nonzero top
entries, and push the Euler-angle measure forward to the normalized Haar measure (Vilenkin–Klimyk,
Vol. 1, §6.1.4 (1), p. 275). The measure identity compares integrals of monomials in the top-row
entries and their conjugates. The radial moments on Haar measure follow from Tau Ceti's Schur
orthogonality for the highest-weight coefficient of each normalized symmetric power.
-/

public section

open Complex Matrix MeasureTheory Set
open scoped ComplexConjugate Real
open TauCeti TauCeti.SU2

namespace SFVK.SU2

/-- The lower row of a special unitary matrix is determined by its top row. -/
private theorem coe_eq_of_topRow (g : TauCeti.SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0, (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1;
        -conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1), conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0)] := by
  have h := Matrix.specialUnitaryGroup.star_eq_adjugate g
  rw [Matrix.adjugate_fin_two] at h
  have ha : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) := by
    simpa using (congrFun (congrFun h 0) 0).symm
  have hb : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = -conj ((g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) :=
    neg_eq_iff_eq_neg.mp (by simpa using (congrFun (congrFun h 1) 0).symm)
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [ha, hb]

/-- A special unitary matrix of degree two is determined by its top row. -/
private theorem eq_of_topRow_eq {g h : TauCeti.SU2}
    (ha : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = (h : Matrix (Fin 2) (Fin 2) ℂ) 0 0)
    (hb : (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = (h : Matrix (Fin 2) (Fin 2) ℂ) 0 1) : g = h := by
  apply Subtype.ext
  rw [coe_eq_of_topRow g, coe_eq_of_topRow h]
  simp only [ha, hb]

/-- The two top entries of a special unitary matrix have squared norms summing to one. -/
private theorem norm_topRow_sq_add (g : TauCeti.SU2) :
    ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 0 1‖ ^ 2 = 1 := by
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp g.2).2
  conv_lhs at hd => rw [coe_eq_of_topRow g]
  rw [Matrix.det_fin_two_of, mul_neg, sub_neg_eq_add, Complex.mul_conj, Complex.mul_conj,
    normSq_eq_norm_sq, normSq_eq_norm_sq] at hd
  exact_mod_cast hd

/-- The left top entry has phase given by the half-sum of the Euler angles. -/
private theorem euler_topLeft (α β γ : ℝ) :
    (euler α β γ : Matrix (Fin 2) (Fin 2) ℂ) 0 0 =
      (Real.cos (β / 2) : ℂ) * (Circle.exp ((α + γ) / 2) : ℂ) := by
  rw [euler_def, Submonoid.coe_mul, Submonoid.coe_mul, coe_torusExp, coe_torusExp,
    coe_eulerMiddle, Matrix.mul_diagonal, Matrix.diagonal_mul, add_div, Circle.exp_add]
  simp [Circle.coe_mul, Circle.coe_exp]
  ring

/-- The right top entry has phase given by the half-difference of the Euler angles. -/
private theorem euler_topRight (α β γ : ℝ) :
    (euler α β γ : Matrix (Fin 2) (Fin 2) ℂ) 0 1 =
      (Real.sin (β / 2) : ℂ) * (Circle.exp ((α - γ) / 2) : ℂ) := by
  rw [euler_def, Submonoid.coe_mul, Submonoid.coe_mul, coe_torusExp, coe_torusExp,
    coe_eulerMiddle, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_div, Circle.exp_sub]
  simp [Circle.coe_exp, Complex.exp_neg, div_eq_mul_inv]
  ring

/-- The norm of the top-left entry gives the cosine of the half-angle on the Euler box. -/
private theorem norm_euler_topLeft (α γ : ℝ) {β : ℝ} (hβ : β ∈ Icc 0 π) :
    ‖(euler α β γ : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ = Real.cos (β / 2) := by
  rw [euler_topLeft, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hβ.1, Real.pi_pos], by linarith [hβ.2]⟩)]

/-- In the interior of the middle-angle interval, the cosine of the half-angle is positive. -/
private theorem cos_half_pos {β : ℝ} (hβ : β ∈ Ioo 0 π) : 0 < Real.cos (β / 2) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hβ.1, Real.pi_pos], by linarith [hβ.2]⟩

/-- In the interior of the middle-angle interval, the sine of the half-angle is positive. -/
private theorem sin_half_pos {β : ℝ} (hβ : β ∈ Ioo 0 π) : 0 < Real.sin (β / 2) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hβ.1]) (by linarith [hβ.2, Real.pi_pos])

/-- With the middle angle allowed to reach its endpoints, the Euler coordinates cover `SU(2)`. -/
theorem exists_euler_eq (g : TauCeti.SU2) :
    ∃ α β γ, α ∈ Ico 0 (2 * π) ∧ β ∈ Icc 0 π ∧ γ ∈ Ico (-(2 * π)) (2 * π) ∧
      euler α β γ = g := by
  let a := (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0
  let b := (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1
  have hsq : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := norm_topRow_sq_add g
  let β := 2 * Real.arccos ‖a‖
  have hβ : β ∈ Icc 0 π := ⟨by linarith [Real.arccos_nonneg ‖a‖],
    by linarith [Real.arccos_le_pi_div_two.mpr (norm_nonneg a)]⟩
  have hcos : Real.cos (β / 2) = ‖a‖ := by
    rw [show β / 2 = Real.arccos ‖a‖ by dsimp [β]; ring]
    exact Real.cos_arccos (by linarith [norm_nonneg a]) (by nlinarith [sq_nonneg ‖b‖])
  have hsin : Real.sin (β / 2) = ‖b‖ := by
    have hnonneg := Real.sin_nonneg_of_nonneg_of_le_pi (x := β / 2)
      (by linarith [hβ.1]) (by linarith [hβ.2, Real.pi_pos])
    have hsinSq : Real.sin (β / 2) ^ 2 = ‖b‖ ^ 2 := by
      linarith [Real.cos_sq_add_sin_sq (β / 2), congrArg (· ^ 2) hcos]
    exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsinSq).elim id
      (fun heq => by linarith [norm_nonneg b])
  obtain ⟨α, hα, γ, hγ, ha, hb⟩ := Circle.exists_exp_add_half_eq_and_exp_sub_half_eq
    (Circle.exp (arg a)) (Circle.exp (arg b))
  refine ⟨α, β, γ, hα, hβ, hγ, eq_of_topRow_eq ?_ ?_⟩
  · rw [euler_topLeft, hcos, ha, Circle.coe_exp, norm_mul_exp_arg_mul_I]
  · rw [euler_topRight, hsin, hb, Circle.coe_exp, norm_mul_exp_arg_mul_I]

/-- On the open-middle-angle box the Euler coordinates are a bijection onto the matrices with
two nonzero top entries. -/
theorem bijOn_euler :
    BijOn (fun p : ℝ × ℝ × ℝ => euler p.1 p.2.1 p.2.2) eulerBox
      {g : TauCeti.SU2 | (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 *
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 ≠ 0} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨α, β, γ⟩ hp
    have hβ := (mem_eulerBox.mp hp).2.1
    simp only [mem_ofPred_eq, euler_topLeft, euler_topRight, mul_ne_zero_iff,
      Complex.ofReal_ne_zero]
    exact ⟨⟨(cos_half_pos hβ).ne', Circle.coe_ne_zero _⟩,
      (sin_half_pos hβ).ne', Circle.coe_ne_zero _⟩
  · rintro ⟨α, β, γ⟩ hp ⟨α', β', γ'⟩ hp' heq
    obtain ⟨hα, hβ, hγ⟩ := mem_eulerBox.mp hp
    obtain ⟨hα', hβ', hγ'⟩ := mem_eulerBox.mp hp'
    have ha := congrArg (fun g : TauCeti.SU2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0) heq
    have hb := congrArg (fun g : TauCeti.SU2 => (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1) heq
    have hmid : β = β' := by
      have hn := congrArg norm ha
      simp only [norm_euler_topLeft α γ ⟨hβ.1.le, hβ.2.le⟩,
        norm_euler_topLeft α' γ' ⟨hβ'.1.le, hβ'.2.le⟩] at hn
      have hh := Real.strictAntiOn_cos.injOn
        (x₁ := β / 2) (x₂ := β' / 2)
        ⟨by linarith [hβ.1], by linarith [hβ.2, Real.pi_pos]⟩
        ⟨by linarith [hβ'.1], by linarith [hβ'.2, Real.pi_pos]⟩ hn
      linarith
    subst β'
    have hpA : Circle.exp ((α + γ) / 2) = Circle.exp ((α' + γ') / 2) := by
      apply Subtype.ext
      simp only [euler_topLeft] at ha
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (cos_half_pos hβ).ne') ha
    have hpB : Circle.exp ((α - γ) / 2) = Circle.exp ((α' - γ') / 2) := by
      apply Subtype.ext
      simp only [euler_topRight] at hb
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (sin_half_pos hβ).ne') hb
    have hangles := @Circle.injOn_exp_add_half_sub_half (α, γ) ⟨hα, hγ⟩ (α', γ') ⟨hα', hγ'⟩
      (Prod.ext hpA hpB)
    exact congrArg (fun p : ℝ × ℝ => (p.1, β, p.2)) hangles
  · intro g hg
    obtain ⟨α, β, γ, hα, hβ, hγ, rfl⟩ := exists_euler_eq g
    have hb : β ∈ Ioo 0 π := by
      constructor
      · refine lt_of_le_of_ne hβ.1 fun heq => ?_
        subst β
        exact hg (by simp [euler_topRight])
      · refine lt_of_le_of_ne hβ.2 fun heq => ?_
        subst β
        exact hg (by simp [euler_topLeft, Real.cos_pi_div_two])
    exact ⟨(α, β, γ), mem_eulerBox.mpr ⟨hα, hb, hγ⟩, rfl⟩

namespace EulerHaar

open scoped BoundedContinuousFunction InnerProductSpace Matrix.Norms.Elementwise

noncomputable section

/-- The top-row matrix entry in the indicated column. -/
private def topEntry (j : Fin 2) (g : TauCeti.SU2) : ℂ :=
  (g : Matrix (Fin 2) (Fin 2) ℂ) 0 j

/-- A top-row matrix entry is continuous on the special unitary group. -/
private theorem continuous_topEntry (j : Fin 2) : Continuous (topEntry j) :=
  (continuous_apply j).comp ((continuous_apply 0).comp continuous_subtype_val)

/-- The squared moduli of the two entries sum to one. -/
private theorem normSq_topEntries (g : TauCeti.SU2) :
    normSq (topEntry 0 g) + normSq (topEntry 1 g) = 1 := by
  simpa only [topEntry, normSq_eq_norm_sq] using norm_topRow_sq_add g

/-- Left multiplication by a torus element gives both entries the same phase. -/
private theorem topEntry_torusExp_mul (θ : ℝ) (j : Fin 2) (g : TauCeti.SU2) :
    topEntry j (torusExp θ * g) = exp (I * θ) * topEntry j g := by
  simp only [topEntry, Submonoid.coe_mul, torusExp_def, coe_torusHom, Matrix.mul_apply,
    Fin.sum_univ_two, torusMatrix_apply_zero_zero, torusMatrix_apply_zero_one,
    zero_mul, add_zero, Circle.coe_exp, mul_comm (I : ℂ)]

/-- Right multiplication gives the first entry the positive phase. -/
private theorem topEntry_mul_torusExp_zero (θ : ℝ) (g : TauCeti.SU2) :
    topEntry 0 (g * torusExp θ) = exp (I * θ) * topEntry 0 g := by
  simp only [topEntry, Submonoid.coe_mul, torusExp_def, coe_torusHom, Matrix.mul_apply,
    Fin.sum_univ_two, torusMatrix_apply_zero_zero, torusMatrix_apply_one_zero,
    mul_zero, add_zero, Circle.coe_exp, mul_comm (I : ℂ)]
  ring

/-- Right multiplication gives the second entry the negative phase. -/
private theorem topEntry_mul_torusExp_one (θ : ℝ) (g : TauCeti.SU2) :
    topEntry 1 (g * torusExp θ) = exp (-(I * θ)) * topEntry 1 g := by
  simp only [topEntry, Submonoid.coe_mul, torusExp_def, coe_torusHom, Matrix.mul_apply,
    Fin.sum_univ_two, torusMatrix_apply_zero_one, torusMatrix_apply_one_one, mul_zero,
    zero_add, Circle.coe_exp, mul_comm (I : ℂ), exp_neg]
  ring

/-- The monomial in the two top-row entries and their conjugates. -/
private def coordinateMonomial (a b c d : ℕ) (g : TauCeti.SU2) : ℂ :=
  topEntry 0 g ^ a * conj (topEntry 0 g) ^ b * topEntry 1 g ^ c * conj (topEntry 1 g) ^ d

/-- A coordinate monomial is continuous. -/
private theorem continuous_coordinateMonomial (a b c d : ℕ) :
    Continuous (coordinateMonomial a b c d) := by
  unfold coordinateMonomial
  exact (((continuous_topEntry 0).pow a).mul
    ((continuous_conj.comp (continuous_topEntry 0)).pow b)).mul
    ((continuous_topEntry 1).pow c) |>.mul ((continuous_conj.comp (continuous_topEntry 1)).pow d)

/-- Conjugation reverses a positive real angle in the complex exponential. -/
private theorem conj_exp_I_mul (θ : ℝ) : conj (exp (I * θ)) = exp (-(I * θ)) := by
  rw [← exp_conj, map_mul, conj_I, conj_ofReal, neg_mul]

/-- Conjugation reverses a negative real angle in the complex exponential. -/
private theorem conj_exp_neg_I_mul (θ : ℝ) : conj (exp (-(I * θ))) = exp (I * θ) := by
  rw [← exp_conj, map_neg, map_mul, conj_I, conj_ofReal, neg_mul, neg_neg]

/-- The integer exponent for the left torus action on the monomial. -/
private def leftTorusWeight (a b c d : ℕ) : ℤ := (a : ℤ) - b + c - d

/-- The integer exponent for the right torus action on the monomial. -/
private def rightTorusWeight (a b c d : ℕ) : ℤ := (a : ℤ) - b - c + d

/-- The left torus acts on a monomial by its left weight. -/
private theorem coordinateMonomial_torusExp_mul (a b c d : ℕ) (θ : ℝ) (g : TauCeti.SU2) :
    coordinateMonomial a b c d (torusExp θ * g) =
      exp (I * (leftTorusWeight a b c d : ℂ) * θ) * coordinateMonomial a b c d g := by
  calc
    _ = (exp (a * (I * θ)) * exp (b * -(I * θ)) * exp (c * (I * θ)) *
        exp (d * -(I * θ))) * coordinateMonomial a b c d g := by
      simp only [coordinateMonomial, topEntry_torusExp_mul, map_mul, mul_pow,
        conj_exp_I_mul, ← exp_nat_mul]
      ring
    _ = _ := by
      rw [← exp_add, ← exp_add, ← exp_add]
      congr 2
      unfold leftTorusWeight
      push_cast
      ring

/-- The right torus acts on a monomial by its right weight. -/
private theorem coordinateMonomial_mul_torusExp (a b c d : ℕ) (θ : ℝ) (g : TauCeti.SU2) :
    coordinateMonomial a b c d (g * torusExp θ) =
      exp (I * (rightTorusWeight a b c d : ℂ) * θ) * coordinateMonomial a b c d g := by
  calc
    _ = (exp (a * (I * θ)) * exp (b * -(I * θ)) * exp (c * -(I * θ)) *
        exp (d * (I * θ))) * coordinateMonomial a b c d g := by
      simp only [coordinateMonomial, topEntry_mul_torusExp_zero, topEntry_mul_torusExp_one,
        map_mul, mul_pow, conj_exp_I_mul, conj_exp_neg_I_mul, ← exp_nat_mul]
      ring
    _ = _ := by
      rw [← exp_add, ← exp_add, ← exp_add]
      congr 2
      unfold rightTorusWeight
      push_cast
      ring

/-- Rescaling a half-turn by a nonzero frequency yields the phase `-1`. -/
private theorem exp_I_mul_int_cast_halfTurn (n : ℤ) (hn : n ≠ 0) :
    exp (I * n * ((Real.pi / (n : ℝ) : ℝ) : ℂ)) = -1 := by
  rw [Complex.ofReal_div, Complex.ofReal_intCast]
  have h : (n : ℂ) ≠ 0 := Int.cast_ne_zero.2 hn
  calc
    _ = exp (Real.pi * I) := by
      congr 1
      field_simp
    _ = -1 := exp_pi_mul_I

/-- Torus invariance annihilates monomials with nonzero weight. -/
private theorem integral_coordinateMonomial_haar_eq_zero (a b c d : ℕ)
    (hne : a ≠ b ∨ c ≠ d) :
    ∫ g, coordinateMonomial a b c d g ∂haarProb TauCeti.SU2 = 0 := by
  by_cases hl : leftTorusWeight a b c d = 0
  · have hr : rightTorusWeight a b c d ≠ 0 := by
      unfold leftTorusWeight at hl
      unfold rightTorusWeight
      omega
    refine integral_eq_zero_of_mul_right_eq_neg
      (g := torusExp (Real.pi / (rightTorusWeight a b c d : ℝ))) ?_
    intro g
    rw [coordinateMonomial_mul_torusExp, exp_I_mul_int_cast_halfTurn _ hr, neg_one_mul]
  · refine integral_eq_zero_of_mul_left_eq_neg
      (g := torusExp (Real.pi / (leftTorusWeight a b c d : ℝ))) ?_
    intro g
    rw [coordinateMonomial_torusExp_mul, exp_I_mul_int_cast_halfTurn _ hl, neg_one_mul]

/-- The highest-weight coefficient is a power of the first entry. -/
private theorem matrixElement_last_last (d : ℕ) (g : TauCeti.SU2) :
    matrixElement d (Fin.last d) (Fin.last d) g = topEntry 0 g ^ d := by
  rw [matrixElement_eq_entrySum, entrySum]
  simp only [Fin.val_last]
  rw [Finset.sum_eq_single 0]
  · simp only [topEntry, zero_add, Nat.le_add_right, le_refl, and_self, ↓reduceIte,
      Nat.add_sub_cancel, tsub_self, Nat.factorial_zero, Nat.cast_one, mul_one,
      one_mul, pow_zero]
    have h : (0 : ℝ) < d.factorial := by positivity
    rw [← sq, Real.sqrt_sq h.le, div_self h.ne', Complex.ofReal_one, one_mul]
  · intro k hk hne
    have hk' : ¬ (d ≤ k + d + d ∧ k + d ≤ d ∧ k + d ≤ d) := by omega
    rw [ite_eq_right hk']
  · simp

/-- Schur orthogonality gives the Haar moments of the first modulus. -/
private theorem integral_normSq_topEntry_power_haar (n : ℕ) :
    ∫ g, normSq (topEntry 0 g) ^ n ∂haarProb TauCeti.SU2 = ((n : ℝ) + 1)⁻¹ := by
  let e := EuclideanSpace.basisFun (Fin (n + 1)) ℂ
  let k := Fin.last n
  have hnorm := ContRepresentation.norm_matrixCoeffLp_sq (unitaryModel n)
    (continuous_unitaryModel n) (e k) (e k)
  -- Tau Ceti's Schur orthogonality applies to the normalized weight basis.
  have horth := ContRepresentation.schur_orthogonality_basis (unitaryModel n)
    (continuous_unitaryModel n) (isUnitary_unitaryModel n) (isIrreducible_unitaryModel n)
    e k k k k
  simp only [↓reduceIte, mul_one] at horth
  rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
    ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_inj,
    Nat.cast_add, Nat.cast_one] at horth
  have hv (g : TauCeti.SU2) : ‖⟪unitaryModel n g (e k), e k⟫_ℂ‖ ^ 2 =
      normSq (topEntry 0 g) ^ n := by
    have h := matrixElement_last_last n g
    rw [matrixElement_def, ← EuclideanSpace.basisFun_apply] at h
    have hk : e k = (EuclideanSpace.basisFun _ ℂ) (Fin.last n) := rfl
    rw [hk, ← inner_conj_symm, h, Complex.norm_conj, norm_pow, ← Complex.sq_norm,
      ← pow_mul, ← pow_mul]
    rw [Nat.mul_comm]
  simp_rw [hv] at hnorm
  rw [← hnorm, horth]

/-- The Euler product is continuous in all three angles. -/
private theorem continuous_eulerMap :
    Continuous (fun p : ℝ × ℝ × ℝ => euler p.1 p.2.1 p.2.2) := by
  have hmiddle : Continuous eulerMiddle := by
    apply continuous_induced_rng.2
    simp only [Function.comp_def, coe_eulerMiddle]
    fun_prop
  exact ((continuous_torusExp.comp (continuous_fst.div_const 2)).mul
    (hmiddle.comp (continuous_fst.comp continuous_snd))).mul
    (continuous_torusExp.comp ((continuous_snd.comp continuous_snd).div_const 2))

/-- The Euler parameter box is a measurable product of intervals. -/
private theorem measurableSet_eulerBox : MeasurableSet eulerBox :=
  measurableSet_Ico.prod (measurableSet_Ioo.prod measurableSet_Ico)

/-- The Euler density is bounded on a finite-volume box. -/
private theorem isFiniteMeasure_eulerMeasure : IsFiniteMeasure eulerMeasure := by
  constructor
  rw [eulerMeasure_def, smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  calc
    _ ≤ ∫⁻ _ : ℝ × ℝ × ℝ, 1 ∂volume.restrict eulerBox := by
      apply lintegral_mono
      intro p
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (Real.sin_le_one _)
    _ < ⊤ := by
      simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, eulerBox,
        Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ioo]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- Products of single-angle functions integrate separately. -/
private theorem integral_eulerMeasure_prod (F G H : ℝ → ℂ) :
    ∫ p : ℝ × ℝ × ℝ, F p.1 * G p.2.1 * H p.2.2 ∂eulerMeasure =
      ((16 * Real.pi ^ 2)⁻¹ : ℝ) •
        (∫ α in Ico 0 (2 * Real.pi), F α) *
        (∫ β in Ioo 0 Real.pi, G β * (Real.sin β : ℂ)) *
        (∫ γ in Ico (-(2 * Real.pi)) (2 * Real.pi), H γ) := by
  rw [eulerMeasure_def, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ENNReal.toReal_ofReal (by positivity)]
  have h : ∫ p : ℝ × ℝ × ℝ,
        (ENNReal.ofReal (Real.sin p.2.1)).toReal • (F p.1 * G p.2.1 * H p.2.2)
        ∂volume.restrict eulerBox =
      ∫ p : ℝ × ℝ × ℝ, F p.1 * ((G p.2.1 * (Real.sin p.2.1 : ℂ)) * H p.2.2)
        ∂volume.restrict eulerBox := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_eulerBox] with p hp
    rw [ENNReal.toReal_ofReal (Real.sin_nonneg_of_nonneg_of_le_pi
      (mem_eulerBox.mp hp).2.1.1.le (mem_eulerBox.mp hp).2.1.2.le), Complex.real_smul]
    ring
  rw [h]
  simp only [eulerBox, Measure.volume_eq_prod]
  rw [setIntegral_prod_mul F (fun p : ℝ × ℝ => (G p.1 * (Real.sin p.1 : ℂ)) * H p.2),
    setIntegral_prod_mul (fun β => G β * (Real.sin β : ℂ)) H]
  simp only [Complex.real_smul]
  ring

/-- The first entry of the middle factor is the cosine of the half-angle. -/
private theorem topEntry_eulerMiddle_zero (β : ℝ) :
    topEntry 0 (eulerMiddle β) = Real.cos (β / 2) := by simp [topEntry]

/-- The second entry of the middle factor is the sine of the half-angle. -/
private theorem topEntry_eulerMiddle_one (β : ℝ) :
    topEntry 1 (eulerMiddle β) = Real.sin (β / 2) := by simp [topEntry]

/-- In Euler coordinates the two phases separate from the middle angle. -/
private theorem coordinateMonomial_euler (a b c d : ℕ) (p : ℝ × ℝ × ℝ) :
    coordinateMonomial a b c d (euler p.1 p.2.1 p.2.2) =
      exp (I * (leftTorusWeight a b c d : ℂ) * ((p.1 / 2 : ℝ) : ℂ)) *
        ((Real.cos (p.2.1 / 2) : ℂ) ^ (a + b) * (Real.sin (p.2.1 / 2) : ℂ) ^ (c + d)) *
          exp (I * (rightTorusWeight a b c d : ℂ) * ((p.2.2 / 2 : ℝ) : ℂ)) := by
  rw [euler_def, mul_assoc, coordinateMonomial_torusExp_mul, coordinateMonomial_mul_torusExp]
  simp only [coordinateMonomial, topEntry_eulerMiddle_zero, topEntry_eulerMiddle_one,
    conj_ofReal, pow_add]
  ring

/-- A nonzero integer frequency integrates to zero over a full period. -/
private theorem integral_exp_int_mul_Ico (n : ℤ) (hn : n ≠ 0) :
    ∫ θ in Ico 0 (2 * Real.pi), exp (I * (n : ℂ) * θ) = 0 := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.two_pi_pos.le,
    integral_exp_mul_complex (mul_ne_zero I_ne_zero (Int.cast_ne_zero.2 hn))]
  have h : I * (n : ℂ) * ((2 * Real.pi : ℝ) : ℂ) = (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    push_cast
    ring
  rw [h, exp_int_mul_two_pi_mul_I]
  simp

/-- A nonzero half-integer frequency integrates to zero over two periods. -/
private theorem integral_exp_half_int_mul_Ico (n : ℤ) (hn : n ≠ 0) :
    ∫ θ in Ico (-(2 * Real.pi)) (2 * Real.pi), exp (I * (n : ℂ) * ((θ / 2 : ℝ) : ℂ)) =
      0 := by
  have hle : -(2 * Real.pi) ≤ 2 * Real.pi := by linarith [Real.pi_pos]
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  simp_rw [Complex.ofReal_div, Complex.ofReal_ofNat]
  have hw (θ : ℝ) : I * (n : ℂ) * ((θ : ℂ) / 2) = (I * (n : ℂ) / 2) * (θ : ℂ) := by ring
  simp_rw [hw]
  have hfreq : I * (n : ℂ) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero I_ne_zero (Int.cast_ne_zero.2 hn)) (by norm_num)
  rw [integral_exp_mul_complex hfreq]
  push_cast
  have ha : I * (n : ℂ) / 2 * (2 * (Real.pi : ℂ)) = (n : ℂ) * (Real.pi * I) := by ring
  have hb : I * (n : ℂ) / 2 * -(2 * (Real.pi : ℂ)) = (-n : ℤ) * (Real.pi * I) := by
    push_cast
    ring
  rw [ha, hb, exp_int_mul, exp_int_mul, exp_pi_mul_I, _root_.zpow_neg]
  simp only [← _root_.inv_zpow, inv_neg, inv_one, sub_self, zero_div]

/-- The Euler angular integrals annihilate nonzero weights. -/
private theorem integral_coordinateMonomial_euler_eq_zero (a b c d : ℕ)
    (hne : a ≠ b ∨ c ≠ d) :
    ∫ p : ℝ × ℝ × ℝ, coordinateMonomial a b c d (euler p.1 p.2.1 p.2.2) ∂eulerMeasure =
      0 := by
  simp_rw [coordinateMonomial_euler]
  rw [integral_eulerMeasure_prod
    (fun α => exp (I * (leftTorusWeight a b c d : ℂ) * ((α / 2 : ℝ) : ℂ)))
    (fun β => (Real.cos (β / 2) : ℂ) ^ (a + b) * (Real.sin (β / 2) : ℂ) ^ (c + d))
    (fun γ => exp (I * (rightTorusWeight a b c d : ℂ) * ((γ / 2 : ℝ) : ℂ)))]
  by_cases hr : rightTorusWeight a b c d = 0
  · have hl : leftTorusWeight a b c d = 2 * ((a : ℤ) - b) := by
      unfold rightTorusWeight at hr
      unfold leftTorusWeight
      omega
    have hne' : (a : ℤ) - b ≠ 0 := by
      unfold rightTorusWeight at hr
      omega
    have hθ (θ : ℝ) : I * (leftTorusWeight a b c d : ℂ) * ((θ / 2 : ℝ) : ℂ) =
        I * (((a : ℤ) - (b : ℤ) : ℤ) : ℂ) * θ := by
      rw [hl]
      push_cast
      ring
    simp only [hθ, integral_exp_int_mul_Ico _ hne', smul_zero, zero_mul]
  · rw [integral_exp_half_int_mul_Ico _ hr, mul_zero]

/-- A middle-angle integral is evaluated by its cosine primitive. -/
private theorem integral_sin_mul_cosHalf_sq_pow (n : ℕ) :
    (∫ β in (0 : ℝ)..Real.pi, (Real.cos (β / 2) ^ 2) ^ n * Real.sin β) =
      2 / ((n : ℝ) + 1) := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun y : ℝ => (-(2 / ((n : ℝ) + 1))) *
          (Real.cos (y / 2) ^ 2) ^ (n + 1))
        ((Real.cos (x / 2) ^ 2) ^ n * Real.sin x) x := by
    have h := (Real.hasDerivAt_cos (x / 2)).comp x ((hasDerivAt_id x).div_const 2)
    have hs := ((h.pow 2).pow (n + 1)).const_mul (-(2 / ((n : ℝ) + 1)))
    convert hs using 1
    · rfl
    · have hx : 2 * (x / 2) = x := by ring
      have hsin : Real.sin x = 2 * Real.sin (x / 2) * Real.cos (x / 2) := by
        rw [← Real.sin_two_mul, hx]
      simp only [hsin, Function.comp_apply, id_eq, Pi.pow_apply, Nat.add_sub_cancel,
        Nat.reduceSub, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_one]
      field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)]
  · simp
  · exact (by fun_prop : Continuous fun β : ℝ =>
      (Real.cos (β / 2) ^ 2) ^ n * Real.sin β).intervalIntegrable _ _

/-- The first modulus has the same moments in Euler angles. -/
private theorem integral_coordinateMonomial_euler_radial (n : ℕ) :
    ∫ p : ℝ × ℝ × ℝ, coordinateMonomial n n 0 0 (euler p.1 p.2.1 p.2.2) ∂eulerMeasure =
      (((n : ℝ) + 1)⁻¹ : ℝ) := by
  have hpoint (p : ℝ × ℝ × ℝ) : coordinateMonomial n n 0 0 (euler p.1 p.2.1 p.2.2) =
      (fun _ : ℝ => (1 : ℂ)) p.1 * (fun β : ℝ => (Real.cos (β / 2) : ℂ) ^ (n + n)) p.2.1 *
        (fun _ : ℝ => (1 : ℂ)) p.2.2 := by
    simp [coordinateMonomial_euler, leftTorusWeight, rightTorusWeight]
  simp_rw [hpoint]
  rw [integral_eulerMeasure_prod (fun _ => 1) (fun β => (Real.cos (β / 2) : ℂ) ^ (n + n))
    (fun _ => 1)]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ico,
    Complex.real_smul, mul_one, sub_zero,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)]
  have hmid :
      (∫ β in Ioo 0 Real.pi,
        (Real.cos (β / 2) : ℂ) ^ (n + n) * (Real.sin β : ℂ)) =
        (2 / ((n : ℝ) + 1) : ℝ) := by
    simp_rw [← two_mul, pow_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    rw [integral_complex_ofReal, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le Real.pi_pos.le, integral_sin_mul_cosHalf_sq_pow]
  rw [hmid]
  simp only [← Complex.ofReal_mul, Complex.ofReal_inj]
  rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ 2 * Real.pi - -(2 * Real.pi))]
  field_simp [Real.pi_ne_zero]
  ring

/-- Matching powers of an entry and its conjugate give powers of its modulus. -/
private theorem coordinateMonomial_balanced (a b : ℕ) (g : TauCeti.SU2) :
    coordinateMonomial a a b b g = (normSq (topEntry 0 g) : ℂ) ^ a *
      (normSq (topEntry 1 g) : ℂ) ^ b := by
  unfold coordinateMonomial
  rw [← mul_pow, mul_conj, mul_assoc, ← mul_pow, mul_conj]

/-- The sum of squared moduli reduces the exponent of the second modulus. -/
private theorem coordinateMonomial_balanced_succ (a b : ℕ) (g : TauCeti.SU2) :
    coordinateMonomial a a (b + 1) (b + 1) g =
      coordinateMonomial a a b b g - coordinateMonomial (a + 1) (a + 1) b b g := by
  simp only [coordinateMonomial_balanced, pow_succ]
  have h : (normSq (topEntry 1 g) : ℂ) = 1 - (normSq (topEntry 0 g) : ℂ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_inj, eq_sub_iff_add_eq]
    rw [add_comm, normSq_topEntries]
  nth_rewrite 1 [mul_assoc]
  nth_rewrite 2 [← mul_assoc]
  rw [h]
  ring

/-- Euler-angle measure transported to the group. -/
private def eulerPushforward : Measure TauCeti.SU2 :=
  eulerMeasure.map (fun p : ℝ × ℝ × ℝ => euler p.1 p.2.1 p.2.2)

/-- The pushforward of the finite Euler-angle measure is finite. -/
private instance : IsFiniteMeasure eulerPushforward := by
  let := isFiniteMeasure_eulerMeasure
  exact Measure.isFiniteMeasure_map _ _

/-- A continuous test function integrates by pulling back to Euler angles. -/
private theorem integral_eulerPushforward (f : TauCeti.SU2 → ℂ) (hf : Continuous f) :
    ∫ g, f g ∂eulerPushforward =
      ∫ p : ℝ × ℝ × ℝ, f (euler p.1 p.2.1 p.2.2) ∂eulerMeasure :=
  integral_map continuous_eulerMap.measurable.aemeasurable hf.aestronglyMeasurable

/-- The two measures agree on monomials in the squared moduli. -/
private theorem integral_coordinateMonomial_radial (a b : ℕ) :
    ∫ g, coordinateMonomial a a b b g ∂haarProb TauCeti.SU2 =
      ∫ g, coordinateMonomial a a b b g ∂eulerPushforward := by
  induction b generalizing a with
  | zero =>
    rw [integral_eulerPushforward _ (continuous_coordinateMonomial _ _ _ _),
      integral_coordinateMonomial_euler_radial]
    simp_rw [coordinateMonomial_balanced, pow_zero, mul_one, ← Complex.ofReal_pow]
    rw [integral_complex_ofReal, integral_normSq_topEntry_power_haar]
  | succ b ih =>
    simp_rw [coordinateMonomial_balanced_succ]
    rw [integral_sub ((continuous_coordinateMonomial _ _ _ _).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        ((continuous_coordinateMonomial _ _ _ _).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)),
      integral_sub ((continuous_coordinateMonomial _ _ _ _).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        ((continuous_coordinateMonomial _ _ _ _).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)), ih a, ih (a + 1)]

/-- The two measures agree on every coordinate monomial. -/
private theorem integral_coordinateMonomial_eq (a b c d : ℕ) :
    ∫ g, coordinateMonomial a b c d g ∂haarProb TauCeti.SU2 =
      ∫ g, coordinateMonomial a b c d g ∂eulerPushforward := by
  by_cases h : a = b ∧ c = d
  · obtain ⟨rfl, rfl⟩ := h
    exact integral_coordinateMonomial_radial _ _
  · have hne : a ≠ b ∨ c ≠ d := not_and_or.mp h
    rw [integral_coordinateMonomial_haar_eq_zero _ _ _ _ hne,
      integral_eulerPushforward _ (continuous_coordinateMonomial _ _ _ _),
      integral_coordinateMonomial_euler_eq_zero _ _ _ _ hne]

/-- A coordinate monomial as a bounded continuous function. -/
private def boundedCoordinateMonomial (m : ℕ × ℕ × ℕ × ℕ) :
    TauCeti.SU2 →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨coordinateMonomial m.1 m.2.1 m.2.2.1 m.2.2.2, continuous_coordinateMonomial _ _ _ _⟩

/-- The bundled monomial evaluates to the original monomial. -/
private theorem boundedCoordinateMonomial_apply (m : ℕ × ℕ × ℕ × ℕ) (g : TauCeti.SU2) :
    boundedCoordinateMonomial m g = coordinateMonomial m.1 m.2.1 m.2.2.1 m.2.2.2 g := rfl

/-- The monomial in the two top-row entries and their conjugates. -/
private def coordinateMonomials : Submonoid (TauCeti.SU2 →ᵇ ℂ) where
  carrier := Set.range boundedCoordinateMonomial
  one_mem' := by
    refine ⟨(0,  0,  0,  0), ?_⟩
    ext g
    simp [boundedCoordinateMonomial_apply, coordinateMonomial]
  mul_mem' := by
    rintro f h ⟨⟨a, b, c, d⟩, rfl⟩ ⟨⟨p, q, r, s⟩, rfl⟩
    refine ⟨(a+p, b+q, c+r, d+s), ?_⟩
    ext g
    simp only [boundedCoordinateMonomial_apply, mul_apply,
      coordinateMonomial, pow_add]
    ring

open scoped Pointwise in
/-- Complex conjugation exchanges the paired exponents of each entry. -/
private theorem star_coordinateMonomials_subset :
    star (coordinateMonomials : Set (TauCeti.SU2 →ᵇ ℂ)) ⊆ coordinateMonomials := by
  intro f hf
  rw [Set.mem_star] at hf
  obtain ⟨⟨a, b, c, d⟩, h⟩ := hf
  refine ⟨(b, a, d, c), ?_⟩
  rw [← star_star f, ← h]
  ext g
  simp only [boundedCoordinateMonomial_apply, BoundedContinuousFunction.star_apply,
    coordinateMonomial, Complex.star_def, map_mul, map_pow, starRingEnd_self_apply]
  ring

open scoped Pointwise in
set_option backward.isDefEq.respectTransparency false in
/-- The coordinate monomials span a separating star subalgebra. -/
private theorem eulerPushforward_eq_haarProb : eulerPushforward = haarProb TauCeti.SU2 := by
  symm
  let A := StarAlgebra.adjoin ℂ (coordinateMonomials : Set (TauCeti.SU2 →ᵇ ℂ))
  have hspan : A.toSubalgebra.toSubmodule =
      Submodule.span ℂ (coordinateMonomials : Set (TauCeti.SU2 →ᵇ ℂ)) := by
    dsimp only [A]
    rw [StarAlgebra.adjoin_eq_span, Set.union_eq_left.2 star_coordinateMonomials_subset,
      Submonoid.closure_eq]
  have hmem (t : ℕ × ℕ × ℕ × ℕ) : boundedCoordinateMonomial t ∈ A :=
    StarAlgebra.subset_adjoin _ _ ⟨t, rfl⟩
  let t : TopologicalSpace TauCeti.SU2 := PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
  have hborel : @BorelSpace TauCeti.SU2 t inferInstance := TauCeti.SU2.instBorelSpace
  have hcompact : @CompactSpace TauCeti.SU2 t :=
    isCompact_iff_compactSpace.mp (Matrix.isCompact_specialUnitaryGroup (n := Fin 2) (𝕜 := ℂ))
  have hcount : @SecondCountableTopology TauCeti.SU2 t :=
    @EMetric.secondCountable_of_sigmaCompact _ _ (@CompactSpace.sigmaCompact _ _ hcompact)
  refine @ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    TauCeti.SU2 ℂ _ _ _ hborel _ hcount _ _ _ _ A ?_ ?_
  · intro g h hne
    by_cases ha : topEntry 0 g = topEntry 0 h
    · have hb : topEntry 1 g ≠ topEntry 1 h := fun hh => hne (eq_of_topRow_eq ha hh)
      refine ⟨_, ⟨_, StarSubalgebra.mem_map.mpr ⟨_, hmem (0, 0, 1, 0), rfl⟩, rfl⟩, ?_⟩
      simpa [boundedCoordinateMonomial_apply, coordinateMonomial,
        BoundedContinuousFunction.toContinuousMapStarₐ] using hb
    · refine ⟨_, ⟨_, StarSubalgebra.mem_map.mpr ⟨_, hmem (1, 0, 0, 0), rfl⟩, rfl⟩, ?_⟩
      simpa [boundedCoordinateMonomial_apply, coordinateMonomial,
        BoundedContinuousFunction.toContinuousMapStarₐ] using ha
  · intro f hf
    have h : f ∈ A.toSubalgebra.toSubmodule := hf
    rw [hspan] at h
    refine Submodule.span_induction ?_ ?_ ?_ ?_ h
    · rintro _ ⟨⟨a, b, c, d⟩, rfl⟩
      exact integral_coordinateMonomial_eq _ _ _ _
    · simp
    · intro f g _ _ hf hg
      simp only [FunLike.coe_add, Pi.add_apply]
      rw [integral_add (f.integrable (haarProb TauCeti.SU2)) (g.integrable (haarProb TauCeti.SU2)),
        integral_add (f.integrable eulerPushforward) (g.integrable eulerPushforward), hf, hg]
    · intro c f _ hf
      simp only [FunLike.coe_smul, Pi.smul_apply, integral_smul, hf]

end

end EulerHaar

/-- The pushforward of Euler-angle measure is the normalized Haar measure of `SU(2)`. -/
theorem haarProb_eq_map_eulerMeasure :
    haarProb TauCeti.SU2 = eulerMeasure.map (fun p => euler p.1 p.2.1 p.2.2) :=
  EulerHaar.eulerPushforward_eq_haarProb.symm

end SFVK.SU2
