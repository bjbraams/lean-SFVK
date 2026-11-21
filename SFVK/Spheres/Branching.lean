/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.Spheres.Addition

/-!
# Branching of spherical harmonics from `ℝ^{m+1}` to `ℝᵐ`

For `h` harmonic of degree `k` on `ℝᵐ`, the polynomial
`|x|^{l-k} ω_{m+1+2k,l-k}(x_{m+1}/|x|) h(x₁, …, x_m)` is harmonic of degree `l` on `ℝ^{m+1}`; the
harmonics of degree `l` on `ℝ^{m+1}` are the direct sum of these images over `k ≤ l`, and the
branching map multiplies `L²` norms by an explicit constant. Iterating gives the
Gel'fand–Tsetlin basis of Vilenkin–Klimyk. The dimensions are obtained from Tau Ceti's
Fischer decomposition and the Pascal recurrence for multiset coefficients.

Sources: Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2, §9.3.1
(1)–(5), pp. 44–46 (the orthonormal basis of `L²(S^{n-1})` built from Gegenbauer polynomials);
Wawrzyńczyk, *Group Representations and Special Functions*, (9.2.9), p. 330.
-/

public noncomputable section

open MeasureTheory

namespace SFVK.Spheres

/-- **Branching harmonics are harmonic.** For `m ≥ 1`, `k ≤ l` and `h ∈ H_k(ℝᵐ)`,
`branchHarmonic m l k h ∈ H_l(ℝ^{m+1})`. -/
theorem branchHarmonic_mem_harmonicSubmodule {m l k : ℕ} (hm : 1 ≤ m) (hkl : k ≤ l)
    {h : MvPolynomial (Fin m) ℝ} (hh : h ∈ MvPolynomial.harmonicSubmodule (Fin m) ℝ k) :
    branchHarmonic m l k h ∈ MvPolynomial.harmonicSubmodule (Fin (m + 1)) ℝ l := by
  sorry

/-- **Branching decomposition, spanning.** For `m ≥ 1`, `H_l(ℝ^{m+1})` is the sum over `k ≤ l`
of the images of `H_k(ℝᵐ)` under the branching maps. -/
theorem harmonicSubmodule_eq_iSup_map_branchHarmonic {m : ℕ} (hm : 1 ≤ m) (l : ℕ) :
    MvPolynomial.harmonicSubmodule (Fin (m + 1)) ℝ l =
      ⨆ k : Fin (l + 1),
        (MvPolynomial.harmonicSubmodule (Fin m) ℝ k).map (branchHarmonic m l k) := by
  sorry

/-- **Branching decomposition, independence.** For `m ≥ 1` the images of the `H_k(ℝᵐ)`, `k ≤ l`,
are independent. -/
theorem iSupIndep_map_branchHarmonic {m : ℕ} (hm : 1 ≤ m) (l : ℕ) :
    iSupIndep fun k : Fin (l + 1) =>
      (MvPolynomial.harmonicSubmodule (Fin m) ℝ k).map (branchHarmonic m l k) := by
  sorry

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
