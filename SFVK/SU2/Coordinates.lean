/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.RepresentationTheory.SU2.Borel
public import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Euler coordinates on `SU(2)`

The middle factor is the real matrix in Edmonds (4.1.13), p. 56. The torus factors
use Tau Ceti's `SU2.torusExp`. The Euler-angle Haar density is Vilenkin–Klimyk,
Vol. 1, §6.1.4 (1), p. 275, with the middle factor in Edmonds's convention.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate Real
open TauCeti TauCeti.SU2

namespace SFVK.SU2

/-- The element of `SU(2)` with top row `[a, b]` and bottom row `[-conj b, conj a]`. -/
def ofPair (a b : ℂ) (h : normSq a + normSq b = 1) : TauCeti.SU2 :=
  ⟨!![a, b; -conj b, conj a], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    have hc : a * conj a + b * conj b = 1 := by
      rw [mul_conj, mul_conj, ← ofReal_add, h, ofReal_one]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, hc] <;>
        simp_all [mul_comm, add_comm]
    · simp [Matrix.det_fin_two_of]
      linear_combination hc⟩

/-- The underlying matrix of the pair constructor. -/
@[simp]
theorem coe_ofPair (a b : ℂ) (h : normSq a + normSq b = 1) :
    (ofPair a b h : Matrix (Fin 2) (Fin 2) ℂ) = !![a, b; -conj b, conj a] :=
  (rfl)

/-- Edmonds's middle factor, the real rotation by the half-angle `β/2`. -/
noncomputable def bBeta (β : ℝ) : TauCeti.SU2 :=
  ofPair (Real.cos (β / 2)) (Real.sin (β / 2)) (by
    rw [normSq_ofReal, normSq_ofReal]
    nlinarith [Real.cos_sq_add_sin_sq (β / 2)])

/-- The entries of the middle Euler factor. -/
@[simp]
theorem coe_bBeta (β : ℝ) :
    (bBeta β : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.cos (β / 2) : ℂ), (Real.sin (β / 2) : ℂ);
        -(Real.sin (β / 2) : ℂ), (Real.cos (β / 2) : ℂ)] := by
  simp only [bBeta, coe_ofPair, Complex.conj_ofReal]

/-- Edmonds's Euler element with angles `(α, β, γ)`. -/
noncomputable def eulerD (α β γ : ℝ) : TauCeti.SU2 :=
  torusExp (α / 2) * bBeta β * torusExp (γ / 2)

/-- The three factors in the Euler parametrization. -/
theorem eulerD_def (α β γ : ℝ) :
    eulerD α β γ = torusExp (α / 2) * bBeta β * torusExp (γ / 2) :=
  (rfl)

/-- The parameter box on which both entries in the top row are nonzero. -/
noncomputable def eulerBox : Set (ℝ × ℝ × ℝ) :=
  Ico 0 (2 * π) ×ˢ Ioo 0 π ×ˢ Ico (-(2 * π)) (2 * π)

/-- Membership in the open-middle-angle Euler box. -/
theorem mem_eulerBox {p : ℝ × ℝ × ℝ} :
    p ∈ eulerBox ↔ p.1 ∈ Ico 0 (2 * π) ∧ p.2.1 ∈ Ioo 0 π ∧
      p.2.2 ∈ Ico (-(2 * π)) (2 * π) :=
  Iff.rfl

/-- With the middle angle allowed to reach its endpoints, the Euler coordinates cover `SU(2)`.
On the open-middle-angle box they give a bijection to matrices with two nonzero top entries. -/
theorem exists_eulerD_eq_and_bijOn :
    (∀ g : TauCeti.SU2, ∃ α β γ, α ∈ Ico 0 (2 * π) ∧ β ∈ Icc 0 π ∧
      γ ∈ Ico (-(2 * π)) (2 * π) ∧ eulerD α β γ = g) ∧
    BijOn (fun p : ℝ × ℝ × ℝ => eulerD p.1 p.2.1 p.2.2) eulerBox
      {g : TauCeti.SU2 | (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 *
        (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 ≠ 0} := by
  sorry

/-- The probability density in Euler angles is `sin β / (16 * π²)` on the Euler box. -/
noncomputable def eulerMeasure : Measure (ℝ × ℝ × ℝ) :=
  ENNReal.ofReal (16 * π ^ 2)⁻¹ •
    (volume.restrict eulerBox).withDensity fun p => ENNReal.ofReal (Real.sin p.2.1)

/-- The weighted restriction of Lebesgue measure that defines `eulerMeasure`. -/
theorem eulerMeasure_def :
    eulerMeasure = ENNReal.ofReal (16 * π ^ 2)⁻¹ •
      (volume.restrict eulerBox).withDensity (fun p => ENNReal.ofReal (Real.sin p.2.1)) :=
  (rfl)

/-- The pushforward of Euler-angle measure is the normalized Haar measure of `SU(2)`. -/
theorem haarProb_eq_map_eulerMeasure :
    haarProb TauCeti.SU2 = eulerMeasure.map (fun p => eulerD p.1 p.2.1 p.2.2) := by
  sorry

end SFVK.SU2
