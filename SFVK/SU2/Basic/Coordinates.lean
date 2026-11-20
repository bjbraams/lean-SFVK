/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.RepresentationTheory.SU2.Borel
public import TauCeti.RepresentationTheory.Compact.Haar

/-!
# Euler coordinates on `SU(2)`

The Euler element `euler α β γ` is `torusExp (α/2) * eulerMiddle β * torusExp (γ/2)`, where the
middle factor is the real matrix of Edmonds, *Angular Momentum in Quantum Mechanics*, (4.1.13),
p. 56, and the torus factors are Tau Ceti's `SU2.torusExp`. The Euler-angle measure has density
`sin β / (16π²)` on the box `0 ≤ α < 2π`, `0 < β < π`, `-2π ≤ γ < 2π`, as in Vilenkin–Klimyk,
*Representation of Lie Groups and Special Functions*, Vol. 1, §6.1.4 (1), p. 275, with the middle
factor in Edmonds's convention.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate Real
open TauCeti TauCeti.SU2

namespace SFVK.SU2

/-- The element of `SU(2)` with top row `[a, b]` and bottom row `[-conj b, conj a]`. -/
@[expose]
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

/-- Edmonds's middle Euler factor, the real rotation by the half-angle `β/2`. -/
@[expose]
noncomputable def eulerMiddle (β : ℝ) : TauCeti.SU2 :=
  ofPair (Real.cos (β / 2)) (Real.sin (β / 2)) (by
    rw [normSq_ofReal, normSq_ofReal]
    nlinarith [Real.cos_sq_add_sin_sq (β / 2)])

/-- The entries of the middle Euler factor. -/
@[simp]
theorem coe_eulerMiddle (β : ℝ) :
    (eulerMiddle β : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(Real.cos (β / 2) : ℂ), (Real.sin (β / 2) : ℂ);
        -(Real.sin (β / 2) : ℂ), (Real.cos (β / 2) : ℂ)] := by
  simp only [eulerMiddle, coe_ofPair, Complex.conj_ofReal]

/-- Edmonds's Euler element with angles `(α, β, γ)`. -/
@[expose]
noncomputable def euler (α β γ : ℝ) : TauCeti.SU2 :=
  torusExp (α / 2) * eulerMiddle β * torusExp (γ / 2)

/-- The three factors in the Euler parametrization. -/
theorem euler_def (α β γ : ℝ) :
    euler α β γ = torusExp (α / 2) * eulerMiddle β * torusExp (γ / 2) :=
  (rfl)

/-- The parameter box on which both entries in the top row are nonzero. -/
@[expose]
noncomputable def eulerBox : Set (ℝ × ℝ × ℝ) :=
  Ico 0 (2 * π) ×ˢ Ioo 0 π ×ˢ Ico (-(2 * π)) (2 * π)

/-- Membership in the open-middle-angle Euler box. -/
theorem mem_eulerBox {p : ℝ × ℝ × ℝ} :
    p ∈ eulerBox ↔ p.1 ∈ Ico 0 (2 * π) ∧ p.2.1 ∈ Ioo 0 π ∧
      p.2.2 ∈ Ico (-(2 * π)) (2 * π) :=
  Iff.rfl

/-- The probability density in Euler angles is `sin β / (16 * π²)` on the Euler box. -/
@[expose]
noncomputable def eulerMeasure : Measure (ℝ × ℝ × ℝ) :=
  ENNReal.ofReal (16 * π ^ 2)⁻¹ •
    (volume.restrict eulerBox).withDensity fun p => ENNReal.ofReal (Real.sin p.2.1)

/-- The weighted restriction of Lebesgue measure that defines `eulerMeasure`. -/
theorem eulerMeasure_def :
    eulerMeasure = ENNReal.ofReal (16 * π ^ 2)⁻¹ •
      (volume.restrict eulerBox).withDensity (fun p => ENNReal.ofReal (Real.sin p.2.1)) :=
  (rfl)

end SFVK.SU2
