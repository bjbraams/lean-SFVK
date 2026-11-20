/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU2.Coordinates
public import SFVK.SU2.Basic.SO3
public import TauCeti.RepresentationTheory.SU2.Adjoint

/-!
# Euler angles under the double cover of `SO(3)`

The three rotations are about the third, second, and third axes, in the order used by Edmonds,
*Angular Momentum in Quantum Mechanics*, §1.3, pp. 6–8. Tau Ceti's double cover `SU2.toSO3` uses
the Pauli basis, in which the positive `SU(2)` factor angles give negative rotation angles.
-/

public section

open Complex Matrix Set
open scoped ComplexConjugate Real

namespace SFVK.SU2

/-- The torus factor rotates about the third axis in Tau Ceti's Pauli coordinates. -/
private theorem toSO3_torusExp_half (α : ℝ) :
    (TauCeti.SU2.toSO3 (TauCeti.SU2.torusExp (α / 2)) : Matrix (Fin 3) (Fin 3) ℝ) =
      rotationZ (-α) := by
  have h : ((Circle.exp (α / 2) : ℂ) ^ 2) = Circle.exp α := by
    rw [sq, ← Circle.coe_mul, ← Circle.exp_add, add_halves]
  rw [TauCeti.SU2.torusExp_def, TauCeti.SU2.coe_toSO3_torusHom, h, rotationZ_def,
    Circle.coe_exp, Complex.exp_re, Complex.exp_im]
  simp

/-- The middle Euler factor rotates about the second axis in Tau Ceti's Pauli coordinates. -/
private theorem toSO3_eulerMiddle (β : ℝ) :
    (TauCeti.SU2.toSO3 (eulerMiddle β) : Matrix (Fin 3) (Fin 3) ℝ) = rotationY (-β) := by
  rw [TauCeti.SU2.coe_toSO3, TauCeti.pauliRotation_eq_iff]
  intro x
  have hcos : Real.cos β = Real.cos (β / 2) ^ 2 - Real.sin (β / 2) ^ 2 := by
    simpa only [mul_div_cancel₀ β (two_ne_zero : (2 : ℝ) ≠ 0)] using
      Real.cos_two_mul' (β / 2)
  have hsin : Real.sin β = 2 * Real.sin (β / 2) * Real.cos (β / 2) := by
    simpa only [mul_div_cancel₀ β (two_ne_zero : (2 : ℝ) ≠ 0)] using
      Real.sin_two_mul (β / 2)
  have hnorm : (Real.cos (β / 2) : ℂ) ^ 2 + (Real.sin (β / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (β / 2)
  rw [Submonoid.coe_inclusion, coe_eulerMiddle, rotationY_def, Real.cos_neg, Real.sin_neg,
    hcos, hsin]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    simp [TauCeti.pauli_apply, Matrix.mul_apply, dotProduct, Fin.sum_univ_two,
      Fin.sum_univ_three, Matrix.star_apply, -Complex.ofReal_sin, -Complex.ofReal_cos]
  · ring
  · linear_combination (x 1 : ℂ) * Complex.I * hnorm
  · linear_combination -(x 1 : ℂ) * Complex.I * hnorm
  · ring

/-- The Euler element maps to the product of three real rotations with negated angles. -/
theorem toSO3_euler (α β γ : ℝ) :
    (TauCeti.SU2.toSO3 (euler α β γ) : Matrix (Fin 3) (Fin 3) ℝ) =
      rotationZ (-α) * rotationY (-β) * rotationZ (-γ) := by
  rw [euler_def, map_mul, map_mul, Submonoid.coe_mul, Submonoid.coe_mul, toSO3_torusExp_half,
    toSO3_eulerMiddle, toSO3_torusExp_half]

/-- The rotations from the closed-middle-angle `SU(2)` chart cover `SO(3)`. -/
theorem exists_eq_rotationZ_mul_rotationY_mul_rotationZ
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ α β γ, α ∈ Ico 0 (2 * π) ∧ β ∈ Icc 0 π ∧ γ ∈ Ico (-(2 * π)) (2 * π) ∧
      (R : Matrix (Fin 3) (Fin 3) ℝ) = rotationZ (-α) * rotationY (-β) * rotationZ (-γ) := by
  obtain ⟨g, rfl⟩ := TauCeti.SU2.toSO3_surjective R
  obtain ⟨α, β, γ, hα, hβ, hγ, rfl⟩ := exists_euler_eq g
  exact ⟨α, β, γ, hα, hβ, hγ, toSO3_euler α β γ⟩

end SFVK.SU2
