/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SFVK.SU2.Coordinates
public import TauCeti.RepresentationTheory.SU2.Adjoint

/-!
# Euler angles under the double cover of `SO(3)`

The three rotations are about the third, second, and third axes, in the order
used by Edmonds, §1.3, pp. 6–8. Tau Ceti's double cover `SU2.toSO3` uses the Pauli
basis, in which the positive `SU(2)` factor angles give negative rotation angles.
-/

public noncomputable section

open Set
open scoped Real

namespace SFVK.SU2

/-- The rotation matrix about the third axis through the angle `α`. -/
def rotZ (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos α, -Real.sin α, 0; Real.sin α, Real.cos α, 0; 0, 0, 1]

/-- The entries of the rotation about the third axis. -/
theorem rotZ_def (α : ℝ) :
    rotZ α = !![Real.cos α, -Real.sin α, 0; Real.sin α, Real.cos α, 0; 0, 0, 1] :=
  (rfl)

/-- The rotation matrix about the second axis through the angle `β`. -/
def rotY (β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos β, 0, Real.sin β; 0, 1, 0; -Real.sin β, 0, Real.cos β]

/-- The entries of the rotation about the second axis. -/
theorem rotY_def (β : ℝ) :
    rotY β = !![Real.cos β, 0, Real.sin β; 0, 1, 0; -Real.sin β, 0, Real.cos β] :=
  (rfl)

/-- The Euler element maps to the product of three real rotations with negated angles. -/
theorem toSO3_eulerD (α β γ : ℝ) :
    (TauCeti.SU2.toSO3 (eulerD α β γ) : Matrix (Fin 3) (Fin 3) ℝ) =
      rotZ (-α) * rotY (-β) * rotZ (-γ) := by
  sorry

/-- The rotations from the closed-middle-angle `SU(2)` chart cover `SO(3)`. -/
theorem exists_eq_rotZ_mul_rotY_mul_rotZ
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ α β γ, α ∈ Ico 0 (2 * π) ∧ β ∈ Icc 0 π ∧ γ ∈ Ico (-(2 * π)) (2 * π) ∧
      (R : Matrix (Fin 3) (Fin 3) ℝ) = rotZ (-α) * rotY (-β) * rotZ (-γ) := by
  obtain ⟨g, rfl⟩ := TauCeti.SU2.toSO3_surjective R
  obtain ⟨α, β, γ, hα, hβ, hγ, rfl⟩ := exists_eulerD_eq_and_bijOn.1 g
  exact ⟨α, β, γ, hα, hβ, hγ, toSO3_eulerD α β γ⟩

end SFVK.SU2
