/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Rotations about the coordinate axes

The rotation matrices about the third and second axes, in the convention of Edmonds,
*Angular Momentum in Quantum Mechanics*, §1.3, pp. 6–8.
-/

public noncomputable section

namespace SFVK.SU2

/-- The rotation matrix about the third axis through the angle `α`. -/
@[expose]
def rotationZ (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos α, -Real.sin α, 0; Real.sin α, Real.cos α, 0; 0, 0, 1]

/-- The entries of the rotation about the third axis. -/
theorem rotationZ_def (α : ℝ) :
    rotationZ α = !![Real.cos α, -Real.sin α, 0; Real.sin α, Real.cos α, 0; 0, 0, 1] :=
  (rfl)

/-- The rotation matrix about the second axis through the angle `β`. -/
@[expose]
def rotationY (β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos β, 0, Real.sin β; 0, 1, 0; -Real.sin β, 0, Real.cos β]

/-- The entries of the rotation about the second axis. -/
theorem rotationY_def (β : ℝ) :
    rotationY β = !![Real.cos β, 0, Real.sin β; 0, 1, 0; -Real.sin β, 0, Real.cos β] :=
  (rfl)

end SFVK.SU2
