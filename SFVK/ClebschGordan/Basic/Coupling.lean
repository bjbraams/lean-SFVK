/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.ClebschGordan.Basic.Coefficients
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The coupled vectors

The coupled vector `w_{jm} = Σ (j₁ m₁ j₂ m₂ | j m) e_{m₁} ⊗ e_{m₂}` (Edmonds, *Angular Momentum
in Quantum Mechanics*, (3.5.1), p. 37) in the algebraic tensor product of the spaces of the
unitary models of spins `d₁/2` and `d₂/2`, on which Tau Ceti's `ContRepresentation.tprod` acts.
-/

public noncomputable section

open scoped TensorProduct

namespace SFVK.ClebschGordan

/-- The coupled vector of spin `d/2` and index `i` in `ℂ^{d₁+1} ⊗ ℂ^{d₂+1}`. -/
@[expose]
def coupledVector (d₁ d₂ d : ℕ) (i : Fin (d + 1)) :
    EuclideanSpace ℂ (Fin (d₁ + 1)) ⊗[ℂ] EuclideanSpace ℂ (Fin (d₂ + 1)) :=
  ∑ i₁ : Fin (d₁ + 1), ∑ i₂ : Fin (d₂ + 1),
    (clebschGordan d₁ d₂ d i₁ i₂ i : ℂ) •
      (EuclideanSpace.single i₁ (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single i₂ (1 : ℂ))

/-- The coupled vector is the Clebsch–Gordan expansion in the tensor products of the monomial basis
vectors. -/
theorem coupledVector_def (d₁ d₂ d : ℕ) (i : Fin (d + 1)) :
    coupledVector d₁ d₂ d i =
      ∑ i₁ : Fin (d₁ + 1), ∑ i₂ : Fin (d₂ + 1),
        (clebschGordan d₁ d₂ d i₁ i₂ i : ℂ) •
          (EuclideanSpace.single i₁ (1 : ℂ) ⊗ₜ[ℂ] EuclideanSpace.single i₂ (1 : ℂ)) :=
  rfl

end SFVK.ClebschGordan
