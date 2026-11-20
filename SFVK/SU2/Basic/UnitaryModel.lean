/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.RepresentationTheory.SU2.Exhaustion
public import TauCeti.RepresentationTheory.Continuous.Transport

/-!
# The symmetric powers of the defining representation of `SU(2)`

Edmonds's normalized monomials `z₁^i z₂^(d-i) / √(i! (d-i)!)` (*Angular Momentum in Quantum
Mechanics*, p. 56) give the basis of the spin `d/2` representation. The diagonal change of basis
`monomialScale d` transports Tau Ceti's `SU2.symPowerModel` from monomial coordinates to the
coordinates in the normalized basis. The index `i : Fin (d + 1)` has magnetic weight `i - d/2`,
the order of Tau Ceti's weight basis.
-/

public noncomputable section

open TauCeti TauCeti.SU2

namespace SFVK.SU2

/-- The magnetic weight `i - d/2` of the `i`-th vector in spin `d/2`. -/
@[expose]
def magneticWeight (d i : ℕ) : ℝ := i - d / 2

/-- The magnetic weight in terms of its natural indices. -/
theorem magneticWeight_def (d i : ℕ) : magneticWeight d i = (i : ℝ) - (d : ℝ) / 2 := (rfl)

/-- The norm of the monomial `z₁^i z₂^(d-i)` in the factorial normalization. -/
@[expose]
def monomialNorm (d : ℕ) (i : Fin (d + 1)) : ℝ :=
  Real.sqrt ((i : ℕ).factorial * (d - i).factorial)

/-- The factorial expression for the monomial norm. -/
theorem monomialNorm_def (d : ℕ) (i : Fin (d + 1)) :
    monomialNorm d i = Real.sqrt ((i : ℕ).factorial * (d - i).factorial) := (rfl)

/-- The monomial norm is positive for every weight index. -/
theorem monomialNorm_pos (d : ℕ) (i : Fin (d + 1)) : 0 < monomialNorm d i :=
  Real.sqrt_pos.2 (by positivity)

/-- The diagonal change from monomial coefficients to normalized monomial coefficients. -/
@[expose]
def monomialScale (d : ℕ) :
    EuclideanSpace ℂ (Fin (d + 1)) ≃L[ℂ] EuclideanSpace ℂ (Fin (d + 1)) :=
  LinearEquiv.toContinuousLinearEquiv <|
    (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.equiv
      ((EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.unitsSMul fun i =>
        Units.mk0 (monomialNorm d i : ℂ) (Complex.ofReal_ne_zero.2 (monomialNorm_pos d i).ne'))
      (Equiv.refl _)

/-- The change of basis multiplies the `i`-th unit vector by the corresponding monomial norm. -/
theorem monomialScale_single (d : ℕ) (i : Fin (d + 1)) :
    monomialScale d (EuclideanSpace.single i 1) =
      (monomialNorm d i : ℂ) • EuclideanSpace.single i 1 := by
  classical
  simp only [monomialScale, LinearEquiv.coe_toContinuousLinearEquiv',
    ← EuclideanSpace.basisFun_apply, ← OrthonormalBasis.coe_toBasis, Module.Basis.equiv_apply,
    Equiv.refl_apply, Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0]

/-- The spin `d/2` representation in the normalized weight basis. -/
@[expose]
def unitaryModel (d : ℕ) :
    ContRepresentation ℂ TauCeti.SU2 (EuclideanSpace ℂ (Fin (d + 1))) :=
  (monomialScale d).congr (symPowerModel d)

/-- The action in the normalized basis is the diagonal conjugate of Tau Ceti's action. -/
theorem unitaryModel_apply (d : ℕ) (g : TauCeti.SU2) (v : EuclideanSpace ℂ (Fin (d + 1))) :
    unitaryModel d g v = monomialScale d (symPowerModel d g ((monomialScale d).symm v)) :=
  (monomialScale d).congr_apply (symPowerModel d) g v

/-- The normalized symmetric powers are continuous in operator norm. -/
theorem continuous_unitaryModel (d : ℕ) : Continuous (unitaryModel d) :=
  (monomialScale d).continuous_congr (continuous_symPowerModel d)

/-- The normalized symmetric powers are irreducible. -/
theorem isIrreducible_unitaryModel (d : ℕ) :
    (unitaryModel d).toRepresentation.IsIrreducible :=
  (monomialScale d).isIrreducible_congr (isIrreducible_symPowerModel d)

end SFVK.SU2
