/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Exp
public import TauCeti.RepresentationTheory.Continuous.Basic
public import SFVK.MotionGroups.Basic.Group

/-!
# The circle models of the plane motion group

For complex `R`, the circle model of `M(2)` acts on functions on `𝕋 = ℝ/2πℤ` by
`(T_R(g) f)(ψ) = e^{iR⟨a, e(ψ)⟩} f(ψ - α)` for `g = (a, k_α)`. It is Vilenkin–Klimyk's `T_{iR}`
(*Representation of Lie Groups and Special Functions*, Vol. 1, §4.1.2 (2), p. 166, where the
exponent is `R r cos(ψ - φ)`) and Miller's representation `(ρ)` with `ρ = R` (*Lie Theory and
Special Functions*, §3-8 (3.56), p. 73). For real `R` it is the sphere model
`(T_R(g) f)(ξ) = e^{iR⟨a, ξ⟩} f(k⁻¹ξ)` of `M(n)` restricted to `n = 2`.

## Main definitions

* `SFVK.MotionGroups.circleAction`: the pointwise operator on functions on `𝕋`.
* `SFVK.MotionGroups.circleRep`: the representation on `L²(𝕋)` that agrees almost everywhere
  with `circleAction` and has continuous orbit maps, when one exists, and the trivial
  representation otherwise.
* `SFVK.MotionGroups.motionAction`: the sphere model of `M(n)` on functions on `ℝⁿ`.
-/

public noncomputable section

open AddCircle Complex MeasureTheory
open scoped Real InnerProductSpace

namespace SFVK.MotionGroups

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The circle model `(T_R(g) f)(ψ) = e^{iR⟨a, e(ψ)⟩} f(ψ - α)` for `g = (a, k)`, `α` the
angle of `k`, and complex `R`. -/
@[expose]
def circleAction (R : ℂ) (g : MotionGroup 2) (f : 𝕋 → ℂ) (ψ : 𝕋) : ℂ :=
  Complex.exp (I * R * (⟪g.a, unitVec ψ⟫_ℝ : ℝ)) * f (ψ - rotAngle g.k)

/-- The plane motion acts by a plane-wave multiplier and a shift of the circle argument. -/
theorem circleAction_def (R : ℂ) (g : MotionGroup 2) (f : 𝕋 → ℂ) (ψ : 𝕋) :
    circleAction R g f ψ =
      Complex.exp (I * R * (⟪g.a, unitVec ψ⟫_ℝ : ℝ)) * f (ψ - rotAngle g.k) :=
  rfl

/-- A representation on `L²(𝕋)` realizes `T_R` when it agrees almost everywhere with the
pointwise formula and has continuous orbit maps. -/
@[expose]
def IsCircleRealization (R : ℂ)
    (U : ContRepresentation ℂ (MotionGroup 2) (Lp ℂ 2 (haarAddCircle (T := 2 * π)))) : Prop :=
  (∀ g f, (U g f : 𝕋 → ℂ) =ᵐ[haarAddCircle] circleAction R g f) ∧
    ∀ f, Continuous fun g => U g f

/-- The circle model on `L²(𝕋)`: the realization of `circleAction R` when one exists, and the
trivial representation otherwise. -/
@[expose]
def circleRep (R : ℂ) :
    ContRepresentation ℂ (MotionGroup 2) (Lp ℂ 2 (haarAddCircle (T := 2 * π))) :=
  open Classical in
  if h : ∃ U, IsCircleRealization R U then h.choose
  else ContRepresentation.trivial ℂ (MotionGroup 2) _

/-- When a realization exists, `circleRep R` is one. -/
theorem isCircleRealization_circleRep {R : ℂ} (h : ∃ U, IsCircleRealization R U) :
    IsCircleRealization R (circleRep R) := by
  unfold circleRep
  split_ifs with h'
  · exact h'.choose_spec
  · exact absurd h h'

/-- The sphere model of `M(n)`: `(a, k)` acts by `e^{iR⟨a, ξ⟩} f(k⁻¹ ξ)`. -/
@[expose]
def motionAction {n : ℕ} (R : ℝ) (g : MotionGroup n) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  Complex.exp ((R * ⟪g.a, ξ⟫_ℝ : ℝ) * Complex.I) * f (rotE g.k⁻¹ ξ)

/-- The action on a circle vector is the circle model evaluated at a chosen almost-everywhere
representative. -/
theorem motionAction_def {n : ℕ} (R : ℝ) (g : MotionGroup n) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    motionAction R g f ξ = Complex.exp ((R * ⟪g.a, ξ⟫_ℝ : ℝ) * Complex.I) * f (rotE g.k⁻¹ ξ) :=
  rfl

end SFVK.MotionGroups
