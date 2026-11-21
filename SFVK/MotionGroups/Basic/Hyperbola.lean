/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.RepresentationTheory.Continuous.Basic
public import SFVK.MotionGroups.Basic.Group

/-!
# The hyperbola model of `ISO(1,1)`

Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 1, §4.2.3 (1)–(3),
pp. 173–174: for complex `R`, `ISO(1,1)` acts on functions on the branch
`x = (cosh θ, sinh θ)` of the hyperbola `x₁² - x₂² = 1` by
`(T_R(g) Φ)(θ) = e^{-R[x, a]} Φ(θ - s)`, `[x, a] = x₁ a₁ - x₂ a₂`, for `g = (a, s)`. The
two-sided Laplace transform `F(λ) = ∫ Φ(θ) e^{λθ} dθ` gives the realization of §4.2.4 (1),
p. 175.

## Main definitions

* `SFVK.MotionGroups.hyperbolaAction`: the pointwise operator.
* `SFVK.MotionGroups.hyperbolaRep`: the representation on `L²(ℝ)` agreeing almost everywhere
  with it and with continuous orbit maps, when one exists, and the trivial one otherwise.
* `SFVK.MotionGroups.fourierLaplace`: the two-sided Laplace transform.
-/

public noncomputable section

open Complex MeasureTheory

namespace SFVK.MotionGroups

/-- The hyperbola model `(T_R(g) Φ)(θ) = e^{-R(a₁ cosh θ - a₂ sinh θ)} Φ(θ - s)` for
`g = (a, s)`. -/
@[expose]
def hyperbolaAction (R : ℂ) (g : ISO11) (Φ : ℝ → ℂ) (θ : ℝ) : ℂ :=
  Complex.exp (-R * (g.a.1 * Real.cosh θ - g.a.2 * Real.sinh θ : ℝ)) * Φ (θ - g.s)

/-- The hyperbola model multiplies by its exponential weight and shifts the rapidity. -/
theorem hyperbolaAction_def (R : ℂ) (g : ISO11) (Φ : ℝ → ℂ) (θ : ℝ) :
    hyperbolaAction R g Φ θ =
      Complex.exp (-R * (g.a.1 * Real.cosh θ - g.a.2 * Real.sinh θ : ℝ)) * Φ (θ - g.s) :=
  rfl

/-- The identity acts trivially in the hyperbola model. -/
@[simp]
theorem hyperbolaAction_one (R : ℂ) (Φ : ℝ → ℂ) : hyperbolaAction R 1 Φ = Φ := by
  funext θ
  simp [hyperbolaAction]

/-- A representation on `L²(ℝ)` realizes the hyperbola model when it agrees almost everywhere
with the pointwise formula and has continuous orbit maps. -/
@[expose]
def IsHyperbolaRealization (R : ℂ)
    (U : ContRepresentation ℂ ISO11 (Lp ℂ 2 (volume : Measure ℝ))) : Prop :=
  (∀ g f, (U g f : ℝ → ℂ) =ᵐ[volume] hyperbolaAction R g f) ∧ ∀ f, Continuous fun g => U g f

/-- The hyperbola model on `L²(ℝ)`: the realization when one exists, and the trivial
representation otherwise. -/
@[expose]
def hyperbolaRep (R : ℂ) : ContRepresentation ℂ ISO11 (Lp ℂ 2 (volume : Measure ℝ)) :=
  open Classical in
  if h : ∃ U, IsHyperbolaRealization R U then h.choose
  else ContRepresentation.trivial ℂ ISO11 _

/-- When a realization exists, `hyperbolaRep R` is one. -/
theorem isHyperbolaRealization_hyperbolaRep {R : ℂ} (h : ∃ U, IsHyperbolaRealization R U) :
    IsHyperbolaRealization R (hyperbolaRep R) := by
  unfold hyperbolaRep
  split_ifs with h'
  · exact h'.choose_spec
  · exact absurd h h'

/-- The two-sided Laplace transform `F(λ) = ∫ Φ(θ) e^{λθ} dθ`, Vilenkin–Klimyk Vol. 1 §4.2.4 (1),
p. 175. -/
@[expose]
def fourierLaplace (Φ : ℝ → ℂ) (lam : ℂ) : ℂ := ∫ θ, Φ θ * Complex.exp (lam * θ)

/-- The two-sided Laplace transform integrates against the exponential with positive spectral sign.
-/
theorem fourierLaplace_def (Φ : ℝ → ℂ) (lam : ℂ) :
    fourierLaplace Φ lam = ∫ θ, Φ θ * Complex.exp (lam * θ) :=
  rfl

end SFVK.MotionGroups
