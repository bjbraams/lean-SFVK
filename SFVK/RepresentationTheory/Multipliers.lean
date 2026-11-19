/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic

/-!
# Multiplier actions

For a left action of `G` on `X`, a multiplier acts by multiplication followed by pullback
along the inverse group element. The convention comes from Vilenkin–Klimyk, Vol. 1,
§2.1.6 (4), p. 80. The cocycle law is equivalent to the operator composition law.
The Radon–Nikodym density is taken for the pushforward by the forward action.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace SFVK

variable {G X : Type*} [Group G] [MulAction G X]

/-- The pushforward of `μ` by each group element has density `ρ g` with respect to `μ`. -/
def IsQuasiInvariantWith [MeasurableSpace X] (μ : Measure X) (ρ : G → X → ℝ≥0∞) : Prop :=
  ∀ g, Measure.map (fun x => g • x) μ = μ.withDensity (ρ g)

/-- The pushforward characterization of quasi-invariance with a given density. -/
theorem isQuasiInvariantWith_iff [MeasurableSpace X] {μ : Measure X} {ρ : G → X → ℝ≥0∞} :
    IsQuasiInvariantWith μ ρ ↔ ∀ g, Measure.map (fun x => g • x) μ = μ.withDensity (ρ g) :=
  Iff.rfl

/-- Multiply the pullback of `f` under `g⁻¹` by the function `α g`. -/
def multiplierAction (α : G → X → ℂ) (g : G) (f : X → ℂ) (x : X) : ℂ :=
  α g x * f (g⁻¹ • x)

/-- The value of the multiplier action at a point. -/
theorem multiplierAction_def (α : G → X → ℂ) (g : G) (f : X → ℂ) (x : X) :
    multiplierAction α g f x = α g x * f (g⁻¹ • x) :=
  (rfl)

/-- The normalized cocycle law for a multiplier of a left group action. -/
def IsMultiplierCocycle (α : G → X → ℂ) : Prop :=
  (∀ x, α 1 x = 1) ∧ ∀ g h x, α (g * h) x = α g x * α h (g⁻¹ • x)

/-- A pointwise multiplier gives a representation on functions exactly when it is a cocycle. -/
theorem multiplierAction_law_iff (α : G → X → ℂ) :
    ((∀ f x, multiplierAction α 1 f x = f x) ∧
      ∀ g h f x, multiplierAction α (g * h) f x =
        multiplierAction α g (multiplierAction α h f) x) ↔ IsMultiplierCocycle α := by
  constructor
  · rintro ⟨h₁, hmul⟩
    exact ⟨fun x => by simpa [multiplierAction_def] using h₁ (fun _ => 1) x,
      fun g h x => by simpa [multiplierAction_def] using hmul g h (fun _ => 1) x⟩
  · rintro ⟨h₁, hmul⟩
    exact ⟨fun f x => by simp [multiplierAction_def, h₁],
      fun g h f x => by simp [multiplierAction_def, hmul, mul_smul, mul_assoc]⟩

/-- The densities of a quasi-invariant σ-finite measure satisfy the cocycle law almost
everywhere for each pair of group elements. -/
theorem IsQuasiInvariantWith.cocycle [MeasurableSpace X] [MeasurableConstSMul G X]
    {μ : Measure X} [SigmaFinite μ] {ρ : G → X → ℝ≥0∞} (hρ : IsQuasiInvariantWith μ ρ)
    (hρm : ∀ g, Measurable (ρ g)) (g h : G) :
    ∀ᵐ x ∂μ, ρ (g * h) x = ρ g x * ρ h (g⁻¹ • x) := by
  sorry

/-- The almost-everywhere multiplier formula determines an operator-valued representation
on `L²` uniquely. -/
theorem multiplierRep_unique [MeasurableSpace X] {μ : Measure X} {α : G → X → ℂ}
    {U V : ContRepresentation ℂ G (Lp ℂ 2 μ)}
    (hU : ∀ g f, (U g f : X → ℂ) =ᵐ[μ] multiplierAction α g f)
    (hV : ∀ g f, (V g f : X → ℂ) =ᵐ[μ] multiplierAction α g f) : U = V := by
  apply DFunLike.ext
  intro g
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((hU g f).trans (hV g f).symm)

/-- A measurable multiplier cocycle acts unitarily on `L²(μ)` exactly when its squared modulus
agrees almost everywhere with the Radon–Nikodym density of the action. -/
theorem exists_isUnitary_multiplierAction_iff [MeasurableSpace X] [MeasurableConstSMul G X]
    {μ : Measure X} [SigmaFinite μ] {ρ : G → X → ℝ≥0∞} {α : G → X → ℂ}
    (hα : IsMultiplierCocycle α) (hαm : ∀ g, Measurable (α g)) (hρm : ∀ g, Measurable (ρ g))
    (hρ : IsQuasiInvariantWith μ ρ) :
    (∃ U : ContRepresentation ℂ G (Lp ℂ 2 μ),
        U.IsUnitary ∧ ∀ g f, (U g f : X → ℂ) =ᵐ[μ] multiplierAction α g f) ↔
      ∀ g, ∀ᵐ x ∂μ, ‖α g x‖ₑ ^ 2 = ρ g x := by
  sorry

end SFVK
