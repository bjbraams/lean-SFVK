/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Function.L2Space
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Multiplier actions and quasi-invariant measures

For a left action of `G` on `X`, a multiplier `α : G → X → ℂ` acts on functions by
multiplication followed by pullback along the inverse group element,
`(T(g) f)(x) = α(g, x) f(g⁻¹ • x)`, as in Vilenkin–Klimyk, *Representation of Lie Groups and
Special Functions*, Vol. 1, §2.1.6 (4), p. 80. The cocycle law for `α` is equivalent to the
composition law for the operators.

A measure is quasi-invariant with density `ρ` when the pushforward by each group element has
density `ρ g`; the multiplier action is unitary on `L²` exactly when `|α g|² = ρ g` almost
everywhere.
-/

public section

open MeasureTheory
open scoped ENNReal

variable {G X : Type*} [Group G] [MulAction G X]

namespace MeasureTheory.Measure

/-- The pushforward of `μ` by each group element has density `ρ g` with respect to `μ`. -/
@[expose]
def IsQuasiInvariantWith [MeasurableSpace X] (μ : Measure X) (ρ : G → X → ℝ≥0∞) : Prop :=
  ∀ g, Measure.map (fun x => g • x) μ = μ.withDensity (ρ g)

/-- The pushforward characterization of quasi-invariance with a given density. -/
theorem isQuasiInvariantWith_iff [MeasurableSpace X] {μ : Measure X} {ρ : G → X → ℝ≥0∞} :
    μ.IsQuasiInvariantWith ρ ↔ ∀ g, Measure.map (fun x => g • x) μ = μ.withDensity (ρ g) :=
  Iff.rfl

/-- The densities of a quasi-invariant σ-finite measure satisfy the cocycle law almost
everywhere for each pair of group elements. -/
theorem IsQuasiInvariantWith.cocycle [MeasurableSpace X] [MeasurableConstSMul G X]
    {μ : Measure X} [SigmaFinite μ] {ρ : G → X → ℝ≥0∞} (hρ : μ.IsQuasiInvariantWith ρ)
    (hρm : ∀ g, Measurable (ρ g)) (g h : G) :
    ∀ᵐ x ∂μ, ρ (g * h) x = ρ g x * ρ h (g⁻¹ • x) := by
  have hcomp : Measurable (fun x : X => ρ h (g⁻¹ • x)) :=
    (hρm h).comp (measurable_const_smul g⁻¹)
  apply (withDensity_eq_iff_of_sigmaFinite (hρm (g * h)).aemeasurable
    ((hρm g).mul hcomp).aemeasurable).mp
  have hmap : (μ.map (fun x => h • x)).map (fun x => g • x) =
      μ.map (fun x => (g * h) • x) := by
    simp only [Measure.map_map (measurable_const_smul g) (measurable_const_smul h),
      Function.comp_def, mul_smul]
  have hpush : (μ.withDensity (ρ h)).map (fun x => g • x) =
      (μ.map (fun x => g • x)).withDensity (fun x => ρ h (g⁻¹ • x)) := by
    ext s hs
    rw [Measure.map_apply (measurable_const_smul g) hs,
      withDensity_apply _ (hs.preimage (measurable_const_smul g)), withDensity_apply _ hs,
      setLIntegral_map hs hcomp (measurable_const_smul g)]
    simp only [inv_smul_smul]
  rw [← hρ (g * h), ← hmap, hρ h, hpush, hρ g, withDensity_mul μ (hρm g) hcomp]

end MeasureTheory.Measure

namespace MulAction

/-- Multiply the pullback of `f` under `g⁻¹` by the function `α g`. -/
@[expose]
def multiplierAction (α : G → X → ℂ) (g : G) (f : X → ℂ) (x : X) : ℂ :=
  α g x * f (g⁻¹ • x)

/-- The value of the multiplier action at a point. -/
theorem multiplierAction_def (α : G → X → ℂ) (g : G) (f : X → ℂ) (x : X) :
    multiplierAction α g f x = α g x * f (g⁻¹ • x) :=
  (rfl)

/-- The normalized cocycle law for a multiplier of a left group action. -/
@[expose]
def IsMultiplierCocycle (α : G → X → ℂ) : Prop :=
  (∀ x, α 1 x = 1) ∧ ∀ g h x, α (g * h) x = α g x * α h (g⁻¹ • x)

/-- A multiplier cocycle is normalized at the identity and obeys the product law. -/
theorem isMultiplierCocycle_def (α : G → X → ℂ) :
    IsMultiplierCocycle α ↔
      (∀ x, α 1 x = 1) ∧ ∀ g h x, α (g * h) x = α g x * α h (g⁻¹ • x) :=
  Iff.rfl

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

/-- A multiplier cocycle with bounded `L²` operators gives a representation. -/
theorem exists_multiplierRepresentation [MeasurableSpace X]
    {μ : Measure X} {α : G → X → ℂ} (hα : IsMultiplierCocycle α)
    (hquasi : ∀ g : G, QuasiMeasurePreserving (fun x : X => g • x) μ μ)
    (hMem : ∀ g (f : Lp ℂ 2 μ), MemLp (multiplierAction α g f) 2 μ)
    (hbound : ∀ g, ∃ C : ℝ, ∀ f : Lp ℂ 2 μ,
      ‖(hMem g f).toLp (multiplierAction α g f)‖ ≤ C * ‖f‖) :
    ∃ U : ContRepresentation ℂ G (Lp ℂ 2 μ),
      ∀ g f, (U g f : X → ℂ) =ᵐ[μ] multiplierAction α g f := by
  classical
  let act (g : G) (f : Lp ℂ 2 μ) := (hMem g f).toLp (multiplierAction α g f)
  have hact (g : G) (f : Lp ℂ 2 μ) : (act g f : X → ℂ) =ᵐ[μ] multiplierAction α g f :=
    (hMem g f).coeFn_toLp
  let linear (g : G) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := act g
      map_add' := fun f k => by
        apply Lp.ext
        filter_upwards [hact g (f + k), hact g f, hact g k, Lp.coeFn_add (act g f) (act g k),
          (hquasi g⁻¹).ae (Lp.coeFn_add f k)] with x hl hf hk hr hfk
        simp only [hl, hr, Pi.add_apply, hf, hk, multiplierAction_def, hfk, mul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [hact g (c • f), hact g f, Lp.coeFn_smul c (act g f),
          (hquasi g⁻¹).ae (Lp.coeFn_smul c f)] with x hl hf hr hcf
        simp only [hl, RingHom.id_apply, hr, Pi.smul_apply, hf, multiplierAction_def, hcf,
          smul_eq_mul, mul_left_comm] }
  let operator (g : G) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    (linear g).mkContinuous (hbound g).choose (hbound g).choose_spec
  have hfun (g : G) (f : Lp ℂ 2 μ) : (operator g f : X → ℂ) =ᵐ[μ] multiplierAction α g f :=
    hact g f
  refine ⟨{ toMonoidHom := { toFun := operator, map_one' := ?_, map_mul' := ?_ } }, hfun⟩
  · apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [hfun 1 f] with x hx
    simpa only [one_apply_eq_self, multiplierAction_def, hα.1, one_mul, inv_one,
      one_smul] using hx
  · intro g h
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    filter_upwards [hfun (g * h) f, hfun g (operator h f),
      (hquasi g⁻¹).ae (hfun h f)] with x hl hg hh
    simp only [mul_apply_eq_comp, hl, hg, multiplierAction_def, hh, hα.2,
      mul_inv_rev, mul_smul, mul_assoc]

/-- A measurable multiplier cocycle acts unitarily on `L²(μ)` exactly when its squared modulus
agrees almost everywhere with the Radon–Nikodym density of the action. -/
theorem exists_isUnitary_multiplierAction_iff [MeasurableSpace X] [MeasurableConstSMul G X]
    {μ : Measure X} [SigmaFinite μ] {ρ : G → X → ℝ≥0∞} {α : G → X → ℂ}
    (hα : IsMultiplierCocycle α) (hαm : ∀ g, Measurable (α g)) (hρm : ∀ g, Measurable (ρ g))
    (hρ : μ.IsQuasiInvariantWith ρ) :
    (∃ U : ContRepresentation ℂ G (Lp ℂ 2 μ),
        U.IsUnitary ∧ ∀ g f, (U g f : X → ℂ) =ᵐ[μ] multiplierAction α g f) ↔
      ∀ g, ∀ᵐ x ∂μ, ‖α g x‖ₑ ^ 2 = ρ g x := by
  classical
  let weight (g : G) (x : X) := ‖α g x‖ₑ ^ 2
  let translate (g : G) : X ≃ᵐ X := MeasurableEquiv.smul g
  have hm (g : G) : Measurable (weight g) := (hαm g).eNorm.pow_const 2
  have hq (g : G) : QuasiMeasurePreserving (translate g) μ μ :=
    ⟨(translate g).measurable.aemeasurable, by
      have heq : μ.map (translate g) = μ.withDensity (ρ g) := hρ g
      rw [heq]
      exact withDensity_absolutelyContinuous _ _⟩
  have hnorm (f : X → ℂ) (hf : AEStronglyMeasurable f μ) :
      (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) = eLpNorm f 2 μ ^ 2 := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) hf]
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      (lintegral_rpow_eNorm_eq_rpow_eLpNorm' (μ := μ) (f := f) (q := 2) (by norm_num))
  have hchange (g : G) (f : X → ℂ) :
      (∫⁻ x, ‖multiplierAction α g f x‖ₑ ^ 2 ∂μ) =
        ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(μ.withDensity (weight g)).map (translate g).symm := by
    rw [lintegral_map_equiv, lintegral_withDensity_eq_lintegral_mul_non_measurable μ (hm g)
      (Filter.Eventually.of_forall fun x => ENNReal.pow_lt_top (by simp))]
    simp only [weight, multiplierAction_def, eNorm_mul, mul_pow, Pi.mul_apply]
    rfl
  have hmeas (g : G) (f : Lp ℂ 2 μ) :
      AEStronglyMeasurable (multiplierAction α g f) μ :=
    (hαm g).aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving (hq g⁻¹))
  constructor
  · rintro ⟨U, hU, hformula⟩ g
    have hnorm_eq (f : Lp ℂ 2 μ) :
        (∫⁻ x, ‖multiplierAction α g f x‖ₑ ^ 2 ∂μ) = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
      rw [hnorm _ (hmeas g f), ← eLpNorm_congr_ae (hformula g f),
        hnorm _ (Lp.aestronglyMeasurable f), ← Lp.eNorm_def, ← Lp.eNorm_def,
        eNorm_eq_iff_norm_eq.mpr (hU.norm_map g f)]
    have hsets (s : Set X) (hs : MeasurableSet s) (hfin : μ s ≠ ∞) :
        ((μ.withDensity (weight g)).map (translate g).symm) s = μ s := by
      let f := indicatorConstLp 2 hs hfin (1 : ℂ)
      have hf : (f : X → ℂ) =ᵐ[μ] s.indicator (fun _ => 1) := indicatorConstLp_coeFn
      have hcomp : (fun x => multiplierAction α g f x) =ᵐ[μ]
          multiplierAction α g (s.indicator (fun _ => 1)) := by
        filter_upwards [(hq g⁻¹).ae hf] with x hx
        exact congrArg (α g x * ·) hx
      have hind (ν : Measure X) : (∫⁻ x, ‖s.indicator (fun _ => (1 : ℂ)) x‖ₑ ^ 2 ∂ν) =
          ν s := by
        have heq : (fun x => ‖s.indicator (fun _ => (1 : ℂ)) x‖ₑ ^ 2) =
            s.indicator (fun _ => (1 : ℝ≥0∞)) := by
          ext x
          by_cases hx : x ∈ s <;> simp [hx]
        rw [heq, lintegral_indicator_const hs, one_mul]
      rw [← hind, ← hchange]
      calc
        _ = ∫⁻ x, ‖multiplierAction α g f x‖ₑ ^ 2 ∂μ :=
          lintegral_congr_ae (hcomp.fun_comp (fun z : ℂ => ‖z‖ₑ ^ 2)).symm
        _ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := hnorm_eq f
        _ = ∫⁻ x, ‖s.indicator (fun _ => (1 : ℂ)) x‖ₑ ^ 2 ∂μ :=
          lintegral_congr_ae (hf.fun_comp (fun z : ℂ => ‖z‖ₑ ^ 2))
        _ = μ s := hind μ
    have hmap : (μ.withDensity (weight g)).map (translate g).symm = μ := by
      apply Measure.ext_of_iUnion_eq_univ (iUnion_spanningSets μ)
      intro n
      ext s hs
      rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
      exact hsets _ (hs.inter (measurableSet_spanningSets μ n))
        ((measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n)).ne
    have hw : μ.withDensity (weight g) = μ.withDensity (ρ g) := by
      rw [← hρ g]
      exact (MeasurableEquiv.map_measurableEquiv_injective (translate g).symm)
        (hmap.trans (MeasurableEquiv.map_symm_map (μ := μ) (translate g)).symm)
    exact ((withDensity_eq_iff_of_sigmaFinite (hm g).aemeasurable (hρm g).aemeasurable).mp hw)
  · intro h
    have hnorm_eq (g : G) (f : Lp ℂ 2 μ) :
        eLpNorm (multiplierAction α g f) 2 μ ^ 2 = ‖f‖ₑ ^ 2 := by
      rw [← hnorm _ (hmeas g f), hchange, withDensity_congr_ae (h g), ← hρ g]
      change (∫⁻ x, ‖f x‖ₑ ^ 2 ∂(μ.map (translate g)).map (translate g).symm) = _
      rw [MeasurableEquiv.map_symm_map, hnorm _ (Lp.aestronglyMeasurable f), Lp.eNorm_def]
    have hMem (g : G) (f : Lp ℂ 2 μ) : MemLp (multiplierAction α g f) 2 μ := by
      apply memLp_iff.mpr
      apply lt_top_iff_ne_top.mpr
      intro heq
      have hfin := ENNReal.pow_ne_top (n := 2) (Lp.eLpNorm_ne_top f)
      rw [← Lp.eNorm_def, ← hnorm_eq, heq] at hfin
      simp at hfin
    have hnorm_toLp (g : G) (f : Lp ℂ 2 μ) :
        ‖(hMem g f).toLp (multiplierAction α g f)‖ = ‖f‖ := by
      have hsq := congrArg ENNReal.toReal (hnorm_eq g f)
      rw [ENNReal.toReal_pow, ENNReal.toReal_pow, ← Lp.norm_toLp _ (hMem g f),
        toReal_eNorm] at hsq
      nlinarith [norm_nonneg ((hMem g f).toLp (multiplierAction α g f)), norm_nonneg f]
    obtain ⟨U, hU⟩ := exists_multiplierRepresentation hα hq hMem fun g =>
      ⟨1, fun f => by rw [hnorm_toLp, one_mul]⟩
    refine ⟨U, (U.isUnitary_iff_norm_map).mpr fun g f => ?_, hU⟩
    rw [Lp.norm_def (U g f), eLpNorm_congr_ae (hU g f), ← Lp.norm_toLp _ (hMem g f)]
    exact hnorm_toLp g f


end MulAction
