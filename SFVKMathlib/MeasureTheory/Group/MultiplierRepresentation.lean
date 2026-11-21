/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVKMathlib.MeasureTheory.Group.Multiplier
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# The multiplier representation on `L²`

For a multiplier `α` of a group action on a measure space `(X, μ)`, the representation on
`L²(X, μ)` whose operators are given almost everywhere by the multiplier formula
`(T(g) f)(x) = α(g, x) f(g⁻¹ x)`. It is defined by choice when such a representation exists
(see `MulAction.exists_multiplierRepresentation` for a criterion) and is the trivial
representation otherwise, so that the definition needs no hypotheses.

For a continuous cocycle on a compact space with finite invariant measure, continuous orbit maps
follow by Mathlib's density of continuous functions in `L²`.
-/

public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]

open scoped Classical in
/-- The multiplier representation on `L²(X, μ)`: a representation whose operators agree almost
everywhere with `multiplierAction α`, chosen when one exists, and the trivial representation
otherwise. -/
@[expose]
def multiplierRepresentation (μ : Measure X) (α : G → X → ℂ) :
    ContRepresentation ℂ G (Lp ℂ 2 μ) :=
  if h : ∃ U : ContRepresentation ℂ G (Lp ℂ 2 μ),
      ∀ g f, (U g f : X → ℂ) =ᵐ[μ] multiplierAction α g f then h.choose
  else .ofMonoidHom 1

open scoped Classical in
/-- The multiplier representation chooses an almost-everywhere realization when one exists and
takes the trivial representation otherwise. -/
theorem multiplierRepresentation_def (μ : Measure X) (α : G → X → ℂ) :
    multiplierRepresentation μ α =
      if h : ∃ U : ContRepresentation ℂ G (Lp ℂ 2 μ),
          ∀ g f, (U g f : X → ℂ) =ᵐ[μ] multiplierAction α g f then h.choose
      else .ofMonoidHom 1 :=
  rfl

/-- When some representation realizes the multiplier formula, so does
`multiplierRepresentation`. -/
theorem multiplierRepresentation_ae_eq {μ : Measure X} {α : G → X → ℂ}
    (h : ∃ U : ContRepresentation ℂ G (Lp ℂ 2 μ),
      ∀ g f, (U g f : X → ℂ) =ᵐ[μ] multiplierAction α g f) (g : G) (f : Lp ℂ 2 μ) :
    (multiplierRepresentation μ α g f : X → ℂ) =ᵐ[μ] multiplierAction α g f := by
  classical
  rw [multiplierRepresentation_def, dite_eq_left h]
  exact h.choose_spec g f

/-- A continuous multiplier cocycle on a compact space with invariant finite measure has an
`L²` realization with continuous orbit maps. -/
theorem exists_stronglyContinuous_multiplierRepresentation
    [TopologicalSpace G] [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [μ.WeaklyRegular] {α : G → X → ℂ}
    (hα : IsMultiplierCocycle α)
    (hcont : Continuous (fun p : G × X => α p.1 p.2))
    (hact : Continuous (fun p : G × X => p.1⁻¹ • p.2))
    (hpres : ∀ g : G, MeasurePreserving (fun x : X => g • x) μ μ) :
    ∃ U : ContRepresentation ℂ G (Lp ℂ 2 μ),
      (∀ g f, (U g f : X → ℂ) =ᵐ[μ] multiplierAction α g f) ∧
        ∀ f, Continuous fun g => U g f := by
  let weight : C(G × X, ℂ) := ⟨_, hcont⟩
  let bound (g : G) := ‖weight.curry g‖
  have hmeas (g : G) (f : Lp ℂ 2 μ) :
      AEStronglyMeasurable (multiplierAction α g f) μ :=
    (weight.curry g).continuous.aestronglyMeasurable.mul
      ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
        (hpres g⁻¹).quasiMeasurePreserving)
  have hestimate (g : G) (f : Lp ℂ 2 μ) :
      eLpNorm (multiplierAction α g f) 2 μ ≤ ENNReal.ofReal (bound g) * eLpNorm f 2 μ := by
    have hpoint : ∀ᵐ x ∂μ, ‖multiplierAction α g f x‖ ≤ bound g * ‖f (g⁻¹ • x)‖ :=
      Eventually.of_forall fun x => by
        rw [multiplierAction_def, norm_mul]
        exact mul_le_mul_of_nonneg_right ((weight.curry g).norm_coe_le_norm x) (norm_nonneg _)
    have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hmeas g f) hpoint 2
    have hpull := eLpNorm_comp_measurePreserving (p := 2) (Lp.aestronglyMeasurable f) (hpres g⁻¹)
    dsimp only [Function.comp_def] at hpull
    rwa [hpull] at hle
  have hMem (g : G) (f : Lp ℂ 2 μ) : MemLp (multiplierAction α g f) 2 μ :=
    memLp_iff.mpr ((hestimate g f).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top f)))
  have hbound (g : G) (f : Lp ℂ 2 μ) :
      ‖(hMem g f).toLp (multiplierAction α g f)‖ ≤ bound g * ‖f‖ := by
    rw [Lp.norm_toLp]
    calc
      _ ≤ (ENNReal.ofReal (bound g) * eLpNorm f 2 μ).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) (hestimate g f)
      _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (show 0 ≤ bound g from norm_nonneg _),
          Lp.norm_def]
  obtain ⟨U, hU⟩ := exists_multiplierRepresentation hα
    (fun g => (hpres g).quasiMeasurePreserving) hMem (fun g => ⟨bound g, hbound g⟩)
  refine ⟨U, hU, ?_⟩
  have hOp (g : G) (f : Lp ℂ 2 μ) : ‖U g f‖ ≤ bound g * ‖f‖ := by
    have heq : U g f = (hMem g f).toLp (multiplierAction α g f) :=
      Lp.ext ((hU g f).trans (hMem g f).coeFn_toLp.symm)
    simpa only [heq] using hbound g f
  have hC : Continuous bound := weight.curry.continuous.norm
  let L : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ
  have horbit (f : C(X, ℂ)) : Continuous fun g => U g (L f) := by
    let F : C(G × X, ℂ) :=
      ⟨fun p => multiplierAction α p.1 f p.2,
        hcont.mul (f.continuous.comp hact)⟩
    have hF (g : G) : U g (L f) = L (F.curry g) := by
      apply Lp.ext
      have hf := (hpres g⁻¹).quasiMeasurePreserving.ae_eq_comp
        (ContinuousMap.coeFn_toLp μ f (p := 2) (𝕜 := ℂ))
      filter_upwards [hU g (L f), ContinuousMap.coeFn_toLp μ (F.curry g) (p := 2) (𝕜 := ℂ),
        hf] with x hu hr hx
      dsimp only [Function.comp_apply] at hx
      rw [hu, hr, multiplierAction_def, hx]
      rfl
    simp_rw [hF]
    exact L.continuous.comp F.curry.continuous
  have hdense : DenseRange L := ContinuousMap.toLp_denseRange (μ := μ) (p := 2) ℂ ℂ (by simp)
  intro f
  rw [continuous_iff_continuousAt]
  intro g
  rw [Metric.continuousAt_iff']
  intro ε hε
  let B := bound g + 1
  have hB : 0 < B := add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  have hBg : bound g < B := lt_add_one _
  have hBnear : ∀ᶠ a in 𝓝 g, bound a < B := hC.continuousAt.eventually_lt continuousAt_const hBg
  obtain ⟨k, hk⟩ := (Metric.mem_closure_range_iff.mp (hdense f))
    (ε / (3 * B)) (div_pos hε (by positivity))
  have hsmall (a : G) (ha : bound a < B) : dist (U a f) (U a (L k)) < ε / 3 := by
    rw [dist_eq_norm] at hk
    calc
      dist (U a f) (U a (L k)) = ‖U a (f - L k)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ bound a * ‖f - L k‖ := hOp a _
      _ ≤ B * ‖f - L k‖ := mul_le_mul_of_nonneg_right ha.le (norm_nonneg _)
      _ < ε / 3 := by
        rw [lt_div_iff₀ (by positivity : 0 < 3 * B)] at hk
        linarith
  have hmid : ∀ᶠ a in 𝓝 g, dist (U a (L k)) (U g (L k)) < ε / 3 :=
    Metric.continuousAt_iff'.mp (horbit k).continuousAt (ε / 3) (by positivity)
  filter_upwards [hBnear, hmid] with a ha hdist
  have hlast := hsmall g hBg
  rw [dist_comm] at hlast
  exact (dist_triangle4 (U a f) (U a (L k)) (U g (L k)) (U g f)).trans_lt (by
    linarith [hsmall a ha, hdist, hlast])

end MulAction
