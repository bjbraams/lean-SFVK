/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Group.Circle
public import TauCeti.RepresentationTheory.Compact.Haar
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Sum and difference of two circle phases

The half-sum and half-difference of two real angles parametrize the product of two unit
circles when the first angle ranges over `[0, 2π)` and the second over `[-2π, 2π)`.
We use Mathlib's injectivity of `Circle.exp` on half-open intervals of length `2π`.
The pushforward of the normalized angle measure is the product Haar probability, by Mathlib's
measure-preserving covering map and skew-product formula.
-/

public section

open Function MeasureTheory Set TauCeti
open scoped ENNReal Real

namespace Circle

/-- Every circle element is the exponential of an angle in a prescribed period interval. -/
theorem surjOn_exp_Ico (a : ℝ) : SurjOn exp (Ico a (a + 2 * π)) univ := by
  intro z _
  obtain ⟨θ, rfl⟩ := exp_surjective z
  refine ⟨toIcoMod Real.two_pi_pos a θ, toIcoMod_mem_Ico Real.two_pi_pos a θ, ?_⟩
  rw [← self_sub_toIcoDiv_zsmul, exp_sub, exp_zsmul, exp_two_pi, one_zpow, div_one]

/-- Each pair of phases is attained by a half-sum and a half-difference. -/
theorem exists_exp_add_half_eq_and_exp_sub_half_eq (z w : Circle) :
    ∃ α ∈ Ico 0 (2 * π), ∃ γ ∈ Ico (-(2 * π)) (2 * π),
      exp ((α + γ) / 2) = z ∧ exp ((α - γ) / 2) = w := by
  obtain ⟨α, hα, hzw⟩ := surjOn_exp_Ico 0 (mem_univ (z * w))
  obtain ⟨v, hv, hvz⟩ := surjOn_exp_Ico (-π) (mem_univ (z / exp (α / 2)))
  refine ⟨α, by simpa only [zero_add] using hα, 2 * v, ⟨?_, ?_⟩, ?_, ?_⟩
  · linarith [hv.1]
  · linarith [hv.2]
  · rw [show (α + 2 * v) / 2 = α / 2 + v by ring, exp_add, hvz]
    simp
  · rw [show (α - 2 * v) / 2 = α - (α / 2 + v) by ring, exp_sub, exp_add, hvz, hzw]
    simp

/-- On the product of the period intervals the two phases determine both angles. -/
theorem injOn_exp_add_half_sub_half :
    InjOn (fun p : ℝ × ℝ => (exp ((p.1 + p.2) / 2), exp ((p.1 - p.2) / 2)))
      (Ico 0 (2 * π) ×ˢ Ico (-(2 * π)) (2 * π)) := by
  rintro ⟨α, γ⟩ h ⟨α', γ'⟩ h' heq
  have hadd : exp ((α + γ) / 2) = exp ((α' + γ') / 2) := congrArg Prod.fst heq
  have hsub : exp ((α - γ) / 2) = exp ((α' - γ') / 2) := congrArg Prod.snd heq
  have hα : α = α' := by
    apply exp_injOn_Ico (by linarith : 2 * π - 0 ≤ 2 * π) h.1 h'.1
    calc
      exp α = exp ((α + γ) / 2) * exp ((α - γ) / 2) := by rw [← exp_add]; congr 1; ring
      _ = exp α' := by rw [hadd, hsub, ← exp_add]; congr 1; ring
  subst α'
  have hγ : γ / 2 = γ' / 2 := by
    apply exp_injOn_Ico (by linarith : π - (-π) ≤ 2 * π)
    · exact ⟨by linarith [h.2.1], by linarith [h.2.2]⟩
    · exact ⟨by linarith [h'.2.1], by linarith [h'.2.2]⟩
    rw [add_div, add_div, exp_add, exp_add, mul_right_inj] at hadd
    exact hadd
  exact Prod.ext rfl (by linarith)

/-- The additive circle and unit circle carry the same Haar probability under the exponential. -/
private theorem measurePreserving_toCircle_haarAddCircle (T : ℝ) [hT : Fact (0 < T)] :
    MeasurePreserving (@AddCircle.toCircle T) AddCircle.haarAddCircle (haarProb Circle) := by
  let f : Multiplicative (AddCircle T) →* Circle :=
    { toFun := AddCircle.toCircle
      map_one' := AddCircle.toCircle_zero
      map_mul' := AddCircle.toCircle_add }
  let : MeasurableSpace (Multiplicative (AddCircle T)) :=
    inferInstanceAs (MeasurableSpace (AddCircle T))
  let : BorelSpace (Multiplicative (AddCircle T)) :=
    inferInstanceAs (BorelSpace (AddCircle T))
  let μ : Measure (Multiplicative (AddCircle T)) := AddCircle.haarAddCircle
  have hf : Continuous f := AddCircle.continuous_toCircle
  have hsurj : Surjective f := fun x => by
    obtain ⟨a, ha⟩ := (AddCircle.homeomorphCircle hT.out.ne').surjective x
    exact ⟨a, (AddCircle.homeomorphCircle_apply _ a).symm.trans ha⟩
  let : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
  let : μ.IsHaarMeasure := by
    let h : (AddCircle.haarAddCircle (T := T)).IsAddHaarMeasure := inferInstance
    exact
      { map_mul_left_eq_self := fun g => h.map_add_left_eq_self g
        lt_top_of_isCompact := h.lt_top_of_isCompact
        open_pos := h.open_pos }
  let : (μ.map f).IsHaarMeasure := Measure.isHaarMeasure_map_of_isFiniteMeasure μ f hf hsurj
  exact ⟨hf.measurable, Measure.isHaarMeasure_eq_of_isProbabilityMeasure (μ.map f) _⟩

/-- The phase winds once on a period interval with normalized Lebesgue measure. -/
theorem measurePreserving_exp_mul_restrict_Ico {T : ℝ} (hT : 0 < T) (a : ℝ) :
    MeasurePreserving (fun x : ℝ => exp (2 * π / T * x))
      ((ENNReal.ofReal T)⁻¹ • (volume : Measure ℝ).restrict (Ico a (a + T)))
      (haarProb Circle) := by
  let : Fact (0 < T) := ⟨hT⟩
  have hm := AddCircle.measurePreserving_mk T a
  have hmk : MeasurePreserving ((↑) : ℝ → AddCircle T)
      ((ENNReal.ofReal T)⁻¹ • (volume : Measure ℝ).restrict (Ico a (a + T)))
      (AddCircle.haarAddCircle (T := T)) := by
    refine ⟨hm.measurable, ?_⟩
    rw [Measure.map_smul _ hm.measurable.aemeasurable, restrict_Ico_eq_restrict_Ioc, hm.map_eq,
      AddCircle.volume_eq_smul_haarAddCircle, smul_smul,
      ENNReal.inv_mul_cancel (by simp [hT]) ENNReal.ofReal_ne_top, one_smul]
  simpa only [Function.comp_def, AddCircle.toCircle_apply_mk] using
    (measurePreserving_toCircle_haarAddCircle T).comp hmk

/-- The exponential sends Lebesgue measure on a full period to scaled circle Haar measure. -/
theorem map_exp_restrict_Ioo (a : ℝ) :
    ((volume : Measure ℝ).restrict (Ioo a (a + 2 * π))).map exp =
      ENNReal.ofReal (2 * π) • haarProb Circle := by
  have h := measurePreserving_exp_mul_restrict_Ico Real.two_pi_pos a
  have hdiv : 2 * π / (2 * π) = 1 := div_self Real.two_pi_pos.ne'
  simp only [hdiv, one_mul] at h
  have hmap := h.map_eq
  rw [Measure.map_smul _ Circle.exp.continuous.measurable.aemeasurable] at hmap
  rw [restrict_Ioo_eq_restrict_Ico, ← hmap, smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr Real.two_pi_pos)
      ENNReal.ofReal_ne_top, one_smul]

/-- The Euler phases send normalized Lebesgue measure on the angle box to independent
Haar probability measures on the unit circle. -/
theorem map_eulerPhases_angleMeasure :
    Measure.map (fun p : ℝ × ℝ => (exp ((p.1 + p.2) / 2), exp ((p.1 - p.2) / 2)))
      (ENNReal.ofReal ((8 * π ^ 2)⁻¹) •
        (volume : Measure (ℝ × ℝ)).restrict (Ico 0 (2 * π) ×ˢ Ico (-(2 * π)) (2 * π))) =
      (haarProb Circle).prod (haarProb Circle) := by
  let μα : Measure ℝ := (ENNReal.ofReal (2 * π))⁻¹ • volume.restrict (Ico 0 (2 * π))
  let μγ : Measure ℝ := (ENNReal.ofReal (4 * π))⁻¹ • volume.restrict (Ico (-(2 * π)) (2 * π))
  let μ := haarProb Circle
  have hbox : ENNReal.ofReal ((8 * π ^ 2)⁻¹) •
        (volume : Measure (ℝ × ℝ)).restrict (Ico 0 (2 * π) ×ˢ Ico (-(2 * π)) (2 * π)) =
      μα.prod μγ := by
    dsimp only [μα, μγ]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.prod_smul_left,
      Measure.prod_smul_right, smul_smul]
    congr 1
    rw [← ENNReal.ofReal_inv_of_pos Real.two_pi_pos,
      ← ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < 4 * π by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← mul_inv]
    ring
  have hα : MeasurePreserving exp μα μ := by
    have hone : 2 * π / (2 * π) = 1 := div_self Real.two_pi_pos.ne'
    simpa only [hone, one_mul, zero_add] using
      measurePreserving_exp_mul_restrict_Ico Real.two_pi_pos 0
  have hγ : MeasurePreserving (fun γ : ℝ => exp (γ / 2)) μγ μ := by
    have hh : 2 * π / (4 * π) = 1 / 2 := by field_simp [Real.pi_ne_zero]; ring
    have he : -(2 * π) + (4 * π) = 2 * π := by ring
    have hm (γ : ℝ) : 1 / 2 * γ = γ / 2 := by ring
    simpa only [hh, he, hm] using
      measurePreserving_exp_mul_restrict_Ico (show (0 : ℝ) < 4 * π by positivity) (-(2 * π))
  -- For a fixed first angle, the half-sum phase is a translate of the uniform phase.
  have hskew : MeasurePreserving (fun p : ℝ × ℝ => (exp p.1, exp ((p.1 + p.2) / 2)))
      (μα.prod μγ) (μ.prod μ) := by
    apply hα.skew_product (g := fun α γ => exp ((α + γ) / 2))
    · have hsum : Continuous (fun p : ℝ × ℝ => (p.1 + p.2) / 2) := by fun_prop
      exact (Circle.exp.continuous.comp hsum).measurable
    · exact ae_of_all _ fun α => by
        have he : (fun γ : ℝ => exp ((α + γ) / 2)) =
            (exp (α / 2) * ·) ∘ (fun γ : ℝ => exp (γ / 2)) := by
          funext γ
          rw [add_div, exp_add, Function.comp_apply]
        rw [he]
        exact ((measurePreserving_mul_left μ (exp (α / 2))).comp hγ).map_eq
  have hpres := (measurePreserving_prod_div_swap μ μ).comp hskew
  rw [hbox]
  rw [← hpres.map_eq]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.mk.injEq, true_and, ← exp_sub]
  congr 1
  ring

/-- Integration against a weighted Euler angle measure separates the middle coordinate from
the two independent phases. -/
theorem lintegral_eulerPhases_angleMeasure (d : ℝ → ℝ≥0∞) (hd : Measurable d)
    (H : ℝ × Circle × Circle → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p : ℝ × ℝ × ℝ, H (p.2.1, exp ((p.1 + p.2.2) / 2), exp ((p.1 - p.2.2) / 2))
      ∂(ENNReal.ofReal ((8 * π ^ 2)⁻¹) •
        ((volume : Measure (ℝ × ℝ × ℝ)).restrict
          (Ico 0 (2 * π) ×ˢ Ioi 0 ×ˢ Ico (-(2 * π)) (2 * π))).withDensity (fun p => d p.2.1))) =
    ∫⁻ t in Ioi (0 : ℝ), d t *
      ∫⁻ w, H (t, w) ∂((haarProb Circle).prod (haarProb Circle)) := by
  let μα := (volume : Measure ℝ).restrict (Ico 0 (2 * π))
  let μt := (volume : Measure ℝ).restrict (Ioi 0)
  let μγ := (volume : Measure ℝ).restrict (Ico (-(2 * π)) (2 * π))
  let μcircle := (haarProb Circle).prod (haarProb Circle)
  let C := ENNReal.ofReal ((8 * π ^ 2)⁻¹)
  let phase (p : ℝ × ℝ) := (exp ((p.1 + p.2) / 2), exp ((p.1 - p.2) / 2))
  have hphase : MeasurePreserving phase (C • (μα.prod μγ)) μcircle := by
    refine ⟨?_, ?_⟩
    · exact ((Circle.exp.continuous.comp (by fun_prop)).prodMk
        (Circle.exp.continuous.comp (by fun_prop))).measurable
    · simpa only [phase, C, μα, μγ, μcircle, Measure.prod_restrict, ← Measure.volume_eq_prod] using
        map_eulerPhases_angleMeasure
  have hbox :
      (volume : Measure (ℝ × ℝ × ℝ)).restrict (Ico 0 (2 * π) ×ˢ Ioi 0 ×ˢ Ico (-(2 * π)) (2 * π))
        = μα.prod (μt.prod μγ) := by
    dsimp only [μα, μt, μγ]
    rw [Measure.prod_restrict, Measure.prod_restrict, ← Measure.volume_eq_prod,
      ← Measure.volume_eq_prod]
  have hswap : MeasurePreserving (fun p : ℝ × ℝ × ℝ => (p.2.1, p.1, p.2.2))
      (μα.prod (μt.prod μγ)) (μt.prod (μα.prod μγ)) :=
    (measurePreserving_prodAssoc μt μα μγ).comp
      ((Measure.measurePreserving_swap (μ := μα) (ν := μt)).prod (MeasurePreserving.id μγ) |>.comp
        ((measurePreserving_prodAssoc μα μt μγ).symm MeasurableEquiv.prodAssoc))
  have hswap' : MeasurePreserving (fun p : ℝ × ℝ × ℝ => (p.2.1, p.1, p.2.2))
      (C • μα.prod (μt.prod μγ)) (μt.prod (C • μα.prod μγ)) := by
    refine ⟨hswap.measurable, ?_⟩
    rw [Measure.map_smul _ hswap.measurable.aemeasurable, hswap.map_eq, Measure.prod_smul_right]
  let htotal := ((MeasurePreserving.id μt).prod hphase).comp hswap'
  have hmeas : Measurable (fun x : ℝ × Circle × Circle => d x.1 * H x) :=
    (hd.comp measurable_fst).mul hH
  have hd' : Measurable (fun p : ℝ × ℝ × ℝ => d p.2.1) :=
    hd.comp measurable_snd.fst
  have hsource : Measurable (fun p : ℝ × ℝ × ℝ =>
      H (p.2.1, exp ((p.1 + p.2.2) / 2), exp ((p.1 - p.2.2) / 2))) :=
    hH.comp htotal.measurable
  rw [hbox, lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hd' hsource,
    ← lintegral_smul_measure]
  have h := htotal.lintegral_comp hmeas
  -- Express the pushforward on the product as its iterated integral.
  rw [lintegral_prod _ hmeas.aemeasurable] at h
  have hsection (t : ℝ) : Measurable (fun w : Circle × Circle => H (t, w)) :=
    hH.comp measurable_prodMk_left
  simp_rw [lintegral_const_mul'' _ (hsection _).aemeasurable] at h
  exact h

end Circle
