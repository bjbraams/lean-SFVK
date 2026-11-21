/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.RankOne.Jacobi

import DLMF.Hypergeometric.ParameterHolomorphy
import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import SFVKMathlib.Analysis.Complex.GaussCutPlane

/-!
# The Jacobi transform

The Jacobi transform `f̃(λ) = ∫₀^∞ f(t) φ_λ(t) Δ(t) dt` with
`Δ(t) = (2 sinh t)^{2α+1} (2 cosh t)^{2β+1}` (DLMF 15.9.12), its evenness, holomorphy and
Paley–Wiener estimate, the transform of the Jacobi operator, and the inversion and Plancherel
formulas with density `(2π)⁻¹ |c(λ)|⁻²` for `α > −1`, `|β| ≤ α + 1`, with the unitary extension.

Sources: DLMF 15.9.12–15.9.13; Klimyk–Vilenkin, *Representations of Lie Groups and Special
Functions* (Kirillov (ed.), EMS 59), Part II Ch. 5 §2.4, (15)–(16), p. 233; Wawrzyńczyk,
*Group Representations and Special Functions*, Theorem 18.6.1, p. 631. The holomorphy proof uses
the Gauss parameter holomorphy and dominated parametric integration from lean-DLMF.

## Main definitions

* `SFVK.RankOne.jacobiTransform`.

## Main results

* `SFVK.RankOne.jacobiTransform_neg`.
* `SFVK.RankOne.differentiable_jacobiTransform`.
* `SFVK.RankOne.norm_jacobiTransform_le`.
* `SFVK.RankOne.jacobiTransform_jacobiOperator`.
* `SFVK.RankOne.jacobiTransform_inversion`.
* `SFVK.RankOne.jacobiTransform_plancherel`.
* `SFVK.RankOne.exists_jacobiTransform_linearIsometryEquiv`.
-/

public noncomputable section

open Complex Filter Topology Set MeasureTheory DLMF.Hypergeometric DLMF.Legendre
open scoped Real ContDiff Interval

namespace SFVK.RankOne

/-- The Jacobi transform `f̃(λ) = ∫₀^∞ f(t) φ_λ(t) Δ(t) dt` (DLMF 15.9.12). -/
@[expose]
def jacobiTransform (α β : ℝ) (f : ℝ → ℂ) (lam : ℂ) : ℂ :=
  ∫ t in Ioi 0, f t * jacobiFunction α β lam t * jacobiWeight α β t

/-- The Jacobi transform integrates the profile against the Jacobi function and its radial measure.
-/
theorem jacobiTransform_def (α β : ℝ) (f : ℝ → ℂ) (lam : ℂ) :
    jacobiTransform α β f lam = ∫ t in Ioi 0, f t * jacobiFunction α β lam t * jacobiWeight α β t :=
  rfl

/-- **Evenness**: `f̃(−λ) = f̃(λ)`. -/
theorem jacobiTransform_neg (α β : ℝ) (f : ℝ → ℂ) (lam : ℂ) :
    jacobiTransform α β f (-lam) = jacobiTransform α β f lam := by
  simp only [jacobiTransform_def, jacobiFunction_neg_spectral]

/-- The Jacobi function is jointly continuous in the spectral parameter and radius. -/
theorem continuous_jacobiFunction_joint (α β : ℂ) :
    Continuous (fun p : ℂ × ℝ => jacobiFunction α β p.1 p.2) := by
  let arg (p : ℂ × ℝ) : ℂ × ℂ × ℂ × ℂ :=
    ((α + β + 1 + I * p.1) / 2, (α + β + 1 - I * p.1) / 2, α + 1, -(Complex.sinh p.2) ^ 2)
  have harg : Continuous arg := by dsimp [arg]; fun_prop
  have hc := differentiableOn_regularizedGaussHypergeometric_joint.continuousOn.comp_continuous
    harg (fun p => Complex.neg_sinh_sq_mem_gaussCutPlane p.2)
  exact continuous_const.mul hc

namespace JacobiTransform

/-- A compactly supported positive-half-line integral reduces to a finite interval containing its
support. -/
private theorem eq_integral_Ioc (α β : ℝ) (f : ℝ → ℂ) {R : ℝ}
    (hf : ∀ t, R < t → f t = 0) (z : ℂ) :
    jacobiTransform α β f z = ∫ t in Ioc 0 R, f t * jacobiFunction α β z t *
      jacobiWeight α β t := by
  rw [jacobiTransform_def]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
  intro t ht
  have htR : R < t := lt_of_not_ge fun h => ht.2 ⟨ht.1, h⟩
  simp only [hf t htR, zero_mul]

/-- For a differentiable function with continuous derivative, the divided slope from zero is
continuous. -/
private theorem continuous_dslope_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : Continuous f) (hf₀ : DifferentiableAt ℝ f 0) :
    Continuous (dslope f 0) :=
  continuous_iff_continuousAt.mpr fun t => by
    by_cases ht : t = 0
    · subst t
      exact continuousAt_dslope_same.mpr hf₀
    · exact (continuousAt_dslope_of_ne ht).mpr hf.continuousAt

/-- Away from zero the divided slope of the hyperbolic sine is its value divided by the argument. -/
private theorem dslope_sinh_zero_apply (t : ℝ) (ht : t ≠ 0) :
    dslope Real.sinh 0 t = Real.sinh t / t := by
  rw [dslope_of_ne _ ht, slope_def_field, Real.sinh_zero, sub_zero, sub_zero]

/-- The divided slope of the hyperbolic sine from zero is positive. -/
private theorem dslope_sinh_zero_pos (t : ℝ) : 0 < dslope Real.sinh 0 t := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · rw [dslope_sinh_zero_apply _ h.ne]
    exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr h) h
  · simp [dslope_same, (Real.hasDerivAt_sinh 0).deriv]
  · rw [dslope_sinh_zero_apply _ h.ne']
    exact div_pos (Real.sinh_pos_iff.mpr h) h

/-- The continuous factor remaining after the origin power is extracted from the Jacobi weight. -/
private def weightFactor (α β : ℝ) (t : ℝ) : ℝ :=
  (2 * dslope Real.sinh 0 t) ^ (2 * α + 1) * (2 * Real.cosh t) ^ (2 * β + 1)

/-- The regular factor of the Jacobi weight is continuous. -/
private theorem continuous_weightFactor (α β : ℝ) : Continuous (weightFactor α β) := by
  have hs := continuous_dslope_zero Real.continuous_sinh (Real.hasDerivAt_sinh 0).differentiableAt
  exact ((continuous_const.mul hs).rpow_const
    (fun x => Or.inl (mul_pos two_pos (dslope_sinh_zero_pos x)).ne')).mul
    ((continuous_const.mul Real.continuous_cosh).rpow_const
      (fun x => Or.inl (mul_pos two_pos (Real.cosh_pos x)).ne'))

/-- On the positive half-line the Jacobi weight is the origin power times its regular factor. -/
private theorem jacobiWeight_eq_rpow_mul (α β : ℝ) {t : ℝ} (ht : 0 < t) :
    jacobiWeight α β t = t ^ (2 * α + 1) * weightFactor α β t := by
  have hs : 2 * Real.sinh t = t * (2 * dslope Real.sinh 0 t) := by
    rw [dslope_sinh_zero_apply _ ht.ne']
    field_simp
  rw [jacobiWeight_def, hs, Real.mul_rpow ht.le (mul_pos two_pos (dslope_sinh_zero_pos t)).le]
  simp only [weightFactor, mul_assoc]

/-- The Jacobi weight is locally integrable at zero in its Jacobi parameter range. -/
private theorem integrableOn_jacobiWeight (α β : ℝ) (hα : -1 < α) (R : ℝ) :
    IntegrableOn (jacobiWeight α β) (Ioc 0 R) := by
  have hp := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := R)
    (r := 2 * α + 1) (by linarith : -1 < 2 * α + 1)).continuousOn_mul
      (continuous_weightFactor α β).continuousOn
  refine hp.1.congr_fun ?_ measurableSet_Ioc
  intro t ht
  change weightFactor α β t * t ^ (2 * α + 1) = _
  rw [jacobiWeight_eq_rpow_mul α β ht.1, mul_comm]

/-- A continuous function times the Jacobi weight is integrable on bounded radial intervals. -/
private theorem integrableOn_mul_jacobiWeight (α β : ℝ) (hα : -1 < α) {g : ℝ → ℂ}
    (hg : Continuous g) (R : ℝ) :
    IntegrableOn (fun t => g t * (jacobiWeight α β t : ℂ)) (Ioc 0 R) := by
  have hw : IntegrableOn (fun t => (jacobiWeight α β t : ℂ)) (Ioc 0 R) := by
    unfold IntegrableOn
    simpa only [Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.integrable_comp (integrableOn_jacobiWeight α β hα R)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
    hg.continuousOn
  exact hw.bdd_mul hg.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => hC t ⟨ht.1.le, ht.2⟩)

/-- The derivative at zero of a differentiable even function vanishes. -/
private theorem deriv_even_zero {f : ℝ → ℂ} (hf : DifferentiableAt ℝ f 0)
    (heven : ∀ t, f (-t) = f t) : deriv f 0 = 0 := by
  have hf' : HasDerivAt f (deriv f 0) (-(0 : ℝ)) := by
    rw [neg_zero]
    exact hf.hasDerivAt
  have h := hf'.scomp (0 : ℝ) (hasDerivAt_id (0 : ℝ)).neg
  simp only [Function.comp_def, neg_smul, one_smul] at h
  rw [show (fun t => f (-t)) = f from funext heven] at h
  linear_combination (1 / 2 : ℂ) * h.deriv

/-- Compute the logarithmic derivative of the Jacobi weight at a positive radius. -/
private theorem hasDerivAt_jacobiWeight (α β : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (jacobiWeight α β)
      (jacobiWeight α β t * ((2 * α + 1) * (Real.cosh t / Real.sinh t) +
        (2 * β + 1) * Real.tanh t)) t := by
  have hs := (Real.sinh_pos_iff.mpr ht).ne'
  have hc := (Real.cosh_pos t).ne'
  have hA := ((Real.hasDerivAt_sinh t).const_mul 2).rpow_const
    (p := 2 * α + 1) (Or.inl (mul_ne_zero two_ne_zero hs))
  have hB := ((Real.hasDerivAt_cosh t).const_mul 2).rpow_const
    (p := 2 * β + 1) (Or.inl (mul_ne_zero two_ne_zero hc))
  refine (hA.mul hB).congr_deriv ?_
  simp only [jacobiWeight_def, Real.tanh_eq_sinh_div_cosh,
    Real.rpow_sub_one (mul_ne_zero two_ne_zero hs), Real.rpow_sub_one (mul_ne_zero two_ne_zero hc)]
  field_simp
end JacobiTransform

set_option maxHeartbeats 800000 in
/-- **Holomorphy** for continuous compactly supported `f` and `α > −1`. -/
theorem differentiable_jacobiTransform (α β : ℝ) (hα : -1 < α) (f : ℝ → ℂ)
    (hf : Continuous f) (hfs : HasCompactSupport f) :
    Differentiable ℂ (jacobiTransform α β f) := by
  obtain ⟨R, _, hs⟩ := hfs.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  let F (lam : ℂ) (t : ℝ) := f t * jacobiFunction α β lam t * jacobiWeight α β t
  have hfOutside (t : ℝ) (ht : R < t) : f t = 0 := by
    by_contra hn
    have h := hs (subset_tsupport f (Function.mem_support.mpr hn))
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at h
    exact (not_le_of_gt ht) h.2
  have heq : jacobiTransform α β f = fun z => ∫ t in Ioc 0 R, F z t :=
    funext (JacobiTransform.eq_integral_Ioc α β f hfOutside)
  rw [heq, ← differentiableOn_univ]
  apply Complex.differentiableOn_integral_of_locally_dominated
    (Φ := F) (μ := (volume : Measure ℝ).restrict (Ioc 0 R)) isOpen_univ
  · intro z _
    have hc : Continuous (fun t : ℝ => jacobiFunction α β z t) :=
      continuous_iff_continuousAt.mpr (fun t =>
        (analyticAt_jacobiFunction_radius (α : ℂ) (β : ℂ) z t).continuousAt)
    have hw : AEStronglyMeasurable (fun t => (jacobiWeight α β t : ℂ))
        (volume.restrict (Ioc 0 R)) :=
      continuous_ofReal.comp_aestronglyMeasurable
        (JacobiTransform.integrableOn_jacobiWeight α β hα R).aestronglyMeasurable
    exact (hf.mul hc).aestronglyMeasurable.mul hw
  · exact ae_of_all _ fun t =>
      (((differentiable_jacobiFunction α β t).const_mul (f t)).mul_const
        (jacobiWeight α β t : ℂ)).differentiableOn
  · intro z _
    have hC : Continuous (fun p : ℂ × ℝ => f p.2 * jacobiFunction α β p.1 p.2) :=
      (hf.comp continuous_snd).mul (continuous_jacobiFunction_joint α β)
    have hK : IsCompact (Metric.closedBall z 1 ×ˢ Icc (0 : ℝ) R) :=
      (isCompact_closedBall z 1).prod isCompact_Icc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hC.continuousOn
    refine ⟨Metric.ball z 1, Metric.ball_mem_nhds _ (by norm_num),
      fun t => C * ‖jacobiWeight α β t‖, ?_, ?_⟩
    · exact (JacobiTransform.integrableOn_jacobiWeight α β hα R).norm.const_mul C
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      intro w hw
      have hbound := hC (w, t) ⟨Metric.ball_subset_closedBall hw, ⟨ht.1.le, ht.2⟩⟩
      rw [show ‖F w t‖ = ‖f t * jacobiFunction α β w t‖ * ‖jacobiWeight α β t‖ by
        simp only [F, norm_mul, norm_real] ]
      exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)

/-- **The Paley–Wiener estimate**: for `f` continuous with support in `[−R, R]`,
`|f̃(λ)| ≤ C e^{R |Im λ|}`. -/
theorem norm_jacobiTransform_le (α β : ℝ) (hαβ : β ≤ α) (hβ : -1 / 2 ≤ β) (f : ℝ → ℂ)
    (hf : Continuous f) {R : ℝ} (hR : tsupport f ⊆ Icc (-R) R) :
    ∃ C, ∀ lam : ℂ, ‖jacobiTransform α β f lam‖ ≤ C * Real.exp (R * |lam.im|) := by
  have hfOutside (t : ℝ) (ht : R < t) : f t = 0 := by
    by_contra hn
    exact (not_le_of_gt ht) (hR (subset_tsupport f (Function.mem_support.mpr hn))).2
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
    hf.continuousOn
  have hα : -1 / 2 ≤ α := hβ.trans hαβ
  have hw := (JacobiTransform.integrableOn_jacobiWeight α β (by linarith) R).norm
  refine ⟨C * (∫ t in Ioc 0 R, ‖jacobiWeight α β t‖), fun lam => ?_⟩
  let bound := Real.exp (R * |lam.im|)
  rw [JacobiTransform.eq_integral_Ioc α β f hfOutside]
  change _ ≤ _
  calc
    _ ≤ ∫ t in Ioc 0 R, (C * bound) * ‖jacobiWeight α β t‖ := by
      apply norm_integral_le_of_norm_le (hw.const_mul (C * bound))
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hfBound := hC t ⟨ht.1.le, ht.2⟩
      have hφ := norm_jacobiFunction_le_exp α β hα (by linarith) lam t
      rw [abs_of_pos ht.1, mul_comm] at hφ
      have hφBound : ‖jacobiFunction α β lam t‖ ≤ bound :=
        hφ.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)))
      simp only [norm_mul, norm_real]
      exact mul_le_mul_of_nonneg_right (mul_le_mul hfBound hφBound (norm_nonneg _)
        ((norm_nonneg (f t)).trans hfBound)) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul]; dsimp only [bound]; ring

set_option maxHeartbeats 1400000 in
/-- **The transform diagonalizes `L`**: `(L f)~(λ) = −(λ² + ρ²) f̃(λ)` for smooth even compactly
supported `f`. -/
theorem jacobiTransform_jacobiOperator (α β : ℝ) (hα : -1 < α) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) (heven : ∀ t, f (-t) = f t) (lam : ℂ) :
    jacobiTransform α β (jacobiOperator α β f) lam =
      -(lam ^ 2 + (α + β + 1) ^ 2) * jacobiTransform α β f lam := by
  let φ (t : ℝ) := jacobiFunction α β lam t
  let w := jacobiWeight α β
  let κ := lam ^ 2 + ((α : ℂ) + β + 1) ^ 2
  have hfTwo : ContDiff ℝ 2 f := hf.of_le (by simp)
  have hφTwo : ContDiff ℝ 2 φ := contDiff_iff_contDiffAt.mpr
    (fun s => (analyticAt_jacobiFunction_radius α β lam s).contDiffAt)
  have hf' := (hfTwo.differentiable (by norm_num))
  have hφ' := (hφTwo.differentiable (by norm_num))
  have hf'' := (ContDiff.deriv' (n := 1) hfTwo).differentiable (by norm_num)
  have hφ'' := (ContDiff.deriv' (n := 1) hφTwo).differentiable (by norm_num)
  have hf₀ := JacobiTransform.deriv_even_zero (hf' 0) heven
  have hφ₀ := JacobiTransform.deriv_even_zero (hφ' 0) (jacobiFunction_even α β lam)
  let fSlope := dslope (deriv f) 0
  let φSlope := dslope (deriv φ) 0
  have hfSlope : Continuous fSlope :=
    JacobiTransform.continuous_dslope_zero hf''.continuous (hf'' 0)
  have hφSlope : Continuous φSlope :=
    JacobiTransform.continuous_dslope_zero hφ''.continuous (hφ'' 0)
  have hfSlopeEq (t : ℝ) : (t : ℂ) * fSlope t = deriv f t := by
    simpa only [Complex.real_smul, fSlope, sub_zero] using sub_smul_dslope_of_zero hf₀ t
  have hφSlopeEq (t : ℝ) : (t : ℂ) * φSlope t = deriv φ t := by
    simpa only [Complex.real_smul, φSlope, sub_zero] using sub_smul_dslope_of_zero hφ₀ t
  -- The Wronskian vanishes at the singular endpoint because both first derivatives are odd.
  let H (t : ℝ) : ℂ :=
    ((t ^ (2 * α + 1 + 1) * JacobiTransform.weightFactor α β t : ℝ) : ℂ) *
      (fSlope t * φ t - f t * φSlope t)
  let Hraw (t : ℝ) : ℂ := (w t : ℂ) * (deriv f t * φ t - f t * deriv φ t)
  have hH : Continuous H := by
    have hpow : Continuous (fun t : ℝ => t ^ (2 * α + 1 + 1)) :=
      continuous_id.rpow_const (fun _ => Or.inr (by linarith))
    exact (continuous_ofReal.comp (hpow.mul (JacobiTransform.continuous_weightFactor α β))).mul
      ((hfSlope.mul hφ'.continuous).sub (hf'.continuous.mul hφSlope))
  have hH₀ : H 0 = 0 := by simp [H, Real.zero_rpow (by linarith : 2 * α + 1 + 1 ≠ 0)]
  have hHraw (t : ℝ) (ht : 0 < t) : H t = Hraw t := by
    dsimp only [H, Hraw, w]
    rw [JacobiTransform.jacobiWeight_eq_rpow_mul α β ht, Real.rpow_add ht, Real.rpow_one,
      ← hfSlopeEq t, ← hφSlopeEq t]
    push_cast
    ring
  let g (t : ℝ) := jacobiOperator α β f t * φ t * (w t : ℂ)
  let l (t : ℝ) := f t * φ t * (w t : ℂ)
  have hHD (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : HasDerivAt H (g t + κ * l t) t := by
    have hw := (JacobiTransform.hasDerivAt_jacobiWeight α β ht).ofReal_comp
    have hp := ((hf'' t).hasDerivAt.mul (hφ' t).hasDerivAt).sub
      ((hf' t).hasDerivAt.mul (hφ'' t).hasDerivAt)
    have h := hw.mul hp
    have hφD := jacobiOperator_jacobiFunction α β lam ht
    rw [jacobiOperator_def] at hφD
    change deriv (deriv φ) t +
      ((2 * (α : ℂ) + 1) * (Real.cosh t / Real.sinh t : ℝ) +
        (2 * (β : ℂ) + 1) * (Real.tanh t : ℂ)) * deriv φ t = -κ * φ t at hφD
    have hCongr : H =ᶠ[𝓝 t] Hraw := by
      filter_upwards [Ioi_mem_nhds (show 0 < t from ht)] with s hs
      exact hHraw s hs
    refine (h.congr_deriv ?_).congr_of_eventuallyEq hCongr
    simp only [g, l, jacobiOperator_def, w, ofReal_add, ofReal_mul, ofReal_ofNat,
      ofReal_one, Pi.sub_apply, Pi.mul_apply]
    linear_combination -(jacobiWeight α β t : ℂ) * f t * hφD
  obtain ⟨R, hR, hsupp⟩ := hfs.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  have hOutside (t : ℝ) (ht : R < t) : t ∉ tsupport f := by
    intro h
    have hmem := hsupp h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hmem
    exact not_le_of_gt ht hmem.2
  have hfOut (t : ℝ) (ht : R < t) : f t = 0 :=
    image_eq_zero_of_notMem_tsupport (hOutside t ht)
  have hf'Out (t : ℝ) (ht : R < t) : deriv f t = 0 :=
    deriv_of_notMem_tsupport (hOutside t ht)
  have hf''Out (t : ℝ) (ht : R < t) : deriv (deriv f) t = 0 :=
    deriv_of_notMem_tsupport (fun hn => hOutside t ht (tsupport_deriv_subset hn))
  have hgOut (t : ℝ) (ht : R < t) : g t = 0 := by
    simp [g, jacobiOperator_def, hf'Out t ht, hf''Out t ht]
  have hT : Tendsto H atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioi_mem_atTop R] with t ht
    rw [hHraw t (hR.trans ht)]
    simp [Hraw, hfOut t ht, hf'Out t ht]
  let q := dslope Real.sinh 0
  -- Express the operator with a continuous coefficient at zero before taking the integral.
  let Op (t : ℝ) := deriv (deriv f) t +
    (((2 * α + 1) * (Real.cosh t / q t) + (2 * β + 1) * Real.tanh t * t : ℝ) : ℂ) *
      fSlope t
  have hOp : Continuous Op := by
    have hq : Continuous q := JacobiTransform.continuous_dslope_zero Real.continuous_sinh
      (Real.hasDerivAt_sinh 0).differentiableAt
    have hq₀ (t : ℝ) : q t ≠ 0 := (JacobiTransform.dslope_sinh_zero_pos t).ne'
    have htan : Continuous (fun t => Real.tanh t) := by
      rw [show (fun t => Real.tanh t) = Real.sinh / Real.cosh from
        funext fun t => by rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh] ]
      exact Real.continuous_sinh.div Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')
    have := (ContDiff.deriv' (n := 0) (ContDiff.deriv' (n := 1) hfTwo)).continuous
    fun_prop
  have hOpEq (t : ℝ) (ht : 0 < t) : jacobiOperator α β f t = Op t := by
    rw [jacobiOperator_def, ← hfSlopeEq t]
    simp only [Op, q, JacobiTransform.dslope_sinh_zero_apply t ht.ne', ofReal_add, ofReal_mul,
      ofReal_ofNat, ofReal_one, ofReal_div, div_div_eq_mul_div]
    ring
  have hsplit : Ioi (0 : ℝ) = Ioc 0 R ∪ Ioi R := (Ioc_union_Ioi_eq_Ioi hR.le).symm
  have hgI : IntegrableOn g (Ioi 0) := by
    rw [hsplit]
    refine IntegrableOn.union ?_ ((integrableOn_zero).congr_fun
      (fun t ht => (hgOut t ht).symm) measurableSet_Ioi)
    refine (JacobiTransform.integrableOn_mul_jacobiWeight α β hα
      (hOp.mul hφ'.continuous) R).congr_fun ?_ measurableSet_Ioc
    intro t ht
    simp only [g, w, hOpEq t ht.1, Pi.mul_apply]
  have hlI : IntegrableOn l (Ioi 0) := by
    rw [hsplit]
    refine IntegrableOn.union (JacobiTransform.integrableOn_mul_jacobiWeight α β hα
      (hf'.continuous.mul hφ'.continuous) R) ((integrableOn_zero).congr_fun
      (fun t ht => ?_) measurableSet_Ioi)
    simp [l, hfOut t ht]
  have hInt := integral_Ioi_of_hasDerivAt_of_tendsto hH.continuousAt.continuousWithinAt hHD
    (hgI.add (hlI.const_mul κ)) hT
  rw [hH₀, sub_zero, integral_add hgI (hlI.const_mul κ), integral_const_mul, add_eq_zero_iff_eq_neg,
    ← neg_mul] at hInt
  exact hInt

/-- **Inversion**: for `α > −1`, `|β| ≤ α + 1` and smooth even compactly supported `f`,
`f(t) = (2π)⁻¹ ∫₀^∞ f̃(λ) φ_λ(t) |c(λ)|⁻² dλ`. -/
theorem jacobiTransform_inversion (α β : ℝ) (hα : -1 < α) (hβ : |β| ≤ α + 1) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) (heven : ∀ t, f (-t) = f t) (t : ℝ) :
    f t = ∫ lam in Ioi (0 : ℝ), jacobiTransform α β f lam * jacobiFunction α β lam t *
      ((2 * π)⁻¹ * ‖cFunction α β lam‖⁻¹ ^ 2 : ℝ) := by
  sorry

/-- **Plancherel**: `∫₀^∞ |f|² Δ dt = (2π)⁻¹ ∫₀^∞ |f̃(λ)|² |c(λ)|⁻² dλ`. -/
theorem jacobiTransform_plancherel (α β : ℝ) (hα : -1 < α) (hβ : |β| ≤ α + 1) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) (heven : ∀ t, f (-t) = f t) :
    ∫ t in Ioi 0, ‖f t‖ ^ 2 * jacobiWeight α β t =
      ∫ lam in Ioi (0 : ℝ),
        ‖jacobiTransform α β f lam‖ ^ 2 * ((2 * π)⁻¹ * ‖cFunction α β lam‖⁻¹ ^ 2) := by
  sorry

/-- **The unitary Jacobi transform**
`L²((0, ∞), Δ dt) ≃ L²((0, ∞), (2π)⁻¹ |c|⁻² dλ)`, extending the transform of smooth even
compactly supported functions. -/
theorem exists_jacobiTransform_linearIsometryEquiv (α β : ℝ) (hα : -1 < α)
    (hβ : |β| ≤ α + 1) :
    ∃ U : Lp ℂ 2 (jacobiMeasure α β) ≃ₗᵢ[ℂ] Lp ℂ 2 (jacobiPlancherelMeasure α β),
      ∀ f : ℝ → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f → (∀ t, f (-t) = f t) →
        ∀ (hf : MemLp f 2 (jacobiMeasure α β))
          (hf' : MemLp (fun lam : ℝ => jacobiTransform α β f lam) 2
            (jacobiPlancherelMeasure α β)),
          U (hf.toLp f) = hf'.toLp _ := by
  sorry

end SFVK.RankOne
