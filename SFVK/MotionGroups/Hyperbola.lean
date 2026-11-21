/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic.Definitions
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import SFVK.MotionGroups.Basic.Hyperbola
import DLMF.Bessel.KIntegralRep
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Analysis.Fourier.Integrable
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import SFVKMathlib.MeasureTheory.Group.Multiplier
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence

/-!
# The hyperbola model of `ISO(1,1)` and the Macdonald kernel

The operators of the hyperbola model form a representation; it has an `L²(ℝ)` realization
exactly for `Re R = 0`, and that realization is unitary. In the two-sided Laplace model boosts
act diagonally and the translations by an integral kernel whose inner integral is
`2 K_{λ-a-it}(R r)`. Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*,
Vol. 1, §§4.2.1–4.2.4, pp. 171–176; DLMF 10.32.9 through lean-DLMF's
`DLMF.Bessel.besselK_eq_half_integral`. Strong continuity uses Mathlib's continuity of
measure-preserving composition in `L²` and Tau Ceti's dominated convergence there.
The translation formula uses Mathlib's Fourier inversion, Tau Ceti's Fourier integrability for
smooth compactly supported functions, and lean-DLMF's integrability of the Bessel kernel.
-/

public noncomputable section

open Complex MeasureTheory Filter Set MulAction
open scoped Real Topology ENNReal FourierTransform InnerProductSpace ContDiff

namespace SFVK.MotionGroups

/-- Representation law of the hyperbola model. -/
theorem hyperbolaAction_mul (R : ℂ) (g h : ISO11) (Φ : ℝ → ℂ) :
    hyperbolaAction R (g * h) Φ = hyperbolaAction R g (hyperbolaAction R h Φ) := by
  funext θ
  have hshift : θ - (g.s + h.s) = θ - g.s - h.s := by ring
  have hpair : (g * h).a.1 * Real.cosh θ - (g * h).a.2 * Real.sinh θ =
      (g.a.1 * Real.cosh θ - g.a.2 * Real.sinh θ) +
        (h.a.1 * Real.cosh (θ - g.s) - h.a.2 * Real.sinh (θ - g.s)) := by
    simp only [ISO11.mul_a, Prod.fst_add, Prod.snd_add, lorentzBoost_def, Real.cosh_sub,
      Real.sinh_sub]
    ring
  simp only [hyperbolaAction_def, ISO11.mul_s, hshift, hpair,
    Complex.ofReal_add, mul_add, Complex.exp_add, mul_assoc]

namespace HyperbolaRealization

local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-- The boost parameter acts by translations of the real coordinate. -/
local instance : MulAction ISO11 ℝ where
  smul g t := t + g.s
  one_smul t := by change t + 0 = t; simp
  mul_smul g h t := by change t + (g.s + h.s) = t + h.s + g.s; abel

/-- Boost translations preserve Lebesgue measure. -/
private theorem measurePreserving_shift (g : ISO11) :
    MeasurePreserving (fun t : ℝ => g • t) volume volume :=
  measurePreserving_add_right volume g.s

/-- The multiplier of the hyperbola action, given by its value on the constant function. -/
private def weight (R : ℂ) (g : ISO11) (t : ℝ) : ℂ := hyperbolaAction R g (fun _ => 1) t

/-- Multiplication by the weight and inverse translation give the model action. -/
private theorem weight_action (R : ℂ) (g : ISO11) (f : ℝ → ℂ) :
    multiplierAction (weight R) g f = hyperbolaAction R g f := by
  funext t
  simp only [multiplierAction_def, hyperbolaAction_def, weight, mul_one]
  rfl

/-- The group action on functions gives the cocycle law of the weight. -/
private theorem isMultiplierCocycle_weight (R : ℂ) : IsMultiplierCocycle (weight R) := by
  apply (multiplierAction_law_iff _).mp
  constructor
  · intro f t
    rw [weight_action, hyperbolaAction_one]
  · intro g h f t
    rw [weight_action, weight_action, weight_action, hyperbolaAction_mul]

/-- Hyperbola multipliers are jointly continuous in the group element and real coordinate. -/
private theorem continuous_weight (R : ℂ) :
    Continuous (fun p : ISO11 × ℝ => weight R p.1 p.2) := by
  have h : Continuous (fun g : ISO11 => (g.a, g.s)) := continuous_induced_dom
  have hfst : Continuous (fun p : ISO11 × ℝ => p.1.a.1) := h.fst.fst.comp continuous_fst
  have hsnd : Continuous (fun p : ISO11 × ℝ => p.1.a.2) := h.fst.snd.comp continuous_fst
  simp only [weight, hyperbolaAction_def, mul_one]
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    ((hfst.mul (Real.continuous_cosh.comp continuous_snd)).sub
      (hsnd.mul (Real.continuous_sinh.comp continuous_snd))))).cexp

/-- For imaginary spectral parameter the hyperbola multiplier has modulus one. -/
private theorem norm_weight (R : ℂ) (hR : R.re = 0) (g : ISO11) (t : ℝ) :
    ‖weight R g t‖ = 1 := by
  simp [weight, hyperbolaAction_def, Complex.norm_exp, Complex.mul_re, hR]

/-- A pure translation must act unboundedly if the real part of the parameter is nonzero. -/
private theorem re_eq_zero_of_realization {R : ℂ}
    {U : ContRepresentation ℂ ISO11 H} (hU : IsHyperbolaRealization R U) : R.re = 0 := by
  by_contra hR
  let g : ISO11 := ⟨(-R.re, 0), 0⟩
  let C := ‖U g‖ + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun t : ℝ => Real.exp (R.re ^ 2 * Real.cosh t)) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (Filter.Tendsto.const_mul_atTop (sq_pos_of_ne_zero hR) Real.tendsto_cosh_atTop)
  obtain ⟨a, ha⟩ := eventually_atTop.1 (hlim.eventually (eventually_ge_atTop C))
  let s := Icc a (a + 1)
  have hmeas : MeasurableSet s := measurableSet_Icc
  have hμ : volume s = 1 := by simp [s, Real.volume_Icc]
  have hfin : volume s ≠ ⊤ := by simp [hμ]
  let f : H := indicatorConstLp 2 hmeas hfin (1 : ℂ)
  let b : H := indicatorConstLp 2 hmeas hfin (C : ℂ)
  have hf : ‖f‖ = 1 := by
    dsimp only [f]
    rw [norm_indicatorConstLp (by norm_num) (by simp), measureReal_def, hμ]
    simp
  have hb : ‖b‖ = C := by
    dsimp only [b]
    rw [norm_indicatorConstLp (by norm_num) (by simp), measureReal_def, hμ]
    simp [Complex.norm_real, Real.norm_of_nonneg hC]
  have hnorm : ∀ᵐ t ∂(volume : Measure ℝ), ‖b t‖ ≤ ‖U g f t‖ := by
    filter_upwards [hU.1 g f, indicatorConstLp_coeFn_mem (p := (2 : ℝ≥0∞))
      (hs := hmeas) (hμs := hfin) (c := (1 : ℂ)),
      indicatorConstLp_coeFn_mem (p := (2 : ℝ≥0∞)) (hs := hmeas) (hμs := hfin) (c := (C : ℂ)),
      indicatorConstLp_coeFn_notMem (p := (2 : ℝ≥0∞))
        (hs := hmeas) (hμs := hfin) (c := (C : ℂ))] with t ht ht₁ htC ht₀
    by_cases hs : t ∈ s
    · have htform : hyperbolaAction R g f t =
          Complex.exp (-R * ((-R.re * Real.cosh t : ℝ) : ℂ)) := by
        simpa [hyperbolaAction_def, g] using congrArg
          (fun z : ℂ => Complex.exp (-R * ((-R.re * Real.cosh t : ℝ) : ℂ)) * z) (ht₁ hs)
      rw [ht, htform, htC hs, Complex.norm_real, Real.norm_of_nonneg hC, Complex.norm_exp]
      have he : (-R * ((-R.re * Real.cosh t : ℝ) : ℂ)).re = R.re ^ 2 * Real.cosh t := by
        simp [Complex.mul_re]
        ring
      rw [he]
      exact ha t hs.1
    · rw [ht₀ hs, norm_zero]
      exact norm_nonneg _
  have hle : ‖b‖ ≤ ‖U g f‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
      (eLpNorm_mono_ae (Lp.aestronglyMeasurable b) hnorm)
  have hu := (U g).le_opNorm f
  rw [hb] at hle
  rw [hf, mul_one] at hu
  dsimp [C] at hle
  linarith

/-- Multiplication by a unit-modulus hyperbola weight is defined on all of the Hilbert space. -/
private theorem memLp_weight_mul (R : ℂ) (hR : R.re = 0) (g : ISO11) (f : H) :
    MemLp (fun t : ℝ => weight R g t * f t) 2 volume := by
  have hc : Continuous (weight R g) :=
    (continuous_weight R).comp (continuous_const.prodMk continuous_id)
  apply (Lp.memLp f).congr_norm (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall fun t => by
    simp only [Pi.mul_apply, norm_mul, norm_weight R hR, one_mul]

/-- The Hilbert-space operator of multiplication by a unit-modulus hyperbola weight. -/
private def multiply (R : ℂ) (hR : R.re = 0) (g : ISO11) (f : H) : H :=
  (memLp_weight_mul R hR g f).toLp _

/-- The Hilbert-space multiplier agrees with the pointwise formula. -/
private theorem multiply_ae (R : ℂ) (hR : R.re = 0) (g : ISO11) (f : H) :
    (multiply R hR g f : ℝ → ℂ) =ᵐ[volume] fun t => weight R g t * f t :=
  (memLp_weight_mul R hR g f).coeFn_toLp

/-- Multiplication by the weight is an isometry. -/
private theorem isometry_multiply (R : ℂ) (hR : R.re = 0) (g : ISO11) :
    Isometry (multiply R hR g) := by
  apply Isometry.of_dist_eq
  intro f k
  rw [dist_eq_norm, dist_eq_norm, Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [Lp.coeFn_sub (multiply R hR g f) (multiply R hR g k),
    Lp.coeFn_sub f k, multiply_ae R hR g f, multiply_ae R hR g k] with t h₁ h₂ h₃ h₄
  rw [h₁, h₂, Pi.sub_apply, Pi.sub_apply, h₃, h₄, ← mul_sub, norm_mul,
    norm_weight R hR, one_mul]

/-- The weight multiplication operators are strongly continuous. -/
private theorem continuous_multiply (R : ℂ) (hR : R.re = 0) (f : H) :
    Continuous (fun g => multiply R hR g f) := by
  have hi : Topology.IsInducing (fun g : ISO11 => (g.a, g.s)) := ⟨rfl⟩
  let : FirstCountableTopology ISO11 := hi.firstCountableTopology
  rw [continuous_iff_continuousAt]
  intro g
  apply TauCeti.tendsto_toLp_of_ae_tendsto_of_norm_le (by simp)
    (fun k => memLp_weight_mul R hR k f) (multiply_ae R hR g f)
  · exact fun k => Eventually.of_forall fun t => by simp only [norm_mul, norm_weight R hR, le_refl]
  · exact Eventually.of_forall fun t =>
      ((continuous_weight R).comp (continuous_id.prodMk continuous_const)).continuousAt.mul
        continuousAt_const

/-- The continuous map of real coordinate shifts belonging to a group element. -/
private def shiftMap (g : ISO11) : C(ℝ, ℝ) :=
  ⟨fun t => t - g.s, continuous_id.sub continuous_const⟩

/-- The translation part acts strongly continuously on the Hilbert space. -/
private theorem continuous_shift (f : H) :
    Continuous (fun g : ISO11 =>
      Lp.compMeasurePreserving (shiftMap g) (measurePreserving_shift g⁻¹) f) := by
  have h : Continuous (fun g : ISO11 => (g.a, g.s)) := continuous_induced_dom
  refine continuous_const.compMeasurePreservingLp
    (ContinuousMap.continuous_of_continuous_uncurry shiftMap ?_) _ (by simp)
  exact continuous_snd.sub (h.snd.comp continuous_fst)

/-- Imaginary parameters give a strongly continuous Hilbert-space realization. -/
private theorem exists_realization {R : ℂ} (hR : R.re = 0) :
    ∃ U, IsHyperbolaRealization R U := by
  let shift (g : ISO11) (f : H) :=
    Lp.compMeasurePreserving (shiftMap g) (measurePreserving_shift g⁻¹) f
  let act (g : ISO11) (f : H) := multiply R hR g (shift g f)
  have hact (g : ISO11) (f : H) :
      (act g f : ℝ → ℂ) =ᵐ[volume] multiplierAction (weight R) g f := by
    filter_upwards [multiply_ae R hR g (shift g f),
      Lp.coeFn_compMeasurePreserving f (measurePreserving_shift g⁻¹)] with t hm hs
    rw [hm]
    exact congrArg (fun z : ℂ => weight R g t * z) hs
  have hmem (g : ISO11) (f : H) : MemLp (multiplierAction (weight R) g f) 2 volume :=
    (Lp.memLp (act g f)).ae_eq (hact g f)
  have hnorm (g : ISO11) (f : H) : ‖act g f‖ = ‖f‖ := by
    have hzero : multiply R hR g 0 = 0 := by
      apply Lp.ext
      filter_upwards [multiply_ae R hR g 0, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t ht ht₀
      rw [ht, ht₀, Pi.zero_apply, mul_zero]
    calc ‖act g f‖ = dist (multiply R hR g (shift g f)) (multiply R hR g 0) := by
           rw [hzero, dist_zero_right]
         _ = ‖f‖ := by
           rw [(isometry_multiply R hR g).dist_eq, dist_zero_right]
           exact Lp.norm_compMeasurePreserving _ _
  have hbound (g : ISO11) : ∃ C : ℝ, ∀ f : H,
      ‖(hmem g f).toLp (multiplierAction (weight R) g f)‖ ≤ C * ‖f‖ := by
    refine ⟨1, fun f => ?_⟩
    have h := Lp.ext ((hmem g f).coeFn_toLp.trans (hact g f).symm)
    rw [h, hnorm, one_mul]
  obtain ⟨U, hU⟩ := exists_multiplierRepresentation (isMultiplierCocycle_weight R)
    (fun g => (measurePreserving_shift g).quasiMeasurePreserving) hmem hbound
  refine ⟨U, fun g f => (hU g f).trans (by rw [weight_action]), ?_⟩
  intro f
  have hf (g : ISO11) : U g f = act g f := Lp.ext ((hU g f).trans (hact g f).symm)
  simp_rw [hf]
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have ht : ∀ᶠ g in 𝓝 g₀, dist (shift g f) (shift g₀ f) < ε / 2 :=
    Metric.tendsto_nhds.mp (continuous_shift f).continuousAt (ε / 2) (by positivity)
  have hm : ∀ᶠ g in 𝓝 g₀,
      dist (multiply R hR g (shift g₀ f)) (multiply R hR g₀ (shift g₀ f)) < ε / 2 :=
    Metric.tendsto_nhds.mp (continuous_multiply R hR (shift g₀ f)).continuousAt
      (ε / 2) (by positivity)
  filter_upwards [ht, hm] with g ht hm
  calc
    dist (act g f) (act g₀ f) ≤
        dist (shift g f) (shift g₀ f) +
          dist (multiply R hR g (shift g₀ f)) (multiply R hR g₀ (shift g₀ f)) := by
      simpa only [act, (isometry_multiply R hR g).dist_eq] using
        dist_triangle (act g f) (multiply R hR g (shift g₀ f)) (act g₀ f)
    _ < ε := by linarith

/-- Any realization with an imaginary parameter is unitary. -/
private theorem isUnitary_of_realization {R : ℂ} (hR : R.re = 0)
    {U : ContRepresentation ℂ ISO11 H} (hU : IsHyperbolaRealization R U) : U.IsUnitary := by
  apply (ContRepresentation.isUnitary_iff_norm_map _).mpr
  intro g f
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  calc
    _ = eLpNorm ((f : ℝ → ℂ) ∘ fun t : ℝ => t - g.s) 2 volume := by
      apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
        ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
          (measurePreserving_shift g⁻¹).quasiMeasurePreserving)
      filter_upwards [hU.1 g f] with t ht
      rw [ht, ← weight_action, multiplierAction_def, norm_mul, norm_weight R hR, one_mul]
      rfl
    _ = _ := eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f)
      (measurePreserving_shift g⁻¹)

end HyperbolaRealization

open HyperbolaRealization

/-- `L²` realization exactly on the imaginary axis (Vilenkin–Klimyk Vol. 1 §4.2.3, pp. 173–175). -/
theorem exists_hyperbolaRealization_iff (R : ℂ) :
    (∃ U, IsHyperbolaRealization R U) ↔ R.re = 0 := by
  exact ⟨fun ⟨U, hU⟩ => re_eq_zero_of_realization hU, exists_realization⟩

/-- The totalized hyperbola representation is unitary for every parameter.
For `R.re ≠ 0` its value is the trivial representation. The parameter range for the
pointwise model is given by `exists_hyperbolaRealization_iff`. -/
theorem isUnitary_hyperbolaRep (R : ℂ) : (hyperbolaRep R).IsUnitary := by
  classical
  by_cases hR : R.re = 0
  · exact isUnitary_of_realization hR
      (isHyperbolaRealization_hyperbolaRep (exists_realization hR))
  · unfold hyperbolaRep
    rw [dite_eq_right (fun h => hR ((exists_hyperbolaRealization_iff R).mp h))]
    exact ContRepresentation.isUnitary_trivial

/-- Boosts act diagonally in the Laplace realization (Vilenkin–Klimyk Vol. 1 §4.2.4 (3),
pp. 175–176). -/
theorem fourierLaplace_hyperbolaAction_boost (R : ℂ) (s : ℝ) (Φ : ℝ → ℂ)
    (lam : ℂ) :
    fourierLaplace (hyperbolaAction R ⟨0, s⟩ Φ) lam =
      Complex.exp (lam * s) * fourierLaplace Φ lam := by
  simp only [fourierLaplace_def, hyperbolaAction_def, Prod.fst_zero, Prod.snd_zero,
    zero_mul, sub_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  let kernel (θ : ℝ) := Φ (θ - s) * Complex.exp (lam * (θ : ℝ))
  calc
    _ = ∫ θ : ℝ, kernel (θ + s) := (integral_add_right_eq_self kernel s).symm
    _ = _ := by
      simp only [kernel, add_sub_cancel_right, Complex.ofReal_add, mul_add, Complex.exp_add]
      simp_rw [show ∀ θ : ℝ, Φ θ * (Complex.exp (lam * θ) * Complex.exp (lam * s)) =
        Complex.exp (lam * s) * (Φ θ * Complex.exp (lam * θ)) by intro; ring,
        integral_const_mul]

/-- Translations act by an integral kernel (Vilenkin–Klimyk Vol. 1 §4.2.4 (4)–(6),
pp. 175–176): for `Re R > 0`, `r > 0` and real `a`,
`F_g(λ) = (1/2π) ∫ (∫ e^{-R r cosh θ + (λ - a - it) θ} dθ) F(a + it) dt`. -/
theorem fourierLaplace_hyperbolaAction_translation {R : ℂ} (hR : 0 < R.re) {r : ℝ} (hr : 0 < r)
    (a : ℝ) (Φ : ℝ → ℂ) (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ) (lam : ℂ) :
    fourierLaplace (hyperbolaAction R ⟨(r, 0), 0⟩ Φ) lam =
      (2 * π)⁻¹ * ∫ t : ℝ,
        (∫ θ : ℝ, Complex.exp (-R * r * Real.cosh θ + (lam - (a + t * I)) * θ)) *
          fourierLaplace Φ (a + t * I) := by
  let f (x : ℝ) := Φ x * Complex.exp (a * x)
  let K (x : ℝ) := DLMF.Bessel.besselKKernel (lam - a) (R * r) x
  let P (t : ℝ) := fourierLaplace Φ (a + t * I)
  let e (t x : ℝ) := Complex.exp (-(t * x : ℝ) * I)
  have hf : ContDiff ℝ ∞ f := by
    have hcast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
    exact hΦ.mul ((contDiff_const.mul hcast).cexp)
  have hfc : HasCompactSupport f := hc.mul_right (f' := fun x : ℝ => Complex.exp (a * x))
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hh : Integrable (𝓕 f) :=
    hf.integrable_fourier_of_hasCompactSupport hfc
  have hP (t : ℝ) : P t = 𝓕⁻ f (t / (2 * π)) := by
    change fourierLaplace Φ (a + t * I) = _
    rw [Real.fourierInv_eq', fourierLaplace_def]
    apply integral_congr_ae
    filter_upwards with θ
    have hθ : 2 * π * ⟪θ, t / (2 * π)⟫_ℝ = t * θ := by
      change 2 * π * (t / (2 * π) * θ) = t * θ
      field_simp [Real.pi_ne_zero]
    rw [hθ]
    simp only [f, smul_eq_mul]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hPi : Integrable P := by
    rw [show P = fun t : ℝ => 𝓕 f (t / (-(2 * π))) by
      funext t
      rw [hP, Real.fourierInv_eq_fourier_neg, div_neg]]
    exact hh.comp_div (neg_ne_zero.mpr Real.two_pi_pos.ne')
  have hK : Integrable K := DLMF.Bessel.integrable_besselKKernel (by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      using mul_pos hR hr)
  have hInv (x : ℝ) : f x = (2 * π : ℂ)⁻¹ * ∫ t, e t x * P t := by
    have h := hfi.fourier_fourierInv_eq hh (v := x) hf.continuous.continuousAt
    rw [Real.fourier_real_eq_integral_exp_smul] at h
    let G (s : ℝ) := Complex.exp ((-(2 * π * s * x) : ℝ) * I) * 𝓕⁻ f s
    have hG : (∫ t, e t x * P t) = ∫ t, G (t / (2 * π)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hP]
      dsimp only [G, e]
      congr 2
      push_cast
      field_simp [Real.pi_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    rw [hG, Measure.integral_comp_div, abs_of_pos Real.two_pi_pos, Complex.real_smul, ← mul_assoc,
      Complex.ofReal_mul, Complex.ofReal_ofNat,
      inv_mul_cancel₀ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)),
      one_mul]
    simpa only [G, smul_eq_mul, neg_mul] using h.symm
  have hprod : Integrable (Function.uncurry (fun x t => K x * e t x * P t))
      ((volume : Measure ℝ).prod volume) := by
    have hmajor : Integrable (fun p : ℝ × ℝ => ‖K p.1‖ * ‖P p.2‖) _ :=
      hK.norm.mul_prod hPi.norm
    refine hmajor.mono' ?_ ?_
    · change AEStronglyMeasurable (fun p : ℝ × ℝ => K p.1 * e p.2 p.1 * P p.2) _
      exact ((hK.aestronglyMeasurable.comp_fst).mul (by dsimp [e]; fun_prop)).mul
        hPi.aestronglyMeasurable.comp_snd
    · exact Eventually.of_forall fun p => by
        have he : ‖e p.2 p.1‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
        change ‖K p.1 * e p.2 p.1 * P p.2‖ ≤ ‖K p.1‖ * ‖P p.2‖
        simp only [norm_mul, he, mul_one, le_rfl]
  calc
    _ = ∫ x, K x * f x := by
      rw [fourierLaplace_def]
      apply integral_congr_ae
      filter_upwards with x
      simp only [hyperbolaAction_def, sub_zero, f, K, DLMF.Bessel.besselKKernel]
      rw [mul_left_comm, mul_assoc, mul_left_comm _ (Φ x), ← Complex.exp_add, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    _ = (2 * π : ℂ)⁻¹ * ∫ x, ∫ t, K x * e t x * P t := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [hInv, mul_left_comm, ← integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = (2 * π : ℂ)⁻¹ * ∫ t, ∫ x, K x * e t x * P t := by
      rw [integral_integral_swap hprod]
    _ = _ := by
      push_cast
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [integral_mul_const]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [K, e, DLMF.Bessel.besselKKernel]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring

/-- The Macdonald kernel: for `Re z > 0`, `∫ e^{-z cosh θ + μθ} dθ = 2 K_μ(z)` (DLMF 10.32.9). -/
theorem integral_exp_cosh_eq_besselK (μ : ℂ) {z : ℂ} (hz : 0 < z.re) :
    ∫ θ : ℝ, Complex.exp (-z * Real.cosh θ + μ * θ) = 2 * DLMF.Bessel.besselK μ z := by
  rw [DLMF.Bessel.besselK_eq_half_integral μ hz]
  simp only [neg_mul]
  ring

end SFVK.MotionGroups
