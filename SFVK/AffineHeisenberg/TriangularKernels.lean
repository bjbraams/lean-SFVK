/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.AffineHeisenberg.Basic
public import DLMF.Confluent.Basic.Whittaker
import DLMF.Gamma.MellinBarnes
import DLMF.Confluent.IntegralRepresentations.EulerAndBessel
import DLMF.Confluent.KummerProperties
import DLMFMathlib.Analysis.SpecialFunctions.Pow.ComplexReal
import DLMFMathlib.Analysis.MellinCubicLaplace
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Triangular group Mellin kernels

Explicit kernel evaluations in §2 of `Roadmaps/AffineHeisenbergGroups/README.md` (section
numbers `§x.y`).
Sources: Vilenkin–Klimyk Vol. 1 §§5.1–5.2, pp. 207–220; Klimyk–Vilenkin Ch. 4 §1.4 (11)–(21), pp.
205–207.
The kernels use lean-DLMF's exponential Mellin, beta, Tricomi and Kummer integrals.
-/

@[expose] public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open DLMF.Confluent
open scoped Real ComplexConjugate InnerProductSpace ENNReal

/-- Translating the positive half-line by the parameter shifts its integration bound. -/
private theorem integral_Ioi_translate (t : ℝ) (f : ℝ → ℂ) :
    (∫ x in Ioi t, f x) = ∫ x in Ioi (0 : ℝ), f (x + t) := by
  let e := MeasurableEquiv.addRight t
  have hpre : e '' Ioi (0 : ℝ) = Ioi t := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change t < y + t
      exact lt_add_of_pos_left _ hy
    · intro hx
      exact ⟨x - t, sub_pos.mpr hx, sub_add_cancel _ _⟩
  have h := (measurePreserving_add_right volume t).setIntegral_image_emb
    e.measurableEmbedding f (Ioi (0 : ℝ))
  rw [← hpre]
  exact h

/-- The scaled beta integral over a half-line. -/
private theorem integral_triangular_beta_Ioi (lam μ : ℂ) {t : ℝ} (ht : 0 < t)
    (hlam : 0 < lam.re) (hlm : lam.re < μ.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (lam - 1) * ((x + t : ℝ) : ℂ) ^ (-μ)) =
      (t : ℂ) ^ (lam - μ) * (Gamma lam * Gamma (μ - lam) / Gamma μ) := by
  let f : ℝ → ℂ := fun x => ((1 + x : ℝ) : ℂ) ^ (-μ)
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hfun (x : ℝ) (hx : x ∈ Ioi 0) :
      ((x + t : ℝ) : ℂ) ^ (-μ) = (t : ℂ) ^ (-μ) • f (t⁻¹ * x) := by
    have hR : t * (1 + t⁻¹ * x) = x + t := by
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ ht.ne', mul_one, one_mul, add_comm]
    rw [← hR, ofReal_mul, mul_cpow_ofReal_nonneg ht.le (by have : 0 < x := hx; positivity)]
    rfl
  calc
    _ = mellin (fun x => (t : ℂ) ^ (-μ) • f (t⁻¹ * x)) lam := by
      rw [mellin]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [smul_eq_mul] at hfun ⊢
      rw [hfun x hx]
    _ = _ := by
      rw [mellin_const_smul, mellin_comp_mul_left f lam (inv_pos.mpr ht),
        DLMF.Gamma.mellin_one_add_cpow_neg hlam hlm, smul_eq_mul, smul_eq_mul, ofReal_inv,
        inv_cpow _ _ (by rw [arg_ofReal_of_nonneg ht.le]; exact Real.pi_ne_zero.symm),
        ← cpow_neg, neg_neg, ← mul_assoc, ← cpow_add _ _ ht']
      congr 1
      ring_nf

/-- §2.4. **Kernels of `g_+(t)`.** -/
theorem triangularKernel_gPlus (σ ω lam μ : ℂ) (t : ℝ) (ht : 0 < t) :
    (lam.re < μ.re → 0 < lam.re →
      triangularKernel σ ω 1 1 lam μ (gPlus t) =
        Gamma (μ - lam) * Gamma lam / (2 * π * Complex.I * Gamma μ) * (t : ℂ) ^ (lam - μ)) ∧
    (0 < lam.re → μ.re < 1 →
      triangularKernel σ ω (-1) 1 lam μ (gPlus t) =
        Gamma lam * Gamma (1 - μ) / (2 * π * Complex.I * Gamma (lam - μ + 1)) *
          (t : ℂ) ^ (lam - μ)) ∧
    (lam.re < μ.re → μ.re < 1 →
      triangularKernel σ ω (-1) (-1) lam μ (gPlus t) =
        Gamma (1 - μ) * Gamma (μ - lam) / (2 * π * Complex.I * Gamma (1 - lam)) *
          (t : ℂ) ^ (lam - μ)) ∧
    triangularKernel σ ω 1 (-1) lam μ (gPlus t) = 0 := by
  have hpos : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < x + t} = Ioi 0 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, and_iff_left_iff_imp]
    intro hx
    linarith
  have hfin : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < -x + t} = Ioo 0 t := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁, by linarith⟩
  have htail : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < -(-x + t)} = Ioi t := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq]
    constructor
    · rintro ⟨_, hx⟩
      linarith
    · intro hx
      exact ⟨by linarith, by linarith⟩
  have hzero : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < -(x + t)} = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hx
    linarith
  have hplus : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (lam - 1) *
        ((|x + t| : ℝ) : ℂ) ^ (-μ)) =
        ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (lam - 1) * ((x + t : ℝ) : ℂ) ^ (-μ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [abs_of_pos (add_pos (show 0 < x from hx) ht)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hlm hlam
    simp only [triangularKernel, gPlus, ofReal_zero, mul_zero, zero_mul, add_zero, Real.exp_zero,
      Complex.exp_zero, one_mul, Units.val_one, Int.cast_one, mul_one, hpos, hplus]
    rw [integral_triangular_beta_Ioi lam μ ht hlam hlm]
    ring
  · intro hlam hμ
    simp only [triangularKernel, gPlus, ofReal_zero, mul_zero, add_zero, Real.exp_zero,
      Complex.exp_zero, one_mul, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg,
      neg_one_mul, zero_mul, mul_one, hfin]
    have hB := betaIntegral_scaled lam (1 - μ) ht
    rw [intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo,
      show 1 - μ - 1 = -μ by ring, show lam + (1 - μ) - 1 = lam - μ by ring,
      betaIntegral_eq_Gamma_mul_div _ _ hlam (by simpa only [sub_re, one_re] using sub_pos.mpr hμ),
      show lam + (1 - μ) = lam - μ + 1 by ring] at hB
    have hInt : (∫ x in Ioo (0 : ℝ) t, (x : ℂ) ^ (lam - 1) *
        ((|-x + t| : ℝ) : ℂ) ^ (-μ)) =
        ∫ x in Ioo (0 : ℝ) t, (x : ℂ) ^ (lam - 1) * ((t : ℂ) - x) ^ (-μ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      dsimp only
      rw [neg_add_eq_sub, abs_of_pos (sub_pos.mpr hx.2), ofReal_sub]
    rw [hInt, hB]
    ring
  · intro hlm hμ
    simp only [triangularKernel, gPlus, ofReal_zero, mul_zero, add_zero, Real.exp_zero,
      Complex.exp_zero, one_mul, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      neg_one_mul,
      zero_mul, mul_one, htail]
    rw [integral_Ioi_translate t]
    have hInt : (∫ x in Ioi (0 : ℝ), ((x + t : ℝ) : ℂ) ^ (lam - 1) *
        ((|-(x + t) + t| : ℝ) : ℂ) ^ (-μ)) =
        ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ ((1 - μ) - 1) * ((x + t : ℝ) : ℂ) ^ (-(1 - lam)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [show -(x + t) + t = -x by ring, abs_neg, abs_of_pos hx,
        show 1 - μ - 1 = -μ by ring, show -(1 - lam) = lam - 1 by ring, mul_comm]
    rw [hInt, integral_triangular_beta_Ioi (1 - μ) (1 - lam) ht
      (by simpa only [sub_re, one_re] using sub_pos.mpr hμ)
      (by simp only [sub_re, one_re]; linarith),
      show 1 - μ - (1 - lam) = lam - μ by ring,
      show 1 - lam - (1 - μ) = μ - lam by ring]
    ring
  · simp only [triangularKernel, gPlus, ofReal_zero, mul_zero, add_zero, Real.exp_zero,
      Complex.exp_zero, one_mul, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      neg_one_mul, zero_mul, mul_one, hzero, Measure.restrict_empty, integral_zero_measure]

/-- §2.4. **Kernel of `g_-(t)`.** -/
theorem triangularKernel_gMinus (σ ω lam μ : ℂ) (t : ℝ) (hσt : (σ * t).re < 0)
    (hlm : μ.re < lam.re) :
    triangularKernel σ ω 1 1 lam μ (gMinus t) =
      Gamma (lam - μ) * (-σ * t) ^ (μ - lam) / (2 * π * Complex.I) ∧
    triangularKernel σ ω 1 (-1) lam μ (gMinus t) = 0 ∧
    triangularKernel σ ω (-1) 1 lam μ (gMinus t) = 0 := by
  have hpos : 0 < (-σ * t).re := by rw [neg_mul, neg_re]; linarith
  have hRe : 0 < (lam - μ).re := by simpa only [sub_re] using sub_pos.mpr hlm
  have hset : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < -x} = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_empty_iff_false, iff_false,
      not_and]
    intro hx
    linarith
  have hset' : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < x} = Ioi 0 := inter_self _
  refine ⟨?_, ?_, ?_⟩
  · simp only [triangularKernel, gMinus, ofReal_zero, mul_zero, Complex.exp_zero,
      Real.exp_zero, Units.val_one, Int.cast_one, one_mul, add_zero, mul_one]
    rw [hset']
    have hEq : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (lam - 1) * cexp (σ * t * x) *
        ((|x| : ℝ) : ℂ) ^ (-μ)) =
        mellin (fun x : ℝ => cexp (-((-σ * t) * x))) (lam - μ) := by
      rw [mellin]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx' : 0 < x := hx
      dsimp only
      rw [abs_of_pos hx', smul_eq_mul, mul_right_comm,
        ← cpow_add _ _ (ofReal_ne_zero.mpr hx'.ne'), neg_mul, neg_mul, neg_neg]
      congr 2
      ring
    rw [hEq, Complex.CubicLaplace.mellin_exp_neg_mul hRe hpos,
      neg_sub, one_div, div_eq_mul_inv, mul_comm]
  · simp only [triangularKernel, gMinus, ofReal_zero, mul_zero, Complex.exp_zero,
      Real.exp_zero, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, one_mul, add_zero,
      neg_one_mul]
    rw [hset, Measure.restrict_empty, integral_zero_measure, mul_zero]
  · simp only [triangularKernel, gMinus, ofReal_zero, mul_zero, Complex.exp_zero,
      Real.exp_zero, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, one_mul, add_zero,
      neg_one_mul]
    rw [hset, Measure.restrict_empty, integral_zero_measure, mul_zero]

/-- Scaling the two positive arguments collects their two complex exponents. -/
private theorem mul_cpow_scale (t x y : ℝ) (ht : 0 < t) (hx : 0 ≤ x) (hy : 0 ≤ y) (p q : ℂ) :
    ((t * x : ℝ) : ℂ) ^ p * ((t * y : ℝ) : ℂ) ^ q =
      (t : ℂ) ^ (p + q) * (x : ℂ) ^ p * (y : ℂ) ^ q := by
  rw [ofReal_mul, ofReal_mul, mul_cpow_ofReal_nonneg ht.le hx, mul_cpow_ofReal_nonneg ht.le hy,
    mul_mul_mul_comm, ← cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), mul_assoc]

/-- Tricomi's Laplace integral, scaled to the triangular group parameters. -/
private theorem integral_scaled_whittakerW (a q : ℂ) {t : ℝ} (ht : 0 < t) (ha : 0 < a.re) :
    cexp (-((t : ℂ) ^ 2) / 2) * (∫ x in Ioi (0 : ℝ),
      (x : ℂ) ^ (a - 1) * ((x + t : ℝ) : ℂ) ^ q * cexp (-(t : ℂ) * x)) =
      Gamma a * whittakerW ((q - a + 1) / 2) ((a + q) / 2) ((t : ℂ) ^ 2) / t := by
  let F : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (a - 1) * ((x + t : ℝ) : ℂ) ^ q * cexp (-(t : ℂ) * x)
  let K : ℝ → ℂ := fun u =>
    cexp (-((t : ℂ) ^ 2) * u) * (u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ q
  have hscale := integral_comp_mul_left_Ioi' F 0 ht
  simp only [mul_zero, real_smul] at hscale
  have hbase (u : ℝ) (hu : u ∈ Ioi 0) :
      F (t * u) = (t : ℂ) ^ (a - 1 + q) * K u := by
    have hx : 0 < u := hu
    dsimp only [F, K]
    rw [show t * u + t = t * (1 + u) by ring, mul_cpow_scale t u (1 + u) ht hx.le (by positivity),
      ofReal_mul, ofReal_add, ofReal_one,
      show -(t : ℂ) * (t * u) = -(t : ℂ) ^ 2 * u by ring]
    ring
  have h := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hbase
  rw [integral_const_mul] at h
  change cexp (-((t : ℂ) ^ 2) / 2) * (∫ x in Ioi (0 : ℝ), F x) = _
  rw [← hscale, h, whittakerW_eq_kummerU,
    show 1 / 2 + (a + q) / 2 - (q - a + 1) / 2 = a by ring,
    show 1 + 2 * ((a + q) / 2) = a + q + 1 by ring,
    kummerU_laplace ha (by rw [← ofReal_pow, ofReal_re]; positivity),
    show a + q + 1 - a - 1 = q by ring]
  have hpow : ((t : ℂ) ^ 2) ^ (1 / 2 + (a + q) / 2) =
      (t : ℂ) * ((t : ℂ) * (t : ℂ) ^ (a - 1 + q)) := by
    rw [← ofReal_pow, ofReal_sq_cpow ht,
      show 2 * (1 / 2 + (a + q) / 2) = 1 + (1 + (a - 1 + q)) by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_one]
  rw [hpow]
  change _ = Gamma a * (cexp (-((t : ℂ) ^ 2) / 2) * _ * (1 / Gamma a *
    (∫ u in Ioi (0 : ℝ), K u))) / t
  field_simp [ofReal_ne_zero.mpr ht.ne', Gamma_ne_zero_of_re_pos ha]

/-- Euler's integral for Kummer M on the triangular group's finite integration interval. -/
private theorem integral_scaled_whittakerM (a q : ℂ) {t : ℝ} (ht : 0 < t)
    (ha : 0 < a.re) (hq : 0 < (q + 1).re) :
    cexp (-((t : ℂ) ^ 2) / 2) * (∫ x in Ioo (0 : ℝ) t,
      (x : ℂ) ^ (a - 1) * ((t - x : ℝ) : ℂ) ^ q * cexp ((t : ℂ) * x)) =
      Gamma a * Gamma (q + 1) * whittakerM ((q - a + 1) / 2) ((a + q) / 2) ((t : ℂ) ^ 2) /
        ((t : ℂ) * Gamma (a + q + 1)) := by
  let F : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (a - 1) * ((t - x : ℝ) : ℂ) ^ q * cexp ((t : ℂ) * x)
  let K : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ q * cexp ((t : ℂ) ^ 2 * u)
  have himg : (fun u : ℝ => t * u) '' Ioo 0 1 = Ioo 0 t := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨mul_pos ht hu.1, by simpa only [mul_one] using mul_lt_mul_of_pos_left hu.2 ht⟩
    · intro hx
      exact ⟨x / t, ⟨div_pos hx.1 ht, (div_lt_one ht).mpr hx.2⟩, by
        dsimp only
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ ht.ne']⟩
  have hd (u : ℝ) : HasDerivAt (fun u => t * u) t u := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul t
  have hS := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 1)
    (f := fun u : ℝ => t * u) measurableSet_Ioo (fun u _ => (hd u).hasDerivWithinAt)
    (mul_right_injective₀ ht.ne').injOn F
  rw [himg] at hS
  have hbase (u : ℝ) (hu : u ∈ Ioo 0 1) :
      |t| • F (t * u) = ((t : ℂ) * (t : ℂ) ^ (a - 1 + q)) * K u := by
    dsimp only [F, K]
    rw [abs_of_pos ht, real_smul, show t - t * u = t * (1 - u) by ring,
      mul_cpow_scale t u (1 - u) ht hu.1.le (sub_nonneg.mpr hu.2.le),
      ofReal_mul, ofReal_sub, ofReal_one,
      show (t : ℂ) * (t * u) = (t : ℂ) ^ 2 * u by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hbase, integral_const_mul] at hS
  change cexp (-((t : ℂ) ^ 2) / 2) * (∫ x in Ioo (0 : ℝ) t, F x) = _
  rw [hS, whittakerM, show (a + q) / 2 - (q - a + 1) / 2 + 1 / 2 = a by ring,
    show 1 + 2 * ((a + q) / 2) = a + q + 1 by ring,
    kummerM_eq_euler_integral ha (by rwa [show a + q + 1 - a = q + 1 by ring]),
    show a + q + 1 - a = q + 1 by ring, add_sub_cancel_right,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hpow : ((t : ℂ) ^ 2) ^ ((a + q) / 2 + 1 / 2) =
      (t : ℂ) * ((t : ℂ) * (t : ℂ) ^ (a - 1 + q)) := by
    rw [← ofReal_pow, ofReal_sq_cpow ht,
      show 2 * ((a + q) / 2 + 1 / 2) = 1 + (1 + (a - 1 + q)) by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_one]
  rw [hpow]
  have hc : 0 < (a + q + 1).re := by
    simp only [add_re, one_re] at hq ⊢
    linarith
  change _ = Gamma a * Gamma (q + 1) * (cexp (-((t : ℂ) ^ 2) / 2) * _ *
    (Gamma (a + q + 1) / (Gamma a * Gamma (q + 1)) * ∫ u in Ioo (0 : ℝ) 1, K u)) / _
  field_simp [ofReal_ne_zero.mpr ht.ne', Gamma_ne_zero_of_re_pos ha,
    Gamma_ne_zero_of_re_pos hq, Gamma_ne_zero_of_re_pos hc]


/-- §2.5. **Whittaker kernels of `g_1(t)`** (at `σ = -1`). -/
theorem triangularKernel_gOne (ω lam μ : ℂ) (t : ℝ) (ht : 0 < t) :
    (0 < lam.re →
      triangularKernel (-1) ω 1 1 lam μ (gOne t) =
        Gamma lam * whittakerW ((1 - lam - μ) / 2) ((lam - μ) / 2) ((t : ℂ) ^ 2) /
          (2 * π * Complex.I * t)) ∧
    (0 < lam.re → μ.re < 1 →
      triangularKernel (-1) ω (-1) 1 lam μ (gOne t) =
        Gamma lam * Gamma (1 - μ) * whittakerM ((1 - lam - μ) / 2) ((lam - μ) / 2) ((t : ℂ) ^ 2) /
          (2 * π * Complex.I * t * Gamma (lam - μ + 1))) ∧
    triangularKernel (-1) ω 1 (-1) lam μ (gOne t) = 0 := by
  have hpos : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < x + t} = Ioi 0 := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, and_iff_left_iff_imp]
    intro hx
    linarith
  have hfin : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < -x + t} = Ioo 0 t := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁, by linarith⟩
  have hzero : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < -(x + t)} = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hx
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro hl
    simp only [triangularKernel, gOne, ofReal_zero, mul_zero, zero_add, Real.exp_zero,
      Units.val_one, Int.cast_one, one_mul, mul_one, neg_one_mul, hpos,
      ofReal_div, ofReal_pow, ofReal_ofNat, ← neg_div]
    have hInt : (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (lam - 1) * cexp (-(t : ℂ) * x) *
          ((|x + t| : ℝ) : ℂ) ^ (-μ)) =
        ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (lam - 1) * ((x + t : ℝ) : ℂ) ^ (-μ) *
          cexp (-(t : ℂ) * x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [abs_of_pos (add_pos (show 0 < x from hx) ht), mul_right_comm]
    rw [hInt, div_mul_eq_mul_div, integral_scaled_whittakerW lam (-μ) ht hl,
      show (-μ - lam + 1) / 2 = (1 - lam - μ) / 2 by ring, ← sub_eq_add_neg]
    ring
  · intro hl hm
    have hm' : 0 < (-μ + 1).re := by simp only [add_re, neg_re, one_re]; linarith
    simp only [triangularKernel, gOne, ofReal_zero, mul_zero, zero_add, Real.exp_zero,
      Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, one_mul, neg_one_mul, hfin,
      ofReal_div, ofReal_pow, ofReal_ofNat, ← neg_div]
    have hInt : (∫ x in Ioo (0 : ℝ) t, (x : ℂ) ^ (lam - 1) * cexp (-(t : ℂ) * -1 * x) *
          ((|-x + t| : ℝ) : ℂ) ^ (-μ)) =
        ∫ x in Ioo (0 : ℝ) t, (x : ℂ) ^ (lam - 1) * ((t - x : ℝ) : ℂ) ^ (-μ) *
          cexp ((t : ℂ) * x) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      dsimp only
      rw [neg_add_eq_sub, abs_of_pos (sub_pos.mpr hx.2), mul_right_comm]
      congr 3
      ring
    rw [hInt, div_mul_eq_mul_div, integral_scaled_whittakerM lam (-μ) ht hl hm',
      show (-μ - lam + 1) / 2 = (1 - lam - μ) / 2 by ring,
      show -μ + 1 = 1 - μ by ring, ← sub_eq_add_neg]
    ring
  · simp only [triangularKernel, gOne, ofReal_zero, mul_zero, zero_add, Real.exp_zero,
      Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul, mul_one, neg_one_mul,
      hzero, Measure.restrict_empty, integral_zero_measure, mul_zero]

/-- §2.5. **Whittaker kernels of `g_2(t)`** (at `σ = -1`). -/
theorem triangularKernel_gTwo (ω lam μ : ℂ) (t : ℝ) (ht : 0 < t) :
    (μ.re < 1 →
      triangularKernel (-1) ω 1 1 lam μ (gTwo t) =
        Gamma (1 - μ) * whittakerW ((lam + μ - 1) / 2) ((lam - μ) / 2) ((t : ℂ) ^ 2) /
          (2 * π * Complex.I * t)) ∧
    (0 < lam.re → μ.re < 1 →
      triangularKernel (-1) ω 1 (-1) lam μ (gTwo t) =
        Gamma lam * Gamma (1 - μ) * whittakerM ((lam + μ - 1) / 2) ((lam - μ) / 2) ((t : ℂ) ^ 2) /
          (2 * π * Complex.I * t * Gamma (lam - μ + 1))) ∧
    triangularKernel (-1) ω (-1) 1 lam μ (gTwo t) = 0 := by
  have htail : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < x + -t} = Ioi t := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq]
    constructor
    · rintro ⟨_, h⟩
      linarith
    · intro h
      exact ⟨by linarith, by linarith⟩
  have hfin : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < -(x + -t)} = Ioo 0 t := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨h₁, by linarith⟩
  have hzero : Ioi (0 : ℝ) ∩ {x : ℝ | 0 < -x + -t} = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hx
    linarith
  have hd : cexp ((t : ℂ) ^ 2 / 2) * cexp (-((t : ℂ) ^ 2)) =
      cexp (-((t : ℂ) ^ 2) / 2) := by rw [← Complex.exp_add]; congr 1; ring
  refine ⟨?_, ?_, ?_⟩
  · intro hm
    have hm' : 0 < (1 - μ).re := by simp only [sub_re, one_re]; linarith
    simp only [triangularKernel, gTwo, ofReal_zero, mul_zero, zero_add, Real.exp_zero,
      Units.val_one, Int.cast_one, one_mul, mul_one, neg_one_mul, htail,
      ofReal_neg, ofReal_div, ofReal_pow, ofReal_ofNat, neg_neg]
    rw [integral_Ioi_translate t]
    have hInt : (∫ x in Ioi (0 : ℝ), ((x + t : ℝ) : ℂ) ^ (lam - 1) *
          cexp (-(t : ℂ) * (x + t : ℝ)) * ((|(x + t) + -t| : ℝ) : ℂ) ^ (-μ)) =
        cexp (-((t : ℂ) ^ 2)) * (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ ((1 - μ) - 1) *
          ((x + t : ℝ) : ℂ) ^ (lam - 1) * cexp (-(t : ℂ) * x)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [add_neg_cancel_right, abs_of_pos hx, ofReal_add,
        show -(t : ℂ) * (x + t) = -((t : ℂ) ^ 2) + (-(t : ℂ)) * x by ring,
        Complex.exp_add, show 1 - μ - 1 = -μ by ring]
      ring
    rw [hInt, div_mul_eq_mul_div, ← mul_assoc, hd,
      integral_scaled_whittakerW (1 - μ) (lam - 1) ht hm',
      show (lam - 1 - (1 - μ) + 1) / 2 = (lam + μ - 1) / 2 by ring,
      show ((1 - μ) + (lam - 1)) / 2 = (lam - μ) / 2 by ring]
    ring
  · intro hl hm
    have hm' : 0 < (1 - μ).re := by simp only [sub_re, one_re]; linarith
    have hl' : 0 < (lam - 1 + 1).re := by rwa [sub_add_cancel]
    simp only [triangularKernel, gTwo, ofReal_zero, mul_zero, zero_add, Real.exp_zero,
      Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul, mul_one, neg_one_mul, hfin,
      ofReal_neg, ofReal_div, ofReal_pow, ofReal_ofNat, neg_neg]
    let F : ℝ → ℂ := fun x =>
      (x : ℂ) ^ (lam - 1) * cexp (-(t : ℂ) * x) * ((|x + -t| : ℝ) : ℂ) ^ (-μ)
    have hsub := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t) F t
    rw [sub_self, sub_zero, intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo] at hsub
    have hInt : (∫ x in Ioo (0 : ℝ) t, F x) =
        cexp (-((t : ℂ) ^ 2)) * (∫ x in Ioo (0 : ℝ) t, (x : ℂ) ^ ((1 - μ) - 1) *
          ((t - x : ℝ) : ℂ) ^ (lam - 1) * cexp ((t : ℂ) * x)) := by
      rw [← hsub, ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      dsimp only [F]
      rw [show t - x + -t = -x by ring, abs_neg, abs_of_pos hx.1,
        ofReal_sub, show -(t : ℂ) * (t - x) = -((t : ℂ) ^ 2) + (t : ℂ) * x by ring,
        Complex.exp_add, show 1 - μ - 1 = -μ by ring]
      ring
    change cexp ((t : ℂ) ^ 2 / 2) / (2 * π * Complex.I) * (∫ x in Ioo (0 : ℝ) t, F x) = _
    rw [hInt, div_mul_eq_mul_div, ← mul_assoc, hd,
      integral_scaled_whittakerM (1 - μ) (lam - 1) ht hm' hl',
      show (lam - 1 - (1 - μ) + 1) / 2 = (lam + μ - 1) / 2 by ring,
      show ((1 - μ) + (lam - 1)) / 2 = (lam - μ) / 2 by ring,
      sub_add_cancel, show 1 - μ + (lam - 1) + 1 = lam - μ + 1 by ring]
    ring
  · simp only [triangularKernel, gTwo, ofReal_zero, mul_zero, zero_add, Real.exp_zero,
      Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul,
      hzero, Measure.restrict_empty, integral_zero_measure, mul_zero]

/-- §2.5. **Reflection.** -/
theorem triangularKernel_reflect (σ ω : ℂ) (ε η : ℤˣ) (lam μ : ℂ) (g : TriangularGroup) :
    triangularKernel σ ω ε η lam μ ⟨-g.a, g.b, -g.d, g.τ⟩ =
      triangularKernel σ ω (-ε) (-η) lam μ g := by
  simp only [triangularKernel, Units.val_neg, Int.cast_neg, Complex.ofReal_neg]
  congr 1
  have h (x : ℝ) :
      Real.exp g.τ * -((ε : ℤ) : ℝ) * x + g.a =
        -(Real.exp g.τ * ((ε : ℤ) : ℝ) * x + -g.a) := by ring
  simp_rw [h, mul_neg, neg_mul, neg_neg, abs_neg]

end SFVK.AffineHeisenberg
