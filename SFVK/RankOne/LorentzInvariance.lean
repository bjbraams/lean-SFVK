/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.RankOne.Basic.Hyperbolic

import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Lorentz invariance on real hyperbolic space

The volume is the normalized projection of ambient Lebesgue measure restricted to a Lorentz
shell. This gives invariance using Mathlib's additive Haar measure scaling and its change of
variables for the time coordinate. The Laplacian is the contraction of the Hessian of the
homogeneous extension with the Lorentz form.

## Main results

* `SFVK.RankOne.map_hyperbolicMeasure`.
* `SFVK.RankOne.hyperbolicLaplacian_comp`.
-/

public noncomputable section

open Complex Filter Function MeasureTheory Set Topology
open scoped Real ENNReal Matrix ContDiff

namespace SFVK.RankOne

namespace HyperbolicVolume

/-- The Lorentz radius in the forward timelike cone. -/
private def radius {n : ℕ} (x : Fin (n + 1) → ℝ) : ℝ :=
  Real.sqrt (lorentz x x)

/-- The portion of the forward cone with radius between one and two. -/
private def shell (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | 0 < x 0 ∧ radius x ∈ Ioo 1 2}

/-- The degree-zero Lorentz normalization to the unit hyperboloid. -/
private def normalize {n : ℕ} (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  (radius x)⁻¹ • x

/-- The radial volume factor of the chosen shell. -/
private def shellFactor (n : ℕ) : ℝ≥0∞ := ∫⁻ r in Ioo (1 : ℝ) 2, ENNReal.ofReal (r ^ n)

/-- The totalized Lorentz radius is measurable. -/
private theorem measurable_radius (n : ℕ) : Measurable (radius (n := n)) := by
  unfold radius
  simp only [lorentz_def]
  fun_prop

/-- Lorentz normalization is measurable. -/
private theorem measurable_normalize (n : ℕ) : Measurable (normalize (n := n)) := by
  exact (measurable_radius n).inv.smul measurable_id

/-- The Lorentz shell is measurable. -/
private theorem measurableSet_shell (n : ℕ) : MeasurableSet (shell n) := by
  change MeasurableSet ((fun x : Fin (n + 1) → ℝ => x 0) ⁻¹' Ioi 0 ∩ radius ⁻¹' Ioo 1 2)
  exact ((measurable_pi_apply (0 : Fin (n + 1))) measurableSet_Ioi).inter
    ((measurable_radius n) measurableSet_Ioo)

/-- Scaling a vector scales its Lorentz square by the square of the scalar. -/
private theorem lorentz_smul_self {n : ℕ} (c : ℝ) (x : Fin (n + 1) → ℝ) :
    lorentz (c • x) (c • x) = c ^ 2 * lorentz x x := by
  simp only [lorentz_def, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.mul_sum]
  have h (r : ℝ) : (c * r) * (c * r) = c ^ 2 * (r * r) := by ring
  simp only [h]

/-- Normalization takes the forward cone to the upper hyperboloid. -/
private theorem normalize_mem_hyperboloid {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx₀ : 0 < x 0) (hq : 0 < radius x) : normalize x ∈ hyperboloid n := by
  have hsq : radius x ^ 2 = lorentz x x := Real.sq_sqrt (Real.sqrt_pos.mp hq).le
  refine ⟨?_, ?_⟩
  · rw [normalize, lorentz_smul_self]
    calc
      (radius x)⁻¹ ^ 2 * lorentz x x = ((radius x)⁻¹ * radius x) ^ 2 := by
        rw [mul_pow, hsq]
      _ = 1 := by rw [inv_mul_cancel₀ hq.ne', one_pow]
  · simp only [normalize, Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr hq) hx₀

/-- Lorentz transformations preserve the radius. -/
private theorem radius_mulVec {n : ℕ} (g : lorentzGroup n) (x : Fin (n + 1) → ℝ) :
    radius (g.1.1 *ᵥ x) = radius x := by rw [radius, lorentz_mulVec, ← radius]

/-- Normalization commutes with every Lorentz transformation. -/
private theorem normalize_mulVec {n : ℕ} (g : lorentzGroup n) (x : Fin (n + 1) → ℝ) :
    normalize (g.1.1 *ᵥ x) = g.1.1 *ᵥ normalize x := by
  simp only [normalize, radius_mulVec, Matrix.mulVec_smul]

/-- The shell is stable under Lorentz transformations. -/
private theorem mulVec_mem_shell {n : ℕ} (g : lorentzGroup n) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ shell n) : g.1.1 *ᵥ x ∈ shell n := by
  have hr : 0 < radius x := zero_lt_one.trans hx.2.1
  have h := mulVec_mem_hyperboloid g (normalize_mem_hyperboloid hx.1 hr)
  rw [← normalize_mulVec] at h
  have htime := h.2
  simp only [normalize, Pi.smul_apply, smul_eq_mul, radius_mulVec] at htime
  refine ⟨?_, by rw [radius_mulVec]; exact hx.2⟩
  exact pos_of_mul_pos_right htime (inv_nonneg.mpr hr.le)

/-- The shell is invariant under every Lorentz transformation. -/
private theorem preimage_shell_mulVec {n : ℕ} (g : lorentzGroup n) :
    (fun x => g.1.1 *ᵥ x) ⁻¹' shell n = shell n := by
  ext x
  constructor
  · intro hx
    have h := mulVec_mem_shell g⁻¹ hx
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul,
      inv_mul_cancel, Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h
    exact h
  · exact mulVec_mem_shell g

/-- Lorentz transformations preserve ambient Lebesgue measure. -/
private theorem measurePreserving_mulVec {n : ℕ} (g : lorentzGroup n) :
    MeasurePreserving (fun x => g.1.1 *ᵥ x) volume volume := by
  let A := Matrix.toLin' g.1.1
  have hdet : LinearMap.det A = 1 := by dsimp only [A]; rw [LinearMap.det_toLin', g.1.2]
  have h : LinearMap.det A ≠ 0 := hdet ▸ one_ne_zero
  refine ⟨A.continuous_of_finiteDimensional.measurable, ?_⟩
  change (volume : Measure (Fin (n + 1) → ℝ)).map A = volume
  simpa only [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul] using
    Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (Fin (n + 1) → ℝ)) (f := A) h

/-- The radial factor is positive. -/
private theorem shellFactor_ne_zero (n : ℕ) : shellFactor n ≠ 0 := by
  have hmeas : MeasurableSet (Ioo (1 : ℝ) 2) := measurableSet_Ioo
  have h : ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioo 1 2), 1 ≤ ENNReal.ofReal (r ^ n) := by
    filter_upwards [ae_restrict_mem hmeas] with r hr
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hr.1.le)
  have hp := lintegral_mono_ae h
  rw [lintegral_const, one_mul, Measure.restrict_apply_univ, Real.volume_Ioo] at hp
  rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.ofReal_one] at hp
  exact ne_of_gt (zero_lt_one.trans_le hp)

/-- The radial factor is finite. -/
private theorem shellFactor_ne_top (n : ℕ) : shellFactor n ≠ ⊤ := by
  have hmeas : MeasurableSet (Ioo (1 : ℝ) 2) := measurableSet_Ioo
  have h : ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioo 1 2),
      ENNReal.ofReal (r ^ n) ≤ ENNReal.ofReal ((2 : ℝ) ^ n) := by
    filter_upwards [ae_restrict_mem hmeas] with r hr
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (zero_le_one.trans hr.1.le) hr.2.le _)
  have hp := lintegral_mono_ae h
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo] at hp
  exact ne_of_lt (hp.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))

/-- The squared Euclidean norm of the spatial coordinates. -/
private def spatialSquare {n : ℕ} (y : Fin n → ℝ) : ℝ := ∑ i, y i ^ 2

/-- The time coordinate at fixed spatial square and Lorentz radius. -/
private def shellTime (q r : ℝ) : ℝ := Real.sqrt (r ^ 2 + q)

/-- The Jacobian for the substitution of radius for time. -/
private theorem hasDerivAt_shellTime (q : ℝ) (hq : 0 ≤ q) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (shellTime q) (r / Real.sqrt (r ^ 2 + q)) r := by
  have hpos : 0 < r ^ 2 + q := by positivity
  have h := (Real.hasDerivAt_sqrt hpos.ne').comp r (((hasDerivAt_id r).pow 2).add_const q)
  refine h.congr_deriv ?_
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  field_simp [(Real.sqrt_pos.mpr hpos).ne']

/-- The time coordinate increases with the radius on the shell. -/
private theorem monotoneOn_shellTime (q : ℝ) :
    MonotoneOn (shellTime q) (Ioo 1 2) := by
  intro r hr t ht hrt
  exact Real.sqrt_le_sqrt (add_le_add_left (pow_le_pow_left₀ (zero_le_one.trans hr.1.le) hrt _) _)

/-- The radius parametrizes each time slice of the shell. -/
private theorem image_shellTime (n : ℕ) (y : Fin n → ℝ) :
    shellTime (spatialSquare y) '' Ioo (1 : ℝ) 2 =
      {t : ℝ | Fin.cons t y ∈ shell n} := by
  let q := spatialSquare y
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg (y i))
  have hLorentz (t : ℝ) : lorentz (Fin.cons t y) (Fin.cons t y) = t ^ 2 - q := by
    simp only [lorentz_def, Fin.cons_zero, Fin.cons_succ, pow_two, q, spatialSquare]
  ext t
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hr' : 0 < r := zero_lt_one.trans hr.1
    have ht : 0 < shellTime q r := Real.sqrt_pos.mpr (by positivity)
    have heq : radius (Fin.cons (shellTime q r) y) = r := by
      rw [radius, hLorentz, shellTime, Real.sq_sqrt (by positivity), add_sub_cancel_right,
        Real.sqrt_sq hr'.le]
    refine ⟨ht, ?_⟩
    change radius (Fin.cons (shellTime q r) y) ∈ Ioo (1 : ℝ) 2
    rwa [heq]
  · intro h
    change Fin.cons t y ∈ shell n at h
    have ht : 0 < t := h.1
    let r := radius (Fin.cons t y)
    have hr : 0 < r := zero_lt_one.trans h.2.1
    have hsq : r ^ 2 = t ^ 2 - q := by
      dsimp only [r, radius] at hr ⊢
      rw [Real.sq_sqrt (Real.sqrt_pos.mp hr).le, hLorentz]
    refine ⟨r, h.2, ?_⟩
    rw [shellTime, hsq, sub_add_cancel, Real.sqrt_sq ht.le]

/-- The transverse Lebesgue integral under positive rescaling. -/
private theorem lintegral_comp_positive_smul (n : ℕ) {r : ℝ} (hr : 0 < r)
    (g : (Fin n → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y) = ENNReal.ofReal (r ^ n) * ∫⁻ y : Fin n → ℝ, g (r • y) := by
  let T : (Fin n → ℝ) → (Fin n → ℝ) := (r⁻¹ • ·)
  let H : (Fin n → ℝ) → ℝ≥0∞ := fun y => g (r • y)
  have hT : Measurable T := measurable_const_smul _
  have hH : Measurable H := hg.comp (measurable_const_smul _)
  have hComp (y : Fin n → ℝ) : H (T y) = g y := by
    simp only [T, H, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hMap : (volume : Measure (Fin n → ℝ)).map T = ENNReal.ofReal (r ^ n) • volume := by
    rw [Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'), Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin, inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hr.le _)]
  calc
    _ = ∫⁻ y, H (T y) := (lintegral_congr hComp).symm
    _ = ∫⁻ y, H y ∂(volume : Measure _).map T := (lintegral_map hH hT).symm
    _ = _ := by rw [hMap, lintegral_smul_measure, smul_eq_mul]

/-- The time coordinate scales with radius and transverse vector. -/
private theorem shellTime_smul (n : ℕ) {r : ℝ} (hr : 0 < r) (y : Fin n → ℝ) :
    shellTime (spatialSquare (r • y)) r = r * Real.sqrt (1 + spatialSquare y) := by
  have hsum : spatialSquare (r • y) = r ^ 2 * spatialSquare y := by
    simp only [spatialSquare, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [shellTime, hsum, show r ^ 2 + r ^ 2 * spatialSquare y =
    r ^ 2 * (1 + spatialSquare y) by ring, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]

/-- The normalization of a radially rescaled spatial chart point. -/
private theorem normalize_cons_shellTime (n : ℕ) {r : ℝ} (hr : 0 < r) (y : Fin n → ℝ) :
    normalize (n := n) (Fin.cons (shellTime (spatialSquare (r • y)) r) (r • y)) =
      hyperboloidChart n y := by
  have hq' : 0 ≤ spatialSquare (r • y) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  let u : Fin (n + 1) → ℝ := Fin.cons (shellTime (spatialSquare (r • y)) r) (r • y)
  have hrad : radius u = r := by
    have hp : 0 ≤ r ^ 2 + spatialSquare (r • y) := by positivity
    dsimp only [u, radius]
    simp only [lorentz_def, Fin.cons_zero, Fin.cons_succ, ← pow_two]
    change √((shellTime (spatialSquare (r • y)) r) ^ 2 - spatialSquare (r • y)) = r
    rw [shellTime, Real.sq_sqrt hp, add_sub_cancel_right, Real.sqrt_sq hr.le]
  change normalize u = _
  rw [normalize, hrad]
  dsimp only [u]
  rw [shellTime_smul n hr y, hyperboloidChart_def]
  ext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero, ← mul_assoc,
      inv_mul_cancel₀ hr.ne', one_mul, spatialSquare]
  · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ, ← mul_assoc,
      inv_mul_cancel₀ hr.ne', one_mul]

set_option maxHeartbeats 2500000 in
/-- Integrating a normalized function on the shell gives the hyperbolic volume integral. -/
private theorem lintegral_normalize_shell (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x in shell n, f (normalize x) =
      shellFactor n * ∫⁻ x, f x ∂hyperbolicMeasure n := by
  let G (x : Fin (n + 1) → ℝ) := (shell n).indicator (fun z => f (normalize z)) x
  have hG : Measurable G := (hf.comp (measurable_normalize n)).indicator (measurableSet_shell n)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have hE (p : ℝ × (Fin n → ℝ)) : e p = Fin.cons p.1 p.2 := by
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  let K (y : Fin n → ℝ) (r : ℝ) :=
    ENNReal.ofReal (r / shellTime (spatialSquare y) r) *
      f (normalize (n := n) (Fin.cons (shellTime (spatialSquare y) r) y))
  have hK : Measurable (uncurry K) := by
    let t (p : (Fin n → ℝ) × ℝ) := shellTime (spatialSquare p.1) p.2
    have ht : Measurable t := by dsimp only [t, shellTime, spatialSquare]; fun_prop
    have hcons : Measurable
        (fun p : (Fin n → ℝ) × ℝ => (Fin.cons (t p) p.1 : Fin (n + 1) → ℝ)) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero] using ht
      · simp only [Fin.cons_succ]
        fun_prop
    exact (measurable_snd.div ht).ennreal_ofReal.mul
      (hf.comp ((measurable_normalize n).comp hcons))
  -- Integrate along the time coordinate before rescaling the spatial coordinates.
  have hSlice (y : Fin n → ℝ) : ∫⁻ t : ℝ, G (Fin.cons t y) = ∫⁻ r in Ioo 1 2, K y r := by
    let q := spatialSquare y
    have hq : 0 ≤ q := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    let M := {t : ℝ | Fin.cons t y ∈ shell n}
    have hY : Measurable (fun t : ℝ => (Fin.cons t y : Fin (n + 1) → ℝ)) := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]; fun_prop
      · simp only [Fin.cons_succ]; fun_prop
    have hMs : MeasurableSet M := hY (measurableSet_shell n)
    have hEq (t : ℝ) : G (Fin.cons t y) =
        M.indicator (fun t => f (normalize (n := n) (Fin.cons t y))) t := by
      by_cases h : t ∈ M
      · have hh : (Fin.cons t y : Fin (n + 1) → ℝ) ∈ shell n := h
        simp only [G, indicator_of_mem h, indicator_of_mem hh]
      · have hh : (Fin.cons t y : Fin (n + 1) → ℝ) ∉ shell n := h
        simp only [G, indicator_of_notMem h, indicator_of_notMem hh]
    have hM : shellTime q '' Ioo (1 : ℝ) 2 = M := image_shellTime n y
    simp_rw [hEq]
    rw [lintegral_indicator hMs, ← hM]
    exact lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioo
      (fun r h => (hasDerivAt_shellTime q hq (zero_lt_one.trans h.1)).hasDerivWithinAt)
      (monotoneOn_shellTime q) (fun t => f (normalize (n := n) (Fin.cons t y)))
  have hC : Measurable (fun y : Fin n → ℝ => f (hyperboloidChart n y)) :=
    hf.comp (continuous_hyperboloidChart n).measurable
  let w (y : Fin n → ℝ) := ENNReal.ofReal (Real.sqrt (1 + spatialSquare y))⁻¹
  have hw : Measurable w := by dsimp only [w, spatialSquare]; fun_prop
  have hChart : ∫⁻ y, w y * f (hyperboloidChart n y) = ∫⁻ x, f x ∂hyperbolicMeasure n := by
    symm
    have hw' : Measurable (fun y : Fin n → ℝ =>
        ENNReal.ofReal (Real.sqrt (1 + ∑ i, y i ^ 2))⁻¹) := hw
    rw [hyperbolicMeasure_def, lintegral_map hf (continuous_hyperboloidChart n).measurable,
      lintegral_withDensity_eq_lintegral_mul _ hw' hC]
    rfl
  have hRescale (r : ℝ) (hr : r ∈ Ioo (1 : ℝ) 2) :
      ∫⁻ y, K y r = ENNReal.ofReal (r ^ n) * ∫⁻ x, f x ∂hyperbolicMeasure n := by
    have hr' := zero_lt_one.trans hr.1
    have hPair : Measurable (fun y : Fin n → ℝ => (y, r)) := measurable_id.prodMk measurable_const
    have hmeas : Measurable (fun y => K y r) := by
      simpa only [Function.comp_def, uncurry_apply_pair] using hK.comp hPair
    refine (lintegral_comp_positive_smul n hr' (fun y => K y r) hmeas).trans ?_
    rw [← hChart]
    congr 1
    refine lintegral_congr fun y => ?_
    have htime := shellTime_smul n hr' y
    dsimp only [K, w]
    rw [normalize_cons_shellTime n hr', htime, div_mul_eq_div_div, div_self hr'.ne', one_div]
  calc
    _ = ∫⁻ x, G x := (lintegral_indicator (measurableSet_shell n) _).symm
    _ = ∫⁻ p : ℝ × (Fin n → ℝ), G (e p) := by
      symm
      have hpres := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
      exact hpres.lintegral_comp hG
    _ = ∫⁻ y : Fin n → ℝ, ∫⁻ t : ℝ, G (Fin.cons t y) := by
      change (∫⁻ p, (G ∘ e) p ∂(volume : Measure ℝ).prod volume) = _
      rw [lintegral_prod_symm' _ (hG.comp e.measurable)]
      exact lintegral_congr fun y => lintegral_congr fun t => congrArg G (hE (t, y))
    _ = ∫⁻ y : Fin n → ℝ, ∫⁻ r in Ioo 1 2, K y r := lintegral_congr hSlice
    _ = ∫⁻ r in Ioo (1 : ℝ) 2, ∫⁻ y : Fin n → ℝ, K y r :=
      lintegral_lintegral_swap hK.aemeasurable
    _ = ∫⁻ r in Ioo (1 : ℝ) 2, ENNReal.ofReal (r ^ n) *
        ∫⁻ x, f x ∂hyperbolicMeasure n :=
      lintegral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioo hRescale)
    _ = _ := by
      rw [lintegral_mul_const _ (by fun_prop)]
      rfl

/-- The normalized shell measure is proportional to hyperbolic volume. -/
private theorem map_normalize_shell (n : ℕ) :
    (volume.restrict (shell n)).map normalize = shellFactor n • hyperbolicMeasure n := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_normalize n), lintegral_smul_measure, smul_eq_mul]
  exact lintegral_normalize_shell n f hf

end HyperbolicVolume

set_option maxHeartbeats 1200000 in
/-- **Invariance of the volume** under `SO₀(n, 1)`. -/
theorem map_hyperbolicMeasure (n : ℕ) (g : lorentzGroup n) :
    (hyperbolicMeasure n).map
        (fun x => (g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ x) =
      hyperbolicMeasure n := by
  open HyperbolicVolume in
  let A (x : Fin (n + 1) → ℝ) := g.1.1 *ᵥ x
  have hp : MeasurePreserving A volume volume := measurePreserving_mulVec g
  have heq := Measure.restrict_map hp.measurable (measurableSet_shell n)
    (μ := (volume : Measure (Fin (n + 1) → ℝ)))
  rw [hp.map_eq, preimage_shell_mulVec g] at heq
  -- The normalized shell measure is a nonzero finite multiple of the hyperbolic measure.
  have hvol := map_normalize_shell n
  have hconj : A ∘ normalize = normalize ∘ A := funext fun x => (normalize_mulVec g x).symm
  have hScale :
      shellFactor n • (hyperbolicMeasure n).map A = shellFactor n • hyperbolicMeasure n := by
    rw [← Measure.map_smul _ hp.measurable.aemeasurable, ← hvol,
      Measure.map_map hp.measurable (measurable_normalize n),
      hconj, ← Measure.map_map (measurable_normalize n) hp.measurable, ← heq]
  ext s hs
  have h := congrArg (fun μ : Measure (Fin (n + 1) → ℝ) => μ s) hScale
  simp only [smul_apply, smul_eq_mul] at h
  have h' := congrArg (fun z => (shellFactor n)⁻¹ * z) h
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel (shellFactor_ne_zero n) (shellFactor_ne_top n),
    one_mul] using h'

namespace LorentzTrace

/-- The diagonal entries of the negative Lorentz form. -/
private def signature (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  if i = 0 then -1 else 1

/-- The time coordinate has negative sign in the wave operator. -/
private theorem signature_zero (n : ℕ) : signature n 0 = -1 := by simp [signature]

/-- Every spatial coordinate has positive sign in the wave operator. -/
private theorem signature_succ (n : ℕ) (i : Fin n) : signature n i.succ = 1 := by
  simp [signature, Fin.succ_ne_zero]

/-- The diagonal signature represents the negative Lorentz pairing. -/
private theorem dotProduct_diagonal_signature (n : ℕ) (x y : Fin (n + 1) → ℝ) :
    x ⬝ᵥ (Matrix.diagonal (signature n) *ᵥ y) = -lorentz x y := by
  simp only [dotProduct, Fin.sum_univ_succ, Matrix.mulVec_diagonal, lorentz_def,
    signature_zero, signature_succ, neg_one_mul, one_mul, mul_neg]
  ring

/-- The rows of a Lorentz matrix preserve the diagonal signature pairing. -/
private theorem weighted_row_pairing (n : ℕ) (g : lorentzGroup n) (j k : Fin (n + 1)) :
    ∑ i : Fin (n + 1), signature n i * (g.1.1 j i * g.1.1 k i) =
      if j = k then signature n j else 0 := by
  let A := g.1.1
  let B := (g⁻¹).1.1
  let J := Matrix.diagonal (signature n)
  have hJJ : J * J = 1 := by
    rw [← Matrix.diagonal_one]
    dsimp only [J]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [signature]
    split <;> norm_num
  have hAB : A * B = 1 := by
    dsimp only [A, B]
    simp only [← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one]
  have hAtJ : Aᵀ * J * A = J := by
    have h (x y : Fin (n + 1) → ℝ) : x ⬝ᵥ ((Aᵀ * J * A) *ᵥ y) = x ⬝ᵥ (J *ᵥ y) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
        dotProduct_comm (J *ᵥ (A *ᵥ y)), dotProduct_diagonal_signature,
        dotProduct_diagonal_signature]
      exact congrArg Neg.neg (lorentz_mulVec g x y)
    ext a b
    simpa only [Matrix.mulVec_single_one, single_one_dotProduct, Matrix.col_apply] using
      h (Pi.single a 1) (Pi.single b 1)
  have hAtJB : Aᵀ * J = J * B := by
    calc
      _ = (Aᵀ * J) * (A * B) := by rw [hAB, mul_one]
      _ = _ := by rw [← mul_assoc, hAtJ]
  have hAt : Aᵀ = J * B * J := by
    calc
      _ = (Aᵀ * J) * J := by rw [mul_assoc, hJJ, mul_one]
      _ = _ := by rw [hAtJB]
  have hAJAt : A * J * Aᵀ = J := by
    rw [hAt]
    calc
      (A * J) * ((J * B) * J) = ((A * (J * J)) * B) * J := by noncomm_ring
      _ = _ := by rw [hJJ, mul_one, hAB, one_mul]
  have h := congrFun (congrFun hAJAt j) k
  dsimp only [J] at h
  rw [Matrix.mul_apply, Matrix.diagonal_apply] at h
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply] at h
  refine Eq.trans ?_ h
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [A]
  ring

/-- Expansion in the standard coordinate basis. -/
private theorem sum_single_smul (n : ℕ) (x : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), x i • Pi.single i 1) = x := by
  classical
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [Pi.single_eq_of_ne hij.symm]
  · simp

/-- Expansion of a bilinear map in the standard coordinate basis. -/
private theorem bilinear_expand (n : ℕ)
    (D : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℂ)
    (x y : Fin (n + 1) → ℝ) :
    D x y = ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
      (x j * y k) • D (Pi.single j 1) (Pi.single k 1) := by
  calc
    _ = ∑ j : Fin (n + 1), x j • D (Pi.single j 1) y := by
      conv_lhs => rw [← sum_single_smul n x]
      simp only [map_sum, sum_apply, map_smul, smul_apply]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      conv_lhs => rw [← sum_single_smul n y]
      simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]

/-- Contraction of a bilinear form with the Lorentz signs is invariant. -/
private theorem sum_signature_bilinear_lorentz (n : ℕ) (g : lorentzGroup n)
    (D : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℂ) :
    ∑ i : Fin (n + 1), signature n i • D (g.1.1 *ᵥ Pi.single i 1) (g.1.1 *ᵥ Pi.single i 1) =
      ∑ i : Fin (n + 1), signature n i • D (Pi.single i 1) (Pi.single i 1) := by
  have hExpand (i : Fin (n + 1)) :
      D (g.1.1 *ᵥ Pi.single i 1) (g.1.1 *ᵥ Pi.single i 1) =
        ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
          (g.1.1 j i * g.1.1 k i) • D (Pi.single j 1) (Pi.single k 1) := by
    rw [bilinear_expand n D (g.1.1 *ᵥ Pi.single i 1) (g.1.1 *ᵥ Pi.single i 1)]
    simp only [Matrix.mulVec_single_one, Matrix.col_apply]
  conv_lhs =>
    simp only [hExpand, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  have h (k : Fin (n + 1)) :
      ∑ i : Fin (n + 1), (signature n i * (g.1.1 j i * g.1.1 k i)) •
        D (Pi.single j 1) (Pi.single k 1) =
        (if j = k then signature n j else 0) • D (Pi.single j 1) (Pi.single k 1) := by
    rw [← Finset.sum_smul, weighted_row_pairing]
  simp only [h]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [hkj.symm]
  · simp

/-- The second derivative along an affine line is the Hessian on its direction. -/
private theorem iteratedDeriv_affineLine (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℂ)
    {x : Fin (n + 1) → ℝ} (hF : ContDiffAt ℝ 2 F x) (v : Fin (n + 1) → ℝ) :
    iteratedDeriv 2 (fun s : ℝ => F (x + s • v)) 0 =
      iteratedFDeriv ℝ 2 F x (fun _ => v) := by
  let l (s : ℝ) := x + s • v
  have hl0 : l 0 = x := by simp [l]
  have hlc : ContDiff ℝ 2 l := by
    change ContDiff ℝ 2 (fun s : ℝ => x + s • v)
    fun_prop
  have hd (s : ℝ) : HasDerivAt l v s := by
    simpa only [l, id_eq, one_smul] using (((hasDerivAt_id s).smul_const v).const_add x)
  have heq : deriv l = fun _ => v := funext fun s => (hd s).deriv
  have hsec : iteratedDeriv 2 l 0 = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, heq, deriv_const]
  have hF' : ContDiffAt ℝ 2 F (l 0) := by rwa [hl0]
  change iteratedDeriv 2 (F ∘ l) 0 = _
  rw [iteratedDeriv_vcomp_two hF' hlc.contDiffAt, hl0, (hd 0).deriv, hsec, map_zero, add_zero]

end LorentzTrace

set_option maxHeartbeats 2000000 in
/-- **Invariance of the Laplacian**: `Δ(f ∘ g) = (Δf) ∘ g` on `ℍⁿ`. -/
theorem hyperbolicLaplacian_comp (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℂ) (hf : ContDiff ℝ 2 f)
    (g : lorentzGroup n) {x : Fin (n + 1) → ℝ} (hx : x ∈ hyperboloid n) :
    hyperbolicLaplacian n
        (fun y => f ((g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ y)) x =
      hyperbolicLaplacian n f ((g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ x) := by
  let Y := Fin (n + 1) → ℝ
  let A := g.1.1
  let P (x : Y) := (Real.sqrt (lorentz x x))⁻¹ • x
  let F := f ∘ P
  have hA (y : Y) : A *ᵥ P y = P (A *ᵥ y) := by
    have hL : lorentz (A *ᵥ y) (A *ᵥ y) = lorentz y y := lorentz_mulVec g y y
    dsimp only [P]
    rw [hL]
    exact Matrix.mulVec_smul A _ y
  have hp : ContDiffAt ℝ 2 P (A *ᵥ x) := by
    have hq : ContDiff ℝ 2 (fun y : Y => lorentz y y) := by
      simp only [lorentz_def]
      fun_prop
    have hq0 : lorentz (A *ᵥ x) (A *ᵥ x) = 1 := (lorentz_mulVec g x x).trans hx.1
    have hs := hq.contDiffAt.sqrt (by rw [hq0]; norm_num)
    have hsi := hs.inv (by rw [hq0, Real.sqrt_one]; norm_num)
    exact hsi.smul contDiffAt_id
  have hF : ContDiffAt ℝ 2 F (A *ᵥ x) := hf.contDiffAt.comp _ hp
  -- Contract the ambient Hessian of the homogeneous extension with the Lorentz form.
  let B := iteratedFDeriv ℝ 2 F (A *ᵥ x)
  let D : Y →L[ℝ] Y →L[ℝ] ℂ :=
    (continuousMultilinearCurryFin1 ℝ Y ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp
      B.curryLeft
  have hD (v : Y) : D v v = B (fun _ => v) := by
    change continuousMultilinearCurryFin1 ℝ Y ℂ (B.curryLeft v) v = _
    rw [continuousMultilinearCurryFin1_apply, ContinuousMultilinearMap.curryLeft_apply]
    apply congrArg B
    funext j
    fin_cases j <;> rfl
  have hfirst (i : Fin (n + 1)) :
      iteratedDeriv 2 (fun s : ℝ => f (A *ᵥ P (x + s • Pi.single i 1))) 0 =
        D (A *ᵥ Pi.single i 1) (A *ᵥ Pi.single i 1) := by
    have hgl (s : ℝ) : A *ᵥ (x + s • Pi.single i 1) =
        A *ᵥ x + s • (A *ᵥ Pi.single i 1) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul A s]
    simp_rw [hA, hgl]
    rw [hD]
    exact LorentzTrace.iteratedDeriv_affineLine n F (x := A *ᵥ x) hF (A *ᵥ Pi.single i 1)
  have hsecond (i : Fin (n + 1)) :
      iteratedDeriv 2 (fun s : ℝ => F (A *ᵥ x + s • Pi.single i 1)) 0 =
        D (Pi.single i 1) (Pi.single i 1) := by
    rw [hD]
    exact LorentzTrace.iteratedDeriv_affineLine n F hF _
  rw [hyperbolicLaplacian_def, hyperbolicLaplacian_def]
  change (∑ i : Fin n, iteratedDeriv 2 (fun s : ℝ =>
      f (A *ᵥ P (x + s • Pi.single i.succ 1))) 0) -
      iteratedDeriv 2 (fun s : ℝ => f (A *ᵥ P (x + s • Pi.single 0 1))) 0 =
    (∑ i : Fin n, iteratedDeriv 2 (fun s : ℝ => F (A *ᵥ x + s • Pi.single i.succ 1)) 0) -
      iteratedDeriv 2 (fun s : ℝ => F (A *ᵥ x + s • Pi.single 0 1)) 0
  simp only [hfirst, hsecond]
  have hsum := LorentzTrace.sum_signature_bilinear_lorentz n g D
  simpa only [Fin.sum_univ_succ, LorentzTrace.signature_zero, LorentzTrace.signature_succ,
    neg_one_smul, one_smul, neg_add_eq_sub, A] using hsum

end SFVK.RankOne
