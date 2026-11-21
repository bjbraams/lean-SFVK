/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.RankOne.Basic.Hyperbolic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Horospherical integration on real hyperbolic space

The volume element in the coordinates used for the Abel transform of Heckman–Schlichtkrull,
*Harmonic Analysis and Special Functions on Symmetric Spaces*, Part I §5.4, (5.4.3), p. 83.
The proof uses Mathlib's monotone change of variables on each axial slice and its
additive Haar measure scaling on the transverse space.

## Main result

* `SFVK.RankOne.lintegral_hyperbolicMeasure_horospherical`.
-/

public noncomputable section

open Function Filter Topology MeasureTheory Set
open scoped Real ENNReal Matrix

namespace SFVK.RankOne

namespace HorosphericalCoordinates

/-- The last spatial coordinate on a horosphere with fixed transverse Euclidean coordinates. -/
private def axialCoordinate (q s : ℝ) : ℝ :=
  -Real.sinh s - q * Real.exp s / 2

/-- The time coordinate on a horosphere with fixed transverse Euclidean coordinates. -/
private def timeCoordinate (q s : ℝ) : ℝ :=
  Real.cosh s + q * Real.exp s / 2

/-- The axial coordinate expressed in terms of exponentials. -/
private theorem axialCoordinate_exp (q s : ℝ) :
    axialCoordinate q s = (Real.exp (-s) - (1 + q) * Real.exp s) / 2 := by
  rw [axialCoordinate, Real.sinh_eq]
  ring

/-- The time coordinate lies on the upper sheet. -/
private theorem timeCoordinate_pos {q : ℝ} (hq : 0 ≤ q) (s : ℝ) :
    0 < timeCoordinate q s :=
  add_pos_of_pos_of_nonneg (Real.cosh_pos s) (by positivity)

/-- The time coordinate satisfies the hyperboloid equation. -/
private theorem sqrt_axialCoordinate (q : ℝ) (hq : 0 ≤ q) (s : ℝ) :
    Real.sqrt (1 + q + axialCoordinate q s ^ 2) = timeCoordinate q s := by
  have hplus : timeCoordinate q s + axialCoordinate q s = Real.exp (-s) := by
    rw [timeCoordinate, axialCoordinate, Real.cosh_eq, Real.sinh_eq]
    ring
  have hminus : timeCoordinate q s - axialCoordinate q s = (1 + q) * Real.exp s := by
    rw [timeCoordinate, axialCoordinate, Real.cosh_eq, Real.sinh_eq]
    ring
  have hprod : (timeCoordinate q s + axialCoordinate q s) *
      (timeCoordinate q s - axialCoordinate q s) = 1 + q := by
    rw [hplus, hminus, mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have heq : 1 + q + axialCoordinate q s ^ 2 = timeCoordinate q s ^ 2 := by
    linear_combination -hprod
  rw [heq, Real.sqrt_sq (timeCoordinate_pos hq s).le]

/-- The axial coordinate covers the real line on each fixed transverse slice. -/
private theorem surjective_axialCoordinate (q : ℝ) (hq : 0 ≤ q) :
    Surjective (axialCoordinate q) := by
  intro z
  let P := Real.sqrt (1 + q + z ^ 2)
  have hp : P ^ 2 = 1 + q + z ^ 2 := Real.sq_sqrt (by positivity)
  have hpos : 0 < P + z := by
    have hn : 0 ≤ P := Real.sqrt_nonneg _
    by_contra! h
    have hle : P ≤ -z := by linarith
    have hsq : P ^ 2 ≤ (-z) ^ 2 := sq_le_sq₀ hn (hn.trans hle) |>.mpr hle
    nlinarith
  let s := -Real.log (P + z)
  refine ⟨s, ?_⟩
  have hneg : Real.exp s = (P + z)⁻¹ := by dsimp only [s]; rw [Real.exp_neg, Real.exp_log hpos]
  have hreal : Real.exp (-s) = P + z := by dsimp only [s]; rw [neg_neg, Real.exp_log hpos]
  have hdiv : (1 + q) * (P + z)⁻¹ = P - z := by
    rw [← div_eq_mul_inv]
    apply (div_eq_iff hpos.ne').mpr
    nlinarith
  rw [axialCoordinate_exp, hneg, hreal, hdiv]
  ring

/-- The axial derivative is the negative of the time coordinate. -/
private theorem hasDerivAt_axialCoordinate (q s : ℝ) :
    HasDerivAt (axialCoordinate q) (-timeCoordinate q s) s := by
  have h := (Real.hasDerivAt_sinh s).neg.sub
    (((Real.hasDerivAt_exp s).const_mul q).div_const 2)
  have heq : axialCoordinate q = -Real.sinh - fun t => q * Real.exp t / 2 := by
    funext t
    simp only [axialCoordinate, Pi.sub_apply, Pi.neg_apply]
  rw [heq]
  refine h.congr_deriv ?_
  dsimp only [timeCoordinate]
  ring

/-- The axial coordinate decreases along the slice. -/
private theorem antitone_axialCoordinate (q : ℝ) (hq : 0 ≤ q) :
    AntitoneOn (axialCoordinate q) univ := by
  apply antitoneOn_of_deriv_nonpos convex_univ
  · exact (continuous_iff_continuousAt.2 (fun s =>
      (hasDerivAt_axialCoordinate q s).continuousAt)).continuousOn
  · exact fun s _ => (hasDerivAt_axialCoordinate q s).differentiableAt.differentiableWithinAt
  · intro s _
    rw [(hasDerivAt_axialCoordinate q s).deriv]
    exact neg_nonpos.mpr (timeCoordinate_pos hq s).le

/-- The Lebesgue change of variables under the horospherical transverse rescaling. -/
private theorem lintegral_rescale (n : ℕ) (s : ℝ) (g : (Fin n → ℝ) → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ y, g y = ∫⁻ v, g (Real.exp (-s) • v) * ENNReal.ofReal (Real.exp (-(n * s))) := by
  let T : (Fin n → ℝ) → (Fin n → ℝ) := (Real.exp s • ·)
  let f : (Fin n → ℝ) → ℝ≥0∞ := fun v => g (Real.exp (-s) • v)
  have hf : Measurable f := hg.comp (measurable_const_smul _)
  have hT : Measurable T := measurable_const_smul _
  have hcomp (y : Fin n → ℝ) : f (T y) = g y := by
    dsimp only [f, T]
    rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
  have hmap : (volume : Measure (Fin n → ℝ)).map T =
      ENNReal.ofReal (Real.exp (-(n * s))) • volume := by
    rw [Measure.map_addHaar_smul volume (Real.exp_pos s).ne', Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin, ← Real.exp_nat_mul, abs_of_nonneg (inv_nonneg.mpr (Real.exp_pos _).le),
      ← Real.exp_neg]
  calc
    _ = ∫⁻ y, f (T y) := (lintegral_congr hcomp).symm
    _ = ∫⁻ v, f v ∂(volume : Measure _).map T := (lintegral_map hf hT).symm
    _ = _ := by
      rw [hmap, lintegral_smul_measure, lintegral_mul_const _ hf, smul_eq_mul, mul_comm]

end HorosphericalCoordinates

set_option maxHeartbeats 1600000 in
/-- **Horospherical coordinates** on `ℍ^{n+1}`: with
`x(s, v) = (cosh s + |v|² e^{−s}/2, e^{−s} v, −sinh s − |v|² e^{−s}/2)`,
`∫ f dm = ∫_ℝ ∫_{ℝⁿ} f(x(s, v)) e^{−ns} dv ds`. -/
theorem lintegral_hyperbolicMeasure_horospherical (n : ℕ) (f : (Fin (n + 2) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ x, f x ∂hyperbolicMeasure (n + 1) =
      ∫⁻ s, ∫⁻ v : Fin n → ℝ,
        f (Fin.cons (Real.cosh s + (∑ i, v i ^ 2) * Real.exp (-s) / 2)
            (Fin.snoc (fun i => v i * Real.exp (-s))
              (-Real.sinh s - (∑ i, v i ^ 2) * Real.exp (-s) / 2))) *
          ENNReal.ofReal (Real.exp (-(n * s))) := by
  let K (y : Fin n → ℝ) := ∑ i, y i ^ 2
  let W (y : Fin (n + 1) → ℝ) := ENNReal.ofReal (Real.sqrt (1 + ∑ i, y i ^ 2))⁻¹
  let F (z : Fin (n + 1) → ℝ) := f (hyperboloidChart (n + 1) z) * W z
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hchart := (continuous_hyperboloidChart (n + 1)).measurable
  have hF : Measurable F := (hf.comp hchart).mul hW
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have hE (p : ℝ × (Fin n → ℝ)) : e p = Fin.snoc p.2 p.1 := by
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  let Q (s : ℝ) (y : Fin n → ℝ) :=
    f (Fin.cons (HorosphericalCoordinates.timeCoordinate (K y) s)
      (Fin.snoc y (HorosphericalCoordinates.axialCoordinate (K y) s)))
  have hQ : Measurable (uncurry Q) := by
    apply hf.comp
    dsimp only [uncurry, Q, K, HorosphericalCoordinates.timeCoordinate,
      HorosphericalCoordinates.axialCoordinate]
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero]
      fun_prop
    · simp only [Fin.cons_succ]
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]
        fun_prop
      · simp only [Fin.snoc_castSucc]
        fun_prop
  -- For fixed transverse coordinates, the axial Jacobian cancels the chart density.
  have hstrand (y : Fin n → ℝ) : ∫⁻ z : ℝ, F (Fin.snoc y z) = ∫⁻ s : ℝ, Q s y := by
    have hk : 0 ≤ K y := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsum (z : ℝ) : (∑ i : Fin (n + 1), (Fin.snoc y z i) ^ 2) = K y + z ^ 2 := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_last, Fin.snoc_castSucc, K]
    have hsurj := HorosphericalCoordinates.surjective_axialCoordinate (K y) hk
    have hchange := lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
      (s := (univ : Set ℝ)) MeasurableSet.univ
      (fun s _ => (HorosphericalCoordinates.hasDerivAt_axialCoordinate (K y) s).hasDerivWithinAt)
      (HorosphericalCoordinates.antitone_axialCoordinate (K y) hk)
      (fun z => F (Fin.snoc y z))
    rw [image_univ, range_eq_univ.mpr hsurj, Measure.restrict_univ] at hchange
    refine hchange.trans (lintegral_congr fun s => ?_)
    let z := HorosphericalCoordinates.axialCoordinate (K y) s
    let p := HorosphericalCoordinates.timeCoordinate (K y) s
    have hp : 0 < p := HorosphericalCoordinates.timeCoordinate_pos hk s
    have hp' : Real.sqrt (1 + ∑ i : Fin (n + 1), (Fin.snoc y z i) ^ 2) = p := by
      rw [hsum]
      simpa only [add_assoc] using HorosphericalCoordinates.sqrt_axialCoordinate (K y) hk s
    change ENNReal.ofReal (- -p) * F (Fin.snoc y z) = f (Fin.cons p (Fin.snoc y z))
    dsimp only [F, W, hyperboloidChart_def]
    rw [hp', neg_neg, ← mul_assoc, mul_comm (ENNReal.ofReal p), mul_assoc,
      ← ENNReal.ofReal_mul hp.le, mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one, mul_one]
  -- Rescaling the transverse coordinates supplies the remaining Jacobian.
  have hscale (s : ℝ) :
      ∫⁻ y, Q s y = ∫⁻ v : Fin n → ℝ,
        f (Fin.cons (Real.cosh s + (∑ i, v i ^ 2) * Real.exp (-s) / 2)
            (Fin.snoc (fun i => v i * Real.exp (-s))
              (-Real.sinh s - (∑ i, v i ^ 2) * Real.exp (-s) / 2))) *
          ENNReal.ofReal (Real.exp (-(n * s))) := by
    have hPair : Measurable (fun y : Fin n → ℝ => (s, y)) :=
      measurable_const.prodMk measurable_id
    have hmeas : Measurable (Q s) := by
      simpa only [Function.comp_def, uncurry_apply_pair] using hQ.comp hPair
    refine (HorosphericalCoordinates.lintegral_rescale n s (Q s) hmeas).trans ?_
    refine lintegral_congr fun v => ?_
    have hK : K (Real.exp (-s) • v) * Real.exp s =
        (∑ i, v i ^ 2) * Real.exp (-s) := by
      calc
        _ = (Real.exp (-s) ^ 2 * Real.exp s) * ∑ i, v i ^ 2 := by
          simp only [K, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
          ring
        _ = _ := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_ofNat,
            show (2 : ℝ) * (-s) + s = -s by ring, mul_comm]
    have hscaled : Real.exp (-s) • v = fun i => v i * Real.exp (-s) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
    dsimp only [Q, HorosphericalCoordinates.timeCoordinate,
      HorosphericalCoordinates.axialCoordinate]
    rw [hK, hscaled]
  calc
    _ = ∫⁻ z : Fin (n + 1) → ℝ, F z := by
      rw [hyperbolicMeasure_def, lintegral_map hf hchart,
        lintegral_withDensity_eq_lintegral_mul volume hW]
      · exact lintegral_congr fun z => mul_comm _ _
      · have hG : Measurable (fun z => f (hyperboloidChart (n + 1) z)) := hf.comp hchart
        exact hG
    _ = ∫⁻ p : ℝ × (Fin n → ℝ), F (e p) := by
      symm
      have hpres := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
      exact hpres.lintegral_comp hF
    _ = ∫⁻ y : Fin n → ℝ, ∫⁻ z : ℝ, F (Fin.snoc y z) := by
      change (∫⁻ p, (F ∘ e) p ∂(volume : Measure ℝ).prod volume) = _
      rw [lintegral_prod_symm' _ (hF.comp e.measurable)]
      exact lintegral_congr fun y => lintegral_congr fun z => congrArg F (hE (z, y))
    _ = ∫⁻ y : Fin n → ℝ, ∫⁻ s : ℝ, Q s y := lintegral_congr hstrand
    _ = ∫⁻ s : ℝ, ∫⁻ y : Fin n → ℝ, Q s y := by
      symm
      exact lintegral_lintegral_swap hQ.aemeasurable
    _ = _ := lintegral_congr hscale

end SFVK.RankOne
