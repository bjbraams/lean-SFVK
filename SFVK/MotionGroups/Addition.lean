/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

import DLMF.Bessel.GrafAddition
import DLMF.Bessel.BesselIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.JacobianOneDim
import SFVK.MotionGroups.CircleModel
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The addition theorem and the multiplication formula for `Jₙ`

The matrix-element identity `D(g₁g₂) = D(g₁)D(g₂)` for the circle model of `M(2)`, written in
polar coordinates, is the addition theorem
`e^{i(n-m)φ} J_{n-m}(R r) = Σₖ J_{k-m}(R r₁) J_{n-k}(R r₂) e^{i(n-k)φ₂}` with
`r e^{iφ} = r₁ + r₂ e^{iφ₂}`; integrating it over `φ₂` gives the multiplication formula and its
radial form. Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 1,
§4.1.4 (1)–(9), pp. 168–170, where the printed (8) has an exponential that must be the cosine;
Miller, *Lie Theory and Special Functions*, (3.32), p. 63. Graf's form of the addition theorem
is lean-DLMF's `DLMF.Bessel.hasSum_besselJ_graf`. The radial formula uses Mathlib's
change of variables for an antitone map on a compact interval.
-/

public noncomputable section

open Complex MeasureTheory Set
open scoped Real ComplexConjugate

namespace SFVK.MotionGroups

/-- Addition theorem in polar form (Vilenkin–Klimyk Vol. 1 §4.1.4 (1)–(6), pp. 168–169): with
`r e^{iφ} = r₁ + r₂ e^{iφ₂}`,
`e^{i(n-m)φ} J_{n-m}(R r) = Σₖ J_{k-m}(R r₁) J_{n-k}(R r₂) e^{i(n-k)φ₂}`. -/
theorem hasSum_besselJ_polar_addition (R : ℂ) (m n : ℤ) {r₁ r₂ φ₂ r φ : ℝ}
    (h : (r : ℂ) * Complex.exp (φ * I) = r₁ + r₂ * Complex.exp (φ₂ * I)) :
    HasSum (fun k : ℤ => besselJ (k - m : ℤ) (R * r₁) * besselJ (n - k : ℤ) (R * r₂) *
        Complex.exp ((n - k : ℤ) * φ₂ * I))
      (Complex.exp ((n - m : ℤ) * φ * I) * besselJ (n - m : ℤ) (R * r)) := by
  have hc : r * Real.cos φ = r₁ + r₂ * Real.cos φ₂ := by
    simpa [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_re]
      using congrArg Complex.re h
  have hs : r * Real.sin φ = r₂ * Real.sin φ₂ := by
    simpa [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_im]
      using congrArg Complex.im h
  have hc' : R * r * Complex.cos (φ : ℂ) = R * r₁ - (-(R * r₂)) * Complex.cos (-(φ₂ : ℂ)) := by
    have hcast := congrArg (fun x : ℝ => (x : ℂ)) hc
    push_cast at hcast
    rw [Complex.cos_neg]
    linear_combination R * hcast
  have hs' : R * r * Complex.sin (φ : ℂ) = (-(R * r₂)) * Complex.sin (-(φ₂ : ℂ)) := by
    have hcast := congrArg (fun x : ℝ => (x : ℂ)) hs
    push_cast at hcast
    rw [Complex.sin_neg]
    linear_combination R * hcast
  -- Changing the summation index leaves the sum unchanged on the integers.
  have hsum := (Equiv.subRight n : ℤ ≃ ℤ).hasSum_iff.mpr
    (DLMF.Bessel.hasSum_besselJ_graf (n - m) hc' hs')
  convert hsum using 1
  · funext k
    have horder : n - m + (k - n) = k - m := by omega
    have hneg : k - n = -(n - k) := by omega
    simp only [Function.comp_apply, Equiv.subRight_apply]
    rw [horder, hneg]
    simp only [Int.cast_neg, Complex.besselJ_neg_comm, neg_neg]
    congr 2
    push_cast
    ring
  · push_cast
    rw [mul_comm]
    congr 2
    ring

/-- Multiplication formula (Vilenkin–Klimyk Vol. 1 §4.1.4 (7), pp. 169–170): the mean over the
circle `w = r₁ + r₂ e^{iφ₂}` of `(w/|w|)ⁿ e^{-imφ₂} Jₙ(R|w|)` is `J_{n-m}(R r₁) J_m(R r₂)`. -/
theorem integral_besselJ_circleMean (R : ℂ) (m n : ℤ) (r₁ r₂ : ℝ) :
    ∫ φ₂ in (0 : ℝ)..2 * π,
        (let w : ℂ := r₁ + r₂ * Complex.exp (φ₂ * I)
         (w / ‖w‖) ^ n * Complex.exp (-(m * φ₂ * I)) * besselJ n (R * ‖w‖)) =
      2 * π * besselJ (n - m : ℤ) (R * r₁) * besselJ m (R * r₂) := by
  let T := AddCircle (2 * π)
  have : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  let w (ψ : T) : ℂ := r₁ + r₂ * fourier 1 ψ
  let F (ψ : T) : ℂ := (w ψ / ‖w ψ‖) ^ n * besselJ n (R * ‖w ψ‖)
  let c (j : ℤ) : ℂ := besselJ (n - j : ℤ) (R * r₁) * besselJ j (R * r₂)
  have heq (φ : ℝ) : w (φ : T) = r₁ + r₂ * Complex.exp (φ * I) := by
    dsimp only [w]
    rw [fourier_circle_coe]
    simp
  have hsum (ψ : T) : HasSum (fun j : ℤ => fourier j ψ • c j) (F ψ) := by
    obtain ⟨φ, rfl⟩ := QuotientAddGroup.mk_surjective ψ
    let α := Complex.arg (w (φ : T))
    have hw : ((‖w (φ : T)‖ : ℝ) : ℂ) * Complex.exp (α * I) =
        r₁ + r₂ * Complex.exp (φ * I) :=
      (Complex.norm_mul_exp_arg_mul_I _).trans (heq φ)
    have h := hasSum_besselJ_polar_addition R 0 n hw
    let e : ℤ ≃ ℤ := (Equiv.neg ℤ).trans (Equiv.addRight n)
    have h' := e.hasSum_iff.mpr h
    have hF : F (φ : T) =
        Complex.exp (n * α * I) * besselJ n (R * ‖w (φ : T)‖) := by
      by_cases hzero : w (φ : T) = 0
      · by_cases hn : n = 0
        · simp [F, α, hzero, hn]
        · simp [F, hzero, Complex.besselJ_zero, Int.cast_ne_zero.mpr hn]
      · have hnorm : (‖w (φ : T)‖ : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hzero)
        have hratio : w (φ : T) / ‖w (φ : T)‖ = Complex.exp (α * I) := by
          apply (div_eq_iff hnorm).mpr
          exact ((Complex.norm_mul_exp_arg_mul_I (w (φ : T))).symm).trans (mul_comm _ _)
        dsimp only [F]
        rw [hratio, ← Complex.exp_int_mul]
        congr 2
        ring
    rw [hF]
    convert h' using 1
    · funext j
      have hj : e j = n - j := by simp [e, sub_eq_neg_add]
      simp only [Function.comp_apply, hj, sub_zero, sub_sub_cancel, fourier_circle_coe,
        smul_eq_mul, c]
      ring
    · simp
  have hnorm : Summable (fun j => ‖c j‖) := by
    have h := summable_mul_of_summable_norm
      (DLMF.Bessel.summable_norm_besselJ_int (R * r₁))
      (DLMF.Bessel.summable_norm_besselJ_int (R * r₂))
    have hi : Function.Injective (fun j : ℤ => (n - j, j)) :=
      fun x y hxy => congrArg Prod.snd hxy
    have h' := h.norm.comp_injective hi
    have he : (fun j => ‖c j‖) = (fun p : ℤ × ℤ =>
      ‖besselJ p.1 (R * r₁) * besselJ p.2 (R * r₂)‖) ∘ fun j => (n - j, j) := rfl
    rw [he]
    exact h'
  have hcoeff := congrFun (fourierCoeff_eq_of_hasSum_of_summable_norm hsum hnorm) m
  have hInt (t : ℝ) :
      fourier (-m) (t : T) • F t =
        (let w : ℂ := r₁ + r₂ * Complex.exp (t * I)
         (w / ‖w‖) ^ n * Complex.exp (-(m * t * I)) * besselJ n (R * ‖w‖)) := by
    simp only [F, heq, fourier_circle_coe, Int.cast_neg, neg_mul, smul_eq_mul]
    ring
  rw [fourierCoeff, AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * π) 0, zero_add] at hcoeff
  simp_rw [hInt, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat]
    at hcoeff
  have hpi : (2 * π : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have h := congrArg (fun z : ℂ => (2 * π : ℂ) * z) hcoeff
  change (2 * π : ℂ) * _ = (2 * π : ℂ) * c m at h
  rw [← mul_assoc, mul_inv_cancel₀ hpi, one_mul] at h
  simpa only [c, mul_assoc] using h

/-- Radial form of the multiplication formula (Vilenkin–Klimyk Vol. 1 §4.1.4 (8)–(9),
pp. 169–170, with the cosine where the printed (8) has the exponential): for `r₁, r₂ > 0`,
`r₁ ≠ r₂`, `J_{n-m}(r₁) J_m(r₂) = (2/π) ∫_{|r₁-r₂|}^{r₁+r₂} cos(nφ - mφ₂) r Jₙ(r) / √Δ dr`,
`Δ = 4r₁²r₂² - (r² - r₁² - r₂²)²`, with `φ₂ = arccos((r² - r₁² - r₂²)/(2r₁r₂))` and
`φ = arg(r₁ + r₂ e^{iφ₂})`. -/
theorem besselJ_mul_besselJ_eq_integral (m n : ℤ) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂)
    (h₁₂ : r₁ ≠ r₂) :
    besselJ (n - m : ℤ) r₁ * besselJ m r₂ =
      2 / π * ∫ r in |r₁ - r₂|..r₁ + r₂,
        (let φ₂ := Real.arccos ((r ^ 2 - r₁ ^ 2 - r₂ ^ 2) / (2 * r₁ * r₂))
         let φ := Complex.arg (r₁ + r₂ * Complex.exp (φ₂ * I))
         (Real.cos (n * φ - m * φ₂) * r /
            Real.sqrt (4 * r₁ ^ 2 * r₂ ^ 2 - (r ^ 2 - r₁ ^ 2 - r₂ ^ 2) ^ 2) : ℝ) *
           besselJ n r) := by
  let T := AddCircle (2 * π)
  have : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  let w (t : ℝ) : ℂ := r₁ + r₂ * Complex.exp (t * I)
  let radius (t : ℝ) := ‖w t‖
  let phase (t : ℝ) := (n : ℝ) * (w t).arg - (m : ℝ) * t
  let F (t : ℝ) : ℂ := (w t / radius t) ^ n * Complex.exp (-(m * t * I)) * besselJ n (radius t)
  let H (r : ℝ) : ℂ :=
    let θ := Real.arccos ((r ^ 2 - r₁ ^ 2 - r₂ ^ 2) / (2 * r₁ * r₂))
    (Real.cos (phase θ) * r / Real.sqrt (4 * r₁ ^ 2 * r₂ ^ 2 -
      (r ^ 2 - r₁ ^ 2 - r₂ ^ 2) ^ 2) : ℝ) * besselJ n r
  have hw (t : ℝ) : w t ≠ 0 := by
    intro h
    have he : (r₂ : ℂ) * Complex.exp (t * I) = -(r₁ : ℂ) := by
      exact eq_neg_of_add_eq_zero_right h
    have hnorm := congrArg norm he
    simp [Complex.norm_exp, Complex.mul_re, abs_of_pos h₁, abs_of_pos h₂] at hnorm
    exact h₁₂ hnorm.symm
  have hrad (t : ℝ) : 0 < radius t := norm_pos_iff.mpr (hw t)
  have hradSq (t : ℝ) : radius t ^ 2 = r₁ ^ 2 + r₂ ^ 2 + 2 * r₁ * r₂ * Real.cos t := by
    dsimp only [radius]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [w, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, zero_mul, sub_zero, zero_add, add_zero,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    nlinarith [congrArg (fun x : ℝ => r₂ ^ 2 * x) (Real.sin_sq_add_cos_sq t)]
  have hFphase (t : ℝ) : F t = Complex.exp ((phase t : ℝ) * I) * besselJ n (radius t) := by
    have hne := Complex.ofReal_ne_zero.mpr (hrad t).ne'
    have hratio : w t / radius t = Complex.exp ((w t).arg * I) :=
      (div_eq_iff hne).mpr ((Complex.norm_mul_exp_arg_mul_I (w t)).symm.trans (mul_comm _ _))
    dsimp only [F, phase]
    rw [hratio, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hconj (t : ℝ) : w (-t) = conj (w t) := by
    simp only [w, map_add, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
      Complex.conj_I, Complex.ofReal_neg, neg_mul, mul_neg]
  have hpair (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) π) :
      F t + F (-t) = 2 * ((Real.cos (phase t) : ℂ) * besselJ n (radius t)) := by
    have him : 0 < (w t).im := by
      simpa [w, Complex.mul_im, Complex.exp_ofReal_mul_I_im] using
        mul_pos h₂ (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
    have harg : (w t).arg ≠ π := fun h => him.ne' (Complex.arg_eq_pi_iff.mp h).2
    have hphi : phase (-t) = -phase t := by
      dsimp only [phase]
      rw [hconj, Complex.arg_conj, ite_eq_right harg]
      ring
    have he : radius (-t) = radius t := by simp [radius, hconj]
    rw [hFphase, hFphase, he, hphi, Complex.ofReal_cos, Complex.cos]
    push_cast
    ring
  let Fc (ψ : T) : ℂ :=
    let z : ℂ := r₁ + r₂ * fourier 1 ψ
    (z / ‖z‖) ^ n * fourier (-m) ψ * besselJ n ‖z‖
  have hFc (t : ℝ) : Fc (t : T) = F t := by
    simp only [Fc, F, radius, w, fourier_circle_coe, Int.cast_one, one_mul, Int.cast_neg]
    congr 3
    ring
  have hsame : (∫ t in (-π)..π, F t) = ∫ t in (0 : ℝ)..2 * π, F t := by
    simp_rw [← hFc]
    have hleft := AddCircle.intervalIntegral_preimage (2 * π) (-π) Fc
    have hright := AddCircle.intervalIntegral_preimage (2 * π) 0 Fc
    rw [show -π + 2 * π = π by ring] at hleft
    rw [zero_add] at hright
    exact hleft.trans hright.symm
  have hcontW : Continuous w := by dsimp only [w]; fun_prop
  have hJ : Continuous (besselJ (n : ℂ)) :=
    continuousOn_univ.mp (Complex.analyticOnNhd_besselJ_int n).continuousOn
  have hF : Continuous F := by
    have h := hcontW.div (Complex.continuous_ofReal.comp hcontW.norm)
      (fun t => Complex.ofReal_ne_zero.mpr (hrad t).ne')
    have he : Continuous (fun t : ℝ => Complex.exp (-(m * t * I))) := by fun_prop
    have hpow := h.zpow₀ n fun t => Or.inl (div_ne_zero (hw t)
      (Complex.ofReal_ne_zero.mpr (hrad t).ne'))
    exact (hpow.mul he).mul (hJ.comp (Complex.continuous_ofReal.comp hcontW.norm))
  have hfold :
      (∫ t in (0 : ℝ)..2 * π, F t) =
        2 * ∫ t in Ioo (0 : ℝ) π, (Real.cos (phase t) : ℂ) * besselJ n (radius t) := by
    rw [← hsame, ← intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable (-π) 0) (hF.intervalIntegrable 0 π)]
    rw [show (∫ t in (-π)..(0 : ℝ), F t) = ∫ t in (0 : ℝ)..π, F (-t) by
      simpa only [neg_zero] using (intervalIntegral.integral_comp_neg F (a := 0) (b := π)).symm]
    have hneg : IntervalIntegrable (fun t => F (-t)) volume 0 π :=
      (hF.comp continuous_neg).intervalIntegrable 0 π
    rw [add_comm, ← intervalIntegral.integral_add (hF.intervalIntegrable 0 π) hneg,
      intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo,
      ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioo hpair
  let s (t : ℝ) := r₁ ^ 2 + r₂ ^ 2 + 2 * r₁ * r₂ * Real.cos t
  have hsr (t : ℝ) : Real.sqrt (s t) = radius t := by
    rw [show s t = radius t ^ 2 from (hradSq t).symm, Real.sqrt_sq (hrad t).le]
  let speed (t : ℝ) := -(r₁ * r₂ * Real.sin t) / radius t
  have hderiv (t : ℝ) (_ : t ∈ Ioo (0 : ℝ) π) : HasDerivAt radius (speed t) t := by
    have hs : HasDerivAt s (-(2 * r₁ * r₂ * Real.sin t)) t := by
      convert ((Real.hasDerivAt_cos t).const_mul (2 * r₁ * r₂)).const_add (r₁ ^ 2 + r₂ ^ 2) using 1
      ring
    have hn : s t ≠ 0 := by
      dsimp only [s]
      rw [← hradSq]
      exact pow_ne_zero _ (hrad t).ne'
    have h := (Real.hasDerivAt_sqrt hn).comp t hs
    have hf : Real.sqrt ∘ s = radius := funext hsr
    rw [hf, hsr] at h
    convert h using 1
    dsimp only [speed]
    field_simp [(hrad t).ne']
  have hsign (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) π) : speed t ≤ 0 := by
    dsimp only [speed]
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (hrad t).le
  have hchange := integral_Icc_deriv_smul_of_deriv_nonpos (f := radius) (g := H)
    hcontW.norm.continuousOn hderiv hsign Real.pi_pos.le
  have hzero : radius 0 = r₁ + r₂ := by
    simp [radius, w, ← Complex.ofReal_add, Complex.norm_real, abs_of_pos (add_pos h₁ h₂)]
  have hπ : radius π = |r₁ - r₂| := by
    simp only [radius, w, Complex.exp_pi_mul_I, mul_neg_one, ← sub_eq_add_neg,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hzero, hπ, integral_Icc_eq_integral_Ioo, integral_Icc_eq_integral_Ioo] at hchange
  have hcos (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) π) :
      speed t • H (radius t) = -(1 / 2 : ℂ) *
        ((Real.cos (phase t) : ℂ) * besselJ n (radius t)) := by
    have hc : (radius t ^ 2 - r₁ ^ 2 - r₂ ^ 2) / (2 * r₁ * r₂) = Real.cos t := by
      rw [hradSq t]
      field_simp [h₁.ne', h₂.ne']
      ring
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have hd : Real.sqrt (4 * r₁ ^ 2 * r₂ ^ 2 -
        (radius t ^ 2 - r₁ ^ 2 - r₂ ^ 2) ^ 2) = 2 * r₁ * r₂ * Real.sin t := by
      have hh : radius t ^ 2 - r₁ ^ 2 - r₂ ^ 2 = 2 * r₁ * r₂ * Real.cos t := by
        rw [hradSq]
        ring
      rw [hh, show 4 * r₁ ^ 2 * r₂ ^ 2 - (2 * r₁ * r₂ * Real.cos t) ^ 2 =
          (2 * r₁ * r₂ * Real.sin t) ^ 2 by
        nlinarith [congrArg (fun x : ℝ => 4 * r₁ ^ 2 * r₂ ^ 2 * x) (Real.sin_sq_add_cos_sq t)]]
      exact Real.sqrt_sq (by positivity)
    dsimp only [H, speed]
    rw [hc, Real.arccos_cos ht.1.le ht.2.le, hd, Complex.real_smul]
    have hsC : Complex.sin (t : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sin]
      exact Complex.ofReal_ne_zero.mpr hs.ne'
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr h₁.ne', Complex.ofReal_ne_zero.mpr h₂.ne', hsC,
      Complex.ofReal_ne_zero.mpr (hrad t).ne']
  rw [setIntegral_congr_fun measurableSet_Ioo hcos, integral_const_mul] at hchange
  have hfolded := integral_besselJ_circleMean (1 : ℂ) m n r₁ r₂
  simp only [one_mul] at hfolded
  change (∫ t in (0 : ℝ)..2 * π, F t) = _ at hfolded
  rw [hfold] at hfolded
  rw [intervalIntegral.integral_of_le (by
    rw [abs_le]; constructor <;> linarith), integral_Ioc_eq_integral_Ioo]
  change _ = (2 / π : ℂ) * ∫ r in Ioo |r₁ - r₂| (r₁ + r₂), H r
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]
  linear_combination -hfolded / 2 - 2 * hchange

end SFVK.MotionGroups
