/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

import DLMF.Bessel.BesselIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import SFVKMathlib.RepresentationTheory.Continuous.MatrixElement
public import SFVK.MotionGroups.CircleModel

/-!
# Matrix elements and infinitesimal operators of the circle models

In the Fourier basis `eₙ(ψ) = e^{inψ}` of `L²(𝕋)`, the matrix elements of `T_R` are
`D_{mn}(g(r, φ; α)) = i^{n-m} e^{i(n-m)φ} e^{-inα} J_{n-m}(R r)`; the rotations act diagonally;
`D^{-R}_{mn} = (-1)^{m-n} D^R_{mn}`; and the translations act by the ladder operators
`(iR/2)(e^{-iβ} e_{n+1} + e^{iβ} e_{n-1})`. Vilenkin–Klimyk, *Representation of Lie Groups and
Special Functions*, Vol. 1, §4.1.3 (1)–(5), pp. 167–168, §4.1.2 (4)–(9), p. 167, and §4.1.5 (1),
p. 170; Miller, *Lie Theory and Special Functions*, §3-8 (3.57), p. 73.

The Fourier coefficient calculation uses lean-DLMF's Jacobi–Anger expansion
`DLMF.Bessel.hasSum_besselJ_jacobiAnger`.
-/

public noncomputable section

open AddCircle Complex MeasureTheory
open scoped Real InnerProductSpace Topology

namespace SFVK.MotionGroups

open CircleRealization

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- A Fourier character turns addition of angles into multiplication. -/
private theorem fourier_add_argument (n : ℤ) (ψ χ : 𝕋) :
    (fourier n (ψ + χ) : ℂ) = fourier n ψ * fourier n χ := by
  simp only [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]

/-- Translating a Fourier character multiplies it by a phase. -/
private theorem fourier_sub_angle (n : ℤ) (ψ : 𝕋) (α : ℝ) :
    (fourier n (ψ - (α : 𝕋)) : ℂ) = Complex.exp (-(n * α * I)) * fourier n ψ := by
  rw [sub_eq_add_neg, ← AddCircle.coe_neg, fourier_add_argument, fourier_circle_coe,
    mul_comm]
  congr 2
  push_cast
  ring

/-- The Fourier representative agrees almost everywhere after translating the circle. -/
private theorem ae_shift_fourierLp (n : ℤ) (α : ℝ) :
    (fun ψ : 𝕋 => fourierLp 2 n (ψ - (α : 𝕋))) =ᵐ[haarAddCircle]
      fun ψ => fourier n (ψ - (α : 𝕋)) :=
  (coeFn_fourierLp 2 n).comp_tendsto
    (measurePreserving_add_right haarAddCircle (-(α : 𝕋))).quasiMeasurePreserving.tendsto_ae

/-- Bessel's integral on the circle: the `n`-th Fourier coefficient of the plane wave is
`iⁿ e^{inφ} Jₙ(R r)` (Vilenkin–Klimyk Vol. 1 §4.1.5 (1), p. 170). -/
theorem integral_exp_inner_fourier (R : ℂ) (r φ : ℝ) (n : ℤ) :
    ∫ ψ, Complex.exp (I * R * (⟪planePoint r φ, unitVec ψ⟫_ℝ : ℝ)) * fourier n ψ
        ∂haarAddCircle =
      I ^ n * Complex.exp (n * φ * I) * besselJ n (R * r) := by
  let F : 𝕋 → ℂ := fun ψ =>
    Complex.exp (I * R * (⟪planePoint r φ, unitVec ψ⟫_ℝ : ℝ))
  let c : ℤ → ℂ := fun k =>
    I ^ (-k) * Complex.exp ((-k : ℤ) * φ * I) * besselJ (-k : ℤ) (R * r)
  have hsum (ψ : 𝕋) : HasSum (fun k => fourier k ψ • c k) (F ψ) := by
    obtain ⟨θ, rfl⟩ := QuotientAddGroup.mk_surjective ψ
    have h := (Equiv.neg ℤ).hasSum_iff.mpr
      (DLMF.Bessel.hasSum_besselJ_jacobiAnger (R * r) (π / 2 + φ - θ))
    convert h using 1
    · funext k
      have hquarter :
          Complex.exp ((-k : ℤ) * ((π : ℂ) / 2 * I)) = I ^ (-k) := by
        rw [Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]
      have hexp : Complex.exp (I * (-k : ℤ) * ((π / 2 + φ - θ : ℝ) : ℂ)) =
          Complex.exp ((-k : ℤ) * ((π : ℂ) / 2 * I)) *
            Complex.exp ((-k : ℤ) * φ * I) * Complex.exp (k * θ * I) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      change (fourier k (θ : 𝕋) : ℂ) * c k = besselJ (-k : ℤ) (R * r) * _
      rw [show (Equiv.neg ℤ) k = -k from rfl, fourier_circle_coe, hexp, hquarter]
      dsimp [c]
      ring
    · dsimp [F]
      congr 1
      rw [inner_planePoint_unitVec, fourier_circle_coe, Int.cast_one, one_mul, Complex.exp_mul_I,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
        zero_add, add_zero]
      rw [show π / 2 + φ - θ = π / 2 - (θ - φ) by ring, ← Complex.ofReal_sin,
        Real.sin_pi_div_two_sub, Real.cos_sub]
      push_cast
      ring
  have hnorm : Summable fun k => ‖c k‖ := by
    have h := (Equiv.neg ℤ).summable_iff.mpr (DLMF.Bessel.summable_norm_besselJ_int (R * r))
    convert h using 1
    funext k
    have he : ‖Complex.exp ((-k : ℤ) * φ * I)‖ = 1 := by
      rw [← fourier_circle_coe]
      exact Circle.norm_coe _
    change ‖I ^ (-k) * Complex.exp ((-k : ℤ) * φ * I) *
      besselJ (-k : ℤ) (R * r)‖ = ‖besselJ (-k : ℤ) (R * r)‖
    rw [norm_mul, norm_mul, norm_zpow, norm_I, one_zpow, he, one_mul, one_mul]
  have h := congrFun (fourierCoeff_eq_of_hasSum_of_summable_norm hsum hnorm) (-n)
  simpa only [fourierCoeff, neg_neg, smul_eq_mul, mul_comm (fourier n _), c] using h

/-- Matrix elements of `T_R` (Vilenkin–Klimyk Vol. 1 §4.1.3 (1)–(5), pp. 167–168):
`D_{mn}(g(r, φ; α)) = i^{n-m} e^{i(n-m)φ} e^{-inα} J_{n-m}(R r)`. -/
theorem matrixElement_circleRep_polar (R : ℂ) (m n : ℤ) (r φ α : ℝ) :
    (circleRep R).matrixElement fourierBasis m n (polar r φ α) =
      I ^ (n - m) * Complex.exp ((n - m : ℤ) * φ * I) * Complex.exp (-(n * α * I)) *
        besselJ (n - m : ℤ) (R * r) := by
  rw [ContRepresentation.matrixElement_def, coe_fourierBasis, MeasureTheory.L2.inner_def]
  have hintegrand :
      (∫ ψ : 𝕋, ⟪fourierLp 2 m ψ, circleRep R (polar r φ α) (fourierLp 2 n) ψ⟫_ℂ
        ∂haarAddCircle) =
      ∫ ψ : 𝕋, Complex.exp (-(n * α * I)) *
        (Complex.exp (I * R * (⟪planePoint r φ, unitVec ψ⟫_ℝ : ℝ)) * fourier (n - m) ψ)
        ∂haarAddCircle := by
    apply integral_congr_ae
    filter_upwards [coeFn_fourierLp 2 m, circleRep_ae_eq R (polar r φ α) (fourierLp 2 n),
      ae_shift_fourierLp n α] with ψ hm hn hshift
    rw [hm, hn, circleAction_def]
    change ⟪(fourier m ψ : ℂ), Complex.exp (I * R * (⟪planePoint r φ, unitVec ψ⟫_ℝ : ℝ)) *
      fourierLp 2 n (ψ - rotAngle (rotation α))⟫_ℂ = _
    rw [rotAngle_rotation, hshift, fourier_sub_angle, RCLike.inner_apply, ← fourier_neg]
    rw [sub_eq_add_neg, fourier_add]
    ring
  rw [hintegrand, integral_const_mul, integral_exp_inner_fourier]
  ring

/-- Weights: `T_R(k_α) eₙ = e^{-inα} eₙ`. -/
theorem circleRep_rotation_fourierLp (R : ℂ) (α : ℝ) (n : ℤ) :
    circleRep R ⟨0, rotation α⟩ (fourierLp 2 n) =
      Complex.exp (-(n * α * I)) • fourierLp 2 n := by
  apply Lp.ext
  filter_upwards [circleRep_ae_eq R ⟨0, rotation α⟩ (fourierLp 2 n),
    ae_shift_fourierLp n α, coeFn_fourierLp 2 n,
    Lp.coeFn_smul (Complex.exp (-(n * α * I))) (fourierLp 2 n)] with ψ hrep hshift hchar hsmul
  rw [hrep, hsmul, circleAction_def, rotAngle_rotation, inner_zero_left, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero, one_mul, hshift, fourier_sub_angle]
  change _ = Complex.exp (-(n * α * I)) * fourierLp 2 n ψ
  rw [hchar]

/-- Sign change of `R`: `D^{-R}_{mn} = (-1)^{m-n} D^R_{mn}`. -/
theorem matrixElement_circleRep_neg (R : ℂ) (m n : ℤ) (g : MotionGroup 2) :
    (circleRep (-R)).matrixElement fourierBasis m n g =
      (-1 : ℂ) ^ (m - n) * (circleRep R).matrixElement fourierBasis m n g := by
  obtain ⟨φ, α, hg⟩ := exists_polar g
  rw [hg, matrixElement_circleRep_polar, matrixElement_circleRep_polar, neg_mul, besselJ_int_neg]
  have hsign : (-1 : ℂ) ^ (m - n) = (-1 : ℂ) ^ (n - m) := by
    rw [show m - n = -(n - m) by omega, zpow_neg, ← inv_zpow]
    simp
  rw [hsign]
  ring

/-- Ladder operators (Vilenkin–Klimyk Vol. 1 §4.1.2 (4)–(9), p. 167): along the translation
direction `e(β)`, `d/dt T_R(t e(β)) eₙ |₀ = (iR/2)(e^{-iβ} e_{n+1} + e^{iβ} e_{n-1})`. -/
theorem hasDerivAt_circleAction_fourier (R : ℂ) (β : ℝ) (n : ℤ) (ψ : 𝕋) :
    HasDerivAt (fun t : ℝ => circleAction R ⟨planePoint t β, 1⟩ (fourier n) ψ)
      (I * R / 2 * (Complex.exp (-(β * I)) * fourier (n + 1) ψ +
        Complex.exp (β * I) * fourier (n - 1) ψ)) 0 := by
  have hphase :
      ((2 * ⟪planePoint 1 β, unitVec ψ⟫_ℝ : ℝ) : ℂ) =
        Complex.exp (-(β * I)) * fourier 1 ψ +
          Complex.exp (β * I) * fourier (-1) ψ := by
    rw [inner_planePoint_unitVec, one_mul, fourier_neg, show -(β * I) = ((-β : ℝ) : ℂ) * I by
      push_cast; ring, Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im, Complex.re_ofNat,
        Complex.im_ofNat] <;> ring
  have hzero : (⟨planePoint 0 β, 1⟩ : MotionGroup 2) = 1 := by
    apply MotionGroup.ext
    · rw [MotionGroup.one_a]
      apply PiLp.ext
      intro i
      fin_cases i <;> simp
    · exact MotionGroup.one_k.symm
  have h := hasDerivAt_circleAction_translation R β 0 (fourier n) ψ
  rw [hzero, circleAction_one] at h
  convert h using 1
  rw [sub_eq_add_neg, fourier_add, fourier_add]
  have hphase' := congrArg (fun z : ℂ => (I * R / 2) * z * fourier n ψ) hphase
  push_cast at hphase'
  linear_combination -hphase'

/-- A matrix coefficient is the integral of a pointwise action against a Fourier character. -/
private theorem matrixElement_circleRep_eq_integral (R : ℂ) (m n : ℤ) (g : MotionGroup 2) :
    (circleRep R).matrixElement fourierBasis m n g =
      ∫ ψ : 𝕋, star (fourier m ψ : ℂ) * circleAction R g (fourier n) ψ ∂haarAddCircle := by
  obtain ⟨α, hα⟩ := exists_rotation_eq g.k
  rw [ContRepresentation.matrixElement_def, coe_fourierBasis, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_fourierLp 2 m, circleRep_ae_eq R g (fourierLp 2 n),
    ae_shift_fourierLp n α] with ψ hm hn hshift
  rw [hm, hn, circleAction_def, circleAction_def, hα, rotAngle_rotation, hshift, RCLike.inner_apply]
  exact mul_comm _ _

/-- Lie derivative of the matrix elements:
`d/dt D_{mn}(g (t e₁, 1)) |₀ = (iR/2)(D_{m,n+1}(g) + D_{m,n-1}(g))`. -/
theorem hasDerivAt_matrixElement_mul_translation (R : ℂ) (m n : ℤ) (g : MotionGroup 2) :
    HasDerivAt
      (fun t : ℝ => (circleRep R).matrixElement fourierBasis m n (g * ⟨planePoint t 0, 1⟩))
      (I * R / 2 * ((circleRep R).matrixElement fourierBasis m (n + 1) g +
        (circleRep R).matrixElement fourierBasis m (n - 1) g)) 0 := by
  let a (t : ℝ) : MotionGroup 2 := ⟨planePoint t 0, 1⟩
  let angle (ψ : 𝕋) := ψ - rotAngle g.k
  let weight (ψ : 𝕋) :=
    star (fourier m ψ : ℂ) * Complex.exp (I * R * (⟪g.a, unitVec ψ⟫_ℝ : ℝ))
  let scale (ψ : 𝕋) := I * R * (⟪planePoint 1 0, unitVec (angle ψ)⟫_ℝ : ℝ)
  let F (t : ℝ) (ψ : 𝕋) := weight ψ * circleAction R (a t) (fourier n) (angle ψ)
  let F' (t : ℝ) (ψ : 𝕋) := weight ψ * (scale ψ *
    circleAction R (a t) (fourier n) (angle ψ))
  have hc (g : MotionGroup 2) (n : ℤ) : Continuous (circleAction R g (fourier n)) := by
    change Continuous (fun ψ : 𝕋 => circleAction R g (fourier n) ψ)
    simp_rw [circleAction_def]
    exact (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_const.inner continuous_unitVec))).cexp.mul
      ((fourier n).continuous.comp (continuous_id.sub continuous_const))
  have ha : Continuous angle := continuous_id.sub continuous_const
  have hw : Continuous weight :=
    (continuous_star.comp (fourier m).continuous).mul
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.inner continuous_unitVec))).cexp
  have hs : Continuous scale := continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_const.inner (continuous_unitVec.comp ha)))
  have hF (t : ℝ) : Continuous (F t) := hw.mul ((hc (a t) n).comp ha)
  have hF' (t : ℝ) : Continuous (F' t) := hw.mul (hs.mul ((hc (a t) n).comp ha))
  have hd (t : ℝ) (ψ : 𝕋) : HasDerivAt (fun s => F s ψ) (F' t ψ) t :=
    (hasDerivAt_circleAction_translation R 0 t (fourier n) (angle ψ)).const_mul _
  have hjoint : Continuous (fun p : ℝ × 𝕋 => F' p.1 p.2) := by
    have ha' : Continuous (fun p : ℝ × 𝕋 => angle p.2) := ha.comp continuous_snd
    have hh : Continuous (fun p : ℝ × 𝕋 => circleAction R (a p.1) (fourier n) (angle p.2)) := by
      have he (p : ℝ × 𝕋) :
          circleAction R (a p.1) (fourier n) (angle p.2) =
            Complex.exp (scale p.2 * p.1) * fourier n (angle p.2) := by
        have hangle : rotAngle (1 : SOn 2) = (0 : 𝕋) := by simp [← rotation_zero]
        simp only [circleAction_def, a, hangle, sub_zero, scale, inner_planePoint_unitVec,
          one_mul, Complex.ofReal_mul]
        congr 2
        ring
      simp_rw [he]
      exact ((hs.comp continuous_snd).mul (Complex.continuous_ofReal.comp continuous_fst)).cexp.mul
        ((fourier n).continuous.comp ha')
    exact (hw.comp continuous_snd).mul ((hs.comp continuous_snd).mul hh)
  let K := Set.Icc (-1 : ℝ) 1 ×ˢ (Set.univ : Set 𝕋)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.bddAbove_image hjoint.norm.continuousOn
  have hD := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := haarAddCircle) (F := F) (F' := F') (s := Set.Icc (-1 : ℝ) 1)
    (bound := fun _ => C) (x₀ := (0 : ℝ))
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun t => (hF t).aestronglyMeasurable)
    ((hF 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hF' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ψ t ht =>
      hC (Set.mem_image_of_mem (fun p : ℝ × 𝕋 => ‖F' p.1 p.2‖)
        (show (t, ψ) ∈ K from ⟨ht, Set.mem_univ ψ⟩)))
    (integrable_const C) (Filter.Eventually.of_forall fun ψ t _ => hd t ψ)).2
  have hmat (t : ℝ) : (circleRep R).matrixElement fourierBasis m n (g * a t) =
      ∫ ψ : 𝕋, F t ψ ∂haarAddCircle := by
    rw [matrixElement_circleRep_eq_integral, circleAction_mul]
    apply integral_congr_ae
    filter_upwards with ψ
    simp only [F, weight, angle]
    rw [circleAction_def]
    ring
  change HasDerivAt (fun t => (circleRep R).matrixElement fourierBasis m n (g * a t)) _ 0
  rw [funext hmat]
  convert hD using 1
  let G (j : ℤ) (ψ : 𝕋) := weight ψ * fourier j (angle ψ)
  have hG (j : ℤ) : Integrable (G j) haarAddCircle :=
    (hw.mul ((fourier j).continuous.comp ha)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hmatrix (j : ℤ) :
      (circleRep R).matrixElement fourierBasis m j g = ∫ ψ, G j ψ ∂haarAddCircle := by
    rw [matrixElement_circleRep_eq_integral]
    apply integral_congr_ae
    filter_upwards with ψ
    dsimp only [G, weight, angle]
    rw [circleAction_def]
    ring
  rw [hmatrix, hmatrix, ← integral_add (hG (n + 1)) (hG (n - 1))]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ψ
  have h := (hasDerivAt_circleAction_translation R 0 0 (fourier n) (angle ψ)).deriv.symm.trans
    (hasDerivAt_circleAction_fourier R 0 n (angle ψ)).deriv
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul] at h
  dsimp only [F', scale]
  rw [h]
  dsimp only [G]
  ring

end SFVK.MotionGroups
