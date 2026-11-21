/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.RankOne.Basic.Jacobi

import DLMF.Gamma.ComplexBinet
import Mathlib.Analysis.Calculus.DSlope
import TauCeti.Analysis.SpecialFunctions.Gamma.Order

/-!
# Growth of the Jacobi Plancherel density

The inverse square of the Jacobi `c`-function has polynomial growth on the real spectral axis.
Mathlib's Legendre duplication formula expresses the density using Gamma ratios. The proof uses
the vertical Stirling asymptotic from lean-DLMF and the simple zeros of reciprocal Gamma from
Tau Ceti to bound the ratios at infinity and at finite height, respectively.

## Main result

* `SFVK.RankOne.norm_cFunction_inv_sq_le`.
-/

public noncomputable section

open Complex ComplexConjugate Filter Topology Set
open scoped Real

namespace SFVK.RankOne

namespace JacobiDensity

/-- A point of height `t` on the vertical line through `x`. -/
private def verticalArgument (x t : ℝ) : ℂ := (x : ℂ) + I * t

/-- The Gamma function is nonzero off the real axis. -/
private theorem Gamma_vertical_ne_zero (x : ℝ) {t : ℝ} (ht : t ≠ 0) :
    Gamma (verticalArgument x t) ≠ 0 := by
  apply Gamma_ne_zero
  intro k hk
  apply ht
  simpa only [verticalArgument, add_im, ofReal_im, I_mul_im, ofReal_re, zero_add, neg_im,
    natCast_im, neg_zero] using congrArg Complex.im hk

/-- The vertical parametrization is continuous. -/
private theorem continuous_verticalArgument (x : ℝ) : Continuous (verticalArgument x) := by
  change Continuous (fun t : ℝ => (x : ℂ) + I * (t : ℂ))
  fun_prop

/-- The Gamma function is continuous at every nonpole of a vertical line. -/
private theorem continuousAt_Gamma_vertical {x t : ℝ}
    (h : t ≠ 0 ∨ ∀ k : ℕ, x ≠ -(k : ℝ)) :
    ContinuousAt (fun s => Gamma (verticalArgument x s)) t := by
  refine (continuousAt_Gamma _ ?_).comp' (continuous_verticalArgument x).continuousAt
  intro k hk
  rcases h with hn | hx
  · exact Gamma_vertical_ne_zero x hn (by rw [hk, Gamma_neg_nat_eq_zero])
  · apply hx k
    simpa only [verticalArgument, add_re, ofReal_re, I_mul_re, ofReal_im, neg_zero,
      add_zero, neg_re, natCast_re] using congrArg Complex.re hk

/-- The reciprocal Gamma function is differentiable on every vertical line. -/
private theorem differentiable_vertical_invGamma (x : ℝ) :
    Differentiable ℝ (fun t => (Gamma (verticalArgument x t))⁻¹) := by
  have h : Differentiable ℝ (verticalArgument x) := by
    change Differentiable ℝ (fun t : ℝ => (x : ℂ) + I * (t : ℂ))
    fun_prop
  simpa only [Function.comp_def, one_div] using
    (Complex.differentiable_one_div_Gamma.restrictScalars ℝ).comp h

/-- The reciprocal-Gamma secant slope from height zero extends continuously to zero. -/
private theorem continuous_dslope_vertical_invGamma (x : ℝ) :
    Continuous (dslope (fun t => (Gamma (verticalArgument x t))⁻¹) 0) := by
  have h := differentiable_vertical_invGamma x
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    exact continuousAt_dslope_same.mpr (h 0)
  · exact (continuousAt_dslope_of_ne ht).mpr h.continuous.continuousAt

/-- The extended secant slope through a simple reciprocal-Gamma zero never vanishes. -/
private theorem dslope_vertical_invGamma_neg_nat_ne_zero (k : ℕ) (t : ℝ) :
    dslope (fun s => (Gamma (verticalArgument (-(k : ℝ)) s))⁻¹) 0 t ≠ 0 := by
  by_cases ht : t = 0
  · subst t
    have h := Complex.hasDerivAt_inv_Gamma_neg_nat k
    have hArg : HasDerivAt (fun z : ℂ => -(k : ℂ) + I * z) I 0 := by
      simpa only [id_eq, mul_one] using
        (((hasDerivAt_id (0 : ℂ)).const_mul I).const_add (-(k : ℂ)))
    have hGamma : HasDerivAt (fun z : ℂ => (Gamma z)⁻¹)
        ((-1 : ℂ) ^ k * k.factorial) ((fun z : ℂ => -(k : ℂ) + I * z) 0) := by
      simpa only [mul_zero, add_zero] using h
    have hd := (hGamma.comp (0 : ℂ) hArg).comp_ofReal
    rw [dslope_same]
    have hderiv : deriv (fun s => (Gamma (verticalArgument (-(k : ℝ)) s))⁻¹) 0 =
        (-1 : ℂ) ^ k * k.factorial * I := by
      simpa only [verticalArgument, Function.comp_apply, ofReal_neg, ofReal_natCast, ofReal_zero]
        using hd.deriv
    rw [hderiv]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr k.factorial_ne_zero)) I_ne_zero
  · let f (s : ℝ) := (Gamma (verticalArgument (-(k : ℝ)) s))⁻¹
    have hf0 : f 0 = 0 := by
      simp only [f, verticalArgument, ofReal_neg, ofReal_natCast, ofReal_zero, mul_zero, add_zero,
        Gamma_neg_nat_eq_zero, inv_zero]
    intro hz
    have h := sub_smul_dslope_of_zero hf0 t
    rw [hz, smul_zero] at h
    exact inv_ne_zero (Gamma_vertical_ne_zero _ ht) h.symm

/-- A continuous majorant for the quotient when the numerator pole can cancel. -/
private theorem exists_continuous_norm_Gamma_ratio_majorant (x y : ℝ)
    (h : (∀ k : ℕ, x ≠ -(k : ℝ)) ∨ y = 0) :
    ∃ F : ℝ → ℂ, Continuous F ∧
      ∀ t, ‖Gamma (verticalArgument x t) / Gamma (verticalArgument y t)‖ ≤ ‖F t‖ := by
  -- At an exceptional numerator parameter, factor both reciprocal Gamma zeros by the height.
  by_cases hx : ∀ k : ℕ, x ≠ -(k : ℝ)
  · refine ⟨fun t => Gamma (verticalArgument x t) / Gamma (verticalArgument y t), ?_,
      fun _ => le_rfl⟩
    simp only [div_eq_mul_inv]
    exact (continuous_iff_continuousAt.2
      (fun _ => continuousAt_Gamma_vertical (Or.inr hx))).mul
      (differentiable_vertical_invGamma y).continuous
  have hy : y = 0 := h.resolve_left hx
  push Not at hx
  obtain ⟨k, rfl⟩ := hx
  subst y
  let f (a t : ℝ) := (Gamma (verticalArgument a t))⁻¹
  let F (t : ℝ) := dslope (f 0) 0 t / dslope (f (-(k : ℝ))) 0 t
  have hF : Continuous F :=
    (continuous_dslope_vertical_invGamma 0).div (continuous_dslope_vertical_invGamma _)
      (dslope_vertical_invGamma_neg_nat_ne_zero k)
  have h0 (k : ℕ) : f (-(k : ℝ)) 0 = 0 := by
    simp only [f, verticalArgument, ofReal_neg, ofReal_natCast, ofReal_zero, mul_zero, add_zero,
      Gamma_neg_nat_eq_zero, inv_zero]
  have hzero : f 0 0 = 0 := by simpa only [Nat.cast_zero, neg_zero] using h0 0
  refine ⟨F, hF, fun t => ?_⟩
  by_cases ht : t = 0
  · subst t
    simp only [verticalArgument, ofReal_neg, ofReal_natCast, ofReal_zero, mul_zero, add_zero,
      Gamma_neg_nat_eq_zero, zero_div, norm_zero, norm_nonneg]
  · have hNum := sub_smul_dslope_of_zero hzero t
    have hDen := sub_smul_dslope_of_zero (h0 k) t
    simp only [sub_zero, Complex.real_smul] at hNum hDen
    have hEq : Gamma (verticalArgument (-(k : ℝ)) t) / Gamma (verticalArgument 0 t) =
        f 0 t / f (-(k : ℝ)) t := by
      simp only [f, div_eq_mul_inv, inv_inv, mul_comm]
    rw [hEq, ← hNum, ← hDen, mul_div_mul_left _ _ (ofReal_ne_zero.mpr ht)]

/-- The leading power of a Gamma quotient follows from vertical Stirling asymptotics. -/
private theorem tendsto_norm_Gamma_ratio_vertical (x y : ℝ) :
    Tendsto (fun t : ℝ => ‖Gamma (verticalArgument x t) / Gamma (verticalArgument y t)‖ /
      |t| ^ (x - y)) atTop (𝓝 1) := by
  have h := (DLMF.Gamma.tendsto_norm_Gamma_vertical_div x).div
    (DLMF.Gamma.tendsto_norm_Gamma_vertical_div y) (by norm_num : (1 : ℝ) ≠ 0)
  rw [div_self (by norm_num : (1 : ℝ) ≠ 0)] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hpow : |t| ^ (x - y) = |t| ^ (x - 1 / 2) / |t| ^ (y - 1 / 2) := by
    rw [← Real.rpow_sub (abs_pos.mpr ht.ne')]
    congr 1
    ring
  simp only [verticalArgument, norm_div, hpow, Pi.div_apply]
  field_simp [(Real.rpow_pos_of_pos (abs_pos.mpr ht.ne') (x - 1 / 2)).ne',
    (Real.rpow_pos_of_pos (abs_pos.mpr ht.ne') (y - 1 / 2)).ne',
    norm_ne_zero_iff.mpr (Gamma_vertical_ne_zero y ht.ne'), (Real.exp_pos _).ne',
    (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)).ne']

/-- A factor of at most two in the base gives a uniform power bound for either exponent sign. -/
private theorem rpow_le_rescaled (a b p : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hhalf : b ≤ 2 * a) :
    a ^ p ≤ (2 : ℝ) ^ |p| * b ^ p := by
  by_cases hp : 0 ≤ p
  · calc
      a ^ p ≤ b ^ p := Real.rpow_le_rpow ha.le hab hp
      _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg (ha.le.trans hab) _)
        (Real.one_le_rpow (by norm_num) (abs_nonneg _))
  · have hcompare : b / 2 ≤ a := by linarith
    have hpos : 0 < b := ha.trans_le hab
    calc
      a ^ p ≤ (b / 2) ^ p := Real.rpow_le_rpow_of_nonpos (by positivity) hcompare (le_of_not_ge hp)
      _ = _ := by
        rw [Real.div_rpow hpos.le (by norm_num), abs_of_neg (lt_of_not_ge hp),
          Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)), div_eq_mul_inv, mul_comm]

/-- Bounds at finite height and infinity combine into a global Gamma quotient estimate. -/
private theorem exists_norm_Gamma_ratio_vertical_le (x y : ℝ)
    (h : (∀ k : ℕ, x ≠ -(k : ℝ)) ∨ y = 0) :
    ∃ C > 0, ∀ t : ℝ, ‖Gamma (verticalArgument x t) / Gamma (verticalArgument y t)‖ ≤
      C * (1 + |t|) ^ (x - y) := by
  obtain ⟨F, hF, hmajor⟩ := exists_continuous_norm_Gamma_ratio_majorant x y h
  let p := x - y
  let ratio (t : ℝ) := ‖Gamma (verticalArgument x t) / Gamma (verticalArgument y t)‖
  have heven : Function.Even ratio := by
    intro t
    have hconj (a : ℝ) : verticalArgument a (-t) = conj (verticalArgument a t) := by
      simp only [verticalArgument, map_add, map_mul, conj_ofReal, conj_I, ofReal_neg]
      ring
    simp only [ratio, hconj, Gamma_conj, ← map_div₀, norm_conj]
  -- Use vertical Stirling at infinity and the continuous majorant on a compact interval.
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((tendsto_order.1 (tendsto_norm_Gamma_ratio_vertical x y)).2 2 one_lt_two)
  let T := max 1 R
  have hscale : Continuous (fun t : ℝ => ((1 + |t|) ^ p)) :=
    (continuous_const.add continuous_abs).rpow_const (fun t =>
      Or.inl (ne_of_gt (by positivity : 0 < 1 + |t|)))
  have hPos (t : ℝ) : 0 < (1 + |t|) ^ p := by positivity
  have hC : Continuous (fun t : ℝ => ‖F t‖ / (1 + |t|) ^ p) :=
    hF.norm.div hscale (fun t => (hPos t).ne')
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hC.continuousOn
  let B := max (2 * (2 : ℝ) ^ |p|) C
  have hB : 0 < B := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨B, hB, fun t => ?_⟩
  have hPosBound (t : ℝ) (ht : 0 ≤ t) : ratio t ≤ B * (1 + |t|) ^ p := by
    by_cases htT : t ≤ T
    · have hb := hC t ⟨ht, htT⟩
      have hnonneg : 0 ≤ ‖F t‖ / (1 + |t|) ^ p := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hb
      exact (hmajor t).trans (((div_le_iff₀ (hPos t)).mp hb).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (hPos t).le))
    · have htR : R ≤ t := (le_max_right _ _).trans (le_of_not_ge htT)
      have ht1 : 1 ≤ t := (le_max_left _ _).trans (le_of_not_ge htT)
      have ht' : 0 < t := zero_lt_one.trans_le ht1
      have htPow : 0 < |t| ^ p := Real.rpow_pos_of_pos (abs_pos.mpr ht'.ne') _
      have htBound : ratio t ≤ 2 * |t| ^ p := (div_le_iff₀ htPow).mp (hR t htR).le
      exact htBound.trans <| calc
        _ ≤ 2 * ((2 : ℝ) ^ |p| * (1 + |t|) ^ p) := mul_le_mul_of_nonneg_left
          (rpow_le_rescaled _ _ _ (abs_pos.mpr ht'.ne') (by linarith)
            (by rw [abs_of_nonneg ht]; linarith)) (by norm_num)
        _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hPos t).le
  by_cases ht : 0 ≤ t
  · exact hPosBound t ht
  · change ratio t ≤ _
    rw [← heven t, ← abs_neg t]
    exact hPosBound (-t) (neg_nonneg.mpr (le_of_not_ge ht))

/-- Estimate for the two Gamma quotients in the inverse Jacobi `c`-function. -/
private theorem exists_norm_Gamma_pair_ratio_le (x y : ℝ) (hy : 0 < x + y) :
    ∃ C > 0, ∀ t : ℝ,
      ‖(Gamma (verticalArgument x t) * Gamma (verticalArgument y t)) /
        (Gamma (verticalArgument 0 t) * Gamma (verticalArgument (1 / 2) t))‖ ≤
        C * (1 + |t|) ^ (x + y - 1 / 2) := by
  wlog hx : 0 < x generalizing x y
  · obtain ⟨C, hC, h⟩ := this y x (by linarith) (by linarith)
    refine ⟨C, hC, fun t => ?_⟩
    simpa only [mul_comm (Gamma (verticalArgument y t)), add_comm y x] using h t
  obtain ⟨C, hC, h⟩ := exists_norm_Gamma_ratio_vertical_le x (1 / 2) (Or.inl fun k hk => by
    linarith [Nat.cast_nonneg (α := ℝ) k])
  obtain ⟨D, hD, h'⟩ := exists_norm_Gamma_ratio_vertical_le y 0 (Or.inr rfl)
  refine ⟨C * D, mul_pos hC hD, fun t => ?_⟩
  rw [mul_comm (Gamma (verticalArgument 0 t)), ← div_mul_div_comm, norm_mul]
  calc
    _ ≤ (C * (1 + |t|) ^ (x - 1 / 2)) * (D * (1 + |t|) ^ (y - 0)) :=
      mul_le_mul (h t) (h' t) (norm_nonneg _) (by positivity)
    _ = _ := by
      have hp : (1 + |t|) ^ (x - 1 / 2) * (1 + |t|) ^ (y - 0) =
          (1 + |t|) ^ (x + y - 1 / 2) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        ring
      rw [← hp]
      ring

/-- Legendre duplication expresses the inverse `c`-function as two vertical Gamma quotients. -/
private theorem cFunction_inv_eq_Gamma_pair_ratio (α β lam : ℝ) :
    let x := (α + β + 1) / 2
    let y := (α - β + 1) / 2
    let t := lam / 2
    let C := (2 : ℂ) ^ (1 - ((α : ℂ) + β + 1)) * (Real.sqrt π : ℂ) / Gamma ((α : ℂ) + 1)
    (cFunction α β lam)⁻¹ =
      C * ((Gamma (verticalArgument x t) * Gamma (verticalArgument y t)) /
        (Gamma (verticalArgument 0 t) * Gamma (verticalArgument (1 / 2) t))) := by
  let x := (α + β + 1) / 2
  let y := (α - β + 1) / 2
  let h := I * (lam : ℂ)
  let r := (α : ℂ) + β + 1
  let t := lam / 2
  let z := I * (t : ℂ)
  have hz : 2 * z = h := by
    dsimp only [h, z, t]
    push_cast
    ring
  have hg₀ : verticalArgument 0 t = z := by simp [verticalArgument, z]
  have hg₁ : verticalArgument (1 / 2) t = z + 1 / 2 := by
    push_cast [verticalArgument]
    abel
  have hGa : (h + r) / 2 = verticalArgument x t := by
    dsimp only [h, r, x, t, verticalArgument]
    push_cast
    ring
  have hGb : (h + α - β + 1) / 2 = verticalArgument y t := by
    dsimp only [h, y, t, verticalArgument]
    push_cast
    ring
  let D := (2 : ℂ) ^ (1 - h) * (Real.sqrt π : ℂ)
  have hD : D ≠ 0 := mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl two_ne_zero))
    (ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')
  have hDup : Gamma z * Gamma (z + 1 / 2) = Gamma h * D := by
    simpa only [D, hz, mul_assoc] using Gamma_mul_Gamma_add_half z
  have hgInv : (Gamma h)⁻¹ = D * (Gamma z * Gamma (z + 1 / 2))⁻¹ := by
    rw [hDup, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hD, one_mul]
  have hpow : (2 : ℂ) ^ (1 - h) * ((2 : ℂ) ^ (r - h))⁻¹ = (2 : ℂ) ^ (1 - r) := by
    rw [← cpow_neg, ← cpow_add _ _ two_ne_zero]
    congr 1
    ring
  dsimp only
  change (cFunction α β lam)⁻¹ = ((2 : ℂ) ^ (1 - r) * (Real.sqrt π : ℂ) /
    Gamma ((α : ℂ) + 1)) * ((Gamma (verticalArgument x t) * Gamma (verticalArgument y t)) /
      (Gamma (verticalArgument 0 t) * Gamma (verticalArgument (1 / 2) t)))
  rw [hg₀, hg₁, cFunction_def, inv_div]
  change _ / ((2 : ℂ) ^ (r - h) * Gamma ((α : ℂ) + 1) * Gamma h) = _
  rw [hGa, hGb]
  simp only [div_eq_mul_inv, mul_inv_rev, hgInv, D]
  rw [← hpow]
  ring

end JacobiDensity

set_option maxHeartbeats 1200000 in
/-- **Polynomial growth of the Plancherel density**: for real `α > −1`,
`|c(λ)|⁻² ≤ C (1 + |λ|)^{2α + 1}` on the real line. -/
theorem norm_cFunction_inv_sq_le (α β : ℝ) (hα : -1 < α) :
    ∃ C, ∀ lam : ℝ, ‖cFunction α β lam‖⁻¹ ^ 2 ≤ C * (1 + |lam|) ^ (2 * α + 1) := by
  let x := (α + β + 1) / 2
  let y := (α - β + 1) / 2
  let p := α + 1 / 2
  let C := (2 : ℂ) ^ (1 - ((α : ℂ) + β + 1)) * (Real.sqrt π : ℂ) / Gamma ((α : ℂ) + 1)
  have hp : x + y - 1 / 2 = p := by dsimp only [x, y, p]; ring
  obtain ⟨B, hB, h⟩ := JacobiDensity.exists_norm_Gamma_pair_ratio_le x y (by dsimp [x, y]; linarith)
  refine ⟨(‖C‖ * B * (2 : ℝ) ^ |p|) ^ 2, fun lam => ?_⟩
  have hpos : 0 < 1 + |lam / 2| := by positivity
  have habs : |lam / 2| = |lam| / 2 := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbasic : ‖cFunction α β lam‖⁻¹ ≤ (‖C‖ * B * (2 : ℝ) ^ |p|) * (1 + |lam|) ^ p := by
    rw [← norm_inv, JacobiDensity.cFunction_inv_eq_Gamma_pair_ratio, norm_mul]
    have hi := h (lam / 2)
    rw [hp] at hi
    calc
      _ ≤ ‖C‖ * (B * (1 + |lam / 2|) ^ p) := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
      _ ≤ ‖C‖ * (B * ((2 : ℝ) ^ |p| * (1 + |lam|) ^ p)) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hB.le
        exact JacobiDensity.rpow_le_rescaled _ _ _ hpos (by rw [habs]; linarith [abs_nonneg lam])
          (by rw [habs]; linarith)
      _ = _ := by ring
  calc
    _ ≤ ((‖C‖ * B * (2 : ℝ) ^ |p|) * (1 + |lam|) ^ p) ^ 2 := by
      exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hbasic
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
      have hp₂ : p * (2 : ℝ) = 2 * α + 1 := by dsimp only [p]; ring
      rw [Nat.cast_ofNat, hp₂]

end SFVK.RankOne
