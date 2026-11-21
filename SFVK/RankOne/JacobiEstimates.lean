/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.RankOne.JacobiAsymptotics
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Estimates and integral formulas for Jacobi functions

The Jacobi functions with real parameters are bounded by `exp (|Im λ| |t|)` for
`α ≥ −1/2` and `α + β + 1 ≥ 0`. For `α ≥ β ≥ −1/2`, boundedness on the real line
is equivalent to `|Im λ| ≤ α + β + 1`. The file also records Koornwinder's
Laplace-type representation and product formula for `α > β > −1/2`.

Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2,
§11.4.6, (4)–(10), pp. 348–350.
-/

public noncomputable section

open Complex Filter Topology Set MeasureTheory DLMF.Hypergeometric DLMF.Legendre
open scoped ContDiff InnerProductSpace Real

namespace SFVK.RankOne

namespace Jacobi

/-- Bound the difference of the Jacobi spectral coefficient from a nonnegative real scalar by its
modulus and imaginary part. -/
private theorem norm_sub_jacobiSpectralValue_le (lam : ℂ) (ρ : ℝ) :
    ‖(‖lam ^ 2 + (ρ : ℂ) ^ 2‖ : ℂ) - (lam ^ 2 + (ρ : ℂ) ^ 2)‖ ≤
      2 * |lam.im| * √‖lam ^ 2 + (ρ : ℂ) ^ 2‖ := by
  let κ := lam ^ 2 + (ρ : ℂ) ^ 2
  let k := ‖κ‖
  change ‖(k : ℂ) - κ‖ ≤ 2 * |lam.im| * √k
  have hk : 0 ≤ k := norm_nonneg _
  have hre : κ.re = lam.re ^ 2 - lam.im ^ 2 + ρ ^ 2 := by
    simp only [κ, add_re, pow_two, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  have hbound : k ≤ lam.re ^ 2 + lam.im ^ 2 + ρ ^ 2 := by
    calc
      k ≤ ‖lam ^ 2‖ + ‖(ρ : ℂ) ^ 2‖ := norm_add_le _ _
      _ = _ := by
        rw [norm_pow, norm_pow, norm_real, Real.norm_eq_abs, sq_abs,
          ← normSq_eq_norm_sq, normSq_apply, pow_two, pow_two, pow_two]
  have hnorm : ‖(k : ℂ) - κ‖ ^ 2 = 2 * k * (k - κ.re) := by
    have h : κ.re * κ.re + κ.im * κ.im = k ^ 2 := by
      rw [← normSq_apply, normSq_eq_norm_sq]
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, zero_sub]
    linear_combination h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hnorm, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hk]
  rw [hre]
  have h : k - (lam.re ^ 2 - lam.im ^ 2 + ρ ^ 2) ≤ 2 * lam.im ^ 2 := by linarith
  calc
    _ ≤ 2 * k * (2 * lam.im ^ 2) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-- The imaginary part of the spectral parameter controls the cross term in the Jacobi energy. -/
private theorem realInner_mul_spectralDifference_le (lam : ℂ) (ρ : ℝ) (u v : ℂ) :
    let κ := lam ^ 2 + (ρ : ℂ) ^ 2
    let k := ‖κ‖
    ⟪v, ((k : ℂ) - κ) * u⟫_ℝ ≤ |lam.im| * (k * ‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  dsimp only
  let κ := lam ^ 2 + (ρ : ℂ) ^ 2
  let k := ‖κ‖
  let m := |lam.im|
  have hm : 0 ≤ m := abs_nonneg _
  let z := ((k : ℂ) - κ) * u
  change ⟪v, z⟫_ℝ ≤ m * (k * ‖u‖ ^ 2 + ‖v‖ ^ 2)
  calc
    _ ≤ ‖v‖ * ‖z‖ := real_inner_le_norm _ _
    _ = ‖v‖ * ‖(k : ℂ) - κ‖ * ‖u‖ := by rw [norm_mul]; ring
    _ ≤ ‖v‖ * (2 * m * √k) * ‖u‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Jacobi.norm_sub_jacobiSpectralValue_le lam ρ)
          (norm_nonneg _)) (norm_nonneg _)
    _ = m * (2 * (√k * ‖u‖) * ‖v‖) := by ring
    _ ≤ m * (k * ‖u‖ ^ 2 + ‖v‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hm
      have h := sq_nonneg (√k * ‖u‖ - ‖v‖)
      have hsquare : (√k * ‖u‖) ^ 2 = k * ‖u‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (norm_nonneg κ)]
      nlinarith only [h, hsquare]

/-- The damping coefficient of the real-radius Jacobi equation is nonnegative on the positive
half-line at `α ≥ −1/2` and `α + β + 1 ≥ 0`. -/
private theorem jacobi_damping_nonneg (α β : ℝ) (hα : -1 / 2 ≤ α)
    (hρ : 0 ≤ α + β + 1) {t : ℝ} (ht : 0 < t) :
    0 ≤ (2 * α + 1) * (Real.cosh t / Real.sinh t) + (2 * β + 1) * Real.tanh t := by
  have hsinh := Real.sinh_pos_iff.mpr ht
  have hcosh := Real.cosh_pos t
  have hratio : Real.cosh t / Real.sinh t - Real.tanh t =
      (Real.cosh t * Real.sinh t)⁻¹ := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
    exact Real.cosh_sq_sub_sinh_sq t
  calc
    _ ≤ (2 * α + 1) * (Real.cosh t / Real.sinh t - Real.tanh t) +
        (2 * (α + β + 1)) * Real.tanh t := by
      rw [hratio, Real.tanh_eq_sinh_div_cosh]
      exact add_nonneg (mul_nonneg (by linarith) (by positivity))
        (mul_nonneg (by positivity) (div_nonneg hsinh.le hcosh.le))
    _ = _ := by ring

end Jacobi

set_option maxHeartbeats 1400000 in
/-- The Jacobi function has spectral growth at most `exp (|Im λ| |t|)`. -/
theorem norm_jacobiFunction_le_exp (α β : ℝ) (hα : -1 / 2 ≤ α) (hρ : 0 ≤ α + β + 1)
    (lam : ℂ) (t : ℝ) :
    ‖jacobiFunction α β lam t‖ ≤ Real.exp (|lam.im| * |t|) := by
  let ρ := α + β + 1
  let κ := lam ^ 2 + (ρ : ℂ) ^ 2
  let k := ‖κ‖
  let m := |lam.im|
  have hreg : ∀ j : ℕ, (α : ℂ) + 1 ≠ -(j : ℂ) := by
    intro j hj
    have hr := congrArg Complex.re hj
    simp only [add_re, ofReal_re, one_re, neg_re, natCast_re] at hr
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hρ' : (ρ : ℂ) = (α : ℂ) + β + 1 := by simp [ρ]
  by_cases hk0 : κ = 0
  · have hfactor : (lam - I * ρ) * (lam + I * ρ) = κ := by
      dsimp only [κ]
      linear_combination -(ρ : ℂ) ^ 2 * Complex.I_sq
    have hon := jacobiFunction_I_mul_rho (α : ℂ) (β : ℂ) hreg t
    rw [← hρ'] at hon
    rw [hk0, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hfactor
    rcases hfactor with rfl | rfl
    · rw [hon, norm_one]
      exact Real.one_le_exp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · rw [jacobiFunction_neg_spectral, hon, norm_one]
      exact Real.one_le_exp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hk : 0 < k := norm_pos_iff.mpr hk0
  let u (s : ℝ) := jacobiFunction α β lam s
  have hu : ContDiff ℝ 2 u := contDiff_iff_contDiffAt.mpr
    (fun s => (analyticAt_jacobiFunction_radius α β lam s).contDiffAt)
  have huDiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hudDiff : Differentiable ℝ (deriv u) :=
    (ContDiff.deriv' (n := 1) hu).differentiable (by norm_num)
  have huZero : u 0 = 1 := jacobiFunction_zero α β lam hreg
  have hderivZero : deriv u 0 = 0 := by
    have hu0 : HasDerivAt u (deriv u 0) (-(0 : ℝ)) := by
      rw [neg_zero]
      exact (huDiff 0).hasDerivAt
    have hn : HasDerivAt (fun s : ℝ => -s) (-1) (0 : ℝ) := (hasDerivAt_id (0 : ℝ)).neg
    have h := hu0.scomp (0 : ℝ) hn
    simp only [Function.comp_def, neg_smul, one_smul] at h
    have hEven : (fun s : ℝ => u (-s)) = u :=
      funext fun s => jacobiFunction_even α β lam s
    rw [hEven] at h
    linear_combination (1 / 2 : ℂ) * h.deriv
  let damping (s : ℝ) :=
    (2 * α + 1) * (Real.cosh s / Real.sinh s) + (2 * β + 1) * Real.tanh s
  have hDamp (s : ℝ) (hs : 0 < s) : 0 ≤ damping s :=
    Jacobi.jacobi_damping_nonneg α β hα hρ hs
  have hODE (s : ℝ) (hs : 0 < s) :
      deriv (deriv u) s = -(k • u s) + ((k : ℂ) - κ) * u s - damping s • deriv u s := by
    have h : jacobiOperator (α : ℂ) (β : ℂ) u s = -κ * u s := by
      have hκ : κ = lam ^ 2 + ((α : ℂ) + β + 1) ^ 2 :=
        congrArg (fun z => lam ^ 2 + z ^ 2) hρ'
      rw [hκ]
      exact jacobiOperator_jacobiFunction α β lam hs
    rw [jacobiOperator_def] at h
    simp only [Complex.real_smul, damping, ofReal_mul, ofReal_add, ofReal_one,
      ofReal_ofNat]
    linear_combination h
  let E (s : ℝ) := k * ‖u s‖ ^ 2 + ‖deriv u s‖ ^ 2
  have hEDeriv (s : ℝ) :
      HasDerivAt E (k * (2 * ⟪u s, deriv u s⟫_ℝ) +
        2 * ⟪deriv u s, deriv (deriv u) s⟫_ℝ) s :=
    (((huDiff s).hasDerivAt.norm_sq).const_mul k).add ((hudDiff s).hasDerivAt.norm_sq)
  -- The real comparison coefficient cancels against the derivative of the norm term.
  have hE' (s : ℝ) (hs : 0 < s) : deriv E s ≤ 2 * m * E s := by
    let z := ((k : ℂ) - κ) * u s
    have hcross : ⟪deriv u s, z⟫_ℝ ≤ m * E s :=
      Jacobi.realInner_mul_spectralDifference_le lam ρ (u s) (deriv u s)
    rw [(hEDeriv s).deriv, hODE s hs, inner_sub_right, inner_add_right, inner_neg_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_comm (u s) (deriv u s)]
    have hpositive := mul_nonneg (hDamp s hs) (sq_nonneg ‖deriv u s‖)
    change k * (2 * ⟪u s, deriv u s⟫_ℝ) +
      2 * (-(k * ⟪u s, deriv u s⟫_ℝ) + ⟪deriv u s, z⟫_ℝ -
        damping s * ‖deriv u s‖ ^ 2) ≤ _
    linarith only [hpositive, hcross]
  let E₀ (s : ℝ) := Real.exp (-(2 * m) * s) * E s
  have hScale (s : ℝ) : HasDerivAt E₀
      (Real.exp (-(2 * m) * s) * (-(2 * m) * E s + deriv E s)) s := by
    have h := (((hasDerivAt_id s).const_mul (-(2 * m))).exp).mul (hEDeriv s)
    rw [← (hEDeriv s).deriv] at h
    refine h.congr_deriv ?_
    simp only [id_eq, mul_one]
    ring
  have hAnti : AntitoneOn E₀ (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact (continuous_iff_continuousAt.mpr (fun s => (hScale s).continuousAt)).continuousOn
    · exact fun s _ => (hScale s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hScale s).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (by linarith only [hE' s hs])
  have hAt (s : ℝ) (hs : 0 ≤ s) : ‖u s‖ ≤ Real.exp (m * s) := by
    have hle := hAnti (show (0 : ℝ) ∈ Ici 0 by simp) (show s ∈ Ici 0 from hs) hs
    have hEzero : E₀ 0 = k := by simp [E₀, E, huZero, hderivZero]
    rw [hEzero] at hle
    have hpos : k * ‖u s‖ ^ 2 ≤ E s := le_add_of_nonneg_right (sq_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hle (Real.exp_nonneg ((2 * m) * s))
    have heq : Real.exp ((2 * m) * s) * E₀ s = E s := by
      dsimp only [E₀]
      rw [← mul_assoc, ← Real.exp_add, show (2 * m) * s + -(2 * m) * s = 0 by ring, Real.exp_zero,
        one_mul]
    rw [heq] at hmul
    apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp
    apply (mul_le_mul_iff_of_pos_left hk).mp
    calc
      _ ≤ E s := hpos
      _ ≤ _ := hmul
      _ = _ := by rw [pow_two, ← Real.exp_add, mul_comm k]; congr 2; ring
  by_cases ht : 0 ≤ t
  · simpa only [u, abs_of_nonneg ht] using hAt t ht
  · have h := hAt (-t) (by linarith)
    simpa only [u, jacobiFunction_even, abs_of_nonpos (le_of_not_ge ht)] using h

/-- **The energy bound**: for real `λ`, real `α ≥ −1/2` and `α + β + 1 ≥ 0`,
`|φ_λ(t)| ≤ 1`. -/
theorem norm_jacobiFunction_le_one (α β lam : ℝ) (hα : -1 / 2 ≤ α) (hρ : 0 ≤ α + β + 1)
    (t : ℝ) :
    ‖jacobiFunction α β lam t‖ ≤ 1 := by
  simpa only [ofReal_im, abs_zero, zero_mul, Real.exp_zero] using
    norm_jacobiFunction_le_exp α β hα hρ lam t

/-- **Koornwinder's Laplace-type representation**, for real `α > β > −1/2`
(Vilenkin–Klimyk Vol. 2 §11.4.6, (5), p. 349). -/
theorem jacobiFunction_laplace (α β : ℝ) (hαβ : β < α) (hβ : -1 / 2 < β) (lam : ℂ) (t : ℝ) :
    jacobiFunction α β lam t =
      2 * Gamma (α + 1) / (Real.sqrt π * Gamma (α - β) * Gamma (β + 1 / 2)) *
        ∫ ψ in (0 : ℝ)..π, ∫ r in (0 : ℝ)..1,
          ((‖(Real.cosh t : ℂ) + r * exp (ψ * I) * Real.sinh t‖ : ℝ) : ℂ) ^
              (I * lam - (α + β + 1)) *
            (r ^ (2 * β + 1) * (1 - r ^ 2) ^ (α - β - 1) * Real.sin ψ ^ (2 * β) : ℝ) := by
  sorry

/-- **Bound by the imaginary part**, for real `α ≥ β ≥ −1/2`: `|φ_λ(t)| ≤ φ_{i Im λ}(t)`. -/
theorem norm_jacobiFunction_le (α β : ℝ) (hαβ : β ≤ α) (hβ : -1 / 2 ≤ β) (lam : ℂ) (t : ℝ) :
    ‖jacobiFunction α β lam t‖ ≤ (jacobiFunction α β (I * lam.im) t).re := by
  sorry

set_option maxHeartbeats 1400000 in
/-- **Bounded Jacobi functions**: for real `α ≥ β ≥ −1/2`, `φ_λ` is bounded on `[0, ∞)`
exactly when `|Im λ| ≤ ρ`. -/
theorem bddAbove_jacobiFunction_iff (α β : ℝ) (hαβ : β ≤ α) (hβ : -1 / 2 ≤ β) (lam : ℂ) :
    BddAbove (range fun t : ℝ => ‖jacobiFunction α β lam t‖) ↔ |lam.im| ≤ α + β + 1 := by
  have hρ : 0 ≤ α + β + 1 := by linarith
  wlog hIm : lam.im ≤ 0 generalizing lam
  · have h := this (-lam) (by rw [neg_im]; linarith)
    simpa only [jacobiFunction_neg_spectral, neg_im, abs_neg] using h
  rcases lt_or_eq_of_le hIm with hneg | hzero
  swap
  · have hreal : lam = (lam.re : ℂ) := Complex.ext (by simp) (by simp [hzero])
    refine iff_of_true ⟨1, ?_⟩ (by simpa [hzero] using hρ)
    rintro _ ⟨t, rfl⟩
    rw [hreal]
    exact norm_jacobiFunction_le_one α β lam.re (hβ.trans hαβ) hρ t
  let ρ := α + β + 1
  let q (t : ℝ) := jacobiFunction α β lam t * exp (((α : ℂ) + β + 1 - I * lam) * t)
  have hq : Tendsto q atTop (𝓝 (cFunction α β lam)) :=
    tendsto_jacobiFunction_mul_exp α β lam hneg
  have hNorm (t : ℝ) : ‖q t‖ =
      ‖jacobiFunction α β lam t‖ * Real.exp ((ρ + lam.im) * t) := by
    simp [q, ρ, norm_exp, mul_re, sub_re, add_re, one_re]
  rw [abs_of_nonpos hIm]
  change _ ↔ -lam.im ≤ ρ
  constructor
  · rintro ⟨C, hC⟩
    by_contra! hbad
    have hμ : ρ + lam.im < 0 := by linarith
    have ht : Tendsto (fun t : ℝ => C * Real.exp ((ρ + lam.im) * t)) atTop (𝓝 0) := by
      have h := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hμ)).const_mul C
      simpa only [Function.comp_def, id_eq, mul_zero] using h
    have hNormLim : Tendsto (fun t : ℝ => ‖q t‖) atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) (fun t => by
        rw [hNorm]
        exact mul_le_mul_of_nonneg_right (hC (mem_range_self t)) (Real.exp_nonneg _)) ht
    have hcZero : cFunction α β lam = 0 :=
      tendsto_nhds_unique hq (tendsto_zero_iff_norm_tendsto_zero.mpr hNormLim)
    have hαg : Gamma ((α : ℂ) + 1) ≠ 0 := by
      apply Gamma_ne_zero_of_re_pos
      simp only [add_re, ofReal_re, one_re]
      linarith
    have hGammaSpectral : Gamma (I * lam) ≠ 0 :=
      Gamma_ne_zero_of_re_pos (by rw [I_mul_re]; linarith)
    have hρg : Gamma ((I * lam + ((α : ℂ) + β + 1)) / 2) ≠ 0 := by
      apply Gamma_ne_zero_of_re_pos
      rw [div_ofNat_re]
      simp only [add_re, I_mul_re, ofReal_re, one_re]
      linarith
    have hdiffg : Gamma ((I * lam + α - β + 1) / 2) ≠ 0 := by
      apply Gamma_ne_zero_of_re_pos
      rw [div_ofNat_re]
      simp only [add_re, sub_re, I_mul_re, ofReal_re, one_re]
      linarith
    have hpow : (2 : ℂ) ^ ((α : ℂ) + β + 1 - I * lam) ≠ 0 := by
      exact cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
    apply (div_ne_zero (mul_ne_zero (mul_ne_zero hpow hαg) hGammaSpectral) (mul_ne_zero hρg hdiffg))
    exact hcZero
  · intro h
    have hμ : 0 ≤ ρ + lam.im := by linarith
    have hevt : ∀ᶠ t : ℝ in atTop, ‖q t‖ ≤ 1 + ‖cFunction α β lam‖ := by
      filter_upwards [Metric.tendsto_nhds.mp hq 1 zero_lt_one] with t ht
      rw [dist_eq_norm] at ht
      exact (norm_le_norm_sub_add (q t) (cFunction α β lam)).trans (add_le_add_left ht.le _)
    obtain ⟨R, hR⟩ := eventually_atTop.mp hevt
    have hφ : Continuous (fun t : ℝ => jacobiFunction α β lam t) :=
      continuous_iff_continuousAt.mpr fun t =>
        (analyticAt_jacobiFunction_radius α β lam t).continuousAt
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max R 0)).exists_bound_of_continuousOn
      hφ.continuousOn
    refine ⟨max C (1 + ‖cFunction α β lam‖), ?_⟩
    have hPos (t : ℝ) (ht : 0 ≤ t) : ‖jacobiFunction α β lam t‖ ≤
        max C (1 + ‖cFunction α β lam‖) := by
      by_cases htR : max R 0 ≤ t
      · have hle := hR t ((le_max_left R (0 : ℝ)).trans htR)
        rw [hNorm] at hle
        exact (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg hμ ht))).trans
          (hle.trans (le_max_right _ _))
      · exact (hC t ⟨ht, le_of_not_ge htR⟩).trans (le_max_left _ _)
    rintro _ ⟨t, rfl⟩
    by_cases ht : 0 ≤ t
    · exact hPos t ht
    · simpa only [jacobiFunction_even] using hPos (-t) (by linarith)

/-- **Koornwinder's product formula**, for real `α > β > −1/2` (Vilenkin–Klimyk Vol. 2
§11.4.6, (4), p. 348). -/
theorem jacobiFunction_mul_jacobiFunction (α β : ℝ) (hαβ : β < α) (hβ : -1 / 2 < β) (lam : ℂ)
    (t₁ t₂ : ℝ) :
    jacobiFunction α β lam t₁ * jacobiFunction α β lam t₂ =
      2 * Gamma (α + 1) / (Real.sqrt π * Gamma (α - β) * Gamma (β + 1 / 2)) *
        ∫ ψ in (0 : ℝ)..π, ∫ r in (0 : ℝ)..1,
          jacobiFunction α β lam
              (Real.arcosh ‖(Real.cosh t₁ * Real.cosh t₂ : ℂ) +
                r * exp (ψ * I) * (Real.sinh t₁ * Real.sinh t₂)‖) *
            (r ^ (2 * β + 1) * (1 - r ^ 2) ^ (α - β - 1) * Real.sin ψ ^ (2 * β) : ℝ) := by
  sorry

end SFVK.RankOne
