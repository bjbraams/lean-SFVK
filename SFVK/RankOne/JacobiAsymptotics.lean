/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.RankOne.JacobiIdentities
public import SFVK.RankOne.HarishChandra
public import SFVK.RankOne.JacobiDensity
import DLMF.Hypergeometric.Boundary
import DLMF.Hypergeometric.PrincipalConnections
import SFVKMathlib.Analysis.Complex.GaussCutPlane

/-!
# Harish-Chandra expansion and asymptotics of Jacobi functions

For `t > 0` and nonresonant `iλ`, the Jacobi function is the sum of two Harish-Chandra
solutions weighted by the `c`-function at `λ` and `−λ`. Their normalization at infinity
is `Φ_λ(t) e^{(ρ − iλ)t} → 1`, where `ρ = α + β + 1`. For `Im λ < 0`, the Jacobi
function in the same normalization tends to `c(λ)`.

Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2,
§11.4.6, (4)–(10), pp. 348–350.
-/

public noncomputable section

open Complex Filter Topology Set MeasureTheory DLMF.Hypergeometric DLMF.Legendre
open scoped ContDiff InnerProductSpace Real

namespace SFVK.RankOne

namespace Jacobi

/-- Exponential decay of the doubled radius. -/
private theorem tendsto_exp_neg_double :
    Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))

/-- Factor out the increasing exponential from the decaying one. -/
private theorem exp_neg_eq_mul_exp_neg_double (t : ℝ) :
    Real.exp (-t) = Real.exp t * Real.exp (-(2 * t)) := by
  rw [← Real.exp_add, show t + -(2 * t) = -t by ring]

/-- At infinity the exponential is asymptotic to twice the hyperbolic cosine. -/
private theorem tendsto_exp_div_cosh :
    Tendsto (fun t : ℝ => Real.exp t / Real.cosh t) atTop (𝓝 2) := by
  have h := (tendsto_const_nhds (x := (2 : ℝ))).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_exp_neg_double) (by norm_num)
  rw [add_zero, div_one] at h
  refine h.congr fun t => ?_
  simp only [Pi.div_apply]
  rw [Real.cosh_eq, exp_neg_eq_mul_exp_neg_double t]
  have hp : Real.exp t + Real.exp t * Real.exp (-(2 * t)) ≠ 0 := by positivity
  field_simp [hp, show 1 + Real.exp (-(2 * t)) ≠ 0 by positivity]

/-- The squared hyperbolic tangent approaches one from below. -/
private theorem tendsto_tanh_sq :
    Tendsto (fun t : ℝ => Real.tanh t ^ 2) atTop (𝓝[<] 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_exp_neg_double).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_exp_neg_double) (by norm_num)
  rw [sub_zero, add_zero, div_one] at h
  have htanh : Tendsto Real.tanh atTop (𝓝 1) := h.congr fun t => by
    simp only [Pi.div_apply]
    rw [Real.tanh_eq, exp_neg_eq_mul_exp_neg_double t]
    have hp : Real.exp t + Real.exp t * Real.exp (-(2 * t)) ≠ 0 := by positivity
    field_simp [hp, show 1 + Real.exp (-(2 * t)) ≠ 0 by positivity]
  exact tendsto_nhdsWithin_iff.mpr
    ⟨by simpa only [one_pow] using htanh.pow 2, Eventually.of_forall Real.tanh_sq_lt_one⟩

/-- Combine a power of a positive radius with the exponential. -/
private theorem ofReal_cpow_mul_exp_eq_div_cpow (r : ℝ) (hr : 0 < r) (t : ℝ) (w : ℂ) :
    (r : ℂ) ^ (-w) * Complex.exp (w * t) =
      ((Real.exp t / r : ℝ) : ℂ) ^ w := by
  rw [ofReal_cpow_eq_exp hr, ofReal_cpow_eq_exp (div_pos (Real.exp_pos _) hr),
    Real.log_div (Real.exp_ne_zero _) hr.ne', Real.log_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The squared hyperbolic cosine doubles the complex exponent. -/
private theorem ofReal_cosh_sq_cpow (t : ℝ) (w : ℂ) :
    ((Real.cosh t ^ 2 : ℝ) : ℂ) ^ w = (Real.cosh t : ℂ) ^ (2 * w) := by
  rw [ofReal_cpow_eq_exp (by positivity : 0 < Real.cosh t ^ 2),
    ofReal_cpow_eq_exp (Real.cosh_pos t), Real.log_pow]
  push_cast
  ring_nf

/-- The normalizing powers of two cancel in the Harish-Chandra term. -/
private theorem two_cpow_mul_cosh (t : ℝ) (w : ℂ) :
    (2 : ℂ) ^ (-w) * ((2 * Real.cosh t : ℝ) : ℂ) ^ w = (Real.cosh t : ℂ) ^ w := by
  have htwo : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
  rw [htwo, ofReal_cpow_eq_exp (by norm_num : (0 : ℝ) < 2),
    ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (Real.cosh_pos t),
    Real.log_mul (by norm_num) (Real.cosh_pos t).ne', ← exp_add]
  congr 1
  push_cast
  ring

/-- A product of the connection coefficient and a Harish-Chandra term,
in the hypergeometric normalization. -/
private theorem cFunction_mul_harishChandraSeries (α β lam : ℂ) (t : ℝ) :
    cFunction α β lam * harishChandraSeries α β lam t =
      (Real.cosh t : ℂ) ^ (I * lam - (α + β + 1)) * Gamma (α + 1) *
        ((Gamma (I * lam) * Gamma (1 - I * lam)) *
          regularizedGaussHypergeometric ((α + β + 1 - I * lam) / 2) ((α - β + 1 - I * lam) / 2)
            (1 - I * lam) ((Real.cosh t : ℂ) ^ 2)⁻¹ /
          (Gamma ((α + β + 1 + I * lam) / 2) * Gamma ((α - β + 1 + I * lam) / 2))) := by
  rw [cFunction_def, harishChandraSeries_def]
  have h1 : (I * lam + (α + β + 1)) / 2 = (α + β + 1 + I * lam) / 2 := by ring
  have h2 : (I * lam + α - β + 1) / 2 = (α - β + 1 + I * lam) / 2 := by ring
  rw [h1, h2]
  have hpow := two_cpow_mul_cosh t (I * lam - (α + β + 1))
  rw [neg_sub] at hpow
  rw [← hpow]
  ring

/-- The argument complementary to the Jacobi Gauss argument. -/
private theorem one_sub_neg_sinh_sq_eq_cosh_sq (t : ℝ) :
    (1 : ℂ) - -(Complex.sinh t) ^ 2 = ((Real.cosh t ^ 2 : ℝ) : ℂ) := by
  rw [Real.cosh_sq', ofReal_add, ofReal_one, ofReal_pow, ofReal_sinh, sub_neg_eq_add]

/-- The argument obtained after the Pfaff transformation. -/
private theorem neg_sinh_sq_div_sub_one_eq_tanh_sq (t : ℝ) :
    (-(Complex.sinh t) ^ 2) / (-(Complex.sinh t) ^ 2 - 1) = ((Real.tanh t ^ 2 : ℝ) : ℂ) := by
  rw [show -(Complex.sinh t) ^ 2 - 1 = -(1 - -(Complex.sinh t) ^ 2) by ring,
    one_sub_neg_sinh_sq_eq_cosh_sq, neg_div_neg_eq, Real.tanh_eq_sinh_div_cosh, div_pow, ofReal_div]
  simp only [ofReal_pow, ofReal_sinh]

end Jacobi

/-- **Leading behaviour of `Φ_λ`**: `Φ_λ(t) e^{(ρ − iλ)t} → 1`. -/
theorem tendsto_harishChandraSeries (α β lam : ℂ) (hlam : ∀ k : ℕ, I * lam ≠ k + 1) :
    Tendsto (fun t : ℝ => harishChandraSeries α β lam t * exp ((α + β + 1 - I * lam) * t))
      atTop (𝓝 1) := by
  let w := α + β + 1 - I * lam
  let a := w / 2
  let b := (α - β + 1 - I * lam) / 2
  let c := 1 - I * lam
  have hc : ∀ k : ℕ, c ≠ -(k : ℂ) := by
    intro k hk
    apply hlam k
    dsimp only [c] at hk
    linear_combination -hk
  have hcosh : Tendsto (fun t : ℝ => ((Real.cosh t : ℂ) ^ 2)⁻¹) atTop (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ => (Real.cosh t)⁻¹) atTop (𝓝 0) := by
      have h := Jacobi.tendsto_exp_div_cosh.mul Real.tendsto_exp_neg_atTop_nhds_zero
      rw [mul_zero] at h
      refine h.congr fun t => ?_
      rw [Real.exp_neg]
      field_simp
    have h := hinv.ofReal.pow (n := 2)
    simpa only [ofReal_zero, zero_pow two_ne_zero, ofReal_inv, inv_pow] using h
  have harg : (0 : ℂ) ∈ cutPlane := mem_cutPlane_of_norm_lt_one (by simp)
  have hGauss := (analyticAt_regularizedGaussHypergeometric a b c harg).continuousAt.tendsto.comp
    hcosh
  have hratio : Tendsto (fun t : ℝ => ((Real.exp t / (2 * Real.cosh t) : ℝ) : ℂ) ^ w)
      atTop (𝓝 1) := by
    have h := Jacobi.tendsto_exp_div_cosh.div_const 2
    rw [div_self (by norm_num : (2 : ℝ) ≠ 0)] at h
    have hr : Tendsto (fun t : ℝ => (Real.exp t / (2 * Real.cosh t) : ℝ)) atTop (𝓝 1) :=
      h.congr fun t => by ring_nf
    have hp := (continuousAt_cpow_const (b := w) (a := 1) (by simp)).tendsto.comp hr.ofReal
    rw [one_cpow] at hp
    exact hp
  have h := hratio.mul (hGauss.const_mul (Gamma c))
  rw [regularizedGaussHypergeometric_zero, mul_inv_cancel₀ (Gamma_ne_zero hc), one_mul] at h
  refine h.congr fun t => ?_
  have hpow := Jacobi.ofReal_cpow_mul_exp_eq_div_cpow (2 * Real.cosh t) (by positivity) t w
  rw [← hpow, harishChandraSeries_def]
  simp only [Function.comp_apply, w, a, b, c]
  rw [neg_sub]
  ring

set_option maxHeartbeats 550000 in
/-- **The connection formula**: `φ_λ = c(λ) Φ_λ + c(−λ) Φ_{−λ}` on `t > 0`, for `iλ ∉ ℤ`. -/
theorem jacobiFunction_eq_cFunction (α β lam : ℂ)
    (hlam : ∀ k : ℤ, I * lam ≠ k) {t : ℝ} (ht : 0 < t) :
    jacobiFunction α β lam t =
      cFunction α β lam * harishChandraSeries α β lam t +
        cFunction α β (-lam) * harishChandraSeries α β (-lam) t := by
  let ρ := α + β + 1
  let x := I * lam
  let a := (ρ + x) / 2
  let b := (ρ - x) / 2
  let c := α + 1
  let p := (α - β + 1 - x) / 2
  let m := (α - β + 1 + x) / 2
  let z : ℂ := ((Real.tanh t ^ 2 : ℝ) : ℂ)
  let q : ℂ := ((Real.cosh t : ℂ) ^ 2)⁻¹
  let R : ℂ := Real.cosh t
  have hR : R ≠ 0 := ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
  have hz : z ∈ cutPlane := by
    apply mem_cutPlane_of_norm_lt_one
    dsimp only [z]
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Real.tanh_sq_lt_one t
  have hz' : 1 - z ∈ cutPlane := by
    rw [mem_cutPlane, sub_sub_cancel]
    apply ofReal_mem_slitPlane.mpr
    rw [Real.tanh_eq_sinh_div_cosh]
    exact sq_pos_of_pos (div_pos (Real.sinh_pos_iff.mpr ht) (Real.cosh_pos t))
  have hcomplexCosh : (Real.cosh t : ℂ) ^ 2 - (Real.sinh t : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq t
  have hq : 1 - z = q := by
    dsimp only [z, q]
    rw [Real.tanh_eq_sinh_div_cosh, div_pow, ofReal_div, ofReal_pow, ofReal_pow]
    rw [← one_div]
    have hne : (Real.cosh t : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hR
    apply (eq_div_iff hne).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hne]
    exact hcomplexCosh
  have hp : c - a = p := by dsimp only [c, a, p, ρ]; ring
  have hm : c - b = m := by dsimp only [c, b, m, ρ]; ring
  have ha : c - p = a := by dsimp only [c, p, a, ρ]; ring
  have hgap : c - b - p = x := by dsimp only [c, b, p, ρ]; ring
  have hcp : 1 + b + p - c = 1 - x := by rw [← hgap]; ring
  have hcm : 1 + c - b - p = 1 + x := by rw [← hgap]; ring
  have hpf := regularizedGaussHypergeometric_pfaff b a c (Complex.neg_sinh_sq_mem_gaussCutPlane t)
  have hpow : 2 * (-b) = x - ρ := by dsimp only [b]; ring
  rw [hp, Jacobi.one_sub_neg_sinh_sq_eq_cosh_sq, Jacobi.neg_sinh_sq_div_sub_one_eq_tanh_sq,
    Jacobi.ofReal_cosh_sq_cpow, hpow] at hpf
  have hJ : jacobiFunction α β lam t = Gamma c *
      (R ^ (x - ρ) * regularizedGaussHypergeometric b p c z) := by
    rw [jacobiFunction,
      regularizedGaussHypergeometric_symm a b c (Complex.neg_sinh_sq_mem_gaussCutPlane t), hpf]
  have hConn := regularizedGaussHypergeometric_eq_connection_one_sub b p c
    (by rw [hgap]; exact hlam) hz hz'
  rw [GaussConnection.atOne_def, hgap, hcp, hcm, hm, ha, hq,
    regularizedGaussHypergeometric_symm m a (1 + x) (hq ▸ hz')] at hConn
  have hG := Gamma_mul_Gamma_one_sub x
  have hGneg : Gamma (-x) * Gamma (1 + x) = -(Real.pi / Complex.sin (Real.pi * x)) := by
    simpa only [sub_neg_eq_add, mul_neg, sin_neg, div_neg] using Gamma_mul_Gamma_one_sub (-x)
  have hpowQ : q ^ x = R ^ (-2 * x) := by
    dsimp only [q, R]
    rw [← ofReal_pow, ← ofReal_inv, ofReal_cpow_eq_exp (by positivity),
      ofReal_cpow_eq_exp (Real.cosh_pos t), Real.log_inv, Real.log_pow]
    push_cast
    ring_nf
  have hpowPlusMinus : R ^ (x - ρ) * q ^ x = R ^ (-x - ρ) := by
    rw [hpowQ, ← cpow_add _ _ hR]
    congr 1
    ring
  rw [hJ, hConn, ← hG]
  have hpos := Jacobi.cFunction_mul_harishChandraSeries α β lam t
  have hneg := Jacobi.cFunction_mul_harishChandraSeries α β (-lam) t
  simp only [mul_neg, sub_neg_eq_add, ← sub_eq_add_neg] at hneg
  rw [hpos, hneg]
  -- Both coefficients are now the Gauss connection coefficients in the same normalization.
  dsimp only [p, m, q, a, b, c, ρ, R, x] at hpowPlusMinus hGneg ⊢
  rw [hGneg]
  -- Group the powers in the second term before using the combined exponent.
  calc
    _ =
        (Real.cosh t : ℂ) ^ (I * lam - (α + β + 1)) * Gamma (α + 1) *
          ((Gamma (I * lam) * Gamma (1 - I * lam)) *
            regularizedGaussHypergeometric ((α + β + 1 - I * lam) / 2)
              ((α - β + 1 - I * lam) / 2) (1 - I * lam) ((Real.cosh t : ℂ) ^ 2)⁻¹ /
              (Gamma ((α + β + 1 + I * lam) / 2) * Gamma ((α - β + 1 + I * lam) / 2))) -
        ((Real.cosh t : ℂ) ^ (I * lam - (α + β + 1)) * (((Real.cosh t : ℂ) ^ 2)⁻¹) ^ (I * lam)) *
          Gamma (α + 1) *
          ((Gamma (I * lam) * Gamma (1 - I * lam)) *
            regularizedGaussHypergeometric ((α + β + 1 + I * lam) / 2)
              ((α - β + 1 + I * lam) / 2) (1 + I * lam) ((Real.cosh t : ℂ) ^ 2)⁻¹ /
              (Gamma ((α + β + 1 - I * lam) / 2) * Gamma ((α - β + 1 - I * lam) / 2))) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
    _ = _ := by
      rw [hpowPlusMinus, ← hG]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- **Asymptotics**: for `Im λ < 0`, `φ_λ(t) e^{(ρ − iλ)t} → c(λ)`. -/
theorem tendsto_jacobiFunction_mul_exp (α β lam : ℂ)
    (hlam : lam.im < 0) :
    Tendsto (fun t : ℝ => jacobiFunction α β lam t * exp ((α + β + 1 - I * lam) * t))
      atTop (𝓝 (cFunction α β lam)) := by
  let w := α + β + 1 - I * lam
  let a := (α + β + 1 + I * lam) / 2
  let b := w / 2
  let c := α + 1
  have hgap : c - b - (c - a) = I * lam := by dsimp only [a, b, c, w]; ring
  have hca : c - b = (I * lam + α - β + 1) / 2 := by dsimp only [b, c, w]; ring
  have hGauss := (tendsto_regularizedGaussHypergeometric_left_one
    (a := b) (b := c - a) (c := c) (by rw [hgap, I_mul_re]; linarith)).comp
      Jacobi.tendsto_tanh_sq
  have hratio := (continuousAt_cpow_const (b := w) (a := (↑(2 : ℝ) : ℂ))
    (ofReal_mem_slitPlane.mpr (by norm_num))).tendsto.comp Jacobi.tendsto_exp_div_cosh.ofReal
  have h := hratio.mul (hGauss.const_mul (Gamma c))
  have hlim : ((↑(2 : ℝ) : ℂ) ^ w) *
      (Gamma c * (Gamma (c - b - (c - a)) / (Gamma (c - b) * Gamma (c - (c - a))))) =
      cFunction α β lam := by
    rw [hgap, hca, sub_sub_cancel, cFunction_def]
    simp only [a, w, c, ofReal_ofNat, div_eq_mul_inv]
    ring_nf
  rw [hlim] at h
  refine h.congr fun t => ?_
  have hpf := regularizedGaussHypergeometric_pfaff b a c (Complex.neg_sinh_sq_mem_gaussCutPlane t)
  have hw : 2 * -b = -w := by dsimp only [b]; ring
  rw [Jacobi.one_sub_neg_sinh_sq_eq_cosh_sq, Jacobi.neg_sinh_sq_div_sub_one_eq_tanh_sq,
    Jacobi.ofReal_cosh_sq_cpow, hw] at hpf
  have heq : jacobiFunction α β lam t =
      Gamma c * regularizedGaussHypergeometric a b c (-(Complex.sinh t) ^ 2) := rfl
  simp only [Function.comp_apply]
  rw [heq, regularizedGaussHypergeometric_symm a b c (Complex.neg_sinh_sq_mem_gaussCutPlane t), hpf,
    ← Jacobi.ofReal_cpow_mul_exp_eq_div_cpow (Real.cosh t) (Real.cosh_pos t) t w]
  ring

end SFVK.RankOne
