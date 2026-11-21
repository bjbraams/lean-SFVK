/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.PrincipalBranch
public import SFVK.RankOne.Basic.Jacobi

import DLMF.Hypergeometric.Basic.CutPlane
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Harish-Chandra series

The Harish-Chandra series of the Jacobi equation in the DLMF 15.9.14 normalization, using the
principal-branch regularized Gauss function and its differential equation from lean-DLMF.

## Main definitions

* `SFVK.RankOne.harishChandraSeries`.

## Main results

* `SFVK.RankOne.jacobiOperator_harishChandraSeries`.
-/

public noncomputable section

open Complex Filter Topology Set DLMF.Hypergeometric
open scoped Real

namespace SFVK.RankOne

/-- The Harish-Chandra series
`Φ_λ(t) = (2 cosh t)^{iλ − ρ} F((ρ − iλ)/2, (α − β + 1 − iλ)/2; 1 − iλ; cosh⁻² t)`
(DLMF 15.9.14), with `F = Γ(c) 𝐅`; junk for `iλ ∈ {1, 2, …}`. -/
@[expose]
def harishChandraSeries (α β lam : ℂ) (t : ℝ) : ℂ :=
  ((2 * Real.cosh t : ℝ) : ℂ) ^ (I * lam - (α + β + 1)) * Gamma (1 - I * lam) *
    regularizedGaussHypergeometric ((α + β + 1 - I * lam) / 2) ((α - β + 1 - I * lam) / 2)
      (1 - I * lam) ((Real.cosh t : ℂ) ^ 2)⁻¹

theorem harishChandraSeries_def (α β lam : ℂ) (t : ℝ) :
    harishChandraSeries α β lam t =
      ((2 * Real.cosh t : ℝ) : ℂ) ^ (I * lam - (α + β + 1)) * Gamma (1 - I * lam) *
        regularizedGaussHypergeometric ((α + β + 1 - I * lam) / 2) ((α - β + 1 - I * lam) / 2)
          (1 - I * lam) ((Real.cosh t : ℂ) ^ 2)⁻¹ :=
  rfl

namespace HarishChandra

private theorem hasDerivAt_cosh_inv_sq (s : ℝ) :
    HasDerivAt (fun t : ℝ => ((Complex.cosh t) ^ 2)⁻¹)
      (-2 * ((Complex.cosh s) ^ 2)⁻¹ * (Complex.sinh s / Complex.cosh s)) s := by
  have hc : Complex.cosh s ≠ 0 := by
    rw [← ofReal_cosh]
    exact ofReal_ne_zero.mpr (Real.cosh_pos s).ne'
  have h := (((Complex.hasDerivAt_cosh s).pow 2).inv (pow_ne_zero _ hc)).comp_ofReal
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
  field_simp [hc]

private theorem hasDerivAt_sinh_div_cosh (s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.sinh t / Complex.cosh t)
      ((Complex.cosh s ^ 2)⁻¹) s := by
  have hc : Complex.cosh s ≠ 0 := by
    rw [← ofReal_cosh]
    exact ofReal_ne_zero.mpr (Real.cosh_pos s).ne'
  have h := ((Complex.hasDerivAt_sinh s).div (Complex.hasDerivAt_cosh s) hc).comp_ofReal
  refine h.congr_deriv ?_
  simp only [← pow_two, Complex.cosh_sq_sub_sinh_sq, one_div]

private theorem hasDerivAt_prefactor (σ c : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => Gamma c * (2 * Complex.cosh t) ^ σ)
      (Gamma c * (2 * Complex.cosh s) ^ σ * (σ * (Complex.sinh s / Complex.cosh s))) s := by
  have hc : Complex.cosh s ≠ 0 := by
    rw [← ofReal_cosh]
    exact ofReal_ne_zero.mpr (Real.cosh_pos s).ne'
  have hslit : (2 : ℂ) * Complex.cosh s ∈ slitPlane := by
    rw [← ofReal_cosh, ← ofReal_ofNat, ← ofReal_mul]
    exact ofReal_mem_slitPlane.mpr (mul_pos two_pos (Real.cosh_pos s))
  have h := ((((Complex.hasDerivAt_cosh s).const_mul (2 : ℂ)).cpow_const
    (c := σ) hslit).const_mul (Gamma c)).comp_ofReal
  refine h.congr_deriv ?_
  rw [sub_eq_add_neg σ, cpow_add _ _ (mul_ne_zero (by norm_num) hc), cpow_neg_one]
  field_simp [hc]

private theorem inv_cosh_sq_mem_cutPlane {s : ℝ} (hs : 0 < s) :
    (Complex.cosh s ^ 2)⁻¹ ∈ cutPlane := by
  apply mem_cutPlane_of_norm_lt_one
  rw [← ofReal_cosh, ← ofReal_pow, ← ofReal_inv, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (Real.cosh s ^ 2)⁻¹)]
  apply inv_lt_one_of_one_lt₀
  rw [Real.cosh_sq]
  exact lt_add_of_pos_left _ (sq_pos_of_pos (Real.sinh_pos_iff.mpr hs))

private theorem hasDerivAt_gauss_inv_cosh_sq (a b c : ℂ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => regularizedGaussHypergeometric a b c ((Complex.cosh t ^ 2)⁻¹))
      ((a * b * regularizedGaussHypergeometric (a + 1) (b + 1) (c + 1)
        ((Complex.cosh s ^ 2)⁻¹)) *
        (-2 * ((Complex.cosh s ^ 2)⁻¹) * (Complex.sinh s / Complex.cosh s))) s := by
  let q (z : ℂ) := (Complex.cosh z ^ 2)⁻¹
  have hC : Complex.cosh s ≠ 0 := by
    rw [← ofReal_cosh]
    exact ofReal_ne_zero.mpr (Real.cosh_pos s).ne'
  have hQ : HasDerivAt q (-2 * ((Complex.cosh s ^ 2)⁻¹) *
      (Complex.sinh s / Complex.cosh s)) (s : ℂ) := by
    refine (((Complex.hasDerivAt_cosh s).pow 2).inv (pow_ne_zero _ hC)).congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
    field_simp [hC]
  have hy : q ↑s ∈ cutPlane := inv_cosh_sq_mem_cutPlane hs
  have hd := (differentiableAt_regularizedGaussHypergeometric a b c hy).hasDerivAt
  rw [deriv_regularizedGaussHypergeometric a b c hy] at hd
  exact (hd.comp (s : ℂ) hQ).comp_ofReal

end HarishChandra

set_option maxHeartbeats 1400000 in
set_option linter.unusedVariables false in
/-- **`Φ_λ` solves the Jacobi equation** on `t > 0` for `iλ ∉ {1, 2, …}`. -/
theorem jacobiOperator_harishChandraSeries (α β lam : ℂ) (hlam : ∀ k : ℕ, I * lam ≠ k + 1)
    {t : ℝ} (ht : 0 < t) :
    jacobiOperator α β (harishChandraSeries α β lam) t =
      -(lam ^ 2 + (α + β + 1) ^ 2) * harishChandraSeries α β lam t := by
  let ρ := α + β + 1
  let x := I * lam
  let σ := x - ρ
  let a := (ρ - x) / 2
  let b := (α - β + 1 - x) / 2
  let c := 1 - x
  let q (s : ℝ) := (Complex.cosh s ^ 2)⁻¹
  let d (s : ℝ) := Complex.sinh s / Complex.cosh s
  let p (s : ℝ) := Gamma c * (2 * Complex.cosh s) ^ σ
  let Z (s : ℝ) := -2 * q s * d s
  let W (s : ℝ) := -2 * (Z s * d s + q s * q s)
  let g (s : ℝ) := regularizedGaussHypergeometric a b c (q s)
  let g₁ (s : ℝ) := a * b * regularizedGaussHypergeometric (a + 1) (b + 1) (c + 1) (q s)
  let g₂ (s : ℝ) := pochhammer a 2 * pochhammer b 2 *
    regularizedGaussHypergeometric (a + 2) (b + 2) (c + 2) (q s)
  let A (s : ℝ) := σ * d s * g s + Z s * g₁ s
  have hp (s : ℝ) : HasDerivAt p (p s * (σ * d s)) s :=
    HarishChandra.hasDerivAt_prefactor σ c s
  have hg (s : ℝ) (hs : 0 < s) : HasDerivAt g (g₁ s * Z s) s :=
    HarishChandra.hasDerivAt_gauss_inv_cosh_sq a b c hs
  have hg₁ : HasDerivAt g₁ (g₂ t * Z t) t := by
    have h := (HarishChandra.hasDerivAt_gauss_inv_cosh_sq (a + 1) (b + 1) (c + 1) ht).const_mul
      (a * b)
    convert h using 1
    simp only [g₂, pochhammer_succ, pochhammer_zero, Nat.cast_one, Nat.cast_zero, add_zero, one_mul,
      Z, d, q]
    ring_nf
  have hZ : HasDerivAt Z (W t) t := by
    have h := (((HarishChandra.hasDerivAt_cosh_inv_sq t).mul
      (HarishChandra.hasDerivAt_sinh_div_cosh t)).const_mul (-2))
    simpa only [Z, W, q, d, Pi.mul_def, mul_assoc] using h
  have hA : HasDerivAt A (σ * (q t * g t + d t * (g₁ t * Z t)) +
      (W t * g₁ t + Z t * (g₂ t * Z t))) t := by
    have h := (((HarishChandra.hasDerivAt_sinh_div_cosh t).mul (hg t ht)).const_mul σ).add
      (hZ.mul hg₁)
    simpa only [A, d, Pi.add_def, Pi.mul_def, mul_assoc] using h
  have hΦ : harishChandraSeries α β lam = fun s => p s * g s := by
    funext s
    simp only [harishChandraSeries_def, ofReal_mul, ofReal_ofNat, ofReal_cosh]
    dsimp only [p, g, q, σ, ρ, x, a, b, c]
    ring
  have hFirst (s : ℝ) (hs : 0 < s) : HasDerivAt (harishChandraSeries α β lam)
      (p s * A s) s := by
    rw [hΦ]
    refine ((hp s).mul (hg s hs)).congr_deriv ?_
    dsimp only [A]
    ring
  have hFirstEq : deriv (harishChandraSeries α β lam) =ᶠ[𝓝 t] fun s => p s * A s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (hFirst s hs).deriv
  have hSecond : deriv (deriv (harishChandraSeries α β lam)) t =
      p t * (σ * d t * A t + σ * (q t * g t + d t * (g₁ t * Z t)) +
        (W t * g₁ t + Z t * (g₂ t * Z t))) := by
    rw [hFirstEq.deriv_eq]
    change deriv (p * A) t = _
    rw [((hp t).mul hA).deriv]
    ring
  let P := (2 * α + 1) * (Real.cosh t / Real.sinh t : ℝ) +
    (2 * β + 1) * (Real.tanh t : ℂ)
  let κ := lam ^ 2 + ρ ^ 2
  have hcosh : Complex.cosh t ≠ 0 := by
    rw [← ofReal_cosh]
    exact ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
  have hsinh : Complex.sinh t ≠ 0 := by
    rw [← ofReal_sinh]
    exact ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr ht).ne'
  have hq : d t ^ 2 = 1 - q t := by
    dsimp only [d, q]
    rw [div_pow]
    field_simp [hcosh]
    linear_combination -(Complex.cosh_sq_sub_sinh_sq ↑t)
  have hP : P * d t = 2 * α + 1 + (2 * β + 1) * (1 - q t) := by
    dsimp only [P]
    rw [Real.tanh_eq_sinh_div_cosh, ofReal_div, ofReal_div, ofReal_sinh, ofReal_cosh]
    have hco : (Complex.cosh t / Complex.sinh t) * d t = 1 := by
      dsimp only [d]
      field_simp [hcosh, hsinh]
    change ((2 * α + 1) * (Complex.cosh t / Complex.sinh t) +
      (2 * β + 1) * d t) * d t = _
    rw [add_mul, mul_assoc (2 * α + 1), hco, mul_one, mul_assoc (2 * β + 1), ← pow_two, hq]
  have hquadratic : Z t ^ 2 = 4 * q t * (q t * (1 - q t)) := by
    dsimp only [Z]
    rw [mul_pow, mul_pow, hq]
    ring
  have hlinear : W t + (2 * σ * d t + P) * Z t = 4 * q t * (c - (a + b + 1) * q t) := by
    calc
      _ = (-2 * q t) * ((2 * σ - 2) * d t ^ 2 + q t + P * d t) := by
        dsimp only [W, Z]
        ring
      _ = _ := by
        rw [hq, hP]
        dsimp only [σ, a, b, c, ρ, x]
        ring
  have hconstant : σ ^ 2 * d t ^ 2 + σ * q t + σ * (P * d t) + κ = -4 * q t * (a * b) := by
    rw [hq, hP]
    dsimp only [σ, a, b, c, κ, ρ, x]
    linear_combination lam ^ 2 * Complex.I_sq
  -- The three coefficients reduce the Jacobi equation to the Gauss equation.
  have heq : q t * (1 - q t) * g₂ t + (c - (a + b + 1) * q t) * g₁ t - a * b * g t = 0 :=
    regularizedGaussHypergeometric_ode a b c (HarishChandra.inv_cosh_sq_mem_cutPlane ht)
  rw [jacobiOperator_def, hSecond, (hFirst t ht).deriv, congrFun hΦ t]
  calc
    _ = p t * (Z t ^ 2 * g₂ t + (W t + (2 * σ * d t + P) * Z t) * g₁ t +
        (σ ^ 2 * d t ^ 2 + σ * q t + σ * (P * d t) + κ) * g t) -
        κ * (p t * g t) := by
      dsimp only [P, A, κ]
      ring
    _ = _ := by
      rw [hquadratic, hlinear, hconstant]
      linear_combination (p t * (4 * q t)) * heq

end SFVK.RankOne
