/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import SFVK.SU2.Basic.WignerSmallD
import DLMF.OrthogonalPolynomials.Limits
import SFVK.SU2.SpecialFunctions

/-!
# Contraction of `SO(3)` and `SO(n+1)` to the motion groups

As the radius of the sphere grows, the matrix elements of `SO(3)` tend to those of `M(2)` and
the zonal functions of `SO(n+1)` to those of `M(n)`: `d^l_{pq}(x/l) → J_{p-q}(x)` for the
Wigner functions `SFVK.SU2.wignerSmallD` of spin `l`, and
`l!/Γ(2p+l) C^p_l(cos(r/l)) → √π J_{p-1/2}(r) / ((2r)^{p-1/2} Γ(p))` for lean-DLMF's Gegenbauer
polynomials. Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2,
§9.3.4 (3)–(4), p. 51. Both contractions use lean-DLMF’s Mehler–Heine limit for scaled terminating
Gauss series. The Wigner limit uses the Jacobi form of the matrix element, and the
Gegenbauer normalization uses Mathlib’s Gamma duplication formula.
-/

public noncomputable section

open Complex Filter Topology DLMF.Bessel DLMF.Hypergeometric DLMF.OrthogonalPolynomials
open scoped Real

namespace SFVK.MotionGroups

namespace Contraction

/-- For a positive-real-part denominator, the regularized terminating series has a Bessel limit
under the Mehler–Heine scaling of its argument. -/
theorem tendsto_terminatingGauss (c b : ℂ) (hb : 0 < b.re)
    {d : ℕ → ℕ} (hd : Tendsto d atTop atTop) {w : ℂ} {u : ℕ → ℂ}
    (hu : Tendsto u atTop (𝓝 w)) :
    Tendsto (fun l : ℕ => (Gamma b)⁻¹ *
      ordinaryHypergeometric (-(d l : ℂ)) (d l + c) b (u l / (d l : ℂ) ^ 2)) atTop
      (𝓝 (regularizedHGFun ∅ {b} (-w))) := by
  have h := (JacobiBesselLimit.tendsto_scaled_series c b w).comp
    (hd.prodMk hu)
  refine h.congr' ?_
  filter_upwards [hd.eventually (eventually_gt_atTop (0 : ℕ))] with l hn
  simp only [Function.comp_apply]
  generalize d l = n at hn ⊢
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [tsum_eq_sum (s := Finset.range (n + 1)), ordinaryHypergeometric_eq_sum_neg_nat,
    Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [DLMF.Bessel.regularizedHGFunCoeff_empty, gaussHypergeometricCoeff,
      Gamma_add_nat_eq_pochhammer_mul_Gamma hb k, div_pow]
    simp only [mul_inv_rev, div_eq_mul_inv]
    ring
  · intro k hk
    rw [pochhammer_neg_nat_eq_zero (by simpa [Finset.mem_range] using hk : n < k)]
    simp

/-- The scaled half-angle sine tends to half of the radius. -/
private theorem tendsto_natCast_mul_sin_half_angle (r : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.sin (r / n / 2)) atTop (𝓝 (r / 2)) := by
  have ht : Tendsto (fun n : ℕ => r / n / 2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := r) |>.div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))).div_const (2 : ℝ)
  have h := ((Real.continuous_sinc.tendsto 0).comp ht).const_mul (r / 2)
  simp only [Real.sinc_zero, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simp only [Function.comp_apply]
  have he : r / 2 = (r / (n : ℝ) / 2) * n := by field_simp
  rw [he, mul_comm (_ * _) (Real.sinc _), ← mul_assoc]
  by_cases hz : r / (n : ℝ) / 2 = 0
  · simp [hz]
  · rw [Real.sinc_of_ne_zero hz, div_mul_cancel₀ _ hz, mul_comm]

/-- The scaled cosine endpoint is the square of the corresponding scaled half-angle sine. -/
private theorem scaled_cosine_eq (n : ℕ) (v : ℝ) :
    (n : ℂ) ^ 2 * ((1 - (Real.cos v : ℂ)) / 2) =
      (((n : ℝ) * Real.sin (v / 2)) ^ 2 : ℝ) := by
  have h : (1 - Real.cos v) / 2 = Real.sin (v / 2) ^ 2 := by
    have hc := Real.cos_two_mul (v / 2)
    rw [show 2 * (v / 2) = v by ring] at hc
    nlinarith [Real.sin_sq_add_cos_sq (v / 2)]
  have hr := congrArg (fun t : ℝ => (n : ℝ) ^ 2 * t) h
  rw [← mul_pow] at hr
  exact_mod_cast hr

/-- The cosine endpoint after rescaling has limit `r² / 4`. -/
theorem tendsto_scaled_cosine (r : ℝ) :
    Tendsto (fun n : ℕ => (n : ℂ) ^ 2 * ((1 - (Real.cos (r / n) : ℂ)) / 2)) atTop
      (𝓝 ((r : ℂ) ^ 2 / 4)) := by
  have h := ((tendsto_natCast_mul_sin_half_angle r).pow 2).ofReal
  norm_num [ofReal_pow, ofReal_div, div_pow] at h
  refine h.congr fun n => ?_
  have he := scaled_cosine_eq n (r / n)
  push_cast at he ⊢
  exact he.symm

/-- The normalized ascending factorial has limit one as its starting point tends to infinity. -/
private theorem tendsto_factorial_normalization (a : ℕ) :
    Tendsto (fun n : ℕ => ((n + a).factorial : ℝ) / n.factorial / (n : ℝ) ^ a)
      atTop (𝓝 1) := by
  have hterm (j : ℕ) :
      Tendsto (fun n : ℕ => 1 + ((j + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := ((j + 1 : ℕ) : ℝ))).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [add_zero] using h.const_add (1 : ℝ)
  have h := tendsto_finsetProd (Finset.range a) (fun j _ => hterm j)
  simp only [Finset.prod_const, one_pow] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [← Nat.factorial_mul_ascFactorial, Nat.ascFactorial_eq_prod_range, Nat.cast_mul,
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Nat.cast_prod,
    show (n : ℝ) ^ a = ∏ _j ∈ Finset.range a, (n : ℝ) by simp,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast
  field_simp
  ring

/-- The factorial ratio in the Wigner–Jacobi prefactor tends to one. -/
private theorem tendsto_wigner_factorial_ratio (a b : ℕ) :
    Tendsto (fun n : ℕ => ((n.factorial * (n + a + b).factorial : ℕ) : ℝ) /
      ((n + a).factorial * (n + b).factorial : ℕ)) atTop (𝓝 1) := by
  have h := (tendsto_factorial_normalization (a + b)).div
    ((tendsto_factorial_normalization a).mul (tendsto_factorial_normalization b))
    (by norm_num)
  simp only [one_mul, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [Pi.div_apply, ← Nat.add_assoc, Nat.cast_mul, pow_add]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hnR]

/-- The sine factor absorbs the growth of the ascending factorial in the Jacobi prefactor. -/
private theorem tendsto_wigner_angular_factor (a : ℕ) {degree : ℕ → ℕ} {angle : ℕ → ℝ}
    {x : ℝ} (hd : Tendsto degree atTop atTop)
    (hangle : Tendsto (fun l => (degree l : ℝ) * Real.sin (angle l / 2)) atTop (𝓝 x)) :
    Tendsto (fun l => ((degree l + a).factorial : ℝ) / (degree l).factorial *
        Real.sin (angle l / 2) ^ a) atTop (𝓝 (x ^ a)) := by
  have h := ((tendsto_factorial_normalization a).comp hd).mul (hangle.pow a)
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [hd.eventually (eventually_gt_atTop (0 : ℕ))] with l hl
  have hdR : (degree l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
  simp only [Function.comp_apply, mul_pow, ← mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hdR)]

/-- The fixed offsets of the magnetic weights determine the two Jacobi indices and the degree
lost relative to the spin. -/
private theorem wigner_indices (p q : ℤ) (l : ℕ) (h : max p.natAbs q.natAbs ≤ l) :
    let i := ((l : ℤ) + p).toNat
    let j := ((l : ℤ) + q).toNat
    let r := min (min i j) (min (2 * l - i) (2 * l - j))
    i ≤ 2 * l ∧ j ≤ 2 * l ∧
      (l - max p.natAbs q.natAbs = r) ∧
      2 * l - r = r + (p - q).natAbs + (p + q).natAbs ∧
      ((i : ℤ) - j).natAbs = (p - q).natAbs ∧
      ((2 * l : ℕ) - (i : ℤ) - j).natAbs = (p + q).natAbs ∧
      j - i = (q - p).toNat := by
  dsimp only
  omega

/-- The limiting regularized series and the angular power in the contraction reproduce the
signed integer order of the Bessel function. -/
private theorem wigner_limit_eq_besselJ (p q : ℤ) (x : ℝ) :
    (-1 : ℂ) ^ (q - p).toNat * ((x : ℂ) / 2) ^ (p - q).natAbs *
        regularizedHGFun ∅ {((p - q).natAbs : ℂ) + 1} (-((x : ℂ) ^ 2 / 4)) =
      besselJ (p - q : ℤ) x := by
  set a := (p - q).natAbs with ha
  have he : ((x : ℂ) / 2) ^ a *
      regularizedHGFun ∅ {(a : ℂ) + 1} (-((x : ℂ) ^ 2 / 4)) = besselJ (a : ℕ) x := by
    rw [besselJ_eq_regularized, cpow_natCast]
  rw [mul_assoc, he]
  by_cases h : 0 ≤ p - q
  · have hz : (q - p).toNat = 0 := by omega
    have hi : (a : ℤ) = p - q := by omega
    rw [hz, pow_zero, one_mul, ← hi, Int.cast_natCast]
  · have hz : (q - p).toNat = a := by omega
    have hi : p - q = -(a : ℤ) := by omega
    rw [hi, Int.cast_neg, Complex.besselJ_neg_int, hz, zpow_natCast, Int.cast_natCast]

end Contraction

open Contraction in
/-- Contraction of Wigner's `d`-functions (Vilenkin–Klimyk Vol. 2 §9.3.4, p. 51): for fixed
`p, q ∈ ℤ` and real `x`, `d^l_{pq}(x/l) → J_{p-q}(x)` as `l → ∞`, with `d^l_{pq}` the
spin-`l` function `SFVK.SU2.wignerSmallD (2l) (l+p) (l+q)`. -/
theorem tendsto_wignerSmallD_besselJ (p q : ℤ) (x : ℝ) :
    Tendsto (fun l : ℕ =>
        (SFVK.SU2.wignerSmallD (2 * l) ((l : ℤ) + p).toNat ((l : ℤ) + q).toNat (x / l) : ℂ))
      atTop (𝓝 (besselJ (p - q : ℤ) x)) := by
  let a := (p - q).natAbs
  let b := (p + q).natAbs
  let offset := max p.natAbs q.natAbs
  let d (l : ℕ) := l - offset
  let angle (l : ℕ) : ℝ := x / l
  have hd : Tendsto d atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun k => ?_
    refine ⟨k + offset, fun l hl => ?_⟩
    dsimp only [d]
    omega
  have hangle : Tendsto angle atTop (𝓝 0) :=
    (tendsto_const_nhds (x := x)).div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hhalf := hangle.div_const 2
  simp only [zero_div] at hhalf
  have hlSin : Tendsto (fun l : ℕ => (l : ℝ) * Real.sin (angle l / 2)) atTop (𝓝 (x / 2)) :=
    tendsto_natCast_mul_sin_half_angle x
  have hdSin : Tendsto (fun l => (d l : ℝ) * Real.sin (angle l / 2)) atTop (𝓝 (x / 2)) := by
    have h := hlSin.sub (((Real.continuous_sin.tendsto 0).comp hhalf).const_mul (offset : ℝ))
    simp only [Real.sin_zero, mul_zero, sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop offset] with l hl
    simp [d, Function.comp_apply, Nat.cast_sub hl, sub_mul]
  have hcos := ((Real.continuous_cos.tendsto 0).comp hhalf).pow b
  simp only [Real.cos_zero, one_pow] at hcos
  let u (l : ℕ) := (d l : ℂ) ^ 2 * ((1 - (Real.cos (angle l) : ℂ)) / 2)
  have hu : Tendsto u atTop (𝓝 ((x : ℂ) ^ 2 / 4)) := by
    have h := (hdSin.pow 2).ofReal
    norm_num [ofReal_pow, ofReal_div, div_pow] at h
    refine h.congr fun l => ?_
    have he := scaled_cosine_eq (d l) (angle l)
    dsimp only [u]
    push_cast at he ⊢
    exact he.symm
  have hG := tendsto_terminatingGauss ((a : ℂ) + b + 1) (a + 1) (by simp; positivity) hd hu
  have hN := ((Real.continuous_sqrt.tendsto 1).comp
    ((tendsto_wigner_factorial_ratio a b).comp hd))
  simp only [Real.sqrt_one] at hN
  have hAng := tendsto_wigner_angular_factor a hd hdSin
  have hlim := (((hN.ofReal.mul hAng.ofReal).mul hcos.ofReal).mul hG).const_mul
    ((-1 : ℂ) ^ (q - p).toNat)
  simp only [ofReal_one, one_mul, mul_one, ofReal_pow, ofReal_div, ofReal_ofNat] at hlim
  rw [← mul_assoc, wigner_limit_eq_besselJ] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop offset,
    hd.eventually (eventually_gt_atTop (0 : ℕ))] with l hl hl'
  have hlC : (d l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl'.ne'
  obtain ⟨hi, hj, hdegree, hdegree', ha, hb, hdiff⟩ := wigner_indices p q l hl
  rw [SFVK.SU2.wignerSmallD_eq_jacobi _ _ _ hi hj]
  rw [← hdegree] at hdegree'
  rw [← hdegree, hdegree', ha, hb, hdiff]
  have harg : u l / (d l : ℂ) ^ 2 = (1 - (Real.cos (angle l) : ℂ)) / 2 := by
    dsimp only [u]
    field_simp [hlC]
  rw [harg, jacobiPolynomialP]
  have hparam : ((d l : ℂ) + a + b + 1) = d l + ((a : ℂ) + b + 1) := by ring
  have hnorm : pochhammer ((a : ℂ) + 1) (d l) =
      ((d l + a).factorial : ℂ) * (Gamma ((a : ℂ) + 1))⁻¹ := by
    have hg : 0 < ((a : ℂ) + 1).re := by simp; positivity
    have h := Gamma_add_nat_eq_pochhammer_mul_Gamma hg (d l)
    rw [show (a : ℂ) + 1 + d l = ((d l + a : ℕ) : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial] at h
    exact (eq_mul_inv_iff_mul_eq₀ (Gamma_ne_zero_of_re_pos hg)).2 h.symm
  rw [hnorm, hparam]
  dsimp only [Function.comp_apply, a, b, d, offset, angle]
  push_cast
  ring

/-- Contraction of zonal functions (Vilenkin–Klimyk Vol. 2 §9.3.4 (3), p. 51): for `Re p > 0`
and `r > 0`, `l!/Γ(2p+l) C^p_l(cos(r/l)) → √π / ((2r)^{p-1/2} Γ(p)) J_{p-1/2}(r)`. -/
theorem tendsto_ultrasphericalPolynomial_besselJ {p : ℂ} (hp : 0 < p.re) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun l : ℕ => (l.factorial : ℂ) / Complex.Gamma (2 * p + l) *
        DLMF.OrthogonalPolynomials.ultrasphericalPolynomial p l (Real.cos (r / l)))
      atTop (𝓝 (Real.sqrt π / ((2 * r : ℂ) ^ (p - 1 / 2) * Complex.Gamma p) *
        besselJ (p - 1 / 2) r)) := by
  let b := p + 1 / 2
  let a := p - 1 / 2
  have hb : 0 < b.re := by simp [b]; linarith
  have h2p : 0 < (2 * p).re := by simp [mul_re]; linarith
  have hG := Gamma_ne_zero_of_re_pos h2p
  have hGb := Gamma_ne_zero_of_re_pos hb
  have hGp := Gamma_ne_zero_of_re_pos hp
  let u (l : ℕ) := (l : ℂ) ^ 2 * ((1 - (Real.cos (r / l) : ℂ)) / 2)
  have hlim := (Contraction.tendsto_terminatingGauss (2 * p) b hb (d := id) tendsto_id
    (Contraction.tendsto_scaled_cosine r)).const_mul (Gamma b / Gamma (2 * p))
  have hr2 : (0 : ℝ) < r / 2 := by positivity
  have hrC : (r : ℂ) / 2 ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr hr.ne') (by norm_num)
  have harg : a + 1 = b := by dsimp [a, b]; ring
  have hprod : ((2 : ℂ) * r) ^ a = (2 : ℂ) ^ (2 * a) * ((r : ℂ) / 2) ^ a := by
    have h := Complex.mul_cpow_ofReal_nonneg (a := 4) (b := r / 2)
      (by norm_num) hr2.le a
    push_cast at h
    rw [show (4 : ℂ) * (r / 2) = 2 * r by ring] at h
    have hpow := cpow_mul_ofReal_nonneg (x := 2) (by norm_num) 2 a
    rw [Real.rpow_two] at hpow
    norm_num at hpow
    exact h.trans (congrArg (fun z : ℂ => z * ((r : ℂ) / 2) ^ a) hpow.symm)
  have hnormal : Gamma b / Gamma (2 * p) =
      Real.sqrt π / (((2 : ℂ) ^ (2 * a)) * Gamma p) := by
    have h := Gamma_mul_Gamma_add_half p
    rw [show 1 - 2 * p = -(2 * a) by dsimp [a]; ring, cpow_neg] at h
    have hpow : (2 : ℂ) ^ (2 * a) ≠ 0 :=
      cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
    change Gamma p * Gamma b = _ at h
    field_simp [hG, hGp, hpow] at h ⊢
    linear_combination h
  have hlimeq : Gamma b / Gamma (2 * p) * regularizedHGFun ∅ {b} (-((r : ℂ) ^ 2 / 4)) =
      Real.sqrt π / (((2 : ℂ) * r) ^ a * Gamma p) * besselJ a r := by
    rw [besselJ_eq_regularized, harg, hnormal, hprod]
    have hpow : ((r : ℂ) / 2) ^ a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hrC)
    field_simp [hpow]
  simp only [id_eq] at hlim
  rw [hlimeq] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with l hl
  have hlC : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
  have hf : (l.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr l.factorial_ne_zero
  have hg : pochhammer (2 * p) l ≠ 0 :=
    pochhammer_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos h2p) l
  rw [ultrasphericalPolynomial, Gamma_add_nat_eq_pochhammer_mul_Gamma h2p]
  have harg' : u l / (l : ℂ) ^ 2 = (1 - (Real.cos (r / l) : ℂ)) / 2 := by
    dsimp only [u]
    field_simp [hlC]
  rw [harg']
  field_simp [hG, hGb, hf, hg]
  congr 1
  dsimp only [b]
  ring

end SFVK.MotionGroups
