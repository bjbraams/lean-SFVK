/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import SFVK.MotionGroups.Basic.Miller
import DLMF.Bessel.Basic.RegularizedSeries

/-!
# Miller's model of `T₃`: generating function, addition theorem and Bessel form

The matrix elements `A_{lk}` of Miller's multiplier representation of `T₃` have the generating
function `exp(ω b z + ω c / z + (k + m₀) τ) = Σ_l A_{lk}(g) z^{l-k}` and satisfy
`A(gh) = A(g) A(h)`; in the coordinates `b = r v / 2`, `c = -r / (2v)` they are
`e^{(m₀+k)τ} (-v)^{l-k} J_{l-k}(-ω r)`; and the multiplier representation on the functions
`tⁿ / Γ(m - n + 1)` gives Weisner's generating function. Miller, *Lie Theory and Special
Functions*, §3-1 (3.3)–(3.15), pp. 52–56, and §3-4 (3.33)–(3.38), pp. 63–65.
-/

public noncomputable section

open Complex

namespace SFVK.MotionGroups

/-- Generating function of the matrix elements (Miller (3.9), p. 55):
`exp(ω b z + ω c / z + (k + m₀) τ) = Σ_l A_{lk}(g) z^{l-k}` for `z ≠ 0`. -/
theorem hasSum_millerMatrix (ω m₀ : ℂ) (k : ℤ) (g : T3) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun l : ℤ => millerMatrix ω m₀ l k g * z ^ (l - k))
      (Complex.exp (ω * g.b * z + ω * g.c / z + (k + m₀) * g.τ)) := by
  sorry

/-- Addition theorem for the matrix elements (Miller (3.10), p. 55). -/
theorem hasSum_millerMatrix_mul (ω m₀ : ℂ) (l k : ℤ) (g h : T3) :
    HasSum (fun j : ℤ => millerMatrix ω m₀ l j g * millerMatrix ω m₀ j k h)
      (millerMatrix ω m₀ l k (g * h)) := by
  sorry

/-- An offset diagonal of two exponential series, in regularized form. -/
private theorem tsum_exp_diagonal (x y : ℂ) (n : ℕ) :
    (∑' s : ℕ, x ^ (s + n) * y ^ s / (((s + n).factorial : ℂ) * s.factorial)) =
      x ^ n * regularizedHGFun (∅ : Multiset ℂ) {(n : ℂ) + 1} (x * y) := by
  rw [DLMF.Bessel.regularized0F1_eq_tsum, ← tsum_mul_left]
  refine tsum_congr fun s => ?_
  have hΓ : Complex.Gamma ((n : ℂ) + 1 + s) = ((s + n).factorial : ℂ) := by
    rw [show (n : ℂ) + 1 + s = ((s + n : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
  rw [hΓ, mul_pow, pow_add]
  ring

/-- Bessel form of the matrix elements (Miller (3.13)–(3.14), p. 56): for `b = r v / 2`,
`c = -r / (2v)`, `A_{lk} = e^{(m₀+k)τ} (-v)^{l-k} J_{l-k}(-ω r)`. -/
theorem millerMatrix_eq_besselJ (ω m₀ : ℂ) (l k : ℤ) (r v τ : ℂ) (hv : v ≠ 0) :
    millerMatrix ω m₀ l k ⟨r * v / 2, -r / (2 * v), τ⟩ =
      Complex.exp ((m₀ + k) * τ) * (-v) ^ (l - k) * besselJ (l - k : ℤ) (-ω * r) := by
  rw [millerMatrix_def, add_comm (k : ℂ), mul_assoc]
  congr 1
  let x := ω * (r * v / 2)
  let y := ω * (-r / (2 * v))
  let z := -ω * r
  have hxy : x * y = -(z ^ 2 / 4) := by
    dsimp [x, y, z]
    field_simp
    ring
  change (∑' s : ℕ, x ^ (s + (l - k).toNat) * y ^ (s + (k - l).toNat) /
    (((s + (l - k).toNat).factorial : ℂ) * (s + (k - l).toNat).factorial)) =
    (-v) ^ (l - k) * besselJ (l - k : ℤ) z
  have hsub : k - l = -(l - k) := by omega
  rw [hsub]
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg (l - k)
  · rw [hn]
    simp only [Int.toNat_natCast, Int.toNat_neg_natCast, add_zero]
    rw [tsum_exp_diagonal, hxy, DLMF.Bessel.besselJ_eq_regularized, Int.cast_natCast,
      Complex.cpow_natCast, zpow_natCast]
    rw [show x = (-v) * (z / 2) by dsimp [x, z]; ring, mul_pow, mul_assoc]
  · rw [hn]
    simp only [neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, add_zero]
    have hswap :
        (∑' s : ℕ, x ^ s * y ^ (s + n) / ((s.factorial : ℂ) * (s + n).factorial)) =
          ∑' s : ℕ, y ^ (s + n) * x ^ s / (((s + n).factorial : ℂ) * s.factorial) := by
      apply tsum_congr
      intro s
      rw [mul_comm (x ^ s), mul_comm (s.factorial : ℂ)]
    rw [hswap]
    rw [tsum_exp_diagonal, mul_comm y x, hxy, Int.cast_neg, Complex.besselJ_neg_int,
      DLMF.Bessel.besselJ_eq_regularized, Int.cast_natCast, Complex.cpow_natCast,
      zpow_neg, zpow_natCast]
    have hy : y = (-v)⁻¹ * (-(1 : ℂ)) * (z / 2) := by
      dsimp [y, z]
      field_simp
    rw [hy, mul_pow, mul_pow, inv_pow, mul_assoc, mul_assoc, zpow_natCast]

/-- `E_m(u²) = u^{-m} J_m(u)` for `u` in the slit plane. -/
theorem besselJEntire_sq {m u : ℂ} (hu : u ∈ slitPlane) :
    besselJEntire m (u ^ 2) = u ^ (-m) * besselJ m u := by
  rw [besselJEntire_def, DLMF.Bessel.besselJ_eq_regularized, ← mul_assoc,
    DLMF.Bessel.regularized0F1_eq_tsum]
  have hu₀ : u ≠ 0 := slitPlane_ne_zero hu
  have harg : u.arg + ((2 : ℂ)⁻¹).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    have hzero : ((2 : ℂ)⁻¹).arg = 0 := by
      rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num]
      exact Complex.arg_ofReal_of_nonneg (by norm_num)
    rw [hzero, add_zero]
    exact ⟨Complex.neg_pi_lt_arg u, Complex.arg_le_pi u⟩
  have hargTwo : ((2 : ℂ).arg) ≠ Real.pi := by
    rw [show (2 : ℂ).arg = 0 from Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.pi_ne_zero.symm
  have hpow : (u / 2) ^ m = u ^ m * ((2 : ℂ)⁻¹) ^ m := by
    rw [div_eq_mul_inv, Complex.mul_cpow harg]
  rw [hpow, Complex.cpow_neg, ← mul_assoc,
    inv_mul_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hu₀)), one_mul,
    Complex.inv_cpow _ _ hargTwo, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [show -u ^ 2 / 4 = -(u ^ 2 / 4) by ring, show m + ↑k + 1 = m + 1 + k by ring]
  simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

/-- Weisner's generating function (Miller (3.38), p. 65): for `|x t| < 2`, `t ≠ 0`,
`Σₙ Jₙ(x) tⁿ / Γ(m - n + 1) = (2 + x t)^m E_m(x² + 2x/t)`. -/
theorem hasSum_besselJ_weisner (m x t : ℂ) (ht : t ≠ 0) (hxt : ‖x * t‖ < 2) :
    HasSum (fun n : ℤ => besselJ n x * t ^ n * (Complex.Gamma (m - n + 1))⁻¹)
      ((2 + x * t) ^ m * besselJEntire m (x ^ 2 + 2 * x / t)) := by
  sorry

end SFVK.MotionGroups
