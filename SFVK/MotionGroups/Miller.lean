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
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import SFVK.MotionGroups.CircleModel
import SFVKMathlib.Analysis.Fourier.AddCircle

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

open Complex MeasureTheory
open scoped Real

namespace SFVK.MotionGroups

/-- Index the pairs of natural numbers of a given signed difference by the smaller entry. -/
private def indexExponentialDiagonal (d : ℤ) :
    ℕ ≃ {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = d} :=
  Equiv.ofBijective (fun s => ⟨(s + d.toNat, s + (-d).toNat), by omega⟩) (by
    constructor
    · intro s t h
      have he := congrArg (fun p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = d} => p.val.1) h
      exact Nat.add_right_cancel he
    · intro p
      refine ⟨min p.val.1 p.val.2, Subtype.ext (Prod.ext ?_ ?_)⟩
      · have hd := p.property
        dsimp
        omega
      · have hd := p.property
        dsimp
        omega)

/-- The Laurent coefficient of integer index in the exponential product. -/
private def exponentialLaurentCoefficient (u v : ℂ) (d : ℤ) : ℂ :=
  ∑' j : ℕ, u ^ (j + d.toNat) * v ^ (j + (-d).toNat) /
    (((j + d.toNat).factorial : ℂ) * (j + (-d).toNat).factorial)

/-- Integer diagonals give the Laurent coefficients of the product of two exponentials. -/
private theorem hasSum_exponentialLaurent (u v : ℂ) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun d : ℤ => exponentialLaurentCoefficient u v d * z ^ d)
      (Complex.exp (u * z + v / z)) := by
  let a (n : ℕ) := (u * z) ^ n / (n.factorial : ℂ)
  let b (n : ℕ) := (v / z) ^ n / (n.factorial : ℂ)
  have ha : HasSum a (Complex.exp (u * z)) := by
    simpa only [a, Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (u * z)
  have hb : HasSum b (Complex.exp (v / z)) := by
    simpa only [b, Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (v / z)
  have hs : HasSum (fun p : ℕ × ℕ => a p.1 * b p.2) (Complex.exp (u * z + v / z)) := by
    rw [Complex.exp_add]
    exact ha.mul hb (summable_mul_of_summable_norm ha.summable.norm hb.summable.norm)
  let f (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - p.2
  refine (hs.tsum_fiberwise f).congr_fun fun d => ?_
  symm
  unfold exponentialLaurentCoefficient
  change (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = d}, a p.val.1 * b p.val.2) =
    (∑' s : ℕ, u ^ (s + d.toNat) * v ^ (s + (-d).toNat) /
      (((s + d.toNat).factorial : ℂ) * (s + (-d).toNat).factorial)) * z ^ d
  rw [← (indexExponentialDiagonal d).tsum_eq, ← tsum_mul_right]
  apply tsum_congr
  intro s
  let k := s + d.toNat
  let l := s + (-d).toNat
  change a k * b l = u ^ k * v ^ l / ((k.factorial : ℂ) * l.factorial) * z ^ d
  have hpow : z ^ k / z ^ l = z ^ d := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hz]
    congr 1
    dsimp [k, l]
    omega
  dsimp only [a, b]
  rw [mul_pow, div_pow, ← hpow]
  ring

/-- Generating function of the matrix elements (Miller (3.9), p. 55):
`exp(ω b z + ω c / z + (k + m₀) τ) = Σ_l A_{lk}(g) z^{l-k}` for `z ≠ 0`. -/
theorem hasSum_millerMatrix (ω m₀ : ℂ) (k : ℤ) (g : T3) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun l : ℤ => millerMatrix ω m₀ l k g * z ^ (l - k))
      (Complex.exp (ω * g.b * z + ω * g.c / z + (k + m₀) * g.τ)) := by
  have hs := (hasSum_exponentialLaurent (ω * g.b) (ω * g.c) hz).mul_left
    (Complex.exp ((k + m₀) * g.τ))
  rw [← Complex.exp_add] at hs
  have hs' := (Equiv.subRight k : ℤ ≃ ℤ).hasSum_iff.mpr hs
  convert hs' using 1
  · funext l
    simp only [Function.comp_apply, Equiv.subRight_apply, millerMatrix_def,
      exponentialLaurentCoefficient,
      show ∀ l : ℤ, -(l - k) = k - l by omega, mul_assoc]
  · congr 1
    ring

/-- Multiplying the Laurent variable scales its coefficient by the corresponding power. -/
private theorem exponentialLaurentCoefficient_scale (u v z : ℂ) (hz : z ≠ 0) (d : ℤ) :
    exponentialLaurentCoefficient (z * u) (z⁻¹ * v) d =
      exponentialLaurentCoefficient u v d * z ^ d := by
  unfold exponentialLaurentCoefficient
  rw [← tsum_mul_right]
  apply tsum_congr
  intro j
  have hp : z ^ (j + d.toNat) * (z⁻¹) ^ (j + (-d).toNat) = z ^ d := by
    rw [inv_pow, ← div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hz]
    congr 1
    omega
  rw [mul_pow, mul_pow, ← hp]
  ring

/-- The Fourier series of the exponential product on the circle. -/
private theorem hasSum_fourier_exponentialLaurent (u v : ℂ) (ψ : AddCircle (2 * π)) :
    HasSum (fun k : ℤ => fourier k ψ • exponentialLaurentCoefficient u v k)
      (Complex.exp (u * fourier 1 ψ + v / fourier 1 ψ)) := by
  let z : ℂ := fourier 1 ψ
  have hz : z ≠ 0 := Circle.coe_ne_zero _
  exact (hasSum_exponentialLaurent u v hz).congr_fun fun k => by
    rw [AddCircle.fourier_eq_zpow, smul_eq_mul, mul_comm]

/-- The Fourier series of a product has the convoluted coefficients. -/
private theorem hasSum_fourier_convolution {a b : ℤ → ℂ} {A B : AddCircle (2 * π) → ℂ}
    (ha : ∀ ψ, HasSum (fun k => fourier k ψ • a k) (A ψ))
    (hb : ∀ ψ, HasSum (fun k => fourier k ψ • b k) (B ψ)) (ψ : AddCircle (2 * π)) :
    HasSum (fun d : ℤ => fourier d ψ • (∑' j : ℤ, a (d - j) * b j)) (A ψ * B ψ) := by
  let f (k : ℤ) := fourier k ψ • a k
  let g (k : ℤ) := fourier k ψ • b k
  have hs : Summable (fun p : ℤ × ℤ => f p.1 * g p.2) :=
    summable_mul_of_summable_norm (ha ψ).summable.norm (hb ψ).summable.norm
  have h := (ha ψ).mul (hb ψ) hs
  refine (h.tsum_fiberwise (fun p : ℤ × ℤ => p.1 + p.2)).congr_fun fun d => ?_
  let e : ℤ ≃ {p : ℤ × ℤ // p.1 + p.2 = d} :=
    { toFun j := ⟨(d - j, j), by omega⟩
      invFun p := p.val.2
      left_inv j := rfl
      right_inv p := Subtype.ext (Prod.ext (by have := p.property; dsimp; omega) rfl) }
  symm
  change (∑' p : {p : ℤ × ℤ // p.1 + p.2 = d}, f p.val.1 * g p.val.2) =
    fourier d ψ • (∑' j : ℤ, a (d - j) * b j)
  rw [← e.tsum_eq, smul_eq_mul, ← tsum_mul_left]
  apply tsum_congr
  intro j
  change (fourier (d - j) ψ • a (d - j)) * (fourier j ψ • b j) =
    fourier d ψ * (a (d - j) * b j)
  rw [smul_eq_mul, smul_eq_mul,
    show fourier d ψ = (fourier (d - j) ψ) * fourier j ψ by
      rw [← fourier_add, sub_add_cancel]]
  ring

/-- The Laurent coefficients convolve under multiplication of the exponential products. -/
private theorem hasSum_exponentialLaurentCoefficient_add (u v u' v' : ℂ) (d : ℤ) :
    HasSum (fun j : ℤ =>
      exponentialLaurentCoefficient u v (d - j) * exponentialLaurentCoefficient u' v' j)
      (exponentialLaurentCoefficient (u + u') (v + v') d) := by
  let a := exponentialLaurentCoefficient u v
  let b := exponentialLaurentCoefficient u' v'
  let c := exponentialLaurentCoefficient (u + u') (v + v')
  let A (ψ : AddCircle (2 * π)) := Complex.exp (u * fourier 1 ψ + v / fourier 1 ψ)
  let B (ψ : AddCircle (2 * π)) := Complex.exp (u' * fourier 1 ψ + v' / fourier 1 ψ)
  have ha : ∀ ψ, HasSum (fun k => fourier k ψ • a k) (A ψ) :=
    hasSum_fourier_exponentialLaurent u v
  have hb : ∀ ψ, HasSum (fun k => fourier k ψ • b k) (B ψ) :=
    hasSum_fourier_exponentialLaurent u' v'
  have hc (ψ : AddCircle (2 * π)) : HasSum (fun k => fourier k ψ • c k) (A ψ * B ψ) := by
    have h := hasSum_fourier_exponentialLaurent (u + u') (v + v') ψ
    dsimp only [A, B]
    rw [← Complex.exp_add]
    convert h using 2
    rw [add_div]
    ring
  let : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  have heq : (∑' j : ℤ, a (d - j) * b j) = c d := by
    exact congrFun ((fourierCoeff_eq_of_hasSum (hasSum_fourier_convolution ha hb)).symm.trans
      (fourierCoeff_eq_of_hasSum hc)) d
  have han : Summable (‖a ·‖) := by simpa [a] using (ha 0).summable.norm
  have hbn : Summable (‖b ·‖) := by simpa [b] using (hb 0).summable.norm
  have hs : Summable (fun p : ℤ × ℤ => a p.1 * b p.2) :=
    summable_mul_of_summable_norm han hbn
  have hsum : Summable (fun j : ℤ => a (d - j) * b j) :=
    hs.comp_injective (i := fun j : ℤ => (d - j, j)) (fun _ _ h => congrArg Prod.snd h)
  change HasSum (fun j : ℤ => a (d - j) * b j) (c d)
  rw [← heq]
  exact hsum.hasSum

/-- Addition theorem for the matrix elements (Miller (3.10), p. 55). -/
theorem hasSum_millerMatrix_mul (ω m₀ : ℂ) (l k : ℤ) (g h : T3) :
    HasSum (fun j : ℤ => millerMatrix ω m₀ l j g * millerMatrix ω m₀ j k h)
      (millerMatrix ω m₀ l k (g * h)) := by
  let z := Complex.exp g.τ
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hs := hasSum_exponentialLaurentCoefficient_add (ω * g.b) (ω * g.c)
    (z * (ω * h.b)) (z⁻¹ * (ω * h.c)) (l - k)
  have hs' := (hs.mul_left (Complex.exp ((k + m₀) * (g * h).τ))).congr_fun
    (fun j => by rw [exponentialLaurentCoefficient_scale _ _ _ hz j])
  have ht := (Equiv.subRight k : ℤ ≃ ℤ).hasSum_iff.mpr hs'
  convert ht using 1
  · funext j
    simp only [Function.comp_apply, Equiv.subRight_apply]
    have hsub : l - k - (j - k) = l - j := by omega
    have hpow : z ^ (j - k) = Complex.exp (((j - k : ℤ) : ℂ) * g.τ) := by
      dsimp only [z]
      rw [Complex.exp_int_mul]
    rw [hsub, hpow, millerMatrix_def, millerMatrix_def]
    have hcoef (u v : ℂ) (a b : ℤ) :
        (∑' s : ℕ, u ^ (s + (a - b).toNat) * v ^ (s + (b - a).toNat) /
          (((s + (a - b).toNat).factorial : ℂ) * (s + (b - a).toNat).factorial)) =
            exponentialLaurentCoefficient u v (a - b) := by
      rw [exponentialLaurentCoefficient, show -(a - b) = b - a by omega]
    rw [hcoef, hcoef]
    have hphase : Complex.exp ((j + m₀) * g.τ) * Complex.exp ((k + m₀) * h.τ) =
        Complex.exp ((k + m₀) * (g * h).τ) * Complex.exp (((j - k : ℤ) : ℂ) * g.τ) := by
      rw [← Complex.exp_add, ← Complex.exp_add, T3.mul_τ]
      congr 1
      push_cast
      ring
    linear_combination (exponentialLaurentCoefficient (ω * g.b) (ω * g.c) (l - j) *
      exponentialLaurentCoefficient (ω * h.b) (ω * h.c) (j - k)) * hphase
  · have hb : ω * (g * h).b = ω * g.b + z * (ω * h.b) := by
      simp only [T3.mul_b, z]
      ring
    have hc : ω * (g * h).c = ω * g.c + z⁻¹ * (ω * h.c) := by
      simp only [T3.mul_c, z, Complex.exp_neg]
      ring
    rw [millerMatrix_def, hb, hc, exponentialLaurentCoefficient, show -(l - k) = k - l by omega]

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
