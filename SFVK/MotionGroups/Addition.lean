/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

import DLMF.Bessel.GrafAddition
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
is lean-DLMF's `DLMF.Bessel.hasSum_besselJ_graf`.
-/

public noncomputable section

open Complex
open scoped Real

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
  sorry

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
  sorry

end SFVK.MotionGroups
