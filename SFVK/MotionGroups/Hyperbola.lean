/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.KIntegralRep
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import SFVK.MotionGroups.Basic.Hyperbola
import Mathlib.MeasureTheory.Group.Integral

/-!
# The hyperbola model of `ISO(1,1)` and the Macdonald kernel

The operators of the hyperbola model form a representation; it has an `L²(ℝ)` realization
exactly for `Re R = 0`, and it is unitary there; in the two-sided Laplace realization the boosts
act diagonally and the translations by an integral kernel whose inner integral is
`2 K_{λ-a-it}(R r)`. Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*,
Vol. 1, §§4.2.1–4.2.4, pp. 171–176; DLMF 10.32.9 through lean-DLMF's
`DLMF.Bessel.besselK_eq_half_integral`.
-/

public noncomputable section

open Complex MeasureTheory
open scoped Real

namespace SFVK.MotionGroups

/-- Representation law of the hyperbola model. -/
theorem hyperbolaAction_mul (R : ℂ) (g h : ISO11) (Φ : ℝ → ℂ) :
    hyperbolaAction R (g * h) Φ = hyperbolaAction R g (hyperbolaAction R h Φ) := by
  funext θ
  have hshift : θ - (g.s + h.s) = θ - g.s - h.s := by ring
  have hpair : (g * h).a.1 * Real.cosh θ - (g * h).a.2 * Real.sinh θ =
      (g.a.1 * Real.cosh θ - g.a.2 * Real.sinh θ) +
        (h.a.1 * Real.cosh (θ - g.s) - h.a.2 * Real.sinh (θ - g.s)) := by
    simp only [ISO11.mul_a, Prod.fst_add, Prod.snd_add, lorentzBoost_def, Real.cosh_sub,
      Real.sinh_sub]
    ring
  simp only [hyperbolaAction_def, ISO11.mul_s, hshift, hpair,
    Complex.ofReal_add, mul_add, Complex.exp_add, mul_assoc]

/-- `L²` realization exactly on the imaginary axis (Vilenkin–Klimyk Vol. 1 §4.2.3, pp. 173–175). -/
theorem exists_hyperbolaRealization_iff (R : ℂ) :
    (∃ U, IsHyperbolaRealization R U) ↔ R.re = 0 := by
  sorry

/-- The hyperbola model is unitary on the imaginary axis. -/
theorem isUnitary_hyperbolaRep {R : ℂ} (hR : R.re = 0) : (hyperbolaRep R).IsUnitary := by
  sorry

/-- Boosts act diagonally in the Laplace realization (Vilenkin–Klimyk Vol. 1 §4.2.4 (3),
pp. 175–176). -/
theorem fourierLaplace_hyperbolaAction_boost (R : ℂ) (s : ℝ) (Φ : ℝ → ℂ) (hΦ : Continuous Φ)
    (hc : HasCompactSupport Φ) (lam : ℂ) :
    fourierLaplace (hyperbolaAction R ⟨0, s⟩ Φ) lam =
      Complex.exp (lam * s) * fourierLaplace Φ lam := by
  simp only [fourierLaplace_def, hyperbolaAction_def, Prod.fst_zero, Prod.snd_zero,
    zero_mul, sub_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  let kernel (θ : ℝ) := Φ (θ - s) * Complex.exp (lam * (θ : ℝ))
  calc
    _ = ∫ θ : ℝ, kernel (θ + s) := (integral_add_right_eq_self kernel s).symm
    _ = _ := by
      simp only [kernel, add_sub_cancel_right, Complex.ofReal_add, mul_add, Complex.exp_add]
      simp_rw [show ∀ θ : ℝ, Φ θ * (Complex.exp (lam * θ) * Complex.exp (lam * s)) =
        Complex.exp (lam * s) * (Φ θ * Complex.exp (lam * θ)) by intro; ring,
        integral_const_mul]

/-- Translations act by an integral kernel (Vilenkin–Klimyk Vol. 1 §4.2.4 (4)–(6),
pp. 175–176): for `Re R > 0`, `r > 0` and real `a`,
`F_g(λ) = (1/2π) ∫ (∫ e^{-R r cosh θ + (λ - a - it) θ} dθ) F(a + it) dt`. -/
theorem fourierLaplace_hyperbolaAction_translation {R : ℂ} (hR : 0 < R.re) {r : ℝ} (hr : 0 < r)
    (a : ℝ) (Φ : ℝ → ℂ) (hΦ : ContDiff ℝ ⊤ Φ) (hc : HasCompactSupport Φ) (lam : ℂ) :
    fourierLaplace (hyperbolaAction R ⟨(r, 0), 0⟩ Φ) lam =
      (2 * π)⁻¹ * ∫ t : ℝ,
        (∫ θ : ℝ, Complex.exp (-R * r * Real.cosh θ + (lam - (a + t * I)) * θ)) *
          fourierLaplace Φ (a + t * I) := by
  sorry

/-- The Macdonald kernel: for `Re z > 0`, `∫ e^{-z cosh θ + μθ} dθ = 2 K_μ(z)` (DLMF 10.32.9). -/
theorem integral_exp_cosh_eq_besselK (μ : ℂ) {z : ℂ} (hz : 0 < z.re) :
    ∫ θ : ℝ, Complex.exp (-z * Real.cosh θ + μ * θ) = 2 * DLMF.Bessel.besselK μ z := by
  rw [DLMF.Bessel.besselK_eq_half_integral μ hz]
  simp only [neg_mul]
  ring

end SFVK.MotionGroups
