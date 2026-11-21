/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import SFVK.MotionGroups.Basic.Group
public import SFVKMathlib.MeasureTheory.Group.GelfandPair

/-!
# The Hankel transform and the zonal Bessel functions

The Hankel (Fourier–Bessel) transform `(H_ν φ)(R) = ∫₀^∞ φ(r) J_ν(R r) r dr`, Vilenkin–Klimyk,
*Representation of Lie Groups and Special Functions*, Vol. 1, §4.4.2 (3), p. 196, and Vol. 2,
§10.2.6 (3)–(4), p. 186; the zonal Bessel function
`Ω_n(λ, r) = Γ(n/2) Σₖ (-λ²r²/4)^k / (k! Γ(k + n/2))`, which is
`Γ(n/2) (2/(λr))^{n/2-1} J_{n/2-1}(λr)` for `λr ≠ 0` (Vilenkin–Klimyk Vol. 2 §9.3.2 (8)–(10),
p. 48, for `ISO(n - 1)`); and the spherical functions `φ_λ(a, k) = Ω_n(λ, |a|)` of the pair
`(M(n), SO(n))` (Dieudonné, *Special Functions and Linear Representations of Lie Groups*, §16,
(193), p. 57, for `n = 2`), with the notions of bi-invariant and spherical function for a
subgroup.

## Main definitions

* `SFVK.MotionGroups.hankelTransform`, `besselZonal`, `motionSphericalFunction`.
-/

public noncomputable section

open Complex MeasureTheory Set

namespace SFVK.MotionGroups

/-- The Hankel transform of order `ν`, `(H_ν φ)(R) = ∫₀^∞ φ(r) J_ν(R r) r dr`. -/
@[expose]
def hankelTransform (ν : ℂ) (φ : ℝ → ℂ) (R : ℝ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), φ r * besselJ ν (R * r) * r

theorem hankelTransform_def (ν : ℂ) (φ : ℝ → ℂ) (R : ℝ) :
    hankelTransform ν φ R = ∫ r in Ioi (0 : ℝ), φ r * besselJ ν (R * r) * r :=
  rfl

/-- The zonal Bessel function `Ω_n(λ, r) = Γ(n/2) Σₖ (-λ²r²/4)^k / (k! Γ(k + n/2))`, entire in
`λ` and `r`. -/
@[expose]
def besselZonal (n : ℕ) (lam : ℂ) (r : ℝ) : ℂ :=
  Complex.Gamma (n / 2) *
    ∑' k : ℕ, (-(lam ^ 2) * r ^ 2 / 4) ^ k / ((k.factorial : ℂ) * Complex.Gamma (k + n / 2))

theorem besselZonal_def (n : ℕ) (lam : ℂ) (r : ℝ) :
    besselZonal n lam r =
      Complex.Gamma (n / 2) *
        ∑' k : ℕ, (-(lam ^ 2) * r ^ 2 / 4) ^ k /
          ((k.factorial : ℂ) * Complex.Gamma (k + n / 2)) :=
  rfl

/-- The spherical function `φ_λ(a, k) = Ω_n(λ, |a|)` of `(M(n), SO(n))`. -/
@[expose]
def motionSphericalFunction (n : ℕ) (lam : ℂ) (g : MotionGroup n) : ℂ := besselZonal n lam ‖g.a‖

theorem motionSphericalFunction_def (n : ℕ) (lam : ℂ) (g : MotionGroup n) :
    motionSphericalFunction n lam g = besselZonal n lam ‖g.a‖ :=
  rfl

end SFVK.MotionGroups
