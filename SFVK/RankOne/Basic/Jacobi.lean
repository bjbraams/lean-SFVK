/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Jacobi operator, the `c`-function and the Jacobi weight

The parts of the Jacobi analysis that do not involve the hypergeometric function: the Jacobi
operator `L = d²/dt² + ((2α + 1) coth t + (2β + 1) tanh t) d/dt`, the Harish-Chandra
`c`-function `c(λ) = 2^{ρ − iλ} Γ(α + 1) Γ(iλ) / (Γ((iλ + ρ)/2) Γ((iλ + α − β + 1)/2))` with
`ρ = α + β + 1`, the weight `Δ(t) = (2 sinh t)^{2α+1} (2 cosh t)^{2β+1}` and the measures
`Δ dt` on `(0, ∞)` and `(2π)⁻¹ |c(λ)|⁻² dλ` on `(0, ∞)`. The conventions are those of
Klimyk–Vilenkin, *Representations of Lie Groups and Special Functions* (Kirillov (ed.), EMS 59),
Part II Ch. 5 §2.4, (12)–(16), p. 233, and DLMF 15.9.12–15.9.13, with Koornwinder's `c`
normalized by `c(−iρ) = 1` (Klimyk–Vilenkin's `𝐜` is `2√π c / Γ(α + 1)`).

## Main definitions

* `SFVK.RankOne.jacobiOperator`: the Jacobi operator.
* `SFVK.RankOne.cFunction`: the `c`-function; junk where Mathlib's `Γ` has a pole.
* `SFVK.RankOne.jacobiWeight`, `SFVK.RankOne.jacobiMeasure`,
  `SFVK.RankOne.jacobiPlancherelMeasure`.

## Main results

* `SFVK.RankOne.cFunction_neg_I_mul_rho`: `c(−iρ) = 1`.
* `SFVK.RankOne.jacobiWeight_neg_half_neg_half`: the weight of the Fourier case is `1`.
* `SFVK.RankOne.jacobiOperator_const`: `L` kills constants.
-/

public noncomputable section

open Complex MeasureTheory Set
open scoped Real

namespace SFVK.RankOne

/-- The Jacobi operator `L u = u'' + ((2α + 1) coth t + (2β + 1) tanh t) u'`, the radial part of
the Laplacian of a rank-one symmetric space (Klimyk–Vilenkin, Part II Ch. 5 §2.4, p. 233). -/
@[expose]
def jacobiOperator (α β : ℂ) (u : ℝ → ℂ) (t : ℝ) : ℂ :=
  deriv (deriv u) t +
    ((2 * α + 1) * (Real.cosh t / Real.sinh t : ℝ) + (2 * β + 1) * (Real.tanh t : ℂ)) *
      deriv u t

/-- The Jacobi operator is the second derivative plus the first derivative with hyperbolic drift. -/
theorem jacobiOperator_def (α β : ℂ) (u : ℝ → ℂ) (t : ℝ) :
    jacobiOperator α β u t = deriv (deriv u) t +
      ((2 * α + 1) * (Real.cosh t / Real.sinh t : ℝ) + (2 * β + 1) * (Real.tanh t : ℂ)) *
        deriv u t :=
  rfl

/-- The Harish-Chandra `c`-function of the Jacobi analysis,
`c(λ) = 2^{ρ − iλ} Γ(α + 1) Γ(iλ) / (Γ((iλ + ρ)/2) Γ((iλ + α − β + 1)/2))`, `ρ = α + β + 1`
(Klimyk–Vilenkin, Part II Ch. 5 §2.4, (14), p. 233, divided by `2√π / Γ(α + 1)`; DLMF 15.9.13).
Mathlib's `Γ` is `0` at its poles, so the value is junk where `iλ ∈ {0, −1, −2, …}`. -/
@[expose]
def cFunction (α β lam : ℂ) : ℂ :=
  (2 : ℂ) ^ (α + β + 1 - I * lam) * Gamma (α + 1) * Gamma (I * lam) /
    (Gamma ((I * lam + (α + β + 1)) / 2) * Gamma ((I * lam + α - β + 1) / 2))

/-- The Jacobi `c`-function is the ratio of Gamma factors with its power-of-two constant. -/
theorem cFunction_def (α β lam : ℂ) :
    cFunction α β lam = (2 : ℂ) ^ (α + β + 1 - I * lam) * Gamma (α + 1) * Gamma (I * lam) /
      (Gamma ((I * lam + (α + β + 1)) / 2) * Gamma ((I * lam + α - β + 1) / 2)) :=
  rfl

/-- **Normalization of the `c`-function**: `c(−iρ) = 1` for `ρ ∉ {0, −1, −2, …}` and
`α + 1 ∉ {0, −1, −2, …}`. -/
theorem cFunction_neg_I_mul_rho (α β : ℂ) (hα : ∀ k : ℕ, α + 1 ≠ -k)
    (hρ : ∀ k : ℕ, α + β + 1 ≠ -k) :
    cFunction α β (-(I * (α + β + 1))) = 1 := by
  have hI : I * -(I * (α + β + 1)) = α + β + 1 := by
    rw [mul_neg, ← mul_assoc, I_mul_I]; ring
  have h1 : (α + β + 1 + (α + β + 1)) / 2 = α + β + 1 := by ring
  have h2 : (α + β + 1 + α - β + 1) / 2 = α + 1 := by ring
  have hgα : Gamma (α + 1) ≠ 0 := Gamma_ne_zero hα
  have hgρ : Gamma (α + β + 1) ≠ 0 := Gamma_ne_zero hρ
  rw [cFunction_def, hI, h1, h2, sub_self, cpow_zero, one_mul]
  field_simp

/-- The weight `Δ(t) = (2 sinh t)^{2α+1} (2 cosh t)^{2β+1}` of the Jacobi transform
(DLMF 15.9.12), for real `α`, `β` and `t > 0`. -/
@[expose]
def jacobiWeight (α β t : ℝ) : ℝ :=
  (2 * Real.sinh t) ^ (2 * α + 1) * (2 * Real.cosh t) ^ (2 * β + 1)

/-- The Jacobi weight is the product of the specified real powers of twice the hyperbolic sine and
cosine. -/
theorem jacobiWeight_def (α β t : ℝ) :
    jacobiWeight α β t = (2 * Real.sinh t) ^ (2 * α + 1) * (2 * Real.cosh t) ^ (2 * β + 1) :=
  rfl

/-- At `α = β = −1/2` the weight is `1` (the Fourier cosine case). -/
theorem jacobiWeight_neg_half_neg_half (t : ℝ) : jacobiWeight (-1 / 2) (-1 / 2) t = 1 := by
  norm_num [jacobiWeight_def]

/-- The measure `Δ(t) dt` on `(0, ∞)`. -/
@[expose]
def jacobiMeasure (α β : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (jacobiWeight α β t)

/-- The Jacobi measure on the positive half-line has density `jacobiWeight`. -/
theorem jacobiMeasure_def (α β : ℝ) :
    jacobiMeasure α β =
      (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (jacobiWeight α β t) :=
  rfl

/-- The Plancherel measure `(2π)⁻¹ |c(λ)|⁻² dλ` of the Jacobi transform on `(0, ∞)`. -/
@[expose]
def jacobiPlancherelMeasure (α β : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun lam : ℝ =>
    ENNReal.ofReal ((2 * π)⁻¹ * ‖cFunction α β lam‖⁻¹ ^ 2)

/-- The positive spectral half-line is weighted by the inverse squared norm of the Jacobi
`c`-function. -/
theorem jacobiPlancherelMeasure_def (α β : ℝ) :
    jacobiPlancherelMeasure α β = (volume.restrict (Ioi (0 : ℝ))).withDensity fun lam : ℝ =>
      ENNReal.ofReal ((2 * π)⁻¹ * ‖cFunction α β lam‖⁻¹ ^ 2) :=
  rfl

/-- The Jacobi operator kills constants. -/
theorem jacobiOperator_const (α β c : ℂ) (t : ℝ) : jacobiOperator α β (fun _ => c) t = 0 := by
  simp [jacobiOperator_def]

end SFVK.RankOne
