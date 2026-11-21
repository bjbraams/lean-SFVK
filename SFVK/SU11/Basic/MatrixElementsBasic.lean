/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import SFVK.SU11.Basic.Coordinates

/-!
# The matrix elements `𝔓^τ_{mn}` of `SU(1,1)` and the Mehler–Fock transform

The function `𝔓^τ_{mn}(cosh t)` of Vilenkin–Klimyk, *Representation of Lie Groups and Special
Functions*, Vol. 1, §6.5.1 (1)–(4), p. 311, is the boost matrix element of the principal series
in the circle model. It is defined here, following §6.5.4 (1), p. 314, as a function of
`t ∈ ℝ`, for every degree `τ ∈ ℂ` and real indices `m`, `n`, by the circle integral
`(2π)⁻¹ ∫₀^{2π} A(θ)^{τ+n} A(-θ)^{τ-n} e^{i(m-n)θ} dθ` with
`A(θ) = cosh(t/2) + sinh(t/2) e^{iθ}`. Both bases have positive real part (at least
`e^{-|t|/2}`), so the principal powers are analytic in all parameters and there is no branch
ambiguity.

The parabolic one-parameter subgroup `[[1 + is/2, s/2], [s/2, 1 - is/2]]`, the measures
`sinh t dt` and `ρ tanh(πρ) dρ` on `(0, ∞)` and the Mehler–Fock transforms of order `0` and of
integer order `m` (kernel `conj 𝔓^{-1/2+iρ}_{m0}(cosh t)`) complete the foundational layer.

## Main definitions

* `SFVK.SU11.boostMatrixElement`: `𝔓^τ_{mn}(cosh t)` as a function of `t`.
* `SFVK.SU11.parabolic`: the parabolic subgroup, a homomorphism from `ℝ` (`parabolic_add`).
* `SFVK.SU11.sinhMeasure`, `SFVK.SU11.plancherelMeasure`: `sinh t dt` and `ρ tanh(πρ) dρ`.
* `SFVK.SU11.mehlerFock`, `SFVK.SU11.mehlerFockOrder`: the Mehler–Fock transforms.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set
open scoped ComplexConjugate Real

namespace SFVK.SU11

/-! ### The boost matrix element -/

/-- Vilenkin–Klimyk's `𝔓^τ_{mn}(cosh t)` (Vol. 1, §6.5.4 (1), p. 314) as a function of `t`:
`(2π)⁻¹ ∫₀^{2π} (cosh(t/2) + sinh(t/2) e^{iθ})^{τ+n} (cosh(t/2) + sinh(t/2) e^{-iθ})^{τ-n}
e^{i(m-n)θ} dθ`, with principal complex powers of bases of positive real part. -/
def boostMatrixElement (τ : ℂ) (m n t : ℝ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
    ((Real.cosh (t / 2) : ℂ) + Real.sinh (t / 2) * exp ((θ : ℂ) * I)) ^ (τ + n) *
      ((Real.cosh (t / 2) : ℂ) + Real.sinh (t / 2) * exp (-((θ : ℂ) * I))) ^ (τ - n) *
      exp (((m - n : ℝ) : ℂ) * θ * I)

/-- The defining circle integral of `boostMatrixElement`. -/
theorem boostMatrixElement_def (τ : ℂ) (m n t : ℝ) :
    boostMatrixElement τ m n t =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π,
        ((Real.cosh (t / 2) : ℂ) + Real.sinh (t / 2) * exp ((θ : ℂ) * I)) ^ (τ + n) *
          ((Real.cosh (t / 2) : ℂ) + Real.sinh (t / 2) * exp (-((θ : ℂ) * I))) ^ (τ - n) *
          exp (((m - n : ℝ) : ℂ) * θ * I) :=
  (rfl)

/-- The bases of the powers in `boostMatrixElement` have real part at least `e^{-|t|/2}`; in
particular they lie off the branch cut of the principal power. -/
theorem exp_neg_abs_le_re_boostBase (t θ : ℝ) :
    Real.exp (-(|t| / 2)) ≤
      ((Real.cosh (t / 2) : ℂ) + Real.sinh (t / 2) * exp ((θ : ℂ) * I)).re := by
  have hre : ((Real.cosh (t / 2) : ℂ) + Real.sinh (t / 2) * exp ((θ : ℂ) * I)).re =
      Real.cosh (t / 2) + Real.sinh (t / 2) * Real.cos θ := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [hre]
  have hc : |Real.sinh (t / 2) * Real.cos θ| ≤ |Real.sinh (t / 2)| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one θ)
  have hs : Real.cosh (t / 2) - |Real.sinh (t / 2)| = Real.exp (-(|t| / 2)) := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by linarith)), abs_of_nonneg ht,
        Real.cosh_sub_sinh]
    · rw [abs_of_nonpos (Real.sinh_nonpos_iff.mpr (by linarith)), abs_of_nonpos ht, sub_neg_eq_add,
        Real.cosh_add_sinh]
      ring_nf
  have := neg_abs_le (Real.sinh (t / 2) * Real.cos θ)
  linarith

/-! ### The parabolic subgroup -/

/-- The parabolic element `[[1 + is/2, s/2], [s/2, 1 - is/2]]` of `SU(1,1)`. -/
def parabolic (s : ℝ) : SU11 :=
  ofPair ((1 : ℂ) + ((s / 2 : ℝ) : ℂ) * I) ((s / 2 : ℝ) : ℂ) (by
    have h : (1 : ℂ) + ((s / 2 : ℝ) : ℂ) * I = ((1 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * I := by simp
    rw [h, normSq_add_mul_I, normSq_ofReal]
    ring)

/-- The first coordinate of a parabolic element. -/
@[simp]
theorem entryA_parabolic (s : ℝ) : entryA (parabolic s) = 1 + ((s / 2 : ℝ) : ℂ) * I := (rfl)

/-- The second coordinate of a parabolic element. -/
@[simp]
theorem entryB_parabolic (s : ℝ) : entryB (parabolic s) = ((s / 2 : ℝ) : ℂ) := (rfl)

/-- Elements of `SU(1,1)` with the same upper row are equal. -/
private theorem eq_of_entry {g h : SU11} (ha : entryA g = entryA h) (hb : entryB g = entryB h) :
    g = h := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_eq_matrix g, coe_eq_matrix h, ha, hb]

/-- `parabolic 0` is the identity. -/
@[simp]
theorem parabolic_zero : parabolic 0 = 1 :=
  eq_of_entry (by simp) (by simp)

/-- `parabolic` is a homomorphism from `(ℝ, +)`. -/
theorem parabolic_add (s s' : ℝ) : parabolic (s + s') = parabolic s * parabolic s' := by
  apply eq_of_entry
  · rw [entryA_mul]
    simp only [entryA_parabolic, entryB_parabolic, conj_ofReal]
    push_cast
    linear_combination (-(s : ℂ) * s' / 4) * I_sq
  · rw [entryB_mul]
    simp only [entryA_parabolic, entryB_parabolic, map_add, map_one, map_mul, conj_ofReal,
      conj_I]
    push_cast
    ring

/-! ### The Mehler–Fock transform -/

/-- The measure `sinh t dt` on `(0, ∞)`. -/
def sinhMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (Real.sinh t)

/-- The defining density of `sinhMeasure`. -/
theorem sinhMeasure_def :
    sinhMeasure = (volume.restrict (Ioi 0)).withDensity fun t => ENNReal.ofReal (Real.sinh t) :=
  (rfl)

/-- The Plancherel measure `ρ tanh(πρ) dρ` of the Mehler–Fock transform on `(0, ∞)`. -/
def plancherelMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun ρ => ENNReal.ofReal (ρ * Real.tanh (π * ρ))

/-- The defining density of `plancherelMeasure`. -/
theorem plancherelMeasure_def :
    plancherelMeasure =
      (volume.restrict (Ioi 0)).withDensity fun ρ => ENNReal.ofReal (ρ * Real.tanh (π * ρ)) :=
  (rfl)

/-- The Mehler–Fock transform `ρ ↦ ∫₀^∞ f(t) 𝔓^{-1/2+iρ}_{00}(cosh t) sinh t dt`, with the
Bochner convention that a non-integrable integrand gives `0`. -/
def mehlerFock (f : ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ∫ t, f t * boostMatrixElement (-1 / 2 + ρ * I) 0 0 t ∂sinhMeasure

/-- The defining integral of `mehlerFock`. -/
theorem mehlerFock_def (f : ℝ → ℂ) (ρ : ℝ) :
    mehlerFock f ρ = ∫ t, f t * boostMatrixElement (-1 / 2 + ρ * I) 0 0 t ∂sinhMeasure :=
  (rfl)

/-- The Mehler–Fock transform of integer order `m`,
`ρ ↦ ∫₀^∞ f(t) conj 𝔓^{-1/2+iρ}_{m0}(cosh t) sinh t dt`. -/
def mehlerFockOrder (m : ℤ) (f : ℝ → ℂ) (ρ : ℝ) : ℂ :=
  ∫ t, f t * conj (boostMatrixElement (-1 / 2 + ρ * I) m 0 t) ∂sinhMeasure

/-- The defining integral of `mehlerFockOrder`. -/
theorem mehlerFockOrder_def (m : ℤ) (f : ℝ → ℂ) (ρ : ℝ) :
    mehlerFockOrder m f ρ =
      ∫ t, f t * conj (boostMatrixElement (-1 / 2 + ρ * I) m 0 t) ∂sinhMeasure :=
  (rfl)

end SFVK.SU11
