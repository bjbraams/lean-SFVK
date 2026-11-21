/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.RingTheory.MvPolynomial.Harmonic
public import SFVK.Spheres.Basic.Sphere

/-!
# Zonal polynomials and zonal harmonics of `SO(n)`

The normalized zonal polynomial `ω_{n,l}(t) = ₂F₁(-l, l + n - 2; (n - 1)/2; (1 - t)/2)` is the
zonal spherical function of `(SO(n), SO(n - 1))` as a function of `t = ⟪η, g η⟫`
(Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2, §9.3.2 (2)–(4),
p. 47; Wawrzyńczyk, *Group Representations and Special Functions*, (9.2.11), p. 330). For
`n ≥ 3` it is `C_l^{(λ)}(t)/C_l^{(λ)}(1)` with `λ = (n - 2)/2`; for `n = 2` it is the Chebyshev
polynomial `T_l` and for `n = 3` the Legendre polynomial `P_l`. It is defined here by its
terminating hypergeometric sum, so that it is a real polynomial for every `n`; for `n ≤ 1` the
lower parameter `(n - 1)/2` is not positive and the value is junk.

## Main definitions

* `SFVK.Spheres.zonalPolynomial n l`: the polynomial `ω_{n,l}`.
* `SFVK.Spheres.linearForm η`: the polynomial `x ↦ ⟪η, x⟫`.
* `SFVK.Spheres.zonalHarmonic n l η`: the homogenization `|x|ˡ ω_{n,l}(⟪η, x⟫/|x|)`.
* `SFVK.Spheres.zonalSpherical n l η`: the function `g ↦ ω_{n,l}(⟪η, g η⟫)` on `SO(n)`.
* `SFVK.Spheres.branchFactor`, `SFVK.Spheres.branchHarmonic`: the branching harmonics
  `|x|^{l-k} ω_{m+1+2k,l-k}(x_{m+1}/|x|) h(x₁, …, x_m)` of `SO(m + 1) ↓ SO(m)`
  (Vilenkin–Klimyk, Vol. 2, §9.3.1 (1)–(5), pp. 44–46).
-/

public noncomputable section

open Polynomial
open scoped Nat InnerProductSpace

namespace SFVK.Spheres

/-- The normalized zonal polynomial `ω_{n,l}(t) = ₂F₁(-l, l + n - 2; (n - 1)/2; (1 - t)/2)`,
as the terminating sum `∑_{k ≤ l} (-l)_k (l + n - 2)_k / (((n - 1)/2)_k k!) ((1 - t)/2)^k`. -/
@[expose]
def zonalPolynomial (n l : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (l + 1),
    C ((ascPochhammer ℝ k).eval (-(l : ℝ)) * (ascPochhammer ℝ k).eval ((l : ℝ) + n - 2) /
      ((ascPochhammer ℝ k).eval (((n : ℝ) - 1) / 2) * k !)) * (C (1 / 2) * (1 - X)) ^ k

/-- The zonal polynomial is a finite sum in the radial coordinate with its specified dimension and
degree normalization. -/
theorem zonalPolynomial_def (n l : ℕ) :
    zonalPolynomial n l = ∑ k ∈ Finset.range (l + 1),
      C ((ascPochhammer ℝ k).eval (-(l : ℝ)) * (ascPochhammer ℝ k).eval ((l : ℝ) + n - 2) /
        ((ascPochhammer ℝ k).eval (((n : ℝ) - 1) / 2) * k !)) * (C (1 / 2) * (1 - X)) ^ k :=
  rfl

/-- `ω_{n,0} = 1`. -/
@[simp]
theorem zonalPolynomial_zero_right (n : ℕ) : zonalPolynomial n 0 = 1 := by
  simp [zonalPolynomial]

/-- `ω_{n,l}(1) = 1`, for every `n`. -/
@[simp]
theorem zonalPolynomial_eval_one (n l : ℕ) : (zonalPolynomial n l).eval 1 = 1 := by
  rw [zonalPolynomial, Polynomial.eval_finsetSum, Finset.sum_range_succ']
  simp

/-- `ω_{n,1} = X` for `n ≥ 2`. -/
theorem zonalPolynomial_one_right {n : ℕ} (hn : 2 ≤ n) : zonalPolynomial n 1 = X := by
  have hn' : (n : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [zonalPolynomial, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [ascPochhammer_zero, ascPochhammer_one, eval_one, eval_X, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, mul_one, div_one, map_one]
  have h2 : (-(1 : ℝ)) * (1 + n - 2) / ((n - 1) / 2) = -2 := by
    field_simp
    ring
  rw [h2, ← mul_assoc, ← C_mul]
  norm_num

/-- The linear form `x ↦ ⟪η, x⟫` as a polynomial on `ℝⁿ`. -/
@[expose]
def linearForm {n : ℕ} (η : EuclideanSpace ℝ (Fin n)) : MvPolynomial (Fin n) ℝ :=
  ∑ i, MvPolynomial.C (η i) * MvPolynomial.X i

/-- The linear form is the polynomial whose coefficients are the coordinates of the pole. -/
theorem linearForm_def {n : ℕ} (η : EuclideanSpace ℝ (Fin n)) :
    linearForm η = ∑ i, MvPolynomial.C (η i) * MvPolynomial.X i :=
  rfl

/-- Evaluation of the linear form gives the real inner product with the pole. -/
@[simp]
theorem eval_linearForm {n : ℕ} (η x : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial.eval (fun i => x i) (linearForm η) = ⟪η, x⟫_ℝ := by
  simp [linearForm, PiLp.inner_apply, mul_comm]

/-- The zonal harmonic `Z_{l,η}(x) = |x|ˡ ω_{n,l}(⟪η, x⟫/|x|)`: the homogenization of `ω_{n,l}`
in `⟪η, x⟫` and `|x|²`. Only the coefficients of the parity of `l` enter; the others vanish for
`n ≥ 2`. -/
@[expose]
def zonalHarmonic (n l : ℕ) (η : EuclideanSpace ℝ (Fin n)) : MvPolynomial (Fin n) ℝ :=
  ∑ j ∈ Finset.range (l + 1),
    if Even (l - j) then
      MvPolynomial.C ((zonalPolynomial n l).coeff j) * linearForm η ^ j *
        MvPolynomial.normSq (Fin n) ℝ ^ ((l - j) / 2)
    else 0

/-- Homogenize the zonal polynomial in the pole coordinate and the squared norm. -/
theorem zonalHarmonic_def (n l : ℕ) (η : EuclideanSpace ℝ (Fin n)) :
    zonalHarmonic n l η = ∑ j ∈ Finset.range (l + 1),
      if Even (l - j) then
        MvPolynomial.C ((zonalPolynomial n l).coeff j) * linearForm η ^ j *
          MvPolynomial.normSq (Fin n) ℝ ^ ((l - j) / 2)
      else 0 :=
  rfl

/-- The zonal spherical function `g ↦ ω_{n,l}(⟪η, g η⟫)` of `(SO(n), K_η)`. -/
@[expose]
def zonalSpherical (n l : ℕ) (η : EuclideanSpace ℝ (Fin n)) (g : RotationGroup n) : ℂ :=
  ((zonalPolynomial n l).eval ⟪η, rotate g η⟫_ℝ : ℝ)

/-- The real spherical function is the zonal polynomial evaluated at the overlap with the rotated
pole. -/
theorem zonalSpherical_apply (n l : ℕ) (η : EuclideanSpace ℝ (Fin n)) (g : RotationGroup n) :
    zonalSpherical n l η g = ((zonalPolynomial n l).eval ⟪η, rotate g η⟫_ℝ : ℝ) :=
  rfl

/-- The zonal spherical function is `1` at the identity, for a unit vector `η`. -/
theorem zonalSpherical_one (n l : ℕ) {η : EuclideanSpace ℝ (Fin n)} (hη : ‖η‖ = 1) :
    zonalSpherical n l η 1 = 1 := by
  simp [zonalSpherical, hη]

/-- The factor `|x|^{l-k} ω_{m+1+2k,l-k}(x_{m+1}/|x|)` of the branching harmonics on `ℝ^{m+1}`:
the homogenization of `ω_{m+1+2k,l-k}` in the last coordinate and `|x|²`. -/
@[expose]
def branchFactor (m l k : ℕ) : MvPolynomial (Fin (m + 1)) ℝ :=
  ∑ j ∈ Finset.range (l - k + 1),
    if Even (l - k - j) then
      MvPolynomial.C ((zonalPolynomial (m + 1 + 2 * k) (l - k)).coeff j) *
        MvPolynomial.X (Fin.last m) ^ j * MvPolynomial.normSq (Fin (m + 1)) ℝ ^ ((l - k - j) / 2)
    else 0

/-- The branching factor is the homogenized zonal polynomial of the last coordinate in the effective
dimension. -/
theorem branchFactor_def (m l k : ℕ) :
    branchFactor m l k = ∑ j ∈ Finset.range (l - k + 1),
      if Even (l - k - j) then
        MvPolynomial.C ((zonalPolynomial (m + 1 + 2 * k) (l - k)).coeff j) *
          MvPolynomial.X (Fin.last m) ^ j *
            MvPolynomial.normSq (Fin (m + 1)) ℝ ^ ((l - k - j) / 2)
      else 0 :=
  rfl

/-- The branching map `h ↦ |x|^{l-k} ω_{m+1+2k,l-k}(x_{m+1}/|x|) h(x₁, …, x_m)` from polynomials
on `ℝᵐ` to polynomials on `ℝ^{m+1}`. -/
@[expose]
def branchHarmonic (m l k : ℕ) : MvPolynomial (Fin m) ℝ →ₗ[ℝ] MvPolynomial (Fin (m + 1)) ℝ :=
  LinearMap.mulLeft ℝ (branchFactor m l k) ∘ₗ (MvPolynomial.rename Fin.castSucc).toLinearMap

/-- A branch polynomial is the renamed lower-dimensional harmonic multiplied by its branching
factor. -/
theorem branchHarmonic_apply (m l k : ℕ) (h : MvPolynomial (Fin m) ℝ) :
    branchHarmonic m l k h = branchFactor m l k * MvPolynomial.rename Fin.castSucc h :=
  rfl

end SFVK.Spheres
