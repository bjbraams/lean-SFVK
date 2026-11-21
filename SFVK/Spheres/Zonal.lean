/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

import SFVK.Spheres.SphereMeasure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import TauCeti.Analysis.MvPolynomial.Sphere
public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import SFVK.Spheres.Basic

/-!
# Spherical harmonics, zonal polynomials and Gegenbauer polynomials

The closed dimension of the harmonic polynomials of degree `l` on `ℝⁿ`; the parity, degree,
hypergeometric, Gegenbauer, Chebyshev and Legendre forms of the normalized zonal polynomial
`ω_{n,l}`; its derivative and differential equation; the zonal harmonic `Z_{l,η}`, its
harmonicity, its values on the sphere, its invariance under `K_η` and its uniqueness; and the
Laplace integral.

The value at one, the generating function and the derivative of the Gegenbauer polynomials are
lean-DLMF's `DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_at_one`,
`DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_generating_function` and
`DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_derivative`; they are not restated here.

Sources: Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2, §9.2.3
(3)–(5), p. 30 (the harmonic projection and the dimension; the printed dimension of the
homogeneous polynomials is corrected in erratum E09.2.01 of the project's errata file), §9.3.2
(2)–(4), p. 47 (the zonal spherical function, its Laplace integral and its Gegenbauer form), and
§10.2.1, p. 173 (uniqueness of the zonal harmonic; the denominator of the second display is
`C_l^{(n-2)/2}(1)`, erratum E10.2.01); Wawrzyńczyk, *Group Representations and Special
Functions*, (9.2.9)–(9.2.11), p. 330, and §9.4, p. 335; Dieudonné, *Special Functions and Linear
Representations of Lie Groups*, §7, (99) and (103), pp. 23–24.
-/

public noncomputable section

open Polynomial Real
open scoped Nat InnerProductSpace

namespace SFVK.Spheres

/-! ### Dimension -/

/-- **Closed dimension formula** (Vilenkin–Klimyk, Vol. 2, §9.2.3 (4), p. 30; Wawrzyńczyk §9.4,
p. 335). For `n ≥ 3`, `dim H_l(ℝⁿ) = (2l + n - 2)(l + n - 3)!/((n - 2)! l!)`. -/
theorem finrank_harmonicSubmodule_mul {n : ℕ} (hn : 3 ≤ n) (l : ℕ) :
    Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l) * ((n - 2)! * l !) =
      (2 * l + n - 2) * (l + n - 3)! := by
  sorry

/-! ### The zonal polynomial -/

/-- **Parity.** `ω_{n,l}(-t) = (-1)ˡ ω_{n,l}(t)` for `n ≥ 2`. -/
theorem zonalPolynomial_comp_neg {n : ℕ} (hn : 2 ≤ n) (l : ℕ) :
    (zonalPolynomial n l).comp (-X) = (-1) ^ l * zonalPolynomial n l := by
  sorry

/-- **Degree.** `ω_{n,l}` has degree `l` for `n ≥ 2`. -/
theorem natDegree_zonalPolynomial {n : ℕ} (hn : 2 ≤ n) (l : ℕ) :
    (zonalPolynomial n l).natDegree = l := by
  sorry

/-- **Gegenbauer form** (Vilenkin–Klimyk, Vol. 2, §9.3.2 (4), p. 47; Wawrzyńczyk (9.2.11),
p. 330). For `n ≥ 3` and `λ = (n - 2)/2`, `ω_{n,l}(x) = C_l^{(λ)}(x)/C_l^{(λ)}(1)` with lean-DLMF's
Gegenbauer polynomial. -/
theorem zonalPolynomial_eq_ultrasphericalPolynomial_div {n : ℕ} (hn : 3 ≤ n) (l : ℕ) (x : ℝ) :
    (((zonalPolynomial n l).eval x : ℝ) : ℂ) =
      DLMF.OrthogonalPolynomials.ultrasphericalPolynomial (((n : ℂ) - 2) / 2) l x /
        DLMF.OrthogonalPolynomials.ultrasphericalPolynomial (((n : ℂ) - 2) / 2) l 1 := by
  sorry

/-- **Chebyshev.** `ω_{2,l} = T_l`. -/
theorem zonalPolynomial_two (l : ℕ) : zonalPolynomial 2 l = Chebyshev.T ℝ l := by
  sorry

/-- **Legendre.** `ω_{3,l} = P_l`, with lean-DLMF's Legendre polynomial. -/
theorem zonalPolynomial_three (l : ℕ) (x : ℝ) :
    (((zonalPolynomial 3 l).eval x : ℝ) : ℂ) =
      DLMF.OrthogonalPolynomials.legendrePolynomialP l x := by
  sorry

/-- **`n = 4`.** `(l + 1) ω_{4,l} = U_l`, the Chebyshev polynomial of the second kind. -/
theorem zonalPolynomial_four (l : ℕ) :
    C ((l : ℝ) + 1) * zonalPolynomial 4 l = Chebyshev.U ℝ l := by
  sorry

/-- **Derivative.** `ω_{n,l+1}' = ((l + 1)(l + n - 1)/(n - 1)) ω_{n+2,l}` for `n ≥ 2`. -/
theorem derivative_zonalPolynomial {n : ℕ} (hn : 2 ≤ n) (l : ℕ) :
    derivative (zonalPolynomial n (l + 1)) =
      C (((l : ℝ) + 1) * ((l : ℝ) + n - 1) / ((n : ℝ) - 1)) * zonalPolynomial (n + 2) l := by
  sorry

/-- **Differential equation.** For `n ≥ 2`,
`(1 - t²) ω'' - (n - 1) t ω' + l(l + n - 2) ω = 0`. -/
theorem zonalPolynomial_ode {n : ℕ} (hn : 2 ≤ n) (l : ℕ) :
    (1 - X ^ 2) * derivative (derivative (zonalPolynomial n l)) -
        C ((n : ℝ) - 1) * X * derivative (zonalPolynomial n l) +
      C ((l : ℝ) * ((l : ℝ) + n - 2)) * zonalPolynomial n l = 0 := by
  sorry

/-! ### The zonal harmonic -/

/-- **The zonal harmonic is harmonic of degree `l`**, for `n ≥ 2` and a unit vector `η`
(Vilenkin–Klimyk, Vol. 2, §10.2.1, p. 173; Wawrzyńczyk (9.2.9)–(9.2.11), p. 330). -/
theorem zonalHarmonic_mem_harmonicSubmodule {n : ℕ} (hn : 2 ≤ n) (l : ℕ)
    {η : EuclideanSpace ℝ (Fin n)} (hη : ‖η‖ = 1) :
    zonalHarmonic n l η ∈ MvPolynomial.harmonicSubmodule (Fin n) ℝ l := by
  sorry

/-- **Values on the sphere.** For `n ≥ 2` and `|x| = 1`, `Z_{l,η}(x) = ω_{n,l}(⟪η, x⟫)`. -/
theorem eval_zonalHarmonic {n : ℕ} (hn : 2 ≤ n) (l : ℕ) (η : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) :
    MvPolynomial.eval (fun i => x i) (zonalHarmonic n l η) =
      (zonalPolynomial n l).eval ⟪η, x⟫_ℝ := by
  sorry

/-- **`K_η`-invariance of the zonal harmonic.** -/
theorem eval_rotate_zonalHarmonic {n : ℕ} (l : ℕ) (η : EuclideanSpace ℝ (Fin n))
    {k : RotationGroup n} (hk : k ∈ rotationStabilizer η) (x : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial.eval (fun i => rotate k x i) (zonalHarmonic n l η) =
      MvPolynomial.eval (fun i => x i) (zonalHarmonic n l η) := by
  have hη : rotate k η = η := mem_rotationStabilizer.mp hk
  have hinner : ⟪η, rotate k x⟫_ℝ = ⟪η, x⟫_ℝ := by
    simpa only [hη] using inner_rotate_rotate k η x
  have hnorm : MvPolynomial.eval (fun i => rotate k x i) (MvPolynomial.normSq (Fin n) ℝ) =
      MvPolynomial.eval (fun i => x i) (MvPolynomial.normSq (Fin n) ℝ) := by
    rw [MvPolynomial.eval_normSq, MvPolynomial.eval_normSq]
    change ∑ i, (rotate k x).ofLp i ^ 2 = ∑ i, x.ofLp i ^ 2
    rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
    simpa only [real_inner_self_eq_norm_sq] using inner_rotate_rotate k x x
  simp only [zonalHarmonic_def, map_sum, apply_ite (MvPolynomial.eval _), map_zero, map_mul,
    map_pow, MvPolynomial.eval_C, eval_linearForm, hinner, hnorm]

/-- **Uniqueness of the zonal harmonic** (Vilenkin–Klimyk, Vol. 2, §10.2.1, Lemma, p. 173;
Dieudonné §7, p. 23). For `n ≥ 3` and a unit vector `η`, a `K_η`-invariant harmonic polynomial
of degree `l` is `p(η) Z_{l,η}`. -/
theorem eq_smul_zonalHarmonic {n : ℕ} (hn : 3 ≤ n) {l : ℕ} {η : EuclideanSpace ℝ (Fin n)}
    (hη : ‖η‖ = 1) {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ MvPolynomial.harmonicSubmodule (Fin n) ℝ l)
    (hinv : ∀ k ∈ rotationStabilizer η, ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => rotate k x i) p = MvPolynomial.eval (fun i => x i) p) :
    p = MvPolynomial.eval (fun i => η i) p • zonalHarmonic n l η := by
  sorry

/-! ### The Laplace integral -/

/-- **Laplace integral** (Vilenkin–Klimyk, Vol. 2, §9.3.2 (2), p. 47). For `n ≥ 3`,
`ω_{n,l}(cos φ) = c'ₙ ∫_0^π (cos φ + i sin φ cos θ)ˡ sin^{n-3} θ dθ` with
`c'ₙ = Γ((n - 1)/2)/(√π Γ((n - 2)/2))`. -/
theorem zonalPolynomial_eval_cos_eq_integral {n : ℕ} (hn : 3 ≤ n) (l : ℕ) (ϕ : ℝ) :
    (((zonalPolynomial n l).eval (cos ϕ) : ℝ) : ℂ) =
      ((Gamma (((n : ℝ) - 1) / 2) / (√π * Gamma (((n : ℝ) - 2) / 2)) : ℝ) : ℂ) *
        ∫ θ in (0 : ℝ)..π, ((cos ϕ : ℂ) + Complex.I * sin ϕ * cos θ) ^ l *
          ((sin θ ^ (n - 3) : ℝ) : ℂ) := by
  sorry

end SFVK.Spheres
