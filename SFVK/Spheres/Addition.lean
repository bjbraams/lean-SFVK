/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.Spheres.SphereMeasure
public import SFVK.Spheres.Zonal

/-!
# Addition theorem, Funk–Hecke formula and zonal spherical functions of `SO(n)`

The addition theorem `∑ᵢ Yᵢ(x) Yᵢ(y) = dim H_l · ω_{n,l}(⟪x, y⟫)` for an orthonormal basis of the
spherical harmonics of degree `l` in `L²` of the normalized sphere measure; the reproducing
property; the bound `|ω_{n,l}| ≤ 1`; the orthogonality of the zonal polynomials; the Funk–Hecke
formula; the zonal spherical functions of `(SO(n), K_η)` with their classification; and the
product formula.

The Gegenbauer addition theorem (Vilenkin–Klimyk, Vol. 2, §9.4.3 (5), p. 71) is lean-DLMF's
`DLMF.SphericalHarmonics.ultrasphericalPolynomial_addition` and is not restated here.

Sources: Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2, §10.2.1
(2)–(6), pp. 174–175 (the convolution and addition theorems with the normalized measure and the
Funk–Hecke formula), §9.3.8 (1)–(3), pp. 62–63 (orthogonality), §9.4.5 (1), p. 76 (product
formula); Wawrzyńczyk, *Group Representations and Special Functions*, (9.4.9)–(9.4.10) and
Theorem 9.4.1, p. 335, and (9.5.1)–(9.5.2), p. 337; Dieudonné, *Special Functions and Linear
Representations of Lie Groups*, §7, (101), p. 23.
-/

public noncomputable section

open MeasureTheory Polynomial Real Set
open scoped InnerProductSpace

namespace SFVK.Spheres

/-- **Addition theorem** (Vilenkin–Klimyk, Vol. 2, §10.2.1 (3), pp. 174–175). For `n ≥ 2` and an
`L²(sphereMeasure n)`-orthonormal basis `Y` of `H_l`,
`∑ᵢ Yᵢ(x) Yᵢ(y) = dim H_l · ω_{n,l}(⟪x, y⟫)` on the sphere. -/
theorem sum_sphereEval_mul_sphereEval_eq {n : ℕ} (hn : 2 ≤ n) (l : ℕ)
    (Y : Fin (Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l)) →
      MvPolynomial.harmonicSubmodule (Fin n) ℝ l)
    (hY : ∀ i j, ∫ x : Sphere n, MvPolynomial.sphereEval (Y i : MvPolynomial (Fin n) ℝ) x *
      MvPolynomial.sphereEval (Y j : MvPolynomial (Fin n) ℝ) x ∂sphereMeasure n =
        if i = j then 1 else 0)
    (x y : Sphere n) :
    ∑ i, MvPolynomial.sphereEval (Y i : MvPolynomial (Fin n) ℝ) x *
        MvPolynomial.sphereEval (Y i : MvPolynomial (Fin n) ℝ) y =
      Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l) *
        (zonalPolynomial n l).eval ⟪(x : EuclideanSpace ℝ (Fin n)), y⟫_ℝ := by
  sorry

/-- **Reproducing property** (Vilenkin–Klimyk, Vol. 2, §10.2.1 (2), p. 174). For `n ≥ 2`,
`p ∈ H_l` and `y` on the sphere, `∫ p(x) ω_{n,l}(⟪x, y⟫) dσ(x) = p(y)/dim H_l`. -/
theorem integral_sphereEval_mul_zonalPolynomial {n : ℕ} (hn : 2 ≤ n) {l : ℕ}
    {p : MvPolynomial (Fin n) ℝ} (hp : p ∈ MvPolynomial.harmonicSubmodule (Fin n) ℝ l)
    (y : Sphere n) :
    ∫ x : Sphere n, MvPolynomial.sphereEval p x *
        (zonalPolynomial n l).eval ⟪(x : EuclideanSpace ℝ (Fin n)), y⟫_ℝ ∂sphereMeasure n =
      MvPolynomial.sphereEval p y /
        Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l) := by
  sorry

/-- **Bound.** `|ω_{n,l}(t)| ≤ 1` on `[-1, 1]` for `n ≥ 2`. -/
theorem abs_zonalPolynomial_eval_le_one {n : ℕ} (hn : 2 ≤ n) (l : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    |(zonalPolynomial n l).eval t| ≤ 1 := by
  sorry

/-- **Orthogonality of the zonal polynomials** (Vilenkin–Klimyk, Vol. 2, §9.3.8 (1), p. 63;
Wawrzyńczyk (9.4.10), p. 335). For `n ≥ 2`,
`c_n ∫_{-1}^{1} ω_{n,l} ω_{n,l'} (1 - t²)^{(n-3)/2} dt = δ_{ll'}/dim H_l`. -/
theorem integral_zonalPolynomial_mul_zonalPolynomial {n : ℕ} (hn : 2 ≤ n) (l l' : ℕ) :
    polarConstant n * ∫ t in Ioo (-1 : ℝ) 1,
        (zonalPolynomial n l).eval t * (zonalPolynomial n l').eval t *
          (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2) =
      if l = l' then 1 / (Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l) : ℝ)
      else 0 := by
  sorry

/-- **Funk–Hecke formula** (Vilenkin–Klimyk, Vol. 2, §10.2.1 (5)–(6), p. 175). For `n ≥ 2`,
continuous `f`, a unit vector `η` and `p ∈ H_l`, `∫ f(⟪η, x⟫) p(x) dσ(x) = λ p(η)` with
`λ = c_n ∫_{-1}^{1} f(t) ω_{n,l}(t) (1 - t²)^{(n-3)/2} dt`. -/
theorem integral_comp_inner_mul_sphereEval {n : ℕ} (hn : 2 ≤ n) {l : ℕ} (f : ℝ → ℝ)
    (hf : Continuous f) {η : EuclideanSpace ℝ (Fin n)} (hη : ‖η‖ = 1)
    {p : MvPolynomial (Fin n) ℝ} (hp : p ∈ MvPolynomial.harmonicSubmodule (Fin n) ℝ l) :
    ∫ x : Sphere n, f ⟪η, (x : EuclideanSpace ℝ (Fin n))⟫_ℝ * MvPolynomial.sphereEval p x
        ∂sphereMeasure n =
      (polarConstant n * ∫ t in Ioo (-1 : ℝ) 1,
          f t * (zonalPolynomial n l).eval t * (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2)) *
        MvPolynomial.eval (fun i => η i) p := by
  sorry

/-- **Zonal spherical functions** (Vilenkin–Klimyk, Vol. 2, §9.3.2 (4), p. 47;
Wawrzyńczyk (9.4.9), p. 335). For `n ≥ 3`, a unit vector `η` and a left-invariant probability
measure `ν` on `K_η`, `g ↦ ω_{n,l}(⟪η, g η⟫)` is a spherical function of `(SO(n), K_η)`. -/
theorem isSphericalFunction_zonalSpherical {n : ℕ} (hn : 3 ≤ n) (l : ℕ)
    {η : EuclideanSpace ℝ (Fin n)} (hη : ‖η‖ = 1) (ν : Measure (rotationStabilizer η))
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] :
    Subgroup.IsSphericalFunction (rotationStabilizer η) ν (zonalSpherical n l η) := by
  sorry

/-- **Classification of the spherical functions** of `(SO(n), K_η)`, `n ≥ 3`: each is
`zonalSpherical n l η` for some `l`. -/
theorem exists_eq_zonalSpherical {n : ℕ} (hn : 3 ≤ n) {η : EuclideanSpace ℝ (Fin n)}
    (hη : ‖η‖ = 1) (ν : Measure (rotationStabilizer η)) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] {φ : RotationGroup n → ℂ}
    (hφ : Subgroup.IsSphericalFunction (rotationStabilizer η) ν φ) :
    ∃ l, φ = zonalSpherical n l η := by
  sorry

/-- **Product formula** (Vilenkin–Klimyk, Vol. 2, §9.4.5 (1), p. 76; Wawrzyńczyk (9.5.2),
p. 337). For `n ≥ 3`, `ω(cos a) ω(cos b) =
c'ₙ ∫_0^π ω(cos a cos b + sin a sin b cos ψ) sin^{n-3} ψ dψ`. -/
theorem zonalPolynomial_eval_cos_mul_eval_cos {n : ℕ} (hn : 3 ≤ n) (l : ℕ) (a b : ℝ) :
    (zonalPolynomial n l).eval (cos a) * (zonalPolynomial n l).eval (cos b) =
      Gamma (((n : ℝ) - 1) / 2) / (√π * Gamma (((n : ℝ) - 2) / 2)) *
        ∫ ψ in (0 : ℝ)..π, (zonalPolynomial n l).eval (cos a * cos b + sin a * sin b * cos ψ) *
          sin ψ ^ (n - 3) := by
  sorry

end SFVK.Spheres
