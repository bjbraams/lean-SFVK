/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import SFVK.Spheres.Basic.Sphere

/-!
# Harmonics of bidegree `(p, q)` and disk polynomials

Polynomials on `ℂⁿ` in `z` and `z̄` are polynomials in the variables `Sum.inl j` (for `zⱼ`) and
`Sum.inr j` (for `z̄ⱼ`). The harmonics of bidegree `(p, q)` are the polynomials of degree `p` in
`z` and `q` in `z̄` killed by `∑ⱼ ∂²/∂zⱼ∂z̄ⱼ`; they carry the irreducible representations of
`U(n)` of class one with respect to `U(n - 1)` (Vilenkin–Klimyk, *Representation of Lie Groups
and Special Functions*, Vol. 2, §11.2.1 (18)–(20), p. 295, and §11.2.2 (1)–(15), pp. 295–297).

The disk polynomial `R^α_{p,q}(w)` is `w^{p-q} ₂F₁(-q, p + α + 1; α + 1; 1 - |w|²)` for `p ≥ q`
and `conj R^α_{q,p}(w)` for `p < q` (Vilenkin–Klimyk, Vol. 2, §11.3.2 (4)–(6), p. 309, and
§11.4.5, p. 345, where the printed case `m < n` has `z` in place of `z̄`). It is defined here by
the finite sum `∑_{i ≤ min(p,q)} (-1)ⁱ C(p,i) C(q,i) i!/(α + 1)ᵢ (1 - |w|²)ⁱ w^{p-i} w̄^{q-i}`,
which is symmetric in `p` and `q`; for `α ∈ {-1, -2, …}` a denominator vanishes and the value
is junk. The zonal spherical function of `(U(n), K_η)` is `g ↦ R^{n-2}_{p,q}(⟪g η, η⟫)`.

## Main definitions

* `SFVK.Spheres.bidegreeHarmonic n p q`: the space `H^{p,q}`.
* `SFVK.Spheres.evalC z f`: the value of `f` at `(z, z̄)`.
* `SFVK.Spheres.diskPolynomial α p q`: the disk polynomial `R^α_{p,q}`.
* `SFVK.Spheres.diskHarmonic n p q η`: the `K_η`-invariant element of `H^{p,q}` with value
  `R^{n-2}_{p,q}(⟪η, ξ⟫)` on the sphere.
* `SFVK.Spheres.diskSpherical n p q η`: the spherical function `g ↦ R^{n-2}_{p,q}(⟪g η, η⟫)`.
-/

public noncomputable section

open scoped Nat ComplexConjugate InnerProductSpace

namespace SFVK.Spheres

/-- The bidegree weight: `zⱼ` has bidegree `(1, 0)` and `z̄ⱼ` has bidegree `(0, 1)`. -/
@[expose]
def bidegreeWeight (n : ℕ) : Fin n ⊕ Fin n → ℕ × ℕ :=
  Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))

@[simp]
theorem bidegreeWeight_inl (n : ℕ) (j : Fin n) : bidegreeWeight n (Sum.inl j) = (1, 0) :=
  rfl

@[simp]
theorem bidegreeWeight_inr (n : ℕ) (j : Fin n) : bidegreeWeight n (Sum.inr j) = (0, 1) :=
  rfl

/-- The complex Laplacian `∑ⱼ ∂²/∂zⱼ∂z̄ⱼ`. -/
@[expose]
def complexLaplacian (n : ℕ) :
    MvPolynomial (Fin n ⊕ Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n ⊕ Fin n) ℂ :=
  ∑ j, (MvPolynomial.pderiv (R := ℂ) (Sum.inl j)).toLinearMap ∘ₗ
    (MvPolynomial.pderiv (R := ℂ) (Sum.inr j)).toLinearMap

theorem complexLaplacian_apply (n : ℕ) (f : MvPolynomial (Fin n ⊕ Fin n) ℂ) :
    complexLaplacian n f =
      ∑ j, MvPolynomial.pderiv (Sum.inl j) (MvPolynomial.pderiv (Sum.inr j) f) := by
  simp [complexLaplacian]

/-- The space `H^{p,q}` of harmonic polynomials of bidegree `(p, q)` in `z, z̄`. -/
@[expose]
def bidegreeHarmonic (n p q : ℕ) : Submodule ℂ (MvPolynomial (Fin n ⊕ Fin n) ℂ) :=
  MvPolynomial.weightedHomogeneousSubmodule ℂ (bidegreeWeight n) (p, q) ⊓
    LinearMap.ker (complexLaplacian n)

theorem mem_bidegreeHarmonic_iff {n p q : ℕ} {f : MvPolynomial (Fin n ⊕ Fin n) ℂ} :
    f ∈ bidegreeHarmonic n p q ↔
      f.IsWeightedHomogeneous (bidegreeWeight n) (p, q) ∧ complexLaplacian n f = 0 := by
  simp [bidegreeHarmonic, MvPolynomial.mem_weightedHomogeneousSubmodule]

/-- The value of a polynomial in `z, z̄` at the point `z ∈ ℂⁿ`. -/
@[expose]
def evalC {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) (f : MvPolynomial (Fin n ⊕ Fin n) ℂ) : ℂ :=
  MvPolynomial.eval (Sum.elim (fun j => z j) (fun j => conj (z j))) f

theorem evalC_def {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) (f : MvPolynomial (Fin n ⊕ Fin n) ℂ) :
    evalC z f = MvPolynomial.eval (Sum.elim (fun j => z j) (fun j => conj (z j))) f :=
  rfl

/-- The disk polynomial `R^α_{p,q}(w) = ∑_{i ≤ min(p,q)} (-1)ⁱ C(p,i) C(q,i) i!/(α + 1)ᵢ
(1 - |w|²)ⁱ w^{p-i} w̄^{q-i}`. -/
@[expose]
def diskPolynomial (α : ℝ) (p q : ℕ) (w : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (min p q + 1),
    (((-1) ^ i * (p.choose i * q.choose i * i ! : ℝ) / (ascPochhammer ℝ i).eval (α + 1) : ℝ) : ℂ) *
      ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) ^ i * w ^ (p - i) * conj w ^ (q - i)

theorem diskPolynomial_def (α : ℝ) (p q : ℕ) (w : ℂ) :
    diskPolynomial α p q w = ∑ i ∈ Finset.range (min p q + 1),
      (((-1) ^ i * (p.choose i * q.choose i * i ! : ℝ) / (ascPochhammer ℝ i).eval (α + 1) : ℝ) :
        ℂ) * ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) ^ i * w ^ (p - i) * conj w ^ (q - i) :=
  rfl

/-- `R^α_{p,0}(w) = w^p`. -/
@[simp]
theorem diskPolynomial_zero_right (α : ℝ) (p : ℕ) (w : ℂ) : diskPolynomial α p 0 w = w ^ p := by
  simp [diskPolynomial]

/-- `R^α_{0,q}(w) = w̄^q`. -/
@[simp]
theorem diskPolynomial_zero_left (α : ℝ) (q : ℕ) (w : ℂ) :
    diskPolynomial α 0 q w = conj w ^ q := by
  simp [diskPolynomial]

/-- `R^α_{p,q}(1) = 1`, for every `α`. -/
@[simp]
theorem diskPolynomial_one (α : ℝ) (p q : ℕ) : diskPolynomial α p q 1 = 1 := by
  rw [diskPolynomial, Finset.sum_range_succ']
  simp

/-- **Symmetry.** `R^α_{q,p} = conj R^α_{p,q}`, for every `α`. -/
theorem diskPolynomial_swap (α : ℝ) (p q : ℕ) (w : ℂ) :
    diskPolynomial α q p w = conj (diskPolynomial α p q w) := by
  simp only [diskPolynomial, map_sum, map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj,
    min_comm q p]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm (p.choose i : ℝ) (q.choose i : ℝ)]
  ring

/-- The `U(n)`-zonal harmonic of bidegree `(p, q)`: with `w = ⟪η, z⟫`, the polynomial
`∑ᵢ cᵢ (|z|² - w w̄)ⁱ w^{p-i} w̄^{q-i}` with the coefficients `cᵢ` of `R^{n-2}_{p,q}`. -/
@[expose]
def diskHarmonic (n p q : ℕ) (η : EuclideanSpace ℂ (Fin n)) : MvPolynomial (Fin n ⊕ Fin n) ℂ :=
  let w : MvPolynomial (Fin n ⊕ Fin n) ℂ :=
    ∑ j, MvPolynomial.C (conj (η j)) * MvPolynomial.X (Sum.inl j)
  let wb : MvPolynomial (Fin n ⊕ Fin n) ℂ := ∑ j, MvPolynomial.C (η j) * MvPolynomial.X (Sum.inr j)
  let r2 : MvPolynomial (Fin n ⊕ Fin n) ℂ :=
    ∑ j, MvPolynomial.X (Sum.inl j) * MvPolynomial.X (Sum.inr j)
  ∑ i ∈ Finset.range (min p q + 1),
    MvPolynomial.C ((((-1) ^ i * (p.choose i * q.choose i * i ! : ℝ) /
      (ascPochhammer ℝ i).eval ((n : ℝ) - 1) : ℝ) : ℂ)) *
      (r2 - w * wb) ^ i * w ^ (p - i) * wb ^ (q - i)

theorem diskHarmonic_def (n p q : ℕ) (η : EuclideanSpace ℂ (Fin n)) :
    diskHarmonic n p q η = ∑ i ∈ Finset.range (min p q + 1),
      MvPolynomial.C ((((-1) ^ i * (p.choose i * q.choose i * i ! : ℝ) /
        (ascPochhammer ℝ i).eval ((n : ℝ) - 1) : ℝ) : ℂ)) *
        ((∑ j, MvPolynomial.X (Sum.inl j) * MvPolynomial.X (Sum.inr j)) -
            (∑ j, MvPolynomial.C (conj (η j)) * MvPolynomial.X (Sum.inl j)) *
              ∑ j, MvPolynomial.C (η j) * MvPolynomial.X (Sum.inr j)) ^ i *
        (∑ j, MvPolynomial.C (conj (η j)) * MvPolynomial.X (Sum.inl j)) ^ (p - i) *
        (∑ j, MvPolynomial.C (η j) * MvPolynomial.X (Sum.inr j)) ^ (q - i) :=
  rfl

/-- The spherical function `g ↦ R^{n-2}_{p,q}(⟪g η, η⟫)` of `(U(n), K_η)`. -/
@[expose]
def diskSpherical (n p q : ℕ) (η : EuclideanSpace ℂ (Fin n)) (g : UnitaryMatrixGroup n) : ℂ :=
  diskPolynomial ((n : ℝ) - 2) p q ⟪unitaryRotate g η, η⟫_ℂ

theorem diskSpherical_apply (n p q : ℕ) (η : EuclideanSpace ℂ (Fin n))
    (g : UnitaryMatrixGroup n) :
    diskSpherical n p q η g = diskPolynomial ((n : ℝ) - 2) p q ⟪unitaryRotate g η, η⟫_ℂ :=
  rfl

/-- The spherical function is `1` at the identity, for a unit vector `η`. -/
theorem diskSpherical_one (n p q : ℕ) {η : EuclideanSpace ℂ (Fin n)} (hη : ‖η‖ = 1) :
    diskSpherical n p q η 1 = 1 := by
  rw [diskSpherical_apply, unitaryRotate_one, inner_self_eq_norm_sq_to_K, hη]
  simp

end SFVK.Spheres
