/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib
public import TauCeti.RepresentationTheory.SU2.Exhaustion
public import TauCeti.RepresentationTheory.SU2.Adjoint
public import TauCeti.RepresentationTheory.SU2.Completeness
public import TauCeti.RepresentationTheory.SU2.Weyl.Integration
public import TauCeti.RepresentationTheory.Compact.PeterWeyl
public import TauCeti.RepresentationTheory.Continuous.Transport

/-!
# Matrix elements of SU(2) and SO(3): suggested statements

`README.md` is the roadmap; this file is not the roadmap. It states the headlines of `README.md`
that carry a Lean name, each with every conclusion the README attaches to it, against the pinned
Mathlib and Tau Ceti, with `sorry` proofs and the definitions they need. These are suggested
forms. The file is not an exhaustive acceptance test: the README's other headlines are targets of
the same standing, stated in prose.

Conventions (README, Conventions), after Edmonds, *Angular Momentum in Quantum Mechanics*:
spin `j = d / 2` with `d : ℕ`; the index `i : Fin (d + 1)` carries the magnetic quantum number
`m = i - d / 2` (`edWeight`), so Edmonds's order `m = j, j - 1, …, -j` is `i = d, …, 0`;
`matrixElement d i k g = ⟪e_i, T(g) e_k⟫` is Edmonds's `D^j_{m'm}` with `m' = i - d/2`,
`m = k - d/2`; the group element of the Euler angles `(α, β, γ)` is
`eulerD α β γ = diag(e^{iα/2}, e^{-iα/2}) · [[cos(β/2), sin(β/2)], [-sin(β/2), cos(β/2)]] ·
diag(e^{iγ/2}, e^{-iγ/2})`, so that `D^j_{m'm}(eulerD α β γ) = e^{im'α} d^j_{m'm}(β) e^{imγ}`
exactly as in Edmonds (4.1.12).

Bold headlines of the README that are not stated here, and what each lacks:

* the Gegenbauer form (Layer 2): a prose corollary of the Jacobi form through the Gegenbauer
  polynomials of the LaguerreJacobi roadmap, §6; no second local copy is made;
* Jacobi orthogonality for integral parameters (Layer 3): a consistency check of
  `integral_smallD_mul_smallD` against the LaguerreJacobi roadmap, §4.3, whose statement it
  restates;
* the raising and lowering operators (Layer 4): they are read off from `lieMatrix₁` and
  `lieMatrix₂`, and a separate statement would repeat their definitions;
* the expansion of class functions in characters (Layer 5): a corollary of `hasSum_plancherel`;
  stating it separately needs the closed subspace of class functions in `L²`;
* the decomposition of `L²(S²)` (Layer 6): needs the quasi-regular representation of SO(3) on
  `L²(S²)`, which belongs to the general function-space infrastructure of the planned Roadmap 2.
-/

@[expose] public section

noncomputable section

namespace SFVK.SU2MatrixElements

open TauCeti TauCeti.SU2 Matrix MeasureTheory Polynomial Set Complex
open scoped Real ComplexConjugate

/-! ## Layer 1: coordinates -/

/-- The element `[[α, β], [-conj β, conj α]]` of `SU(2)` defined by a pair with
`|α|² + |β|² = 1`. -/
def ofPair (α β : ℂ) (h : normSq α + normSq β = 1) : SU2 :=
  ⟨!![α, β; -conj β, conj α], by
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    have h' : (α * conj α + β * conj β : ℂ) = 1 := by
      rw [mul_conj, mul_conj, ← ofReal_add, h, ofReal_one]
    have h'' : (conj α * α + conj β * β : ℂ) = 1 := by
      rw [mul_comm (conj α), mul_comm (conj β), h']
    refine ⟨?_, ?_⟩
    · ext a b
      fin_cases a <;> fin_cases b <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, h'] <;>
        simp_all [mul_comm, add_comm]
    · simp [Matrix.det_fin_two_of]
      linear_combination h'⟩

/-- Edmonds's middle factor, `exp(iβ J_y)` at spin one half (Edmonds (4.1.13)):
`[[cos(β/2), sin(β/2)], [-sin(β/2), cos(β/2)]]`. -/
def bBeta (β : ℝ) : SU2 :=
  ofPair (Real.cos (β / 2)) (Real.sin (β / 2)) (by
    rw [normSq_ofReal, normSq_ofReal]
    nlinarith [Real.cos_sq_add_sin_sq (β / 2)])

/-- **The Euler element** of Edmonds's angles `(α, β, γ)`:
`exp(iαJ_z) exp(iβJ_y) exp(iγJ_z)` at spin one half, that is
`torusExp (α/2) * bBeta β * torusExp (γ/2)`. -/
def eulerD (α β γ : ℝ) : SU2 :=
  torusExp (α / 2) * bBeta β * torusExp (γ / 2)

/-- The parameter box `0 ≤ α < 2π`, `0 < β < π`, `-2π ≤ γ < 2π`. -/
def eulerBox : Set (ℝ × ℝ × ℝ) :=
  Ico 0 (2 * π) ×ˢ Ioo 0 π ×ˢ Ico (-(2 * π)) (2 * π)

/-- **The Euler matrix.** The entries of `eulerD α β γ`. -/
theorem coe_eulerD (α β γ : ℝ) :
    (eulerD α β γ : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Real.cos (β / 2) * exp (I * ((α + γ) / 2)), Real.sin (β / 2) * exp (I * ((α - γ) / 2));
        -(Real.sin (β / 2) * exp (-(I * ((α - γ) / 2)))),
          Real.cos (β / 2) * exp (-(I * ((α + γ) / 2)))] := by
  sorry

/-- **Euler angles cover SU(2), and are a bijection on the generic set.** Every element is
`eulerD α β γ` with `0 ≤ α < 2π`, `0 ≤ β ≤ π`, `-2π ≤ γ < 2π`; on the box the parametrization is
a bijection onto the set where both entries of the first row are nonzero. -/
theorem exists_eulerD_eq_and_bijOn :
    (∀ g : SU2, ∃ α β γ, α ∈ Ico 0 (2 * π) ∧ β ∈ Icc 0 π ∧ γ ∈ Ico (-(2 * π)) (2 * π) ∧
      eulerD α β γ = g) ∧
    BijOn (fun p : ℝ × ℝ × ℝ ↦ eulerD p.1 p.2.1 p.2.2) eulerBox
      {g : SU2 | (g : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℂ) 0 1 ≠ 0} := by
  sorry

/-- The rotation about the third axis by `a`. -/
def rotZ (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos a, -Real.sin a, 0; Real.sin a, Real.cos a, 0; 0, 0, 1]

/-- The rotation about the second axis by `a`. -/
def rotY (a : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos a, 0, Real.sin a; 0, 1, 0; -Real.sin a, 0, Real.cos a]

/-- **Euler angles on SO(3).** Under Tau Ceti's double cover the Euler element maps to
`R_z(-α) R_y(-β) R_z(-γ)`, and every rotation has this form with `0 ≤ α < 2π`, `0 ≤ β ≤ π`,
`0 ≤ γ < 2π`. -/
theorem toSO3_eulerD (α β γ : ℝ) :
    (toSO3 (eulerD α β γ) : Matrix (Fin 3) (Fin 3) ℝ) = rotZ (-α) * rotY (-β) * rotZ (-γ) ∧
    ∀ R : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∃ α β γ, α ∈ Ico 0 (2 * π) ∧
      β ∈ Icc 0 π ∧ γ ∈ Ico 0 (2 * π) ∧
      (R : Matrix (Fin 3) (Fin 3) ℝ) = rotZ (-α) * rotY (-β) * rotZ (-γ) := by
  sorry

/-- The Euler-angle measure `(16π²)⁻¹ sin β dα dβ dγ` on the box. -/
def eulerMeasure : Measure (ℝ × ℝ × ℝ) :=
  ENNReal.ofReal (16 * π ^ 2)⁻¹ •
    (volume.restrict eulerBox).withDensity fun p ↦ ENNReal.ofReal (Real.sin p.2.1)

/-- **Haar measure in Euler angles.** The normalized Haar measure of `SU(2)` is the image of
`(16π²)⁻¹ sin β dα dβ dγ` on the box; for every Haar-integrable `f` the integral is the iterated
Euler-angle integral. -/
theorem haarProb_eq_map_eulerMeasure :
    haarProb SU2 = (eulerMeasure).map (fun p ↦ eulerD p.1 p.2.1 p.2.2) ∧
    ∀ f : SU2 → ℂ, Integrable f (haarProb SU2) →
      ∫ g, f g ∂haarProb SU2 =
        ((16 * π ^ 2)⁻¹ : ℝ) * ∫ p in eulerBox, f (eulerD p.1 p.2.1 p.2.2) * Real.sin p.2.1 := by
  sorry

/-- **Haar measure of SO(3).** The normalized Haar measure of `SO(3)` is the image of that of
`SU(2)` under the double cover. -/
theorem map_toSO3_haarProb :
    (haarProb SU2).map (fun g ↦ toSO3 g) =
      haarProb (Matrix.specialOrthogonalGroup (Fin 3) ℝ) := by
  sorry

/-! ## Layer 1: the unitary model -/

/-- The magnetic quantum number `m = i - d / 2` of the index `i` (Edmonds's convention). -/
def edWeight (d i : ℕ) : ℝ := i - d / 2

/-- The positive scale `√(i! (d - i)!)`, the norm of the monomial `z₁^i z₂^{d-i}` for the
invariant inner product. -/
def monomialNorm (d : ℕ) (i : Fin (d + 1)) : ℝ :=
  Real.sqrt ((i : ℕ).factorial * (d - i).factorial)

/-- The squared norm assigned to a basis monomial is strictly positive. -/
theorem monomialNorm_pos (d : ℕ) (i : Fin (d + 1)) : 0 < monomialNorm d i :=
  Real.sqrt_pos.2 (by positivity)

/-- The diagonal change of basis `e_i ↦ √(i! (d - i)!) e_i` of the model space. -/
def scale (d : ℕ) : EuclideanSpace ℂ (Fin (d + 1)) ≃L[ℂ] EuclideanSpace ℂ (Fin (d + 1)) :=
  LinearEquiv.toContinuousLinearEquiv <|
    (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.equiv
      ((EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.unitsSMul fun i ↦
        Units.mk0 ((monomialNorm d i : ℝ) : ℂ) (ofReal_ne_zero.2 (monomialNorm_pos d i).ne'))
      (Equiv.refl _)

/-- **The unitary model of `Sym^d`.** Tau Ceti's `symPowerModel d` transported by `scale d`; the
standard basis vector `e_i` corresponds to the normalized monomial
`z₁^i z₂^{d-i} / √(i! (d - i)!)`, Edmonds's `u(j, m)` with `j = d/2`, `m = i - d/2`. -/
def unitaryModel (d : ℕ) : ContRepresentation ℂ SU2 (EuclideanSpace ℂ (Fin (d + 1))) :=
  (scale d).congr (symPowerModel d)

/-- The finite-dimensional unitary model varies continuously with the group element. -/
theorem continuous_unitaryModel (d : ℕ) : Continuous (unitaryModel d) :=
  (scale d).continuous_congr (continuous_symPowerModel d)

/-- **The invariant inner product.** The unitary model is unitary and irreducible. -/
theorem isUnitary_unitaryModel (d : ℕ) :
    ContRepresentation.IsUnitary (unitaryModel d) ∧
    Representation.IsIrreducible (unitaryModel d).toRepresentation := by
  sorry

/-- The unitary model as a Tau Ceti `IrrepModel`. -/
def irrepModel (d : ℕ) : IrrepModel ℂ SU2 where
  dim := d + 1
  rep := unitaryModel d
  continuous_rep := continuous_unitaryModel d
  isUnitary := (isUnitary_unitaryModel d).1
  isIrreducible := (isUnitary_unitaryModel d).2

/-- **The unitary dual of SU(2).** The models `irrepModel d`, `d : ℕ`, form a skeleton of the
continuous unitary irreducible representations. -/
theorem isIrrepSkeleton_irrepModel : IsIrrepSkeleton irrepModel := by
  sorry

/-! ## Layer 2: matrix elements and their closed forms -/

/-- **The matrix element** `D^j_{m'm}(g) = ⟪e_{m'}, T^j(g) e_m⟫` (Edmonds (4.1.10)), as the
conjugate of Tau Ceti's matrix coefficient `⟪T^j(g) e_m, e_{m'}⟫`. Here `j = d / 2`,
`m' = i - d / 2`, `m = k - d / 2`. -/
def matrixElement (d : ℕ) (i k : Fin (d + 1)) (g : SU2) : ℂ :=
  conj (ContRepresentation.matrixCoeff (unitaryModel d) (continuous_unitaryModel d)
    (EuclideanSpace.single k 1) (EuclideanSpace.single i 1) g)

/-- **The basis expansion.** `T^l(g) e_n = Σ_m t^l_{mn}(g) e_m`. -/
theorem unitaryModel_single (d : ℕ) (g : SU2) (j : Fin (d + 1)) :
    unitaryModel d g (EuclideanSpace.single j 1) =
      ∑ i, matrixElement d i j g • EuclideanSpace.single i 1 := by
  sorry

/-- The explicit polynomial in the entries `a, b, c, e` of `A` (row by row):
`Σ_k √(i!(d-i)! j!(d-j)!) a^{k+i+j-d} b^{d-j-k} c^{d-i-k} e^k / (k!(k+i+j-d)!(d-j-k)!(d-i-k)!)`,
the sum over the `k` for which every exponent is a natural number. -/
def entrySum (d i j : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    if d ≤ k + i + j ∧ k + i ≤ d ∧ k + j ≤ d then
      ((Real.sqrt (i.factorial * (d - i).factorial * j.factorial * (d - j).factorial) /
          (k.factorial * (k + i + j - d).factorial * (d - j - k).factorial *
            (d - i - k).factorial) : ℝ) : ℂ) *
        A 0 0 ^ (k + i + j - d) * A 0 1 ^ (d - j - k) * A 1 0 ^ (d - i - k) * A 1 1 ^ k
    else 0

/-- **The explicit polynomial formula.** -/
theorem matrixElement_eq_entrySum (d : ℕ) (i j : Fin (d + 1)) (g : SU2) :
    matrixElement d i j g = entrySum d i j (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  sorry

/-- **Spin one half is the defining representation.** With `m = i - 1/2`, Edmonds's order
`m = +1/2, -1/2` is `i = 1, 0`, and the matrix of `T^{1/2}(g)` in that order is `g`. -/
theorem matrixElement_one (i j : Fin 2) (g : SU2) :
    matrixElement 1 i j g = (g : Matrix (Fin 2) (Fin 2) ℂ) (Fin.rev i) (Fin.rev j) := by
  sorry

/-- **The group law.** `D(gh) = D(g) D(h)`, `D(g⁻¹)_{m'm} = conj D(g)_{mm'}`, and the two
unitarity relations. -/
theorem matrixElement_mul_inv (d : ℕ) (i j : Fin (d + 1)) (g h : SU2) :
    matrixElement d i j (g * h) = ∑ k, matrixElement d i k g * matrixElement d k j h ∧
    matrixElement d i j g⁻¹ = conj (matrixElement d j i g) ∧
    ∑ k, conj (matrixElement d k i g) * matrixElement d k j g = (if i = j then 1 else 0) ∧
    ∑ k, matrixElement d i k g * conj (matrixElement d j k g) = (if i = j then 1 else 0) := by
  sorry

/-- **The centre and the passage to SO(3).** `-1 = torusExp π` acts by `(-1)^d`; for even `d`
the unitary model factors through the double cover. -/
theorem matrixElement_torusExp_pi_mul (d : ℕ) (i j : Fin (d + 1)) (g : SU2) :
    matrixElement d i j (torusExp π * g) = (-1) ^ d * matrixElement d i j g ∧
    (Even d → ∃ ρ : ContRepresentation ℂ (Matrix.specialOrthogonalGroup (Fin 3) ℝ)
        (EuclideanSpace ℂ (Fin (d + 1))),
      Continuous ρ ∧ ContRepresentation.IsUnitary ρ ∧ ∀ g, ρ (toSO3 g) = unitaryModel d g) := by
  sorry

/-- **Edmonds's `d^j_{m'm}(β)`** by his finite sum (4.1.15), in the indices `i = j + m'`,
`k = j + m`:
`√(i!(d-i)!/(k!(d-k)!)) Σ_σ C(k, d-i-σ) C(d-k, σ) (-1)^{d-i-σ} cos(β/2)^{2σ+i+k-d}
sin(β/2)^{2d-i-k-2σ}`. It is `0` when an index exceeds `d`, and is defined for every real `β`. -/
def smallD (d i k : ℕ) (β : ℝ) : ℝ :=
  if i ≤ d ∧ k ≤ d then
    Real.sqrt ((i.factorial * (d - i).factorial : ℕ) / (k.factorial * (d - k).factorial : ℕ)) *
      ∑ σ ∈ Finset.range (d - i + 1),
        ((k.choose (d - i - σ) * (d - k).choose σ : ℕ) : ℝ) * (-1) ^ (d - i - σ) *
          Real.cos (β / 2) ^ (2 * σ + i + k - d) * Real.sin (β / 2) ^ (2 * d - i - k - 2 * σ)
  else 0

/-- **Matrix elements in Euler angles** (Edmonds (4.1.12)).
`D^j_{m'm}(eulerD α β γ) = e^{im'α} d^j_{m'm}(β) e^{imγ}` for all real angles. -/
theorem matrixElement_eulerD (d : ℕ) (i k : Fin (d + 1)) (α β γ : ℝ) :
    matrixElement d i k (eulerD α β γ) =
      exp (I * (edWeight d i * α)) * smallD d i k β * exp (I * (edWeight d k * γ)) := by
  sorry

/-- Local copy of the Jacobi polynomial `P_n^{(α,β)}` of the LaguerreJacobi roadmap, §3.2
(DLMF 18.5.8), verbatim; the owner is that roadmap. -/
def jacobi {R : Type*} [CommRing R] [Algebra ℚ R] (α β : R) (n : ℕ) : R[X] :=
  ((1 : ℚ) / 2 ^ n) • ∑ k ∈ Finset.range (n + 1),
    (((1 : ℚ) / ((n - k).factorial * k.factorial)) •
      ((ascPochhammer R (n - k)).smeval (β + k + 1) *
        (ascPochhammer R k).smeval (α + (n - k : ℕ) + 1))) • ((X - 1) ^ (n - k) * (X + 1) ^ k)

/-- **The Jacobi form** (Edmonds (4.1.23), extended to all indices). With `a = |i - k| = |m' - m|`,
`b = |d - i - k| = |m' + m|`, `κ = min(i, k, d - i, d - k) = j - max(|m'|, |m|)`:
`d^j_{m'm}(β) = (-1)^{max(k - i, 0)} √(κ!(d-κ)!/((κ+a)!(κ+b)!)) sin(β/2)^a cos(β/2)^b
P_κ^{(a,b)}(cos β)`. -/
theorem smallD_eq_jacobi (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) (β : ℝ) :
    smallD d i k β =
      (-1) ^ (k - i) *
        Real.sqrt ((Nat.min (Nat.min i k) (Nat.min (d - i) (d - k))).factorial *
            (d - Nat.min (Nat.min i k) (Nat.min (d - i) (d - k))).factorial /
          ((Nat.min (Nat.min i k) (Nat.min (d - i) (d - k)) + Int.natAbs ((i : ℤ) - k)).factorial *
            (Nat.min (Nat.min i k) (Nat.min (d - i) (d - k)) +
              Int.natAbs ((d : ℤ) - i - k)).factorial)) *
        Real.sin (β / 2) ^ Int.natAbs ((i : ℤ) - k) *
        Real.cos (β / 2) ^ Int.natAbs ((d : ℤ) - i - k) *
        (jacobi (Int.natAbs ((i : ℤ) - k) : ℝ) (Int.natAbs ((d : ℤ) - i - k) : ℝ)
          (Nat.min (Nat.min i k) (Nat.min (d - i) (d - k)))).eval (Real.cos β) := by
  sorry

/-- **The hypergeometric form.** With `a, b, κ` as in `smallD_eq_jacobi`,
`P_κ^{(a,b)}(cos β) = (a+1)_κ / κ! · F(-κ, d-κ+1; a+1; sin²(β/2))`. -/
theorem smallD_eq_hypergeometric (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) (β : ℝ) :
    smallD d i k β =
      (-1) ^ (k - i) *
        Real.sqrt ((Nat.min (Nat.min i k) (Nat.min (d - i) (d - k))).factorial *
            (d - Nat.min (Nat.min i k) (Nat.min (d - i) (d - k))).factorial /
          ((Nat.min (Nat.min i k) (Nat.min (d - i) (d - k)) + Int.natAbs ((i : ℤ) - k)).factorial *
            (Nat.min (Nat.min i k) (Nat.min (d - i) (d - k)) +
              Int.natAbs ((d : ℤ) - i - k)).factorial)) *
        Real.sin (β / 2) ^ Int.natAbs ((i : ℤ) - k) *
        Real.cos (β / 2) ^ Int.natAbs ((d : ℤ) - i - k) *
        ((ascPochhammer ℝ (Nat.min (Nat.min i k) (Nat.min (d - i) (d - k)))).eval
            ((Int.natAbs ((i : ℤ) - k) : ℝ) + 1) /
          (Nat.min (Nat.min i k) (Nat.min (d - i) (d - k))).factorial) *
        ordinaryHypergeometric (𝔸 := ℝ)
          (-(Nat.min (Nat.min i k) (Nat.min (d - i) (d - k)) : ℝ))
          ((d - Nat.min (Nat.min i k) (Nat.min (d - i) (d - k)) + 1 : ℕ) : ℝ)
          ((Int.natAbs ((i : ℤ) - k) : ℝ) + 1) (Real.sin (β / 2) ^ 2) := by
  sorry

/-- **Symmetries** (Edmonds (4.2.2)–(4.2.6)). For `i, k ≤ d`:
`d_{m'm} = (-1)^{m'-m} d_{mm'} = (-1)^{m'-m} d_{-m',-m}`, `d_{m'm}(-β) = d_{mm'}(β)`, and
`d_{m'm}(π + β) = (-1)^{j-m'} d_{-m',m}(β)`. -/
theorem smallD_symm (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) (β : ℝ) :
    smallD d i k β = (-1) ^ (i + k) * smallD d k i β ∧
    smallD d i k β = (-1) ^ (i + k) * smallD d (d - i) (d - k) β ∧
    smallD d i k (-β) = smallD d k i β ∧
    smallD d i k (π + β) = (-1) ^ (d - i) * smallD d (d - i) k β := by
  sorry

/-- **Values at `0` and `π`** (Edmonds (4.2.1)). `d_{m'm}(0) = δ_{m'm}` and
`d_{m'm}(π) = (-1)^{j+m} δ_{m',-m}`. -/
theorem smallD_zero_pi (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) :
    smallD d i k 0 = (if i = k then 1 else 0) ∧
    smallD d i k π = (if i + k = d then (-1) ^ k else 0) := by
  sorry

/-- The Legendre polynomial `P_l(z) = P̃_l((1 - z)/2)`, from Mathlib's shifted Legendre
polynomial `P̃_l(x) = Σ_k (-1)^k C(l,k) C(l+k,l) x^k`. -/
def legendrePoly (l : ℕ) : ℝ[X] :=
  ((shiftedLegendre l).map (Int.castRingHom ℝ)).comp (C (1 / 2 : ℝ) * (1 - X))

/-- **Legendre polynomials are the zonal matrix elements** (Edmonds (4.1.26)).
`d^l_{00}(β) = P_l(cos β)` and `D^l_{00}(eulerD α β γ) = P_l(cos β)` for integral `l`. -/
theorem smallD_two_mul_self (l : ℕ) (α β γ : ℝ) :
    smallD (2 * l) l l β = (legendrePoly l).eval (Real.cos β) ∧
    matrixElement (2 * l) ⟨l, by omega⟩ ⟨l, by omega⟩ (eulerD α β γ) =
      (legendrePoly l).eval (Real.cos β) := by
  sorry

/-- **Associated Legendre functions** (Edmonds (4.1.24)). For `0 ≤ n ≤ l`,
`d^l_{n0}(β) = √((l-n)!/(l+n)!) sin^n β P_l^{(n)}(cos β)`; with DLMF's Ferrers function
`P_l^n(x) = (-1)^n (1-x²)^{n/2} P_l^{(n)}(x)` this is `(-1)^n √((l-n)!/(l+n)!) P_l^n(cos β)` for
`0 ≤ β ≤ π`. -/
theorem smallD_eq_ferrers (l n : ℕ) (hn : n ≤ l) (β : ℝ) :
    smallD (2 * l) (l + n) l β =
      Real.sqrt ((l - n).factorial / (l + n).factorial) * Real.sin β ^ n *
        ((derivative^[n]) (legendrePoly l)).eval (Real.cos β) := by
  sorry

/-- Vilenkin–Klimyk's Euler factor `a_θ = [[cos(θ/2), i sin(θ/2)], [i sin(θ/2), cos(θ/2)]]`,
which is `exp(iθJ_x)` at spin one half. -/
def aTheta (θ : ℝ) : SU2 :=
  ofPair (Real.cos (θ / 2)) (I * Real.sin (θ / 2)) (by
    rw [normSq_ofReal, normSq_mul, normSq_I, normSq_ofReal, one_mul]
    nlinarith [Real.cos_sq_add_sin_sq (θ / 2)])

/-- Vilenkin–Klimyk's Euler element `u(φ, θ, ψ) = g_φ a_θ g_ψ`, used only by `vk_conversion`. -/
def eulerU (φ θ ψ : ℝ) : SU2 :=
  torusExp (φ / 2) * aTheta θ * torusExp (ψ / 2)

/-- Vilenkin–Klimyk's weight `m_VK = d / 2 - i = -edWeight d i` of the index `i`. -/
def vkWeight (d i : ℕ) : ℝ := d / 2 - i

/-- **The conversion from Vilenkin–Klimyk.** VK's Euler element `u(φ, θ, ψ) = g_φ a_θ g_ψ` is
`eulerD (φ + π/2) θ (ψ - π/2)`; VK's basis `ψ_m` is `e_i` with `m_VK = d/2 - i = -m`, so
`t^{VK}_{m n} = D_{-m,-n}`, and VK's Euler formula
`t^{VK}_{mn}(u(φ, θ, ψ)) = i^{m-n} e^{-i(mφ+nψ)} P^l_{mn}(cos θ)` holds with
`P^l_{mn}(cos θ) = d^l_{mn}(θ)`, which in the index `i` is `smallD d (d - i) (d - k) θ`. -/
theorem vk_conversion (φ θ ψ : ℝ) :
    eulerU φ θ ψ = eulerD (φ + π / 2) θ (ψ - π / 2) ∧
    ∀ (d : ℕ) (i k : Fin (d + 1)),
      matrixElement d i k (eulerU φ θ ψ) =
        I ^ ((k : ℤ) - i) * exp (-(I * (vkWeight d i * φ + vkWeight d k * ψ))) *
          smallD d (d - i) (d - k) θ := by
  sorry

/-! ## Layer 3: identities from the group law -/

/-- **The angle of a product.** If `eulerD 0 β₁ 0 * eulerD α₂ β₂ 0 = eulerD α β γ` then
`cos β = cos β₁ cos β₂ - sin β₁ sin β₂ cos α₂`. -/
theorem cos_of_eulerD_mul {β₁ α₂ β₂ α β γ : ℝ}
    (h : eulerD 0 β₁ 0 * eulerD α₂ β₂ 0 = eulerD α β γ) :
    Real.cos β = Real.cos β₁ * Real.cos β₂ - Real.sin β₁ * Real.sin β₂ * Real.cos α₂ := by
  sorry

/-- **The addition theorem for `d^j`.** If `eulerD 0 β₁ 0 * eulerD α₂ β₂ 0 = eulerD α β γ` then
`e^{i(m'α + mγ)} d_{m'm}(β) = Σ_μ e^{iμα₂} d_{m'μ}(β₁) d_{μm}(β₂)`. -/
theorem smallD_addition (d : ℕ) (i k : Fin (d + 1)) {β₁ α₂ β₂ α β γ : ℝ}
    (h : eulerD 0 β₁ 0 * eulerD α₂ β₂ 0 = eulerD α β γ) :
    exp (I * (edWeight d i * α + edWeight d k * γ)) * smallD d i k β =
      ∑ μ : Fin (d + 1), exp (I * (edWeight d μ * α₂)) *
        smallD d i μ β₁ * smallD d μ k β₂ := by
  sorry

/-- **The Legendre addition theorem.**
`P_l(cos β₁ cos β₂ - sin β₁ sin β₂ cos α)` equals
`Σ_m (-1)^m cos(mα) d^l_{m0}(β₁) d^l_{m0}(β₂)`, with `m = i - l`, for all real angles. -/
theorem legendre_addition (l : ℕ) (β₁ β₂ α : ℝ) :
    (legendrePoly l).eval
        (Real.cos β₁ * Real.cos β₂ - Real.sin β₁ * Real.sin β₂ * Real.cos α) =
      ∑ i ∈ Finset.range (2 * l + 1), (-1) ^ (i + l) * Real.cos (((i : ℝ) - l) * α) *
        smallD (2 * l) i l β₁ * smallD (2 * l) i l β₂ := by
  sorry

/-- **The product formula and the functional equation of the zonal function.**
`P_l(cos θ₁) P_l(cos θ₂) = π⁻¹ ∫_0^π P_l(cos θ₁ cos θ₂ - sin θ₁ sin θ₂ cos φ) dφ`, and
`(2π)⁻¹ ∫_0^{2π} t^l_{00}(g · torusExp t · h) dt = t^l_{00}(g) t^l_{00}(h)`. -/
theorem legendre_product (l : ℕ) (θ₁ θ₂ : ℝ) (g h : SU2) :
    (legendrePoly l).eval (Real.cos θ₁) * (legendrePoly l).eval (Real.cos θ₂) =
      π⁻¹ * ∫ φ in (0 : ℝ)..π, (legendrePoly l).eval
        (Real.cos θ₁ * Real.cos θ₂ - Real.sin θ₁ * Real.sin θ₂ * Real.cos φ) ∧
    ((2 * π)⁻¹ : ℂ) * ∫ t in (0 : ℝ)..(2 * π),
        matrixElement (2 * l) ⟨l, by omega⟩ ⟨l, by omega⟩ (g * torusExp t * h) =
      matrixElement (2 * l) ⟨l, by omega⟩ ⟨l, by omega⟩ g *
        matrixElement (2 * l) ⟨l, by omega⟩ ⟨l, by omega⟩ h := by
  sorry

/-- **Schur orthogonality in coordinates.** -/
theorem integral_matrixElement_mul_conj (d d' : ℕ) (i j : Fin (d + 1)) (i' j' : Fin (d' + 1)) :
    ∫ g, matrixElement d i j g * conj (matrixElement d' i' j' g) ∂haarProb SU2 =
      if d = d' ∧ (i : ℕ) = i' ∧ (j : ℕ) = j' then ((d + 1 : ℕ) : ℂ)⁻¹ else 0 := by
  sorry

/-- **Orthogonality of `d^j_{m'm}` for fixed `(m', m)`.** If the weights agree,
`2i - d = 2i' - d'` and `2k - d = 2k' - d'`, then
`∫_0^π d^j_{m'm}(β) d^{j'}_{m'm}(β) sin β dβ = 2/(2j+1) δ_{jj'}`. -/
theorem integral_smallD_mul_smallD (d d' i k i' k' : ℕ) (hi : i ≤ d) (hk : k ≤ d)
    (hi' : i' ≤ d') (hk' : k' ≤ d') (hm : 2 * (i : ℤ) - d = 2 * i' - d')
    (hn : 2 * (k : ℤ) - d = 2 * k' - d') :
    ∫ β in (0 : ℝ)..π, smallD d i k β * smallD d' i' k' β * Real.sin β =
      if d = d' then 2 / (d + 1) else 0 := by
  sorry

/-- **Plancherel on SU(2).** For `f ∈ L²(SU(2))`,
`∫ |f|² = Σ_{l,m,n} (2l+1) |∫ f conj t^l_{mn}|²`. -/
theorem hasSum_plancherel (f : SU2 → ℂ) (hf : MemLp f 2 (haarProb SU2)) :
    HasSum (fun x : Σ d : ℕ, Fin (d + 1) × Fin (d + 1) ↦
        ((x.1 + 1 : ℕ) : ℝ) *
          ‖∫ g, f g * conj (matrixElement x.1 x.2.1 x.2.2 g) ∂haarProb SU2‖ ^ 2)
      (∫ g, ‖f g‖ ^ 2 ∂haarProb SU2) := by
  sorry

/-! ## Layer 4: the Lie-algebra action -/

/-- `i J_x` in the basis `e_i`, `m = i - d/2`: the derivative of `T(aTheta t)` at `0`. -/
def lieMatrix₁ (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun k j ↦
  if (k : ℕ) + 1 = j then I / 2 * Real.sqrt ((j : ℕ) * (d - j + 1 : ℕ))
  else if (k : ℕ) = j + 1 then I / 2 * Real.sqrt ((d - j : ℕ) * ((j : ℕ) + 1))
  else 0

/-- `i J_y` in the basis `e_i`: the derivative of `T(bBeta t)` at `0` (Edmonds (4.1.9)). -/
def lieMatrix₂ (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ := fun k j ↦
  if (k : ℕ) + 1 = j then -(1 / 2 * Real.sqrt ((j : ℕ) * (d - j + 1 : ℕ)))
  else if (k : ℕ) = j + 1 then 1 / 2 * Real.sqrt ((d - j : ℕ) * ((j : ℕ) + 1))
  else 0

/-- `i J_z` in the basis `e_i`: the diagonal `i m`, `m = j - d/2`. -/
def lieMatrix₃ (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.diagonal fun j ↦ I * edWeight d j

/-- **The infinitesimal operators.** The right derivatives of the matrix elements along
`aTheta t = exp(itJ_x)`, `bBeta t = exp(itJ_y)` and `torusExp (t/2) = exp(itJ_z)` are given by
the three matrices. -/
theorem hasDerivAt_matrixElement (d : ℕ) (i k : Fin (d + 1)) (g : SU2) :
    HasDerivAt (fun t ↦ matrixElement d i k (g * aTheta t))
      (∑ μ, matrixElement d i μ g * lieMatrix₁ d μ k) 0 ∧
    HasDerivAt (fun t ↦ matrixElement d i k (g * bBeta t))
      (∑ μ, matrixElement d i μ g * lieMatrix₂ d μ k) 0 ∧
    HasDerivAt (fun t ↦ matrixElement d i k (g * torusExp (t / 2)))
      (∑ μ, matrixElement d i μ g * lieMatrix₃ d μ k) 0 := by
  sorry

/-- **Commutation relations and the Casimir.** `[iJ_x, iJ_y] = -iJ_z` cyclically, and
`(iJ_x)² + (iJ_y)² + (iJ_z)² = -j(j+1)`. -/
theorem lieMatrix_comm_casimir (d : ℕ) :
    lieMatrix₁ d * lieMatrix₂ d - lieMatrix₂ d * lieMatrix₁ d = -lieMatrix₃ d ∧
    lieMatrix₂ d * lieMatrix₃ d - lieMatrix₃ d * lieMatrix₂ d = -lieMatrix₁ d ∧
    lieMatrix₃ d * lieMatrix₁ d - lieMatrix₁ d * lieMatrix₃ d = -lieMatrix₂ d ∧
    lieMatrix₁ d * lieMatrix₁ d + lieMatrix₂ d * lieMatrix₂ d + lieMatrix₃ d * lieMatrix₃ d =
      -(((d : ℂ) / 2) * ((d : ℂ) / 2 + 1)) • (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
  sorry

/-- **The differential equation of `d^j_{m'm}`.** On `(0, π)`,
`d'' + cot β d' - (m'² + m² - 2m'm cos β)/sin² β · d = -j(j+1) d`. -/
theorem smallD_ode (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) {β : ℝ} (hβ : β ∈ Ioo 0 π) :
    deriv (deriv (smallD d i k)) β + Real.cot β * deriv (smallD d i k) β -
        (edWeight d i ^ 2 + edWeight d k ^ 2 - 2 * edWeight d i * edWeight d k * Real.cos β) /
          Real.sin β ^ 2 * smallD d i k β =
      -((d / 2 : ℝ) * (d / 2 + 1)) * smallD d i k β := by
  sorry

/-- The derivative of `f` at `g` along the right translates `g * Y t`. -/
def rightField (Y : ℝ → SU2) (f : SU2 → ℂ) (g : SU2) : ℂ :=
  deriv (fun t ↦ f (g * Y t)) 0

/-- The derivative of `f` at `g` along the left translates `Y t * g`. -/
def leftField (Y : ℝ → SU2) (f : SU2 → ℂ) (g : SU2) : ℂ :=
  deriv (fun t ↦ f (Y t * g)) 0

/-- **The Casimir of the right regular representation**, `Σ_k X_k²` for the one-parameter
subgroups `aTheta t = exp(itJ_x)`, `bBeta t = exp(itJ_y)`, `torusExp (t/2) = exp(itJ_z)`. -/
def rightCasimir (f : SU2 → ℂ) (g : SU2) : ℂ :=
  rightField aTheta (rightField aTheta f) g + rightField bBeta (rightField bBeta f) g +
    rightField (fun t ↦ torusExp (t / 2)) (rightField (fun t ↦ torusExp (t / 2)) f) g

/-- **The Casimir of the left regular representation**, built from left translates. -/
def leftCasimir (f : SU2 → ℂ) (g : SU2) : ℂ :=
  leftField aTheta (leftField aTheta f) g + leftField bBeta (leftField bBeta f) g +
    leftField (fun t ↦ torusExp (t / 2)) (leftField (fun t ↦ torusExp (t / 2)) f) g

/-- **The Laplacian of SU(2) in Euler angles**, on functions of `p = (α, β, γ)`:
`∂²_β + cot β ∂_β + sin⁻² β (∂²_α - 2 cos β ∂_α ∂_γ + ∂²_γ)`. Meaningful for `0 < β < π`. -/
def eulerLaplacian (F : ℝ × ℝ × ℝ → ℂ) (p : ℝ × ℝ × ℝ) : ℂ :=
  deriv (fun b ↦ deriv (fun b' ↦ F (p.1, b', p.2.2)) b) p.2.1 +
    (Real.cot p.2.1 : ℂ) * deriv (fun b ↦ F (p.1, b, p.2.2)) p.2.1 +
    (deriv (fun a ↦ deriv (fun a' ↦ F (a', p.2.1, p.2.2)) a) p.1 -
        2 * (Real.cos p.2.1 : ℂ) * deriv (fun c ↦ deriv (fun a ↦ F (a, p.2.1, c)) p.1) p.2.2 +
        deriv (fun c ↦ deriv (fun c' ↦ F (p.1, p.2.1, c')) c) p.2.2) /
      (Real.sin p.2.1 : ℂ) ^ 2

/-- **The Laplace–Beltrami operator of `S²` in polar coordinates** `q = (θ, φ)`:
`∂²_θ + cot θ ∂_θ + sin⁻² θ ∂²_φ`. Meaningful for `0 < θ < π`. -/
def sphereLaplacian (u : ℝ × ℝ → ℂ) (q : ℝ × ℝ) : ℂ :=
  deriv (fun θ ↦ deriv (fun θ' ↦ u (θ', q.2)) θ) q.1 +
    (Real.cot q.1 : ℂ) * deriv (fun θ ↦ u (θ, q.2)) q.1 +
    deriv (fun φ ↦ deriv (fun φ' ↦ u (q.1, φ')) φ) q.2 / (Real.sin q.1 : ℂ) ^ 2

/-- **The Casimir in Euler angles.** On the open chart `0 < β < π`, for `f` whose pullback by
`eulerD` is `C²` there, the Casimirs of the right and of the left regular representation both
equal `eulerLaplacian` of the pullback. -/
theorem casimir_eulerD (f : SU2 → ℂ)
    (hf : ContDiffOn ℝ 2 (fun p : ℝ × ℝ × ℝ ↦ f (eulerD p.1 p.2.1 p.2.2))
      (univ ×ˢ Ioo 0 π ×ˢ univ))
    {p : ℝ × ℝ × ℝ} (hp : p.2.1 ∈ Ioo 0 π) :
    rightCasimir f (eulerD p.1 p.2.1 p.2.2) =
      eulerLaplacian (fun q ↦ f (eulerD q.1 q.2.1 q.2.2)) p ∧
    leftCasimir f (eulerD p.1 p.2.1 p.2.2) =
      eulerLaplacian (fun q ↦ f (eulerD q.1 q.2.1 q.2.2)) p := by
  sorry

/-- **Matrix elements are Casimir eigenfunctions.** `D^j_{m'm}` is an eigenfunction of both
Casimirs on all of SU(2), and of `eulerLaplacian` on the chart, with eigenvalue `-j(j+1)`. -/
theorem eulerLaplacian_matrixElement (d : ℕ) (i k : Fin (d + 1)) (g : SU2)
    {p : ℝ × ℝ × ℝ} (hp : p.2.1 ∈ Ioo 0 π) :
    rightCasimir (matrixElement d i k) g =
      -((d / 2 : ℂ) * (d / 2 + 1)) * matrixElement d i k g ∧
    leftCasimir (matrixElement d i k) g =
      -((d / 2 : ℂ) * (d / 2 + 1)) * matrixElement d i k g ∧
    eulerLaplacian (fun q ↦ matrixElement d i k (eulerD q.1 q.2.1 q.2.2)) p =
      -((d / 2 : ℂ) * (d / 2 + 1)) * matrixElement d i k (eulerD p.1 p.2.1 p.2.2) := by
  sorry

/-- **The first-order recurrence in the column index.** For every real `β`,
`d/dβ d_{m'm} = ½ (√((j-m)(j+m+1)) d_{m',m+1} - √((j+m)(j-m+1)) d_{m',m-1})`; with `m = k - j`
the neighbours are the columns `k + 1` and `k - 1` (the coefficients vanish at the ends). -/
theorem hasDerivAt_smallD (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) (β : ℝ) :
    HasDerivAt (smallD d i k)
      (1 / 2 * (Real.sqrt ((d - k : ℕ) * (k + 1)) * smallD d i (k + 1) β -
        Real.sqrt (k * (d - k + 1 : ℕ)) * smallD d i (k - 1) β)) β := by
  sorry

/-- **The generating function for a fixed column** (Edmonds (4.1.14) at `x₋ = 1`, `x₊ = w`).
`(w cos(β/2) - sin(β/2))^k (w sin(β/2) + cos(β/2))^{d-k} / √(k!(d-k)!)
  = Σ_i w^i d_{ik}(β) / √(i!(d-i)!)`. -/
theorem generating_function (d k : ℕ) (hk : k ≤ d) (β : ℝ) (w : ℂ) :
    (w * Real.cos (β / 2) - Real.sin (β / 2)) ^ k *
        (w * Real.sin (β / 2) + Real.cos (β / 2)) ^ (d - k) /
        (Real.sqrt (k.factorial * (d - k).factorial) : ℂ) =
      ∑ i ∈ Finset.range (d + 1), w ^ i * (smallD d i k β : ℂ) /
        (Real.sqrt (i.factorial * (d - i).factorial) : ℂ) := by
  sorry

/-! ## Layer 5: characters and the column index -/

/-- **Characters are Chebyshev polynomials.** `χ_j(g) = Σ_m D^j_{mm}(g)` is Tau Ceti's
character of `Sym^d`, equals `U_{2j}(tr g / 2)`, and in Euler angles
`U_{2j}(cos(β/2) cos((α+γ)/2))`. -/
theorem sum_matrixElement_self (d : ℕ) (g : SU2) (α β γ : ℝ) :
    ∑ i, matrixElement d i i g = (symPower d).character g ∧
    ∑ i, matrixElement d i i g =
      (Chebyshev.U ℂ d).eval (Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) / 2) ∧
    ∑ i, matrixElement d i i (eulerD α β γ) =
      (Chebyshev.U ℝ d).eval (Real.cos (β / 2) * Real.cos ((α + γ) / 2)) := by
  sorry

/-- The Krawtchouk polynomial
`K_s(x; p, N) = Σ_{k ≤ s} (-s)_k (-x)_k / ((-N)_k k!) p^{-k}`, for `s ≤ N` and `p ≠ 0`. -/
def krawtchouk (N s : ℕ) (p x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (s + 1),
    (ascPochhammer ℝ k).eval (-(s : ℝ)) * (ascPochhammer ℝ k).eval (-x) /
      ((ascPochhammer ℝ k).eval (-(N : ℝ)) * k.factorial) * (p⁻¹) ^ k

/-- **Matrix elements as Krawtchouk polynomials of the column index.** For `0 < β < π` and
`i, k ≤ d`, with `s = sin(β/2)`, `c = cos(β/2)`:
`d_{ik}(β) c^d = (-1)^k d! / √(i! k! (d-i)! (d-k)!) s^{i+k} c^{2d-i-k} K_i(k; s², d)`. -/
theorem smallD_eq_krawtchouk (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) {β : ℝ} (hβ : β ∈ Ioo 0 π) :
    smallD d i k β * Real.cos (β / 2) ^ d =
      (-1) ^ k * d.factorial /
          Real.sqrt (i.factorial * k.factorial * (d - i).factorial * (d - k).factorial) *
        Real.sin (β / 2) ^ (i + k) * Real.cos (β / 2) ^ (2 * d - i - k) *
        krawtchouk d i (Real.sin (β / 2) ^ 2) k := by
  sorry

/-- **Krawtchouk orthogonality, from unitarity.** For `0 < p < 1` and `s, q ≤ N`. -/
theorem krawtchouk_orthogonal (N s q : ℕ) (hs : s ≤ N) (hq : q ≤ N) {p : ℝ}
    (hp : p ∈ Ioo 0 1) :
    ∑ x ∈ Finset.range (N + 1), (N.choose x : ℝ) * p ^ x * (1 - p) ^ (N - x) *
        krawtchouk N s p x * krawtchouk N q p x =
      if s = q then ((1 - p) / p) ^ s / N.choose s else 0 := by
  sorry

/-! ## Layer 6: the sphere and the Gel'fand pair -/

/-- The image `R(g) e₃` of the north pole under the rotation `toSO3 g`. -/
def orbitPoint (g : SU2) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ((toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ![0, 0, 1])

/-- **The spherical harmonic** `Y_l^m`, `m = i - l`, as a polynomial on `ℝ³`:
`N_{l|m|} w^{|m|} P_l^{(|m|)}(x₃)` with `w = -(x₁ + i x₂)` for `m ≥ 0` (Condon–Shortley phase)
and `w = x₁ - i x₂` for `m < 0`, `N_{lk} = √((2l+1)/(4π) (l-k)!/(l+k)!)`. -/
def sphericalHarmonic (l : ℕ) (i : ℕ) (x : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (Real.sqrt ((2 * l + 1) / (4 * π) *
      ((l - Int.natAbs ((i : ℤ) - l)).factorial /
        (l + Int.natAbs ((i : ℤ) - l)).factorial)) : ℂ) *
    (if l ≤ i then (-(x 0 + I * x 1)) ^ (i - l) else (x 0 - I * x 1) ^ (l - i)) *
    ((((derivative^[Int.natAbs ((i : ℤ) - l)]) (legendrePoly l)).eval (x 2) : ℝ) : ℂ)

/-- The point of `S²` with polar angle `θ` and azimuth `φ`. -/
def spherePoint (θ φ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![Real.sin θ * Real.cos φ, Real.sin θ * Real.sin φ, Real.cos θ]

/-- **Spherical harmonics are matrix elements** (Edmonds (4.1.25), with Edmonds's `Y_{lm}` equal
to DLMF's `Y_l^m`). With `m = i - l`:
`D^l_{m0}(αβγ) = (-1)^m √(4π/(2l+1)) Y_l^m(β, α)`,
`D^l_{0m}(αβγ) = √(4π/(2l+1)) Y_l^m(β, γ)`, `Y_l^m(R(g) e₃) = √((2l+1)/(4π)) conj D^l_{m0}(g)`,
and the rotation law `Y_l^m(R(g)⁻¹ x) = Σ_{m'} D^l_{m'm}(g) Y_l^{m'}(x)`. -/
theorem sphericalHarmonic_matrixElement (l : ℕ) (i : Fin (2 * l + 1)) (α β γ : ℝ) (g : SU2)
    (x : EuclideanSpace ℝ (Fin 3)) :
    matrixElement (2 * l) i ⟨l, by omega⟩ (eulerD α β γ) =
      (-1) ^ (i + l : ℕ) * Real.sqrt (4 * π / (2 * l + 1)) *
        sphericalHarmonic l i (spherePoint β α) ∧
    matrixElement (2 * l) ⟨l, by omega⟩ i (eulerD α β γ) =
      Real.sqrt (4 * π / (2 * l + 1)) * sphericalHarmonic l i (spherePoint β γ) ∧
    sphericalHarmonic l i (orbitPoint g) =
      Real.sqrt ((2 * l + 1) / (4 * π)) * conj (matrixElement (2 * l) i ⟨l, by omega⟩ g) ∧
    sphericalHarmonic l i
        (WithLp.toLp 2 ((toSO3 g⁻¹ : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ WithLp.ofLp x)) =
      ∑ j : Fin (2 * l + 1), matrixElement (2 * l) j i g * sphericalHarmonic l j x := by
  sorry

/-- **The Laplacian of SU(2) and that of `S²`.** On functions independent of `γ`,
`eulerLaplacian` is `sphereLaplacian` in the polar coordinates `(θ, φ) = (β, α)`; the spherical
harmonic `Y_l^m(spherePoint θ φ)` has eigenvalue `-l(l+1)`, so by
`sphericalHarmonic_matrixElement` the column `D^l_{m0}` is the lift of a Laplace–Beltrami
eigenfunction. -/
theorem eulerLaplacian_sphere (u : ℝ × ℝ → ℂ) (p : ℝ × ℝ × ℝ) (l : ℕ) (i : Fin (2 * l + 1))
    {q : ℝ × ℝ} (hq : q.1 ∈ Ioo 0 π) :
    eulerLaplacian (fun r ↦ u (r.2.1, r.1)) p = sphereLaplacian u (p.2.1, p.1) ∧
    sphereLaplacian (fun r ↦ sphericalHarmonic l i (spherePoint r.1 r.2)) q =
      -((l : ℂ) * (l + 1)) * sphericalHarmonic l i (spherePoint q.1 q.2) := by
  sorry

/-- **Orthonormality and completeness on `S²`.** For the surface measure (total mass `4π`), the
`Y_l^m` are orthonormal, and a square-integrable function orthogonal to all of them vanishes
almost everywhere. -/
theorem sphericalHarmonic_orthonormal_complete :
    (∀ (l l' : ℕ) (i : Fin (2 * l + 1)) (i' : Fin (2 * l' + 1)),
      ∫ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          sphericalHarmonic l i x * conj (sphericalHarmonic l' i' x) ∂volume.toSphere =
        if l = l' ∧ (i : ℕ) = i' then 1 else 0) ∧
    ∀ f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℂ, MemLp f 2 volume.toSphere →
      (∀ (l : ℕ) (i : Fin (2 * l + 1)),
        ∫ x, f x * conj (sphericalHarmonic l i x) ∂volume.toSphere = 0) →
      f =ᵐ[volume.toSphere] 0 := by
  sorry

/-- **The addition theorem for spherical harmonics.** For unit vectors `x, y`,
`Σ_m Y_l^m(x) conj Y_l^m(y) = (2l+1)/(4π) P_l(x · y)`. -/
theorem sum_sphericalHarmonic_mul_conj (l : ℕ) (x y : EuclideanSpace ℝ (Fin 3))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∑ i ∈ Finset.range (2 * l + 1), sphericalHarmonic l i x * conj (sphericalHarmonic l i y) =
      ((2 * l + 1) / (4 * π) * (legendrePoly l).eval (inner ℝ x y) : ℝ) := by
  sorry

/-- **Solid harmonics are harmonic.** `‖x‖^l Y_l^m(x/‖x‖)` has zero Euclidean Laplacian away from
the origin. -/
theorem laplacian_solidHarmonic (l i : ℕ) (hi : i ≤ 2 * l) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ≠ 0) :
    Laplacian.laplacian
        (fun y : EuclideanSpace ℝ (Fin 3) ↦ (‖y‖ ^ l : ℂ) * sphericalHarmonic l i (‖y‖⁻¹ • y)) x =
      0 := by
  sorry

/-- Convolution on `SU(2)` for the normalized Haar measure. -/
def conv (f₁ f₂ : SU2 → ℂ) (g : SU2) : ℂ :=
  ∫ h, f₁ h * f₂ (h⁻¹ * g) ∂haarProb SU2

/-- **Gel'fand's criterion and the commutative algebra.** Every `g⁻¹` lies in `T g T` for the
torus `T` (the preimage of `SO(2)`); hence convolution of continuous bi-`T`-invariant functions
is commutative. -/
theorem gelfand_pair :
    (∀ g : SU2, ∃ k₁ ∈ torus, ∃ k₂ ∈ torus, k₁ * g * k₂ = g⁻¹) ∧
    ∀ f₁ f₂ : SU2 → ℂ, Continuous f₁ → Continuous f₂ →
      (∀ k₁ ∈ torus, ∀ k₂ ∈ torus, ∀ g, f₁ (k₁ * g * k₂) = f₁ g) →
      (∀ k₁ ∈ torus, ∀ k₂ ∈ torus, ∀ g, f₂ (k₁ * g * k₂) = f₂ g) →
      conv f₁ f₂ = conv f₂ f₁ := by
  sorry

/-! ## Supplier contracts consumed (README, Exact supplier contracts) -/

#check @TauCeti.SU2.symPowerModel
#check @TauCeti.SU2.weightBasis
#check @TauCeti.SU2.continuous_symPowerModel
#check @TauCeti.SU2.isIrreducible_symPowerModel
#check @TauCeti.SU2.existsUnique_nonempty_equiv_symPower
#check @TauCeti.SU2.torusExp
#check @TauCeti.SU2.torus
#check @TauCeti.SU2.toSO3
#check @TauCeti.SU2.coe_toSO3_torusHom
#check @TauCeti.SU2.toSO3_surjective
#check @TauCeti.SU2.ker_toSO3
#check @TauCeti.SU2.weyl_integration_formula
#check @TauCeti.SU2.character_symPower_eq_chebyshevU_eval
#check @TauCeti.haarProb
#check @TauCeti.IrrepModel
#check @TauCeti.IsIrrepSkeleton
#check @TauCeti.peterWeylBasis
#check @TauCeti.coe_peterWeylBasis
#check @ContRepresentation.schur_orthogonality
#check @ContinuousLinearEquiv.congr
#check @ContinuousLinearEquiv.continuous_congr
#check @ContRepresentation.matrixCoeff
#check @ContRepresentation.IsUnitary
#check @Polynomial.shiftedLegendre
#check @Polynomial.Chebyshev.U
#check @ordinaryHypergeometric
#check @MeasureTheory.Measure.toSphere
#check @Laplacian.laplacian

end SFVK.SU2MatrixElements
