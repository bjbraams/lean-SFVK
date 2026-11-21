/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Basic

/-!
# Coordinates for noncompact groups

The coordinate groups for the function-space models are `SU(1,1)`, the Euclidean motion
groups, the affine group, and `ISO(1,1)`. The file records their matrix and semidirect
product descriptions, the rotation and boost conventions, and the topological and
Haar measure properties used in the model statements. Section numbers refer to the
function-space roadmap.
-/

@[expose] public section

noncomputable section

namespace SFVK.FunctionSpaceModels

open MeasureTheory Filter Topology Set Matrix AddCircle
open scoped Real ComplexConjugate ComplexOrder ENNReal NNReal InnerProductSpace ContDiff

/-! ## Layer 0: groups in coordinates -/

/-- README 0.1. The group `SU(1,1)` of matrices `[[a, b], [conj b, conj a]]` of determinant `1`,
as a subgroup of `SL(2, ℂ)`. -/
def su11 : Subgroup (SpecialLinearGroup (Fin 2) ℂ) where
  carrier := {g | g.1 1 0 = conj (g.1 0 1) ∧ g.1 1 1 = conj (g.1 0 0)}
  mul_mem' := by
    rintro g h ⟨hg₁, hg₂⟩ ⟨hh₁, hh₂⟩
    show (g.1 * h.1) 1 0 = conj ((g.1 * h.1) 0 1) ∧ (g.1 * h.1) 1 1 = conj ((g.1 * h.1) 0 0)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hg₁, hg₂, hh₁, hh₂, map_add, map_mul,
      Complex.conj_conj]
    constructor <;> ring
  one_mem' := by simp
  inv_mem' := by
    rintro g ⟨hg₁, hg₂⟩
    show (adjugate g.1) 1 0 = conj ((adjugate g.1) 0 1) ∧
      (adjugate g.1) 1 1 = conj ((adjugate g.1) 0 0)
    simp [Matrix.adjugate_fin_two, hg₁, hg₂]

/-- README 0.1. `SU(1,1)` as a type, with the subspace topology of `SL(2, ℂ)`. -/
abbrev SU11 := ↥su11

/-- The Borel σ-algebra on `SU(1,1)`. -/
instance : MeasurableSpace SU11 := borel SU11

instance : BorelSpace SU11 := ⟨rfl⟩

/-- The entry `a = g₀₀` of `g = [[a, b], [conj b, conj a]]`. -/
def entryA (g : SU11) : ℂ := g.1.1 0 0

/-- The entry `b = g₀₁` of `g = [[a, b], [conj b, conj a]]`. -/
def entryB (g : SU11) : ℂ := g.1.1 0 1

/-- The element `[[a, b], [conj b, conj a]]` of `SU(1,1)` for `|a|² - |b|² = 1`. -/
def su11Mk (a b : ℂ) (h : Complex.normSq a - Complex.normSq b = 1) : SU11 :=
  ⟨⟨!![a, b; conj b, conj a], by
      rw [Matrix.det_fin_two_of, Complex.mul_conj, Complex.mul_conj]
      exact_mod_cast h⟩, by
    show _ ∧ _
    simp⟩

/-- README 0.1. The rotation `k_α = diag(e^{iα/2}, e^{-iα/2})`, the matrix of Roadmap 1's
`torusExp (α/2)`. -/
def rot (α : ℝ) : SU11 :=
  su11Mk (Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I)) 0 (by
    rw [map_zero, sub_zero, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num)

/-- README 0.1. The boost `b_t = [[cosh (t/2), sinh (t/2)], [sinh (t/2), cosh (t/2)]]`. -/
def boost (t : ℝ) : SU11 :=
  su11Mk (Real.cosh (t / 2) : ℂ) (Real.sinh (t / 2) : ℂ) (by
    rw [Complex.normSq_ofReal, Complex.normSq_ofReal]
    linear_combination Real.cosh_sq_sub_sinh_sq (t / 2))

/-- README 0.1. The second boost `[[cosh (t/2), i sinh (t/2)], [-i sinh (t/2), cosh (t/2)]]`,
the value of Roadmap 1's `[[cos (β/2), sin (β/2)], [-sin (β/2), cos (β/2)]]` at `β = it`. -/
def boostY (t : ℝ) : SU11 :=
  su11Mk (Real.cosh (t / 2) : ℂ) ((Real.sinh (t / 2) : ℂ) * Complex.I) (by
    rw [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal, Complex.normSq_ofReal]
    linear_combination Real.cosh_sq_sub_sinh_sq (t / 2))

/-- README 0.1. The Euler parametrization `g(α, t, γ) = k_α b_t k_γ`, with the letters and order
of Roadmap 1's `eulerD α β γ = k_α b_β k_γ`. -/
def eulerSU11 (α t γ : ℝ) : SU11 := rot α * boost t * rot γ

/-- README 0.1. The circle subgroup `K = {diag(u, conj u)}`, the entries `b = 0`. -/
def su11K : Subgroup SU11 where
  carrier := {g | g.1.1 0 1 = 0}
  mul_mem' := by
    rintro g h (hg : g.1.1 0 1 = 0) (hh : h.1.1 0 1 = 0)
    show (g.1.1 * h.1.1) 0 1 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hg, hh]
  one_mem' := by
    show (1 : SpecialLinearGroup (Fin 2) ℂ).1 0 1 = 0
    simp
  inv_mem' := by
    rintro g (hg : g.1.1 0 1 = 0)
    show (adjugate g.1.1) 0 1 = 0
    simp [Matrix.adjugate_fin_two, hg]

/-- README 0.1. **Euler factorization.** The matrix of `k_α b_t k_γ`. -/
theorem eulerSU11_coe (α t γ : ℝ) :
    (eulerSU11 α t γ).1.1 =
      !![(Real.cosh (t / 2) : ℂ) * Complex.exp ((((α + γ) / 2 : ℝ) : ℂ) * Complex.I),
        (Real.sinh (t / 2) : ℂ) * Complex.exp ((((α - γ) / 2 : ℝ) : ℂ) * Complex.I);
        (Real.sinh (t / 2) : ℂ) * Complex.exp ((((γ - α) / 2 : ℝ) : ℂ) * Complex.I),
        (Real.cosh (t / 2) : ℂ) * Complex.exp (((-(α + γ) / 2 : ℝ) : ℂ) * Complex.I)] := by
  sorry

/-- README 0.1. **Euler angles.** Every element of `SU(1,1)` is `g(α, t, γ)` with
`0 ≤ α < 2π`, `t ≥ 0`, `-2π ≤ γ < 2π`, and the angles are unique when `t > 0`. -/
theorem eulerSU11_surjective_unique :
    (∀ g : SU11, ∃ α ∈ Ico 0 (2 * π), ∃ t, 0 ≤ t ∧ ∃ γ ∈ Ico (-(2 * π)) (2 * π),
      g = eulerSU11 α t γ) ∧
    ∀ α₁ ∈ Ico 0 (2 * π), ∀ α₂ ∈ Ico 0 (2 * π), ∀ t₁ t₂ : ℝ, 0 < t₁ → 0 < t₂ →
      ∀ γ₁ ∈ Ico (-(2 * π)) (2 * π), ∀ γ₂ ∈ Ico (-(2 * π)) (2 * π),
        eulerSU11 α₁ t₁ γ₁ = eulerSU11 α₂ t₂ γ₂ → α₁ = α₂ ∧ t₁ = t₂ ∧ γ₁ = γ₂ := by
  sorry

/-- README 0.1. **Conversion to the `SU(2)` Euler angles.** Roadmap 1's middle factor
`[[cos (β/2), sin (β/2)], [-sin (β/2), cos (β/2)]]` at `β = it` is `boostY t`, and
`k_α · (its value at β = it) · k_γ = g(α + π/2, t, γ - π/2)`: the phase `π/2` moves between the
outer angles. -/
theorem eulerSU11_continuation (α t γ : ℝ) :
    let bIt : Matrix (Fin 2) (Fin 2) ℂ :=
      !![Complex.cos ((t : ℂ) * Complex.I / 2), Complex.sin ((t : ℂ) * Complex.I / 2);
        -Complex.sin ((t : ℂ) * Complex.I / 2), Complex.cos ((t : ℂ) * Complex.I / 2)]
    (boostY t).1.1 = bIt ∧
      (rot α).1.1 * bIt * (rot γ).1.1 = (eulerSU11 (α + π / 2) t (γ - π / 2)).1.1 := by
  sorry

/-- README 0.1. The Cayley matrix `C = [[1, -i], [1, i]]`. -/
def cayleyMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![1, -Complex.I; 1, Complex.I]

/-- README 0.1. **Cayley transform.** Conjugation by `C` maps `SL(2, ℝ)` onto `SU(1,1)`. -/
theorem mem_su11_iff_cayley (g : SpecialLinearGroup (Fin 2) ℂ) :
    g ∈ su11 ↔ ∃ h : SpecialLinearGroup (Fin 2) ℝ,
      g.1 = cayleyMatrix * h.1.map (fun x : ℝ => (x : ℂ)) * cayleyMatrix⁻¹ := by
  sorry

/-- The Euler-angle domain `[0, 2π) × (0, ∞) × [-2π, 2π)`. -/
def eulerDomain : Set (ℝ × ℝ × ℝ) := Ico 0 (2 * π) ×ˢ Ioi 0 ×ˢ Ico (-(2 * π)) (2 * π)

/-- README 0.1. The Haar measure `(8π²)⁻¹ sinh t dα dt dγ` in Euler angles. -/
def su11Haar : Measure SU11 :=
  Measure.map (fun p : ℝ × ℝ × ℝ => eulerSU11 p.1 p.2.1 p.2.2)
    ((volume.restrict eulerDomain).withDensity
      fun p => ENNReal.ofReal (Real.sinh p.2.1 / (8 * π ^ 2)))

/-- README 0.1. **Haar measure of `SU(1,1)`.** The Euler-angle measure is a Haar measure and is
right invariant; `SU(1,1)` is unimodular. -/
theorem su11Haar_isHaarMeasure : su11Haar.IsHaarMeasure ∧ su11Haar.IsMulRightInvariant := by
  sorry

/-- README 0.1. The basis `b₁` of `su(1,1)`. -/
def lieB₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1 / 2; 1 / 2, 0]

/-- README 0.1. The basis `b₂` of `su(1,1)`. -/
def lieB₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I / 2; -Complex.I / 2, 0]

/-- README 0.1. The basis `b₃` of `su(1,1)`. -/
def lieB₃ : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I / 2, 0; 0, -Complex.I / 2]

/-- README 0.1. **Lie algebra of `SU(1,1)`.** The brackets of the basis, and `boost`, `boostY`,
`rot` are one-parameter subgroups with tangents `b₁`, `b₂`, `b₃`. -/
theorem su11_lieBasis :
    (lieB₁ * lieB₂ - lieB₂ * lieB₁ = -lieB₃ ∧ lieB₂ * lieB₃ - lieB₃ * lieB₂ = lieB₁ ∧
      lieB₃ * lieB₁ - lieB₁ * lieB₃ = lieB₂) ∧
    (∀ s t : ℝ, boost (s + t) = boost s * boost t ∧ boostY (s + t) = boostY s * boostY t ∧
      rot (s + t) = rot s * rot t) ∧
    ∀ i j : Fin 2, HasDerivAt (fun s => (boost s).1.1 i j) (lieB₁ i j) 0 ∧
      HasDerivAt (fun s => (boostY s).1.1 i j) (lieB₂ i j) 0 ∧
      HasDerivAt (fun s => (rot s).1.1 i j) (lieB₃ i j) 0 := by
  sorry

/-- README 0.2. The left Haar measure `a⁻² da db` of the `ax + b` group in coordinates. -/
def axbLeftHaar : Measure (ℝ × ℝ) :=
  (volume.restrict {p : ℝ × ℝ | 0 < p.1}).withDensity fun p => ENNReal.ofReal (p.1 ^ 2)⁻¹

/-- README 0.2. The right Haar measure `a⁻¹ da db` of the `ax + b` group in coordinates. -/
def axbRightHaar : Measure (ℝ × ℝ) :=
  (volume.restrict {p : ℝ × ℝ | 0 < p.1}).withDensity fun p => ENNReal.ofReal p.1⁻¹

/-- README 0.2. **Haar measures of the `ax + b` group.** With `(a, b)(a', b') = (aa', ab' + b)`,
`a⁻² da db` is left invariant, `a⁻¹ da db` is right invariant, and the left measure is not
right invariant. -/
theorem axb_haar :
    (∀ a b : ℝ, 0 < a →
      Measure.map (fun p : ℝ × ℝ => (a * p.1, a * p.2 + b)) axbLeftHaar = axbLeftHaar) ∧
    (∀ a b : ℝ, 0 < a →
      Measure.map (fun p : ℝ × ℝ => (p.1 * a, p.1 * b + p.2)) axbRightHaar = axbRightHaar) ∧
    ∀ a b : ℝ, 0 < a → a ≠ 1 →
      Measure.map (fun p : ℝ × ℝ => (p.1 * a, p.1 * b + p.2)) axbLeftHaar ≠ axbLeftHaar := by
  sorry

/-- README 0.2. **Haar measure of the Heisenberg group.** Lebesgue measure in the coordinates
`(x, y, z)` of Tau Ceti's `HeisenbergGroup ℝ` is left and right invariant. -/
theorem heisenberg_haar (g : TauCeti.HeisenbergGroup ℝ) :
    Measure.map (fun p : ℝ × ℝ × ℝ => TauCeti.HeisenbergGroup.equivProd
        (g * TauCeti.HeisenbergGroup.equivProd.symm p)) volume = volume ∧
    Measure.map (fun p : ℝ × ℝ × ℝ => TauCeti.HeisenbergGroup.equivProd
        (TauCeti.HeisenbergGroup.equivProd.symm p * g)) volume = volume := by
  sorry

/-- README 0.2. The oscillator-group matrix `s(w, α, δ)`, in the corrected form of the
Klimyk–Vilenkin parametrization (erratum E01.1.11). -/
def oscillatorMatrix (w : ℂ) (α δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, Complex.exp (-(α : ℂ) * Complex.I) * conj w / 2,
      (δ : ℂ) * Complex.I - (Complex.normSq w : ℂ) / 8;
    0, Complex.exp (-(α : ℂ) * Complex.I), -w / 2;
    0, 0, 1]

/-- README 0.2. **Oscillator group law.** -/
theorem oscillatorMatrix_mul (w₁ w₂ : ℂ) (α₁ α₂ δ₁ δ₂ : ℝ) :
    oscillatorMatrix w₁ α₁ δ₁ * oscillatorMatrix w₂ α₂ δ₂ =
      oscillatorMatrix (w₁ + Complex.exp (-(α₁ : ℂ) * Complex.I) * w₂) (α₁ + α₂)
        (δ₁ + δ₂ - (Complex.exp (-(α₁ : ℂ) * Complex.I) * conj w₁ * w₂).im / 4) := by
  sorry

/-- README 0.3. `SO(n)` as the special orthogonal matrices of Mathlib. -/
abbrev SOn (n : ℕ) := Matrix.specialOrthogonalGroup (Fin n) ℝ

instance (n : ℕ) : MeasurableSpace (SOn n) := borel (SOn n)

instance (n : ℕ) : BorelSpace (SOn n) := ⟨rfl⟩

/-- README 0.3. A matrix of `SO(n)` acting on `ℝⁿ`. -/
def rotE {n : ℕ} (k : SOn n) (a : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin k.1 a

/-- A product of rotations acts by composition on Euclidean vectors. -/
theorem rotE_mul {n : ℕ} (k k' : SOn n) (a : EuclideanSpace ℝ (Fin n)) :
    rotE (k * k') a = rotE k (rotE k' a) := by
  simp only [rotE, Submonoid.coe_mul, toEuclideanLin_eq_toLin_orthonormal]
  rw [Matrix.toLin_mul _ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  rfl

/-- The identity rotation fixes each Euclidean vector. -/
theorem rotE_one {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) : rotE (1 : SOn n) a = a := by
  simp [rotE]

/-- A rotation distributes over vector addition. -/
theorem rotE_add {n : ℕ} (k : SOn n) (a b : EuclideanSpace ℝ (Fin n)) :
    rotE k (a + b) = rotE k a + rotE k b := by
  simp [rotE]

/-- README 0.3. The motion group `M(n) = ℝⁿ ⋊ SO(n)`, with `(a, k)(a', k') = (a + k a', k k')`. -/
@[ext]
structure MotionGroup (n : ℕ) where
  /-- The translation part. -/
  a : EuclideanSpace ℝ (Fin n)
  /-- The rotation part. -/
  k : SOn n

namespace MotionGroup

variable {n : ℕ}

instance : Mul (MotionGroup n) := ⟨fun g h => ⟨g.a + rotE g.k h.a, g.k * h.k⟩⟩

instance : One (MotionGroup n) := ⟨⟨0, 1⟩⟩

instance : Inv (MotionGroup n) := ⟨fun g => ⟨-rotE g.k⁻¹ g.a, g.k⁻¹⟩⟩

/-- The translation of a product in `MotionGroup`. -/
@[simp] theorem mul_a (g h : MotionGroup n) : (g * h).a = g.a + rotE g.k h.a := rfl

/-- The rotation of a product in `MotionGroup`. -/
@[simp] theorem mul_k (g h : MotionGroup n) : (g * h).k = g.k * h.k := rfl

/-- The translation of the identity in `MotionGroup`. -/
@[simp] theorem one_a : (1 : MotionGroup n).a = 0 := rfl

/-- The rotation of the identity in `MotionGroup`. -/
@[simp] theorem one_k : (1 : MotionGroup n).k = 1 := rfl

/-- The translation of the inverse in `MotionGroup`. -/
@[simp] theorem inv_a (g : MotionGroup n) : g⁻¹.a = -rotE g.k⁻¹ g.a := rfl

/-- The rotation of the inverse in `MotionGroup`. -/
@[simp] theorem inv_k (g : MotionGroup n) : g⁻¹.k = g.k⁻¹ := rfl

instance : Group (MotionGroup n) where
  mul_assoc g h l := by
    ext1
    · simp [rotE_add, rotE_mul, add_assoc]
    · simp [mul_assoc]
  one_mul g := by ext1 <;> simp [rotE_one]
  mul_one g := by ext1 <;> simp [rotE]
  inv_mul_cancel g := by
    ext1
    · simp
    · simp

/-- README 0.3. The topology of `ℝⁿ × SO(n)`. -/
instance : TopologicalSpace (MotionGroup n) :=
  TopologicalSpace.induced (fun g => (g.a, g.k)) inferInstance

/-- README 0.3. **`M(n)` is a topological group.** -/
instance : IsTopologicalGroup (MotionGroup n) := by
  sorry

/-- README 0.3. **`M(n)` is locally compact.** -/
instance : LocallyCompactSpace (MotionGroup n) := by
  sorry

instance : MeasurableSpace (MotionGroup n) := borel (MotionGroup n)

instance : BorelSpace (MotionGroup n) := ⟨rfl⟩

end MotionGroup

/-- README 0.3. `ISO(2) = M(2)`. -/
abbrev ISO2 := MotionGroup 2

/-- README 0.3. The Haar measure `da dk` of `M(n)` in coordinates, for a measure `ν` on
`SO(n)`. -/
def motionHaar (n : ℕ) (ν : Measure (SOn n)) : Measure (MotionGroup n) :=
  (volume.prod ν).map fun p => (⟨p.1, p.2⟩ : MotionGroup n)

/-- README 0.3. **Haar measure of `M(n)`; unimodularity.** For the Haar probability measure `ν`
of `SO(n)`, `da dk` is a Haar measure of `M(n)` and is right invariant. -/
theorem motionHaar_isHaarMeasure (n : ℕ) (ν : Measure (SOn n)) [ν.IsHaarMeasure]
    [IsProbabilityMeasure ν] :
    (motionHaar n ν).IsHaarMeasure ∧ (motionHaar n ν).IsMulRightInvariant := by
  sorry

/-- README 0.3. **Polar decomposition of `M(n)`, `n ≥ 2`.** Every `g` is
`(0, k₁)(r e₁, 1)(0, k₂)` with `r = |g.a|`, and `r ≥ 0` is determined by `g`. -/
theorem motionGroup_polar (n : ℕ) (g : MotionGroup (n + 2)) :
    (∃ k₁ k₂ : SOn (n + 2), g = ⟨0, k₁⟩ * ⟨‖g.a‖ • EuclideanSpace.single 0 1, 1⟩ * ⟨0, k₂⟩) ∧
    ∀ (r : ℝ) (k₁ k₂ : SOn (n + 2)), 0 ≤ r →
      g = ⟨0, k₁⟩ * ⟨r • EuclideanSpace.single 0 1, 1⟩ * ⟨0, k₂⟩ → r = ‖g.a‖ := by
  sorry

/-- README 0.3. The Lorentz boost `Λ_s (x, y) = (x cosh s + y sinh s, x sinh s + y cosh s)`. -/
def lorentzBoost (s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * Real.cosh s + p.2 * Real.sinh s, p.1 * Real.sinh s + p.2 * Real.cosh s)

/-- Boosts with added rapidities act by composition. -/
theorem lorentzBoost_add (s s' : ℝ) (p : ℝ × ℝ) :
    lorentzBoost (s + s') p = lorentzBoost s (lorentzBoost s' p) := by
  simp only [lorentzBoost, Real.cosh_add, Real.sinh_add, Prod.mk.injEq]
  constructor <;> ring

/-- README 0.3. The group `ISO(1,1) = ℝ² ⋊ SO₀(1,1)`, with
`(a, s)(a', s') = (a + Λ_s a', s + s')`. -/
@[ext]
structure ISO11 where
  /-- The translation part. -/
  a : ℝ × ℝ
  /-- The rapidity of the boost. -/
  s : ℝ

namespace ISO11

instance : Mul ISO11 := ⟨fun g h => ⟨g.a + lorentzBoost g.s h.a, g.s + h.s⟩⟩

instance : One ISO11 := ⟨⟨0, 0⟩⟩

instance : Inv ISO11 := ⟨fun g => ⟨-lorentzBoost (-g.s) g.a, -g.s⟩⟩

/-- The translation of a product in `ISO11`. -/
@[simp] theorem mul_a (g h : ISO11) : (g * h).a = g.a + lorentzBoost g.s h.a := rfl

/-- The rapidity of a product in `ISO11`. -/
@[simp] theorem mul_s (g h : ISO11) : (g * h).s = g.s + h.s := rfl

instance : Group ISO11 where
  mul_assoc g h l := by
    ext1
    · simp only [mul_a, mul_s, lorentzBoost_add, add_assoc]
      simp only [lorentzBoost, Prod.fst_add, Prod.snd_add, Prod.ext_iff]
      constructor <;> ring
    · simp [add_assoc]
  one_mul g := by
    ext1
    · change (0 : ℝ × ℝ) + lorentzBoost 0 g.a = g.a
      simp [lorentzBoost]
    · change (0 : ℝ) + g.s = g.s
      simp
  mul_one g := by
    ext1
    · change g.a + lorentzBoost g.s 0 = g.a
      simp [lorentzBoost]
    · change g.s + 0 = g.s
      simp
  inv_mul_cancel g := by
    ext1
    · change -lorentzBoost (-g.s) g.a + lorentzBoost (-g.s) g.a = 0
      simp
    · change -g.s + g.s = 0
      simp

/-- README 0.3. The topology of `ℝ² × ℝ`. -/
instance : TopologicalSpace ISO11 := TopologicalSpace.induced (fun g => (g.a, g.s)) inferInstance

/-- README 0.3. **`ISO(1,1)` is a topological group.** -/
instance : IsTopologicalGroup ISO11 := by
  sorry

/-- README 0.3. **`ISO(1,1)` is locally compact.** -/
instance : LocallyCompactSpace ISO11 := by
  sorry

instance : MeasurableSpace ISO11 := borel ISO11

instance : BorelSpace ISO11 := ⟨rfl⟩

end ISO11

/-- README 0.3. **Haar measure of `ISO(1,1)`; unimodularity.** Lebesgue measure `da₁ da₂ ds` is
a Haar measure and is right invariant. -/
theorem iso11Haar_isHaarMeasure :
    let μ : Measure ISO11 := (volume : Measure ((ℝ × ℝ) × ℝ)).map fun p => ⟨p.1, p.2⟩
    μ.IsHaarMeasure ∧ μ.IsMulRightInvariant := by
  sorry

end SFVK.FunctionSpaceModels
