/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# The hyperboloid model of real hyperbolic space

The real hyperbolic space `ℍⁿ` as the upper sheet of `x₀² − x₁² − ⋯ − xₙ² = 1` in
`Fin (n + 1) → ℝ` (the time coordinate has index `0`), with the Lorentz form `[x, y]`, the group
`SO₀(n, 1)` as the subgroup of `SL(n + 1, ℝ)` that preserves the form and maps `ℍⁿ` onto itself,
its rotation subgroup `K ≅ SO(n)` (the stabilizer of `o = e₀`), the distance
`d(x, y) = arcosh [x, y]`, the volume `dx₁ ⋯ dxₙ / x₀`, the Laplace–Beltrami operator computed by
the ambient wave operator on the extension homogeneous of degree `0`, the boundary points
`b̃ = (1, b)`, `b ∈ S^{n−1}`, the Abel transform and the Helgason–Fourier transform.

Sources: Wawrzyńczyk, *Group Representations and Special Functions*, §11.1, (11.1.6), p. 392
(the volume), §11.5, (11.5.1)–(11.5.3), pp. 411–412 (the Laplacian), §18.7, (18.7.12), p. 640
(the Fourier transform); Heckman–Schlichtkrull, *Harmonic Analysis and Special Functions on
Symmetric Spaces*, Part I §5.4, (5.4.3), p. 83 (the Abel transform).

## Main definitions

* `SFVK.RankOne.lorentz`, `SFVK.RankOne.hyperboloid`, `SFVK.RankOne.basePoint`,
  `SFVK.RankOne.hyperbolicDist`.
* `SFVK.RankOne.lorentzGroup`, `SFVK.RankOne.rotationSubgroup`, `SFVK.RankOne.orbitMap`.
* `SFVK.RankOne.hyperboloidChart`, `SFVK.RankOne.hyperbolicMeasure`, `SFVK.RankOne.sphereArea`.
* `SFVK.RankOne.hyperbolicLaplacian`.
* `SFVK.RankOne.boundaryVector`, `SFVK.RankOne.sphereMeasure`.
* `SFVK.RankOne.plancherelConstant`, `SFVK.RankOne.abelTransform`,
  `SFVK.RankOne.helgasonFourier`.
-/

public noncomputable section

open Complex MeasureTheory Set
open scoped Real Matrix

namespace SFVK.RankOne

/-- The Lorentz form `[x, y] = x₀ y₀ − x₁ y₁ − ⋯ − xₙ yₙ`. -/
@[expose]
def lorentz {n : ℕ} (x y : Fin (n + 1) → ℝ) : ℝ :=
  x 0 * y 0 - ∑ i : Fin n, x i.succ * y i.succ

/-- The Lorentz pairing is the time-coordinate product minus the spatial dot product. -/
theorem lorentz_def {n : ℕ} (x y : Fin (n + 1) → ℝ) :
    lorentz x y = x 0 * y 0 - ∑ i : Fin n, x i.succ * y i.succ :=
  rfl

/-- The Lorentz pairing over the reals is symmetric. -/
theorem lorentz_comm {n : ℕ} (x y : Fin (n + 1) → ℝ) : lorentz x y = lorentz y x := by
  simp only [lorentz_def, mul_comm]

/-- The hyperboloid model `ℍⁿ = {x | [x, x] = 1, x₀ > 0}`. -/
@[expose]
def hyperboloid (n : ℕ) : Set (Fin (n + 1) → ℝ) := {x | lorentz x x = 1 ∧ 0 < x 0}

/-- The upper unit hyperboloid consists of positive-time vectors with Lorentz square one. -/
theorem mem_hyperboloid {n : ℕ} {x : Fin (n + 1) → ℝ} :
    x ∈ hyperboloid n ↔ lorentz x x = 1 ∧ 0 < x 0 :=
  Iff.rfl

/-- The base point `o = e₀`. -/
@[expose]
def basePoint (n : ℕ) : Fin (n + 1) → ℝ := Pi.single 0 1

/-- The base point has time coordinate one and vanishing spatial coordinates. -/
theorem basePoint_def (n : ℕ) : basePoint n = Pi.single 0 1 :=
  rfl

/-- Pairing with the base point extracts the time coordinate. -/
theorem lorentz_basePoint_left {n : ℕ} (x : Fin (n + 1) → ℝ) :
    lorentz (basePoint n) x = x 0 := by
  simp [lorentz_def, basePoint_def, Fin.succ_ne_zero]

/-- The base point lies on the upper unit hyperboloid. -/
theorem basePoint_mem_hyperboloid (n : ℕ) : basePoint n ∈ hyperboloid n := by
  refine ⟨?_, ?_⟩
  · rw [lorentz_basePoint_left]
    simp [basePoint_def]
  · simp [basePoint_def]

/-- The hyperbolic distance `d(x, y) = arcosh [x, y]`. -/
@[expose]
def hyperbolicDist {n : ℕ} (x y : Fin (n + 1) → ℝ) : ℝ := Real.arcosh (lorentz x y)

/-- The hyperbolic distance is the inverse hyperbolic cosine of the Lorentz pairing. -/
theorem hyperbolicDist_def {n : ℕ} (x y : Fin (n + 1) → ℝ) :
    hyperbolicDist x y = Real.arcosh (lorentz x y) :=
  rfl

/-- The distance from the base point is `arcosh x₀`. -/
theorem hyperbolicDist_basePoint_left {n : ℕ} (x : Fin (n + 1) → ℝ) :
    hyperbolicDist (basePoint n) x = Real.arcosh (x 0) := by
  rw [hyperbolicDist_def, lorentz_basePoint_left]

/-- The distance from a point of the hyperboloid to itself is zero. -/
theorem hyperbolicDist_self {n : ℕ} {x : Fin (n + 1) → ℝ} (hx : x ∈ hyperboloid n) :
    hyperbolicDist x x = 0 := by
  rw [hyperbolicDist_def, hx.1, Real.arcosh_zero]

/-- The group `SO₀(n, 1)`: the matrices of determinant one that preserve the Lorentz form and
map `ℍⁿ` onto itself. -/
@[expose]
def lorentzGroup (n : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ) where
  carrier := {g | (∀ x y, lorentz (g.1 *ᵥ x) (g.1 *ᵥ y) = lorentz x y) ∧
    (fun x => g.1 *ᵥ x) '' hyperboloid n = hyperboloid n}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    have h : (fun x => (a * b).1 *ᵥ x) = (fun x => a.1 *ᵥ x) ∘ fun x => b.1 *ᵥ x := by
      ext x : 1
      simp [Matrix.mulVec_mulVec]
    refine ⟨fun x y => ?_, ?_⟩
    · simp only [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ha, hb]
    · rw [h, Set.image_comp, hb', ha']
  one_mem' := by simp
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    have hc : ∀ x, g.1 *ᵥ ((g⁻¹).1 *ᵥ x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    have hc' : ∀ x, (g⁻¹).1 *ᵥ (g.1 *ᵥ x) = x := fun x => by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    refine ⟨fun x y => ?_, ?_⟩
    · rw [← hg, hc, hc]
    · apply Set.Subset.antisymm
      · rintro _ ⟨x, hx, rfl⟩
        rw [← hg'] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        simpa only [hc'] using hz
      · intro x hx
        refine ⟨g.1 *ᵥ x, ?_, hc' x⟩
        rw [← hg']
        exact Set.mem_image_of_mem _ hx

/-- Membership means preservation of the Lorentz pairing and of the positive time sheet. -/
theorem mem_lorentzGroup_iff {n : ℕ} {g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ} :
    g ∈ lorentzGroup n ↔ (∀ x y, lorentz (g.1 *ᵥ x) (g.1 *ᵥ y) = lorentz x y) ∧
      (fun x => g.1 *ᵥ x) '' hyperboloid n = hyperboloid n :=
  Iff.rfl

/-- Elements of `SO₀(n, 1)` preserve the Lorentz form. -/
theorem lorentz_mulVec {n : ℕ} (g : lorentzGroup n) (x y : Fin (n + 1) → ℝ) :
    lorentz ((g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ x)
      ((g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ y) = lorentz x y :=
  g.2.1 x y

/-- Elements of `SO₀(n, 1)` map `ℍⁿ` to itself. -/
theorem mulVec_mem_hyperboloid {n : ℕ} (g : lorentzGroup n) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ hyperboloid n) :
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ x ∈ hyperboloid n := by
  rw [← g.2.2]
  exact Set.mem_image_of_mem _ hx

/-- The maximal compact subgroup `K ≅ SO(n)` of `SO₀(n, 1)`, the stabilizer of `o`. -/
@[expose]
def rotationSubgroup (n : ℕ) : Subgroup (lorentzGroup n) where
  carrier := {g | (g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ basePoint n = basePoint n}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hg]
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul,
      inv_mul_cancel]
    simp

/-- Membership in the rotation subgroup means fixing the base point. -/
theorem mem_rotationSubgroup_iff {n : ℕ} {g : lorentzGroup n} :
    g ∈ rotationSubgroup n ↔
      (g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ basePoint n = basePoint n :=
  Iff.rfl

/-- The orbit map `g ↦ g o`. -/
@[expose]
def orbitMap (n : ℕ) (g : lorentzGroup n) : Fin (n + 1) → ℝ :=
  (g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ basePoint n

/-- The orbit map sends a Lorentz transformation to its value at the base point. -/
theorem orbitMap_def (n : ℕ) (g : lorentzGroup n) :
    orbitMap n g = (g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ basePoint n :=
  rfl

/-- The identity Lorentz transformation maps to the base point. -/
@[simp]
theorem orbitMap_one (n : ℕ) : orbitMap n 1 = basePoint n := by
  simp [orbitMap_def]

/-- The orbit lies in the positive sheet of the unit hyperboloid. -/
theorem orbitMap_mem_hyperboloid (n : ℕ) (g : lorentzGroup n) : orbitMap n g ∈ hyperboloid n :=
  mulVec_mem_hyperboloid g (basePoint_mem_hyperboloid n)

/-- The chart `y ↦ (√(1 + |y|²), y)` of `ℍⁿ` over `ℝⁿ`. -/
@[expose]
def hyperboloidChart (n : ℕ) (y : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (Real.sqrt (1 + ∑ i, y i ^ 2)) y

/-- The spatial chart appends the positive square root of one plus the spatial norm squared as time
coordinate. -/
theorem hyperboloidChart_def (n : ℕ) (y : Fin n → ℝ) :
    hyperboloidChart n y = Fin.cons (Real.sqrt (1 + ∑ i, y i ^ 2)) y :=
  rfl

/-- The spatial chart parametrizing the upper hyperboloid is continuous. -/
theorem continuous_hyperboloidChart (n : ℕ) : Continuous (hyperboloidChart n) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [hyperboloidChart_def, Fin.cons_zero]
    fun_prop
  · simp only [hyperboloidChart_def, Fin.cons_succ]
    fun_prop

/-- Every spatial chart value lies on the upper unit hyperboloid. -/
theorem hyperboloidChart_mem_hyperboloid (n : ℕ) (y : Fin n → ℝ) :
    hyperboloidChart n y ∈ hyperboloid n := by
  have hs : 0 ≤ 1 + ∑ i, y i ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · simp only [lorentz_def, hyperboloidChart_def, Fin.cons_zero, Fin.cons_succ]
    rw [Real.mul_self_sqrt hs]
    simp [sq]
  · simp only [hyperboloidChart_def, Fin.cons_zero]
    exact Real.sqrt_pos.2 (by positivity)

/-- The Riemannian volume of `ℍⁿ`, `dy / √(1 + |y|²)` carried by the chart, as a measure on the
ambient space concentrated on `ℍⁿ`. -/
@[expose]
def hyperbolicMeasure (n : ℕ) : Measure (Fin (n + 1) → ℝ) :=
  ((volume : Measure (Fin n → ℝ)).withDensity fun y =>
    ENNReal.ofReal (Real.sqrt (1 + ∑ i, y i ^ 2))⁻¹).map (hyperboloidChart n)

/-- Hyperbolic volume is the pushforward of weighted Lebesgue measure under the spatial chart. -/
theorem hyperbolicMeasure_def (n : ℕ) :
    hyperbolicMeasure n = ((volume : Measure (Fin n → ℝ)).withDensity fun y =>
      ENNReal.ofReal (Real.sqrt (1 + ∑ i, y i ^ 2))⁻¹).map (hyperboloidChart n) :=
  rfl

/-- The area `ω_{n−1} = 2π^{n/2} / Γ(n/2)` of the unit sphere `S^{n−1}`. -/
@[expose]
def sphereArea (n : ℕ) : ℝ := 2 * π ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)

/-- The area of the real unit sphere is expressed by the Gamma normalization. -/
theorem sphereArea_def (n : ℕ) :
    sphereArea n = 2 * π ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2) :=
  rfl

/-- The circle has length `2π`. -/
theorem sphereArea_two : sphereArea 2 = 2 * π := by
  simp [sphereArea_def]

/-- The Laplace–Beltrami operator of `ℍⁿ` through the ambient wave operator (Wawrzyńczyk
§11.5, (11.5.1)–(11.5.3), pp. 411–412): `Δf(x) = (∂₁² + ⋯ + ∂ₙ² − ∂₀²) f(y / √[y, y])` at
`y = x`. Only the values of `f` on `ℍⁿ` enter at points of `ℍⁿ`; off the cone `[y, y] > 0` the
extension is junk. -/
@[expose]
def hyperbolicLaplacian (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℂ) (x : Fin (n + 1) → ℝ) : ℂ :=
  let fe : (Fin (n + 1) → ℝ) → ℂ := fun y => f ((Real.sqrt (lorentz y y))⁻¹ • y)
  ∑ i : Fin n, iteratedDeriv 2 (fun s : ℝ => fe (x + s • Pi.single i.succ 1)) 0 -
    iteratedDeriv 2 (fun s : ℝ => fe (x + s • Pi.single 0 1)) 0

/-- The hyperbolic Laplacian is the signed ambient second derivative of the homogeneous extension.
-/
theorem hyperbolicLaplacian_def (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℂ) (x : Fin (n + 1) → ℝ) :
    hyperbolicLaplacian n f x =
      ∑ i : Fin n, iteratedDeriv 2
          (fun s : ℝ => f ((Real.sqrt (lorentz (x + s • Pi.single i.succ 1)
            (x + s • Pi.single i.succ 1)))⁻¹ • (x + s • Pi.single i.succ 1))) 0 -
        iteratedDeriv 2 (fun s : ℝ => f ((Real.sqrt (lorentz (x + s • Pi.single 0 1)
          (x + s • Pi.single 0 1)))⁻¹ • (x + s • Pi.single 0 1))) 0 :=
  rfl

/-- The boundary point `b̃ = (1, b)` of the light cone over `b ∈ S^{n−1}`. -/
@[expose]
def boundaryVector (n : ℕ) (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Fin (n + 1) → ℝ :=
  Fin.cons 1 fun i => (b : EuclideanSpace ℝ (Fin n)) i

/-- A unit spatial direction becomes a null boundary vector with time coordinate one. -/
theorem boundaryVector_def (n : ℕ) (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    boundaryVector n b = Fin.cons 1 fun i => (b : EuclideanSpace ℝ (Fin n)) i :=
  rfl

/-- `b̃` lies on the light cone: `[b̃, b̃] = 0`. -/
theorem lorentz_boundaryVector_self (n : ℕ)
    (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    lorentz (boundaryVector n b) (boundaryVector n b) = 0 := by
  have hb : ‖(b : EuclideanSpace ℝ (Fin n))‖ = 1 := by simp
  have h := EuclideanSpace.real_norm_sq_eq (b : EuclideanSpace ℝ (Fin n))
  rw [hb] at h
  simp only [lorentz_def, boundaryVector_def, Fin.cons_zero, Fin.cons_succ]
  simp only [← sq]
  linarith

/-- `[o, b̃] = 1`. -/
theorem lorentz_basePoint_boundaryVector (n : ℕ)
    (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    lorentz (basePoint n) (boundaryVector n b) = 1 := by
  rw [lorentz_basePoint_left, boundaryVector_def, Fin.cons_zero]

/-- The rotation-invariant surface measure on `S^{n−1}`; the normalized measure `dσ` enters
through averages. -/
@[expose]
def sphereMeasure (n : ℕ) : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

/-- The boundary surface measure is induced by ambient Lebesgue measure. -/
theorem sphereMeasure_def (n : ℕ) :
    sphereMeasure n = (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere :=
  rfl

/-- The Plancherel constant `C_n = 2^{n−1} / (2π ω_{n−1})` of `ℍⁿ`. -/
@[expose]
def plancherelConstant (n : ℕ) : ℝ := 2 ^ (n - 1) / (2 * π * sphereArea n)

/-- The spherical Plancherel constant uses the sphere area and the Jacobi weight normalization. -/
theorem plancherelConstant_def (n : ℕ) :
    plancherelConstant n = 2 ^ (n - 1) / (2 * π * sphereArea n) :=
  rfl

/-- The Abel transform on `ℍ^{m+1}`,
`𝒜F(s) = e^{−ms/2} ∫_{ℝ^m} F(arcosh(cosh s + |v|² e^{−s}/2)) dv` (Heckman–Schlichtkrull Part I
§5.4, (5.4.3), p. 83, read in horospherical coordinates). -/
@[expose]
def abelTransform (m : ℕ) (F : ℝ → ℂ) (s : ℝ) : ℂ :=
  Real.exp (-(m * s / 2)) *
    ∫ v : Fin m → ℝ, F (Real.arcosh (Real.cosh s + (∑ i, v i ^ 2) * Real.exp (-s) / 2))

/-- The Abel transform integrates a radial profile over the transverse horospherical coordinates. -/
theorem abelTransform_def (m : ℕ) (F : ℝ → ℂ) (s : ℝ) :
    abelTransform m F s = Real.exp (-(m * s / 2)) *
      ∫ v : Fin m → ℝ, F (Real.arcosh (Real.cosh s + (∑ i, v i ^ 2) * Real.exp (-s) / 2)) :=
  rfl

/-- The Helgason–Fourier transform `f̂(λ, b) = ∫ f(x) [x, b̃]^{iλ − ρ} dm(x)`, `ρ = (n − 1)/2`
(Wawrzyńczyk §18.7, (18.7.12), p. 640, read on `ℍⁿ`). -/
@[expose]
def helgasonFourier (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℂ) (lam : ℂ)
    (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : ℂ :=
  ∫ x, f x * (lorentz x (boundaryVector n b) : ℂ) ^ (I * lam - ((n : ℂ) - 1) / 2)
    ∂hyperbolicMeasure n

/-- The Helgason transform integrates against a complex power of the null-boundary Lorentz pairing.
-/
theorem helgasonFourier_def (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℂ) (lam : ℂ)
    (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    helgasonFourier n f lam b =
      ∫ x, f x * (lorentz x (boundaryVector n b) : ℂ) ^ (I * lam - ((n : ℂ) - 1) / 2)
        ∂hyperbolicMeasure n :=
  rfl

end SFVK.RankOne
