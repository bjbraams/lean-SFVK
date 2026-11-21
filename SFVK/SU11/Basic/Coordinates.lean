/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Coordinates on `SU(1,1)`

The group `SU(1,1)` is the subgroup of `SL(2, ℂ)` of matrices `[[a, b], [conj b, conj a]]`,
with `|a|² - |b|² = 1`. Its Euler parametrization `euler α t γ = rotation α * boost t * rotation γ`
is by two diagonal rotations and a real boost, following Vilenkin–Klimyk, *Representation of Lie
Groups and Special Functions*, Vol. 1, §6.1.1 (10)–(12), p. 271, with the letters and the weight
sign of the `SU(2)` convention of `SFVK.SU2`. The measure `eulerHaar` is the pushforward of
`sinh t / (8π²) dα dt dγ`, the normalization of §6.1.4 (2), p. 275.
-/

public noncomputable section

open Complex Matrix MeasureTheory Set
open scoped ComplexConjugate Real

namespace SFVK

/-- The subgroup of determinant-one matrices with lower row `[conj b, conj a]`
when the upper row is `[a, b]`. -/
@[expose]
def su11 : Subgroup (SpecialLinearGroup (Fin 2) ℂ) where
  carrier := {g | g.1 1 0 = conj (g.1 0 1) ∧ g.1 1 1 = conj (g.1 0 0)}
  mul_mem' := by
    rintro g h ⟨hg₁, hg₂⟩ ⟨hh₁, hh₂⟩
    -- The entry formulas apply after reducing the subgroup carrier and the matrix coercion.
    change (g.1 * h.1) 1 0 = conj ((g.1 * h.1) 0 1) ∧
      (g.1 * h.1) 1 1 = conj ((g.1 * h.1) 0 0)
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hg₁, hg₂, hh₁, hh₂, map_add, map_mul,
      Complex.conj_conj]
    constructor <;> ring
  one_mem' := by simp
  inv_mem' := by
    rintro g ⟨hg₁, hg₂⟩
    -- The inverse in the special linear group has underlying matrix the adjugate.
    change (adjugate g.1) 1 0 = conj ((adjugate g.1) 0 1) ∧
      (adjugate g.1) 1 1 = conj ((adjugate g.1) 0 0)
    simp [Matrix.adjugate_fin_two, hg₁, hg₂]

/-- Membership in `SU(1,1)` is the conjugate symmetry of the two rows. -/
theorem mem_su11 {g : SpecialLinearGroup (Fin 2) ℂ} :
    g ∈ su11 ↔ g.1 1 0 = conj (g.1 0 1) ∧ g.1 1 1 = conj (g.1 0 0) :=
  (Iff.rfl)

/-- The group `SU(1,1)`, with the subspace topology from `SL(2, ℂ)`. -/
abbrev SU11 := ↥su11

namespace SU11

/-- The Borel σ-algebra on `SU(1,1)`. -/
instance : MeasurableSpace SU11 := borel SU11

/-- The measurable sets of `SU(1,1)` are the Borel sets. -/
instance : BorelSpace SU11 := ⟨rfl⟩

/-- The upper left coordinate of a matrix in `SU(1,1)`. -/
@[expose]
def entryA (g : SU11) : ℂ := g.1.1 0 0

/-- The upper right coordinate of a matrix in `SU(1,1)`. -/
@[expose]
def entryB (g : SU11) : ℂ := g.1.1 0 1

/-- The underlying matrix is determined by its upper row. -/
theorem coe_eq_matrix (g : SU11) :
    g.1.1 = !![entryA g, entryB g; conj (entryB g), conj (entryA g)] := by
  obtain ⟨hb, ha⟩ := mem_su11.mp g.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [entryA, entryB, ha, hb]

/-- The squared norms of the upper coordinates have difference one. -/
theorem normSq_entryA_sub_normSq_entryB (g : SU11) :
    normSq (entryA g) - normSq (entryB g) = 1 := by
  have hg := g.1.2
  rw [coe_eq_matrix, Matrix.det_fin_two_of, Complex.mul_conj, Complex.mul_conj] at hg
  exact_mod_cast hg

/-- The matrix `[[a, b], [conj b, conj a]]` when `|a|² - |b|² = 1`. -/
@[expose]
def ofPair (a b : ℂ) (h : normSq a - normSq b = 1) : SU11 :=
  ⟨⟨!![a, b; conj b, conj a], by
    rw [Matrix.det_fin_two_of, Complex.mul_conj, Complex.mul_conj]
    exact_mod_cast h⟩, mem_su11.mpr (by simp)⟩

/-- The first coordinate of the pair constructor. -/
@[simp]
theorem entryA_ofPair (a b : ℂ) (h : normSq a - normSq b = 1) :
    entryA (ofPair a b h) = a := (rfl)

/-- The second coordinate of the pair constructor. -/
@[simp]
theorem entryB_ofPair (a b : ℂ) (h : normSq a - normSq b = 1) :
    entryB (ofPair a b h) = b := (rfl)

/-- The first coordinate of the identity is one. -/
@[simp]
theorem entryA_one : entryA 1 = 1 := by simp [entryA]

/-- The second coordinate of the identity is zero. -/
@[simp]
theorem entryB_one : entryB 1 = 0 := by simp [entryB]

/-- The first coordinate of a product. -/
theorem entryA_mul (g h : SU11) :
    entryA (g * h) = entryA g * entryA h + entryB g * conj (entryB h) := by
  have hg := coe_eq_matrix g
  have hh := coe_eq_matrix h
  simp only [entryA, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rw [hg, hh]
  simp [Matrix.mul_apply, Fin.sum_univ_two, entryA, entryB]

/-- The second coordinate of a product. -/
theorem entryB_mul (g h : SU11) :
    entryB (g * h) = entryA g * entryB h + entryB g * conj (entryA h) := by
  have hg := coe_eq_matrix g
  have hh := coe_eq_matrix h
  simp only [entryB, Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rw [hg, hh]
  simp [Matrix.mul_apply, Fin.sum_univ_two, entryA, entryB]

/-- The diagonal rotation with eigenvalues `exp(iα/2)` and `exp(-iα/2)`. -/
@[expose]
def rotation (α : ℝ) : SU11 :=
  ofPair (exp (((α / 2 : ℝ) : ℂ) * I)) 0 (by
    rw [map_zero, sub_zero, normSq_eq_norm_sq, norm_exp_ofReal_mul_I]
    norm_num)

/-- The first coordinate of a diagonal rotation. -/
@[simp]
theorem entryA_rotation (α : ℝ) : entryA (rotation α) = exp (((α / 2 : ℝ) : ℂ) * I) := by
  simp [rotation]

/-- The second coordinate of a diagonal rotation is zero. -/
@[simp]
theorem entryB_rotation (α : ℝ) : entryB (rotation α) = 0 := by
  simp [rotation]

/-- The real symmetric boost with upper row `[cosh(t/2), sinh(t/2)]`. -/
@[expose]
def boost (t : ℝ) : SU11 :=
  ofPair (Real.cosh (t / 2)) (Real.sinh (t / 2)) (by
    rw [normSq_ofReal, normSq_ofReal]
    linear_combination Real.cosh_sq_sub_sinh_sq (t / 2))

/-- The first coordinate of a boost. -/
@[simp]
theorem entryA_boost (t : ℝ) : entryA (boost t) = Real.cosh (t / 2) := by
  simp [boost]

/-- The second coordinate of a boost. -/
@[simp]
theorem entryB_boost (t : ℝ) : entryB (boost t) = Real.sinh (t / 2) := by
  simp [boost]

/-- The Euler element with left rotation `α`, boost parameter `t`, and right rotation `γ`. -/
@[expose]
def euler (α t γ : ℝ) : SU11 := rotation α * boost t * rotation γ

/-- The rotation–boost–rotation factorization. -/
theorem euler_def (α t γ : ℝ) :
    euler α t γ = rotation α * boost t * rotation γ := (rfl)

/-- The first entry has phase given by the half-sum of the Euler angles. -/
theorem entryA_euler (α t γ : ℝ) :
    entryA (euler α t γ) = (Real.cosh (t / 2) : ℂ) * (Circle.exp ((α + γ) / 2) : ℂ) := by
  rw [euler_def, entryA_mul, entryA_mul, add_div, Circle.exp_add, Circle.coe_mul]
  simp only [entryA_rotation, entryA_boost, entryB_rotation, map_zero, mul_zero, add_zero,
    zero_mul, Circle.coe_exp]
  ring

/-- The second entry has phase given by the half-difference of the Euler angles. -/
theorem entryB_euler (α t γ : ℝ) :
    entryB (euler α t γ) = (Real.sinh (t / 2) : ℂ) * (Circle.exp ((α - γ) / 2) : ℂ) := by
  rw [euler_def, entryB_mul, entryB_mul, sub_div, sub_eq_add_neg, Circle.exp_add, Circle.coe_mul,
    Circle.exp_neg, Circle.coe_inv_eq_conj]
  simp only [entryA_rotation, entryB_rotation, entryB_boost, mul_zero, zero_mul,
    add_zero, zero_add, Circle.coe_exp]
  ring

/-- The Euler box with strictly positive boost parameter. -/
@[expose]
def eulerDomain : Set (ℝ × ℝ × ℝ) := Ico 0 (2 * π) ×ˢ Ioi 0 ×ˢ Ico (-(2 * π)) (2 * π)

/-- Membership in the positive-boost Euler box. -/
theorem mem_eulerDomain {p : ℝ × ℝ × ℝ} :
    p ∈ eulerDomain ↔ p.1 ∈ Ico 0 (2 * π) ∧ 0 < p.2.1 ∧ p.2.2 ∈ Ico (-(2 * π)) (2 * π) :=
  (Iff.rfl)

/-- The Euler-angle measure with density `sinh t / (8 * π²)` pushed forward to `SU(1,1)`. -/
@[expose]
def eulerHaar : Measure SU11 :=
  (ENNReal.ofReal (8 * π ^ 2)⁻¹ •
    (volume.restrict eulerDomain).withDensity (fun p => ENNReal.ofReal (Real.sinh p.2.1))).map
      (fun p => euler p.1 p.2.1 p.2.2)

/-- The expression for `eulerHaar` as an Euler-coordinate pushforward. -/
theorem eulerHaar_def :
    eulerHaar =
      (ENNReal.ofReal (8 * π ^ 2)⁻¹ •
        (volume.restrict eulerDomain).withDensity (fun p => ENNReal.ofReal (Real.sinh p.2.1))).map
          (fun p => euler p.1 p.2.1 p.2.2) :=
  (rfl)

end SU11

end SFVK
