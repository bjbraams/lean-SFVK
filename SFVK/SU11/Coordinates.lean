/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Coordinates on `SU(1,1)`

The subgroup of `SL(2, ℂ)` has a conjugate-symmetric matrix form. Its Euler
parametrization is by two diagonal rotations and a real boost, following
Vilenkin–Klimyk, Vol. 1, §6.1.1 (10)–(12), p. 271. The two-sided Haar measure has the
normalization in §6.1.4 (2), p. 275.
-/

public noncomputable section

open Complex Matrix MeasureTheory Set
open scoped ComplexConjugate Real

namespace SFVK.SU11

/-- The subgroup of determinant-one matrices with lower row `[conj b, conj a]`
when the upper row is `[a, b]`. -/
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

/-- The type of `SU(1,1)` matrices, with its subspace topology. -/
abbrev Group := ↥su11

/-- The Borel σ-algebra on `SU(1,1)`. -/
instance : MeasurableSpace Group := borel Group

/-- The measurable sets of `SU(1,1)` are the Borel sets. -/
instance : BorelSpace Group := ⟨rfl⟩

/-- The upper left coordinate of a matrix in `SU(1,1)`. -/
def entryA (g : Group) : ℂ := g.1.1 0 0

/-- The upper right coordinate of a matrix in `SU(1,1)`. -/
def entryB (g : Group) : ℂ := g.1.1 0 1

/-- The underlying matrix is determined by its upper row. -/
theorem coe_eq_matrix (g : Group) :
    g.1.1 = !![entryA g, entryB g; conj (entryB g), conj (entryA g)] := by
  obtain ⟨hb, ha⟩ := mem_su11.mp g.2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [entryA, entryB, ha, hb]

/-- The squared norms of the upper coordinates have difference one. -/
theorem normSq_entryA_sub_normSq_entryB (g : Group) :
    normSq (entryA g) - normSq (entryB g) = 1 := by
  have hg := g.1.2
  rw [coe_eq_matrix, Matrix.det_fin_two_of, Complex.mul_conj, Complex.mul_conj] at hg
  exact_mod_cast hg

/-- The matrix `[[a, b], [conj b, conj a]]` when `|a|² - |b|² = 1`. -/
def ofPair (a b : ℂ) (h : normSq a - normSq b = 1) : Group :=
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

/-- The diagonal rotation with eigenvalues `exp(iα/2)` and `exp(-iα/2)`. -/
def rot (α : ℝ) : Group :=
  ofPair (exp (((α / 2 : ℝ) : ℂ) * I)) 0 (by
    rw [map_zero, sub_zero, normSq_eq_norm_sq, norm_exp_ofReal_mul_I]
    norm_num)

/-- The two upper coordinates of a diagonal rotation. -/
theorem rot_entries (α : ℝ) :
    entryA (rot α) = exp (((α / 2 : ℝ) : ℂ) * I) ∧ entryB (rot α) = 0 := by
  simp [rot]

/-- The real symmetric boost with upper row `[cosh(t/2), sinh(t/2)]`. -/
def boost (t : ℝ) : Group :=
  ofPair (Real.cosh (t / 2)) (Real.sinh (t / 2)) (by
    rw [normSq_ofReal, normSq_ofReal]
    linear_combination Real.cosh_sq_sub_sinh_sq (t / 2))

/-- The two upper coordinates of a boost. -/
theorem boost_entries (t : ℝ) :
    entryA (boost t) = Real.cosh (t / 2) ∧ entryB (boost t) = Real.sinh (t / 2) := by
  simp [boost]

/-- The Euler element with left rotation `α`, boost parameter `t`, and right rotation `γ`. -/
def eulerSU11 (α t γ : ℝ) : Group := rot α * boost t * rot γ

/-- The rotation–boost–rotation factorization. -/
theorem eulerSU11_def (α t γ : ℝ) :
    eulerSU11 α t γ = rot α * boost t * rot γ := (rfl)

/-- The Euler box with strictly positive boost parameter. -/
def eulerDomain : Set (ℝ × ℝ × ℝ) := Ico 0 (2 * π) ×ˢ Ioi 0 ×ˢ Ico (-(2 * π)) (2 * π)

/-- Membership in the positive-boost Euler box. -/
theorem mem_eulerDomain {p : ℝ × ℝ × ℝ} :
    p ∈ eulerDomain ↔ p.1 ∈ Ico 0 (2 * π) ∧ 0 < p.2.1 ∧ p.2.2 ∈ Ico (-(2 * π)) (2 * π) :=
  (Iff.rfl)

/-- The positive-boost Euler box parametrizes exactly the elements with a nonzero
off-diagonal entry, with unique angles in that box. -/
theorem bijOn_eulerSU11 :
    BijOn (fun p : ℝ × ℝ × ℝ => eulerSU11 p.1 p.2.1 p.2.2) eulerDomain
      {g : Group | entryB g ≠ 0} := by
  sorry

/-- The Euler-angle measure with density `sinh t / (8 * π²)` pushed forward to `SU(1,1)`. -/
def su11Haar : Measure Group :=
  (ENNReal.ofReal (8 * π ^ 2)⁻¹ •
    (volume.restrict eulerDomain).withDensity (fun p => ENNReal.ofReal (Real.sinh p.2.1))).map
      (fun p => eulerSU11 p.1 p.2.1 p.2.2)

/-- The expression for `su11Haar` as an Euler-coordinate pushforward. -/
theorem su11Haar_def :
    su11Haar =
      (ENNReal.ofReal (8 * π ^ 2)⁻¹ •
        (volume.restrict eulerDomain).withDensity (fun p => ENNReal.ofReal (Real.sinh p.2.1))).map
          (fun p => eulerSU11 p.1 p.2.1 p.2.2) :=
  (rfl)

/-- The Euler normalization is a left Haar measure and is also right invariant. -/
theorem su11Haar_isHaarMeasure : su11Haar.IsHaarMeasure ∧ su11Haar.IsMulRightInvariant := by
  sorry

end SFVK.SU11
