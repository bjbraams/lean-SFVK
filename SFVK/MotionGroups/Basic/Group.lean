/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import SFVKMathlib.MeasureTheory.Group.MatrixGroups

/-!
# The Euclidean and pseudo-Euclidean motion groups

The motion group `M(n) = ℝⁿ ⋊ SO(n)` of pairs `(a, k)` with `(a, k)(a', k') = (a + k a', k k')`,
and the group `ISO(1,1) = ℝ² ⋊ SO₀(1,1)` of pairs `(a, s)` with the Lorentz boost of rapidity
`s`; Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 1, §4.1.1,
p. 165, and §4.2.2 (1)–(4), p. 172. On `M(2)`: the rotation `k_α`, the angle of a rotation in
`ℝ/2πℤ`, the polar coordinates `g(r, φ; α) = (r e(φ), k_α)` of Vilenkin–Klimyk §4.1.1 (2), and
the unit vector `e(ψ)` at a point `ψ` of the circle `AddCircle (2π)`.

## Main definitions

* `SFVK.MotionGroups.MotionGroup n`: the group `M(n)`, with the topology of `ℝⁿ × SO(n)`.
* `SFVK.MotionGroups.ISO11`: the group `ISO(1,1)`, with the topology of `ℝ² × ℝ`.
* `SFVK.MotionGroups.rotation`, `rotAngle`, `planePoint`, `unitVec`, `polar`, `toComplex`.
* `SFVK.MotionGroups.motionApply`: the affine action of `M(n)` on `ℝⁿ`.
* `SFVK.MotionGroups.rotationSubgroup n`: the subgroup `K = {(0, k)}`.
-/

public noncomputable section

open Complex
open scoped Real

namespace SFVK.MotionGroups

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- `SO(n)` as Mathlib's special orthogonal matrices. -/
abbrev SOn (n : ℕ) := Matrix.specialOrthogonalGroup (Fin n) ℝ

/-- A matrix of `SO(n)` acting on `ℝⁿ`. -/
@[expose]
def rotE {n : ℕ} (k : SOn n) (a : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin k.1 a

theorem rotE_def {n : ℕ} (k : SOn n) (a : EuclideanSpace ℝ (Fin n)) :
    rotE k a = Matrix.toEuclideanLin k.1 a :=
  rfl

theorem rotE_mul {n : ℕ} (k k' : SOn n) (a : EuclideanSpace ℝ (Fin n)) :
    rotE (k * k') a = rotE k (rotE k' a) := by
  simp only [rotE, Submonoid.coe_mul, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [Matrix.toLin_mul _ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  rfl

@[simp]
theorem rotE_one {n : ℕ} (a : EuclideanSpace ℝ (Fin n)) : rotE (1 : SOn n) a = a := by
  simp [rotE]

theorem rotE_add {n : ℕ} (k : SOn n) (a b : EuclideanSpace ℝ (Fin n)) :
    rotE k (a + b) = rotE k a + rotE k b := by
  simp [rotE]

@[simp]
theorem rotE_zero {n : ℕ} (k : SOn n) : rotE k 0 = 0 := by
  simp [rotE]

@[simp]
theorem rotE_neg {n : ℕ} (k : SOn n) (a : EuclideanSpace ℝ (Fin n)) :
    rotE k (-a) = -rotE k a := by
  simp [rotE]

/-- The motion group `M(n) = ℝⁿ ⋊ SO(n)`, with `(a, k)(a', k') = (a + k a', k k')`. -/
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

@[simp] theorem mul_a (g h : MotionGroup n) : (g * h).a = g.a + rotE g.k h.a := rfl

@[simp] theorem mul_k (g h : MotionGroup n) : (g * h).k = g.k * h.k := rfl

@[simp] theorem one_a : (1 : MotionGroup n).a = 0 := rfl

@[simp] theorem one_k : (1 : MotionGroup n).k = 1 := rfl

@[simp] theorem inv_a (g : MotionGroup n) : g⁻¹.a = -rotE g.k⁻¹ g.a := rfl

@[simp] theorem inv_k (g : MotionGroup n) : g⁻¹.k = g.k⁻¹ := rfl

instance : Group (MotionGroup n) where
  mul_assoc g h l := by
    ext1
    · simp [rotE_add, rotE_mul, add_assoc]
    · simp [mul_assoc]
  one_mul g := by ext1 <;> simp
  mul_one g := by ext1 <;> simp
  inv_mul_cancel g := by
    ext1
    · simp
    · simp

/-- The topology of `ℝⁿ × SO(n)`. -/
instance : TopologicalSpace (MotionGroup n) :=
  TopologicalSpace.induced (fun g => (g.a, g.k)) inferInstance

instance : MeasurableSpace (MotionGroup n) := borel (MotionGroup n)

instance : BorelSpace (MotionGroup n) := ⟨rfl⟩

end MotionGroup

/-- The Lorentz boost `Λ_s (x, y) = (x cosh s + y sinh s, x sinh s + y cosh s)`, Vilenkin–Klimyk
Vol. 1 §4.2.2 (1), p. 172. -/
@[expose]
def lorentzBoost (s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * Real.cosh s + p.2 * Real.sinh s, p.1 * Real.sinh s + p.2 * Real.cosh s)

theorem lorentzBoost_def (s : ℝ) (p : ℝ × ℝ) :
    lorentzBoost s p =
      (p.1 * Real.cosh s + p.2 * Real.sinh s, p.1 * Real.sinh s + p.2 * Real.cosh s) :=
  rfl

theorem lorentzBoost_add (s s' : ℝ) (p : ℝ × ℝ) :
    lorentzBoost (s + s') p = lorentzBoost s (lorentzBoost s' p) := by
  simp only [lorentzBoost, Real.cosh_add, Real.sinh_add, Prod.mk.injEq]
  constructor <;> ring

@[simp]
theorem lorentzBoost_zero (p : ℝ × ℝ) : lorentzBoost 0 p = p := by
  simp [lorentzBoost]

@[simp]
theorem lorentzBoost_apply_zero (s : ℝ) : lorentzBoost s 0 = 0 := by
  simp [lorentzBoost]

/-- The group `ISO(1,1) = ℝ² ⋊ SO₀(1,1)`, with `(a, s)(a', s') = (a + Λ_s a', s + s')`. -/
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

@[simp] theorem mul_a (g h : ISO11) : (g * h).a = g.a + lorentzBoost g.s h.a := rfl

@[simp] theorem mul_s (g h : ISO11) : (g * h).s = g.s + h.s := rfl

@[simp] theorem one_a : (1 : ISO11).a = 0 := rfl

@[simp] theorem one_s : (1 : ISO11).s = 0 := rfl

@[simp] theorem inv_a (g : ISO11) : g⁻¹.a = -lorentzBoost (-g.s) g.a := rfl

@[simp] theorem inv_s (g : ISO11) : g⁻¹.s = -g.s := rfl

instance : Group ISO11 where
  mul_assoc g h l := by
    ext1
    · simp only [mul_a, mul_s, lorentzBoost_add, add_assoc]
      simp only [lorentzBoost, Prod.fst_add, Prod.snd_add, Prod.ext_iff]
      constructor <;> ring
    · simp [add_assoc]
  one_mul g := by ext1 <;> simp
  mul_one g := by ext1 <;> simp
  inv_mul_cancel g := by
    ext1
    · simp
    · simp

/-- The topology of `ℝ² × ℝ`. -/
instance : TopologicalSpace ISO11 := TopologicalSpace.induced (fun g => (g.a, g.s)) inferInstance

instance : MeasurableSpace ISO11 := borel ISO11

instance : BorelSpace ISO11 := ⟨rfl⟩

end ISO11

/-- The rotation `k_α = [[cos α, -sin α], [sin α, cos α]]` of the plane, Vilenkin–Klimyk Vol. 1
§4.1.1, p. 165. -/
@[expose]
def rotation (α : ℝ) : SOn 2 :=
  ⟨!![Real.cos α, -Real.sin α; Real.sin α, Real.cos α], by
    rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [Real.sin_sq_add_cos_sq α]
    · simp [Matrix.det_fin_two]
      nlinarith [Real.sin_sq_add_cos_sq α]⟩

theorem coe_rotation (α : ℝ) :
    (rotation α : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos α, -Real.sin α; Real.sin α, Real.cos α] :=
  rfl

/-- A plane vector as the complex number `a₁ + i a₂`. -/
@[expose]
def toComplex (a : EuclideanSpace ℝ (Fin 2)) : ℂ := (a 0 : ℂ) + (a 1 : ℂ) * I

theorem toComplex_def (a : EuclideanSpace ℝ (Fin 2)) : toComplex a = (a 0 : ℂ) + (a 1 : ℂ) * I :=
  rfl

/-- The plane vector `r e(φ) = (r cos φ, r sin φ)`. -/
@[expose]
def planePoint (r φ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![r * Real.cos φ, r * Real.sin φ]

@[simp]
theorem planePoint_apply_zero (r φ : ℝ) : planePoint r φ 0 = r * Real.cos φ :=
  rfl

@[simp]
theorem planePoint_apply_one (r φ : ℝ) : planePoint r φ 1 = r * Real.sin φ :=
  rfl

/-- The unit vector `e(ψ) = (cos ψ, sin ψ)` at a point `ψ` of `ℝ/2πℤ`, through Mathlib's
character `fourier 1 ψ = e^{iψ}`. -/
@[expose]
def unitVec (ψ : 𝕋) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(fourier 1 ψ : ℂ).re, (fourier 1 ψ : ℂ).im]

theorem unitVec_def (ψ : 𝕋) :
    unitVec ψ = WithLp.toLp 2 ![(fourier 1 ψ : ℂ).re, (fourier 1 ψ : ℂ).im] :=
  rfl

/-- The angle of a rotation of the plane, the argument of `k₀₀ + i k₁₀`, modulo `2π`. -/
@[expose]
def rotAngle (k : SOn 2) : 𝕋 := (Complex.arg ((k.1 0 0 : ℂ) + (k.1 1 0 : ℂ) * I) : 𝕋)

theorem rotAngle_def (k : SOn 2) :
    rotAngle k = (Complex.arg ((k.1 0 0 : ℂ) + (k.1 1 0 : ℂ) * I) : 𝕋) :=
  rfl

/-- The element `g(r, φ; α) = (r e(φ), k_α)` of `M(2)`, Vilenkin–Klimyk Vol. 1 §4.1.1 (2),
p. 165. -/
@[expose]
def polar (r φ α : ℝ) : MotionGroup 2 := ⟨planePoint r φ, rotation α⟩

theorem polar_def (r φ α : ℝ) : polar r φ α = ⟨planePoint r φ, rotation α⟩ :=
  rfl

/-- The affine action `x ↦ a + k x` of `M(n)` on `ℝⁿ`. -/
@[expose]
def motionApply {n : ℕ} (g : MotionGroup n) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  g.a + rotE g.k x

theorem motionApply_def {n : ℕ} (g : MotionGroup n) (x : EuclideanSpace ℝ (Fin n)) :
    motionApply g x = g.a + rotE g.k x :=
  rfl

/-- The action law of `motionApply`. -/
theorem motionApply_mul {n : ℕ} (g h : MotionGroup n) (x : EuclideanSpace ℝ (Fin n)) :
    motionApply (g * h) x = motionApply g (motionApply h x) := by
  simp [motionApply, rotE_add, rotE_mul, add_assoc]

/-- The rotation subgroup `K = {(0, k)}` of `M(n)`. -/
@[expose]
def rotationSubgroup (n : ℕ) : Subgroup (MotionGroup n) where
  carrier := {g | g.a = 0}
  mul_mem' := by
    intro g h hg hh
    change g.a = 0 at hg
    change h.a = 0 at hh
    change g.a + rotE g.k h.a = 0
    simp [hg, hh]
  one_mem' := rfl
  inv_mem' := by
    intro g hg
    change g.a = 0 at hg
    change -rotE g.k⁻¹ g.a = 0
    simp [hg]

theorem mem_rotationSubgroup {n : ℕ} (g : MotionGroup n) :
    g ∈ rotationSubgroup n ↔ g.a = 0 :=
  Iff.rfl

end SFVK.MotionGroups
