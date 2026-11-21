/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import SFVKMathlib.MeasureTheory.Group.MatrixGroups

/-!
# The real and complex unit spheres with `SO(n)` and `U(n)`

The rotation group `SO(n)` acts on `ℝⁿ` and the unitary group `U(n)` on `ℂⁿ` by matrix
multiplication. A unit vector `η` replaces the north pole of the sources, and its stabilizer
`K_η` is the subgroup `SO(n - 1)` (respectively `U(n - 1)`) of the Gel'fand pairs. The spheres
carry their surface measures normalized to total mass one, as in Vilenkin–Klimyk,
*Representation of Lie Groups and Special Functions*, Vol. 2, §9.1.9 (1)–(6), p. 22.

## Main definitions

* `SFVK.Spheres.RotationGroup n`: `SO(n)` as `Matrix.specialOrthogonalGroup (Fin n) ℝ`, with
  `rotate g x = g x` and the stabilizer `rotationStabilizer η`.
* `SFVK.Spheres.sphereMeasure n`: the normalized surface measure on `S^{n-1} ⊂ ℝⁿ`.
* `SFVK.Spheres.polarConstant n`: `c_n = Γ(n/2)/(√π Γ((n - 1)/2))`, the constant of the density
  `c_n (1 - t²)^{(n-3)/2}` of `⟪η, x⟫` on the sphere.
* `SFVK.Spheres.UnitaryMatrixGroup n`: `U(n)` as `Matrix.unitaryGroup (Fin n) ℂ`, with
  `unitaryRotate`, `unitaryStabilizer η` and `complexSphereMeasure n` on `S^{2n-1} ⊂ ℂⁿ`.
-/

public noncomputable section

open MeasureTheory Set
open scoped Real

namespace SFVK.Spheres

/-! ### The rotation group -/

/-- The rotation group `SO(n)`. -/
abbrev RotationGroup (n : ℕ) := Matrix.specialOrthogonalGroup (Fin n) ℝ

/-- A rotation acting on `ℝⁿ` by matrix multiplication. -/
@[expose]
def rotate {n : ℕ} (g : RotationGroup n) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin g.1 x

theorem rotate_def {n : ℕ} (g : RotationGroup n) (x : EuclideanSpace ℝ (Fin n)) :
    rotate g x = Matrix.toEuclideanLin g.1 x :=
  rfl

@[simp]
theorem rotate_one {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : rotate (1 : RotationGroup n) x = x := by
  simp [rotate]

theorem rotate_mul {n : ℕ} (g h : RotationGroup n) (x : EuclideanSpace ℝ (Fin n)) :
    rotate (g * h) x = rotate g (rotate h x) := by
  simp only [rotate, Submonoid.coe_mul, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [Matrix.toLin_mul _ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  rfl

theorem rotate_inv_rotate {n : ℕ} (g : RotationGroup n) (x : EuclideanSpace ℝ (Fin n)) :
    rotate g⁻¹ (rotate g x) = x := by
  rw [← rotate_mul, inv_mul_cancel, rotate_one]

/-- The stabilizer `K_η` of a vector `η` in `SO(n)`. For a unit vector it is a copy of
`SO(n - 1)`. -/
@[expose]
def rotationStabilizer {n : ℕ} (η : EuclideanSpace ℝ (Fin n)) : Subgroup (RotationGroup n) where
  carrier := {g | rotate g η = η}
  mul_mem' {g h} hg hh := by
    simp only [mem_ofPred_eq] at hg hh ⊢
    rw [rotate_mul, hh, hg]
  one_mem' := by simp
  inv_mem' {g} hg := by
    simp only [mem_ofPred_eq] at hg ⊢
    conv_lhs => rw [← hg]
    exact rotate_inv_rotate g η

theorem mem_rotationStabilizer {n : ℕ} {η : EuclideanSpace ℝ (Fin n)} {g : RotationGroup n} :
    g ∈ rotationStabilizer η ↔ rotate g η = η :=
  Iff.rfl

/-! ### The real sphere -/

/-- The unit sphere `S^{n-1}` of `ℝⁿ`. -/
abbrev Sphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The rotation-invariant probability measure on `S^{n-1}`: Mathlib's surface measure
`Measure.toSphere` divided by its total mass. -/
@[expose]
def sphereMeasure (n : ℕ) : Measure (Sphere n) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

theorem sphereMeasure_def (n : ℕ) :
    sphereMeasure n = ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ)⁻¹ •
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere :=
  rfl

/-- The constant `c_n = Γ(n/2)/(√π Γ((n - 1)/2))` of the polar-angle density
`c_n (1 - t²)^{(n-3)/2}` (Vilenkin–Klimyk, Vol. 2, §9.1.9 (6), p. 22). -/
@[expose]
def polarConstant (n : ℕ) : ℝ := Real.Gamma ((n : ℝ) / 2) / (√π * Real.Gamma (((n : ℝ) - 1) / 2))

theorem polarConstant_def (n : ℕ) :
    polarConstant n = Real.Gamma ((n : ℝ) / 2) / (√π * Real.Gamma (((n : ℝ) - 1) / 2)) :=
  rfl

/-- `c_3 = 1/2`: the height on `S²` is uniformly distributed (Archimedes). -/
theorem polarConstant_three : polarConstant 3 = 1 / 2 := by
  have h : (3 : ℝ) / 2 = 1 / 2 + 1 := by norm_num
  have hπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  rw [polarConstant_def, show ((3 : ℕ) : ℝ) = 3 by norm_num, h, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq, show (3 : ℝ) - 1 = 2 by norm_num, show (2 : ℝ) / 2 = 1 by norm_num,
    Real.Gamma_one]
  field_simp

/-! ### The unitary group and the complex sphere -/

/-- The unitary group `U(n)`. -/
abbrev UnitaryMatrixGroup (n : ℕ) := Matrix.unitaryGroup (Fin n) ℂ

/-- A unitary matrix acting on `ℂⁿ` by matrix multiplication. -/
@[expose]
def unitaryRotate {n : ℕ} (g : UnitaryMatrixGroup n) (z : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanLin g.1 z

theorem unitaryRotate_def {n : ℕ} (g : UnitaryMatrixGroup n) (z : EuclideanSpace ℂ (Fin n)) :
    unitaryRotate g z = Matrix.toEuclideanLin g.1 z :=
  rfl

@[simp]
theorem unitaryRotate_one {n : ℕ} (z : EuclideanSpace ℂ (Fin n)) :
    unitaryRotate (1 : UnitaryMatrixGroup n) z = z := by
  simp [unitaryRotate]

theorem unitaryRotate_mul {n : ℕ} (g h : UnitaryMatrixGroup n) (z : EuclideanSpace ℂ (Fin n)) :
    unitaryRotate (g * h) z = unitaryRotate g (unitaryRotate h z) := by
  simp only [unitaryRotate, Submonoid.coe_mul, Matrix.toEuclideanLin_eq_toLin_orthonormal]
  rw [Matrix.toLin_mul _ (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
  rfl

theorem unitaryRotate_inv_unitaryRotate {n : ℕ} (g : UnitaryMatrixGroup n)
    (z : EuclideanSpace ℂ (Fin n)) : unitaryRotate g⁻¹ (unitaryRotate g z) = z := by
  rw [← unitaryRotate_mul, inv_mul_cancel, unitaryRotate_one]

/-- The stabilizer of `η` in `U(n)`; for a unit vector it is a copy of `U(n - 1)`. -/
@[expose]
def unitaryStabilizer {n : ℕ} (η : EuclideanSpace ℂ (Fin n)) :
    Subgroup (UnitaryMatrixGroup n) where
  carrier := {g | unitaryRotate g η = η}
  mul_mem' {g h} hg hh := by
    simp only [mem_ofPred_eq] at hg hh ⊢
    rw [unitaryRotate_mul, hh, hg]
  one_mem' := by simp
  inv_mem' {g} hg := by
    simp only [mem_ofPred_eq] at hg ⊢
    conv_lhs => rw [← hg]
    exact unitaryRotate_inv_unitaryRotate g η

theorem mem_unitaryStabilizer {n : ℕ} {η : EuclideanSpace ℂ (Fin n)}
    {g : UnitaryMatrixGroup n} : g ∈ unitaryStabilizer η ↔ unitaryRotate g η = η :=
  Iff.rfl

/-- The unit sphere `S^{2n-1}` of `ℂⁿ`. -/
abbrev ComplexSphere (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1

/-- The `U(n)`-invariant probability measure on `S^{2n-1} ⊂ ℂⁿ`: the surface measure divided by
its total mass. -/
@[expose]
def complexSphereMeasure (n : ℕ) : Measure (ComplexSphere n) :=
  ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere

theorem complexSphereMeasure_def (n : ℕ) :
    complexSphereMeasure n = ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere univ)⁻¹ •
      (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere :=
  rfl

end SFVK.Spheres
