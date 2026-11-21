/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.MotionGroups.Basic.Group

/-!
# Polar coordinates on the plane motion group

The rotations `k_α` form a circle group, every rotation of the plane is some `k_α`, and the
product of two elements `g(r, φ; α)` of `M(2)` in polar coordinates; Vilenkin–Klimyk,
*Representation of Lie Groups and Special Functions*, Vol. 1, §4.1.1 (1)–(4), p. 165.
-/

public noncomputable section

open Complex
open scoped Real

namespace SFVK.MotionGroups

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- Rotations form a circle group: `k_{α+β} = k_α k_β`. -/
theorem rotation_add (α β : ℝ) : rotation (α + β) = rotation α * rotation β := by
  apply Subtype.ext
  rw [Submonoid.coe_mul, coe_rotation, coe_rotation, coe_rotation]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

/-- `k_0` is the identity. -/
@[simp]
theorem rotation_zero : rotation 0 = 1 := by
  apply Subtype.ext
  rw [coe_rotation]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Every rotation of the plane is some `k_α`. -/
theorem exists_rotation_eq (k : SOn 2) : ∃ α : ℝ, k = rotation α := by
  let z : ℂ := (k.1 0 0 : ℂ) + (k.1 1 0 : ℂ) * I
  obtain ⟨hdiag, hoff, hsq⟩ := Matrix.mem_specialOrthogonalGroup_fin_two_iff.mp k.2
  have hz : ‖z‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [z, hoff] at hsq ⊢
    simpa only [pow_two] using hsq
  refine ⟨arg z, ?_⟩
  have hphase : Complex.exp ((arg z : ℝ) * I) = z := by
    simpa only [hz, ofReal_one, one_mul] using norm_mul_exp_arg_mul_I z
  have hre := congrArg Complex.re hphase
  have him := congrArg Complex.im hphase
  simp [z, exp_ofReal_mul_I_re] at hre
  simp [z, exp_ofReal_mul_I_im] at him
  apply Subtype.ext
  rw [coe_rotation]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [z, hre, him, ← hdiag, hoff]

/-- `rotAngle` recovers the angle of `k_α` modulo `2π`. -/
@[simp]
theorem rotAngle_rotation (α : ℝ) : rotAngle (rotation α) = (α : 𝕋) := by
  rw [rotAngle_def, coe_rotation]
  have h := (AddCircle.homeomorphCircle').left_inv (α : 𝕋)
  change (arg (Real.Angle.toCircle (α : Real.Angle)) : 𝕋) = (α : 𝕋) at h
  rw [Real.Angle.toCircle_coe, Circle.coe_exp] at h
  simpa [← Complex.exp_mul_I] using h

/-- `rotAngle` is a homomorphism to `ℝ/2πℤ`. -/
theorem rotAngle_mul (k k' : SOn 2) : rotAngle (k * k') = rotAngle k + rotAngle k' := by
  obtain ⟨α, rfl⟩ := exists_rotation_eq k
  obtain ⟨β, rfl⟩ := exists_rotation_eq k'
  rw [← rotation_add, rotAngle_rotation, rotAngle_rotation, rotAngle_rotation]
  exact AddCircle.coe_add (2 * π) α β

/-- `k_α` is multiplication by `e^{iα}` in the complex coordinate. -/
theorem toComplex_rotE_rotation (α : ℝ) (a : EuclideanSpace ℝ (Fin 2)) :
    toComplex (rotE (rotation α) a) = Complex.exp (α * I) * toComplex a := by
  rw [toComplex_def, toComplex_def, rotE_def, coe_rotation, Complex.exp_mul_I]
  simp [Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two,
    -Complex.ofReal_cos, -Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  linear_combination (-Complex.sin (α : ℂ) * (a 1 : ℂ)) * Complex.I_sq

/-- The complex coordinate of `r e(φ)` is `r e^{iφ}`. -/
theorem toComplex_planePoint (r φ : ℝ) :
    toComplex (planePoint r φ) = r * Complex.exp (φ * I) := by
  rw [toComplex_def, planePoint_apply_zero, planePoint_apply_one, Complex.exp_mul_I]
  push_cast
  ring

/-- Translation part of the polar product law (Vilenkin–Klimyk Vol. 1 §4.1.1 (4), p. 165):
`g(r₁, φ₁; α₁) g(r₂, φ₂; α₂)` has translation `r₁ e^{iφ₁} + r₂ e^{i(φ₂+α₁)}`. -/
theorem toComplex_polar_mul_a (r₁ φ₁ α₁ r₂ φ₂ α₂ : ℝ) :
    toComplex (polar r₁ φ₁ α₁ * polar r₂ φ₂ α₂).a =
      r₁ * Complex.exp (φ₁ * I) + r₂ * Complex.exp ((φ₂ + α₁) * I) := by
  have hadd (a b : EuclideanSpace ℝ (Fin 2)) : toComplex (a + b) = toComplex a + toComplex b := by
    simp only [toComplex_def, PiLp.add_apply, ofReal_add]
    ring
  rw [MotionGroup.mul_a, hadd]
  change toComplex (planePoint r₁ φ₁) +
    toComplex (rotE (rotation α₁) (planePoint r₂ φ₂)) = _
  rw [toComplex_rotE_rotation, toComplex_planePoint, toComplex_planePoint, add_mul,
    Complex.exp_add]
  ring

/-- Rotation part of the polar product law: the angles add. -/
theorem polar_mul_k (r₁ φ₁ α₁ r₂ φ₂ α₂ : ℝ) :
    (polar r₁ φ₁ α₁ * polar r₂ φ₂ α₂).k = rotation (α₁ + α₂) := by
  rw [MotionGroup.mul_k, rotation_add]
  rfl

/-- Polar form of `M(2)`: every `g` is `g(|a|, φ; α)` for some angles. -/
theorem exists_polar (g : MotionGroup 2) : ∃ φ α : ℝ, g = polar ‖g.a‖ φ α := by
  have hnorm : ‖toComplex g.a‖ = ‖g.a‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [Complex.sq_norm, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Complex.normSq_apply]
    simp [toComplex_def, pow_two]
  obtain ⟨α, hα⟩ := exists_rotation_eq g.k
  refine ⟨arg (toComplex g.a), α, MotionGroup.ext ?_ hα⟩
  have hphase : toComplex (planePoint ‖g.a‖ (arg (toComplex g.a))) = toComplex g.a := by
    rw [toComplex_planePoint, ← hnorm, norm_mul_exp_arg_mul_I]
  have hre := congrArg Complex.re hphase.symm
  have him := congrArg Complex.im hphase.symm
  simp [toComplex_def] at hre him
  apply PiLp.ext
  intro i
  fin_cases i
  · exact hre
  · exact him

end SFVK.MotionGroups
