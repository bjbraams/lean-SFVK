/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU2.Basic.UnitaryModel
import Mathlib.Analysis.InnerProductSpace.Adjoint
import SFVK.SU2.Basic.MatrixElements
import TauCeti.RepresentationTheory.Continuous.Basic

/-!
# Unitarity of the normalized symmetric powers

The factorial normalization of Edmonds, *Angular Momentum in Quantum Mechanics*, p. 56, makes the
symmetric powers of the defining representation of `SU(2)` unitary. The entry polynomial
intertwines conjugate transpose with swapping the weight indices, which identifies the adjoint
of each action operator with the action of the inverse group element.
-/

public section

open scoped ComplexConjugate InnerProductSpace

namespace SFVK.SU2

/-- Conjugating and transposing the input swaps the weight indices and conjugates the value. -/
private theorem entrySum_star (d i j : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    entrySum d i j (star A) = conj (entrySum d j i A) := by
  simp only [entrySum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : d ≤ k + i + j ∧ k + i ≤ d ∧ k + j ≤ d
  · have h' : d ≤ k + j + i ∧ k + j ≤ d ∧ k + i ≤ d := by omega
    simp only [ite_eq_left h, ite_eq_left h', Matrix.star_apply, map_mul, map_pow,
      Complex.conj_ofReal]
    have he : k + j + i - d = k + i + j - d := by omega
    rw [he]
    have hc : Real.sqrt (i.factorial * (d - i).factorial * j.factorial * (d - j).factorial) /
        (k.factorial * (k + i + j - d).factorial * (d - j - k).factorial *
          (d - i - k).factorial) =
        Real.sqrt (j.factorial * (d - j).factorial * i.factorial * (d - i).factorial) /
        (k.factorial * (k + i + j - d).factorial * (d - i - k).factorial *
          (d - j - k).factorial) := by
      congr 1
      · congr 1
        ring
      · ring
    rw [hc]
    simp only [starRingEnd_apply]
    ring
  · have h' : ¬ (d ≤ k + j + i ∧ k + j ≤ d ∧ k + i ≤ d) := by omega
    rw [ite_eq_right h, ite_eq_right h', map_zero]

/-- The entry formula relates inversion to conjugate transpose. -/
private theorem matrixElement_inv_eq_conj (d : ℕ) (i j : Fin (d + 1)) (g : TauCeti.SU2) :
    matrixElement d i j g⁻¹ = conj (matrixElement d j i g) := by
  rw [matrixElement_eq_entrySum, matrixElement_eq_entrySum,
    ← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star, entrySum_star]

/-- The adjoint acts by the inverse group element. -/
private theorem adjoint_unitaryModel (d : ℕ) (g : TauCeti.SU2) :
    (unitaryModel d g).adjoint = unitaryModel d g⁻¹ := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.ext
  intro j
  simp only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply]
  ext i
  have hcoord (v : EuclideanSpace ℂ (Fin (d + 1))) :
      ⟪EuclideanSpace.single i 1, v⟫_ℂ = v i := by
    rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [← hcoord, ← hcoord, ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm,
    ← matrixElement_def, ← matrixElement_def, matrixElement_inv_eq_conj]

/-- The factorial normalization makes the symmetric powers unitary. -/
theorem isUnitary_unitaryModel (d : ℕ) : (unitaryModel d).IsUnitary := by
  rw [ContRepresentation.isUnitary_iff_norm_map]
  intro g
  apply (LinearMap.norm_map_iff_inner_map_map (unitaryModel d g)).mpr
  intro v w
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_unitaryModel]
  have hw : unitaryModel d g⁻¹ (unitaryModel d g w) = w := by
    simpa only [inv_inv, ContRepresentation.toRepresentation_apply] using
      Representation.self_inv_apply (unitaryModel d).toRepresentation g⁻¹ w
  rw [hw]

end SFVK.SU2
