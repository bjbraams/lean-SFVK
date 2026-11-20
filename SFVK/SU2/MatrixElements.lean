/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU2.Basic.MatrixElements
public import SFVK.SU2.UnitaryModel

/-!
# Matrix elements of `SU(2)`: unitarity and the entry polynomial

In the unitary normalization the matrix elements of the inverse are the conjugate transposes.
For spin one half the finite entry polynomial gives the entries of the defining representation
in reverse index order (Edmonds, *Angular Momentum in Quantum Mechanics*, pp. 56–57).
-/

public section

open scoped ComplexConjugate

namespace SFVK.SU2

/-- The inverse element gives the conjugate transpose in the normalized basis. -/
theorem matrixElement_inv (d : ℕ) (i j : Fin (d + 1)) (g : TauCeti.SU2) :
    matrixElement d i j g⁻¹ = conj (matrixElement d j i g) :=
  (unitaryModel d).matrixElement_inv (isUnitary_unitaryModel d)
    (EuclideanSpace.basisFun _ ℂ).toHilbertBasis i j g

/-- Spin one half is the defining representation in reverse index order. -/
theorem matrixElement_spinHalf (i j : Fin 2) (g : TauCeti.SU2) :
    matrixElement 1 i j g = (g : Matrix (Fin 2) (Fin 2) ℂ) (Fin.rev i) (Fin.rev j) := by
  rw [matrixElement_eq_entrySum]
  fin_cases i <;> fin_cases j <;>
    norm_num [entrySum, Finset.sum_range_succ, Nat.factorial, Fin.rev]

end SFVK.SU2
