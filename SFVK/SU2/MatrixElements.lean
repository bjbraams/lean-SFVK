/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SFVK.RepresentationTheory.MatrixElements
public import SFVK.SU2.UnitaryModel

/-!
# Matrix elements of `SU(2)`

In the spin `d/2` representation the indices `i, j` correspond to the weights
`i - d/2, j - d/2`. The matrix convention is Edmonds (4.1.10), p. 55.
The entry polynomial is the binomial expansion of the symmetric-power action,
as in the spinor calculation on pp. 56–57 and Vilenkin–Klimyk, Vol. 1, §6.3.1, p. 280.
-/

public noncomputable section

open scoped ComplexConjugate InnerProductSpace

namespace SFVK.SU2

/-- The matrix element in row `i`, column `j` of the normalized spin `d/2` action. -/
def matrixElement (d : ℕ) (i j : Fin (d + 1)) (g : TauCeti.SU2) : ℂ :=
  SFVK.matrixElement (unitaryModel d) (EuclideanSpace.basisFun _ ℂ).toHilbertBasis i j g

/-- The matrix element is the inner product against the `i`-th standard unit vector. -/
theorem matrixElement_def (d : ℕ) (i j : Fin (d + 1)) (g : TauCeti.SU2) :
    matrixElement d i j g =
      ⟪EuclideanSpace.single i 1, unitaryModel d g (EuclideanSpace.single j 1)⟫_ℂ := by
  simp [matrixElement, SFVK.matrixElement_def]

/-- The matrix elements multiply as matrices under the group law. -/
theorem matrixElement_mul (d : ℕ) (i j : Fin (d + 1)) (g h : TauCeti.SU2) :
    matrixElement d i j (g * h) = ∑ k, matrixElement d i k g * matrixElement d k j h :=
  (SFVK.hasSum_matrixElement_mul (unitaryModel d)
    (EuclideanSpace.basisFun _ ℂ).toHilbertBasis i j g h).tsum_eq.symm.trans
    (tsum_fintype _)

/-- The inverse element gives the conjugate transpose in the normalized basis. -/
theorem matrixElement_inv (d : ℕ) (i j : Fin (d + 1)) (g : TauCeti.SU2) :
    matrixElement d i j g⁻¹ = conj (matrixElement d j i g) :=
  SFVK.matrixElement_inv (unitaryModel d) (isUnitary_unitaryModel d)
    (EuclideanSpace.basisFun _ ℂ).toHilbertBasis i j g

/-- The finite polynomial in the entries of a matrix giving the normalized symmetric-power
coefficient. The summation conditions ensure that all four monomial exponents are nonnegative. -/
def entrySum (d i j : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    if d ≤ k + i + j ∧ k + i ≤ d ∧ k + j ≤ d then
      ((Real.sqrt (i.factorial * (d - i).factorial * j.factorial * (d - j).factorial) /
          (k.factorial * (k + i + j - d).factorial * (d - j - k).factorial *
            (d - i - k).factorial) : ℝ) : ℂ) *
        A 0 0 ^ (k + i + j - d) * A 0 1 ^ (d - j - k) * A 1 0 ^ (d - i - k) * A 1 1 ^ k
    else 0

/-- The normalized matrix element is given by the finite entry polynomial. -/
theorem matrixElement_eq_entrySum (d : ℕ) (i j : Fin (d + 1)) (g : TauCeti.SU2) :
    matrixElement d i j g = entrySum d i j (g : Matrix (Fin 2) (Fin 2) ℂ) := by
  sorry

/-- The coefficient at the lowest weight of spin one half is the bottom-right matrix entry. -/
theorem entrySum_one_zero_zero (A : Matrix (Fin 2) (Fin 2) ℂ) :
    entrySum 1 0 0 A = A 1 1 := by
  norm_num [entrySum, Finset.sum_range_succ, Nat.factorial]

/-- Spin one half is the defining representation in reverse index order. -/
theorem matrixElement_one (i j : Fin 2) (g : TauCeti.SU2) :
    matrixElement 1 i j g = (g : Matrix (Fin 2) (Fin 2) ℂ) (Fin.rev i) (Fin.rev j) := by
  rw [matrixElement_eq_entrySum]
  fin_cases i <;> fin_cases j <;>
    norm_num [entrySum, Finset.sum_range_succ, Nat.factorial, Fin.rev]

end SFVK.SU2
