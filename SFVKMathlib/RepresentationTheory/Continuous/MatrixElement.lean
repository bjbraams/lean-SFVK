/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.RepresentationTheory.Continuous.MatrixCoefficient
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Matrix elements in a Hilbert basis

For a continuous representation `U` on a complex inner product space and a Hilbert basis `e`,
the matrix element `U.matrixElement e m n g` is `⟪e m, U g (e n)⟫`, conjugate-linear in the row
vector, as in Edmonds, *Angular Momentum in Quantum Mechanics*, (4.1.10), p. 55.

Tau Ceti's `ContRepresentation.matrixCoeff` uses the opposite inner-product order and assumes
continuity in the operator-norm topology, which fails for the infinite-dimensional
representations of noncompact groups. The definition here assumes no continuity; the bridge
`matrixElement_eq_conj_matrixCoeff` relates the two where both apply.

## Main results

* `ContRepresentation.hasSum_matrixElement_mul`: the matrix element of a product is the sum over
  intermediate indices, by Mathlib's Hilbert-basis expansion.
* `ContRepresentation.matrixElement_inv`: for a unitary representation the matrix element of the
  inverse is the conjugate of the transposed matrix element.
-/

public section

open scoped InnerProductSpace ComplexConjugate

namespace ContRepresentation

variable {G H ι : Type*} [Monoid G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The row `m`, column `n` matrix element of `U g` in the Hilbert basis `e`. -/
@[expose]
noncomputable def matrixElement (U : ContRepresentation ℂ G H) (e : HilbertBasis ι ℂ H)
    (m n : ι) (g : G) : ℂ :=
  ⟪e m, U g (e n)⟫_ℂ

/-- The matrix element is the inner product with the row vector in the first argument. -/
theorem matrixElement_def (U : ContRepresentation ℂ G H) (e : HilbertBasis ι ℂ H)
    (m n : ι) (g : G) : U.matrixElement e m n g = ⟪e m, U g (e n)⟫_ℂ :=
  (rfl)

/-- Continuous orbit maps give continuous matrix elements. -/
theorem continuous_matrixElement [TopologicalSpace G] (U : ContRepresentation ℂ G H)
    (e : HilbertBasis ι ℂ H) (m n : ι) (h : Continuous fun g => U g (e n)) :
    Continuous (U.matrixElement e m n) :=
  continuous_const.inner h

/-- For a norm-continuous representation, the matrix element is the conjugate of Tau Ceti's
coefficient with the input vector first. -/
theorem matrixElement_eq_conj_matrixCoeff [TopologicalSpace G] (U : ContRepresentation ℂ G H)
    (hU : Continuous U) (e : HilbertBasis ι ℂ H) (m n : ι) (g : G) :
    U.matrixElement e m n g = conj (U.matrixCoeff hU (e n) (e m) g) := by
  rw [matrixElement_def, ContRepresentation.matrixCoeff_apply, inner_conj_symm]

/-- The identity operator has Kronecker-delta matrix elements. -/
@[simp]
theorem matrixElement_one [DecidableEq ι] (U : ContRepresentation ℂ G H) (e : HilbertBasis ι ℂ H)
    (m n : ι) : U.matrixElement e m n 1 = if m = n then 1 else 0 := by
  simpa only [matrixElement_def, map_one, one_apply_eq_self] using
    (orthonormal_iff_ite.mp e.orthonormal m n)

/-- The matrix element of a product is the sum of the products through the intermediate
indices. -/
theorem hasSum_matrixElement_mul [CompleteSpace H] (U : ContRepresentation ℂ G H)
    (e : HilbertBasis ι ℂ H) (m n : ι) (g h : G) :
    HasSum (fun k => U.matrixElement e m k g * U.matrixElement e k n h)
      (U.matrixElement e m n (g * h)) := by
  simpa only [matrixElement_def, map_mul, mul_apply_eq_comp, Function.comp_apply,
    ContinuousLinearMap.adjoint_inner_left] using
    e.hasSum_inner_mul_inner ((U g).adjoint (e m)) (U h (e n))

/-- The matrix-product series is absolutely summable. -/
theorem summable_norm_matrixElement_mul [CompleteSpace H] (U : ContRepresentation ℂ G H)
    (e : HilbertBasis ι ℂ H) (m n : ι) (g h : G) :
    Summable (fun k => ‖U.matrixElement e m k g * U.matrixElement e k n h‖) :=
  (U.hasSum_matrixElement_mul e m n g h).summable.norm

/-- The matrix element of the inverse of a unitary operator is the conjugate of the transposed
matrix element. -/
theorem matrixElement_inv {G' : Type*} [Group G'] (U : ContRepresentation ℂ G' H)
    (hU : U.IsUnitary) (e : HilbertBasis ι ℂ H) (m n : ι) (g : G') :
    U.matrixElement e m n g⁻¹ = conj (U.matrixElement e n m g) := by
  rw [matrixElement_def, matrixElement_def, inner_conj_symm, hU.inner_map_left]

end ContRepresentation
