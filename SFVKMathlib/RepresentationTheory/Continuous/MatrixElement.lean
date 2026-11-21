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

Let `U` act on a real or complex inner product space with Hilbert basis `e`.
The matrix element `U.matrixElement e m n g` is `⟪e m, U g (e n)⟫`, conjugate-linear in the row
vector, as in Edmonds, *Angular Momentum in Quantum Mechanics*, (4.1.10), p. 55.

Tau Ceti's `ContRepresentation.matrixCoeff` uses the opposite inner-product order and assumes
operator-norm continuity. The bridge `matrixElement_eq_conj_matrixCoeff` relates the two under
that hypothesis. A continuous orbit map is enough for continuity of a single matrix element.

## Main results

* `ContRepresentation.hasSum_matrixElement_mul`: the matrix element of a product is the sum over
  intermediate indices, by Mathlib's Hilbert-basis expansion.
* `ContRepresentation.hasSum_norm_sq_matrixElement`: by Mathlib's `lp.hasSum_norm`, the squared
  norms of the coefficients of a unitary image of a basis vector sum to one.
* `ContRepresentation.matrixElement_inv`: for a unitary representation the matrix element of the
  inverse is the conjugate of the transposed matrix element.
-/

public section

open scoped InnerProductSpace ComplexConjugate

namespace ContRepresentation

variable {𝕜 G H ι : Type*} [RCLike 𝕜] [Monoid G] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H]

/-- The row `m`, column `n` matrix element of `U g` in the Hilbert basis `e`. -/
@[expose]
noncomputable def matrixElement (U : ContRepresentation 𝕜 G H) (e : HilbertBasis ι 𝕜 H)
    (m n : ι) (g : G) : 𝕜 :=
  ⟪e m, U g (e n)⟫_𝕜

/-- The matrix element is the inner product with the row vector in the first argument. -/
theorem matrixElement_def (U : ContRepresentation 𝕜 G H) (e : HilbertBasis ι 𝕜 H)
    (m n : ι) (g : G) : U.matrixElement e m n g = ⟪e m, U g (e n)⟫_𝕜 :=
  (rfl)

/-- Continuous orbit maps give continuous matrix elements. -/
theorem continuous_matrixElement [TopologicalSpace G] (U : ContRepresentation 𝕜 G H)
    (e : HilbertBasis ι 𝕜 H) (m n : ι) (h : Continuous fun g => U g (e n)) :
    Continuous (U.matrixElement e m n) :=
  continuous_const.inner h

/-- For a norm-continuous representation, the matrix element is the conjugate of Tau Ceti's
coefficient with the input vector first. -/
theorem matrixElement_eq_conj_matrixCoeff [TopologicalSpace G] (U : ContRepresentation 𝕜 G H)
    (hU : Continuous U) (e : HilbertBasis ι 𝕜 H) (m n : ι) (g : G) :
    U.matrixElement e m n g = star (U.matrixCoeff hU (e n) (e m) g) := by
  rw [matrixElement_def, ContRepresentation.matrixCoeff_apply]
  exact (inner_conj_symm _ _).symm

/-- The identity operator has Kronecker-delta matrix elements. -/
@[simp]
theorem matrixElement_one [DecidableEq ι] (U : ContRepresentation 𝕜 G H) (e : HilbertBasis ι 𝕜 H)
    (m n : ι) : U.matrixElement e m n 1 = if m = n then 1 else 0 := by
  simpa only [matrixElement_def, map_one, one_apply_eq_self] using
    (orthonormal_iff_ite.mp e.orthonormal m n)

/-- The matrix element of a product is the sum of the products through the intermediate
indices. -/
theorem hasSum_matrixElement_mul [CompleteSpace H] (U : ContRepresentation 𝕜 G H)
    (e : HilbertBasis ι 𝕜 H) (m n : ι) (g h : G) :
    HasSum (fun k => U.matrixElement e m k g * U.matrixElement e k n h)
      (U.matrixElement e m n (g * h)) := by
  simpa only [matrixElement_def, map_mul, mul_apply_eq_comp, Function.comp_apply,
    ContinuousLinearMap.adjoint_inner_left] using
    e.hasSum_inner_mul_inner ((U g).adjoint (e m)) (U h (e n))

/-- The matrix-product series is absolutely summable. -/
theorem summable_norm_matrixElement_mul [CompleteSpace H] (U : ContRepresentation 𝕜 G H)
    (e : HilbertBasis ι 𝕜 H) (m n : ι) (g h : G) :
    Summable (fun k => ‖U.matrixElement e m k g * U.matrixElement e k n h‖) :=
  (U.hasSum_matrixElement_mul e m n g h).summable.norm

/-- Parseval in a Hilbert basis gives total squared mass one for the image of a basis vector
under a unitary representation. -/
theorem hasSum_norm_sq_matrixElement (U : ContRepresentation 𝕜 G H)
    (hU : U.IsUnitary) (e : HilbertBasis ι 𝕜 H) (n : ι) (g : G) :
    HasSum (fun m => ‖U.matrixElement e m n g‖ ^ 2) 1 := by
  let f := U g (e n)
  have hnorm : ‖e.repr f‖ = 1 := by
    rw [e.repr.norm_map]
    exact (hU.norm_map _ _).trans (e.orthonormal.norm_eq_one n)
  have hS : HasSum (fun i => ‖e.repr f i‖ ^ 2) (‖e.repr f‖ ^ 2) := by
    apply_mod_cast lp.hasSum_norm ?_ (e.repr f)
    simp
  simpa only [hnorm, one_pow, HilbertBasis.repr_apply_apply, matrixElement_def, f] using hS

/-- The matrix element of the inverse of a unitary operator is the conjugate of the transposed
matrix element. -/
theorem matrixElement_inv {G' : Type*} [Group G'] (U : ContRepresentation 𝕜 G' H)
    (hU : U.IsUnitary) (e : HilbertBasis ι 𝕜 H) (m n : ι) (g : G') :
    U.matrixElement e m n g⁻¹ = star (U.matrixElement e n m g) := by
  rw [matrixElement_def, matrixElement_def, ← hU.inner_map_left]
  exact (inner_conj_symm _ _).symm

end ContRepresentation
