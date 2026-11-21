/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVKMathlib.RepresentationTheory.Continuous.MatrixElement
public import SFVK.SU2.Basic.UnitaryModel
import TauCeti.Algebra.Polynomial.Binomial
import TauCeti.LinearAlgebra.SymmetricPower.Lift

/-!
# Matrix elements of `SU(2)`

In the spin `d/2` representation the indices `i, j` correspond to the magnetic weights
`i - d/2, j - d/2`. The matrix convention is Edmonds, *Angular Momentum in Quantum Mechanics*,
(4.1.10), p. 55. The entry polynomial `entrySum` is the binomial expansion of the
symmetric-power action, as in the spinor calculation of Edmonds, pp. 56–57, and Vilenkin–Klimyk,
*Representation of Lie Groups and Special Functions*, Vol. 1, §6.3.1, p. 280. The proof uses
Tau Ceti's symmetric-power lift and its formula for the coefficients of powers of a linear
polynomial.
-/

public noncomputable section

open scoped ComplexConjugate InnerProductSpace TensorProduct

namespace SFVK.SU2

/-- The matrix element in row `i`, column `j` of the normalized spin `d/2` action. -/
@[expose]
def matrixElement (d : ℕ) (i j : Fin (d + 1)) (g : TauCeti.SU2) : ℂ :=
  (unitaryModel d).matrixElement (EuclideanSpace.basisFun _ ℂ).toHilbertBasis i j g

/-- The matrix element is the inner product against the `i`-th standard unit vector. -/
theorem matrixElement_def (d : ℕ) (i j : Fin (d + 1)) (g : TauCeti.SU2) :
    matrixElement d i j g =
      ⟪EuclideanSpace.single i 1, unitaryModel d g (EuclideanSpace.single j 1)⟫_ℂ := by
  simp [matrixElement, ContRepresentation.matrixElement_def]

/-- The matrix elements multiply as matrices under the group law. -/
theorem matrixElement_mul (d : ℕ) (i j : Fin (d + 1)) (g h : TauCeti.SU2) :
    matrixElement d i j (g * h) = ∑ k, matrixElement d i k g * matrixElement d k j h :=
  ((unitaryModel d).hasSum_matrixElement_mul
    (EuclideanSpace.basisFun _ ℂ).toHilbertBasis i j g h).tsum_eq.symm.trans
    (tsum_fintype _)

/-- The finite polynomial in the entries of a matrix giving the normalized symmetric-power
coefficient. The summation conditions ensure that all four monomial exponents are nonnegative. -/
@[expose]
def entrySum (d i j : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑ k ∈ Finset.range (d + 1),
    if d ≤ k + i + j ∧ k + i ≤ d ∧ k + j ≤ d then
      ((Real.sqrt (i.factorial * (d - i).factorial * j.factorial * (d - j).factorial) /
          (k.factorial * (k + i + j - d).factorial * (d - j - k).factorial *
            (d - i - k).factorial) : ℝ) : ℂ) *
        A 0 0 ^ (k + i + j - d) * A 0 1 ^ (d - j - k) * A 1 0 ^ (d - i - k) * A 1 1 ^ k
    else 0

/-- The coefficient at the lowest weight of spin one half is the bottom-right matrix entry. -/
theorem entrySum_one_zero_zero (A : Matrix (Fin 2) (Fin 2) ℂ) :
    entrySum 1 0 0 A = A 1 1 := by
  norm_num [entrySum, Finset.sum_range_succ, Nat.factorial]

namespace WeightPolynomial

open TauCeti TauCeti.SU2 Polynomial

/-- The linear polynomial representing a vector of the defining representation. -/
private def fromVector : (Fin 2 → ℂ) →ₗ[ℂ] ℂ[X] where
  toFun v := C (v 1) + C (v 0) * X
  map_add' v w := by simp only [Pi.add_apply, map_add, add_mul]; abel
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply,
      Algebra.smul_def, Polynomial.algebraMap_eq, mul_add]
    rw [mul_assoc]

/-- The constant and linear coefficients are the second and first coordinates. -/
private theorem fromVector_apply (v : Fin 2 → ℂ) :
    fromVector v = C (v 1) + C (v 0) * X := rfl

/-- The product of the linear polynomials attached to the tensor factors. -/
private def multilinear (d : ℕ) :
    MultilinearMap (RingHom.id ℂ) (fun _ : Fin d => Fin 2 → ℂ) ℂ[X] :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin d) ℂ[X]).compLinearMap fun _ => fromVector

/-- The product map multiplies the linear polynomials of the input vectors. -/
private theorem multilinear_apply (d : ℕ) (v : Fin d → Fin 2 → ℂ) :
    multilinear d v = ∏ i, fromVector (v i) := rfl

/-- The polynomial obtained by multiplying the factors of a symmetric tensor. -/
private def fromTensor (d : ℕ) :
    Sym[ℂ]^d(Fin 2 → ℂ) →ₗ[ℂ] ℂ[X] :=
  SymmetricPower.lift (multilinear d) fun σ => by
    apply MultilinearMap.ext
    intro v
    simpa only [MultilinearMap.domDomCongr_apply, multilinear_apply] using
      Equiv.prod_comp σ (fun i => fromVector (v i))

/-- A pure symmetric tensor maps to the product of its linear factors. -/
private theorem fromTensor_apply_tprod (d : ℕ) (v : Fin d → Fin 2 → ℂ) :
    fromTensor d (⨂ₛ[ℂ] i, v i) = ∏ i, fromVector (v i) := by
  rw [fromTensor, SymmetricPower.lift_tprod, multilinear_apply]

/-- The image of a weight vector consists of two powers of linear factors. -/
private theorem fromTensor_symmetricPower (d : ℕ) (i : Fin (d + 1))
    (F : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) :
    fromTensor d (SymmetricPower.map F (weightBasis d i)) =
      fromVector (F (Pi.basisFun ℂ (Fin 2) 0)) ^ (i : ℕ) *
        fromVector (F (Pi.basisFun ℂ (Fin 2) 1)) ^ (d - (i : ℕ)) := by
  classical
  obtain ⟨f, hf⟩ := Sym.ofFn_surjective ((symFinTwoEquiv d).symm i)
  rw [weightBasis_apply, ← hf, Module.Basis.symmetricPower_apply,
    SymmetricPower.tprodOfSym_ofFn, SymmetricPower.map_tprod, fromTensor_apply_tprod]
  rw [← List.prod_ofFn]
  have hvalues := congrArg (fun s : Sym (Fin 2) d => (s : Multiset (Fin 2))) hf
  rw [Sym.coe_ofFn, coe_symFinTwoEquiv_symm_apply] at hvalues
  have hproducts := congrArg
    (fun s : Multiset (Fin 2) => (s.map fun k => fromVector (F (Pi.basisFun ℂ _ k))).prod)
    hvalues
  simpa only [Multiset.map_coe, List.map_ofFn, Function.comp_def, Multiset.prod_coe,
    Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate] using
    hproducts

/-- The weight vector of index `i` maps to `X ^ i`. -/
private theorem fromTensor_weightBasis (d : ℕ) (i : Fin (d + 1)) :
    fromTensor d (weightBasis d i) = X ^ (i : ℕ) := by
  have h := fromTensor_symmetricPower d i LinearMap.id
  simpa [fromVector, Fin.isValue, Pi.basisFun_apply, Pi.single_apply, zero_ne_one, one_ne_zero]
    using h

/-- Extracting a polynomial coefficient gives the corresponding weight coordinate. -/
private theorem coeff_fromTensor (d : ℕ) (v : Sym[ℂ]^d(Fin 2 → ℂ)) (i : Fin (d + 1)) :
    (fromTensor d v).coeff i = weightEquiv d v i := by
  have h : (lcoeff ℂ i).comp (fromTensor d) =
      (EuclideanSpace.proj i).toLinearMap.comp (weightEquiv d).toLinearMap := by
    apply (weightBasis d).ext
    intro k
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe]
    rw [weightEquiv_weightBasis,
      lcoeff_apply, fromTensor_weightBasis, coeff_X_pow]
    simp [PiLp.single_apply, Fin.ext_iff]
  exact DFunLike.congr_fun h v


/-- The symmetric power action substitutes the columns of the matrix. -/
private theorem fromTensor_symPower_weightBasis (d : ℕ) (g : TauCeti.SU2)
    (j : Fin (d + 1)) :
    let A := (g : Matrix (Fin 2) (Fin 2) ℂ)
    fromTensor d (symPower d g (weightBasis d j)) =
      (C (A 1 0) + C (A 0 0) * X) ^ (j : ℕ) *
        (C (A 1 1) + C (A 0 1) * X) ^ (d - (j : ℕ)) := by
  dsimp only
  have hmap : symPower d g = SymmetricPower.map
      (g : Matrix (Fin 2) (Fin 2) ℂ).mulVecLin := by
    have hstd : stdRep ℂ 2 (toGL g) = (g : Matrix (Fin 2) (Fin 2) ℂ).mulVecLin := by
      apply LinearMap.ext
      intro v
      rw [stdRep_apply_apply, coe_toGL, Matrix.mulVecLin_apply]
    rw [symPower_apply, symPowerRep, Representation.symmetricPower_apply, hstd]
  rw [hmap, fromTensor_symmetricPower]
  simp only [fromVector_apply, Matrix.mulVecLin_apply, Pi.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.col_apply]

/-- Scaling a vector multiplies its coordinate by the monomial norm. -/
private theorem monomialScale_apply_coordinate (d : ℕ) (i : Fin (d + 1))
    (v : EuclideanSpace ℂ (Fin (d + 1))) :
    monomialScale d v i = (monomialNorm d i : ℂ) * v i := by
  have h : (EuclideanSpace.projₗ i).comp (monomialScale d).toLinearEquiv.toLinearMap =
      (monomialNorm d i : ℂ) • EuclideanSpace.projₗ i := by
    apply (EuclideanSpace.basisFun (Fin (d + 1)) ℂ).toBasis.ext
    intro k
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    have hs := congrArg (fun v : EuclideanSpace ℂ (Fin (d + 1)) => v i)
      (monomialScale_single d k)
    refine hs.trans ?_
    have hproj (x : EuclideanSpace ℂ (Fin (d + 1))) : EuclideanSpace.projₗ i x = x i := rfl
    rw [hproj, PiLp.smul_apply, smul_eq_mul]
    by_cases hik : i = k
    · subst k
      rfl
    · simp only [PiLp.single_apply, ite_eq_right hik, mul_zero]
  exact DFunLike.congr_fun h v

/-- Inverse scaling divides a standard basis vector by the monomial norm. -/
private theorem monomialScale_symm_single (d : ℕ) (j : Fin (d + 1)) :
    (monomialScale d).symm (EuclideanSpace.single j 1) =
      (monomialNorm d j : ℂ)⁻¹ • EuclideanSpace.single j 1 := by
  apply (monomialScale d).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul, monomialScale_single, smul_smul,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.2 (monomialNorm_pos d j).ne'), one_smul]

/-- The diagonal normalization scales the polynomial coefficient. -/
private theorem matrixElement_eq_coeff (d : ℕ) (i j : Fin (d + 1)) (g : TauCeti.SU2) :
    let A := (g : Matrix (Fin 2) (Fin 2) ℂ)
    matrixElement d i j g = (monomialNorm d i / monomialNorm d j : ℝ) *
      (((C (A 1 0) + C (A 0 0) * X) ^ (j : ℕ) *
        (C (A 1 1) + C (A 0 1) * X) ^ (d - (j : ℕ))).coeff i) := by
  dsimp only
  rw [matrixElement_def, EuclideanSpace.inner_single_left, map_one, one_mul,
    unitaryModel_apply, monomialScale_symm_single, map_smul, symPowerModel_apply,
    weightEquiv_symm_single, monomialScale_apply_coordinate, PiLp.smul_apply, smul_eq_mul,
    ← coeff_fromTensor, fromTensor_symPower_weightBasis, Complex.ofReal_div, div_eq_mul_inv,
    mul_assoc]

/-- The two binomial coefficients supply the four factorials. -/
private theorem choose_mul_choose_eq_div_factorials (d j a b : ℕ) (ha : a ≤ j)
    (hb : b ≤ d - j) :
    (j.choose a : ℝ) * ((d - j).choose b : ℝ) =
      (j.factorial * (d - j).factorial : ℝ) /
        (((d - j - b).factorial : ℝ) * a.factorial * b.factorial * (j - a).factorial) := by
  have hleft : (j.choose a : ℝ) * a.factorial * (j - a).factorial = j.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial ha
  have hright : ((d - j).choose b : ℝ) * b.factorial * (d - j - b).factorial =
      (d - j).factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hb
  apply (eq_div_iff (by positivity)).2
  linear_combination
    (j.choose a : ℝ) * a.factorial * (j - a).factorial * hright +
      ((d - j).factorial : ℝ) * hleft

/-- The monomial norm ratio combines with the two binomial coefficients. -/
private theorem normalized_choose_mul (d : ℕ) (i j : Fin (d + 1)) (a b : ℕ)
    (ha : a ≤ (j : ℕ)) (hb : b ≤ d - (j : ℕ)) :
    (monomialNorm d i / monomialNorm d j) *
        (((j : ℕ).choose a : ℝ) * ((d - (j : ℕ)).choose b : ℝ)) =
      Real.sqrt ((i : ℕ).factorial * (d - (i : ℕ)).factorial *
        (j : ℕ).factorial * (d - (j : ℕ)).factorial) /
        ((((d - (j : ℕ) - b).factorial : ℝ) * a.factorial * b.factorial *
          ((j : ℕ) - a).factorial)) := by
  rw [choose_mul_choose_eq_div_factorials d j a b ha hb]
  have hs : (monomialNorm d j) ^ 2 =
      ((j : ℕ).factorial * (d - (j : ℕ)).factorial : ℝ) := by
    rw [monomialNorm_def, Real.sq_sqrt (by positivity)]
  rw [← hs]
  have hsqrt : Real.sqrt ((i : ℕ).factorial * (d - (i : ℕ)).factorial *
        (j : ℕ).factorial * (d - (j : ℕ)).factorial) =
        monomialNorm d i * monomialNorm d j := by
    rw [monomialNorm_def, monomialNorm_def, ← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  rw [hsqrt]
  field_simp [(monomialNorm_pos d j).ne']


/-- The coefficient convolution gives the factorial entry polynomial. -/
private theorem coeff_mul_eq_entrySum (d : ℕ) (i j : Fin (d + 1))
    (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (monomialNorm d i / monomialNorm d j : ℝ) *
      (((C (A 1 0) + C (A 0 0) * X) ^ (j : ℕ) *
        (C (A 1 1) + C (A 0 1) * X) ^ (d - (j : ℕ))).coeff i) =
      entrySum d i j A := by
  classical
  rw [entrySum, ← Finset.sum_filter, coeff_mul, Finset.mul_sum]
  simp_rw [TauCeti.coeff_C_add_C_mul_X_pow]
  -- The coefficient uses output exponents (a, b) with a + b = i.
  -- Reindex by the number of second-column factors in the bottom row, d - j - b.
  rw [← Finset.sum_subset (Finset.filter_subset
      (fun p : ℕ × ℕ => p.1 ≤ (j : ℕ) ∧ p.2 ≤ d - (j : ℕ)) (Finset.antidiagonal (i : ℕ)))]
  · refine Finset.sum_nbij' (fun p : ℕ × ℕ => d - (j : ℕ) - p.2)
      (fun k => (k + (i : ℕ) + (j : ℕ) - d, d - (j : ℕ) - k)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_range] at hp ⊢
      omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_range] at hk ⊢
      omega
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
      exact Prod.ext (by omega) (by omega)
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_range] at hk
      omega
    · intro p hp
      rcases p with ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
      have he : d - (j : ℕ) - b + (i : ℕ) + (j : ℕ) - d = a := by omega
      have hf : d - (j : ℕ) - (d - (j : ℕ) - b) = b := by omega
      have hg : d - (i : ℕ) - (d - (j : ℕ) - b) = (j : ℕ) - a := by omega
      simp only [he, hf, hg]
      have hc := congrArg Complex.ofReal (normalized_choose_mul d i j a b hp.2.1 hp.2.2)
      push_cast at hc ⊢
      rw [← hc]
      ring
  · intro p hp hnot
    simp only [Finset.mem_filter, hp, true_and, not_and_or, not_le] at hnot
    rcases hnot with ha | hb
    · simp [Nat.choose_eq_zero_of_lt ha]
    · simp [Nat.choose_eq_zero_of_lt hb]

end WeightPolynomial

/-- The normalized matrix element is given by the finite entry polynomial. -/
theorem matrixElement_eq_entrySum (d : ℕ) (i j : Fin (d + 1)) (g : TauCeti.SU2) :
    matrixElement d i j g = entrySum d i j (g : Matrix (Fin 2) (Fin 2) ℂ) :=
  (WeightPolynomial.matrixElement_eq_coeff d i j g).trans
    (WeightPolynomial.coeff_mul_eq_entrySum d i j g)


end SFVK.SU2
