/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import SFVK.Spheres.Zonal
public import SFVK.Spheres.DiskPolynomials
public import SFVK.Spheres.SphereMeasure
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.LIntegral
import SFVKMathlib.Analysis.Complex.EulerPhases
import TauCeti.Analysis.Complex.Euclidean.Space
import TauCeti.Analysis.InnerProductSpace.Gram.Rigidity
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Analysis.SpecialFunctions.Beta.Basic
import TauCeti.Probability.Distributions.Beta.Basic
import TauCeti.Probability.Distributions.Beta.PDF
import TauCeti.Probability.Distributions.Uniform.Sphere.Dirichlet

/-!
# The complex sphere `S^{2n-1}` under `U(n)` and disk polynomials

Transitivity of `U(n)`, the density `((n - 1)/π)(1 - |w|²)^{n-2}` of `⟪η, ξ⟫` on the unit disc,
the Gel'fand pair `(U(n), K_η)`; the dimension, decomposition and branching of the harmonics of
bidegree `(p, q)`; the symmetry, Jacobi form, orthogonality and bound of the disk polynomials;
the `U(n)`-zonal harmonic and its uniqueness; the spherical functions of `(U(n), K_η)` with their
classification and addition theorem; and the expansion of the zonal polynomials of `SO(2n)` in
disk polynomials. The unitary orbit and double-coset proofs use Tau Ceti's Gram rigidity.
The sphere projection uses Tau Ceti's Beta law for the real coordinate block and Mathlib's
complex polar coordinates.

Sources: Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2, §11.2.1
(18)–(20), p. 295 (dimension of `H^{p,q}`), §11.2.2 (1)–(15), pp. 295–297 (the representations,
the `U(n - 1)`-fixed vector and branching), §11.3.2 (4)–(6), p. 309 (the zonal spherical functions
as `₂F₁` and Jacobi polynomials), §11.4.5, p. 345 (the disk polynomials; the printed case `m < n`
has `z` in place of `z̄`); Klimyk–Vilenkin, *Representations of Lie Groups and Special Functions*,
in Encyclopaedia of Mathematical Sciences 59, Part II, Chapter 2, §2.8, (34), p. 182.
-/

public noncomputable section

open MeasureTheory Polynomial Real Set
open scoped Nat ComplexConjugate InnerProductSpace

namespace SFVK.Spheres

/-! ### The complex sphere -/

namespace UnitaryActions

/-- Unitary matrices realize equality of Gram data. -/
private theorem exists_unitaryRotate_eq_of_inner_eq {n : ℕ} {ι : Type*}
    {v w : ι → EuclideanSpace ℂ (Fin n)}
    (h : ∀ i j, ⟪v i, v j⟫_ℂ = ⟪w i, w j⟫_ℂ) :
    ∃ g : UnitaryMatrixGroup n, ∀ i, unitaryRotate g (v i) = w i := by
  obtain ⟨e, he⟩ := TauCeti.exists_linearIsometryEquiv_of_inner_eq h
  obtain ⟨g, hg⟩ := Matrix.UnitaryGroup.toLinearIsometryEquiv_surjective e
  exact ⟨g, fun i => by
    simpa only [unitaryRotate_def, ← hg, Matrix.UnitaryGroup.toLinearIsometryEquiv_apply,
      Matrix.toLpLin_apply] using he i⟩

/-- The matrix action preserves complex inner products. -/
private theorem inner_unitaryRotate_unitaryRotate {n : ℕ} (g : UnitaryMatrixGroup n)
    (x y : EuclideanSpace ℂ (Fin n)) :
    ⟪unitaryRotate g x, unitaryRotate g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simpa only [unitaryRotate_def, Matrix.UnitaryGroup.toLinearIsometryEquiv_apply,
    Matrix.toLpLin_apply] using (Matrix.UnitaryGroup.toLinearIsometryEquiv g).inner_map_map x y

/-- Two unitary matrices with the same overlap lie in the same double coset. -/
private theorem exists_mul_mul_eq_of_inner_eq {n : ℕ} {η : EuclideanSpace ℂ (Fin n)}
    {g h : UnitaryMatrixGroup n}
    (hinner : ⟪η, unitaryRotate g η⟫_ℂ = ⟪η, unitaryRotate h η⟫_ℂ) :
    ∃ k₁ ∈ unitaryStabilizer η, ∃ k₂ ∈ unitaryStabilizer η, k₁ * g * k₂ = h := by
  let v : Bool → EuclideanSpace ℂ (Fin n) := fun b => if b then unitaryRotate g η else η
  let w : Bool → EuclideanSpace ℂ (Fin n) := fun b => if b then unitaryRotate h η else η
  have hgram (i j : Bool) : ⟪v i, v j⟫_ℂ = ⟪w i, w j⟫_ℂ := by
    cases i <;> cases j
    · rfl
    · exact hinner
    · change ⟪unitaryRotate g η, η⟫_ℂ = ⟪unitaryRotate h η, η⟫_ℂ
      rw [← inner_conj_symm (unitaryRotate g η) η,
        ← inner_conj_symm (unitaryRotate h η) η, hinner]
    · change ⟪unitaryRotate g η, unitaryRotate g η⟫_ℂ =
        ⟪unitaryRotate h η, unitaryRotate h η⟫_ℂ
      rw [inner_unitaryRotate_unitaryRotate, inner_unitaryRotate_unitaryRotate]
  obtain ⟨k, hk⟩ := exists_unitaryRotate_eq_of_inner_eq hgram
  have hkη : unitaryRotate k η = η := by simpa [v, w] using hk false
  have hkg : unitaryRotate k (unitaryRotate g η) = unitaryRotate h η := by
    simpa [v, w] using hk true
  let k₂ := (k * g)⁻¹ * h
  refine ⟨k, mem_unitaryStabilizer.mpr hkη, k₂, mem_unitaryStabilizer.mpr ?_, ?_⟩
  · have hkg' : unitaryRotate (k * g) η = unitaryRotate h η := by
      rw [unitaryRotate_mul, hkg]
    rw [show k₂ = (k * g)⁻¹ * h from rfl, unitaryRotate_mul, ← hkg',
      unitaryRotate_inv_unitaryRotate]
  · calc
      _ = (k * g * (k * g)⁻¹) * h := (mul_assoc _ _ _).symm
      _ = _ := by rw [mul_inv_cancel, one_mul]

/-- The overlap at a coordinate vector is the corresponding diagonal entry. -/
private theorem inner_single_unitaryRotate_single {n : ℕ} (j : Fin n) (g : UnitaryMatrixGroup n) :
    ⟪EuclideanSpace.single j 1, unitaryRotate g (EuclideanSpace.single j 1)⟫_ℂ =
      g.val j j := by
  rw [EuclideanSpace.inner_single_left]
  have h : (Matrix.UnitaryGroup.toLinearIsometryEquiv g) (EuclideanSpace.single j 1) =
      unitaryRotate g (EuclideanSpace.single j 1) := by
    rw [Matrix.UnitaryGroup.toLinearIsometryEquiv_apply, unitaryRotate_def, Matrix.toLpLin_apply]
  rw [← h, Matrix.UnitaryGroup.toLinearIsometryEquiv_single]
  simp

/-- The matrix transpose is continuous on the unitary group. -/
private theorem continuous_transpose {n : ℕ} :
    Continuous (Matrix.UnitaryGroup.transpose : UnitaryMatrixGroup n → UnitaryMatrixGroup n) :=
  (continuous_matrix fun i j => continuous_subtype_val.matrix_elem j i).subtype_mk _

/-- Transposition preserves normalized Haar measure on the unitary group. -/
private theorem measurePreserving_transpose (n : ℕ) :
    MeasurePreserving (Matrix.UnitaryGroup.transpose : UnitaryMatrixGroup n → UnitaryMatrixGroup n)
      (TauCeti.haarProb (UnitaryMatrixGroup n)) (TauCeti.haarProb (UnitaryMatrixGroup n)) := by
  let c : UnitaryMatrixGroup n →* UnitaryMatrixGroup n :=
    { toFun := Matrix.UnitaryGroup.map_star
      map_one' := by
        apply Subtype.ext
        exact Matrix.map_one (n := Fin n) Complex.conjAe (map_zero _) (map_one _)
      map_mul' := fun a b => by
        apply Subtype.ext
        exact Matrix.map_mul (f := Complex.conjAe) }
  have hc : Continuous c :=
    (continuous_matrix fun i j => Complex.continuous_conj.comp
      (continuous_subtype_val.matrix_elem i j)).subtype_mk _
  have hs : Function.Surjective c := fun a => ⟨c a, by
    apply Subtype.ext
    ext i j
    change conj (conj (a.val i j)) = a.val i j
    exact Complex.conj_conj _⟩
  have hm := (MonoidHom.measurePreserving (μ := TauCeti.haarProb (UnitaryMatrixGroup n))
    (ν := TauCeti.haarProb (UnitaryMatrixGroup n)) hc hs rfl)
  exact ((Measure.measurePreserving_inv _).comp hm).congr continuous_transpose.measurable
    (Filter.Eventually.of_forall Matrix.UnitaryGroup.map_star_inv_eq_transpose)

/-- Matrix transposition as a measurable involution. -/
private def transposeMeasurableEquiv (n : ℕ) : UnitaryMatrixGroup n ≃ᵐ UnitaryMatrixGroup n where
  toEquiv := Function.Involutive.toPerm (f := Matrix.UnitaryGroup.transpose)
    (fun a => by apply Subtype.ext; exact Matrix.transpose_transpose a.val)
  measurable_toFun := continuous_transpose.measurable
  measurable_invFun := continuous_transpose.measurable

end UnitaryActions

open UnitaryActions in
set_option linter.unusedVariables false in
/-- **Transitivity.** For `n ≥ 1`, `U(n)` acts transitively on the unit sphere of `ℂⁿ`. -/
theorem exists_unitaryRotate_eq {n : ℕ} (hn : 1 ≤ n) {η ξ : EuclideanSpace ℂ (Fin n)}
    (hη : ‖η‖ = 1) (hξ : ‖ξ‖ = 1) : ∃ g : UnitaryMatrixGroup n, unitaryRotate g η = ξ := by
  obtain ⟨g, hg⟩ := exists_unitaryRotate_eq_of_inner_eq (ι := Unit) (v := fun _ => η)
    (w := fun _ => ξ) (fun _ _ => by rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
      hη, hξ])
  exact ⟨g, hg ()⟩

namespace DiskMeasure

open TauCeti TauCeti.Probability ProbabilityTheory
open scoped ENNReal

/-- The complex normalized sphere measure is the uniform law on its real unit sphere. -/
private theorem complexSphereMeasure_eq_uniformSphereMeasure (n : ℕ) :
    complexSphereMeasure n = uniformSphereMeasure (EuclideanSpace ℂ (Fin n)) := by
  rw [complexSphereMeasure_def, uniformSphereMeasure_def]

/-- Real and imaginary coordinates as a real linear isometry. -/
private def realify (n : ℕ) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n ⊕ Fin n) where
  toLinearEquiv := (WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).trans
    (complexToRealEuclidean (Fin n)).toLinearEquiv
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [LinearEquiv.trans_apply, complexToRealEuclidean_apply, Complex.sq_norm,
      Complex.normSq_apply, ← pow_two]

/-- The squared norm of one complex coordinate has the Beta block law. -/
private theorem map_norm_sq_eval_complexSphereMeasure {n : ℕ} (hn : 2 ≤ n) (j : Fin n) :
    (complexSphereMeasure n).map (fun ξ : ComplexSphere n => ‖ξ.val j‖ ^ 2) =
      betaMeasure 1 ((n : ℝ) - 1) := by
  classical
  let S : Finset (Fin n ⊕ Fin n) := {Sum.inl j, Sum.inr j}
  have hs : S.Nonempty := ⟨Sum.inl j, by simp [S]⟩
  have hsc : Sᶜ.Nonempty := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    obtain ⟨k, hk⟩ := exists_ne j
    exact ⟨Sum.inl k, by simp [S, hk]⟩
  let e := realify n
  let E : ComplexSphere n → Metric.sphere (0 : EuclideanSpace ℝ (Fin n ⊕ Fin n)) 1 :=
    Subtype.map e fun x hx => by simpa using hx
  have hmap : (complexSphereMeasure n).map E = uniformSphereMeasure (_) := by
    rw [complexSphereMeasure_eq_uniformSphereMeasure]
    exact e.map_uniformSphereMeasure
  let f (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n ⊕ Fin n)) 1) :=
    ∑ i ∈ S, (u.val i) ^ 2
  have hF : (fun ξ : ComplexSphere n => ‖ξ.val j‖ ^ 2) = f ∘ E := by
    funext ξ
    change ‖ξ.val j‖ ^ 2 = ∑ i ∈ S, (realify n ξ.val) i ^ 2
    simp [realify, LinearEquiv.trans_apply, S, complexToRealEuclidean_apply, Complex.sq_norm,
      Complex.normSq_apply, ← pow_two]
  rw [hF, ← Measure.map_map (by fun_prop : Measurable f)
    (e.continuous.measurable.subtype_map _), hmap, map_sum_sq_uniformSphereMeasure hs hsc]
  have hS : S.card = 2 := by simp [S]
  have hcard : Sᶜ.card = n + n - 2 := by rw [Finset.card_compl, hS]; simp
  rw [hS, hcard]
  push_cast [Nat.cast_sub (show 2 ≤ n + n by omega)]
  congr 1 <;> ring

/-- A complex isometry preserves normalized sphere measure. -/
private theorem map_complexSphereMeasure_isometry {n : ℕ}
    (e : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    (complexSphereMeasure n).map (Subtype.map e fun x hx => by simpa using hx) =
      complexSphereMeasure n := by
  let e' : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
    ⟨e.toLinearEquiv.restrictScalars ℝ, e.norm_map⟩
  rw [complexSphereMeasure_eq_uniformSphereMeasure]
  exact e'.map_uniformSphereMeasure

/-- The Beta block law for the squared modulus in a unit direction. -/
private theorem map_norm_sq_inner_complexSphereMeasure {n : ℕ} (hn : 2 ≤ n)
    {η : EuclideanSpace ℂ (Fin n)} (hη : ‖η‖ = 1) :
    (complexSphereMeasure n).map (fun ξ : ComplexSphere n => ‖⟪η, ξ.val⟫_ℂ‖ ^ 2) =
      betaMeasure 1 ((n : ℝ) - 1) := by
  let j : Fin n := ⟨0, by omega⟩
  obtain ⟨g, hg⟩ := exists_unitaryRotate_eq (show 1 ≤ n by omega) hη
    (show ‖(EuclideanSpace.single j 1 : EuclideanSpace ℂ (Fin n))‖ = 1 by simp)
  let e := Matrix.UnitaryGroup.toLinearIsometryEquiv g
  have he : e η = EuclideanSpace.single j 1 := by
    simpa only [e, Matrix.UnitaryGroup.toLinearIsometryEquiv_apply, unitaryRotate_def,
      Matrix.toLpLin_apply] using hg
  let S : ComplexSphere n → ComplexSphere n := Subtype.map e fun x hx => by simpa using hx
  have hm : (complexSphereMeasure n).map S = complexSphereMeasure n :=
    map_complexSphereMeasure_isometry e
  have hc (x : ComplexSphere n) : ⟪η, x.val⟫_ℂ = (S x).val j := by
    rw [← e.inner_map_map, he, EuclideanSpace.inner_single_left]
    simp [S]
  simp_rw [hc]
  change (complexSphereMeasure n).map ((fun ζ : ComplexSphere n => ‖ζ.val j‖ ^ 2) ∘ S) = _
  rw [← Measure.map_map (by fun_prop) (e.continuous.measurable.subtype_map _), hm,
    map_norm_sq_eval_complexSphereMeasure hn]

/-- Multiplication of every coordinate by one unit complex number. -/
private def circleIsometry (n : ℕ) (c : Circle) :
    EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n) where
  toFun z := (c : ℂ) • z
  invFun z := ((c⁻¹ : Circle) : ℂ) • z
  left_inv z := by
    beta_reduce
    rw [smul_smul, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_smul]
  right_inv z := by
    beta_reduce
    rw [smul_smul, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one, one_smul]
  map_add' x y := smul_add _ _ _
  map_smul' a x := by simp [smul_smul, mul_comm (c : ℂ) a]
  norm_map' z := by simp [norm_smul]

/-- The complex sphere marginal is invariant under rotations of the disk. -/
private theorem map_mul_circle_map_inner_complexSphereMeasure {n : ℕ}
    (η : EuclideanSpace ℂ (Fin n)) (u : Circle) :
    ((complexSphereMeasure n).map (fun ξ : ComplexSphere n => ⟪η, ξ.val⟫_ℂ)).map
      (fun z => (u : ℂ) * z) =
        (complexSphereMeasure n).map (fun ξ : ComplexSphere n => ⟪η, ξ.val⟫_ℂ) := by
  let e := circleIsometry n u
  let U : ComplexSphere n → ComplexSphere n := Subtype.map e fun x hx => by simpa using hx
  have hU : (complexSphereMeasure n).map U = complexSphereMeasure n :=
    map_complexSphereMeasure_isometry e
  calc
    _ = (complexSphereMeasure n).map ((fun ξ : ComplexSphere n => ⟪η, ξ.val⟫_ℂ) ∘ U) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext ξ
      exact (inner_smul_right (𝕜 := ℂ) η ξ.val (u : ℂ)).symm
    _ = _ := by
      rw [← Measure.map_map (by fun_prop) (e.continuous.measurable.subtype_map _), hU]

/-- A rotation-invariant measure on the plane is determined by its squared-radius law. -/
private theorem lintegral_eq_circleAverage_norm_sq {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : ∀ u : Circle, μ.map (fun z => (u : ℂ) * z) = μ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂μ = ∫⁻ t, (∫⁻ u : Circle, f ((u : ℂ) * (Real.sqrt t : ℂ)) ∂haarProb Circle)
      ∂(μ.map (fun z => ‖z‖ ^ 2)) := by
  let ν := haarProb Circle
  have hinner (u : Circle) : ∫⁻ z, f ((u : ℂ) * z) ∂μ = ∫⁻ z, f z ∂μ := by
    rw [← lintegral_map hf (by fun_prop), hμ]
  have hrad (z : ℂ) : ∫⁻ u : Circle, f ((u : ℂ) * z) ∂ν =
      ∫⁻ u : Circle, f ((u : ℂ) * (Real.sqrt (‖z‖ ^ 2) : ℂ)) ∂ν := by
    rw [Real.sqrt_sq (norm_nonneg _)]
    let c := Circle.exp (Complex.arg z)
    rw [← lintegral_mul_right_eq_self (μ := ν) (fun u : Circle => f ((u : ℂ) * ‖z‖)) c]
    refine lintegral_congr fun u => ?_
    rw [Circle.coe_mul, mul_assoc, mul_comm (c : ℂ), show (‖z‖ : ℂ) * (c : ℂ) = z from
      Complex.norm_mul_exp_arg_mul_I z]
  have hm : Measurable (fun t : ℝ => ∫⁻ u : Circle, f ((u : ℂ) * (Real.sqrt t : ℂ)) ∂ν) :=
    Measurable.lintegral_prod_right (by fun_prop)
  calc
    _ = ∫⁻ u : Circle, ∫⁻ z, f ((u : ℂ) * z) ∂μ ∂ν := by simp [hinner, ν]
    _ = ∫⁻ z, ∫⁻ u : Circle, f ((u : ℂ) * z) ∂ν ∂μ :=
      lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ z, ∫⁻ u : Circle, f ((u : ℂ) * (Real.sqrt (‖z‖ ^ 2) : ℂ)) ∂ν ∂μ :=
      lintegral_congr hrad
    _ = _ := (lintegral_map hm (by fun_prop)).symm

/-- The radial density of the sphere projection against planar area on the unit disk. -/
private def diskDensity (n : ℕ) (z : ℂ) : ℝ :=
  ((n : ℝ) - 1) / Real.pi * (1 - ‖z‖ ^ 2) ^ (n - 2)

/-- The radial density in polar coordinates with the squared radius as variable. -/
private theorem lintegral_diskDensity_eq_beta_circle {n : ℕ} (hn : 2 ≤ n)
    {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (diskDensity n z) * f z =
      ∫⁻ t, (∫⁻ u : Circle, f ((u : ℂ) * (Real.sqrt t : ℂ)) ∂haarProb Circle)
        ∂betaMeasure 1 ((n : ℝ) - 1) := by
  let b := ((n : ℝ) - 1)
  let C := b / Real.pi
  let A := Ioo (-Real.pi) Real.pi
  let F (r : ℝ) (u : Circle) := f ((u : ℂ) * r)
  let G (t : ℝ) := ∫⁻ u, F (Real.sqrt t) u ∂haarProb Circle
  have hb : 0 < b := by
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    exact sub_pos.mpr hn'
  have hC : 0 < C := div_pos hb Real.pi_pos
  have hG : Measurable G := Measurable.lintegral_prod_right (by fun_prop)
  have ha : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hangles (r : ℝ) : ∫⁻ θ in A, F r (Circle.exp θ) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ u, F r u ∂haarProb Circle := by
    rw [← lintegral_map (by fun_prop : Measurable (F r)) Circle.exp.continuous.measurable]
    have hmap := Circle.map_exp_restrict_Ioo (-Real.pi)
    rw [ha] at hmap
    rw [show A = Ioo (-Real.pi) Real.pi from rfl, hmap, lintegral_smul_measure, smul_eq_mul]
  have hpow : b - 1 = ↑(n - 2) := by dsimp [b]; push_cast [Nat.cast_sub hn]; ring
  have hpdf (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      betaPDF 1 b t = ENNReal.ofReal (b * (1 - t) ^ (n - 2)) := by
    rw [betaPDF_of_pos_lt_one ht.1 ht.2, ProbabilityTheory.beta_one_left hb, one_div_div, div_one,
      sub_self, Real.rpow_zero, mul_one, hpow, Real.rpow_natCast]
  have hpolar : (∫⁻ z in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (diskDensity n z) * f z) =
      ∫⁻ p in Ioo (0 : ℝ) 1 ×ˢ A, ENNReal.ofReal p.1 *
        (ENNReal.ofReal (C * (1 - p.1 ^ 2) ^ (n - 2)) * F p.1 (Circle.exp p.2)) := by
    let k (z : ℂ) := ENNReal.ofReal (diskDensity n z) * f z
    change (∫⁻ z in Metric.ball (0 : ℂ) 1, k z) = _
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,
      ← Complex.lintegral_comp_polarCoord_symm]
    have hequal : (Ioo (0 : ℝ) 1 ×ˢ A) = (Complex.polarCoord.symm ⁻¹'
        Metric.ball (0 : ℂ) 1) ∩ polarCoord.target := by
      ext p
      simp only [mem_inter_iff, mem_preimage, Metric.mem_ball, dist_zero_right,
        Complex.norm_polarCoord_symm, polarCoord_target, mem_prod, mem_Ioo, mem_Ioi, A]
      constructor
      · exact fun ⟨⟨hp, hp'⟩, hθ⟩ => ⟨by simpa [abs_of_pos hp] using hp', hp, hθ⟩
      · exact fun ⟨hp', hp, hθ⟩ => ⟨⟨hp, by simpa [abs_of_pos hp] using hp'⟩, hθ⟩
    let S := Complex.polarCoord.symm ⁻¹' Metric.ball (0 : ℂ) 1
    have hsymm : Continuous (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
      rw [funext Complex.polarCoord_symm_apply]
      fun_prop
    have hS : MeasurableSet S := hsymm.measurable Metric.isOpen_ball.measurableSet
    have hind : (fun p : ℝ × ℝ => ENNReal.ofReal p.1 *
        (Metric.ball (0 : ℂ) 1).indicator k (Complex.polarCoord.symm p)) =
        S.indicator (fun p => ENNReal.ofReal p.1 * k (Complex.polarCoord.symm p)) := by
      funext p
      by_cases hp : Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) 1
      · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ S from hp)]
      · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ S from hp), mul_zero]
    simp only [smul_eq_mul]
    rw [hind, lintegral_indicator hS, Measure.restrict_restrict hS, ← hequal]
    refine setLIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun p hp => ?_
    simp only [k, diskDensity, F, C, b]
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1.1]
    simp only [Complex.polarCoord_symm_apply, Circle.coe_exp, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    congr 3
    ring
  have hquad : (fun r : ℝ => r ^ 2) '' Ioo (0 : ℝ) 1 = Ioo 0 1 := by
    have hmono : StrictMonoOn (fun r : ℝ => r ^ 2) (Icc 0 1) :=
      fun _ hr _ hs hrs => (sq_lt_sq₀ hr.1 hs.1).mpr hrs
    have hcont : Continuous (fun r : ℝ => r ^ 2) := by fun_prop
    norm_num [hcont.continuousOn.image_Ioo_of_strictMonoOn zero_le_one hmono]
  calc
    _ = _ := hpolar
    _ = ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal (2 * r) *
        (ENNReal.ofReal (b * (1 - r ^ 2) ^ (n - 2)) * G (r ^ 2)) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
      refine setLIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
      simp only [lintegral_const_mul _ (by fun_prop : Measurable (fun θ => F r (Circle.exp θ))),
        lintegral_const_mul _ (by fun_prop : Measurable (fun θ =>
          ENNReal.ofReal (C * (1 - r ^ 2) ^ (n - 2)) * F r (Circle.exp θ))), hangles, G,
          Real.sqrt_sq hr.1.le]
      have hp : 0 ≤ (1 - r ^ 2) ^ (n - 2) := by
        apply pow_nonneg
        nlinarith [mul_nonneg hr.1.le (sub_nonneg.mpr hr.2.le)]
      have hconst : ENNReal.ofReal r * ENNReal.ofReal (C * (1 - r ^ 2) ^ (n - 2)) *
          ENNReal.ofReal (2 * Real.pi) = ENNReal.ofReal (2 * r) *
            ENNReal.ofReal (b * (1 - r ^ 2) ^ (n - 2)) := by
        rw [← ENNReal.ofReal_mul hr.1.le, ← ENNReal.ofReal_mul (mul_nonneg hr.1.le
          (mul_nonneg hC.le hp)), ← ENNReal.ofReal_mul (mul_nonneg zero_le_two hr.1.le)]
        congr 1
        dsimp [C]
        field_simp [Real.pi_ne_zero]
      simp only [← mul_assoc, hconst]
    _ = ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (b * (1 - t) ^ (n - 2)) * G t := by
      have hmono : MonotoneOn (fun r : ℝ => r ^ 2) (Ioo 0 1) :=
        fun _ hr _ hs hrs => (sq_le_sq₀ hr.1.le hs.1.le).mpr hrs
      have hder (r : ℝ) : HasDerivWithinAt (fun r : ℝ => r ^ 2) (2 * r) (Ioo 0 1) r := by
        simpa using (hasDerivAt_pow 2 r).hasDerivWithinAt (s := Ioo 0 1)
      conv_rhs => rw [← hquad, lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
        measurableSet_Ioo (fun r _ => hder r) hmono]
    _ = _ := by
      rw [TauCeti.Probability.betaMeasure_eq_withDensity_restrict_Ioo,
        lintegral_withDensity_eq_lintegral_mul _ (measurable_betaPDF _ _) hG]
      refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
      change ENNReal.ofReal (b * (1 - t) ^ (n - 2)) * G t = betaPDF 1 b t * G t
      rw [hpdf t ht]

/-- The projection law of the normalized sphere measure as a weighted area measure. -/
private theorem map_inner_complexSphereMeasure {n : ℕ} (hn : 2 ≤ n)
    {η : EuclideanSpace ℂ (Fin n)} (hη : ‖η‖ = 1) :
    (complexSphereMeasure n).map (fun ξ : ComplexSphere n => ⟪η, ξ.val⟫_ℂ) =
      ((volume : Measure ℂ).restrict (Metric.ball 0 1)).withDensity
        (fun w => ENNReal.ofReal (diskDensity n w)) := by
  let μ := complexSphereMeasure n
  have : IsFiniteMeasure μ := by
    change IsFiniteMeasure (complexSphereMeasure n)
    rw [complexSphereMeasure_eq_uniformSphereMeasure]
    infer_instance
  let innerCoordinate (ξ : ComplexSphere n) : ℂ := ⟪η, ξ.val⟫_ℂ
  have hm : Measurable innerCoordinate := by fun_prop
  refine Measure.ext_of_lintegral _ fun h hh => ?_
  change (∫⁻ z, h z ∂μ.map innerCoordinate) = _
  rw [lintegral_eq_circleAverage_norm_sq (map_mul_circle_map_inner_complexSphereMeasure η) hh,
    Measure.map_map (by fun_prop) hm]
  change (∫⁻ t, (∫⁻ u : Circle, h ((u : ℂ) * (Real.sqrt t : ℂ)) ∂haarProb Circle)
    ∂(μ.map (fun ξ => ‖⟪η, ξ.val⟫_ℂ‖ ^ 2))) = _
  rw [map_norm_sq_inner_complexSphereMeasure hn hη,
    lintegral_withDensity_eq_lintegral_mul _ (by unfold diskDensity; fun_prop :
      Measurable (fun w => ENNReal.ofReal (diskDensity n w))) hh]
  exact (lintegral_diskDensity_eq_beta_circle hn hh).symm

end DiskMeasure

open DiskMeasure in
/-- **Disc density.** For `n ≥ 2` and a unit vector `η`, the image of the normalized sphere
measure of `ℂⁿ` under `ξ ↦ ⟪η, ξ⟫` has density `((n - 1)/π)(1 - |w|²)^{n-2}` on the unit disc. -/
theorem integral_inner_complexSphereMeasure {n : ℕ} (hn : 2 ≤ n)
    {η : EuclideanSpace ℂ (Fin n)} (hη : ‖η‖ = 1) (f : ℂ → ℂ) (hf : Continuous f) :
    ∫ ξ : ComplexSphere n, f ⟪η, (ξ : EuclideanSpace ℂ (Fin n))⟫_ℂ ∂complexSphereMeasure n =
      ∫ w in Metric.ball (0 : ℂ) 1, (((n : ℝ) - 1) / π * (1 - ‖w‖ ^ 2) ^ (n - 2) : ℝ) * f w := by
  rw [← integral_map (by fun_prop : Measurable
      (fun ξ : ComplexSphere n => ⟪η, ξ.val⟫_ℂ)).aemeasurable hf.aestronglyMeasurable,
    map_inner_complexSphereMeasure hn hη, integral_withDensity_eq_integral_toReal_smul
      (by unfold diskDensity; fun_prop : Measurable (fun w => ENNReal.ofReal (diskDensity n w)))
      (Filter.Eventually.of_forall fun w => ENNReal.ofReal_lt_top) f]
  refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun w hw => ?_
  have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball] using hw
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hd : 0 ≤ diskDensity n w := by
    dsimp [diskDensity]
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr hn'.le) Real.pi_pos.le)
      (pow_nonneg (by nlinarith [mul_nonneg (norm_nonneg w) (sub_nonneg.mpr hw'.le)]) _)
  rw [ENNReal.toReal_ofReal hd, Complex.real_smul]
  rfl

open UnitaryActions in
/-- **`(U(n), K_η)` is a Gel'fand pair**, for every `n` and every `η`. -/
theorem isGelfandPair_unitaryMatrixGroup (n : ℕ) (η : EuclideanSpace ℂ (Fin n)) :
    Subgroup.IsGelfandPair (unitaryStabilizer η) (TauCeti.haarProb (UnitaryMatrixGroup n)) := by
  let μ := TauCeti.haarProb (UnitaryMatrixGroup n)
  by_cases hη : η = 0
  · apply Subgroup.isGelfandPair_of_measurePreserving_anti (τ := MeasurableEquiv.inv _)
      (Measure.measurePreserving_inv μ) (fun x y => mul_inv_rev x y)
    intro g
    refine ⟨g⁻¹ * g⁻¹, mem_unitaryStabilizer.mpr ?_, 1, (unitaryStabilizer η).one_mem, ?_⟩
    · simp [hη, unitaryRotate_def]
    · change g⁻¹ * g⁻¹ * g * 1 = g⁻¹
      group
  have hn : 0 < n := by
    by_contra! hn
    have hnzero : n = 0 := by omega
    subst n
    exact hη (by ext i; exact Fin.elim0 i)
  let j : Fin n := ⟨0, hn⟩
  let e : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j 1
  let a : ℂ := ‖η‖
  have ha : a ≠ 0 := by
    change ((‖η‖ : ℝ) : ℂ) ≠ 0
    exact_mod_cast norm_ne_zero_iff.mpr hη
  have hnorm : ‖a⁻¹ • η‖ = 1 := by
    rw [norm_smul, norm_inv]
    change ‖((‖η‖ : ℝ) : ℂ)‖⁻¹ * ‖η‖ = 1
    rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr hη
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  obtain ⟨u, hu⟩ := exists_unitaryRotate_eq hn hnorm he
  have humap : unitaryRotate u η = a • e := by
    rw [← hu]
    simp only [unitaryRotate_def, map_smul, smul_smul, mul_inv_cancel₀ ha, one_smul]
  let c := (MeasurableEquiv.mulLeft u).trans (MeasurableEquiv.mulRight u⁻¹)
  let c' := (MeasurableEquiv.mulLeft u⁻¹).trans (MeasurableEquiv.mulRight u)
  let τ := (c.trans (transposeMeasurableEquiv n)).trans c'
  have hc : MeasurePreserving c μ μ :=
    (measurePreserving_mul_right μ u⁻¹).comp (measurePreserving_mul_left μ u)
  have hc' : MeasurePreserving c' μ μ :=
    (measurePreserving_mul_right μ u).comp (measurePreserving_mul_left μ u⁻¹)
  have hτ : MeasurePreserving τ μ μ := hc'.comp ((measurePreserving_transpose n).comp hc)
  have hτapply (g : UnitaryMatrixGroup n) :
      τ g = u⁻¹ * Matrix.UnitaryGroup.transpose (u * g * u⁻¹) * u := rfl
  refine Subgroup.isGelfandPair_of_measurePreserving_anti hτ (fun g h => ?_) (fun g => ?_)
  · have hprod (g h : UnitaryMatrixGroup n) : Matrix.UnitaryGroup.transpose (g * h) =
        Matrix.UnitaryGroup.transpose h * Matrix.UnitaryGroup.transpose g :=
      Subtype.ext (Matrix.transpose_mul g.val h.val)
    rw [hτapply, hτapply, hτapply,
      show u * (g * h) * u⁻¹ = (u * g * u⁻¹) * (u * h * u⁻¹) by group, hprod]
    group
  · apply exists_mul_mul_eq_of_inner_eq
    have hc (g : UnitaryMatrixGroup n) :
        ⟪η, unitaryRotate g η⟫_ℂ =
          conj a * a * ⟪e, unitaryRotate (u * g * u⁻¹) e⟫_ℂ := by
      calc
        _ = ⟪unitaryRotate u η, unitaryRotate (u * g * u⁻¹) (unitaryRotate u η)⟫_ℂ := by
          rw [← unitaryRotate_mul, show u * g * u⁻¹ * u = u * g by group, unitaryRotate_mul,
            inner_unitaryRotate_unitaryRotate]
        _ = _ := by
          rw [humap, unitaryRotate_def, map_smul, ← unitaryRotate_def, inner_smul_left,
            inner_smul_right]
          ring
    rw [hc, hc (τ g), hτapply,
      show u * (u⁻¹ * Matrix.UnitaryGroup.transpose (u * g * u⁻¹) * u) * u⁻¹ =
        Matrix.UnitaryGroup.transpose (u * g * u⁻¹) by group]
    simp only [e, inner_single_unitaryRotate_single]
    rfl

/-! ### Harmonics of bidegree `(p, q)` -/

/-- **Dimension of `H^{p,q}`** (Vilenkin–Klimyk, Vol. 2, §11.2.1 (18), p. 295). For `n ≥ 2`,
`dim H^{p,q} = (p + n - 2)! (q + n - 2)! (p + q + n - 1)/((n - 1)! (n - 2)! p! q!)`. -/
theorem finrank_bidegreeHarmonic_mul {n : ℕ} (hn : 2 ≤ n) (p q : ℕ) :
    Module.finrank ℂ (bidegreeHarmonic n p q) * ((n - 1)! * (n - 2)! * p ! * q !) =
      (p + n - 2)! * (q + n - 2)! * (p + q + n - 1) := by
  sorry

/-- **Real and complex harmonics.** `dim H_m(ℝ^{2n}) = ∑_{p+q=m} dim H^{p,q}(ℂⁿ)`. -/
theorem finrank_harmonicSubmodule_eq_sum_finrank_bidegreeHarmonic (n m : ℕ) :
    Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (2 * n)) ℝ m) =
      ∑ p ∈ Finset.range (m + 1), Module.finrank ℂ (bidegreeHarmonic n p (m - p)) := by
  sorry

/-- **Branching dimension for `U(n + 1) ↓ U(n)`** (Vilenkin–Klimyk, Vol. 2, §11.2.2,
pp. 295–297). For `n ≥ 1`, `dim H^{p,q}(ℂ^{n+1}) = ∑_{a ≤ p, b ≤ q} dim H^{a,b}(ℂⁿ)`. -/
theorem finrank_bidegreeHarmonic_succ {n : ℕ} (hn : 1 ≤ n) (p q : ℕ) :
    Module.finrank ℂ (bidegreeHarmonic (n + 1) p q) =
      ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (q + 1),
        Module.finrank ℂ (bidegreeHarmonic n a b) := by
  sorry

/-! ### Disk polynomials -/

/-- **Bound.** `|R^{n-2}_{p,q}(w)| ≤ 1` on the closed unit disc, for `n ≥ 2`. -/
theorem norm_diskPolynomial_le_one {n : ℕ} (hn : 2 ≤ n) (p q : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖diskPolynomial ((n : ℝ) - 2) p q w‖ ≤ 1 := by
  sorry

/-! ### The `U(n)`-zonal harmonic -/

/-- **The `U(n)`-zonal harmonic lies in `H^{p,q}`**, for `n ≥ 2` and a unit vector `η`. -/
theorem diskHarmonic_mem_bidegreeHarmonic {n : ℕ} (hn : 2 ≤ n) (p q : ℕ)
    {η : EuclideanSpace ℂ (Fin n)} (hη : ‖η‖ = 1) :
    diskHarmonic n p q η ∈ bidegreeHarmonic n p q := by
  sorry

set_option linter.unusedVariables false in
/-- **Values on the sphere.** For `n ≥ 2` and `|ξ| = 1`, the `U(n)`-zonal harmonic takes the
value `R^{n-2}_{p,q}(⟪η, ξ⟫)`. -/
theorem evalC_diskHarmonic {n : ℕ} (hn : 2 ≤ n) (p q : ℕ) (η : EuclideanSpace ℂ (Fin n))
    {ξ : EuclideanSpace ℂ (Fin n)} (hξ : ‖ξ‖ = 1) :
    evalC ξ (diskHarmonic n p q η) = diskPolynomial ((n : ℝ) - 2) p q ⟪η, ξ⟫_ℂ := by
  simp only [diskHarmonic_def, diskPolynomial_def, evalC_def, map_sum, map_mul, map_sub, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
  have innerCoordinates (x y : EuclideanSpace ℂ (Fin n)) :
      (∑ j, conj (x j) * y j) = ⟪x, y⟫_ℂ := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Pi.star_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [innerCoordinates, show (∑ j, η j * conj (ξ j)) = conj ⟪η, ξ⟫_ℂ by
      rw [inner_conj_symm]
      exact (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans (innerCoordinates ξ η),
    show (∑ j, ξ j * conj (ξ j)) = 1 by
      rw [show (∑ j, ξ j * conj (ξ j)) = ⟪ξ, ξ⟫_ℂ from
        (Finset.sum_congr rfl fun j _ => mul_comm _ _).trans (innerCoordinates ξ ξ),
        inner_self_eq_norm_sq_to_K, hξ]
      norm_num,
    show (n : ℝ) - 2 + 1 = (n : ℝ) - 1 by ring]
  have hprod : ⟪η, ξ⟫_ℂ * conj ⟪η, ξ⟫_ℂ = ((‖⟪η, ξ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    exact (Complex.mul_conj _).trans (congrArg Complex.ofReal (Complex.normSq_eq_norm_sq _))
  rw [hprod]
  push_cast
  rfl

/-- **Class one for `U(n)`** (Vilenkin–Klimyk, Vol. 2, §11.2.2 (11)–(13), p. 297). For `n ≥ 2`
and a unit vector `η`, a `K_η`-invariant element of `H^{p,q}` is a multiple of the `U(n)`-zonal
harmonic. -/
theorem eq_smul_diskHarmonic {n : ℕ} (hn : 2 ≤ n) {p q : ℕ} {η : EuclideanSpace ℂ (Fin n)}
    (hη : ‖η‖ = 1) {f : MvPolynomial (Fin n ⊕ Fin n) ℂ} (hf : f ∈ bidegreeHarmonic n p q)
    (hinv : ∀ k ∈ unitaryStabilizer η, ∀ z : EuclideanSpace ℂ (Fin n),
      evalC (unitaryRotate k z) f = evalC z f) :
    f = evalC η f • diskHarmonic n p q η := by
  sorry

/-! ### Spherical functions of `(U(n), K_η)` -/

/-- **Disk polynomials are spherical functions** (Vilenkin–Klimyk, Vol. 2, §11.3.2 (4)–(6),
p. 309). For `n ≥ 2`, a unit vector `η` and a left-invariant probability measure `ν` on `K_η`,
`g ↦ R^{n-2}_{p,q}(⟪g η, η⟫)` is a spherical function of `(U(n), K_η)`. -/
theorem isSphericalFunction_diskSpherical {n : ℕ} (hn : 2 ≤ n) (p q : ℕ)
    {η : EuclideanSpace ℂ (Fin n)} (hη : ‖η‖ = 1) (ν : Measure (unitaryStabilizer η))
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] :
    Subgroup.IsSphericalFunction (unitaryStabilizer η) ν (diskSpherical n p q η) := by
  sorry

/-- **Classification of the spherical functions** of `(U(n), K_η)`, `n ≥ 2`: each is
`diskSpherical n p q η` for some `p, q`. -/
theorem exists_eq_diskSpherical {n : ℕ} (hn : 2 ≤ n) {η : EuclideanSpace ℂ (Fin n)}
    (hη : ‖η‖ = 1) (ν : Measure (unitaryStabilizer η)) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] {Φ : UnitaryMatrixGroup n → ℂ}
    (hΦ : Subgroup.IsSphericalFunction (unitaryStabilizer η) ν Φ) :
    ∃ p q, Φ = diskSpherical n p q η := by
  sorry

/-- **Addition theorem for `H^{p,q}`.** For `n ≥ 2` and an `L²(complexSphereMeasure n)`-
orthonormal basis `Y` of `H^{p,q}`, `∑ᵢ Yᵢ(x) conj Yᵢ(y) = dim H^{p,q} · R^{n-2}_{p,q}(⟪y, x⟫)`. -/
theorem sum_evalC_mul_conj_evalC_eq {n : ℕ} (hn : 2 ≤ n) (p q : ℕ)
    (Y : Fin (Module.finrank ℂ (bidegreeHarmonic n p q)) → bidegreeHarmonic n p q)
    (hY : ∀ i j, ∫ ξ : ComplexSphere n, conj (evalC (ξ : EuclideanSpace ℂ (Fin n)) (Y i : _)) *
      evalC (ξ : EuclideanSpace ℂ (Fin n)) (Y j : _) ∂complexSphereMeasure n =
        if i = j then 1 else 0)
    (x y : ComplexSphere n) :
    ∑ i, evalC (x : EuclideanSpace ℂ (Fin n)) (Y i : _) *
        conj (evalC (y : EuclideanSpace ℂ (Fin n)) (Y i : _)) =
      Module.finrank ℂ (bidegreeHarmonic n p q) *
        diskPolynomial ((n : ℝ) - 2) p q
          ⟪(y : EuclideanSpace ℂ (Fin n)), (x : EuclideanSpace ℂ (Fin n))⟫_ℂ := by
  sorry

/-! ### `SO(2n)` and `U(n)` -/

/-- **Zonal polynomials of `SO(2n)` as sums of disk polynomials.** For `n ≥ 2` and every
`w ∈ ℂ`, `dim H_m(ℝ^{2n}) ω_{2n,m}(Re w) = ∑_{p+q=m} dim H^{p,q}(ℂⁿ) R^{n-2}_{p,q}(w)`. -/
theorem zonalPolynomial_eq_sum_diskPolynomial {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (w : ℂ) :
    ((Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (2 * n)) ℝ m) *
        (zonalPolynomial (2 * n) m).eval w.re : ℝ) : ℂ) =
      ∑ p ∈ Finset.range (m + 1),
        Module.finrank ℂ (bidegreeHarmonic n p (m - p)) *
          diskPolynomial ((n : ℝ) - 2) p (m - p) w := by
  sorry

end SFVK.Spheres
