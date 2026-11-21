/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Prod
import SFVK.MotionGroups.Polar
public import TauCeti.RepresentationTheory.Compact.Haar
public import TauCeti.Topology.Algebra.UnitaryGroup
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.Orbit
import TauCeti.MeasureTheory.Constructions.HaarToSphere
import TauCeti.Probability.Distributions.Beta.Symmetric
import TauCeti.Probability.Distributions.Uniform.Sphere.Coordinate
public import SFVK.Spheres.Basic

/-!
# The sphere `S^{n-1}` under `SO(n)`

Transitivity of `SO(n)` on the unit sphere, the double cosets of the stabilizer `K_η` of a unit
vector, invariance of the normalized sphere measure, the image of the Haar probability measure of
`SO(n)` under `g ↦ g η`, the density `c_n (1 - t²)^{(n-3)/2}` of `⟪η, x⟫`, and the Gel'fand pair
`(SO(n), K_η)`.

Sources: Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2, §9.1.9
(1)–(6), p. 22 (the sphere as `SO(n)/SO(n - 1)`, the invariant measure and its expression in
spherical coordinates); Wawrzyńczyk, *Group Representations and Special Functions*, §9.5,
p. 337 (the `K`-orbits on the sphere); Dieudonné, *Special Functions and Linear Representations
of Lie Groups*, §7, pp. 22–23.

The transitivity proof uses Tau Ceti's nondegenerate special orthogonal orbit theorem. The
projection law uses Tau Ceti's uniform-sphere projection and centered beta density.
-/

public noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace Real

namespace SFVK.Spheres

/-- Rotation of a vector is jointly continuous in the rotation and the vector. -/
theorem continuous_rotate {n : ℕ} :
    Continuous (fun p : RotationGroup n × EuclideanSpace ℝ (Fin n) => rotate p.1 p.2) := by
  simp_rw [rotate_def, ← Matrix.toEuclideanCLM_apply]
  exact (Matrix.continuous_toEuclideanCLM.comp
    (continuous_subtype_val.comp continuous_fst)).clm_apply continuous_snd

/-- The standard quadratic form agrees with the squared Euclidean norm. -/
private theorem standardForm_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toQuadraticForm' (1 : Matrix (Fin n) (Fin n) ℝ) x.ofLp = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, TauCeti.toQuadraticForm'_one_apply]
  simp only [dotProduct, pow_two]

/-- Orthogonality for the standard quadratic form agrees with Euclidean orthogonality. -/
private theorem isOrtho_standardForm_iff {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    (Matrix.toQuadraticForm' (1 : Matrix (Fin n) (Fin n) ℝ)).IsOrtho x.ofLp y.ofLp ↔
      ⟪x, y⟫_ℝ = 0 := by
  rw [← QuadraticMap.isOrtho_polarBilin, QuadraticMap.polarBilin_apply_apply,
    TauCeti.polar_toQuadraticForm'_one,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  simp

/-- The standard quadratic form on coordinates is nondegenerate. -/
private theorem nondegenerate_standardForm (n : ℕ) :
    (Matrix.toQuadraticForm' (1 : Matrix (Fin n) (Fin n) ℝ)).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, QuadraticMap.radical_eq_ker_polarBilin]
  refine le_antisymm (fun v hv => ?_) bot_le
  rw [Submodule.mem_bot]
  have h (i : Fin n) := LinearMap.congr_fun (LinearMap.mem_ker.mp hv) (Pi.single i 1)
  ext i
  simpa [QuadraticMap.polarBilin_apply_apply, TauCeti.polar_toQuadraticForm'_one,
    dotProduct_single_one] using h i

/-- Matrix rotation agrees with the Euclidean linear isometry of its orthogonal matrix. -/
private theorem rotate_eq_linearIsometryEquiv {n : ℕ} (g : RotationGroup n)
    (x : EuclideanSpace ℝ (Fin n)) :
    rotate g x = Matrix.UnitaryGroup.toLinearIsometryEquiv
      (⟨g.1, (Matrix.mem_specialOrthogonalGroup_iff.mp g.2).1⟩ :
        Matrix.orthogonalGroup (Fin n) ℝ) x := by
  apply WithLp.ofLp_injective 2
  rw [Matrix.UnitaryGroup.toLinearIsometryEquiv_apply, rotate_def, Matrix.toLpLin_apply]

/-- **Transitivity.** For `n ≥ 2`, `SO(n)` acts transitively on the unit sphere of `ℝⁿ`. -/
theorem exists_rotate_eq {n : ℕ} (hn : 2 ≤ n) {η ξ : EuclideanSpace ℝ (Fin n)} (hη : ‖η‖ = 1)
    (hξ : ‖ξ‖ = 1) : ∃ g : RotationGroup n, rotate g η = ξ := by
  let Q := Matrix.toQuadraticForm' (1 : Matrix (Fin n) (Fin n) ℝ)
  have hrank : 2 ≤ Module.finrank ℝ (Fin n → ℝ) := by simpa using hn
  obtain ⟨e, he⟩ := QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate Q
    (nondegenerate_standardForm n) hrank (x := η.ofLp) (y := ξ.ofLp)
    (by dsimp [Q]; rw [standardForm_apply, standardForm_apply, hη, hξ])
    (by dsimp [Q]; simp [standardForm_apply, hξ])
  let g : RotationGroup n := ⟨_, (TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ (Fin n)
    ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e.1).mpr e.2⟩
  use g
  apply (WithLp.ofLp_injective 2)
  change (LinearMap.toMatrix' (e.1 : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)).toLinearMap).mulVec
    η.ofLp = ξ.ofLp
  rw [LinearMap.toMatrix'_mulVec]
  exact he

/-- Rotations preserve the real inner product. -/
theorem inner_rotate_rotate {n : ℕ} (g : RotationGroup n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ⟪rotate g x, rotate g y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simp only [rotate_eq_linearIsometryEquiv, LinearIsometryEquiv.inner_map_map]

/-- A rotation fixing one vector can carry any vector to another with the same norm and
the same inner product with the fixed vector. -/
private theorem exists_stabilizer_rotate_eq {n : ℕ} (hn : 3 ≤ n)
    (η p q : EuclideanSpace ℝ (Fin n)) (hnorm : ‖p‖ = ‖q‖)
    (hinner : ⟪η, p⟫_ℝ = ⟪η, q⟫_ℝ) :
    ∃ k ∈ rotationStabilizer η, rotate k p = q := by
  classical
  by_cases hpq : p = q
  · exact ⟨1, (rotationStabilizer η).one_mem, by simp [hpq]⟩
  let E := EuclideanSpace ℝ (Fin n)
  let K := Submodule.span ℝ ({η, q} : Set E)
  have hK : Module.finrank ℝ K ≤ 2 := by
    apply (finrank_span_le_card _).trans
    simpa using (Finset.card_le_two (a := η) (b := q))
  have hdim := K.finrank_add_finrank_orthogonal
  have hdim' : Module.finrank ℝ E = n := by simp [E]
  have hpos : 0 < Module.finrank ℝ ↥Kᗮ := by omega
  have : Nontrivial ↥Kᗮ := Module.finrank_pos_iff.mp hpos
  obtain ⟨z, hz⟩ := exists_ne (0 : Kᗮ)
  have hz₀ : (z : E) ≠ 0 := by exact_mod_cast hz
  have hzη : ⟪(z : E), η⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (by simp)) z.property
  have hzq : ⟪(z : E), q⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (by simp)) z.property
  have hdη : ⟪p - q, η⟫_ℝ = 0 := by
    rw [real_inner_comm, inner_sub_right, hinner, sub_self]
  let Q := Matrix.toQuadraticForm' (1 : Matrix (Fin n) (Fin n) ℝ)
  have hzQ : Q z.val.ofLp ≠ 0 := by
    dsimp [Q]
    rw [standardForm_apply]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr hz₀)
  have hdQ : Q (p.ofLp - q.ofLp) ≠ 0 := by
    change Q (p - q).ofLp ≠ 0
    dsimp [Q]
    rw [standardForm_apply]
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpq))
  let : Invertible (Q z.val.ofLp) := (isUnit_iff_ne_zero.mpr hzQ).invertible
  let : Invertible (Q (p.ofLp - q.ofLp)) := (isUnit_iff_ne_zero.mpr hdQ).invertible
  let e := QuadraticMap.reflectionPairSpecialOrthogonal Q z.val.ofLp (p.ofLp - q.ofLp)
  let k : RotationGroup n := ⟨_, (TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ (Fin n)
    ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e.1).mpr e.2⟩
  have hk (x y : E) (h : e.1 x.ofLp = y.ofLp) : rotate k x = y := by
    apply WithLp.ofLp_injective 2
    change (LinearMap.toMatrix' e.1.toLinearMap).mulVec x.ofLp = y.ofLp
    rw [LinearMap.toMatrix'_mulVec]
    exact h
  have hQ : Q p.ofLp = Q q.ofLp := by dsimp [Q]; rw [standardForm_apply, standardForm_apply, hnorm]
  have hdη' : Q.IsOrtho (p.ofLp - q.ofLp) η.ofLp :=
    (isOrtho_standardForm_iff (p - q) η).mpr hdη
  refine ⟨k, mem_rotationStabilizer.mpr (hk η η ?_), hk p q ?_⟩
  · dsimp [e]
    rw [QuadraticMap.reflectionPairSpecialOrthogonal_apply,
      TauCeti.QuadraticMap.reflection_apply_of_isOrtho Q _ hdη',
      TauCeti.QuadraticMap.reflection_apply_of_isOrtho Q _ ((isOrtho_standardForm_iff _ _).mpr hzη)]
  · dsimp [e]
    rw [QuadraticMap.reflectionPairSpecialOrthogonal_apply,
      TauCeti.QuadraticMap.reflection_sub_apply_eq_of_map_eq Q _ _ hQ,
      TauCeti.QuadraticMap.reflection_apply_of_isOrtho Q _ ((isOrtho_standardForm_iff _ _).mpr hzq)]

/-- **Double cosets.** For `n ≥ 3` and a unit vector `η`, `h ∈ K_η g K_η` exactly when
`⟪η, g η⟫ = ⟪η, h η⟫`. -/
theorem exists_mul_mul_eq_iff_inner {n : ℕ} (hn : 3 ≤ n) {η : EuclideanSpace ℝ (Fin n)}
    (hη : ‖η‖ = 1) (g h : RotationGroup n) :
    (∃ k₁ ∈ rotationStabilizer η, ∃ k₂ ∈ rotationStabilizer η, h = k₁ * g * k₂) ↔
      ⟪η, rotate g η⟫_ℝ = ⟪η, rotate h η⟫_ℝ := by
  constructor
  · rintro ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    rw [mem_rotationStabilizer] at hk₁ hk₂
    rw [rotate_mul, rotate_mul, hk₂]
    calc
      ⟪η, rotate g η⟫_ℝ = ⟪rotate k₁ η, rotate k₁ (rotate g η)⟫_ℝ :=
        (inner_rotate_rotate k₁ _ _).symm
      _ = _ := by rw [hk₁]
  · intro hinner
    have hnorm (k : RotationGroup n) : ‖rotate k η‖ = 1 := by
      rw [rotate_eq_linearIsometryEquiv, LinearIsometryEquiv.norm_map, hη]
    obtain ⟨k₁, hk₁, heq⟩ := exists_stabilizer_rotate_eq hn η (rotate g η) (rotate h η)
      ((hnorm g).trans (hnorm h).symm) hinner
    refine ⟨k₁, hk₁, (k₁ * g)⁻¹ * h, mem_rotationStabilizer.mpr ?_, ?_⟩
    · calc
        rotate ((k₁ * g)⁻¹ * h) η = rotate (k₁ * g)⁻¹ (rotate h η) := rotate_mul _ _ _
        _ = rotate (k₁ * g)⁻¹ (rotate (k₁ * g) η) := by rw [← heq, rotate_mul]
        _ = η := rotate_inv_rotate _ _
    · group

/-- The stabilizer `K_η` is a closed subgroup of `SO(n)`. -/
theorem isClosed_rotationStabilizer {n : ℕ} (η : EuclideanSpace ℝ (Fin n)) :
    IsClosed (rotationStabilizer η : Set (RotationGroup n)) := by
  exact isClosed_eq (continuous_rotate.comp (continuous_id.prodMk continuous_const))
    continuous_const

/-- **Invariance of the sphere measure** under `SO(n)`. -/
theorem integral_rotate_sphereMeasure {n : ℕ} (g : RotationGroup n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) :
    ∫ x : Sphere n, f (rotate g x) ∂sphereMeasure n = ∫ x : Sphere n, f x ∂sphereMeasure n := by
  let e := Matrix.UnitaryGroup.toLinearIsometryEquiv
    (⟨g.1, (Matrix.mem_specialOrthogonalGroup_iff.mp g.2).1⟩ :
      Matrix.orthogonalGroup (Fin n) ℝ)
  let φ : Sphere n → Sphere n := Subtype.map e fun x hx => by simpa using hx
  let μ : Measure (EuclideanSpace ℝ (Fin n)) := volume
  have hφ : Continuous φ := e.continuous.subtype_map _
  have hμ : μ.toSphere.map φ = μ.toSphere := by
    rw [show μ.toSphere.map φ = (μ.map e).toSphere from e.map_toSphere μ,
      e.measurePreserving.map_eq]
  have hmap : (sphereMeasure n).map φ = sphereMeasure n := by
    rw [sphereMeasure_def, Measure.map_smul _ hφ.measurable.aemeasurable, hμ]
  have hrotate : (fun x : Sphere n => f (rotate g x)) =
      (fun x : Sphere n => f x) ∘ φ := by
    funext x
    rw [rotate_eq_linearIsometryEquiv]
    rfl
  rw [hrotate]
  have hchange := integral_map (μ := sphereMeasure n) (f := fun x : Sphere n => f x)
    hφ.measurable.aemeasurable (hf.comp continuous_subtype_val).aestronglyMeasurable
  rw [hmap] at hchange
  exact hchange.symm

/-- **Haar measure pushes forward to the sphere measure.** For `n ≥ 2` and a unit vector `η`,
the image of the Haar probability measure of `SO(n)` under `g ↦ g η` is the normalized sphere
measure. -/
theorem integral_haarProb_rotate {n : ℕ} (hn : 2 ≤ n) {η : EuclideanSpace ℝ (Fin n)}
    (hη : ‖η‖ = 1) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) :
    ∫ g : RotationGroup n, f (rotate g η) ∂TauCeti.haarProb (RotationGroup n) =
      ∫ x : Sphere n, f x ∂sphereMeasure n := by
  let μ := TauCeti.haarProb (RotationGroup n)
  let ν := sphereMeasure n
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [show ν = sphereMeasure n from rfl, sphereMeasure_def, smul_apply, smul_eq_mul]
    refine ENNReal.inv_mul_cancel (Measure.measure_univ_ne_zero.mpr ?_) (measure_ne_top _ _)
    exact Measure.toSphere_ne_zero volume
  let F (g : RotationGroup n) (x : Sphere n) := f (rotate g x)
  have hF : Continuous (Function.uncurry F) :=
    hf.comp (continuous_rotate.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hFint : Integrable (Function.uncurry F) (μ.prod ν) := hF.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hpoint (x : Sphere n) :
      ∫ g, F g x ∂μ = ∫ g, f (rotate g η) ∂μ := by
    have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using x.property
    obtain ⟨k, hk⟩ := exists_rotate_eq hn hη hx
    simp only [F, ← hk, ← rotate_mul]
    exact integral_mul_right_eq_self (fun g => f (rotate g η)) k
  have hmean (g : RotationGroup n) :
      ∫ x, F g x ∂ν = ∫ x : Sphere n, f x ∂ν :=
    integral_rotate_sphereMeasure g f hf
  have hswap := integral_integral_swap hFint
  simp_rw [hmean, hpoint, integral_const, probReal_univ, one_smul] at hswap
  exact hswap.symm

/-- **Polar-angle density** (Vilenkin–Klimyk, Vol. 2, §9.1.9 (6), p. 22). For `n ≥ 2`, a unit
vector `η` and continuous `f`, `∫ f(⟪η, x⟫) dσ(x) = c_n ∫_{-1}^{1} f(t) (1 - t²)^{(n-3)/2} dt`. -/
theorem integral_inner_sphereMeasure {n : ℕ} (hn : 2 ≤ n) {η : EuclideanSpace ℝ (Fin n)}
    (hη : ‖η‖ = 1) (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ x : Sphere n, f ⟪η, (x : EuclideanSpace ℝ (Fin n))⟫_ℝ ∂sphereMeasure n =
      polarConstant n * ∫ t in Ioo (-1 : ℝ) 1, f t * (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2) := by
  let E := EuclideanSpace ℝ (Fin n)
  let a : ℝ := ((n : ℝ) - 1) / 2
  let S := Ioo (-1 : ℝ) 1
  let W (t : ℝ) := (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2)
  let d := S.indicator (fun t => ENNReal.ofReal (W t / ProbabilityTheory.beta (1 / 2) a))
  have ha : 0 < a := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [a]
    linarith
  have hmap := TauCeti.Probability.map_inner_uniformSphereMeasure
    (E := E) (by simpa [E] using hn) η
  rw [TauCeti.Probability.uniformSphereMeasure_def] at hmap
  rw [← sphereMeasure_def] at hmap
  have hshape : a - 1 = ((n : ℝ) - 3) / 2 := by dsimp [a]; ring
  simp only [hη, one_mul, E, finrank_euclideanSpace_fin] at hmap
  rw [TauCeti.Probability.betaMeasure_map_centered_eq_withDensity] at hmap
  have hmap' : (sphereMeasure n).map
      (fun x : Sphere n => ⟪η, (x : E)⟫_ℝ) = volume.withDensity d := by
    simpa only [d, S, W, ← hshape] using hmap
  have hmeas : Measurable (fun x : Sphere n => ⟪η, (x : E)⟫_ℝ) :=
    (continuous_const.inner continuous_subtype_val).measurable
  have hd : Measurable d := by
    apply Measurable.indicator _ measurableSet_Ioo
    dsimp [W]
    fun_prop
  have hfinite : ∀ᵐ t ∂(volume : Measure ℝ), d t < ⊤ :=
    Filter.Eventually.of_forall fun t => by by_cases ht : t ∈ S <;> simp [d, ht]
  have hβ : 0 < ProbabilityTheory.beta (1 / 2) a := by
    unfold ProbabilityTheory.beta
    positivity
  have hnorm : (ProbabilityTheory.beta (1 / 2) a)⁻¹ = polarConstant n := by
    unfold ProbabilityTheory.beta polarConstant
    rw [Real.Gamma_one_half_eq, show 1 / 2 + a = (n : ℝ) / 2 by dsimp [a]; ring, inv_div]
  calc
    _ = ∫ t, f t ∂volume.withDensity d := by
      rw [← hmap']
      exact (integral_map hmeas.aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ t, (S.indicator (fun t => (ProbabilityTheory.beta (1 / 2) a)⁻¹ * (f t * W t))) t := by
      rw [integral_withDensity_eq_integral_toReal_smul hd hfinite]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ S
      · have hbase : 0 ≤ 1 - t ^ 2 := by
          have ht' : -1 < t ∧ t < 1 := ht
          nlinarith [mul_pos (show 0 < t + 1 by linarith [ht'.1])
            (show 0 < 1 - t by linarith [ht'.2])]
        dsimp only [d]
        rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht,
          ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg hbase _) hβ.le), smul_eq_mul]
        ring
      · simp [d, ht]
    _ = _ := by
      rw [integral_indicator measurableSet_Ioo, integral_const_mul, hnorm]

/-- Rotations commute when the ambient dimension is at most two. -/
private theorem mul_comm_rotationGroup {n : ℕ} (hn : n ≤ 2) (g h : RotationGroup n) :
    g * h = h * g := by
  have hsmall : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hsmall with rfl | rfl | rfl
  · apply Subtype.ext
    ext i
    exact Fin.elim0 i
  · have hg := (Matrix.mem_specialOrthogonalGroup_iff.mp g.2).2
    have hh := (Matrix.mem_specialOrthogonalGroup_iff.mp h.2).2
    rw [Matrix.det_fin_one] at hg hh
    apply Subtype.ext
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, hg, hh]
  · obtain ⟨α, hα⟩ := MotionGroups.exists_rotation_eq g
    obtain ⟨β, hβ⟩ := MotionGroups.exists_rotation_eq h
    rw [hα, hβ, ← MotionGroups.rotation_add, ← MotionGroups.rotation_add, add_comm α β]

/-- **`(SO(n), K_η)` is a Gel'fand pair**, for every `n` and every `η` (Wawrzyńczyk §9.5,
p. 337; Dieudonné §7, pp. 22–23). -/
theorem isGelfandPair_rotationGroup (n : ℕ) (η : EuclideanSpace ℝ (Fin n)) :
    Subgroup.IsGelfandPair (rotationStabilizer η) (TauCeti.haarProb (RotationGroup n)) := by
  let K := rotationStabilizer η
  let μ := TauCeti.haarProb (RotationGroup n)
  by_cases hn : 3 ≤ n
  · apply Subgroup.isGelfandPair_of_measurePreserving_anti (K := K) (μ := μ)
      (τ := MeasurableEquiv.inv (RotationGroup n)) (Measure.measurePreserving_inv μ) (by simp)
    intro g
    have hnorm (k : RotationGroup n) : ‖rotate k η‖ = ‖η‖ := by
      rw [rotate_eq_linearIsometryEquiv, LinearIsometryEquiv.norm_map]
    have hinner : ⟪η, rotate g η⟫_ℝ = ⟪η, rotate g⁻¹ η⟫_ℝ := by
      calc
        ⟪η, rotate g η⟫_ℝ = ⟪rotate g⁻¹ η, rotate g⁻¹ (rotate g η)⟫_ℝ :=
          (inner_rotate_rotate g⁻¹ _ _).symm
        _ = _ := by rw [rotate_inv_rotate, real_inner_comm]
    obtain ⟨k, hk, heq⟩ := exists_stabilizer_rotate_eq hn η (rotate g η) (rotate g⁻¹ η)
      ((hnorm g).trans (hnorm g⁻¹).symm) hinner
    refine ⟨k, hk, (k * g)⁻¹ * g⁻¹, mem_rotationStabilizer.mpr ?_, ?_⟩
    · have heq' : rotate (k * g) η = rotate g⁻¹ η := by rwa [rotate_mul]
      rw [rotate_mul, ← heq', rotate_inv_rotate]
    · change k * g * ((k * g)⁻¹ * g⁻¹) = g⁻¹
      group
  · apply Subgroup.isGelfandPair_of_measurePreserving_anti (K := K) (μ := μ)
      (τ := MeasurableEquiv.refl (RotationGroup n)) (MeasurePreserving.id μ)
    · exact fun g h => mul_comm_rotationGroup (by omega) g h
    · exact fun g => ⟨1, K.one_mem, 1, K.one_mem, by simp⟩

end SFVK.Spheres
