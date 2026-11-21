/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU11.Basic.CircleModel
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The circle model of the principal series of `SU(1,1)`: `L²` theory

The pushforward of the circle measure under the action has the Poisson density, the pointwise
formula is realized by a strongly continuous representation on `L²`, the representation is
unitary exactly on the line `Re τ = -1/2`, and the Fourier modes are weight vectors
(Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 1, §6.4.1 (1)–(5),
pp. 298–299). The density calculation uses Mathlib's complex mean-value and Poisson integral
formulas on the dense span of the circle's Fourier characters.
-/

public section

open AddCircle MeasureTheory
open scoped ComplexConjugate InnerProductSpace Real Topology

namespace SFVK.SU11

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- Integrating in angular coordinates is the normalized circle average. -/
private theorem circleAverage_eq_integral_haar (f : ℂ → ℂ) :
    Real.circleAverage f 0 1 = ∫ θ, f (fourier 1 θ) ∂(haarAddCircle (T := 2 * π)) := by
  rw [Real.circleAverage_def, integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * π) 0 (fun θ => f (fourier 1 θ)), zero_add]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only
  rw [fourier_coe_two_pi]
  simp [circleMap]

/-- The `SU(1,1)` norm identity gives a strict bound for the off-diagonal entry. -/
private theorem norm_entryB_lt_entryA (g : SU11) : ‖entryB g‖ < ‖entryA g‖ := by
  have h := normSq_entryA_sub_normSq_entryB g
  simp only [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (entryA g), norm_nonneg (entryB g)]

/-- The fractional linear denominator is nonzero throughout the closed disk. -/
private theorem circleDenominator_ne_zero_of_norm_le (g : SU11) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    circleDenominator g z ≠ 0 := by
  intro h
  have he : entryB g * z = -conj (entryA g) :=
    eq_neg_of_add_eq_zero_left (circleDenominator_def g z ▸ h)
  have hnorm := congrArg norm he
  rw [norm_mul, norm_neg, Complex.norm_conj] at hnorm
  have hle := mul_le_mul_of_nonneg_left hz (norm_nonneg (entryB g))
  rw [mul_one, hnorm] at hle
  exact (not_le.mpr (norm_entryB_lt_entryA g)) hle

/-- The fractional linear formula extends holomorphically to the closed disk. -/
private theorem diffContOnCl_circleMobius (g : SU11) :
    DiffContOnCl ℂ (circleMobius g) (Metric.ball 0 1) := by
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball (0 : ℂ) one_ne_zero]
  unfold circleMobius circleNumerator circleDenominator
  apply DifferentiableOn.div (by fun_prop) (by fun_prop)
  intro z hz
  exact circleDenominator_ne_zero_of_norm_le g (by simpa [Metric.mem_closedBall, dist_zero_right]
    using hz)

/-- The density is the Poisson kernel at the image of the center of the disk. -/
private theorem poissonKernel_circleMobius_zero (g : SU11) {z : ℂ} (hz : ‖z‖ = 1) :
    poissonKernel 0 (circleMobius g 0) z = (‖entryA g - entryB g * z‖ ^ 2)⁻¹ := by
  let a := entryA g
  let b := entryB g
  have ha : a ≠ 0 := norm_ne_zero_iff.mp ((norm_nonneg b).trans_lt (norm_entryB_lt_entryA g)).ne'
  have ha' : conj a ≠ 0 := by simpa using ha
  have hcenter : circleMobius g 0 = conj b / conj a := by
    simp [circleMobius_def, circleNumerator_def, circleDenominator_def, a, b]
  have hunit : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hnorm : ‖z * conj a - conj b‖ = ‖a - b * z‖ := by
    calc
      _ = ‖z * conj (a - b * z)‖ := by
        congr 1
        simp only [map_sub, map_mul]
        linear_combination (conj b) * hunit
      _ = _ := by rw [norm_mul, hz, one_mul, Complex.norm_conj]
  have hdet : ‖a‖ ^ 2 - ‖b‖ ^ 2 = 1 := by
    simpa only [a, b, Complex.normSq_eq_norm_sq] using normSq_entryA_sub_normSq_entryB g
  have hdiff : z - conj b / conj a = (z * conj a - conj b) / conj a := by
    field_simp
  rw [poissonKernel_def, sub_zero, sub_zero, hcenter, hz, hdiff, norm_div, norm_div,
    Complex.norm_conj, Complex.norm_conj, hnorm, div_pow, div_pow, one_pow]
  have haNorm : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  rw [← div_self haNorm, ← sub_div, hdet, div_div_div_cancel_right₀ haNorm, one_div]

/-- The first Fourier character generates the nonnegative Fourier modes by taking powers. -/
private theorem fourier_natCast (n : ℕ) (θ : 𝕋) :
    fourier (n : ℤ) θ = fourier 1 θ ^ n := by
  rw [fourier_apply, fourier_one, natCast_zsmul, toCircle_nsmul, Circle.coe_pow]

/-- The two candidate measures have the same nonnegative Fourier moments by the mean-value and
Poisson integral formulas. -/
private theorem integral_fourier_natCast_circleAct (g : SU11) (n : ℕ) :
    (∫ θ, fourier (n : ℤ) (circleAct g θ) ∂(haarAddCircle (T := 2 * π))) =
      ∫ θ, (‖entryA g - entryB g * fourier 1 θ‖ ^ 2)⁻¹ • fourier (n : ℤ) θ
        ∂(haarAddCircle (T := 2 * π)) := by
  have hdiff := diffContOnCl_circleMobius g
  have hleft : DiffContOnCl ℂ (fun z => circleMobius g z ^ n) (Metric.ball 0 1) :=
    ⟨hdiff.1.pow n, hdiff.2.pow n⟩
  have hr : |(1 : ℝ)| = 1 := abs_one
  have hmean := (hr.symm ▸ hleft :
    DiffContOnCl ℂ (fun z => circleMobius g z ^ n) (Metric.ball 0 |(1 : ℝ)|)).circleAverage
  have hw : circleMobius g 0 ∈ Metric.ball (0 : ℂ) 1 := by
    simp only [Metric.mem_ball, dist_zero_right, circleMobius_def, circleNumerator_def,
      circleDenominator_def, mul_zero, zero_add, norm_div, Complex.norm_conj]
    exact (div_lt_one ((norm_nonneg _).trans_lt (norm_entryB_lt_entryA g))).2
      (norm_entryB_lt_entryA g)
  have hpow : DiffContOnCl ℂ (fun z : ℂ => z ^ n) (Metric.ball 0 1) :=
    (differentiable_id.pow n).differentiableOn.diffContOnCl
  have hpoisson := hpow.circleAverage_poissonKernel_smul hw
  rw [circleAverage_eq_integral_haar] at hmean hpoisson
  simp only [fourier_natCast, fourier_circleAct]
  calc
    _ = circleMobius g 0 ^ n := hmean
    _ = ∫ θ, (poissonKernel 0 (circleMobius g 0) • (fun z : ℂ => z ^ n)) (fourier 1 θ)
          ∂(haarAddCircle (T := 2 * π)) := hpoisson.symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun θ => by
        simp only [Pi.smul_apply', poissonKernel_circleMobius_zero g (norm_fourier_one θ)]

/-- Integration on continuous functions is a continuous linear functional for a finite measure. -/
private noncomputable def circleIntegralFunctional (μ : Measure 𝕋) [IsFiniteMeasure μ] :
    C(𝕋, ℂ) →L[ℂ] ℂ := (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)

/-- The bounded functional on circle `L²` evaluates to integration against its kernel. -/
private theorem circleIntegralFunctional_apply (μ : Measure 𝕋) [IsFiniteMeasure μ] (f : C(𝕋, ℂ)) :
    circleIntegralFunctional μ f = ∫ θ, f θ ∂μ := by
  rw [circleIntegralFunctional, ContinuousLinearMap.comp_apply, ← L1.integral_eq',
    L1.integral_eq_integral]
  exact integral_congr_ae (ContinuousMap.coeFn_toLp μ f)

/-- The pushforward of circle Haar probability by the right action has the Poisson density. -/
theorem map_circleAct_haar (g : SU11) :
    Measure.map (circleAct g) (haarAddCircle (T := 2 * π)) =
      (haarAddCircle (T := 2 * π)).withDensity
        (fun θ => ENNReal.ofReal (‖entryA g - entryB g * fourier 1 θ‖ ^ 2)⁻¹) := by
  let μ : Measure 𝕋 := haarAddCircle
  let ρ : 𝕋 → ℝ := fun θ => (‖entryA g - entryB g * fourier 1 θ‖ ^ 2)⁻¹
  let ν := μ.withDensity (fun θ => ENNReal.ofReal (ρ θ))
  have hρ_nonneg (θ : 𝕋) : 0 ≤ ρ θ := by dsimp [ρ]; positivity
  have hρ : Continuous ρ := by
    dsimp [ρ]
    apply Continuous.inv₀ (by fun_prop)
    intro θ
    apply pow_ne_zero _ (norm_ne_zero_iff.mpr ?_)
    intro h
    have he : ‖entryA g‖ = ‖entryB g * fourier 1 θ‖ := congrArg norm (sub_eq_zero.mp h)
    rw [norm_mul, norm_fourier_one, mul_one] at he
    exact (ne_of_lt (norm_entryB_lt_entryA g)) he.symm
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity (by
    rw [← ofReal_integral_eq_lintegral_ofReal (hρ.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (Filter.Eventually.of_forall hρ_nonneg)]
    exact ENNReal.ofReal_ne_top)
  have hAct : Measurable (circleAct g) :=
    (continuous_circleAct.comp (continuous_const.prodMk continuous_id)).measurable
  let μ' := Measure.map (circleAct g) μ
  have : IsFiniteMeasure μ' := Measure.isFiniteMeasure_map μ (circleAct g)
  have hnat (n : ℕ) : (∫ θ, fourier (n : ℤ) θ ∂μ') = ∫ θ, fourier (n : ℤ) θ ∂ν := by
    dsimp only [μ', ν]
    rw [integral_map hAct.aemeasurable (fourier (n : ℤ)).continuous.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul
        (f := fun θ => ENNReal.ofReal (ρ θ))
        (ENNReal.measurable_ofReal.comp hρ.measurable)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (fourier (n : ℤ))]
    simp_rw [ENNReal.toReal_ofReal (hρ_nonneg _)]
    exact integral_fourier_natCast_circleAct g n
  have hint : circleIntegralFunctional μ' = circleIntegralFunctional ν := by
    apply ContinuousLinearMap.ext_on (s := Set.range (@fourier (2 * π)))
      (by rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
        span_fourier_closure_eq_top]; rfl)
    rintro _ ⟨n, rfl⟩
    simp only [circleIntegralFunctional_apply]
    cases n with
    | ofNat n => exact hnat n
    | negSucc n =>
      have he : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
      simp only [he, fourier_neg, integral_conj, hnat]
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let F : C(𝕋, ℂ) := ⟨fun θ => (f θ : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hF := congrArg (fun L : C(𝕋, ℂ) →L[ℂ] ℂ => (L F).re) hint
  simp only [circleIntegralFunctional_apply, F, ContinuousMap.coe_mk,
    integral_complex_ofReal, Complex.ofReal_re] at hF
  exact hF

/-- The inverse conjugates the diagonal entry. -/
private theorem entryA_inv (g : SU11) : entryA g⁻¹ = conj (entryA g) := by
  rw [entryA, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, coe_eq_matrix,
    Matrix.adjugate_fin_two]
  rfl

/-- The inverse negates the upper off-diagonal entry. -/
private theorem entryB_inv (g : SU11) : entryB g⁻¹ = -entryB g := by
  rw [entryB, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, coe_eq_matrix,
    Matrix.adjugate_fin_two]
  rfl

/-- The Jacobian of the angular map in terms of its complex denominator. -/
private noncomputable def circleJacobian (g : SU11) (θ : 𝕋) : ℝ :=
  (‖circleDenominator g (fourier 1 θ)‖ ^ 2)⁻¹

/-- The pushforward density uses the denominator of the inverse matrix. -/
private theorem map_circleAct_haar_withDensity (g : SU11) :
    Measure.map (circleAct g) (haarAddCircle (T := 2 * π)) =
      (haarAddCircle (T := 2 * π)).withDensity (ENNReal.ofReal ∘ circleJacobian g⁻¹) := by
  simp only [map_circleAct_haar, Function.comp_def, circleJacobian, circleDenominator_def,
    entryA_inv, entryB_inv, Complex.conj_conj, neg_mul, neg_add_eq_sub]

/-- The inverse circle map undoes the forward map. -/
private theorem circleAct_inv_apply (g : SU11) (θ : 𝕋) :
    circleAct g⁻¹ (circleAct g θ) = θ := by
  rw [← circleAct_mul, mul_inv_cancel, circleAct_one]

/-- The angular maps are measurable equivalences with the inverse-matrix action as inverse. -/
private noncomputable def circleActMeasurableEquiv (g : SU11) : 𝕋 ≃ᵐ 𝕋 where
  toFun := circleAct g
  invFun := circleAct g⁻¹
  left_inv := circleAct_inv_apply g
  right_inv θ := by simpa only [inv_inv] using circleAct_inv_apply g⁻¹ θ
  measurable_toFun := (continuous_circleAct.comp (continuous_const.prodMk continuous_id)).measurable
  measurable_invFun :=
    (continuous_circleAct.comp (continuous_const.prodMk continuous_id)).measurable

/-- The right circle action preserves Haar-null sets under pullback. -/
theorem quasiMeasurePreserving_circleAct (g : SU11) :
    QuasiMeasurePreserving (circleAct g) (haarAddCircle (T := 2 * π)) haarAddCircle := by
  refine ⟨(circleActMeasurableEquiv g).measurable.aemeasurable, ?_⟩
  rw [map_circleAct_haar_withDensity]
  exact withDensity_absolutelyContinuous _ _

/-- The Jacobian is strictly positive on the circle. -/
private theorem circleJacobian_pos (g : SU11) (θ : 𝕋) : 0 < circleJacobian g θ :=
  inv_pos.mpr (pow_pos (norm_pos_iff.mpr (circleDenominator_ne_zero g (norm_fourier_one θ))) _)

/-- The Jacobian depends continuously on the element and the angle. -/
private theorem continuous_circleJacobian : Continuous fun p : SU11 × 𝕋 =>
    circleJacobian p.1 p.2 := by
  unfold circleJacobian
  apply Continuous.inv₀ (continuous_circleDenominator.norm.pow 2)
  intro p
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr (circleDenominator_ne_zero p.1 (norm_fourier_one p.2)))

/-- The squared norm of a circle L² function is its integrated pointwise square. -/
private theorem norm_sq_eq_integral (f : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    ‖f‖ ^ 2 = ∫ θ, ‖f θ‖ ^ 2 ∂(haarAddCircle (T := 2 * π)) := by
  have hf : ⟪f, f⟫_ℂ = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact inner_self_eq_norm_sq_to_K f
  have hfs (θ : 𝕋) : ⟪f θ, f θ⟫_ℂ = ((‖f θ‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact inner_self_eq_norm_sq_to_K (f θ)
  rw [L2.inner_def] at hf
  simp_rw [hfs, integral_complex_ofReal] at hf
  exact_mod_cast hf.symm

/-- The density times the squared multiplier, both in the output variable. -/
private noncomputable def circleSquaredWeight (τ : ℂ) (e : Fin 2) (g : SU11) (θ : 𝕋) : ℝ :=
  circleJacobian g⁻¹ θ * ‖principalMultiplier τ e g (circleAct g⁻¹ θ)‖ ^ 2

/-- The weight controlling the square norm is nonnegative. -/
private theorem circleSquaredWeight_nonneg (τ : ℂ) (e : Fin 2) (g : SU11) (θ : 𝕋) :
    0 ≤ circleSquaredWeight τ e g θ :=
  mul_nonneg (circleJacobian_pos g⁻¹ θ).le (sq_nonneg _)

/-- The weight controlling the square norm is jointly continuous. -/
private theorem continuous_circleSquaredWeight (τ : ℂ) (e : Fin 2) :
    Continuous fun p : SU11 × 𝕋 => circleSquaredWeight τ e p.1 p.2 := by
  unfold circleSquaredWeight
  exact (continuous_circleJacobian.comp (continuous_fst.inv.prodMk continuous_snd)).mul
    (((continuous_principalMultiplier τ e).comp
      (continuous_fst.prodMk
        (continuous_circleAct.comp (continuous_fst.inv.prodMk continuous_snd)))).norm.pow _)

/-- The squared weight at each matrix as a continuous function on the circle. -/
private noncomputable def circleSquaredWeightMap (τ : ℂ) (e : Fin 2) (g : SU11) : C(𝕋, ℝ) :=
  (⟨_, continuous_circleSquaredWeight τ e⟩ : C(SU11 × 𝕋, ℝ)).curry g

/-- The squared weight times an L² pointwise square is integrable. -/
private theorem integrable_circleSquaredWeight_norm_sq (τ : ℂ) (e : Fin 2) (g : SU11)
    (f : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    Integrable (fun θ => circleSquaredWeight τ e g θ * ‖f θ‖ ^ 2) haarAddCircle := by
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  exact hf.bdd_mul (c := ‖circleSquaredWeightMap τ e g‖)
    (circleSquaredWeightMap τ e g).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (circleSquaredWeightMap τ e g).norm_coe_le_norm)

/-- Each pointwise principal action on an L² function gives another L² function. -/
private theorem memLp_principalAction (τ : ℂ) (e : Fin 2) (g : SU11)
    (f : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    MemLp (principalAction τ e g f) 2 haarAddCircle := by
  have hfac : AEStronglyMeasurable (principalMultiplier τ e g) haarAddCircle :=
    ((continuous_principalMultiplier τ e).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  unfold principalAction
  have hmeas : AEStronglyMeasurable
      (fun θ => principalMultiplier τ e g θ * f (circleAct g θ)) haarAddCircle :=
    hfac.mul ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_circleAct g))
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  have h := integrable_circleSquaredWeight_norm_sq τ e g f
  have hρ : Measurable (ENNReal.ofReal ∘ circleJacobian g⁻¹) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_circleJacobian.comp (continuous_const.prodMk continuous_id)).measurable)
  let F : 𝕋 → ℝ := fun θ => ‖principalMultiplier τ e g (circleAct g⁻¹ θ) * f θ‖ ^ 2
  have hF : Integrable F (Measure.map (circleAct g) (haarAddCircle (T := 2 * π))) := by
    rw [map_circleAct_haar_withDensity,
      integrable_withDensity_iff_integrable_smul' hρ
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    suffices (fun θ : 𝕋 => ((ENNReal.ofReal ∘ circleJacobian g⁻¹) θ).toReal • F θ) =
        (fun θ : 𝕋 => circleSquaredWeight τ e g θ * ‖f θ‖ ^ 2) by
      rw [this]
      exact h
    funext θ
    rw [Function.comp_apply, ENNReal.toReal_ofReal (circleJacobian_pos g⁻¹ θ).le]
    simp only [circleSquaredWeight, F, smul_eq_mul, norm_mul, mul_pow, mul_assoc]
  have hcomp := (circleActMeasurableEquiv g).measurableEmbedding.integrable_map_iff.mp hF
  have happly (θ : 𝕋) : circleActMeasurableEquiv g θ = circleAct g θ := rfl
  simpa only [Function.comp_def, F, happly, circleAct_inv_apply] using hcomp

/-- The L² norm after applying the principal action is a weighted square integral. -/
private theorem norm_toLp_principalAction (τ : ℂ) (e : Fin 2) (g : SU11)
    (f : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    ‖(memLp_principalAction τ e g f).toLp (principalAction τ e g f)‖ ^ 2 =
      ∫ θ, circleSquaredWeight τ e g θ * ‖f θ‖ ^ 2 ∂(haarAddCircle (T := 2 * π)) := by
  rw [norm_sq_eq_integral]
  calc
    _ = ∫ θ, ‖principalAction τ e g f θ‖ ^ 2 ∂(haarAddCircle (T := 2 * π)) := by
      apply integral_congr_ae
      filter_upwards [(memLp_principalAction τ e g f).coeFn_toLp] with θ hθ
      rw [hθ]
    _ = ∫ θ, ‖principalMultiplier τ e g (circleAct g⁻¹ θ) * f θ‖ ^ 2
          ∂(Measure.map (circleAct g) haarAddCircle) := by
      have he := (circleActMeasurableEquiv g).measurableEmbedding.integral_map
        (μ := haarAddCircle (T := 2 * π))
        (g := fun θ => ‖principalMultiplier τ e g (circleAct g⁻¹ θ) * f θ‖ ^ 2)
      refine Eq.trans ?_ he.symm
      have happly (θ : 𝕋) : circleActMeasurableEquiv g θ = circleAct g θ := rfl
      simp only [happly, circleAct_inv_apply, principalAction_def]
    _ = _ := by
      rw [map_circleAct_haar_withDensity,
        integral_withDensity_eq_integral_toReal_smul
          (f := ENNReal.ofReal ∘ circleJacobian g⁻¹)
          (ENNReal.measurable_ofReal.comp
            ((continuous_circleJacobian.comp (continuous_const.prodMk continuous_id)).measurable))
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
          (fun θ => ‖principalMultiplier τ e g (circleAct g⁻¹ θ) * f θ‖ ^ 2)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun θ => by
        simp only [Function.comp_apply, ENNReal.toReal_ofReal (circleJacobian_pos g⁻¹ θ).le,
          smul_eq_mul, norm_mul, mul_pow, circleSquaredWeight, mul_assoc]

/-- The supremum of the squared weight bounds the operator norm. -/
private theorem norm_toLp_principalAction_le (τ : ℂ) (e : Fin 2) (g : SU11)
    (f : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    ‖(memLp_principalAction τ e g f).toLp (principalAction τ e g f)‖ ≤
      Real.sqrt ‖circleSquaredWeightMap τ e g‖ * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [norm_toLp_principalAction, mul_pow, Real.sq_sqrt (norm_nonneg _), norm_sq_eq_integral,
    ← integral_const_mul]
  refine integral_mono_ae (integrable_circleSquaredWeight_norm_sq τ e g f) ?_ ?_
  · exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp
      (Lp.memLp f)).const_mul _
  · exact Filter.Eventually.of_forall fun θ =>
      mul_le_mul_of_nonneg_right
        ((le_abs_self _).trans ((circleSquaredWeightMap τ e g).norm_coe_le_norm θ)) (sq_nonneg _)

/-- The pointwise formula is realized by a representation on `L²` with continuous orbit maps. -/
theorem exists_principalSeries (τ : ℂ) (e : Fin 2) :
    ∃ U, IsPrincipalSeriesRealization τ e U := by
  let μ : Measure 𝕋 := haarAddCircle
  have heq (g : SU11) (f : 𝕋 → ℂ) :
      MulAction.multiplierAction (principalMultiplier τ e) g f = principalAction τ e g f := by
    funext θ
    simp only [MulAction.multiplierAction_def, circleMulAction_smul, inv_inv, principalAction_def]
  have hMem (g : SU11) (f : Lp ℂ 2 μ) :
      MemLp (MulAction.multiplierAction (principalMultiplier τ e) g f) 2 μ := by
    rw [heq]
    exact memLp_principalAction τ e g f
  let C : SU11 → ℝ := fun g => Real.sqrt ‖circleSquaredWeightMap τ e g‖
  have hbound (g : SU11) (f : Lp ℂ 2 μ) :
      ‖(hMem g f).toLp (MulAction.multiplierAction (principalMultiplier τ e) g f)‖ ≤
        C g * ‖f‖ := by
    simpa only [heq] using norm_toLp_principalAction_le τ e g f
  obtain ⟨U, hU⟩ := MulAction.exists_multiplierRepresentation
    (isMultiplierCocycle_principalMultiplier τ e)
    (fun g => by simpa only [circleMulAction_smul] using quasiMeasurePreserving_circleAct g⁻¹)
    hMem (fun g => ⟨C g, hbound g⟩)
  have hApply (g : SU11) (f : Lp ℂ 2 μ) :
      (U g f : 𝕋 → ℂ) =ᵐ[μ] principalAction τ e g f := by
    simpa only [heq] using hU g f
  refine ⟨U, hApply, ?_⟩
  have hOp (g : SU11) (f : Lp ℂ 2 μ) : ‖U g f‖ ≤ C g * ‖f‖ := by
    have hEq : U g f =
        (memLp_principalAction τ e g f).toLp (principalAction τ e g f) :=
      Lp.ext ((hApply g f).trans (memLp_principalAction τ e g f).coeFn_toLp.symm)
    rw [hEq]
    exact norm_toLp_principalAction_le τ e g f
  have hC : Continuous C := Real.continuous_sqrt.comp
    (⟨_, continuous_circleSquaredWeight τ e⟩ : C(SU11 × 𝕋, ℝ)).curry.continuous.norm
  let L : C(𝕋, ℂ) →L[ℂ] Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ
  have horbit (f : C(𝕋, ℂ)) : Continuous fun g => U g (L f) := by
    let F : C(SU11 × 𝕋, ℂ) :=
      ⟨fun p => principalAction τ e p.1 f p.2, by
        simp only [principalAction_def]
        exact (continuous_principalMultiplier τ e).mul (f.continuous.comp continuous_circleAct)⟩
    have hF (g : SU11) : U g (L f) = L (F.curry g) := by
      apply Lp.ext
      have hf := (quasiMeasurePreserving_circleAct g).ae_eq_comp
        (ContinuousMap.coeFn_toLp μ f (p := 2) (𝕜 := ℂ))
      filter_upwards [hApply g (L f), ContinuousMap.coeFn_toLp μ (F.curry g) (p := 2) (𝕜 := ℂ),
        hf] with θ hu hr hfθ
      dsimp only [Function.comp_apply] at hfθ
      rw [hu, hr, principalAction_def, hfθ]
      rfl
    simp_rw [hF]
    exact L.continuous.comp F.curry.continuous
  have hdense : DenseRange L := ContinuousMap.toLp_denseRange (μ := μ) (p := 2) ℂ ℂ (by simp)
  intro f
  rw [continuous_iff_continuousAt]
  intro g
  rw [Metric.continuousAt_iff']
  intro ε hε
  let B := C g + 1
  have hB : 0 < B := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) zero_lt_one
  have hBg : C g < B := lt_add_one _
  have hBnear : ∀ᶠ a in 𝓝 g, C a < B := hC.continuousAt.eventually_lt continuousAt_const hBg
  obtain ⟨k, hk⟩ := (Metric.mem_closure_range_iff.mp (hdense f))
    (ε / (3 * B)) (div_pos hε (by positivity))
  have hsmall (a : SU11) (ha : C a < B) :
      dist (U a f) (U a (L k)) < ε / 3 := by
    rw [dist_eq_norm] at hk
    calc
      dist (U a f) (U a (L k)) = ‖U a (f - L k)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ C a * ‖f - L k‖ := hOp a _
      _ ≤ B * ‖f - L k‖ := mul_le_mul_of_nonneg_right ha.le (norm_nonneg _)
      _ < ε / 3 := by
        rw [lt_div_iff₀ (by positivity : 0 < 3 * B)] at hk
        linarith
  have hmid : ∀ᶠ a in 𝓝 g, dist (U a (L k)) (U g (L k)) < ε / 3 :=
    Metric.continuousAt_iff'.mp (horbit k).continuousAt (ε / 3) (by positivity)
  filter_upwards [hBnear, hmid] with a ha hdist
  have hlast := hsmall g hBg
  rw [dist_comm] at hlast
  exact (dist_triangle4 (U a f) (U a (L k)) (U g (L k)) (U g f)).trans_lt (by
    linarith [hsmall a ha, hdist, hlast])

/-- The `L²` action agrees almost everywhere with the pointwise formula. -/
theorem principalSeries_ae_eq (τ : ℂ) (e : Fin 2) (g : SU11)
    (f : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    (principalSeries τ e g f : 𝕋 → ℂ) =ᵐ[haarAddCircle] principalAction τ e g f :=
  (isPrincipalSeriesRealization_principalSeries (exists_principalSeries τ e)).1 g f

/-- Every orbit map of the principal series on `L²` is continuous. -/
theorem continuous_principalSeries_apply (τ : ℂ) (e : Fin 2)
    (f : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    Continuous fun g => principalSeries τ e g f :=
  (isPrincipalSeriesRealization_principalSeries (exists_principalSeries τ e)).2 f

/-- The phase of the fractional linear denominator has unit norm. -/
private theorem norm_circleDenominator_phase (g : SU11) (θ : 𝕋) :
    ‖circleDenominator g (fourier 1 θ) / (‖circleDenominator g (fourier 1 θ)‖ : ℂ)‖ = 1 := by
  have hn := norm_pos_iff.mpr (circleDenominator_ne_zero g (norm_fourier_one θ))
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hn.le, div_self hn.ne']

/-- The magnitude of the multiplier depends only on the real part of the parameter. -/
private theorem norm_sq_principalMultiplier (τ : ℂ) (e : Fin 2) (g : SU11) (θ : 𝕋) :
    ‖principalMultiplier τ e g θ‖ ^ 2 =
      ‖circleDenominator g (fourier 1 θ)‖ ^ (4 * τ.re) := by
  have hn := norm_pos_iff.mpr (circleDenominator_ne_zero g (norm_fourier_one θ))
  simp only [principalMultiplier_def, norm_mul, norm_pow, norm_circleDenominator_phase, one_pow,
    mul_one, Complex.norm_cpow_eq_rpow_re_of_pos hn]
  rw [← Real.rpow_mul_natCast hn.le]
  congr 1
  norm_num [Complex.mul_re]
  ring

/-- The multiplier condition for unitarity is exactly equality of the real exponents. -/
private theorem principalMultiplier_density_iff (τ : ℂ) (e : Fin 2) :
    (∀ g, ∀ᵐ θ ∂(haarAddCircle (T := 2 * π)),
      ‖principalMultiplier τ e g θ‖ₑ ^ 2 = ENNReal.ofReal (circleJacobian g θ)) ↔
      τ.re = -1 / 2 := by
  have hreal (g : SU11) (θ : 𝕋) :
      (‖principalMultiplier τ e g θ‖ₑ ^ 2 = ENNReal.ofReal (circleJacobian g θ)) ↔
        ‖principalMultiplier τ e g θ‖ ^ 2 = circleJacobian g θ := by
    rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.pow_ne_top eNorm_ne_top) ENNReal.ofReal_ne_top,
      ENNReal.toReal_pow, toReal_eNorm, ENNReal.toReal_ofReal (circleJacobian_pos g θ).le]
  have hj (g : SU11) (θ : 𝕋) :
      circleJacobian g θ = ‖circleDenominator g (fourier 1 θ)‖ ^ (-(2 : ℝ)) := by
    rw [circleJacobian, Real.rpow_neg (norm_nonneg _)]
    norm_num [Real.rpow_ofNat]
  constructor
  · intro h
    have hpoint : ∀ g, (fun θ => ‖principalMultiplier τ e g θ‖ ^ 2) = circleJacobian g := by
      intro g
      exact Measure.eq_of_ae_eq ((h g).mono fun θ hθ => (hreal g θ).mp hθ)
        (((continuous_principalMultiplier τ e).comp
          (continuous_const.prodMk continuous_id)).norm.pow 2)
        (continuous_circleJacobian.comp (continuous_const.prodMk continuous_id))
    have hboost := congrFun (hpoint (boost 2)) 0
    rw [norm_sq_principalMultiplier, hj] at hboost
    have hden : ‖circleDenominator (boost 2) (fourier 1 (0 : 𝕋))‖ = Real.exp 1 := by
      rw [circleDenominator_def, fourier_eval_zero, mul_one, entryB_boost, entryA_boost,
        Complex.conj_ofReal, ← Complex.ofReal_add]
      norm_num [Complex.norm_exp, Complex.one_re]
    rw [hden] at hboost
    have hpower := (Real.rpow_right_inj (Real.exp_pos 1)
      (Real.one_lt_exp_iff.mpr zero_lt_one).ne').mp hboost
    linarith
  · intro h g
    refine Filter.Eventually.of_forall fun θ => (hreal g θ).mpr ?_
    rw [norm_sq_principalMultiplier, hj, h]
    congr 1
    norm_num

/-- The principal series is unitary on the circle exactly on the line `Re τ = -1/2`. -/
theorem isUnitary_principalSeries_iff (τ : ℂ) (e : Fin 2) :
    (principalSeries τ e).IsUnitary ↔ τ.re = -1 / 2 := by
  let μ : Measure 𝕋 := haarAddCircle
  have : MeasurableConstSMul SU11 𝕋 :=
    ⟨fun g => by
      have hg : Measurable (circleAct g⁻¹) := (circleActMeasurableEquiv g⁻¹).measurable
      simpa only [circleMulAction_smul] using hg⟩
  have hquasi : μ.IsQuasiInvariantWith (fun (g : SU11) (θ : 𝕋) =>
      ENNReal.ofReal (circleJacobian g θ)) := by
    intro g
    simpa only [circleMulAction_smul, inv_inv, Function.comp_def]
      using map_circleAct_haar_withDensity g⁻¹
  have hcriterion := MulAction.exists_isUnitary_multiplierAction_iff
    (ρ := fun (g : SU11) (θ : 𝕋) => ENNReal.ofReal (circleJacobian g θ))
    (isMultiplierCocycle_principalMultiplier τ e)
    (fun g => ((continuous_principalMultiplier τ e).comp
      (continuous_const.prodMk continuous_id)).measurable)
    (fun g => ENNReal.measurable_ofReal.comp
      ((continuous_circleJacobian.comp (continuous_const.prodMk continuous_id)).measurable))
    hquasi
  have hApply (g : SU11) (f : Lp ℂ 2 μ) :
      (principalSeries τ e g f : 𝕋 → ℂ) =ᵐ[μ]
        MulAction.multiplierAction (principalMultiplier τ e) g f := by
    filter_upwards [principalSeries_ae_eq τ e g f] with θ hθ
    simpa only [MulAction.multiplierAction_def, circleMulAction_smul, inv_inv,
      principalAction_def] using hθ
  rw [← principalMultiplier_density_iff τ e]
  convert_to (principalSeries τ e).IsUnitary ↔
    ∀ g, ∀ᵐ θ ∂μ, ‖principalMultiplier τ e g θ‖ₑ ^ 2 = ENNReal.ofReal (circleJacobian g θ)
  rw [← hcriterion]
  constructor
  · exact fun h => ⟨principalSeries τ e, h, hApply⟩
  · rintro ⟨U, hunitary, hU⟩
    have heq : U = principalSeries τ e := MulAction.multiplierRep_unique hU hApply
    exact heq ▸ hunitary

/-- Along the inverse map, the multiplier is the reciprocal of the inverse multiplier. -/
private theorem principalMultiplier_circleAct_inv (τ : ℂ) (e : Fin 2) (g : SU11) (θ : 𝕋) :
    principalMultiplier τ e g (circleAct g⁻¹ θ) = (principalMultiplier τ e g⁻¹ θ)⁻¹ := by
  have h := principalMultiplier_mul τ e g⁻¹ g θ
  rw [inv_mul_cancel] at h
  have hone : principalMultiplier τ e 1 θ = 1 := by
    simpa only [principalAction_def, mul_one]
      using congrFun (principalAction_one τ e (fun _ => 1)) θ
  rw [hone, eq_comm] at h
  exact eq_inv_of_mul_eq_one_right h

/-- The adjoint parameter combines the reciprocal conjugate multiplier with the Jacobian. -/
private theorem principalMultiplier_adjoint (τ : ℂ) (e : Fin 2) (g : SU11) (θ : 𝕋) :
    (circleJacobian g θ : ℂ) * conj ((principalMultiplier τ e g θ)⁻¹) =
      principalMultiplier (-conj τ - 1) e g θ := by
  let u := circleDenominator g (fourier 1 θ)
  let r : ℂ := (‖u‖ : ℂ)
  let phase := u / r
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (circleDenominator_ne_zero g (norm_fourier_one θ)))
  have harg : Complex.arg r ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg (norm_nonneg u)]
    exact Real.pi_ne_zero.symm
  have hconj : conj (r ^ (2 * τ)) = r ^ (2 * conj τ) := by
    simpa only [map_mul, map_ofNat, Complex.conj_ofReal, r] using
      (Complex.cpow_conj r (2 * τ) harg).symm
  have hphase : phase * conj phase = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_circleDenominator_phase]
    norm_num
  have hexp : 2 * (-conj τ - 1) + 2 * conj τ = -((2 : ℕ) : ℂ) := by
    push_cast
    ring
  have hprod :
      principalMultiplier (-conj τ - 1) e g θ * conj (principalMultiplier τ e g θ) =
        (circleJacobian g θ : ℂ) := by
    calc
      _ = (r ^ (2 * (-conj τ - 1)) * phase ^ (e : ℕ)) *
          (conj (r ^ (2 * τ)) * conj phase ^ (e : ℕ)) := by
        simp only [principalMultiplier_def, map_mul, map_pow, u, r, phase]
      _ = r ^ (2 * (-conj τ - 1) + 2 * conj τ) * (phase * conj phase) ^ (e : ℕ) := by
        rw [hconj, Complex.cpow_add _ _ hr, mul_pow]
        ring
      _ = _ := by
        rw [hexp, Complex.cpow_neg, Complex.cpow_natCast, hphase, one_pow, mul_one]
        simp only [circleJacobian, r, u, Complex.ofReal_inv, Complex.ofReal_pow]
  have hm : principalMultiplier τ e g θ ≠ 0 := by
    rw [principalMultiplier_def]
    exact mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hr))
      (pow_ne_zero _ (div_ne_zero (circleDenominator_ne_zero g (norm_fourier_one θ)) hr))
  rw [← hprod, mul_assoc, ← map_mul, mul_inv_cancel₀ hm, map_one, mul_one]

/-- The Hermitian adjoint has parameter `-conj τ - 1` and the inverse group argument. -/
theorem inner_principalSeries (τ : ℂ) (e : Fin 2) (g : SU11)
    (f h : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    ⟪principalSeries τ e g f, h⟫_ℂ = ⟪f, principalSeries (-conj τ - 1) e g⁻¹ h⟫_ℂ := by
  let μ : Measure 𝕋 := haarAddCircle
  let F : 𝕋 → ℂ := fun θ =>
    ⟪principalMultiplier τ e g (circleAct g⁻¹ θ) * f θ, h (circleAct g⁻¹ θ)⟫_ℂ
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ θ, ⟪principalAction τ e g f θ, h θ⟫_ℂ ∂μ := by
      apply integral_congr_ae
      filter_upwards [principalSeries_ae_eq τ e g f] with θ hθ
      rw [hθ]
    _ = ∫ θ, F θ ∂Measure.map (circleAct g) μ := by
      have he := (circleActMeasurableEquiv g).measurableEmbedding.integral_map (μ := μ) (g := F)
      refine Eq.trans ?_ he.symm
      have happly (θ : 𝕋) : circleActMeasurableEquiv g θ = circleAct g θ := rfl
      simp only [F, happly, circleAct_inv_apply, principalAction_def]
    _ = ∫ θ, ⟪f θ, principalAction (-conj τ - 1) e g⁻¹ h θ⟫_ℂ ∂μ := by
      rw [map_circleAct_haar_withDensity,
        integral_withDensity_eq_integral_toReal_smul
          (f := ENNReal.ofReal ∘ circleJacobian g⁻¹)
          (ENNReal.measurable_ofReal.comp
            ((continuous_circleJacobian.comp (continuous_const.prodMk continuous_id)).measurable))
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun θ => ?_
      simp only [Function.comp_apply, ENNReal.toReal_ofReal (circleJacobian_pos g⁻¹ θ).le, F,
        RCLike.inner_apply', principalAction_def, map_mul, Complex.real_smul,
        principalMultiplier_circleAct_inv]
      rw [← principalMultiplier_adjoint τ e g⁻¹ θ]
      ring
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [principalSeries_ae_eq (-conj τ - 1) e g⁻¹ h] with θ hθ
      rw [hθ]

/-- The first Fourier character determines the point of the circle. -/
private theorem fourier_one_injective : Function.Injective (⇑(@fourier (2 * π) 1)) := by
  intro x y h
  rw [fourier_one, fourier_one] at h
  apply AddCircle.injective_toCircle Real.two_pi_pos.ne'
  exact Subtype.ext h

/-- The diagonal subgroup acts by translations of the angle. -/
private theorem circleAct_rotation (α : ℝ) (θ : 𝕋) :
    circleAct (rotation α) θ = (α : 𝕋) + θ := by
  apply fourier_one_injective
  rw [fourier_circleAct, circleMobius_def, circleNumerator_def, circleDenominator_def,
    entryA_rotation, entryB_rotation, fourier_add_angle, fourier_coe_two_pi]
  simp only [map_zero, add_zero, zero_mul, zero_add, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, mul_neg, div_eq_mul_inv, ← Complex.exp_neg]
  rw [neg_neg, mul_right_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The multiplier on a rotation is its parity phase. -/
private theorem principalMultiplier_rotation (τ : ℂ) (e : Fin 2) (α : ℝ) (θ : 𝕋) :
    principalMultiplier τ e (rotation α) θ =
      Complex.exp (-((e : ℂ) * α / 2) * Complex.I) := by
  rw [principalMultiplier_def, circleDenominator_def, entryA_rotation, entryB_rotation]
  simp only [zero_mul, zero_add]
  rw [Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one,
    Complex.one_cpow, one_mul, div_one, ← Complex.exp_conj, map_mul,
    Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The Fourier mode of index `n` has magnetic weight `n - e/2` under diagonal rotations. -/
theorem principalSeries_rotation (τ : ℂ) (e : Fin 2) (n : ℤ) (α : ℝ) :
    principalSeries τ e (rotation α) (fourierLp (T := 2 * π) 2 n) =
      Complex.exp (((n : ℂ) - (e : ℂ) / 2) * α * Complex.I) • fourierLp (T := 2 * π) 2 n := by
  apply Lp.ext
  have hm : MeasurePreserving (fun θ : 𝕋 => (α : 𝕋) + θ) haarAddCircle haarAddCircle :=
    measurePreserving_add_left haarAddCircle _
  have hfourier := coeFn_fourierLp (T := 2 * π) 2 n
  have hshift := (hm.quasiMeasurePreserving.ae_eq_comp hfourier)
  filter_upwards [principalSeries_ae_eq τ e (rotation α) (fourierLp (T := 2 * π) 2 n),
    Lp.coeFn_smul (Complex.exp (((n : ℂ) - (e : ℂ) / 2) * α * Complex.I))
      (fourierLp (T := 2 * π) 2 n), hfourier, hshift] with θ hleft hright hθ htrans
  rw [hleft, hright, principalAction_def, circleAct_rotation, principalMultiplier_rotation]
  simp only [Function.comp_apply] at htrans
  rw [htrans, Pi.smul_apply, smul_eq_mul, hθ, fourier_add_angle, fourier_coe_two_pi]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

end SFVK.SU11
