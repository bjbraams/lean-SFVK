/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU11.Basic.BoostMatrixElements
import SFVK.SU11.MatrixElementKernels
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Differential relations for `SU(1,1)` boost matrix elements

Differentiating the Fourier integrand and integrating its angular derivative gives the
ladder relations and three-term recurrences of Vilenkin–Klimyk, *Representation of Lie Groups and
Special Functions*, Vol. 1, §6.7.2 (5), (8)–(13), pp. 335–336.
-/

public section

open Complex MeasureTheory Set Filter
open scoped ComplexConjugate Real Topology

namespace SFVK.SU11

open FourierExpansion

namespace MatrixElementDerivative

/-- The integer character evaluated on an angle in radians. -/
private noncomputable def phase (k : ℤ) (θ : ℝ) : ℂ := exp ((k : ℂ) * (θ : ℂ) * I)

/-- The complex cast of the hyperbolic cosine of half a boost parameter. -/
private noncomputable def halfCosh (t : ℝ) : ℂ := Real.cosh (t / 2)
/-- The complex cast of the hyperbolic sine of half a boost parameter. -/
private noncomputable def halfSinh (t : ℝ) : ℂ := Real.sinh (t / 2)

/-- The power base at the positive angular frequency. -/
private noncomputable def positiveBase (t θ : ℝ) : ℂ := boostBase t (phase 1 θ)
/-- The power base at the negative angular frequency. -/
private noncomputable def negativeBase (t θ : ℝ) : ℂ := boostBase t (phase (-1) θ)

/-- The Fourier integrand of the boost coefficient at shift `k`. -/
private noncomputable def integrand (τ : ℂ) (n : ℝ) (k : ℤ) (t θ : ℝ) : ℂ :=
  phase k θ * (positiveBase t θ ^ (τ + n) * negativeBase t θ ^ (τ - n))

/-- The logarithmic derivative of the two power factors divided by `I`. -/
private noncomputable def angularWeight (τ : ℂ) (n t θ : ℝ) : ℂ :=
  (τ + n) * halfSinh t * phase 1 θ / positiveBase t θ -
    (τ - n) * halfSinh t * phase (-1) θ / negativeBase t θ

/-- Adding two frequencies multiplies their characters. -/
private theorem phase_add (j k : ℤ) (θ : ℝ) :
    phase (j + k) θ = phase j θ * phase k θ := by
  rw [phase, phase, phase, ← exp_add, Int.cast_add]
  congr 1
  ring

/-- The character at the opposite frequency is the multiplicative inverse. -/
private theorem phase_mul_phase_neg (j : ℤ) (θ : ℝ) :
    phase j θ * phase (-j) θ = 1 := by
  rw [← phase_add, add_neg_cancel]
  simp [phase]

/-- The integer character takes values on the unit circle. -/
private theorem phase_norm (k : ℤ) (θ : ℝ) : ‖phase k θ‖ = 1 := by
  rw [phase, ← ofReal_intCast, ← ofReal_mul, norm_exp_ofReal_mul_I]

/-- Values of the integer character agree at the two integration endpoints. -/
private theorem phase_period (k : ℤ) : phase k (2 * π) = phase k 0 := by
  have h : (k : ℂ) * ((2 * π : ℝ) : ℂ) * I = (k : ℂ) * (2 * π * I) := by
    push_cast
    ring
  rw [phase, phase, h, exp_int_mul, exp_two_pi_mul_I, one_zpow]
  simp

/-- The positive-frequency power uses the principal branch away from its cut. -/
private theorem positiveBase_mem_slitPlane (t θ : ℝ) : positiveBase t θ ∈ slitPlane :=
  boostBase_mem_slitPlane t (phase_norm 1 θ)

/-- The negative-frequency power uses the principal branch away from its cut. -/
private theorem negativeBase_mem_slitPlane (t θ : ℝ) : negativeBase t θ ∈ slitPlane :=
  boostBase_mem_slitPlane t (phase_norm (-1) θ)

/-- The positive-frequency power base is nonzero. -/
private theorem positiveBase_ne_zero (t θ : ℝ) : positiveBase t θ ≠ 0 :=
  slitPlane_ne_zero (positiveBase_mem_slitPlane t θ)

/-- The negative-frequency power base is nonzero. -/
private theorem negativeBase_ne_zero (t θ : ℝ) : negativeBase t θ ≠ 0 :=
  slitPlane_ne_zero (negativeBase_mem_slitPlane t θ)

/-- The character varies continuously in the angle. -/
private theorem continuous_phase (k : ℤ) : Continuous (phase k) := by unfold phase; fun_prop

/-- Joint continuity of the positive-frequency base. -/
private theorem continuous_positiveBase :
    Continuous (fun p : ℝ × ℝ => positiveBase p.1 p.2) := by
  dsimp only [positiveBase, boostBase]
  exact (by fun_prop : Continuous (fun p : ℝ × ℝ => (↑(Real.cosh (p.1 / 2)) : ℂ))).add
    ((by fun_prop : Continuous (fun p : ℝ × ℝ => (↑(Real.sinh (p.1 / 2)) : ℂ))).mul
      ((continuous_phase 1).comp continuous_snd))

/-- Joint continuity of the negative-frequency base. -/
private theorem continuous_negativeBase :
    Continuous (fun p : ℝ × ℝ => negativeBase p.1 p.2) := by
  dsimp only [negativeBase, boostBase]
  exact (by fun_prop : Continuous (fun p : ℝ × ℝ => (↑(Real.cosh (p.1 / 2)) : ℂ))).add
    ((by fun_prop : Continuous (fun p : ℝ × ℝ => (↑(Real.sinh (p.1 / 2)) : ℂ))).mul
      ((continuous_phase (-1)).comp continuous_snd))

/-- Joint continuity of the Fourier integrand in the boost and angle. -/
private theorem continuous_integrand (τ : ℂ) (n : ℝ) (k : ℤ) :
    Continuous (fun p : ℝ × ℝ => integrand τ n k p.1 p.2) := by
  exact ((continuous_phase k).comp continuous_snd).mul
    ((continuous_positiveBase.cpow continuous_const fun p => positiveBase_mem_slitPlane p.1 p.2).mul
      (continuous_negativeBase.cpow continuous_const fun p => negativeBase_mem_slitPlane p.1 p.2))

/-- Continuity of the angular integrand for a fixed boost. -/
private theorem continuous_integrand_angle (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    Continuous (integrand τ n k t) :=
  (continuous_integrand τ n k).comp (continuous_const.prodMk continuous_id)

/-- Continuity of the logarithmic derivative in the angle. -/
private theorem continuous_angularWeight (τ : ℂ) (n t : ℝ) : Continuous (angularWeight τ n t) := by
  have hp := continuous_positiveBase.comp
    (continuous_const.prodMk continuous_id : Continuous (fun θ : ℝ => (t, θ)))
  have hm := continuous_negativeBase.comp
    (continuous_const.prodMk continuous_id : Continuous (fun θ : ℝ => (t, θ)))
  exact ((continuous_const.mul (continuous_phase 1)).div hp (positiveBase_ne_zero t)).sub
    ((continuous_const.mul (continuous_phase (-1))).div hm (negativeBase_ne_zero t))

/-- The normalized angular integral recovers the boost coefficient. -/
private theorem boostMatrixElement_eq_integrand (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    boostMatrixElement τ (n + k) n t =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, integrand τ n k t θ := by
  rw [boostMatrixElement_def]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [integrand, positiveBase, negativeBase, boostBase, phase, add_sub_cancel_left,
    Int.cast_one, Int.cast_neg, one_mul, neg_mul, ofReal_intCast]
  ring

/-- The chain rule for a complex principal power of a real-parameter curve. -/
private theorem hasDerivAt_cpow_real {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hx : f x ∈ slitPlane) (p : ℂ) :
    HasDerivAt (fun x => f x ^ p) (p * f x ^ p * (f' / f x)) x := by
  have hd := (Complex.hasStrictDerivAt_cpow_const (c := p) hx).hasDerivAt
  have h := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt x hf
  convert h using 1
  · rfl
  · change p * f x ^ p * (f' / f x) = f' * (p * f x ^ (p - 1))
    rw [cpow_sub _ _ (slitPlane_ne_zero hx), cpow_one]
    ring

/-- The derivative of the half-argument hyperbolic cosine. -/
private theorem hasDerivAt_halfCosh (t : ℝ) :
    HasDerivAt halfCosh (halfSinh t / 2) t := by
  have h := (Real.hasDerivAt_cosh (t / 2)).comp t
    ((hasDerivAt_id t).div_const (2 : ℝ))
  convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t h using 1
  · rfl
  · simp only [halfSinh, ofRealCLM_apply, ofReal_mul, ofReal_div, ofReal_one, ofReal_ofNat]
    ring

/-- The derivative of the half-argument hyperbolic sine. -/
private theorem hasDerivAt_halfSinh (t : ℝ) :
    HasDerivAt halfSinh (halfCosh t / 2) t := by
  have h := (Real.hasDerivAt_sinh (t / 2)).comp t
    ((hasDerivAt_id t).div_const (2 : ℝ))
  convert Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t h using 1
  · rfl
  · simp only [halfCosh, ofRealCLM_apply, ofReal_mul, ofReal_div, ofReal_one, ofReal_ofNat]
    ring

/-- The angular derivative of an integer character. -/
private theorem hasDerivAt_phase (k : ℤ) (θ : ℝ) :
    HasDerivAt (phase k) (I * k * phase k θ) θ := by
  have h : HasDerivAt (fun z : ℂ => (k : ℂ) * z * I) ((k : ℂ) * I) θ := by
    simpa only [id_eq, mul_one, one_mul] using
      (((hasDerivAt_id (θ : ℂ)).const_mul (k : ℂ)).mul_const I)
  have hd := ((Complex.hasDerivAt_exp _).comp _ h).comp_ofReal
  convert hd using 1
  · rfl
  · unfold phase
    ring

/-- The multiplicative change from lowering the second index by one. -/
private theorem integrand_lower (τ : ℂ) (n : ℝ) (k : ℤ) (t θ : ℝ) :
    integrand τ (n - 1) (k + 1) t θ =
      integrand τ n k t θ * (phase 1 θ * negativeBase t θ / positiveBase t θ) := by
  rw [integrand, integrand, phase_add, ofReal_sub, ofReal_one,
    ← show τ + (n : ℂ) - 1 = τ + ((n : ℂ) - 1) by ring,
    show τ - ((n : ℂ) - 1) = τ - n + 1 by ring]
  rw [cpow_sub _ _ (positiveBase_ne_zero t θ), cpow_add _ _ (negativeBase_ne_zero t θ), cpow_one,
    cpow_one]
  ring

/-- The multiplicative change from raising the second index by one. -/
private theorem integrand_raise (τ : ℂ) (n : ℝ) (k : ℤ) (t θ : ℝ) :
    integrand τ (n + 1) (k - 1) t θ =
      integrand τ n k t θ * (phase (-1) θ * positiveBase t θ / negativeBase t θ) := by
  rw [integrand, integrand, sub_eq_add_neg k, phase_add, ofReal_add, ofReal_one,
    ← show τ + (n : ℂ) + 1 = τ + ((n : ℂ) + 1) by ring,
    ← show τ - (n : ℂ) - 1 = τ - ((n : ℂ) + 1) by ring]
  rw [cpow_add _ _ (positiveBase_ne_zero t θ), cpow_sub _ _ (negativeBase_ne_zero t θ), cpow_one,
    cpow_one]
  ring

/-- The boost derivative of the integrand shifts the second index. -/
private theorem hasDerivAt_integrand_time (τ : ℂ) (n : ℝ) (k : ℤ) (t θ : ℝ) :
    HasDerivAt (fun t => integrand τ n k t θ)
      (((τ + n) / 2) * integrand τ (n - 1) (k + 1) t θ +
        ((τ - n) / 2) * integrand τ (n + 1) (k - 1) t θ) t := by
  have hplus : HasDerivAt (fun t => positiveBase t θ)
      (phase 1 θ * negativeBase t θ / 2) t := by
    convert (hasDerivAt_halfCosh t).add ((hasDerivAt_halfSinh t).mul_const (phase 1 θ)) using 1
    · rfl
    dsimp only [negativeBase, boostBase, halfCosh, halfSinh]
    have hz : phase 1 θ * phase (-1) θ = 1 := phase_mul_phase_neg 1 θ
    have h : phase 1 θ *
        ((Real.sinh (t / 2) : ℂ) * phase (-1) θ) = (Real.sinh (t / 2) : ℂ) := by
      rw [mul_left_comm, hz, mul_one]
    rw [mul_add, h]
    ring
  have hminus : HasDerivAt (fun t => negativeBase t θ)
      (phase (-1) θ * positiveBase t θ / 2) t := by
    convert (hasDerivAt_halfCosh t).add ((hasDerivAt_halfSinh t).mul_const (phase (-1) θ)) using 1
    · rfl
    dsimp only [positiveBase, boostBase, halfCosh, halfSinh]
    have hz : phase (-1) θ * phase 1 θ = 1 := by rw [mul_comm]; exact phase_mul_phase_neg 1 θ
    have h : phase (-1) θ *
        ((Real.sinh (t / 2) : ℂ) * phase 1 θ) = (Real.sinh (t / 2) : ℂ) := by
      rw [mul_left_comm, hz, mul_one]
    rw [mul_add, h]
    ring
  have hp := hasDerivAt_cpow_real hplus (positiveBase_mem_slitPlane t θ) (τ + n)
  have hm := hasDerivAt_cpow_real hminus (negativeBase_mem_slitPlane t θ) (τ - n)
  convert (hp.mul hm).const_mul (phase k θ) using 1
  · rfl
  · rw [integrand_lower, integrand_raise, integrand]
    ring

/-- The angular derivative of the Fourier integrand. -/
private theorem hasDerivAt_integrand_angle (τ : ℂ) (n : ℝ) (k : ℤ) (t θ : ℝ) :
    HasDerivAt (integrand τ n k t)
      (I * (integrand τ n k t θ * ((k : ℂ) + angularWeight τ n t θ))) θ := by
  have hplus : HasDerivAt (positiveBase t) (I * halfSinh t * phase 1 θ) θ := by
    convert ((hasDerivAt_phase 1 θ).const_mul (halfSinh t)).const_add (halfCosh t) using 1
    · rfl
    · push_cast
      ring
  have hminus : HasDerivAt (negativeBase t) (-(I * halfSinh t * phase (-1) θ)) θ := by
    convert ((hasDerivAt_phase (-1) θ).const_mul (halfSinh t)).const_add (halfCosh t) using 1
    · rfl
    · push_cast
      ring
  have hp := hasDerivAt_cpow_real hplus (positiveBase_mem_slitPlane t θ) (τ + n)
  have hm := hasDerivAt_cpow_real hminus (negativeBase_mem_slitPlane t θ) (τ - n)
  convert (hasDerivAt_phase k θ).mul (hp.mul hm) using 1
  · rfl
  · simp only [integrand, angularWeight, Pi.mul_apply]
    ring

/-- Integration of continuous functions against normalized angle measure. -/
private noncomputable def normalizedIntegral : C(ℝ, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ((2 * π : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f θ
  map_add' f g := by
    change _ * (∫ θ in (0 : ℝ)..2 * π, f θ + g θ) =
      _ * (∫ θ in (0 : ℝ)..2 * π, f θ) + _ * (∫ θ in (0 : ℝ)..2 * π, g θ)
    rw [intervalIntegral.integral_add (f.continuous.intervalIntegrable _ _)
      (g.continuous.intervalIntegrable _ _), mul_add]
  map_smul' r f := by
    simp only [RingHom.id_apply, smul_eq_mul]
    change _ * (∫ θ in (0 : ℝ)..2 * π, r * f θ) = _
    rw [intervalIntegral.integral_const_mul, mul_left_comm]

/-- The Fourier integrand as a continuous function of the angle. -/
private noncomputable def fourierIntegrand (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) : C(ℝ, ℂ) :=
  ⟨integrand τ n k t, continuous_integrand_angle τ n k t⟩

/-- The Fourier integrand multiplied by the angular logarithmic derivative. -/
private noncomputable def weightedIntegrand (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) : C(ℝ, ℂ) :=
  fourierIntegrand τ n k t * ⟨angularWeight τ n t, continuous_angularWeight τ n t⟩

/-- Evaluation of the normalized Fourier integral. -/
private theorem normalizedIntegral_fourierIntegrand (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    normalizedIntegral (fourierIntegrand τ n k t) = boostMatrixElement τ (n + k) n t :=
  (boostMatrixElement_eq_integrand τ n k t).symm

/-- The integral of the angular derivative vanishes by periodicity. -/
private theorem normalizedIntegral_weightedIntegrand (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    normalizedIntegral (weightedIntegrand τ n k t) =
      -(k : ℂ) * boostMatrixElement τ (n + k) n t := by
  let H : C(ℝ, ℂ) := I • ((k : ℂ) • fourierIntegrand τ n k t + weightedIntegrand τ n k t)
  have hderiv (θ : ℝ) : HasDerivAt (integrand τ n k t) (H θ) θ := by
    have he : H θ = I * (integrand τ n k t θ * ((k : ℂ) + angularWeight τ n t θ)) := by
      change I * ((k : ℂ) * integrand τ n k t θ +
          integrand τ n k t θ * angularWeight τ n t θ) = _
      ring
    rw [he]
    exact hasDerivAt_integrand_angle τ n k t θ
  have hperiod : integrand τ n k t (2 * π) = integrand τ n k t 0 := by
    simp only [integrand, positiveBase, negativeBase, phase_period]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ)
    (H.continuous.intervalIntegrable 0 (2 * π))
  rw [hperiod, sub_self] at h
  have hi : normalizedIntegral H = 0 := by
    change _ * (∫ θ in (0 : ℝ)..2 * π, H θ) = _
    rw [h, mul_zero]
  have hh : I * ((k : ℂ) * boostMatrixElement τ (n + k) n t +
      normalizedIntegral (weightedIntegrand τ n k t)) = 0 := by
    simpa only [H, map_smul, map_add, smul_eq_mul, normalizedIntegral_fourierIntegrand] using hi
  have hz := (mul_eq_zero.mp hh).resolve_left I_ne_zero
  linear_combination hz

/-- Differentiation under the circle integral gives the second-index shifts. -/
private theorem hasDerivAt_normalizedIntegral (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    HasDerivAt (fun t => boostMatrixElement τ (n + k) n t)
      (((τ + n) / 2) * boostMatrixElement τ ((n - 1) + (k + 1 : ℤ)) (n - 1) t +
        ((τ - n) / 2) * boostMatrixElement τ ((n + 1) + (k - 1 : ℤ)) (n + 1) t) t := by
  let F := integrand τ n k
  let D : ℝ → ℝ → ℂ := fun t θ =>
    ((τ + n) / 2) * integrand τ (n - 1) (k + 1) t θ +
      ((τ - n) / 2) * integrand τ (n + 1) (k - 1) t θ
  have hcD : Continuous (fun p : ℝ × ℝ => D p.1 p.2) :=
    ((continuous_integrand τ (n - 1) (k + 1)).const_mul _).add
      ((continuous_integrand τ (n + 1) (k - 1)).const_mul _)
  have hcompact : IsCompact (Icc (t - 1) (t + 1) ×ˢ Icc 0 (2 * π)) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcD.continuousOn
  have hnhds : Icc (t - 1) (t + 1) ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  have hFc (x : ℝ) : Continuous (F x) := continuous_integrand_angle τ n k x
  have hDc : Continuous (D t) := hcD.comp (continuous_const.prodMk continuous_id)
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := D) (bound := fun _ => M) hnhds
    (.of_forall fun x => (hFc x).aestronglyMeasurable)
    ((hFc t).intervalIntegrable 0 (2 * π)) hDc.aestronglyMeasurable
    (ae_of_all _ fun θ hθ x hx =>
      hM (x, θ) ⟨hx, Ioc_subset_Icc_self (by simpa only [uIoc_of_le Real.two_pi_pos.le]
        using hθ)⟩) intervalIntegrable_const
    (ae_of_all _ fun θ _ x _ => hasDerivAt_integrand_time τ n k x θ)).2
  let H : C(ℝ, ℂ) := ((τ + n : ℂ) / 2) • fourierIntegrand τ (n - 1) (k + 1) t +
    ((τ - n : ℂ) / 2) • fourierIntegrand τ (n + 1) (k - 1) t
  have hh : normalizedIntegral H =
      ((τ + n) / 2) * boostMatrixElement τ ((n - 1) + (k + 1 : ℤ)) (n - 1) t +
        ((τ - n) / 2) * boostMatrixElement τ ((n + 1) + (k - 1 : ℤ)) (n + 1) t := by
    simp only [H, map_add, map_smul, normalizedIntegral_fourierIntegrand, smul_eq_mul]
  have hd' := hd.const_mul (((2 * π : ℝ) : ℂ)⁻¹)
  rw [← hh]
  convert hd' using 1
  · exact funext fun x => boostMatrixElement_eq_integrand τ n k x
  · rfl

/-- Shifting the Fourier index multiplies the integrand by a character. -/
private theorem fourierIntegrand_add_index (τ : ℂ) (n : ℝ) (k j : ℤ) (t θ : ℝ) :
    fourierIntegrand τ n (k + j) t θ = phase j θ * integrand τ n k t θ := by
  change integrand τ n (k + j) t θ = _
  rw [integrand, integrand, phase_add]
  ring

/-- The weighted integrand transforms by the same character. -/
private theorem weightedIntegrand_add_index (τ : ℂ) (n : ℝ) (k j : ℤ) (t θ : ℝ) :
    weightedIntegrand τ n (k + j) t θ =
      phase j θ * integrand τ n k t θ * angularWeight τ n t θ := by
  change fourierIntegrand τ n (k + j) t θ * angularWeight τ n t θ = _
  rw [fourierIntegrand_add_index]

/-- The hyperbolic identity in the complex half-argument notation. -/
private theorem halfCosh_sq_sub_halfSinh_sq (t : ℝ) : halfCosh t ^ 2 - halfSinh t ^ 2 = 1 := by
  simpa only [halfCosh, halfSinh, ofReal_sub, ofReal_pow, ofReal_one] using
    congrArg Complex.ofReal (Real.cosh_sq_sub_sinh_sq (t / 2))

/-- The double-angle hyperbolic cosine in the complex half-argument notation. -/
private theorem ofReal_cosh_eq_half (t : ℝ) :
    (Real.cosh t : ℂ) = halfCosh t ^ 2 + halfSinh t ^ 2 := by
  have ht : 2 * (t / 2) = t := by ring
  simpa only [halfCosh, halfSinh, ofReal_add, ofReal_pow, ht] using
    congrArg Complex.ofReal (Real.cosh_two_mul (x := t / 2))

/-- The double-angle hyperbolic sine in the complex half-argument notation. -/
private theorem ofReal_sinh_eq_half (t : ℝ) :
    (Real.sinh t : ℂ) = 2 * (halfCosh t * halfSinh t) := by
  have h : Real.sinh t = 2 * (Real.cosh (t / 2) * Real.sinh (t / 2)) := by
    have he := Real.sinh_two_mul (x := t / 2)
    rw [show 2 * (t / 2) = t by ring] at he
    linear_combination he
  simpa only [halfCosh, halfSinh, ofReal_mul, ofReal_ofNat] using congrArg Complex.ofReal h

/-- Expressing the second-index sum through first-index shifts. -/
private theorem add_fourierIntegrand_shift (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    (τ + n : ℂ) • fourierIntegrand τ (n - 1) (k + 1) t +
        (τ - n : ℂ) • fourierIntegrand τ (n + 1) (k - 1) t =
      (τ + n : ℂ) • fourierIntegrand τ n (k + 1) t +
        (τ - n : ℂ) • fourierIntegrand τ n (k - 1) t -
        weightedIntegrand τ n (k + 1) t + weightedIntegrand τ n (k - 1) t := by
  ext θ
  change (τ + n) * integrand τ (n - 1) (k + 1) t θ +
      (τ - n) * integrand τ (n + 1) (k - 1) t θ =
    (τ + n) * fourierIntegrand τ n (k + 1) t θ +
      (τ - n) * fourierIntegrand τ n (k - 1) t θ -
      weightedIntegrand τ n (k + 1) t θ + weightedIntegrand τ n (k - 1) t θ
  rw [integrand_lower, integrand_raise, sub_eq_add_neg k,
    fourierIntegrand_add_index, fourierIntegrand_add_index,
    weightedIntegrand_add_index, weightedIntegrand_add_index, angularWeight]
  field_simp [positiveBase_ne_zero t θ, negativeBase_ne_zero t θ]
  dsimp only [positiveBase, negativeBase, boostBase, halfSinh]
  ring

/-- The algebraic decomposition of the fractions in the shift identities. -/
private theorem mul_shift_fraction (c s z a : ℂ) (h : c + s * z ≠ 0) :
    c * s * ((a * c * z + s) / (c + s * z)) =
      s ^ 2 + (a * c ^ 2 - s ^ 2) * (s * z / (c + s * z)) := by
  field_simp
  ring

/-- The second-index difference in terms of the angular derivative. -/
private theorem sub_fourierIntegrand_shift_right (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    (halfCosh t * halfSinh t) •
        ((τ + n : ℂ) • fourierIntegrand τ (n - 1) (k + 1) t -
          (τ - n : ℂ) • fourierIntegrand τ (n + 1) (k - 1) t) =
      (2 * (n : ℂ) * halfSinh t ^ 2) • fourierIntegrand τ n k t + weightedIntegrand τ n k t := by
  ext θ
  let c := halfCosh t
  let s := halfSinh t
  let z := phase 1 θ
  let w := phase (-1) θ
  let A := positiveBase t θ
  let B := negativeBase t θ
  have hAB : z * w = 1 := phase_mul_phase_neg 1 θ
  have hzB : z * B = 1 * c * z + s := by
    change z * (c + s * w) = _
    rw [mul_add, mul_left_comm z s, hAB, mul_one, one_mul, mul_comm z c]
  have hwA : w * A = 1 * c * w + s := by
    change w * (c + s * z) = _
    rw [mul_add, mul_left_comm w s, mul_comm w z, hAB, mul_one, one_mul, mul_comm w c]
  have hplus : c * s * (z * B / A) = s ^ 2 + s * z / A := by
    rw [hzB]
    have h := mul_shift_fraction c s z 1 (positiveBase_ne_zero t θ)
    simp only [one_mul] at h
    rw [show c ^ 2 - s ^ 2 = 1 from halfCosh_sq_sub_halfSinh_sq t, one_mul] at h
    rw [one_mul]
    change c * s * ((c * z + s) / (c + s * z)) = s ^ 2 + s * z / (c + s * z)
    exact h
  have hminus : c * s * (w * A / B) = s ^ 2 + s * w / B := by
    rw [hwA]
    have h := mul_shift_fraction c s w 1 (negativeBase_ne_zero t θ)
    simp only [one_mul] at h
    rw [show c ^ 2 - s ^ 2 = 1 from halfCosh_sq_sub_halfSinh_sq t, one_mul] at h
    rw [one_mul]
    change c * s * ((c * w + s) / (c + s * w)) = s ^ 2 + s * w / (c + s * w)
    exact h
  change (c * s) * ((τ + n) * integrand τ (n - 1) (k + 1) t θ -
      (τ - n) * integrand τ (n + 1) (k - 1) t θ) =
    (2 * (n : ℂ) * s ^ 2) * integrand τ n k t θ +
      integrand τ n k t θ * angularWeight τ n t θ
  rw [integrand_lower, integrand_raise, angularWeight]
  change (c * s) * ((τ + n) * (integrand τ n k t θ * (z * B / A)) -
      (τ - n) * (integrand τ n k t θ * (w * A / B))) =
    (2 * (n : ℂ) * s ^ 2) * integrand τ n k t θ +
      integrand τ n k t θ * ((τ + n) * s * z / A - (τ - n) * s * w / B)
  calc
    _ = integrand τ n k t θ * ((τ + n) * (c * s * (z * B / A)) -
          (τ - n) * (c * s * (w * A / B))) := by ring
    _ = _ := by rw [hplus, hminus]; ring

/-- The first-index difference in terms of the angular derivative. -/
private theorem sub_fourierIntegrand_shift_left (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    (halfCosh t * halfSinh t) •
        ((τ - n : ℂ) • fourierIntegrand τ n (k - 1) t -
          (τ + n : ℂ) • fourierIntegrand τ n (k + 1) t +
          weightedIntegrand τ n (k + 1) t + weightedIntegrand τ n (k - 1) t) =
      (2 * (n : ℂ) * halfSinh t ^ 2) • fourierIntegrand τ n k t -
        (halfCosh t ^ 2 + halfSinh t ^ 2) • weightedIntegrand τ n k t := by
  ext θ
  let c := halfCosh t
  let s := halfSinh t
  let z := phase 1 θ
  let w := phase (-1) θ
  let A := positiveBase t θ
  let B := negativeBase t θ
  let W := integrand τ n k t θ
  let p : ℂ := τ + n
  let q : ℂ := τ - n
  have hz : z * w = 1 := phase_mul_phase_neg 1 θ
  have hp : -p * z + (z + w) * (p * s * z / A) = p * ((-1 * c * z + s) / A) := by
    have hA : A = c + s * z := rfl
    field_simp [show A ≠ 0 from positiveBase_ne_zero t θ]
    rw [hA]
    linear_combination p * s * (hz)
  have hm : q * w - (z + w) * (q * s * w / B) = -q * ((-1 * c * w + s) / B) := by
    have hB : B = c + s * w := rfl
    field_simp [show B ≠ 0 from negativeBase_ne_zero t θ]
    rw [hB]
    linear_combination -q * s * (hz)
  have hplus := mul_shift_fraction c s z (-1) (positiveBase_ne_zero t θ)
  have hminus := mul_shift_fraction c s w (-1) (negativeBase_ne_zero t θ)
  change (c * s) * (q * fourierIntegrand τ n (k - 1) t θ -
        p * fourierIntegrand τ n (k + 1) t θ +
        weightedIntegrand τ n (k + 1) t θ + weightedIntegrand τ n (k - 1) t θ) =
      (2 * (n : ℂ) * s ^ 2) * W - (c ^ 2 + s ^ 2) * (W * angularWeight τ n t θ)
  rw [sub_eq_add_neg k, fourierIntegrand_add_index, fourierIntegrand_add_index,
    weightedIntegrand_add_index, weightedIntegrand_add_index, angularWeight]
  change (c * s) * (q * (w * W) - p * (z * W) +
        z * W * (p * s * z / A - q * s * w / B) + w * W * (p * s * z / A - q * s * w / B)) =
    (2 * (n : ℂ) * s ^ 2) * W - (c ^ 2 + s ^ 2) * (W * (p * s * z / A - q * s * w / B))
  calc
    _ = c * s * (W * ((-p * z + (z + w) * (p * s * z / A)) +
          (q * w - (z + w) * (q * s * w / B)))) := by ring
    _ = W * (p * (c * s * ((-1 * c * z + s) / A)) -
          q * (c * s * ((-1 * c * w + s) / B))) := by rw [hp, hm]; ring
    _ = _ := by
      change W * (p * (c * s * ((-1 * c * z + s) / (c + s * z))) -
          q * (c * s * ((-1 * c * w + s) / (c + s * w)))) = _
      rw [hplus, hminus]
      change W * (p * (s ^ 2 + (-1 * c ^ 2 - s ^ 2) * (s * z / A)) -
          q * (s ^ 2 + (-1 * c ^ 2 - s ^ 2) * (s * w / B))) = _
      dsimp only [p, q]
      ring

/-- Moving an integer successor across the real cast and addition. -/
private theorem add_cast_add_one (n : ℝ) (k : ℤ) :
    n + ((k + 1 : ℤ) : ℝ) = n + k + 1 := by push_cast; ring

/-- Moving an integer predecessor across the real cast and addition. -/
private theorem add_cast_sub_one (n : ℝ) (k : ℤ) :
    n + ((k - 1 : ℤ) : ℝ) = n + k - 1 := by push_cast; ring

/-- A lowering of the second index and a raising of the shift keep the first index. -/
private theorem sub_one_add_cast_add_one (n : ℝ) (k : ℤ) :
    n - 1 + ((k + 1 : ℤ) : ℝ) = n + k := by push_cast; ring

/-- A raising of the second index and a lowering of the shift keep the first index. -/
private theorem add_one_add_cast_sub_one (n : ℝ) (k : ℤ) :
    n + 1 + ((k - 1 : ℤ) : ℝ) = n + k := by push_cast; ring

/-- The half-argument cosine and sine have nonzero product away from zero. -/
private theorem halfCosh_mul_halfSinh_ne_zero {t : ℝ} (ht : t ≠ 0) :
    halfCosh t * halfSinh t ≠ 0 := by
  have hs : (Real.sinh t : ℂ) ≠ 0 := ofReal_ne_zero.mpr
    (fun h => ht (Real.sinh_eq_zero.mp h))
  rw [ofReal_sinh_eq_half, mul_ne_zero_iff] at hs
  exact hs.2

end MatrixElementDerivative

open MatrixElementDerivative

/-- **Derivative through the second index** (Vilenkin–Klimyk, Vol. 1, §6.7.2 (8)–(13), p. 336).
`d/dt 𝔓^τ_{mn} = ½(τ + n) 𝔓^τ_{m,n-1} + ½(τ - n) 𝔓^τ_{m,n+1}`. -/
theorem hasDerivAt_boostMatrixElement_right (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    HasDerivAt (fun s => boostMatrixElement τ (n + k) n s)
      ((τ + n) / 2 * boostMatrixElement τ (n + k) (n - 1) t +
        (τ - n) / 2 * boostMatrixElement τ (n + k) (n + 1) t) t := by
  simpa only [sub_one_add_cast_add_one, add_one_add_cast_sub_one] using
    hasDerivAt_normalizedIntegral τ n k t

/-- **Derivative through the first index** (Vilenkin–Klimyk, Vol. 1, §6.7.2 (8)–(13), p. 336).
`d/dt 𝔓^τ_{mn} = ½(τ - m + 1) 𝔓^τ_{m-1,n} + ½(τ + m + 1) 𝔓^τ_{m+1,n}`. -/
theorem hasDerivAt_boostMatrixElement_left (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    HasDerivAt (fun s => boostMatrixElement τ (n + k) n s)
      ((τ - (n + k : ℝ) + 1) / 2 * boostMatrixElement τ (n + k - 1) n t +
        (τ + (n + k : ℝ) + 1) / 2 * boostMatrixElement τ (n + k + 1) n t) t := by
  have h := congrArg normalizedIntegral (add_fourierIntegrand_shift τ n k t)
  simp only [map_add, map_sub, map_smul, smul_eq_mul, normalizedIntegral_fourierIntegrand,
    normalizedIntegral_weightedIntegrand, add_cast_add_one, add_cast_sub_one] at h
  simp only [Int.cast_add, Int.cast_sub, Int.cast_one] at h
  rw [show n - 1 + (k : ℝ) + 1 = n + k by ring,
    show n + 1 + (k : ℝ) - 1 = n + k by ring] at h
  have he :
      ((τ + n) / 2) * boostMatrixElement τ (n + k) (n - 1) t +
        ((τ - n) / 2) * boostMatrixElement τ (n + k) (n + 1) t =
      ((τ - (n + k : ℝ) + 1) / 2) * boostMatrixElement τ (n + k - 1) n t +
        ((τ + (n + k : ℝ) + 1) / 2) * boostMatrixElement τ (n + k + 1) n t := by
    push_cast
    linear_combination h / 2
  rw [← he]
  exact hasDerivAt_boostMatrixElement_right τ n k t

/-- **Three-term recurrence in the second index.** For `t ≠ 0`, `m = n + k`,
`2(n cosh t - m)/sinh t · 𝔓^τ_{mn} = (τ + n) 𝔓^τ_{m,n-1} - (τ - n) 𝔓^τ_{m,n+1}`. -/
theorem boostMatrixElement_recurrence_right (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) (ht : t ≠ 0) :
    ((2 * (n * Real.cosh t - (n + k)) / Real.sinh t : ℝ) : ℂ) *
        boostMatrixElement τ (n + k) n t =
      (τ + n) * boostMatrixElement τ (n + k) (n - 1) t -
        (τ - n) * boostMatrixElement τ (n + k) (n + 1) t := by
  have h := congrArg normalizedIntegral (sub_fourierIntegrand_shift_right τ n k t)
  simp only [map_add, map_sub, map_smul, smul_eq_mul, normalizedIntegral_fourierIntegrand,
    normalizedIntegral_weightedIntegrand, sub_one_add_cast_add_one, add_one_add_cast_sub_one] at h
  have hc := halfCosh_mul_halfSinh_ne_zero ht
  have hf : (halfCosh t * halfSinh t) *
      (((2 * (n * Real.cosh t - (n + k)) / Real.sinh t : ℝ) : ℂ)) =
      2 * (n : ℂ) * halfSinh t ^ 2 - (k : ℂ) := by
    push_cast
    rw [← ofReal_cosh, ← ofReal_sinh, ofReal_cosh_eq_half, ofReal_sinh_eq_half]
    rw [mul_div_mul_left _ _ (by norm_num : (2 : ℂ) ≠ 0), ← mul_div_assoc,
      mul_div_cancel_left₀ _ hc]
    linear_combination (n : ℂ) * (halfCosh_sq_sub_halfSinh_sq t)
  apply mul_left_cancel₀ hc
  rw [← mul_assoc, hf, h]
  ring

/-- **Three-term recurrence in the first index.** For `t ≠ 0`, `m = n + k`,
`2(m cosh t - n)/sinh t · 𝔓^τ_{mn} = (τ - m + 1) 𝔓^τ_{m-1,n} - (τ + m + 1) 𝔓^τ_{m+1,n}`. -/
theorem boostMatrixElement_recurrence_left (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) (ht : t ≠ 0) :
    ((2 * ((n + k) * Real.cosh t - n) / Real.sinh t : ℝ) : ℂ) *
        boostMatrixElement τ (n + k) n t =
      (τ - (n + k : ℝ) + 1) * boostMatrixElement τ (n + k - 1) n t -
        (τ + (n + k : ℝ) + 1) * boostMatrixElement τ (n + k + 1) n t := by
  have h := congrArg normalizedIntegral (sub_fourierIntegrand_shift_left τ n k t)
  simp only [map_add, map_sub, map_smul, smul_eq_mul, normalizedIntegral_fourierIntegrand,
    normalizedIntegral_weightedIntegrand, add_cast_add_one, add_cast_sub_one] at h
  simp only [Int.cast_add, Int.cast_sub, Int.cast_one] at h
  have hc := halfCosh_mul_halfSinh_ne_zero ht
  have hf : (halfCosh t * halfSinh t) *
      (((2 * ((n + k) * Real.cosh t - n) / Real.sinh t : ℝ) : ℂ)) =
      2 * (n : ℂ) * halfSinh t ^ 2 + (k : ℂ) * (halfCosh t ^ 2 + halfSinh t ^ 2) := by
    push_cast
    rw [← ofReal_cosh, ← ofReal_sinh, ofReal_cosh_eq_half, ofReal_sinh_eq_half]
    rw [mul_div_mul_left _ _ (by norm_num : (2 : ℂ) ≠ 0), ← mul_div_assoc,
      mul_div_cancel_left₀ _ hc]
    linear_combination (n : ℂ) * (halfCosh_sq_sub_halfSinh_sq t)
  apply mul_left_cancel₀ hc
  rw [← mul_assoc, hf]
  push_cast
  linear_combination -h

/-- **Lowering relation.** For `t ≠ 0`, `m = n + k`,
`d/dt 𝔓 + (n cosh t - m)/sinh t · 𝔓 = (τ + n) 𝔓^τ_{m,n-1}`. -/
theorem boostMatrixElement_ladder_lower (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) (ht : t ≠ 0) :
    deriv (fun s => boostMatrixElement τ (n + k) n s) t +
        (((n * Real.cosh t - (n + k)) / Real.sinh t : ℝ) : ℂ) * boostMatrixElement τ (n + k) n t =
      (τ + n) * boostMatrixElement τ (n + k) (n - 1) t := by
  rw [(hasDerivAt_boostMatrixElement_right τ n k t).deriv]
  have h := boostMatrixElement_recurrence_right τ n k t ht
  push_cast at h ⊢
  linear_combination h / 2

/-- **Raising relation.** For `t ≠ 0`, `m = n + k`,
`d/dt 𝔓 - (n cosh t - m)/sinh t · 𝔓 = (τ - n) 𝔓^τ_{m,n+1}`. -/
theorem boostMatrixElement_ladder_raise (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) (ht : t ≠ 0) :
    deriv (fun s => boostMatrixElement τ (n + k) n s) t -
        (((n * Real.cosh t - (n + k)) / Real.sinh t : ℝ) : ℂ) * boostMatrixElement τ (n + k) n t =
      (τ - n) * boostMatrixElement τ (n + k) (n + 1) t := by
  rw [(hasDerivAt_boostMatrixElement_right τ n k t).deriv]
  have h := boostMatrixElement_recurrence_right τ n k t ht
  push_cast at h ⊢
  linear_combination -h / 2

end SFVK.SU11
