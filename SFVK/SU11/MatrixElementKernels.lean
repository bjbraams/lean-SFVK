/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU11.Basic.BoostMatrixElements
public import SFVK.SU11.Basic.CircleModel
public import SFVKMathlib.RepresentationTheory.Continuous.MatrixElement
public import Mathlib.Analysis.Fourier.AddCircle
import SFVK.SU11.CircleModel
public import DLMF.Hypergeometric.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Haar.Unique
import SFVKMathlib.Analysis.Fourier.AddCircle

/-!
# Fourier kernels for the matrix elements of `SU(1,1)`

The generating kernel of the boost coefficients has a convergent Laurent expansion on the unit
circle. The same kernel gives the action on each Fourier mode in the principal-series circle
model. We also record the kernel symmetries and its Laplace specialization. The Laurent
expansion uses the binomial series from lean-DLMF's `DLMF.Hypergeometric.Basic`.
-/

public section

open AddCircle Complex MeasureTheory Set
open scoped ComplexConjugate Real InnerProductSpace

namespace SFVK.SU11

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

namespace FourierExpansion

/-- One factor in the Fourier generating function, given a point of the unit circle. -/
@[expose] noncomputable def boostBase (t : ℝ) (z : ℂ) : ℂ :=
  Real.cosh (t / 2) + Real.sinh (t / 2) * z

/-- The function whose Fourier coefficients are the boost matrix elements. -/
@[expose] noncomputable def boostKernel (τ : ℂ) (n t : ℝ) (z : ℂ) : ℂ :=
  boostBase t z ^ (τ + n) * boostBase t (conj z) ^ (τ - n)

/-- Complex conjugation acts on the unit-circle coordinate in the base. -/
theorem boostBase_conj (t : ℝ) (z : ℂ) :
    boostBase t (conj z) = conj (boostBase t z) := by
  simp only [boostBase, map_add, map_mul, conj_ofReal]

/-- The real part of the base is positive on the unit circle. -/
theorem boostBase_re_pos (t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    0 < (boostBase t z).re :=
  (Real.exp_pos _).trans_le (BoostMatrixElements.exp_neg_abs_le_re_of_norm_le_one t hz.le)

/-- The boost base lies in the principal branch domain on the unit circle. -/
theorem boostBase_mem_slitPlane (t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    boostBase t z ∈ slitPlane :=
  Or.inl (boostBase_re_pos t hz)

/-- Negating the angle conjugates the Fourier character. -/
theorem fourier_neg_angle (k : ℤ) (θ : 𝕋) : fourier k (-θ) = conj (fourier k θ) := by
  simp only [fourier_apply, zsmul_neg, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

/-- The half-period character value is the parity sign. -/
theorem fourier_half_period (k : ℤ) : fourier k (↑π : 𝕋) = (-1 : ℂ) ^ k := by
  rw [AddCircle.fourier_eq_zpow, fourier_coe_two_pi]
  simp [Complex.exp_pi_mul_I]

/-- The integral convention for the boost matrix element extracts Fourier index `-k`. -/
theorem boostMatrixElement_eq_fourierCoeff (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    boostMatrixElement τ (n + k) n t =
      fourierCoeff (fun θ : 𝕋 => boostKernel τ n t (fourier 1 θ)) (-k) := by
  rw [boostMatrixElement_def, fourierCoeff_eq_intervalIntegral _ _ 0, zero_add, real_smul,
    ofReal_div, ofReal_one, one_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [neg_neg, fourier_coe_two_pi, Int.cast_one, one_mul, boostKernel, boostBase,
    smul_eq_mul, add_sub_cancel_left]
  rw [← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg]
  push_cast
  ring

/-- The small boost coefficient is the integral of the kernel against a character. -/
theorem boostMatrixElement_eq_circleIntegral (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    boostMatrixElement τ (n + k) n t =
      ∫ θ : 𝕋, fourier k θ * boostKernel τ n t (fourier 1 θ) ∂haarAddCircle := by
  rw [boostMatrixElement_eq_fourierCoeff, fourierCoeff]
  simp only [neg_neg, smul_eq_mul]

/-- Reflection of the additive circle preserves integration against its Haar probability. -/
theorem integral_neg_angle (f : 𝕋 → ℂ) :
    (∫ θ : 𝕋, f (-θ) ∂haarAddCircle) = ∫ θ : 𝕋, f θ ∂haarAddCircle :=
  (Measure.measurePreserving_neg (haarAddCircle (T := 2 * π))).integral_comp'
    (f := MeasurableEquiv.neg 𝕋) f

/-- Principal powers multiply for a boost base and its conjugate. -/
private theorem boostBase_mul_conj_cpow (t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) (τ : ℂ) :
    boostBase t z ^ τ * boostBase t (conj z) ^ τ = (normSq (boostBase t z) : ℂ) ^ τ := by
  let a := boostBase t z
  have ha : a.arg ≠ π := (arg_lt_pi_iff.mpr (Or.inl (boostBase_re_pos t hz).le)).ne
  have harg : a.arg + (conj a).arg ∈ Ioc (-π) π := by
    rw [arg_conj, ite_eq_right ha, add_neg_cancel]
    exact ⟨neg_neg_of_pos Real.pi_pos, Real.pi_pos.le⟩
  rw [boostBase_conj, ← mul_cpow harg τ, Complex.mul_conj]

/-- The squared norm of the boost base gives the real Laplace kernel. -/
private theorem normSq_boostBase_exp (t θ : ℝ) :
    normSq (boostBase t (exp ((θ : ℂ) * I))) = Real.cosh t + Real.sinh t * Real.cos θ := by
  let a := Real.cosh (t / 2)
  let b := Real.sinh (t / 2)
  let z := exp ((θ : ℂ) * I)
  have hn : normSq z = 1 := by
    dsimp only [z]
    rw [normSq_eq_norm_sq, norm_exp_ofReal_mul_I, one_pow]
  have hre : ((a : ℂ) * conj ((b : ℂ) * z)).re = a * b * Real.cos θ := by
    rw [map_mul, conj_ofReal, ← mul_assoc, ← ofReal_mul, re_ofReal_mul, conj_re]
    exact congrArg (fun x : ℝ => (a * b) * x) (exp_ofReal_mul_I_re θ)
  have ht : 2 * (t / 2) = t := by ring
  have hc := Real.cosh_two_mul (t / 2)
  have hs := Real.sinh_two_mul (t / 2)
  rw [ht] at hc hs
  unfold boostBase
  rw [normSq_add, normSq_mul, normSq_ofReal, normSq_ofReal, hn, mul_one, hre, hc, hs]
  ring

/-- The zeroth boost kernel in angular coordinates is the complex power of the Laplace kernel. -/
theorem boostKernel_zero_eq_laplace (τ : ℂ) (t θ : ℝ) :
    boostKernel τ 0 t (exp ((θ : ℂ) * I)) =
      ((Real.cosh t + Real.sinh t * Real.cos θ : ℝ) : ℂ) ^ τ := by
  simp only [boostKernel, ofReal_zero, add_zero, sub_zero]
  rw [boostBase_mul_conj_cpow t (norm_exp_ofReal_mul_I θ), normSq_boostBase_exp]

/-- The real Laplace kernel is strictly positive for every real boost and real angle. -/
theorem laplaceKernel_pos (t θ : ℝ) :
    0 < Real.cosh t + Real.sinh t * Real.cos θ := by
  rw [← normSq_boostBase_exp]
  exact normSq_pos.mpr (slitPlane_ne_zero (boostBase_mem_slitPlane t (norm_exp_ofReal_mul_I θ)))

/-- The product of the two branch factors is the principal power of the modulus. -/
private theorem boostBase_mul_conj_cpow_eq_norm (t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) (τ : ℂ) :
    boostBase t z ^ τ * boostBase t (conj z) ^ τ = (‖boostBase t z‖ : ℂ) ^ (2 * τ) := by
  have hr : 0 < ‖boostBase t z‖ :=
    norm_pos_iff.mpr (slitPlane_ne_zero (boostBase_mem_slitPlane t hz))
  have him : (log (‖boostBase t z‖ : ℂ) * 2).im = 0 := by
    simp [log_im, arg_ofReal_of_nonneg hr.le, mul_im]
  rw [boostBase_mul_conj_cpow t hz, normSq_eq_norm_sq, ofReal_pow]
  have h2 : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
  nth_rw 1 [← cpow_natCast, ← h2]
  exact (cpow_mul τ (by rw [him]; exact neg_neg_of_pos Real.pi_pos)
    (by rw [him]; exact Real.pi_pos.le)).symm

/-- The half-power quotient becomes the unit phase of the boost base. -/
private theorem boostBase_halfPhase (t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) (e : Fin 2) :
    boostBase t z ^ ((e : ℕ) / (2 : ℂ)) *
      boostBase t (conj z) ^ (-((e : ℕ) / (2 : ℂ))) =
        (boostBase t z / (‖boostBase t z‖ : ℂ)) ^ (e : ℕ) := by
  let a := boostBase t z
  let b := boostBase t (conj z)
  let r : ℂ := (‖a‖ : ℂ)
  have hA : a ≠ 0 := slitPlane_ne_zero (boostBase_mem_slitPlane t hz)
  have hB : b ≠ 0 := slitPlane_ne_zero
    (boostBase_mem_slitPlane t ((norm_conj z).trans hz))
  have hR : r ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hA)
  have hb : b ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hB)
  have hprod : a ^ (1 / 2 : ℂ) * b ^ (1 / 2 : ℂ) = r := by
    simpa [a, b, r] using boostBase_mul_conj_cpow_eq_norm t hz (1 / 2)
  have hsq : (a ^ (1 / 2 : ℂ)) ^ 2 = a := by
    rw [pow_two, ← cpow_add _ _ hA]
    norm_num
  fin_cases e
  · simp
  · norm_num [Fin.val_natCast]
    rw [cpow_neg]
    apply (eq_div_iff hR).mpr
    calc
      _ = (a ^ (1 / 2 : ℂ)) ^ 2 * ((b ^ (1 / 2 : ℂ))⁻¹ * b ^ (1 / 2 : ℂ)) := by
        rw [← hprod]
        ring
      _ = _ := by rw [inv_mul_cancel₀ hb, mul_one, hsq]

/-- The boost denominator of the circle model is the first generating-function factor. -/
private theorem circleDenominator_boost (t : ℝ) (z : ℂ) :
    circleDenominator (boost t) z = boostBase t z := by
  rw [circleDenominator_def, entryA_boost, entryB_boost, conj_ofReal, add_comm, boostBase]

/-- The boost acts on a Fourier character by multiplying it by the reversed generating function. -/
private theorem principalAction_boost_fourier (τ : ℂ) (e : Fin 2) (n : ℤ) (t : ℝ) (θ : 𝕋) :
    principalAction τ e (boost t) (fourier n) θ =
      fourier n θ * boostKernel τ (n - (e : ℕ) / 2) t (conj (fourier 1 θ)) := by
  let z := fourier 1 θ
  let a := boostBase t z
  let b := boostBase t (conj z)
  let d : ℂ := (e : ℕ) / 2
  have hz : ‖z‖ = 1 := norm_fourier_one θ
  have hA : a ≠ 0 := slitPlane_ne_zero (boostBase_mem_slitPlane t hz)
  have hB : b ≠ 0 := slitPlane_ne_zero
    (boostBase_mem_slitPlane t ((norm_conj z).trans hz))
  have hm : fourier 1 (circleAct (boost t) θ) = z * b / a := by
    rw [fourier_circleAct, circleMobius_def,
      circleNumerator_eq_mul_conj (boost t) hz, circleDenominator_boost, ← boostBase_conj]
  have hweight : ((n - (e : ℕ) / 2 : ℝ) : ℂ) = (n : ℂ) - d := by
    push_cast
    rfl
  have hplus : τ + ((n : ℂ) - d) = (τ + (n : ℂ)) + (-d) := by ring
  have hminus : τ - ((n : ℂ) - d) = (τ + (-(n : ℤ) : ℂ)) + d := by ring
  have hkernel :
      boostKernel τ (n - (e : ℕ) / 2) t (conj z) =
        ((‖a‖ : ℂ) ^ (2 * τ)) * (a / (‖a‖ : ℂ)) ^ (e : ℕ) * (b ^ n / a ^ n) := by
    unfold boostKernel
    rw [conj_conj, hweight, hplus, hminus, cpow_add _ _ hB, cpow_add _ _ hB,
      cpow_add _ _ hA, cpow_add _ _ hA, cpow_neg a (n : ℂ), cpow_intCast, cpow_intCast]
    have h1 := boostBase_mul_conj_cpow_eq_norm t hz τ
    have h2 := boostBase_halfPhase t hz e
    dsimp only [a, b, d] at *
    rw [← h2, ← h1, div_eq_mul_inv]
    ring
  simp only [principalAction_def, principalMultiplier_def, circleDenominator_boost]
  rw [AddCircle.fourier_eq_zpow n _, hm, div_zpow, mul_zpow, hkernel, AddCircle.fourier_eq_zpow n θ]
  dsimp only [a, b, z]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The coefficient on a pure boost is the boost matrix element at the Fourier weights. -/
theorem principalSeries_matrixElement_boost_eq
    (τ : ℂ) (e : Fin 2) (n' n : ℤ) (t : ℝ) :
    (principalSeries τ e).matrixElement (fourierBasis (T := 2 * π)) n' n (boost t) =
      boostMatrixElement τ (n' - (e : ℕ) / 2) (n - (e : ℕ) / 2) t := by
  have hw : (n' - (e : ℕ) / 2 : ℝ) = (n - (e : ℕ) / 2 : ℝ) + ((n' - n : ℤ) : ℝ) := by
    push_cast
    ring
  rw [ContRepresentation.matrixElement_def, ← HilbertBasis.repr_apply_apply,
    fourierBasis_repr, fourierCoeff, coe_fourierBasis, hw, boostMatrixElement_eq_circleIntegral,
    ← integral_neg_angle
      (fun θ => fourier (n' - n) θ *
        boostKernel τ (n - (e : ℕ) / 2) t (fourier 1 θ))]
  apply integral_congr_ae
  have hrep := principalSeries_ae_eq τ e (boost t) (fourierLp (T := 2 * π) 2 n)
  have hmode := (quasiMeasurePreserving_circleAct (boost t)).ae_eq_comp
    (coeFn_fourierLp (T := 2 * π) 2 n)
  filter_upwards [hrep, hmode] with θ hrepθ hmodeθ
  dsimp only [Function.comp_apply] at hmodeθ
  rw [smul_eq_mul, hrepθ, principalAction_def, hmodeθ, ← principalAction_def,
    principalAction_boost_fourier, ← mul_assoc, ← fourier_add, fourier_neg_angle,
    fourier_neg_angle, ← fourier_neg]
  have hi : -n' + n = -(n' - n) := by omega
  rw [hi, fourier_neg]

/-- A principal-series matrix element of a rotation is diagonal in the Fourier basis. -/
private theorem matrixElement_rotation (τ : ℂ) (e : Fin 2) (n' n : ℤ) (α : ℝ) :
    (principalSeries τ e).matrixElement (fourierBasis (T := 2 * π)) n' n (rotation α) =
      if n' = n then exp (((n : ℂ) - (e : ℂ) / 2) * α * I) else 0 := by
  rw [ContRepresentation.matrixElement_def, coe_fourierBasis, principalSeries_rotation,
    inner_smul_right, ← coe_fourierBasis, orthonormal_iff_ite.mp fourierBasis.orthonormal]
  split_ifs <;> simp

/-- Left rotation multiplies a matrix element by the corresponding row phase. -/
theorem matrixElement_rotation_mul (τ : ℂ) (e : Fin 2) (n' n : ℤ) (α : ℝ) (g : SU11) :
    (principalSeries τ e).matrixElement (fourierBasis (T := 2 * π)) n' n (rotation α * g) =
      exp (((n' : ℂ) - (e : ℂ) / 2) * α * I) *
        (principalSeries τ e).matrixElement (fourierBasis (T := 2 * π)) n' n g := by
  have h := (principalSeries τ e).hasSum_matrixElement_mul (fourierBasis (T := 2 * π))
    n' n (rotation α) g
  have hsingle := hasSum_single n' (f := fun k =>
    (principalSeries τ e).matrixElement (fourierBasis (T := 2 * π)) n' k (rotation α) *
      (principalSeries τ e).matrixElement (fourierBasis (T := 2 * π)) k n g) (by
    intro k hk
    simp only [matrixElement_rotation, ite_eq_right (Ne.symm hk), zero_mul])
  simpa [matrixElement_rotation] using h.unique hsingle

/-- Right rotation multiplies a matrix element by the corresponding column phase. -/
theorem matrixElement_mul_rotation (τ : ℂ) (e : Fin 2) (n' n : ℤ) (γ : ℝ) (g : SU11) :
    (principalSeries τ e).matrixElement (fourierBasis (T := 2 * π)) n' n (g * rotation γ) =
      exp (((n : ℂ) - (e : ℂ) / 2) * γ * I) *
        (principalSeries τ e).matrixElement (fourierBasis (T := 2 * π)) n' n g := by
  rw [ContRepresentation.matrixElement_def, map_mul, mul_apply_eq_comp,
    coe_fourierBasis, principalSeries_rotation, map_smul, inner_smul_right,
    ContRepresentation.matrixElement_def, coe_fourierBasis]

/-- The complex binomial coefficient of a single boost factor on the unit circle. -/
@[expose] noncomputable def boostBinomialCoefficient (s : ℂ) (t : ℝ) (j : ℕ) : ℂ :=
  (Real.cosh (t / 2) : ℂ) ^ s *
    (DLMF.Hypergeometric.pochhammer (-s) j / (j.factorial : ℂ)) *
    (-(Real.tanh (t / 2) : ℂ)) ^ j

/-- The binomial expansion of one boost factor, using the ratio of the two boost entries. -/
private theorem hasSum_boostBase_cpow (s : ℂ) (t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    HasSum (fun j : ℕ => boostBinomialCoefficient s t j * z ^ j) (boostBase t z ^ s) := by
  let c : ℂ := (Real.cosh (t / 2) : ℂ)
  let r : ℂ := (Real.tanh (t / 2) : ℂ)
  have hc : c ≠ 0 := ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  have hr : ‖-r * z‖ < 1 := by
    simpa only [norm_mul, norm_neg, hz, mul_one, r, Complex.norm_real, Real.norm_eq_abs] using
      Real.abs_tanh_lt_one (t / 2)
  have hbase : boostBase t z = c * (1 - (-r * z)) := by
    simp only [boostBase, r, Real.tanh_eq_sinh_div_cosh, ofReal_div]
    rw [mul_sub, mul_one, neg_mul, mul_neg, sub_neg_eq_add, ← mul_assoc, mul_div_cancel₀ _ hc]
  have harg : c.arg + (1 - (-r * z)).arg ∈ Ioc (-π) π := by
    dsimp only [c]
    rw [arg_ofReal_of_nonneg (Real.cosh_pos _).le, zero_add]
    exact ⟨neg_pi_lt_arg _, arg_le_pi _⟩
  rw [hbase, mul_cpow harg]
  have h := (DLMF.Hypergeometric.hasSum_pochhammer_div_factorial (β := -s) hr).mul_left (c ^ s)
  rw [neg_neg] at h
  refine h.congr_fun fun j => ?_
  simp only [mul_pow, boostBinomialCoefficient, c, r]
  ring

/-- The two-index binomial series is grouped by the difference of its two exponents. -/
@[expose] noncomputable def boostLaurentCoefficient (τ : ℂ) (n t : ℝ) (k : ℤ) : ℂ :=
  ∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = k},
    boostBinomialCoefficient (τ + n) t p.1.1 * boostBinomialCoefficient (τ - n) t p.1.2

/-- The grouped binomial series sums to the boost kernel on the circle. -/
theorem hasSum_boostLaurentCoefficient (τ : ℂ) (n t : ℝ) (θ : 𝕋) :
    HasSum (fun k : ℤ => fourier k θ • boostLaurentCoefficient τ n t k)
      (boostKernel τ n t (fourier 1 θ)) := by
  let z := fourier 1 θ
  have hz : ‖z‖ = 1 := norm_fourier_one θ
  have ha := hasSum_boostBase_cpow (τ + n) t hz
  have hb := hasSum_boostBase_cpow (τ - n) t ((norm_conj _).trans hz)
  have hab := ha.mul hb (summable_mul_of_summable_norm ha.summable.norm hb.summable.norm)
  let freq (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - p.2
  have hp (m : ℕ) : z ^ m = fourier (m : ℤ) θ := by rw [AddCircle.fourier_eq_zpow, zpow_natCast]
  have hn (m : ℕ) : (conj z) ^ m = fourier (-(m : ℤ)) θ := by
    rw [fourier_neg, ← hp, map_pow]
  refine (hab.tsum_fiberwise freq).congr_fun fun k => ?_
  rw [boostLaurentCoefficient, smul_eq_mul, ← tsum_mul_left]
  apply tsum_congr
  intro p
  simp only [hp, hn, mul_mul_mul_comm, ← fourier_add, ← sub_eq_add_neg, p.2, freq]
  ring

/-- The coefficients of the grouped binomial series are the integral coefficients. -/
theorem boostMatrixElement_eq_laurent (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    boostMatrixElement τ (n + k) n t = boostLaurentCoefficient τ n t (-k) := by
  rw [boostMatrixElement_eq_fourierCoeff,
    fourierCoeff_eq_of_hasSum (fun θ => hasSum_boostLaurentCoefficient τ n t θ)]

/-- Shifting the degree and the second index by one half multiplies the kernel by its first base. -/
theorem boostKernel_degree_shift (τ : ℂ) (n t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    boostKernel (τ + 1 / 2) (n + 1 / 2) t z = boostBase t z * boostKernel τ n t z := by
  have hA := slitPlane_ne_zero (boostBase_mem_slitPlane t hz)
  unfold boostKernel
  push_cast
  rw [show τ + 1 / 2 + ((n : ℂ) + 1 / 2) = (τ + n) + 1 by ring,
    show τ + 1 / 2 - ((n : ℂ) + 1 / 2) = τ - n by ring, cpow_add _ _ hA, cpow_one]
  ring

/-- The angle kernel, multiplied by a character, is continuous. -/
theorem continuous_boostKernel_character (τ : ℂ) (n t : ℝ) (k : ℤ) :
    Continuous (fun θ : 𝕋 => fourier k θ * boostKernel τ n t (fourier 1 θ)) := by
  have hA : Continuous (fun θ : 𝕋 => boostBase t (fourier 1 θ)) := by
    unfold boostBase
    fun_prop
  have hB : Continuous (fun θ : 𝕋 => boostBase t (conj (fourier 1 θ))) := by
    unfold boostBase
    fun_prop
  have hbranch (θ : 𝕋) : boostBase t (fourier 1 θ) ∈ slitPlane :=
    boostBase_mem_slitPlane t (norm_fourier_one θ)
  have hconj (θ : 𝕋) : boostBase t (conj (fourier 1 θ)) ∈ slitPlane :=
    boostBase_mem_slitPlane t ((norm_conj _).trans (norm_fourier_one θ))
  unfold boostKernel
  exact (fourier k).continuous.mul
    ((hA.cpow continuous_const hbranch).mul (hB.cpow continuous_const hconj))

/-- The product of degree parameters adds in the kernel. -/
theorem boostKernel_mul (τ₁ τ₂ : ℂ) (n₁ n₂ t : ℝ) {z : ℂ} (hz : ‖z‖ = 1) :
    boostKernel τ₁ n₁ t z * boostKernel τ₂ n₂ t z =
      boostKernel (τ₁ + τ₂) (n₁ + n₂) t z := by
  have hA := slitPlane_ne_zero (boostBase_mem_slitPlane t hz)
  have hB := slitPlane_ne_zero (boostBase_mem_slitPlane t ((norm_conj _).trans hz))
  unfold boostKernel
  push_cast
  rw [show τ₁ + τ₂ + ((n₁ : ℂ) + n₂) = (τ₁ + n₁) + (τ₂ + n₂) by ring,
    show τ₁ + τ₂ - ((n₁ : ℂ) + n₂) = (τ₁ - n₁) + (τ₂ - n₂) by ring,
    cpow_add (τ₁ + n₁) (τ₂ + n₂) hA, cpow_add (τ₁ - n₁) (τ₂ - n₂) hB]
  ring

end FourierExpansion

end SFVK.SU11
