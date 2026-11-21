/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.Definitions
import DLMF.OrthogonalPolynomials.Basic.Classical
import DLMF.OrthogonalPolynomials.Integrals.LaguerreHankel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import TauCeti.Analysis.Complex.Euclidean.Prod
import TauCeti.Analysis.InnerProductSpace.PiL2
import SFVK.MotionGroups.MatrixElements
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import TauCeti.Analysis.Matrix.EuclideanLin
public import SFVK.MotionGroups.Basic.Zonal
public import SFVK.MotionGroups.CircleModel
import SFVK.MotionGroups.Spherical
import TauCeti.Geometry.Euclidean.Volume.Sphere
import TauCeti.MeasureTheory.Constructions.HaarToSphere

/-!
# The quasi-regular representation of `M(n)` and the Hankel transform

Mathlib's Fourier transform `𝓕f(ξ) = ∫ e^{-2πi⟨x, ξ⟩} f(x) dx` carries the quasi-regular
representation `L(g) f = f ∘ g⁻¹` of `M(n)` to `e^{-2πi⟨a, ξ⟩} 𝓕f(k⁻¹ξ)`, which on the circle
`|ξ| = ρ` of `ℝ²` is the circle model `T_{-2πρ}`. On angular modes it is the Hankel transform,
which is self-inverse and isometric for real `ν > -1` and has the Laguerre functions as
eigenfunctions; on radial functions of `ℝⁿ` it is the Hankel transform of order `n/2 - 1`.
Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 1, §4.4.1 (1)–(7),
pp. 193–195, and §4.4.2 (1)–(7), pp. 196–197; Vol. 2, §10.2.6 (1)–(7), pp. 186–187, and
(13)–(17), p. 188; Dieudonné, *Special Functions and Linear Representations of Lie Groups*, §16,
p. 57. The Laguerre eigenfunction formula follows from lean-DLMF's
`integral_laguerreExtended_hankel` by the change of variables `t = r²`. The radial Fourier
formula uses Tau Ceti's polar integration theorem and the area of the unit sphere. The angular
formula uses its complex-plane isometry, Mathlib's polar integration and Bessel's circle integral.
-/

public noncomputable section

open AddCircle Complex MeasureTheory Set
open scoped Real InnerProductSpace FourierTransform Laplacian

namespace SFVK.MotionGroups

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- Fourier transform of a translate-rotate (Vilenkin–Klimyk Vol. 1 §4.4.1, pp. 193–195):
`𝓕(f ∘ g⁻¹)(ξ) = e^{-2πi⟨a, ξ⟩} 𝓕f(k⁻¹ ξ)`. -/
theorem fourier_comp_motionApply {n : ℕ} (g : MotionGroup n)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : Integrable f) (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (fun x => f (motionApply g⁻¹ x)) ξ =
      Complex.exp (-(2 * π * ⟪g.a, ξ⟫_ℝ : ℝ) * I) * 𝓕 f (rotE g.k⁻¹ ξ) := by
  let V := EuclideanSpace ℝ (Fin n)
  let k := g.k⁻¹
  let A := Matrix.UnitaryGroup.toLinearIsometryEquiv
    (⟨k.1, (Matrix.mem_specialOrthogonalGroup_iff.mp k.2).1⟩ :
      Matrix.orthogonalGroup (Fin n) ℝ)
  have hA (x : V) : A x = rotE k x := by
    rw [Matrix.UnitaryGroup.toLinearIsometryEquiv_apply, rotE_def, Matrix.toLpLin_apply]
  have hfun : (fun x : V => f (motionApply g⁻¹ x)) =
      (f ∘ A) ∘ fun x : V => x + -g.a := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, hA, rotE_add, motionApply_def,
      MotionGroup.inv_a, MotionGroup.inv_k, rotE_neg]
    exact congrArg f (add_comm _ _)
  rw [hfun]
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V)
    ((f ∘ A) ∘ fun x : V => x + -g.a) ξ = _
  rw [VectorFourier.fourierIntegral_comp_add_right]
  change Real.fourierChar ⟪-g.a, ξ⟫_ℝ • (𝓕 (f ∘ A) ξ) = _
  rw [Real.fourier_comp_linearIsometry, hA, inner_neg_left, Circle.smul_def,
    Real.fourierChar_apply]
  push_cast
  congr 2
  ring

/-- On the circle `|ξ| = ρ` the quasi-regular representation is `T_{-2πρ}`. -/
theorem fourier_comp_motionApply_circle (g : MotionGroup 2)
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (hf : Integrable f) (ρ : ℝ) (ψ : 𝕋) :
    𝓕 (fun x => f (motionApply g⁻¹ x)) (ρ • unitVec ψ) =
      circleAction (-(2 * π * ρ)) g (fun ψ' => 𝓕 f (ρ • unitVec ψ')) ψ := by
  rw [fourier_comp_motionApply g f hf, circleAction_def, unitVec_sub_rotAngle, rotE_def, map_smul,
    ← rotE_def, real_inner_smul_right]
  push_cast
  congr 2
  ring

/-- Cylindrical waves: `u(x) = Jₙ(R|x|) (x/|x|)ⁿ` (complex coordinate) satisfies `Δu = -R² u`
away from the origin. -/
theorem laplacian_cylindricalWave (R : ℂ) (n : ℤ) {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    Δ (fun y : EuclideanSpace ℝ (Fin 2) => besselJ n (R * ‖y‖) * (toComplex y / ‖y‖) ^ n) x =
      -R ^ 2 * (besselJ n (R * ‖x‖) * (toComplex x / ‖x‖) ^ n) := by
  sorry

/-- Fourier transform of an angular mode (Vilenkin–Klimyk Vol. 1 §4.4.2 (3), p. 196, in
Mathlib's normalization): `𝓕(φ(|x|) e^{inα})(ρ e(ψ)) = 2π (-i)ⁿ e^{inψ} (Hₙφ)(2πρ)`. -/
theorem fourier_angularMode (n : ℤ) (φ : ℝ → ℂ)
    (hφ : IntegrableOn (fun r => φ r * r) (Ioi 0)) (ρ : ℝ) (hρ : 0 < ρ) (ψ : 𝕋) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin 2) => φ ‖x‖ * (toComplex x / ‖x‖) ^ n) (ρ • unitVec ψ) =
      2 * π * (-I) ^ n * fourier n ψ * hankelTransform n φ (2 * π * ρ) := by
  let E := EuclideanSpace ℝ (Fin 2)
  let e : E ≃ₗᵢ[ℝ] ℂ :=
    (EuclideanSpace.finTwoEquivProd ℝ).trans Complex.equivRealProdLp.symm
  have he (x : E) : e x = toComplex x := by
    rw [show e x = Complex.equivRealProdLp.symm (EuclideanSpace.finTwoEquivProd ℝ x) from rfl,
      Complex.equivRealProdLp_symm_apply, EuclideanSpace.finTwoEquivProd_apply_fst,
      EuclideanSpace.finTwoEquivProd_apply_snd, toComplex_def]
  let F (x : E) := Complex.exp (-(2 * π * ⟪x, ρ • unitVec ψ⟫_ℝ : ℝ) * I) *
    (φ ‖x‖ * (toComplex x / ‖x‖) ^ n)
  let P (r : ℝ) (u : 𝕋) :=
    Complex.exp (I * (-(2 * π * (r : ℂ))) * (⟪ρ • unitVec ψ, unitVec u⟫_ℝ : ℝ)) * fourier n u
  let K (r θ : ℝ) := (φ r * r) * P r (θ : 𝕋)
  have hnorm (u : 𝕋) : ‖unitVec u‖ = 1 := by
    rw [← e.norm_map, he, toComplex_unitVec]
    exact Circle.norm_coe _
  have hp (r θ : ℝ) (hr : 0 < r) :
      e.symm (Complex.polarCoord.symm (r, θ)) = r • unitVec (θ : 𝕋) := by
    apply e.injective
    rw [LinearIsometryEquiv.apply_symm_apply, map_smul, he, toComplex_unitVec,
      fourier_circle_coe, Int.cast_one, one_mul, Complex.polarCoord_symm_apply,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.real_smul]
  have hK (r θ : ℝ) (hr : 0 < r) :
      r • F (e.symm (Complex.polarCoord.symm (r, θ))) = K r θ := by
    rw [hp r θ hr]
    have hcoord : toComplex (r • unitVec (θ : 𝕋)) = (r : ℂ) * fourier 1 (θ : 𝕋) := by
      rw [← he, map_smul, he, toComplex_unitVec, Complex.real_smul]
    have hnorm' : ‖r • unitVec (θ : 𝕋)‖ = r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hnorm, mul_one]
    have hphase :
        -(↑(2 * π * ⟪r • unitVec (θ : 𝕋), ρ • unitVec ψ⟫_ℝ) : ℂ) * I =
          I * (-(2 * π * (r : ℂ))) * (⟪ρ • unitVec ψ, unitVec (θ : 𝕋)⟫_ℝ : ℝ) := by
      rw [real_inner_smul_left, real_inner_comm]
      push_cast
      ring
    dsimp only [K, F, P]
    rw [hnorm', hcoord, hphase, mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne'),
      ← fourier_eq_zpow, Complex.real_smul]
    ring
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let ν := (volume : Measure ℝ).restrict (Ioo (-π) π)
  have hKi : Integrable (Function.uncurry K) (μ.prod ν) := by
    have h₁ : Integrable (fun _ : ℝ => (1 : ℝ)) ν :=
      integrableOn_const (measure_Ioo_lt_top (μ := volume)).ne
    have hmajor : Integrable (fun p : ℝ × ℝ => ‖φ p.1 * p.1‖ * (1 : ℝ)) (μ.prod ν) :=
      hφ.norm.mul_prod h₁
    have hcont : Continuous (fun p : ℝ × ℝ => P p.1 (p.2 : 𝕋)) := by
      have hcoe : Continuous (fun p : ℝ × ℝ => (p.2 : 𝕋)) :=
        (AddCircle.continuous_mk' (2 * π)).comp continuous_snd
      have hunit : Continuous (fun p : ℝ × ℝ => unitVec (p.2 : 𝕋)) := by
        have h := e.symm.continuous.comp ((fourier 1).continuous.comp hcoe)
        convert h using 1
        funext p
        apply e.injective
        simp only [Function.comp_apply, e.apply_symm_apply, he, toComplex_unitVec]
      have hinner : Continuous (fun p : ℝ × ℝ => ⟪ρ • unitVec ψ, unitVec (p.2 : 𝕋)⟫_ℝ) :=
        continuous_const.inner hunit
      have hrad : Continuous (fun p : ℝ × ℝ => -(2 * π * (p.1 : ℂ))) := by fun_prop
      have hi : Continuous (fun _ : ℝ × ℝ => I) := continuous_const
      have hphase := (hi.mul hrad).mul (Complex.continuous_ofReal.comp hinner)
      exact (Complex.continuous_exp.comp hphase).mul ((fourier n).continuous.comp hcoe)
    refine hmajor.mono' (hφ.aestronglyMeasurable.comp_fst.mul hcont.aestronglyMeasurable) ?_
    filter_upwards with p
    have hP : ‖P p.1 (p.2 : 𝕋)‖ = 1 := by
      dsimp only [P]
      rw [norm_mul]
      have hfour : ‖fourier n (p.2 : 𝕋)‖ = 1 := Circle.norm_coe _
      rw [hfour, mul_one, Complex.norm_exp, Complex.mul_re]
      simp [Complex.mul_re, Complex.mul_im]
    change ‖(φ p.1 * p.1) * P p.1 (p.2 : 𝕋)‖ ≤ _
    rw [norm_mul, hP]
  obtain ⟨β, rfl⟩ := QuotientAddGroup.mk_surjective ψ
  have hβ : ρ • unitVec (β : 𝕋) = planePoint ρ β := by
    rw [← hp ρ β hρ]
    apply e.injective
    rw [e.apply_symm_apply, he, Complex.polarCoord_symm_apply, toComplex_def,
      planePoint_apply_zero, planePoint_apply_one]
    push_cast
    ring
  have hmean (r : ℝ) :
      ∫ θ, P r (θ : 𝕋) ∂ν = 2 * π * ((-I) ^ n * fourier n (β : 𝕋) *
        besselJ n (2 * π * ρ * r)) := by
    have h := integral_exp_inner_fourier (-(2 * π * r)) ρ β n
    rw [← hβ] at h
    change (∫ u, P r u ∂haarAddCircle) = _ at h
    rw [AddCircle.integral_haarAddCircle, Complex.real_smul,
      ← AddCircle.intervalIntegral_preimage (2 * π) (-π),
      show -π + 2 * π = π by ring, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo] at h
    have hπ : (2 * π : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    push_cast at h
    have h' : (2 * π : ℂ)⁻¹ * (∫ θ, P r (θ : 𝕋) ∂ν) =
        I ^ n * Complex.exp (n * β * I) * besselJ n (-(2 * π * (r : ℂ)) * ρ) := h
    calc
      _ = (2 * π : ℂ) *
          (I ^ n * Complex.exp (n * β * I) * besselJ n (-(2 * π * (r : ℂ)) * ρ)) :=
        by rw [← h', ← mul_assoc, mul_inv_cancel₀ hπ, one_mul]
      _ = _ := by
        rw [show -(2 * π * (r : ℂ)) * ρ = -(2 * π * ρ * r) by ring, besselJ_int_neg,
          fourier_circle_coe]
        have hpow : I ^ n * (-1 : ℂ) ^ n = (-I) ^ n := by
          rw [← mul_zpow, mul_neg_one]
        linear_combination
          (2 * π * Complex.exp (n * β * I) * besselJ n (2 * π * ρ * r)) * hpow
  have hF : (𝓕 (fun x : E => φ ‖x‖ * (toComplex x / ‖x‖) ^ n) (ρ • unitVec (β : 𝕋))) =
      ∫ x, F x := by
    rw [Real.fourier_eq']
    simp only [F, smul_eq_mul, neg_mul, Complex.ofReal_neg]
  rw [hF, ← e.symm.measurePreserving.integral_comp e.symm.toHomeomorph.measurableEmbedding,
    ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, p.1 • F (e.symm (Complex.polarCoord.symm p))) = _
  have hm : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := measurableSet_Ioi.prod measurableSet_Ioo
  rw [setIntegral_congr_fun hm (g := Function.uncurry K) (fun p hp => hK p.1 p.2 hp.1)]
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, Function.uncurry K p
    ∂((volume : Measure ℝ).prod volume)) = _
  rw [← Measure.prod_restrict, integral_prod _ hKi, hankelTransform_def,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  change (∫ θ, (φ r * r) * P r (θ : 𝕋) ∂ν) = _
  rw [integral_const_mul, hmean]
  push_cast
  ring

/-- Hankel inversion for real `ν > -1` on smooth functions with compact support in `(0, ∞)`
(Vilenkin–Klimyk Vol. 1 §4.4.2, pp. 196–197; Vol. 2 §10.2.6 (3)–(4), pp. 186–187). -/
theorem hankelTransform_hankelTransform {ν : ℝ} (hν : -1 < ν) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ⊤ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 0) {r : ℝ} (hr : 0 < r) :
    hankelTransform ν (hankelTransform ν φ) r = φ r := by
  sorry

/-- Plancherel for the Hankel transform (Vilenkin–Klimyk Vol. 1 §4.4.2, pp. 196–197; Vol. 2
§10.2.6 (5), pp. 186–187). -/
theorem lintegral_hankelTransform {ν : ℝ} (hν : -1 < ν) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ⊤ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 0) :
    ∫⁻ R in Ioi (0 : ℝ), ‖hankelTransform ν φ R‖ₑ ^ 2 * ENNReal.ofReal R =
      ∫⁻ r in Ioi (0 : ℝ), ‖φ r‖ₑ ^ 2 * ENNReal.ofReal r := by
  sorry

/-- Laguerre functions are eigenfunctions of the Hankel transform (Vilenkin–Klimyk Vol. 2
§10.2.6 (16), p. 188), with lean-DLMF's Laguerre polynomials:
`H_ν(x^ν e^{-x²/2} L_k^ν(x²))(λ) = (-1)^k λ^ν e^{-λ²/2} L_k^ν(λ²)`. -/
theorem hankelTransform_laguerre {ν : ℝ} (hν : -1 < ν) (k : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    hankelTransform ν
        (fun x => ((x ^ ν * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) *
          DLMF.OrthogonalPolynomials.laguerrePolynomialL ν k ((x ^ 2 : ℝ) : ℂ)) lam =
      (-1) ^ k * ((lam ^ ν * Real.exp (-lam ^ 2 / 2) : ℝ) : ℂ) *
        DLMF.OrthogonalPolynomials.laguerrePolynomialL ν k ((lam ^ 2 : ℝ) : ℂ) := by
  let f (t : ℝ) : ℂ :=
    (t : ℂ) ^ (ν / 2 : ℂ) * besselJ ν (Real.sqrt (lam ^ 2 * t)) *
      exp (-(t : ℂ) / 2) * DLMF.OrthogonalPolynomials.laguerreExtended ν k t
  have hreg : ∀ j : ℕ, (ν : ℂ) + 1 ≠ -j := by
    intro j h
    have hj := congrArg Complex.re h
    simp at hj
    have hj' : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have h := (DLMF.OrthogonalPolynomials.integral_laguerreExtended_hankel hν k
    (x := lam ^ 2) (sq_pos_of_pos hlam)).2
  change (∫ t in Ioi 0, f t) = _ at h
  rw [← integral_comp_rpow_Ioi_of_pos (g := f) (p := (2 : ℝ)) (by norm_num)] at h
  have hp (t : ℝ) (ht : 0 ≤ t) : ((t ^ 2 : ℝ) : ℂ) ^ (ν / 2 : ℂ) = ((t ^ ν : ℝ) : ℂ) := by
    rw [show (ν : ℂ) / 2 = ((ν / 2 : ℝ) : ℂ) by norm_cast,
      ← Complex.ofReal_cpow (sq_nonneg t), ← Real.rpow_two t, ← Real.rpow_mul ht]
    congr 2
    ring
  have hsqrt (t : ℝ) (ht : 0 ≤ t) : Real.sqrt (lam ^ 2 * t ^ 2) = lam * t := by
    rw [← mul_pow, Real.sqrt_sq (mul_nonneg hlam.le ht)]
  have hre (t : ℝ) :
      exp (-((t ^ 2 : ℝ) : ℂ) / 2) = (Real.exp (-(t ^ 2) / 2) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]
  rw [hankelTransform_def]
  have hchange :
      (∫ x in Ioi (0 : ℝ), (2 * x ^ ((2 : ℝ) - 1)) • f (x ^ (2 : ℝ))) =
      2 * ∫ x in Ioi (0 : ℝ), ((x ^ ν * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) *
        besselJ ν (lam * x) * x *
        DLMF.OrthogonalPolynomials.laguerrePolynomialL ν k ((x ^ 2 : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hnon : 0 ≤ t := (mem_Ioi.mp ht).le
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two]
    dsimp only [f]
    rw [hp t hnon, hsqrt t hnon, hre, DLMF.OrthogonalPolynomials.laguerreExtended_eq hreg]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring
  rw [hchange, hp lam hlam.le, hre, DLMF.OrthogonalPolynomials.laguerreExtended_eq hreg] at h
  have hinter :
      (∫ x in Ioi (0 : ℝ), ((x ^ ν * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) *
        DLMF.OrthogonalPolynomials.laguerrePolynomialL ν k ((x ^ 2 : ℝ) : ℂ) *
        besselJ ν (lam * x) * x) =
      ∫ x in Ioi (0 : ℝ), ((x ^ ν * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) *
        besselJ ν (lam * x) * x *
        DLMF.OrthogonalPolynomials.laguerrePolynomialL ν k ((x ^ 2 : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  rw [hinter]
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  convert h using 1
  push_cast
  ring

/-- Fourier transform of a radial function on `ℝⁿ` (Vilenkin–Klimyk Vol. 2 §10.2.6 (1)–(2),
p. 186): `𝓕f(ξ) = 2π |ξ|^{1-n/2} ∫₀^∞ φ(r) J_{n/2-1}(2π|ξ| r) r^{n/2} dr` for `f(x) = φ(|x|)`,
`ξ ≠ 0`. -/
theorem fourier_radial {n : ℕ} (hn : 1 ≤ n) (φ : ℝ → ℂ)
    (hφ : IntegrableOn (fun r => φ r * r ^ (n - 1)) (Ioi 0)) {ξ : EuclideanSpace ℝ (Fin n)}
    (hξ : ξ ≠ 0) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin n) => φ ‖x‖) ξ =
      2 * π * ((‖ξ‖ ^ (1 - (n : ℝ) / 2) : ℝ) : ℂ) *
        ∫ r in Ioi (0 : ℝ), φ r * besselJ ((n : ℂ) / 2 - 1) (2 * π * ‖ξ‖ * r) *
          ((r ^ ((n : ℝ) / 2) : ℝ) : ℂ) := by
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  let c : ℝ := (n : ℝ) / 2
  let q : ℝ := ‖ξ‖
  let σ := (volume : Measure E).toSphere
  have hdim : Module.finrank ℝ E = n := by simp [E]
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank ℝ E by omega)
  have hc : 0 < c := div_pos (by exact_mod_cast (by omega : 0 < n)) two_pos
  have hq : 0 < q := norm_pos_iff.mpr hξ
  have hφ' : Integrable (fun x : E => φ ‖x‖) := by
    rw [integrable_fun_norm_addHaar, hdim]
    simpa only [Complex.real_smul, Complex.ofReal_pow, mul_comm] using hφ
  let F (x : E) := Complex.exp (-(2 * π * ⟪x, ξ⟫_ℝ : ℝ) * I) * φ ‖x‖
  have hF : Integrable F := by
    refine hφ'.norm.mono' ((by
      fun_prop : AEStronglyMeasurable (fun x : E => Complex.exp (-(2 * π * ⟪x, ξ⟫_ℝ : ℝ) * I))
        volume).mul hφ'.aestronglyMeasurable) ?_
    filter_upwards with x
    have he : ‖Complex.exp (-(2 * π * ⟪x, ξ⟫_ℝ : ℝ) * I)‖ = 1 := by
      simp [Complex.norm_exp, Complex.mul_re]
    simp only [F, norm_mul, he, one_mul, le_rfl]
  have hσ : (σ univ).toReal = 2 * π ^ c / Real.Gamma c := by
    dsimp only [σ]
    rw [TauCeti.toSphere_volume_apply_univ, hdim, ENNReal.toReal_ofReal (by positivity)]
  have hΓ : Real.Gamma c ≠ 0 := (Real.Gamma_pos_of_pos hc).ne'
  have hcoef (r : ℝ) (hr : 0 < r) :
      r ^ (n - 1) * (σ univ).toReal *
        (Real.Gamma c * (2 / (2 * π * q * r)) ^ (c - 1)) =
      2 * π * q ^ (1 - c) * r ^ c := by
    rw [hσ]
    have he : (2 : ℝ) / (2 * π * q * r) = (π * q * r)⁻¹ := by
      field_simp [Real.pi_ne_zero, hq.ne', hr.ne']
    rw [he, Real.inv_rpow (by positivity), Real.mul_rpow (by positivity : 0 ≤ π * q) hr.le,
      Real.mul_rpow Real.pi_pos.le hq.le, mul_inv_rev, mul_inv_rev]
    have hp : π ^ c * (π ^ (c - 1))⁻¹ = π := by
      rw [← div_eq_mul_inv, ← Real.rpow_sub Real.pi_pos, show c - (c - 1) = 1 by ring,
        Real.rpow_one]
    have hq' : (q ^ (c - 1))⁻¹ = q ^ (1 - c) := by
      rw [← Real.rpow_neg hq.le, neg_sub]
    have hr' : r ^ (n - 1) * (r ^ (c - 1))⁻¹ = r ^ c := by
      rw [← Real.rpow_natCast, ← div_eq_mul_inv, ← Real.rpow_sub hr,
        Nat.cast_sub hn, Nat.cast_one]
      congr 1
      dsimp [c]
      ring
    calc
      _ = 2 * (π ^ c * (π ^ (c - 1))⁻¹) * (q ^ (c - 1))⁻¹ *
          (r ^ (n - 1) * (r ^ (c - 1))⁻¹) := by field_simp [hΓ]
      _ = _ := by rw [hp, hq', hr']
  have hfourier : 𝓕 (fun x : E => φ ‖x‖) ξ = ∫ x, F x := by
    rw [Real.fourier_eq']
    simp only [F, smul_eq_mul, neg_mul, Complex.ofReal_neg]
  have havg (r : ℝ) (hr : 0 < r) :
      ∫ u : S, F (r • (u : E)) ∂σ =
        (σ univ).toReal * besselZonal n (2 * π) (q * r) * φ r := by
    let k (u : S) := Complex.exp (I * (2 * π) * (⟪-(r • ξ), (u : E)⟫_ℝ : ℝ))
    have hnorm : ‖-(r • ξ)‖ = q * r := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_comm]
    have h := besselZonal_eq_integral_sphere hn (2 * π) (-(r • ξ))
    rw [hnorm] at h
    change besselZonal n (2 * π) (q * r) = ((σ univ).toReal⁻¹ : ℝ) * ∫ u, k u ∂σ at h
    have hzero : (((σ univ).toReal : ℝ) : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      rw [hσ]
      positivity
    calc
      _ = ∫ u : S, k u * φ r ∂σ := by
        apply integral_congr_ae
        filter_upwards with u
        have hu : ‖(u : E)‖ = 1 := by
          simpa only [Metric.mem_sphere, dist_zero_right] using u.property
        dsimp only [F, k]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one,
          real_inner_smul_left, inner_neg_left, real_inner_smul_left, real_inner_comm (u : E) ξ]
        congr 2
        push_cast
        ring
      _ = _ := by
        rw [integral_mul_const, h, ← mul_assoc ((σ univ).toReal : ℂ),
          Complex.ofReal_inv, mul_inv_cancel₀ hzero, one_mul]
  rw [hfourier, TauCeti.integral_eq_integral_Ioi_integral_toSphere F hF, hdim,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : 0 < r := mem_Ioi.mp hr
  have hp : 0 < 2 * π := Real.two_pi_pos
  have hslit : (2 * π : ℂ) ∈ slitPlane := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul]
    exact Complex.ofReal_mem_slitPlane.mpr hp
  rw [havg r hr', besselZonal_eq_besselJ hn hslit (mul_pos hq hr'), Complex.real_smul]
  have harg : 2 / ((2 * π : ℂ) * ((q * r : ℝ) : ℂ)) =
      ((2 / (2 * π * q * r) : ℝ) : ℂ) := by push_cast; ring
  have horder : ((n : ℂ) / 2 - 1) = ((c - 1 : ℝ) : ℂ) := by simp [c]
  have hgamma : Complex.Gamma ((n : ℂ) / 2) = (Real.Gamma c : ℂ) := by
    rw [← Complex.Gamma_ofReal]
    simp [c]
  rw [harg, horder, ← Complex.ofReal_cpow (by positivity), hgamma]
  have hcast := congrArg Complex.ofReal (hcoef r hr')
  push_cast at hcast
  change _ = (2 * π * (q ^ (1 - c) : ℝ) : ℂ) *
    (φ r * besselJ (↑(c - 1)) (2 * π * q * r) * (r ^ c : ℝ))
  have harg' : (2 * π : ℂ) * ((q * r : ℝ) : ℂ) = 2 * π * q * r := by push_cast; ring
  rw [harg', Complex.ofReal_pow]
  linear_combination (φ r * besselJ (↑(c - 1)) (2 * π * q * r)) * hcast

end SFVK.MotionGroups
