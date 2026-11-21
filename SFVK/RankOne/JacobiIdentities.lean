/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.RelatedFunctions
public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import SFVK.RankOne.Basic.Jacobi
public import SFVK.SU11.Basic.BoostMatrixElements
import DLMF.Hypergeometric.ParameterHolomorphy
import DLMF.Hypergeometric.Basic.GaussSeries
import DLMF.Hypergeometric.ArgumentContinuation
import DLMF.Hypergeometric.Boundary
import DLMF.Hypergeometric.PrincipalConnections
import DLMF.Hypergeometric.Elementary.AlgebraicValues
import DLMF.Hypergeometric.FurtherTransformations.Quadratic
import SFVK.SU11.MatrixElements
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Real.Sqrt
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import SFVKMathlib.Analysis.Complex.GaussCutPlane

/-!
# Identities and differential equation for Jacobi functions

The radius `t` is real and `α`, `β`, and `λ` may be complex. With `ρ = α + β + 1`,
the Jacobi function is `Γ(α + 1) 𝐅((ρ + iλ)/2, (ρ − iλ)/2; α + 1; −sinh² t)`,
in lean-DLMF's principal-branch normalization (DLMF 15.9.11). The main results give
the value at the origin, radial evenness, the Jacobi equation, uniqueness, elementary
and terminating cases, and the quadratic transformation.
The elementary cases use Tau Ceti's `ofReal_exp_cpow` for the principal power of a real
exponential.
-/

public noncomputable section

open Complex Filter Topology Set MeasureTheory DLMF.Hypergeometric DLMF.Legendre
open scoped ContDiff InnerProductSpace Real

namespace SFVK.RankOne

/-- **Value at the origin**: `φ_λ(0) = 1` for `α + 1 ∉ {0, −1, …}`. -/
theorem jacobiFunction_zero (α β lam : ℂ) (hα : ∀ k : ℕ, α + 1 ≠ -k) :
    jacobiFunction α β lam 0 = 1 := by
  rw [jacobiFunction, Complex.sinh_zero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero]
  rw [regularizedGaussHypergeometric_zero, mul_inv_cancel₀ (Gamma_ne_zero hα)]

/-- **Evenness in the radius**: `φ_λ(−t) = φ_λ(t)`. -/
theorem jacobiFunction_even (α β lam : ℂ) (t : ℝ) :
    jacobiFunction α β lam ((-t : ℝ) : ℂ) = jacobiFunction α β lam t := by
  simp [jacobiFunction, Complex.sinh_neg]

/-- **Evenness in the spectral parameter**: `φ_{−λ} = φ_λ`. -/
theorem jacobiFunction_neg_spectral (α β lam : ℂ) (t : ℝ) :
    jacobiFunction α β (-lam) t = jacobiFunction α β lam t := by
  simp only [jacobiFunction, mul_neg, sub_neg_eq_add, ← sub_eq_add_neg]
  rw [regularizedGaussHypergeometric_symm _ _ _ (Complex.neg_sinh_sq_mem_gaussCutPlane t)]

/-- **The trivial spherical function**: `φ_{iρ} ≡ 1`. -/
theorem jacobiFunction_I_mul_rho (α β : ℂ) (hα : ∀ k : ℕ, α + 1 ≠ -k) (t : ℝ) :
    jacobiFunction α β (I * (α + β + 1)) t = 1 := by
  have h : (α + β + 1 + I * (I * (α + β + 1))) / 2 = 0 := by
    rw [← mul_assoc, I_mul_I]; ring
  rw [jacobiFunction, h,
    regularizedGaussHypergeometric_zero_left _ _ (Complex.neg_sinh_sq_mem_gaussCutPlane t),
    mul_inv_cancel₀ (Gamma_ne_zero hα)]

/-- **Holomorphy in the spectral parameter.** -/
theorem differentiable_jacobiFunction (α β : ℂ) (t : ℝ) :
    Differentiable ℂ fun lam => jacobiFunction α β lam t := by
  simp only [jacobiFunction]
  exact (differentiable_regularizedGaussHypergeometric_comp
    (A := fun lam => (α + β + 1 + I * lam) / 2)
    (B := fun lam => (α + β + 1 - I * lam) / 2) (C := fun _ => α + 1)
    (by fun_prop) (by fun_prop) (by fun_prop) (Complex.neg_sinh_sq_mem_gaussCutPlane t)).const_mul _

namespace Jacobi

/-- The derivative of the Gauss argument in Jacobi coordinates. -/
private theorem hasDerivAt_neg_sinh_sq (t : ℂ) :
    HasDerivAt (fun z : ℂ => -(Complex.sinh z) ^ 2) (-2 * Complex.sinh t * Complex.cosh t) t := by
  exact ((Complex.hasDerivAt_sinh t).pow 2).neg.congr_deriv (by ring)

/-- The derivative of the continued Gauss function along the Jacobi radius. -/
private theorem hasDerivAt_gauss_neg_sinh_sq (a b c : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => regularizedGaussHypergeometric a b c (-(Complex.sinh s) ^ 2))
      ((a * b * regularizedGaussHypergeometric (a + 1) (b + 1) (c + 1)
        (-(Complex.sinh t) ^ 2)) * (-2 * Complex.sinh t * Complex.cosh t)) t := by
  have hz := Complex.neg_sinh_sq_mem_gaussCutPlane t
  have h := (differentiableAt_regularizedGaussHypergeometric a b c hz).hasDerivAt
  rw [deriv_regularizedGaussHypergeometric a b c hz] at h
  exact (h.comp (t : ℂ) (hasDerivAt_neg_sinh_sq t)).comp_ofReal

/-- The second derivative of the Gauss argument in Jacobi coordinates. -/
private theorem hasDerivAt_neg_two_sinh_mul_cosh (t : ℝ) :
    HasDerivAt (fun s : ℝ => -2 * Complex.sinh s * Complex.cosh s)
      (-2 * (Complex.cosh t ^ 2 + Complex.sinh t ^ 2)) t := by
  exact ((((Complex.hasDerivAt_sinh t).const_mul (-2)).mul
    (Complex.hasDerivAt_cosh t)).comp_ofReal).congr_deriv (by ring)

end Jacobi

set_option maxHeartbeats 550000 in
/-- **The Jacobi equation**: `L φ_λ = −(λ² + ρ²) φ_λ` on `t > 0`. -/
theorem jacobiOperator_jacobiFunction (α β lam : ℂ) {t : ℝ}
    (ht : 0 < t) :
    jacobiOperator α β (fun s : ℝ => jacobiFunction α β lam s) t =
      -(lam ^ 2 + (α + β + 1) ^ 2) * jacobiFunction α β lam t := by
  -- The Gauss equation also gives the zero equation at exceptional lower parameters.
  let a := (α + β + 1 + I * lam) / 2
  let b := (α + β + 1 - I * lam) / 2
  let c := α + 1
  let z (s : ℝ) := -(Complex.sinh s) ^ 2
  let zPrime (s : ℝ) := -2 * Complex.sinh s * Complex.cosh s
  let zSecond (s : ℝ) := -2 * (Complex.cosh s ^ 2 + Complex.sinh s ^ 2)
  let g (s : ℝ) := regularizedGaussHypergeometric a b c (z s)
  let gPrime (s : ℝ) := a * b *
    regularizedGaussHypergeometric (a + 1) (b + 1) (c + 1) (z s)
  let gSecond (s : ℝ) := pochhammer a 2 * pochhammer b 2 *
    regularizedGaussHypergeometric (a + 2) (b + 2) (c + 2) (z s)
  have hg (s : ℝ) : HasDerivAt g (gPrime s * zPrime s) s :=
    Jacobi.hasDerivAt_gauss_neg_sinh_sq a b c s
  have hg' : HasDerivAt gPrime (gSecond t * zPrime t) t := by
    have hd := (Jacobi.hasDerivAt_gauss_neg_sinh_sq (a + 1) (b + 1) (c + 1) t).const_mul (a * b)
    convert hd using 1
    dsimp only [gSecond, z, zPrime]
    simp only [pochhammer_succ, pochhammer_zero, Nat.cast_one, Nat.cast_zero,
      add_zero, one_mul]
    ring_nf
  have hJacobi : (fun s : ℝ => jacobiFunction α β lam s) = fun s => Gamma c * g s := rfl
  have hDeriv : deriv (fun s : ℝ => jacobiFunction α β lam s) = fun s =>
      Gamma c * (gPrime s * zPrime s) := by
    funext s
    rw [hJacobi]
    exact ((hg s).const_mul (Gamma c)).deriv
  have hDeriv₂ : deriv (deriv (fun s : ℝ => jacobiFunction α β lam s)) t =
      Gamma c * ((gSecond t * zPrime t) * zPrime t + gPrime t * zSecond t) := by
    rw [hDeriv]
    exact ((hg'.mul (Jacobi.hasDerivAt_neg_two_sinh_mul_cosh t)).const_mul (Gamma c)).deriv
  have hs : Complex.sinh t ≠ 0 := by
    rw [← Complex.ofReal_sinh]
    exact Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr ht).ne'
  have hc : Complex.cosh t ≠ 0 := by
    rw [← Complex.ofReal_cosh]
    exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
  have hsq : zPrime t ^ 2 = -4 * (z t * (1 - z t)) := by
    dsimp only [zPrime, z]
    linear_combination 4 * Complex.sinh t ^ 2 * (Complex.cosh_sq_sub_sinh_sq (t : ℂ))
  let coeff := (2 * α + 1) * (Real.cosh t / Real.sinh t : ℝ) +
    (2 * β + 1) * (Real.tanh t : ℂ)
  have hlinear : zSecond t + coeff * zPrime t = -4 * (c - (a + b + 1) * z t) := by
    dsimp only [zSecond, coeff, zPrime, c, a, b, z]
    rw [Real.tanh_eq_sinh_div_cosh, Complex.ofReal_div, Complex.ofReal_div,
      Complex.ofReal_sinh, Complex.ofReal_cosh]
    have hcosh : (Complex.cosh t / Complex.sinh t) *
        (-2 * Complex.sinh t * Complex.cosh t) = -2 * Complex.cosh t ^ 2 := by
      field_simp [hs]
    have hsinh : (Complex.sinh t / Complex.cosh t) *
        (-2 * Complex.sinh t * Complex.cosh t) = -2 * Complex.sinh t ^ 2 := by
      field_simp [hc]
    rw [add_mul, mul_assoc (2 * α + 1), hcosh, mul_assoc (2 * β + 1), hsinh]
    linear_combination (-(4 * α + 4)) * (Complex.cosh_sq_sub_sinh_sq (t : ℂ))
  have hEigenvalue : lam ^ 2 + (α + β + 1) ^ 2 = 4 * a * b := by
    dsimp only [a, b]
    linear_combination lam ^ 2 * Complex.I_sq
  have hGauss : z t * (1 - z t) * gSecond t +
      (c - (a + b + 1) * z t) * gPrime t - (a * b) * g t = 0 :=
    regularizedGaussHypergeometric_ode a b c (Complex.neg_sinh_sq_mem_gaussCutPlane t)
  rw [jacobiOperator_def, hDeriv₂, hDeriv, congrFun hJacobi t, hEigenvalue]
  calc
    _ = Gamma c * (zPrime t ^ 2 * gSecond t + (zSecond t + coeff * zPrime t) * gPrime t) := by
      dsimp only [coeff]
      ring
    _ = _ := by
      rw [hsq, hlinear]
      linear_combination -(4 * Gamma c) * hGauss

/-- **Uniqueness**: for `0 ≤ Re α`, a solution of the Jacobi equation on `(0, ∞)` that is
continuous on `[0, ∞)` with value `1` at `0` is `φ_λ`. -/
theorem eq_jacobiFunction_of_jacobiOperator (α β lam : ℂ) (hα : 0 ≤ α.re) (u : ℝ → ℂ)
    (hu : ContDiffOn ℝ 2 u (Ioi 0)) (hc : ContinuousOn u (Ici 0)) (h0 : u 0 = 1)
    (heq : ∀ t > 0, jacobiOperator α β u t = -(lam ^ 2 + (α + β + 1) ^ 2) * u t) :
    ∀ t ≥ 0, u t = jacobiFunction α β lam t := by
  sorry

/-- **The polynomial case**: at `λ = i(2k + ρ)`,
`φ_λ(t) = k! / (α + 1)_k · P_k^{(α,β)}(cosh 2t)` with lean-DLMF's Jacobi polynomial. -/
theorem jacobiFunction_eq_jacobiPolynomialP (α β : ℂ) (hα : ∀ k : ℕ, α + 1 ≠ -k) (k : ℕ)
    (t : ℝ) :
    jacobiFunction α β (I * (2 * k + α + β + 1)) t =
      (k.factorial : ℂ) / (ascPochhammer ℂ k).eval (α + 1) *
        DLMF.OrthogonalPolynomials.jacobiPolynomialP α β k (Real.cosh (2 * t)) := by
  have ha : (α + β + 1 + I * (I * (2 * k + α + β + 1))) / 2 = -(k : ℂ) := by
    rw [← mul_assoc, I_mul_I]
    ring
  have hb : (α + β + 1 - I * (I * (2 * k + α + β + 1))) / 2 = k + α + β + 1 := by
    rw [← mul_assoc, I_mul_I]
    ring
  have harg : (1 - (Real.cosh (2 * t) : ℂ)) / 2 = -(Complex.sinh t) ^ 2 := by
    rw [Real.cosh_two_mul, ofReal_add, ofReal_pow, ofReal_pow, ofReal_cosh, ofReal_sinh]
    linear_combination -(Complex.cosh_sq_sub_sinh_sq t) / 2
  have hterm (b : ℂ) {z : ℂ} (hz : z ∈ cutPlane) :
      ordinaryHypergeometric (-(k : ℂ)) b (α + 1) z =
        Gamma (α + 1) * regularizedGaussHypergeometric (-(k : ℂ)) b (α + 1) z := by
    apply eqOn_cutPlane_of_eqOn_disk
      (f := ordinaryHypergeometric (-(k : ℂ)) b (α + 1))
      (g := fun z => Gamma (α + 1) * regularizedGaussHypergeometric (-(k : ℂ)) b (α + 1) z)
      ?_ ?_ (fun _ hw => ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric hα hw)
      hz
    · rw [funext (ordinaryHypergeometric_eq_sum_neg_nat k b (α + 1))]
      fun_prop
    · exact analyticOnNhd_const.mul (analyticOnNhd_regularizedGaussHypergeometric _ _ _)
  rw [jacobiFunction, ha, hb, ← hterm _ (Complex.neg_sinh_sq_mem_gaussCutPlane t),
    DLMF.OrthogonalPolynomials.jacobiPolynomialP, harg]
  have hp := pochhammer_ne_zero_of_not_neg_nat hα k
  simp only [pochhammer] at hp ⊢
  field_simp [hp, Nat.cast_ne_zero.mpr k.factorial_ne_zero]

/-- The continued Jacobi function is real analytic on the entire real radius line. -/
theorem analyticAt_jacobiFunction_radius (α β lam : ℂ) (t : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => jacobiFunction α β lam s) t := by
  let a := (α + β + 1 + I * lam) / 2
  let b := (α + β + 1 - I * lam) / 2
  let z (w : ℂ) := -(Complex.sinh w) ^ 2
  have hz : AnalyticAt ℂ z t := by dsimp [z]; fun_prop
  have h := (analyticAt_regularizedGaussHypergeometric a b (α + 1)
    (z := z (t : ℂ)) (Complex.neg_sinh_sq_mem_gaussCutPlane t)).comp (f := z) hz
  have hh : AnalyticAt ℂ (jacobiFunction α β lam) t :=
    analyticAt_const.mul h
  exact analyticAt_comp_ofReal hh

namespace Jacobi

/-- Continue a local identity between real analytic functions along the real line. -/
private theorem eq_real_analytic {f g : ℝ → ℂ} (hf : ∀ t, AnalyticAt ℝ f t)
    (hg : ∀ t, AnalyticAt ℝ g t) (h : f =ᶠ[𝓝 (0 : ℝ)] g) (t : ℝ) : f t = g t :=
  AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (fun t _ => hf t) (fun t _ => hg t) isPreconnected_univ (mem_univ _) h (mem_univ t)

/-- The principal square root of the Gauss radicand on the real radial line. -/
private theorem sqrt_one_add_sinh_sq (t : ℝ) :
    (1 + Complex.sinh t ^ 2) ^ (1 / 2 : ℂ) = Complex.cosh t := by
  have hr : Real.sqrt (1 + Real.sinh t ^ 2) = Real.cosh t := by
    rw [← Real.cosh_sq', Real.sqrt_sq (Real.cosh_pos t).le]
  have hz : 1 + Complex.sinh t ^ 2 = ((1 + Real.sinh t ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_sinh]
  have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num [Complex.ofReal_div]
  rw [hz, ← hhalf, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, hr,
    Complex.ofReal_cosh]


/-- A complex power of the exponential of a real number. -/
private theorem cpow_ofReal_exp (t : ℝ) (z : ℂ) : (Complex.exp t) ^ z = Complex.exp (t * z) := by
  rw [← ofReal_exp, TauCeti.ofReal_exp_cpow]

/-- The hypergeometric power series converges on sufficiently small radii. -/
private theorem eventually_norm_sinh_lt_one :
    ∀ᶠ t : ℝ in 𝓝 0, ‖(Complex.sinh t)‖ < 1 := by
  have h : ContinuousAt (fun t : ℝ => ‖Complex.sinh t‖) 0 := by fun_prop
  exact h.eventually_lt continuousAt_const (by norm_num)

end Jacobi

/-- **The Fourier case** `α = β = −1/2`: `φ_λ(t) = cos λt`. -/
theorem jacobiFunction_cos (lam : ℂ) (t : ℝ) :
    jacobiFunction (-1 / 2) (-1 / 2) lam t = Complex.cos (lam * t) := by
  apply Jacobi.eq_real_analytic (fun t => analyticAt_jacobiFunction_radius _ _ _ t)
    (fun t => analyticAt_comp_ofReal (f := fun z => Complex.cos (lam * z)) (by fun_prop))
    ?_ t
  filter_upwards [Jacobi.eventually_norm_sinh_lt_one] with s hs
  have harg : ‖-(Complex.sinh s) ^ 2‖ < 1 := by
    rw [norm_neg, norm_pow]
    nlinarith [norm_nonneg (Complex.sinh s)]
  have hc : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have hre := congrArg Complex.re hk
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) k]
  let a := I * lam / 2
  have hFormula := opposite_parameters_sqrt a hs
  rw [Jacobi.sqrt_one_add_sinh_sq, Complex.cosh_add_sinh, Complex.cosh_sub_sinh,
    Jacobi.cpow_ofReal_exp, ← Complex.ofReal_neg, Jacobi.cpow_ofReal_exp] at hFormula
  have hpos : (s : ℂ) * (2 * a) = lam * s * I := by dsimp [a]; ring
  have hneg : ((-s : ℝ) : ℂ) * (2 * a) = -(lam * s) * I := by
    rw [Complex.ofReal_neg]
    dsimp [a]
    ring
  rw [hpos, hneg, ← Complex.cos] at hFormula
  have hFormula' := hFormula
  rw [ordinaryHypergeometric_symm,
    ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric hc harg] at hFormula'
  have hzero : (-1 / 2 : ℂ) + (-1 / 2) + 1 = 0 := by ring
  have hone : (-1 / 2 : ℂ) + 1 = 1 / 2 := by ring
  rw [jacobiFunction, hzero, hone, zero_add, zero_sub, neg_div]
  exact hFormula'

/-- **The case of `ℍ³`**, `(α, β) = (1/2, −1/2)`: `φ_λ(t) = sin λt / (λ sinh t)`. -/
theorem jacobiFunction_sin (lam : ℂ) (hlam : lam ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    jacobiFunction (1 / 2) (-1 / 2) lam t = Complex.sin (lam * t) / (lam * Real.sinh t) := by
  rw [ofReal_sinh, eq_div_iff (mul_ne_zero hlam (by
    rw [← ofReal_sinh]
    exact ofReal_ne_zero.mpr (Real.sinh_eq_zero.not.mpr ht)))]
  apply Jacobi.eq_real_analytic
    (fun s => (analyticAt_jacobiFunction_radius _ _ _ s).mul
      (analyticAt_comp_ofReal (f := fun w => lam * Complex.sinh w) (by fun_prop)))
    (fun s => analyticAt_comp_ofReal (f := fun w => Complex.sin (lam * w)) (by fun_prop)) ?_ t
  filter_upwards [Jacobi.eventually_norm_sinh_lt_one] with s hs
  have harg : ‖-(Complex.sinh s) ^ 2‖ < 1 := by
    rw [norm_neg, norm_pow]
    nlinarith [norm_nonneg (Complex.sinh s)]
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := by
    intro k hk
    have hre := congrArg Complex.re hk
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) k]
  let a := (1 + I * lam) / 2
  have hFormula := complementary_parameters_odd_sqrt a hs
  rw [ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric hc harg,
    Jacobi.sqrt_one_add_sinh_sq, Complex.cosh_add_sinh, Complex.cosh_sub_sinh,
    Jacobi.cpow_ofReal_exp, ← Complex.ofReal_neg, Jacobi.cpow_ofReal_exp] at hFormula
  have hpos : (s : ℂ) * (1 - 2 * a) = -(lam * s) * I := by dsimp [a]; ring
  have hneg : ((-s : ℝ) : ℂ) * (1 - 2 * a) = lam * s * I := by
    rw [Complex.ofReal_neg]
    dsimp [a]
    ring
  have hb : 1 - a = (1 - I * lam) / 2 := by dsimp [a]; ring
  have hscalar : 2 - 4 * a = -2 * I * lam := by dsimp [a]; ring
  rw [hpos, hneg, hb, hscalar] at hFormula
  have hphi : jacobiFunction (1 / 2) (-1 / 2) lam s = Gamma (3 / 2) *
      regularizedGaussHypergeometric a ((1 - I * lam) / 2) (3 / 2)
        (-(Complex.sinh s) ^ 2) := by
    simp only [jacobiFunction, a, show (1 / 2 : ℂ) + (-1 / 2) + 1 = 1 by ring,
      show (1 / 2 : ℂ) + 1 = 3 / 2 by ring]
  simp only [Pi.mul_apply]
  rw [Complex.sin, hphi]
  linear_combination (I / 2) * hFormula +
    lam * Complex.sinh s *
      (Gamma (3 / 2) * regularizedGaussHypergeometric a ((1 - I * lam) / 2) (3 / 2)
        (-(Complex.sinh s) ^ 2)) * Complex.I_sq

/-- **Quadratic transformation**: `φ_λ^{(α,−1/2)}(t) = φ_{2λ}^{(α,α)}(t/2)`. -/
theorem jacobiFunction_quadratic (α lam : ℂ) (t : ℝ) :
    jacobiFunction α (-1 / 2) lam t = jacobiFunction α α (2 * lam) ((t / 2 : ℝ) : ℂ) := by
  by_cases hα : ∀ k : ℕ, α + 1 ≠ -(k : ℂ)
  · apply Jacobi.eq_real_analytic (fun s => analyticAt_jacobiFunction_radius _ _ _ s)
      (fun s => (analyticAt_jacobiFunction_radius α α (2 * lam) (s / 2)).comp
        (f := fun w : ℝ => w / 2) (by fun_prop)) ?_ t
    have hsmallHalf : ∀ᶠ s : ℝ in 𝓝 0, ‖Complex.sinh (s / 2 : ℝ)‖ < 1 := by
      have h : ContinuousAt (fun t : ℝ => ‖Complex.sinh (t / 2 : ℝ)‖) 0 := by fun_prop
      exact h.eventually_lt continuousAt_const (by norm_num)
    filter_upwards [Jacobi.eventually_norm_sinh_lt_one, hsmallHalf] with s hs hhs
    let a := (α + (-1 / 2 : ℂ) + 1 + I * lam) / 2
    let b := (α + (-1 / 2 : ℂ) + 1 - I * lam) / 2
    let z := -(Complex.sinh (s / 2 : ℝ)) ^ 2
    have hc : a + b + 1 / 2 = α + 1 := by dsimp [a, b]; ring
    have hz : ‖z‖ < 1 := by
      dsimp [z]
      rw [norm_neg, norm_pow]
      nlinarith [norm_nonneg (Complex.sinh (s / 2 : ℝ))]
    have harg : 4 * z * (1 - z) = -(Complex.sinh s) ^ 2 := by
      have hdouble : (2 : ℂ) * ((s / 2 : ℝ) : ℂ) = ↑s := by push_cast; ring
      rw [← hdouble, Complex.sinh_two_mul]
      dsimp [z]
      linear_combination 4 * Complex.sinh (↑(s / 2 : ℝ)) ^ 2 *
        Complex.cosh_sq_sub_sinh_sq (↑(s / 2 : ℝ))
    have hz' : ‖4 * z * (1 - z)‖ < 1 := by
      rw [harg, norm_neg, norm_pow]
      nlinarith [norm_nonneg (Complex.sinh s)]
    have hrez : z.re < 1 / 2 := by
      dsimp [z]
      rw [← Complex.ofReal_sinh, ← Complex.ofReal_pow, Complex.ofReal_re]
      nlinarith [sq_nonneg (Real.sinh (s / 2))]
    have hq := gauss_quadratic (a := a) (b := b) (z := z)
      (fun k => hc ▸ hα k) hz hz' hrez
    rw [hc, ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric hα hz,
      ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric hα hz', harg] at hq
    have ha : (α + α + 1 + I * (2 * lam)) / 2 = 2 * a := by dsimp [a]; ring
    have hb : (α + α + 1 - I * (2 * lam)) / 2 = 2 * b := by dsimp [b]; ring
    simp only [jacobiFunction, ha, hb]
    exact hq.symm
  · push Not at hα
    obtain ⟨k, hk⟩ := hα
    simp only [jacobiFunction, hk, Complex.Gamma_neg_nat_eq_zero, zero_mul]

/-- **The `SU(1, 1)` case**: `φ_λ^{(0,0)}(t) = 𝔓^{−1/2+iλ/2}_{00}(cosh 2t)`, the zonal matrix
element of SpecialFunctionsSU11MatrixElements (its §1.3). -/
theorem jacobiFunction_zero_zero_eq_boostMatrixElement (lam : ℂ) (t : ℝ) :
    jacobiFunction 0 0 lam t = SU11.boostMatrixElement (-1 / 2 + I * lam / 2) 0 0 (2 * t) := by
  rw [SU11.boostMatrixElement_zero_zero_eq_legendreP, jacobiFunction, legendreP]
  have ha : -(-1 / 2 + I * lam / 2) = (1 - I * lam) / 2 := by ring
  have hb : -1 / 2 + I * lam / 2 + 1 = (1 + I * lam) / 2 := by ring
  have hz : (1 - (Real.cosh (2 * t) : ℂ)) / 2 = -(Complex.sinh t) ^ 2 := by
    rw [Real.cosh_two_mul, ofReal_add, ofReal_pow, ofReal_pow, ofReal_cosh, ofReal_sinh]
    linear_combination -(Complex.cosh_sq_sub_sinh_sq t) / 2
  simp only [zero_add, Gamma_one, one_mul, ha, hb, hz]
  exact regularizedGaussHypergeometric_symm _ _ _ (Complex.neg_sinh_sq_mem_gaussCutPlane t)

end SFVK.RankOne
