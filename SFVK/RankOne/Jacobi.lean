/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.RelatedFunctions
public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import SFVK.RankOne.HarishChandra
public import SFVK.SU11.Basic.MatrixElementsBasic
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

/-!
# Jacobi functions

The Jacobi function `φ_λ^{(α,β)}(t) = F((ρ + iλ)/2, (ρ − iλ)/2; α + 1; −sinh² t)`,
`ρ = α + β + 1`, is lean-DLMF's `DLMF.Legendre.jacobiFunction α β λ t`, written there as
`Γ(α + 1) 𝐅(…)` with the principal-branch regularized Gauss function (DLMF 15.9.11), and used
here at real `t`. This file states its theory as a function of the radius: the value at the
origin, evenness, the Jacobi equation, uniqueness, the polynomial and elementary cases, the
quadratic transformation, the Harish-Chandra series `Φ_λ` and the connection formula with the
`c`-function, the asymptotics, the bounds, and Koornwinder's Laplace-type representation and
product formula.

Sources: DLMF 15.9.11–15.9.14; Klimyk–Vilenkin, *Representations of Lie Groups and Special
Functions* (Kirillov (ed.), EMS 59), Part II Ch. 5 §2.4, (12)–(14), p. 233; Vilenkin–Klimyk,
*Representation of Lie Groups and Special Functions*, Vol. 2, §11.4.6, (4)–(10), pp. 348–350;
Wawrzyńczyk, *Group Representations and Special Functions*, §18.5, (18.5.1)–(18.5.2),
pp. 627–628. lean-DLMF supplies `DLMF.Legendre.jacobiFunction` and the regularized Gauss
function.

## Main results

* `SFVK.RankOne.jacobiFunction_zero`, `SFVK.RankOne.jacobiFunction_even`,
  `SFVK.RankOne.jacobiFunction_neg`, `SFVK.RankOne.jacobiFunction_I_mul_rho`.
* `SFVK.RankOne.differentiable_jacobiFunction`: holomorphy in the spectral parameter.
* `SFVK.RankOne.jacobiOperator_jacobiFunction`: the Jacobi equation.
* `SFVK.RankOne.jacobiFunction_eq_jacobiPolynomialP`: the terminating polynomial case.
-/

public noncomputable section

open Complex Filter Topology Set MeasureTheory DLMF.Hypergeometric DLMF.Legendre
open scoped ContDiff InnerProductSpace Real

namespace SFVK.RankOne

/-- `−sinh² t` lies in the cut plane of the Gauss function for every real `t`. -/
theorem neg_sinh_sq_mem_cutPlane (t : ℝ) : -(Complex.sinh t) ^ 2 ∈ cutPlane := by
  rw [mem_cutPlane]
  have h : 1 - -(Complex.sinh t) ^ 2 = ((1 + Real.sinh t ^ 2 : ℝ) : ℂ) := by
    push_cast [← Complex.ofReal_sinh]
    ring
  rw [h, ofReal_mem_slitPlane]
  positivity

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
theorem jacobiFunction_neg (α β lam : ℂ) (t : ℝ) :
    jacobiFunction α β (-lam) t = jacobiFunction α β lam t := by
  simp only [jacobiFunction, mul_neg, sub_neg_eq_add, ← sub_eq_add_neg]
  rw [regularizedGaussHypergeometric_symm _ _ _ (neg_sinh_sq_mem_cutPlane t)]

/-- **The trivial spherical function**: `φ_{iρ} ≡ 1`. -/
theorem jacobiFunction_I_mul_rho (α β : ℂ) (hα : ∀ k : ℕ, α + 1 ≠ -k) (t : ℝ) :
    jacobiFunction α β (I * (α + β + 1)) t = 1 := by
  have h : (α + β + 1 + I * (I * (α + β + 1))) / 2 = 0 := by
    rw [← mul_assoc, I_mul_I]; ring
  rw [jacobiFunction, h, regularizedGaussHypergeometric_zero_left _ _ (neg_sinh_sq_mem_cutPlane t),
    mul_inv_cancel₀ (Gamma_ne_zero hα)]

/-- **Holomorphy in the spectral parameter.** -/
theorem differentiable_jacobiFunction (α β : ℂ) (t : ℝ) :
    Differentiable ℂ fun lam => jacobiFunction α β lam t := by
  simp only [jacobiFunction]
  exact (differentiable_regularizedGaussHypergeometric_comp
    (A := fun lam => (α + β + 1 + I * lam) / 2)
    (B := fun lam => (α + β + 1 - I * lam) / 2) (C := fun _ => α + 1)
    (by fun_prop) (by fun_prop) (by fun_prop) (neg_sinh_sq_mem_cutPlane t)).const_mul _

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
  have hz := neg_sinh_sq_mem_cutPlane t
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
set_option linter.unusedVariables false in
/-- **The Jacobi equation**: `L φ_λ = −(λ² + ρ²) φ_λ` on `t > 0`. -/
theorem jacobiOperator_jacobiFunction (α β lam : ℂ) (hα : ∀ k : ℕ, α + 1 ≠ -k) {t : ℝ}
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
    regularizedGaussHypergeometric_ode a b c (neg_sinh_sq_mem_cutPlane t)
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
  rw [jacobiFunction, ha, hb, ← hterm _ (neg_sinh_sq_mem_cutPlane t),
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
    (z := z (t : ℂ)) (neg_sinh_sq_mem_cutPlane t)).comp (f := z) hz
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
  rw [← ofReal_exp, ofReal_cpow_eq_exp (Real.exp_pos t), Real.log_exp]

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
  exact regularizedGaussHypergeometric_symm _ _ _ (neg_sinh_sq_mem_cutPlane t)

namespace Jacobi

/-- Exponential decay of the doubled radius. -/
private theorem tendsto_exp_neg_double :
    Tendsto (fun t : ℝ => Real.exp (-(2 * t))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))

/-- Factor out the increasing exponential from the decaying one. -/
private theorem exp_neg_eq_mul_exp_neg_double (t : ℝ) :
    Real.exp (-t) = Real.exp t * Real.exp (-(2 * t)) := by
  rw [← Real.exp_add, show t + -(2 * t) = -t by ring]

/-- At infinity the exponential is asymptotic to twice the hyperbolic cosine. -/
private theorem tendsto_exp_div_cosh :
    Tendsto (fun t : ℝ => Real.exp t / Real.cosh t) atTop (𝓝 2) := by
  have h := (tendsto_const_nhds (x := (2 : ℝ))).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_exp_neg_double) (by norm_num)
  rw [add_zero, div_one] at h
  refine h.congr fun t => ?_
  simp only [Pi.div_apply]
  rw [Real.cosh_eq, exp_neg_eq_mul_exp_neg_double t]
  have hp : Real.exp t + Real.exp t * Real.exp (-(2 * t)) ≠ 0 := by positivity
  field_simp [hp, show 1 + Real.exp (-(2 * t)) ≠ 0 by positivity]

/-- The squared hyperbolic tangent approaches one from below. -/
private theorem tendsto_tanh_sq :
    Tendsto (fun t : ℝ => Real.tanh t ^ 2) atTop (𝓝[<] 1) := by
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_exp_neg_double).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add tendsto_exp_neg_double) (by norm_num)
  rw [sub_zero, add_zero, div_one] at h
  have htanh : Tendsto Real.tanh atTop (𝓝 1) := h.congr fun t => by
    simp only [Pi.div_apply]
    rw [Real.tanh_eq, exp_neg_eq_mul_exp_neg_double t]
    have hp : Real.exp t + Real.exp t * Real.exp (-(2 * t)) ≠ 0 := by positivity
    field_simp [hp, show 1 + Real.exp (-(2 * t)) ≠ 0 by positivity]
  exact tendsto_nhdsWithin_iff.mpr
    ⟨by simpa only [one_pow] using htanh.pow 2, Eventually.of_forall Real.tanh_sq_lt_one⟩

/-- Combine a power of a positive radius with the exponential. -/
private theorem ofReal_cpow_mul_exp_eq_div_cpow (r : ℝ) (hr : 0 < r) (t : ℝ) (w : ℂ) :
    (r : ℂ) ^ (-w) * Complex.exp (w * t) =
      ((Real.exp t / r : ℝ) : ℂ) ^ w := by
  rw [ofReal_cpow_eq_exp hr, ofReal_cpow_eq_exp (div_pos (Real.exp_pos _) hr),
    Real.log_div (Real.exp_ne_zero _) hr.ne', Real.log_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The squared hyperbolic cosine doubles the complex exponent. -/
private theorem ofReal_cosh_sq_cpow (t : ℝ) (w : ℂ) :
    ((Real.cosh t ^ 2 : ℝ) : ℂ) ^ w = (Real.cosh t : ℂ) ^ (2 * w) := by
  rw [ofReal_cpow_eq_exp (by positivity : 0 < Real.cosh t ^ 2),
    ofReal_cpow_eq_exp (Real.cosh_pos t), Real.log_pow]
  push_cast
  ring_nf

/-- The normalizing powers of two cancel in the Harish-Chandra term. -/
private theorem two_cpow_mul_cosh (t : ℝ) (w : ℂ) :
    (2 : ℂ) ^ (-w) * ((2 * Real.cosh t : ℝ) : ℂ) ^ w = (Real.cosh t : ℂ) ^ w := by
  have htwo : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_cast
  rw [htwo, ofReal_cpow_eq_exp (by norm_num : (0 : ℝ) < 2),
    ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp (Real.cosh_pos t),
    Real.log_mul (by norm_num) (Real.cosh_pos t).ne', ← exp_add]
  congr 1
  push_cast
  ring

/-- A product of the connection coefficient and a Harish-Chandra term,
in the hypergeometric normalization. -/
private theorem cFunction_mul_harishChandraSeries (α β lam : ℂ) (t : ℝ) :
    cFunction α β lam * harishChandraSeries α β lam t =
      (Real.cosh t : ℂ) ^ (I * lam - (α + β + 1)) * Gamma (α + 1) *
        ((Gamma (I * lam) * Gamma (1 - I * lam)) *
          regularizedGaussHypergeometric ((α + β + 1 - I * lam) / 2) ((α - β + 1 - I * lam) / 2)
            (1 - I * lam) ((Real.cosh t : ℂ) ^ 2)⁻¹ /
          (Gamma ((α + β + 1 + I * lam) / 2) * Gamma ((α - β + 1 + I * lam) / 2))) := by
  rw [cFunction_def, harishChandraSeries_def]
  have h1 : (I * lam + (α + β + 1)) / 2 = (α + β + 1 + I * lam) / 2 := by ring
  have h2 : (I * lam + α - β + 1) / 2 = (α - β + 1 + I * lam) / 2 := by ring
  rw [h1, h2]
  have hpow := two_cpow_mul_cosh t (I * lam - (α + β + 1))
  rw [neg_sub] at hpow
  rw [← hpow]
  ring

/-- The argument complementary to the Jacobi Gauss argument. -/
private theorem one_sub_neg_sinh_sq_eq_cosh_sq (t : ℝ) :
    (1 : ℂ) - -(Complex.sinh t) ^ 2 = ((Real.cosh t ^ 2 : ℝ) : ℂ) := by
  rw [Real.cosh_sq', ofReal_add, ofReal_one, ofReal_pow, ofReal_sinh, sub_neg_eq_add]

/-- The argument obtained after the Pfaff transformation. -/
private theorem neg_sinh_sq_div_sub_one_eq_tanh_sq (t : ℝ) :
    (-(Complex.sinh t) ^ 2) / (-(Complex.sinh t) ^ 2 - 1) = ((Real.tanh t ^ 2 : ℝ) : ℂ) := by
  rw [show -(Complex.sinh t) ^ 2 - 1 = -(1 - -(Complex.sinh t) ^ 2) by ring,
    one_sub_neg_sinh_sq_eq_cosh_sq, neg_div_neg_eq, Real.tanh_eq_sinh_div_cosh, div_pow, ofReal_div]
  simp only [ofReal_pow, ofReal_sinh]

end Jacobi

/-- **Leading behaviour of `Φ_λ`**: `Φ_λ(t) e^{(ρ − iλ)t} → 1`. -/
theorem tendsto_harishChandraSeries (α β lam : ℂ) (hlam : ∀ k : ℕ, I * lam ≠ k + 1) :
    Tendsto (fun t : ℝ => harishChandraSeries α β lam t * exp ((α + β + 1 - I * lam) * t))
      atTop (𝓝 1) := by
  let w := α + β + 1 - I * lam
  let a := w / 2
  let b := (α - β + 1 - I * lam) / 2
  let c := 1 - I * lam
  have hc : ∀ k : ℕ, c ≠ -(k : ℂ) := by
    intro k hk
    apply hlam k
    dsimp only [c] at hk
    linear_combination -hk
  have hcosh : Tendsto (fun t : ℝ => ((Real.cosh t : ℂ) ^ 2)⁻¹) atTop (𝓝 0) := by
    have hinv : Tendsto (fun t : ℝ => (Real.cosh t)⁻¹) atTop (𝓝 0) := by
      have h := Jacobi.tendsto_exp_div_cosh.mul Real.tendsto_exp_neg_atTop_nhds_zero
      rw [mul_zero] at h
      refine h.congr fun t => ?_
      rw [Real.exp_neg]
      field_simp
    have h := hinv.ofReal.pow (n := 2)
    simpa only [ofReal_zero, zero_pow two_ne_zero, ofReal_inv, inv_pow] using h
  have harg : (0 : ℂ) ∈ cutPlane := mem_cutPlane_of_norm_lt_one (by simp)
  have hGauss := (analyticAt_regularizedGaussHypergeometric a b c harg).continuousAt.tendsto.comp
    hcosh
  have hratio : Tendsto (fun t : ℝ => ((Real.exp t / (2 * Real.cosh t) : ℝ) : ℂ) ^ w)
      atTop (𝓝 1) := by
    have h := Jacobi.tendsto_exp_div_cosh.div_const 2
    rw [div_self (by norm_num : (2 : ℝ) ≠ 0)] at h
    have hr : Tendsto (fun t : ℝ => (Real.exp t / (2 * Real.cosh t) : ℝ)) atTop (𝓝 1) :=
      h.congr fun t => by ring_nf
    have hp := (continuousAt_cpow_const (b := w) (a := 1) (by simp)).tendsto.comp hr.ofReal
    rw [one_cpow] at hp
    exact hp
  have h := hratio.mul (hGauss.const_mul (Gamma c))
  rw [regularizedGaussHypergeometric_zero, mul_inv_cancel₀ (Gamma_ne_zero hc), one_mul] at h
  refine h.congr fun t => ?_
  have hpow := Jacobi.ofReal_cpow_mul_exp_eq_div_cpow (2 * Real.cosh t) (by positivity) t w
  rw [← hpow, harishChandraSeries_def]
  simp only [Function.comp_apply, w, a, b, c]
  rw [neg_sub]
  ring

set_option maxHeartbeats 550000 in
set_option linter.unusedVariables false in
/-- **The connection formula**: `φ_λ = c(λ) Φ_λ + c(−λ) Φ_{−λ}` on `t > 0`, for `iλ ∉ ℤ`. -/
theorem jacobiFunction_eq_cFunction (α β lam : ℂ) (hα : ∀ k : ℕ, α + 1 ≠ -k)
    (hlam : ∀ k : ℤ, I * lam ≠ k) {t : ℝ} (ht : 0 < t) :
    jacobiFunction α β lam t =
      cFunction α β lam * harishChandraSeries α β lam t +
        cFunction α β (-lam) * harishChandraSeries α β (-lam) t := by
  let ρ := α + β + 1
  let x := I * lam
  let a := (ρ + x) / 2
  let b := (ρ - x) / 2
  let c := α + 1
  let p := (α - β + 1 - x) / 2
  let m := (α - β + 1 + x) / 2
  let z : ℂ := ((Real.tanh t ^ 2 : ℝ) : ℂ)
  let q : ℂ := ((Real.cosh t : ℂ) ^ 2)⁻¹
  let R : ℂ := Real.cosh t
  have hR : R ≠ 0 := ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
  have hz : z ∈ cutPlane := by
    apply mem_cutPlane_of_norm_lt_one
    dsimp only [z]
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Real.tanh_sq_lt_one t
  have hz' : 1 - z ∈ cutPlane := by
    rw [mem_cutPlane, sub_sub_cancel]
    apply ofReal_mem_slitPlane.mpr
    rw [Real.tanh_eq_sinh_div_cosh]
    exact sq_pos_of_pos (div_pos (Real.sinh_pos_iff.mpr ht) (Real.cosh_pos t))
  have hcomplexCosh : (Real.cosh t : ℂ) ^ 2 - (Real.sinh t : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cosh_sq_sub_sinh_sq t
  have hq : 1 - z = q := by
    dsimp only [z, q]
    rw [Real.tanh_eq_sinh_div_cosh, div_pow, ofReal_div, ofReal_pow, ofReal_pow]
    rw [← one_div]
    have hne : (Real.cosh t : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hR
    apply (eq_div_iff hne).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hne]
    exact hcomplexCosh
  have hp : c - a = p := by dsimp only [c, a, p, ρ]; ring
  have hm : c - b = m := by dsimp only [c, b, m, ρ]; ring
  have ha : c - p = a := by dsimp only [c, p, a, ρ]; ring
  have hgap : c - b - p = x := by dsimp only [c, b, p, ρ]; ring
  have hcp : 1 + b + p - c = 1 - x := by rw [← hgap]; ring
  have hcm : 1 + c - b - p = 1 + x := by rw [← hgap]; ring
  have hpf := regularizedGaussHypergeometric_pfaff b a c (neg_sinh_sq_mem_cutPlane t)
  have hpow : 2 * (-b) = x - ρ := by dsimp only [b]; ring
  rw [hp, Jacobi.one_sub_neg_sinh_sq_eq_cosh_sq, Jacobi.neg_sinh_sq_div_sub_one_eq_tanh_sq,
    Jacobi.ofReal_cosh_sq_cpow, hpow] at hpf
  have hJ : jacobiFunction α β lam t = Gamma c *
      (R ^ (x - ρ) * regularizedGaussHypergeometric b p c z) := by
    rw [jacobiFunction, regularizedGaussHypergeometric_symm a b c (neg_sinh_sq_mem_cutPlane t), hpf]
  have hConn := regularizedGaussHypergeometric_eq_connection_one_sub b p c
    (by rw [hgap]; exact hlam) hz hz'
  rw [GaussConnection.atOne_def, hgap, hcp, hcm, hm, ha, hq,
    regularizedGaussHypergeometric_symm m a (1 + x) (hq ▸ hz')] at hConn
  have hG := Gamma_mul_Gamma_one_sub x
  have hGneg : Gamma (-x) * Gamma (1 + x) = -(Real.pi / Complex.sin (Real.pi * x)) := by
    simpa only [sub_neg_eq_add, mul_neg, sin_neg, div_neg] using Gamma_mul_Gamma_one_sub (-x)
  have hpowQ : q ^ x = R ^ (-2 * x) := by
    dsimp only [q, R]
    rw [← ofReal_pow, ← ofReal_inv, ofReal_cpow_eq_exp (by positivity),
      ofReal_cpow_eq_exp (Real.cosh_pos t), Real.log_inv, Real.log_pow]
    push_cast
    ring_nf
  have hpowPlusMinus : R ^ (x - ρ) * q ^ x = R ^ (-x - ρ) := by
    rw [hpowQ, ← cpow_add _ _ hR]
    congr 1
    ring
  rw [hJ, hConn, ← hG]
  have hpos := Jacobi.cFunction_mul_harishChandraSeries α β lam t
  have hneg := Jacobi.cFunction_mul_harishChandraSeries α β (-lam) t
  simp only [mul_neg, sub_neg_eq_add, ← sub_eq_add_neg] at hneg
  rw [hpos, hneg]
  -- Both coefficients are now the Gauss connection coefficients in the same normalization.
  dsimp only [p, m, q, a, b, c, ρ, R, x] at hpowPlusMinus hGneg ⊢
  rw [hGneg]
  -- Group the powers in the second term before using the combined exponent.
  calc
    _ =
        (Real.cosh t : ℂ) ^ (I * lam - (α + β + 1)) * Gamma (α + 1) *
          ((Gamma (I * lam) * Gamma (1 - I * lam)) *
            regularizedGaussHypergeometric ((α + β + 1 - I * lam) / 2)
              ((α - β + 1 - I * lam) / 2) (1 - I * lam) ((Real.cosh t : ℂ) ^ 2)⁻¹ /
              (Gamma ((α + β + 1 + I * lam) / 2) * Gamma ((α - β + 1 + I * lam) / 2))) -
        ((Real.cosh t : ℂ) ^ (I * lam - (α + β + 1)) * (((Real.cosh t : ℂ) ^ 2)⁻¹) ^ (I * lam)) *
          Gamma (α + 1) *
          ((Gamma (I * lam) * Gamma (1 - I * lam)) *
            regularizedGaussHypergeometric ((α + β + 1 + I * lam) / 2)
              ((α - β + 1 + I * lam) / 2) (1 + I * lam) ((Real.cosh t : ℂ) ^ 2)⁻¹ /
              (Gamma ((α + β + 1 - I * lam) / 2) * Gamma ((α - β + 1 - I * lam) / 2))) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
    _ = _ := by
      rw [hpowPlusMinus, ← hG]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

set_option linter.unusedVariables false in
/-- **Asymptotics**: for `Im λ < 0`, `φ_λ(t) e^{(ρ − iλ)t} → c(λ)`. -/
theorem tendsto_jacobiFunction_mul_exp (α β lam : ℂ) (hα : ∀ k : ℕ, α + 1 ≠ -k)
    (hlam : lam.im < 0) :
    Tendsto (fun t : ℝ => jacobiFunction α β lam t * exp ((α + β + 1 - I * lam) * t))
      atTop (𝓝 (cFunction α β lam)) := by
  let w := α + β + 1 - I * lam
  let a := (α + β + 1 + I * lam) / 2
  let b := w / 2
  let c := α + 1
  have hgap : c - b - (c - a) = I * lam := by dsimp only [a, b, c, w]; ring
  have hca : c - b = (I * lam + α - β + 1) / 2 := by dsimp only [b, c, w]; ring
  have hGauss := (tendsto_regularizedGaussHypergeometric_left_one
    (a := b) (b := c - a) (c := c) (by rw [hgap, I_mul_re]; linarith)).comp
      Jacobi.tendsto_tanh_sq
  have hratio := (continuousAt_cpow_const (b := w) (a := (↑(2 : ℝ) : ℂ))
    (ofReal_mem_slitPlane.mpr (by norm_num))).tendsto.comp Jacobi.tendsto_exp_div_cosh.ofReal
  have h := hratio.mul (hGauss.const_mul (Gamma c))
  have hlim : ((↑(2 : ℝ) : ℂ) ^ w) *
      (Gamma c * (Gamma (c - b - (c - a)) / (Gamma (c - b) * Gamma (c - (c - a))))) =
      cFunction α β lam := by
    rw [hgap, hca, sub_sub_cancel, cFunction_def]
    simp only [a, w, c, ofReal_ofNat, div_eq_mul_inv]
    ring_nf
  rw [hlim] at h
  refine h.congr fun t => ?_
  have hpf := regularizedGaussHypergeometric_pfaff b a c (neg_sinh_sq_mem_cutPlane t)
  have hw : 2 * -b = -w := by dsimp only [b]; ring
  rw [Jacobi.one_sub_neg_sinh_sq_eq_cosh_sq, Jacobi.neg_sinh_sq_div_sub_one_eq_tanh_sq,
    Jacobi.ofReal_cosh_sq_cpow, hw] at hpf
  have heq : jacobiFunction α β lam t =
      Gamma c * regularizedGaussHypergeometric a b c (-(Complex.sinh t) ^ 2) := rfl
  simp only [Function.comp_apply]
  rw [heq, regularizedGaussHypergeometric_symm a b c (neg_sinh_sq_mem_cutPlane t), hpf,
    ← Jacobi.ofReal_cpow_mul_exp_eq_div_cpow (Real.cosh t) (Real.cosh_pos t) t w]
  ring

/-- **Polynomial growth of the Plancherel density**: for real `α > −1`,
`|c(λ)|⁻² ≤ C (1 + |λ|)^{2α + 1}` on the real line. -/
theorem norm_cFunction_inv_sq_le (α β : ℝ) (hα : -1 < α) :
    ∃ C, ∀ lam : ℝ, ‖cFunction α β lam‖⁻¹ ^ 2 ≤ C * (1 + |lam|) ^ (2 * α + 1) := by
  sorry

namespace Jacobi

private theorem norm_sub_jacobiSpectralValue_le (lam : ℂ) (ρ : ℝ) :
    ‖(‖lam ^ 2 + (ρ : ℂ) ^ 2‖ : ℂ) - (lam ^ 2 + (ρ : ℂ) ^ 2)‖ ≤
      2 * |lam.im| * √‖lam ^ 2 + (ρ : ℂ) ^ 2‖ := by
  let κ := lam ^ 2 + (ρ : ℂ) ^ 2
  let k := ‖κ‖
  change ‖(k : ℂ) - κ‖ ≤ 2 * |lam.im| * √k
  have hk : 0 ≤ k := norm_nonneg _
  have hre : κ.re = lam.re ^ 2 - lam.im ^ 2 + ρ ^ 2 := by
    simp only [κ, add_re, pow_two, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  have hbound : k ≤ lam.re ^ 2 + lam.im ^ 2 + ρ ^ 2 := by
    calc
      k ≤ ‖lam ^ 2‖ + ‖(ρ : ℂ) ^ 2‖ := norm_add_le _ _
      _ = _ := by
        rw [norm_pow, norm_pow, norm_real, Real.norm_eq_abs, sq_abs,
          ← normSq_eq_norm_sq, normSq_apply, pow_two, pow_two, pow_two]
  have hnorm : ‖(k : ℂ) - κ‖ ^ 2 = 2 * k * (k - κ.re) := by
    have h : κ.re * κ.re + κ.im * κ.im = k ^ 2 := by
      rw [← normSq_apply, normSq_eq_norm_sq]
    rw [← normSq_eq_norm_sq, normSq_apply]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, zero_sub]
    linear_combination h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [hnorm, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hk]
  rw [hre]
  have h : k - (lam.re ^ 2 - lam.im ^ 2 + ρ ^ 2) ≤ 2 * lam.im ^ 2 := by linarith
  calc
    _ ≤ 2 * k * (2 * lam.im ^ 2) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

end Jacobi

set_option maxHeartbeats 1400000 in
/-- The Jacobi function has spectral growth at most `exp (|Im λ| |t|)`. -/
theorem norm_jacobiFunction_le_exp (α β : ℝ) (hα : -1 / 2 ≤ α) (hρ : 0 ≤ α + β + 1)
    (lam : ℂ) (t : ℝ) :
    ‖jacobiFunction α β lam t‖ ≤ Real.exp (|lam.im| * |t|) := by
  let ρ := α + β + 1
  let κ := lam ^ 2 + (ρ : ℂ) ^ 2
  let k := ‖κ‖
  let m := |lam.im|
  have hm : 0 ≤ m := abs_nonneg _
  have hreg : ∀ j : ℕ, (α : ℂ) + 1 ≠ -(j : ℂ) := by
    intro j hj
    have hr := congrArg Complex.re hj
    simp only [add_re, ofReal_re, one_re, neg_re, natCast_re] at hr
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hρ' : (ρ : ℂ) = (α : ℂ) + β + 1 := by simp [ρ]
  by_cases hk0 : κ = 0
  · have hfactor : (lam - I * ρ) * (lam + I * ρ) = κ := by
      dsimp only [κ]
      linear_combination -(ρ : ℂ) ^ 2 * Complex.I_sq
    have hon := jacobiFunction_I_mul_rho (α : ℂ) (β : ℂ) hreg t
    rw [← hρ'] at hon
    rw [hk0, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hfactor
    rcases hfactor with rfl | rfl
    · rw [hon, norm_one]
      exact Real.one_le_exp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · rw [jacobiFunction_neg, hon, norm_one]
      exact Real.one_le_exp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hk : 0 < k := norm_pos_iff.mpr hk0
  let u (s : ℝ) := jacobiFunction α β lam s
  have hu : ContDiff ℝ 2 u := contDiff_iff_contDiffAt.mpr
    (fun s => (analyticAt_jacobiFunction_radius α β lam s).contDiffAt)
  have huDiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hudDiff : Differentiable ℝ (deriv u) :=
    (ContDiff.deriv' (n := 1) hu).differentiable (by norm_num)
  have huZero : u 0 = 1 := jacobiFunction_zero α β lam hreg
  have hderivZero : deriv u 0 = 0 := by
    have hu0 : HasDerivAt u (deriv u 0) (-(0 : ℝ)) := by
      rw [neg_zero]
      exact (huDiff 0).hasDerivAt
    have hn : HasDerivAt (fun s : ℝ => -s) (-1) (0 : ℝ) := (hasDerivAt_id (0 : ℝ)).neg
    have h := hu0.scomp (0 : ℝ) hn
    simp only [Function.comp_def, neg_smul, one_smul] at h
    have hEven : (fun s : ℝ => u (-s)) = u :=
      funext fun s => jacobiFunction_even α β lam s
    rw [hEven] at h
    linear_combination (1 / 2 : ℂ) * h.deriv
  let damping (s : ℝ) :=
    (2 * α + 1) * (Real.cosh s / Real.sinh s) + (2 * β + 1) * Real.tanh s
  have hDamp (s : ℝ) (hs : 0 < s) : 0 ≤ damping s := by
    have hsin := Real.sinh_pos_iff.mpr hs
    have hcos := Real.cosh_pos s
    have hratio : Real.cosh s / Real.sinh s - Real.tanh s =
        (Real.cosh s * Real.sinh s)⁻¹ := by
      rw [Real.tanh_eq_sinh_div_cosh]
      field_simp
      exact Real.cosh_sq_sub_sinh_sq s
    have hformula : damping s = (2 * α + 1) * (Real.cosh s / Real.sinh s - Real.tanh s) +
        (2 * ρ) * Real.tanh s := by dsimp [damping, ρ]; ring
    rw [hformula, hratio, Real.tanh_eq_sinh_div_cosh]
    have hcoeff : 0 ≤ 2 * α + 1 := by linarith
    exact add_nonneg (mul_nonneg hcoeff (by positivity)) (mul_nonneg (by dsimp [ρ]; linarith)
      (div_nonneg hsin.le hcos.le))
  have hODE (s : ℝ) (hs : 0 < s) :
      deriv (deriv u) s = -(k • u s) + ((k : ℂ) - κ) * u s - damping s • deriv u s := by
    have h : jacobiOperator (α : ℂ) (β : ℂ) u s = -κ * u s := by
      have hκ : κ = lam ^ 2 + ((α : ℂ) + β + 1) ^ 2 :=
        congrArg (fun z => lam ^ 2 + z ^ 2) hρ'
      rw [hκ]
      exact jacobiOperator_jacobiFunction α β lam hreg hs
    rw [jacobiOperator_def] at h
    simp only [Complex.real_smul, damping, ofReal_mul, ofReal_add, ofReal_one,
      ofReal_ofNat]
    linear_combination h
  let E (s : ℝ) := k * ‖u s‖ ^ 2 + ‖deriv u s‖ ^ 2
  have hEDeriv (s : ℝ) :
      HasDerivAt E (k * (2 * ⟪u s, deriv u s⟫_ℝ) +
        2 * ⟪deriv u s, deriv (deriv u) s⟫_ℝ) s :=
    (((huDiff s).hasDerivAt.norm_sq).const_mul k).add ((hudDiff s).hasDerivAt.norm_sq)
  -- The real comparison coefficient cancels against the derivative of the norm term.
  have hE' (s : ℝ) (hs : 0 < s) : deriv E s ≤ 2 * m * E s := by
    let z := ((k : ℂ) - κ) * u s
    have hcross : ⟪deriv u s, z⟫_ℝ ≤ m * E s := by
      calc
        _ ≤ ‖deriv u s‖ * ‖z‖ := real_inner_le_norm _ _
        _ = ‖deriv u s‖ * ‖(k : ℂ) - κ‖ * ‖u s‖ := by rw [norm_mul]; ring
        _ ≤ ‖deriv u s‖ * (2 * m * √k) * ‖u s‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Jacobi.norm_sub_jacobiSpectralValue_le lam ρ)
              (norm_nonneg _)) (norm_nonneg _)
        _ = m * (2 * (√k * ‖u s‖) * ‖deriv u s‖) := by ring
        _ ≤ m * E s := by
          apply mul_le_mul_of_nonneg_left _ hm
          have h := sq_nonneg (√k * ‖u s‖ - ‖deriv u s‖)
          have hsquare : (√k * ‖u s‖) ^ 2 = k * ‖u s‖ ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hk.le]
          dsimp only [E]
          nlinarith only [h, hsquare]
    rw [(hEDeriv s).deriv, hODE s hs, inner_sub_right, inner_add_right, inner_neg_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_comm (u s) (deriv u s)]
    have hpositive := mul_nonneg (hDamp s hs) (sq_nonneg ‖deriv u s‖)
    change k * (2 * ⟪u s, deriv u s⟫_ℝ) +
      2 * (-(k * ⟪u s, deriv u s⟫_ℝ) + ⟪deriv u s, z⟫_ℝ -
        damping s * ‖deriv u s‖ ^ 2) ≤ _
    linarith only [hpositive, hcross]
  let E₀ (s : ℝ) := Real.exp (-(2 * m) * s) * E s
  have hScale (s : ℝ) : HasDerivAt E₀
      (Real.exp (-(2 * m) * s) * (-(2 * m) * E s + deriv E s)) s := by
    have h := (((hasDerivAt_id s).const_mul (-(2 * m))).exp).mul (hEDeriv s)
    rw [← (hEDeriv s).deriv] at h
    refine h.congr_deriv ?_
    simp only [id_eq, mul_one]
    ring
  have hAnti : AntitoneOn E₀ (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact (continuous_iff_continuousAt.mpr (fun s => (hScale s).continuousAt)).continuousOn
    · exact fun s _ => (hScale s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hScale s).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (by linarith only [hE' s hs])
  have hAt (s : ℝ) (hs : 0 ≤ s) : ‖u s‖ ≤ Real.exp (m * s) := by
    have hle := hAnti (show (0 : ℝ) ∈ Ici 0 by simp) (show s ∈ Ici 0 from hs) hs
    have hEzero : E₀ 0 = k := by simp [E₀, E, huZero, hderivZero]
    rw [hEzero] at hle
    have hpos : k * ‖u s‖ ^ 2 ≤ E s := le_add_of_nonneg_right (sq_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hle (Real.exp_nonneg ((2 * m) * s))
    have heq : Real.exp ((2 * m) * s) * E₀ s = E s := by
      dsimp only [E₀]
      rw [← mul_assoc, ← Real.exp_add, show (2 * m) * s + -(2 * m) * s = 0 by ring, Real.exp_zero,
        one_mul]
    rw [heq] at hmul
    apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_nonneg _)).mp
    apply (mul_le_mul_iff_of_pos_left hk).mp
    calc
      _ ≤ E s := hpos
      _ ≤ _ := hmul
      _ = _ := by rw [pow_two, ← Real.exp_add, mul_comm k]; congr 2; ring
  by_cases ht : 0 ≤ t
  · simpa only [u, abs_of_nonneg ht] using hAt t ht
  · have h := hAt (-t) (by linarith)
    simpa only [u, jacobiFunction_even, abs_of_nonpos (le_of_not_ge ht)] using h

/-- **The energy bound**: for real `λ`, real `α ≥ −1/2` and `α + β + 1 ≥ 0`,
`|φ_λ(t)| ≤ 1`. -/
theorem norm_jacobiFunction_le_one (α β lam : ℝ) (hα : -1 / 2 ≤ α) (hρ : 0 ≤ α + β + 1)
    (t : ℝ) :
    ‖jacobiFunction α β lam t‖ ≤ 1 := by
  simpa only [ofReal_im, abs_zero, zero_mul, Real.exp_zero] using
    norm_jacobiFunction_le_exp α β hα hρ lam t

/-- **Koornwinder's Laplace-type representation**, for real `α > β > −1/2`
(Vilenkin–Klimyk Vol. 2 §11.4.6, (5), p. 349). -/
theorem jacobiFunction_laplace (α β : ℝ) (hαβ : β < α) (hβ : -1 / 2 < β) (lam : ℂ) (t : ℝ) :
    jacobiFunction α β lam t =
      2 * Gamma (α + 1) / (Real.sqrt π * Gamma (α - β) * Gamma (β + 1 / 2)) *
        ∫ ψ in (0 : ℝ)..π, ∫ r in (0 : ℝ)..1,
          ((‖(Real.cosh t : ℂ) + r * exp (ψ * I) * Real.sinh t‖ : ℝ) : ℂ) ^
              (I * lam - (α + β + 1)) *
            (r ^ (2 * β + 1) * (1 - r ^ 2) ^ (α - β - 1) * Real.sin ψ ^ (2 * β) : ℝ) := by
  sorry

/-- **Bound by the imaginary part**, for real `α ≥ β ≥ −1/2`: `|φ_λ(t)| ≤ φ_{i Im λ}(t)`. -/
theorem norm_jacobiFunction_le (α β : ℝ) (hαβ : β ≤ α) (hβ : -1 / 2 ≤ β) (lam : ℂ) (t : ℝ) :
    ‖jacobiFunction α β lam t‖ ≤ (jacobiFunction α β (I * lam.im) t).re := by
  sorry

set_option maxHeartbeats 1400000 in
/-- **Bounded Jacobi functions**: for real `α ≥ β ≥ −1/2`, `φ_λ` is bounded on `[0, ∞)`
exactly when `|Im λ| ≤ ρ`. -/
theorem bddAbove_jacobiFunction_iff (α β : ℝ) (hαβ : β ≤ α) (hβ : -1 / 2 ≤ β) (lam : ℂ) :
    BddAbove (range fun t : ℝ => ‖jacobiFunction α β lam t‖) ↔ |lam.im| ≤ α + β + 1 := by
  have hρ : 0 ≤ α + β + 1 := by linarith
  wlog hIm : lam.im ≤ 0 generalizing lam
  · have h := this (-lam) (by rw [neg_im]; linarith)
    simpa only [jacobiFunction_neg, neg_im, abs_neg] using h
  rcases lt_or_eq_of_le hIm with hneg | hzero
  swap
  · have hreal : lam = (lam.re : ℂ) := Complex.ext (by simp) (by simp [hzero])
    refine iff_of_true ⟨1, ?_⟩ (by simpa [hzero] using hρ)
    rintro _ ⟨t, rfl⟩
    rw [hreal]
    exact norm_jacobiFunction_le_one α β lam.re (hβ.trans hαβ) hρ t
  let ρ := α + β + 1
  let q (t : ℝ) := jacobiFunction α β lam t * exp (((α : ℂ) + β + 1 - I * lam) * t)
  have hreg : ∀ j : ℕ, (α : ℂ) + 1 ≠ -(j : ℂ) := by
    intro j hj
    have hr := congrArg Complex.re hj
    simp only [add_re, ofReal_re, one_re, neg_re, natCast_re] at hr
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hq : Tendsto q atTop (𝓝 (cFunction α β lam)) :=
    tendsto_jacobiFunction_mul_exp α β lam hreg hneg
  have hNorm (t : ℝ) : ‖q t‖ =
      ‖jacobiFunction α β lam t‖ * Real.exp ((ρ + lam.im) * t) := by
    simp [q, ρ, norm_exp, mul_re, sub_re, add_re, one_re]
  rw [abs_of_nonpos hIm]
  change _ ↔ -lam.im ≤ ρ
  constructor
  · rintro ⟨C, hC⟩
    by_contra! hbad
    have hμ : ρ + lam.im < 0 := by linarith
    have ht : Tendsto (fun t : ℝ => C * Real.exp ((ρ + lam.im) * t)) atTop (𝓝 0) := by
      have h := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hμ)).const_mul C
      simpa only [Function.comp_def, id_eq, mul_zero] using h
    have hNormLim : Tendsto (fun t : ℝ => ‖q t‖) atTop (𝓝 0) :=
      squeeze_zero (fun _ => norm_nonneg _) (fun t => by
        rw [hNorm]
        exact mul_le_mul_of_nonneg_right (hC (mem_range_self t)) (Real.exp_nonneg _)) ht
    have hcZero : cFunction α β lam = 0 :=
      tendsto_nhds_unique hq (tendsto_zero_iff_norm_tendsto_zero.mpr hNormLim)
    have hαg : Gamma ((α : ℂ) + 1) ≠ 0 := by
      apply Gamma_ne_zero_of_re_pos
      simp only [add_re, ofReal_re, one_re]
      linarith
    have hGammaSpectral : Gamma (I * lam) ≠ 0 :=
      Gamma_ne_zero_of_re_pos (by rw [I_mul_re]; linarith)
    have hρg : Gamma ((I * lam + ((α : ℂ) + β + 1)) / 2) ≠ 0 := by
      apply Gamma_ne_zero_of_re_pos
      rw [div_ofNat_re]
      simp only [add_re, I_mul_re, ofReal_re, one_re]
      linarith
    have hdiffg : Gamma ((I * lam + α - β + 1) / 2) ≠ 0 := by
      apply Gamma_ne_zero_of_re_pos
      rw [div_ofNat_re]
      simp only [add_re, sub_re, I_mul_re, ofReal_re, one_re]
      linarith
    have hpow : (2 : ℂ) ^ ((α : ℂ) + β + 1 - I * lam) ≠ 0 := by
      exact cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
    apply (div_ne_zero (mul_ne_zero (mul_ne_zero hpow hαg) hGammaSpectral) (mul_ne_zero hρg hdiffg))
    exact hcZero
  · intro h
    have hμ : 0 ≤ ρ + lam.im := by linarith
    have hevt : ∀ᶠ t : ℝ in atTop, ‖q t‖ ≤ 1 + ‖cFunction α β lam‖ := by
      filter_upwards [Metric.tendsto_nhds.mp hq 1 zero_lt_one] with t ht
      rw [dist_eq_norm] at ht
      exact (norm_le_norm_sub_add (q t) (cFunction α β lam)).trans (add_le_add_left ht.le _)
    obtain ⟨R, hR⟩ := eventually_atTop.mp hevt
    have hφ : Continuous (fun t : ℝ => jacobiFunction α β lam t) :=
      continuous_iff_continuousAt.mpr fun t =>
        (analyticAt_jacobiFunction_radius α β lam t).continuousAt
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := max R 0)).exists_bound_of_continuousOn
      hφ.continuousOn
    refine ⟨max C (1 + ‖cFunction α β lam‖), ?_⟩
    have hPos (t : ℝ) (ht : 0 ≤ t) : ‖jacobiFunction α β lam t‖ ≤
        max C (1 + ‖cFunction α β lam‖) := by
      by_cases htR : max R 0 ≤ t
      · have hle := hR t ((le_max_left R (0 : ℝ)).trans htR)
        rw [hNorm] at hle
        exact (le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (mul_nonneg hμ ht))).trans
          (hle.trans (le_max_right _ _))
      · exact (hC t ⟨ht, le_of_not_ge htR⟩).trans (le_max_left _ _)
    rintro _ ⟨t, rfl⟩
    by_cases ht : 0 ≤ t
    · exact hPos t ht
    · simpa only [jacobiFunction_even] using hPos (-t) (by linarith)

/-- **Koornwinder's product formula**, for real `α > β > −1/2` (Vilenkin–Klimyk Vol. 2
§11.4.6, (4), p. 348). -/
theorem jacobiFunction_mul_jacobiFunction (α β : ℝ) (hαβ : β < α) (hβ : -1 / 2 < β) (lam : ℂ)
    (t₁ t₂ : ℝ) :
    jacobiFunction α β lam t₁ * jacobiFunction α β lam t₂ =
      2 * Gamma (α + 1) / (Real.sqrt π * Gamma (α - β) * Gamma (β + 1 / 2)) *
        ∫ ψ in (0 : ℝ)..π, ∫ r in (0 : ℝ)..1,
          jacobiFunction α β lam
              (Real.arcosh ‖(Real.cosh t₁ * Real.cosh t₂ : ℂ) +
                r * exp (ψ * I) * (Real.sinh t₁ * Real.sinh t₂)‖) *
            (r ^ (2 * β + 1) * (1 - r ^ 2) ^ (α - β - 1) * Real.sin ψ ^ (2 * β) : ℝ) := by
  sorry

end SFVK.RankOne
