/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU11.Basic.BoostMatrixElements
public import DLMF.Legendre.Basic.Functions
public import DLMF.Legendre.Basic.Associated
public import DLMF.Hypergeometric.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
import SFVK.SU11.MatrixElementKernels
import DLMF.Legendre.Laplace
import DLMF.Hypergeometric.ArgumentContinuation
import SFVKMathlib.Analysis.Complex.GaussCutPlane

/-!
# Special function formulas for `SU(1,1)` boost matrix elements

The hypergeometric forms, the Legendre specialization, and the symmetries of
`SFVK.SU11.boostMatrixElement` are the formulas of Vilenkin–Klimyk, *Representation of Lie Groups
and Special Functions*, Vol. 1, §§6.5.3–6.5.7, pp. 313–323. The reciprocal Gamma factors are
entire, and the regularized Gauss function gives the formulas across exceptional parameters.
The proofs use lean-DLMF's Pfaff transformation and its Laplace integral for the Legendre
function.
-/

public section

open AddCircle Complex MeasureTheory
open scoped ComplexConjugate Real

namespace SFVK.SU11

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

open FourierExpansion

/-- **Parity.** `𝔓^τ_{n+k,n}` at `-t` is `(-1)^k` times its value at `t`. -/
theorem boostMatrixElement_neg (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    boostMatrixElement τ (n + k) n (-t) = (-1 : ℂ) ^ k * boostMatrixElement τ (n + k) n t := by
  rw [boostMatrixElement_eq_circleIntegral, boostMatrixElement_eq_circleIntegral,
    ← integral_const_mul]
  let f : 𝕋 → ℂ := fun θ => fourier k θ * boostKernel τ n t (fourier 1 θ)
  have hpres : MeasurePreserving (MeasurableEquiv.addRight (π : 𝕋)) haarAddCircle haarAddCircle :=
    measurePreserving_add_right haarAddCircle _
  have hshift := hpres.integral_comp' (fun θ => (-1 : ℂ) ^ k * f θ)
  refine Eq.trans ?_ hshift
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    have hbase (w : ℂ) : boostBase (-t) w = boostBase t (-w) := by
      simp only [boostBase, neg_div, Real.cosh_neg, Real.sinh_neg, ofReal_neg, neg_mul, mul_neg]
    have hpar : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
      rw [← mul_zpow]
      simp
    have happly (θ : 𝕋) : MeasurableEquiv.addRight (π : 𝕋) θ = θ + (π : 𝕋) := rfl
    simp only [happly, f, fourier_add_angle, fourier_half_period, zpow_one, mul_neg, mul_one,
      boostKernel, hbase, map_neg]
    rw [← mul_assoc ((-1 : ℂ) ^ k), mul_left_comm ((-1 : ℂ) ^ k) (fourier k θ),
      hpar, mul_one]

/-! ### Hypergeometric and Legendre forms -/

open DLMF.Hypergeometric

/-- **The `tanh²` form** (Vilenkin–Klimyk, Vol. 1, §6.5.3 (1)–(3), p. 313).
For `m = n + k`, `k ∈ ℕ`,
`𝔓^τ_{mn} = (τ - m + 1)_k / k! · cosh^{2τ}(t/2) tanh^k(t/2) F(-τ - n, -τ + m; k + 1; tanh²(t/2))`.
-/
theorem boostMatrixElement_eq_hypergeometric (τ : ℂ) (n : ℝ) (k : ℕ) (t : ℝ) :
    boostMatrixElement τ (n + k) n t =
      (ascPochhammer ℂ k).eval (τ - (n + k : ℝ) + 1) / (k.factorial : ℂ) *
        (Real.cosh (t / 2) : ℂ) ^ (2 * τ) * (Real.tanh (t / 2) : ℂ) ^ k *
        ordinaryHypergeometric (-τ - n) (-τ + (n + k : ℝ)) ((k : ℂ) + 1)
          ((Real.tanh (t / 2) : ℂ) ^ 2) := by
  have hLaurent : boostMatrixElement τ (n + k) n t = boostLaurentCoefficient τ n t (-(k : ℤ)) := by
    simpa only [Int.cast_natCast] using boostMatrixElement_eq_laurent τ n (k : ℤ) t
  rw [hLaurent, boostLaurentCoefficient, ordinaryHypergeometric_eq_tsum]
  let fiber : ℕ ≃ {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = -(k : ℤ)} :=
    { toFun := fun j => ⟨(j, j + k), by push_cast; ring⟩
      invFun := fun p => p.1.1
      left_inv := fun _ => rfl
      right_inv := by
        intro p
        apply Subtype.ext
        refine Prod.ext rfl ?_
        exact_mod_cast show ((p.1.1 + k : ℕ) : ℤ) = (p.1.2 : ℤ) by
          have h := p.2
          push_cast
          omega }
  rw [← fiber.tsum_eq, ← tsum_mul_left]
  apply tsum_congr
  intro j
  let c : ℂ := (Real.cosh (t / 2) : ℂ)
  let r : ℂ := (Real.tanh (t / 2) : ℂ)
  let a : ℂ := -τ - (n : ℂ)
  let b : ℂ := -τ + (n : ℂ)
  have hc : c ≠ 0 := ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  have hCpow : c ^ (τ + n) * c ^ (τ - n) = c ^ (2 * τ) := by
    rw [← cpow_add _ _ hc]
    congr 1
    ring
  have hfactorial : ((j + k).factorial : ℂ) =
      (k.factorial : ℂ) * (ascPochhammer ℂ j).eval ((k : ℂ) + 1) := by
    simpa only [Nat.add_comm j k] using (factorial_mul_ascPochhammer ℂ k j).symm
  have hpoch (v : ℂ) : pochhammer v j = (ascPochhammer ℂ j).eval v := rfl
  have href : (-1 : ℂ) ^ k * pochhammer b k =
      (ascPochhammer ℂ k).eval (τ - (n + k : ℝ) + 1) := by
    rw [← pochhammer_reflect, pochhammer]
    congr 1
    dsimp only [b]
    push_cast
    ring
  have hfreq : (-r) ^ j * (-r) ^ (j + k) = (r ^ 2) ^ j * (-1 : ℂ) ^ k * r ^ k := by
    rw [pow_add, ← mul_assoc, ← mul_pow, neg_mul_neg, ← pow_two, neg_pow, mul_assoc]
  have ha : -(τ + (n : ℂ)) = a := by dsimp only [a]; ring
  have hb : -(τ - (n : ℂ)) = b := by dsimp only [b]; ring
  have hm : -τ + (n + k : ℝ) = b + k := by dsimp only [b]; push_cast; ring
  simp only [fiber, Equiv.coe_fn_mk, boostBinomialCoefficient, smul_eq_mul]
  change ((c ^ (τ + n)) * (pochhammer (-(τ + n)) j / j.factorial) * (-r) ^ j) *
      ((c ^ (τ - n)) * (pochhammer (-(τ - n)) (j + k) / (j + k).factorial) *
        (-r) ^ (j + k)) = _
  have hpAdd : pochhammer b (j + k) = pochhammer b k * pochhammer (b + k) j := by
    rw [Nat.add_comm j k, pochhammer_add]
  rw [ha, hb, hpAdd, hfactorial, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (c ^ (τ + n) * c ^ (τ - n)) * ((-r) ^ j * (-r) ^ (j + k)) *
        pochhammer a j * pochhammer b k * pochhammer (b + k) j * (j.factorial : ℂ)⁻¹ *
          (k.factorial : ℂ)⁻¹ * ((ascPochhammer ℂ j).eval (↑k + 1))⁻¹ := by
      ring
    _ = _ := by
      rw [hCpow, hfreq, hpoch a, hpoch (b + k), hm, ← href, div_eq_mul_inv]
      dsimp only [a, c, r]
      ring

/-- **The `-sinh²` form.** For `m = n + k`, `k ∈ ℕ`,
`𝔓^τ_{mn} = (τ - m + 1)_k sinh^k(t/2) cosh^{-(m+n)}(t/2) 𝐅(-τ - n, τ - n + 1; k + 1; -sinh²(t/2))`
with the regularized Gauss function `𝐅` of lean-DLMF. -/
theorem boostMatrixElement_eq_regularizedGaussHypergeometric (τ : ℂ) (n : ℝ) (k : ℕ) (t : ℝ) :
    boostMatrixElement τ (n + k) n t =
      (ascPochhammer ℂ k).eval (τ - (n + k : ℝ) + 1) * (Real.sinh (t / 2) : ℂ) ^ k *
        (Real.cosh (t / 2) : ℂ) ^ (-((n + k + n : ℝ) : ℂ)) *
        DLMF.Hypergeometric.regularizedGaussHypergeometric (-τ - n) (τ - n + 1) ((k : ℂ) + 1)
          (-((Real.sinh (t / 2) : ℂ) ^ 2)) := by
  let c : ℂ := (Real.cosh (t / 2) : ℂ)
  let s : ℂ := (Real.sinh (t / 2) : ℂ)
  let r : ℂ := (Real.tanh (t / 2) : ℂ)
  have hc : c ≠ 0 := ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  have hc2 : c ^ 2 = 1 + s ^ 2 := by
    have h : Real.cosh (t / 2) ^ 2 = 1 + Real.sinh (t / 2) ^ 2 := by
      linarith [Real.cosh_sq_sub_sinh_sq (t / 2)]
    simpa only [c, s, ofReal_pow, ofReal_add, ofReal_one] using congrArg Complex.ofReal h
  have hz : -s ^ 2 ∈ cutPlane := by
    rw [mem_cutPlane, sub_neg_eq_add, ← hc2, mem_slitPlane_iff]
    exact Or.inl (by simpa only [c, ← ofReal_pow, ofReal_re] using
      (pow_pos (Real.cosh_pos (t / 2)) 2))
  have hr : r = s / c := by
    simp only [r, s, c, Real.tanh_eq_sinh_div_cosh, ofReal_div]
  have harg : -s ^ 2 / (-s ^ 2 - 1) = r ^ 2 := by
    rw [hr, div_pow, hc2, show -s ^ 2 - 1 = -(1 + s ^ 2) by ring, neg_div_neg_eq]
  have hnorm : ‖r ^ 2‖ < 1 := by
    rw [norm_pow]
    dsimp only [r]
    rw [norm_real, Real.norm_eq_abs]
    have habs := Real.abs_tanh_lt_one (t / 2)
    nlinarith [mul_nonneg (sub_nonneg.mpr habs.le) (abs_nonneg (Real.tanh (t / 2)))]
  have hk : ∀ j : ℕ, (k : ℂ) + 1 ≠ -(j : ℂ) := by
    intro j h
    have := congrArg Complex.re h
    simp only [add_re, natCast_re, one_re, neg_re] at this
    linarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) j]
  have hp := regularizedGaussHypergeometric_pfaff (-τ - (n : ℂ)) (τ - n + 1)
    ((k : ℂ) + 1) hz
  rw [sub_neg_eq_add, ← hc2, harg] at hp
  rw [show (k : ℂ) + 1 - (τ - n + 1) = -τ + (n + k : ℝ) by push_cast; ring,
    show -(-τ - (n : ℂ)) = τ + n by ring] at hp
  have hcarg : (log c * (2 : ℂ)).im = 0 := by
    have ha : c.arg = 0 := arg_ofReal_of_nonneg (Real.cosh_pos _).le
    rw [mul_im, log_im, ha]
    norm_num
  have hcPow : (c ^ 2) ^ (τ + (n : ℂ)) = c ^ ((2 : ℂ) * (τ + n)) := by
    rw [← cpow_natCast c 2]
    norm_num only [Nat.cast_ofNat]
    exact (cpow_mul _ (by rw [hcarg]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hcarg]; exact Real.pi_pos.le)).symm
  rw [hcPow] at hp
  rw [boostMatrixElement_eq_hypergeometric]
  change _ / (k.factorial : ℂ) * c ^ (2 * τ) * r ^ k * _ =
    _ * s ^ k * c ^ (-((n + k + n : ℝ) : ℂ)) * _
  rw [ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHypergeometric hk hnorm,
    Gamma_nat_eq_factorial, hp, hr, div_pow, ← cpow_natCast c k]
  have he : (2 : ℂ) * τ = -((n + k + n : ℝ) : ℂ) + 2 * (τ + n) + k := by
    push_cast
    ring
  rw [he, cpow_add _ _ hc, cpow_add _ _ hc]
  have hfac : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hcPowNe : c ^ (k : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hc)
  field_simp

/-- **Laplace's integral.** `𝔓^τ_{00}(cosh t) = π⁻¹ ∫₀^π (cosh t + sinh t cos φ)^τ dφ`. -/
theorem boostMatrixElement_zero_zero (τ : ℂ) (t : ℝ) :
    boostMatrixElement τ 0 0 t =
      ((π : ℝ) : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..π,
        ((Real.cosh t + Real.sinh t * Real.cos φ : ℝ) : ℂ) ^ τ := by
  let f : ℝ → ℂ := fun θ => ((Real.cosh t + Real.sinh t * Real.cos θ : ℝ) : ℂ) ^ τ
  have h : boostMatrixElement τ 0 0 t =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f θ := by
    rw [boostMatrixElement_def]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    have hconj : exp (-((θ : ℂ) * I)) = conj (exp ((θ : ℂ) * I)) := by
      rw [← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg]
    simp only [ofReal_zero, add_zero, sub_zero, zero_mul, exp_zero, mul_one, hconj]
    simpa only [boostKernel, boostBase, ofReal_zero, add_zero, sub_zero, f] using
      boostKernel_zero_eq_laplace τ t θ
  have hcont : Continuous f := by
    apply Continuous.cpow (by fun_prop) continuous_const
    intro θ
    exact Or.inl (by simpa only [ofReal_re] using laplaceKernel_pos t θ)
  have hreflect : (∫ θ in π..2 * π, f θ) = ∫ θ in (0 : ℝ)..π, f θ := by
    have hπ : 2 * π - π = π := by ring
    have hrefl := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := π) f (2 * π)
    rw [hπ, sub_zero] at hrefl
    rw [← hrefl]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [f, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, one_mul, zero_mul, add_zero]
  rw [h, ← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable 0 π) (hcont.intervalIntegrable π (2 * π)), hreflect]
  dsimp only [f]
  push_cast
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

/-- **The Legendre function.** `𝔓^τ_{00}(cosh t) = P_τ(cosh t)` with lean-DLMF's `P_ν`
(DLMF 14.3.1 with `μ = 0`). -/
theorem boostMatrixElement_zero_zero_eq_legendreP (τ : ℂ) (t : ℝ) :
    boostMatrixElement τ 0 0 t = DLMF.Legendre.legendreP τ (Real.cosh t) := by
  have hpar : boostMatrixElement τ 0 0 (-t) = boostMatrixElement τ 0 0 t := by
    simpa only [Int.cast_zero, add_zero, zpow_zero, one_mul] using boostMatrixElement_neg τ 0 0 t
  have habs : boostMatrixElement τ 0 0 |t| = boostMatrixElement τ 0 0 t := by
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, hpar]
  rw [← habs, ← Real.cosh_abs t, boostMatrixElement_zero_zero,
    DLMF.Legendre.legendreP_laplace τ (Real.one_le_cosh |t|)]
  have hsqrt : Real.sqrt (Real.cosh |t| ^ 2 - 1) = Real.sinh |t| := by
    have he := Real.cosh_sq_sub_sinh_sq |t|
    rw [show Real.cosh |t| ^ 2 - 1 = Real.sinh |t| ^ 2 by linarith,
      Real.sqrt_sq (Real.sinh_nonneg_iff.mpr (abs_nonneg _))]
  rw [hsqrt, one_div]

/-- The reciprocal Gamma recurrence iterated by a natural shift. -/
private theorem pochhammer_mul_invGamma_add_nat (a : ℂ) (n : ℕ) :
    pochhammer a n * (Gamma (a + n))⁻¹ = (Gamma a)⁻¹ := by
  have hstep (z : ℂ) : z * (Gamma (z + 1))⁻¹ = (Gamma z)⁻¹ := by
    by_cases hz : z = 0
    · subst z
      have h : Gamma 0 = 0 := by simp
      simp [h]
    · rw [Gamma_add_one z hz, mul_inv_rev, ← mul_assoc]
      calc
        z * (Gamma z)⁻¹ * z⁻¹ = (z * z⁻¹) * (Gamma z)⁻¹ := by ring
        _ = _ := by rw [mul_inv_cancel₀ hz, one_mul]
  induction n with
  | zero => simp [pochhammer_zero]
  | succ n hn =>
    rw [pochhammer_succ, Nat.cast_succ, ← add_assoc, mul_assoc, hstep, hn]

/-- **Associated Legendre functions.** For `m ∈ ℕ` and `t > 0`,
`𝔓^τ_{m0}(cosh t) / Γ(τ + 1) = P^{-m}_τ(cosh t) / Γ(τ - m + 1)` with lean-DLMF's `P^μ_ν`
(DLMF 14.3.6). -/
theorem boostMatrixElement_eq_associatedP (τ : ℂ) (m : ℕ) (t : ℝ) (ht : 0 < t) :
    boostMatrixElement τ m 0 t * (Gamma (τ + 1))⁻¹ =
      DLMF.Legendre.associatedP τ (-(m : ℂ)) (Real.cosh t) * (Gamma (τ - m + 1))⁻¹ := by
  have hform := boostMatrixElement_eq_regularizedGaussHypergeometric τ 0 m t
  simp only [zero_add, add_zero, sub_zero, ofReal_zero, ofReal_natCast] at hform
  rw [hform, DLMF.Legendre.associatedP]
  let s := Real.sinh (t / 2)
  let c := Real.cosh (t / 2)
  have hs : 0 < s := Real.sinh_pos_iff.mpr (by positivity)
  have hc : 0 < c := Real.cosh_pos _
  have hx : Real.cosh t = c ^ 2 + s ^ 2 := by
    simpa only [show 2 * (t / 2) = t by ring, c, s] using Real.cosh_two_mul (x := t / 2)
  have hcs : c ^ 2 - s ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  have hplus : Real.cosh t + 1 = 2 * c ^ 2 := by linarith
  have hminus : Real.cosh t - 1 = 2 * s ^ 2 := by linarith
  have hz : (1 - (Real.cosh t : ℂ)) / 2 = -((s : ℂ) ^ 2) := by
    have h : (1 - Real.cosh t) / 2 = -(s ^ 2) := by linarith
    simpa only [ofReal_div, ofReal_sub, ofReal_one, ofReal_ofNat, ofReal_neg, ofReal_pow] using
      congrArg Complex.ofReal h
  rw [hz, show (1 : ℂ) - -(m : ℂ) = (m : ℂ) + 1 by ring,
    regularizedGaussHypergeometric_symm (τ + 1) (-τ) _
      (by simpa only [← Complex.ofReal_sinh] using Complex.neg_sinh_sq_mem_gaussCutPlane (t / 2))]
  have hlogs : log ((Real.cosh t : ℂ) + 1) - log ((Real.cosh t : ℂ) - 1) =
      (2 : ℂ) * ((Real.log c : ℂ) - (Real.log s : ℂ)) := by
    rw [← ofReal_one, ← ofReal_add, ← ofReal_sub, hplus, hminus,
      ← ofReal_log (by positivity), ← ofReal_log (by positivity),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hc.ne'),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hs.ne'),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hpower : exp (((-(m : ℂ)) / 2) *
      (log ((Real.cosh t : ℂ) + 1) - log ((Real.cosh t : ℂ) - 1))) =
      (s : ℂ) ^ m * (c : ℂ) ^ (-(m : ℂ)) := by
    rw [hlogs, show -(m : ℂ) / 2 * (2 * ((Real.log c : ℂ) - (Real.log s : ℂ))) =
        (m : ℂ) * (Real.log s : ℂ) - (m : ℂ) * (Real.log c : ℂ) by ring,
      exp_sub, exp_nat_mul, exp_nat_mul, ← ofReal_exp, ← ofReal_exp,
      Real.exp_log hs, Real.exp_log hc, cpow_neg, cpow_natCast, div_eq_mul_inv]
  rw [hpower]
  have hgamma := pochhammer_mul_invGamma_add_nat (τ - (m : ℂ) + 1) m
  rw [show τ - (m : ℂ) + 1 + m = τ + 1 by ring, pochhammer] at hgamma
  change (_ * (s : ℂ) ^ m * (c : ℂ) ^ (-(m : ℂ)) * _) * _ = _
  calc
    _ = ((ascPochhammer ℂ m).eval (τ - (m : ℂ) + 1) * (Gamma (τ + 1))⁻¹) *
      ((s : ℂ) ^ m * (c : ℂ) ^ (-(m : ℂ)) *
        regularizedGaussHypergeometric (-τ) (τ + 1) ((m : ℂ) + 1) (-(s : ℂ) ^ 2)) := by ring
    _ = _ := by rw [hgamma]; ring

/-! ### Symmetries -/

/-- **Sign reversal.** `𝔓^τ_{-m,-n} = 𝔓^τ_{mn}` (Vilenkin–Klimyk, Vol. 1, §6.5.5, pp. 318–320). -/
theorem boostMatrixElement_neg_neg (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    boostMatrixElement τ (-(n + k)) (-n) t = boostMatrixElement τ (n + k) n t := by
  have hm : -(n + k : ℝ) = -n + ((-k : ℤ) : ℝ) := by push_cast; ring
  rw [hm, boostMatrixElement_eq_circleIntegral, boostMatrixElement_eq_circleIntegral,
    ← integral_neg_angle (fun θ => fourier (-k) θ * boostKernel τ (-n) t (fourier 1 θ))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    simp only [fourier_neg_angle, fourier_neg, conj_conj, boostKernel, ofReal_neg,
      sub_eq_add_neg, neg_neg, mul_comm]

/-- Weighted transposition for a nonnegative shift. -/
private theorem boostMatrixElement_swap_nat (τ : ℂ) (n : ℝ) (k : ℕ) (t : ℝ) :
    boostMatrixElement τ (n + k) n t * ((Gamma (τ + n + 1))⁻¹ * (Gamma (τ - n + 1))⁻¹) =
      boostMatrixElement τ n (n + k) t *
        ((Gamma (τ + (n + k : ℝ) + 1))⁻¹ * (Gamma (τ - (n + k : ℝ) + 1))⁻¹) := by
  let m : ℝ := n + k
  change boostMatrixElement τ (n + k) n t * _ =
    boostMatrixElement τ n m t * ((Gamma (τ + m + 1))⁻¹ * (Gamma (τ - m + 1))⁻¹)
  have hm : -m + (k : ℝ) = -n := by dsimp only [m]; ring
  have hreversal : boostMatrixElement τ n m t = boostMatrixElement τ (-m + k) (-m) t := by
    rw [hm]
    have hn : m + ((-(k : ℤ) : ℤ) : ℝ) = n := by dsimp only [m]; push_cast; ring
    simpa only [hn] using (boostMatrixElement_neg_neg τ m (-(k : ℤ)) t).symm
  have hshift₁ := pochhammer_mul_invGamma_add_nat (τ - (m : ℂ) + 1) k
  rw [show τ - (m : ℂ) + 1 + k = τ - n + 1 by dsimp only [m]; push_cast; ring,
    pochhammer] at hshift₁
  have hshift₂ := pochhammer_mul_invGamma_add_nat (τ + (n : ℂ) + 1) k
  rw [show τ + (n : ℂ) + 1 + k = τ + m + 1 by dsimp only [m]; push_cast; ring,
    pochhammer] at hshift₂
  rw [hreversal, boostMatrixElement_eq_hypergeometric, boostMatrixElement_eq_hypergeometric, hm,
    ofReal_neg, ofReal_neg]
  have hf : ordinaryHypergeometric (-τ - -(m : ℂ)) (-τ + -(n : ℂ)) ((k : ℂ) + 1)
        ((Real.tanh (t / 2) : ℂ) ^ 2) =
      ordinaryHypergeometric (-τ - n) (-τ + m) ((k : ℂ) + 1)
        ((Real.tanh (t / 2) : ℂ) ^ 2) := by
    rw [sub_neg_eq_add, ← sub_eq_add_neg]
    exact congrFun (ordinaryHypergeometric_symm _ _ _) _
  rw [hf, sub_neg_eq_add]
  let c : ℂ := ↑(Real.cosh (t / 2)) ^ (2 * τ)
  let r : ℂ := (Real.tanh (t / 2) : ℂ) ^ k
  let F : ℂ := ordinaryHypergeometric (-τ - n) (-τ + m) ((k : ℂ) + 1)
    ((Real.tanh (t / 2) : ℂ) ^ 2)
  change (ascPochhammer ℂ k).eval (τ - m + 1) / (k.factorial : ℂ) * c * r * F *
      ((Gamma (τ + n + 1))⁻¹ * (Gamma (τ - n + 1))⁻¹) =
    (ascPochhammer ℂ k).eval (τ + n + 1) / (k.factorial : ℂ) * c * r * F *
      ((Gamma (τ + m + 1))⁻¹ * (Gamma (τ - m + 1))⁻¹)
  calc
    _ = ((ascPochhammer ℂ k).eval (τ - m + 1) * (Gamma (τ - n + 1))⁻¹) *
        (Gamma (τ + n + 1))⁻¹ * ((k.factorial : ℂ)⁻¹ * c * r * F) := by ring
    _ = ((ascPochhammer ℂ k).eval (τ + n + 1) * (Gamma (τ + m + 1))⁻¹) *
        (Gamma (τ - m + 1))⁻¹ * ((k.factorial : ℂ)⁻¹ * c * r * F) := by
      rw [hshift₁, hshift₂, mul_comm (Gamma (τ - m + 1))⁻¹]
    _ = _ := by ring

/-- **Transposition** (Vilenkin–Klimyk, Vol. 1, §6.5.5 (2), pp. 318–320):
`𝔓^τ_{mn} / (Γ(τ + n + 1) Γ(τ - n + 1)) = 𝔓^τ_{nm} / (Γ(τ + m + 1) Γ(τ - m + 1))`. -/
theorem boostMatrixElement_swap (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    boostMatrixElement τ (n + k) n t * ((Gamma (τ + n + 1))⁻¹ * (Gamma (τ - n + 1))⁻¹) =
      boostMatrixElement τ n (n + k) t *
        ((Gamma (τ + (n + k : ℝ) + 1))⁻¹ * (Gamma (τ - (n + k : ℝ) + 1))⁻¹) := by
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    simpa only [Int.cast_natCast] using boostMatrixElement_swap_nat τ n k t
  · let l : ℕ := (-k).toNat
    have hl : (l : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have hm : -n + (l : ℝ) = -(n + k) := by
      rw [← Int.cast_natCast, hl, Int.cast_neg]
      ring
    have h₁ : boostMatrixElement τ (-(n + k)) (-n) t =
        boostMatrixElement τ (n + k) n t := boostMatrixElement_neg_neg τ n k t
    have hn : n + (k : ℝ) + ((-k : ℤ) : ℝ) = n := by push_cast; ring
    have h₂ : boostMatrixElement τ (-n) (-(n + k)) t =
        boostMatrixElement τ n (n + k) t := by
      simpa only [hn] using boostMatrixElement_neg_neg τ (n + k) (-k) t
    simpa only [hm, h₁, h₂, ofReal_neg, ← sub_eq_add_neg, sub_neg_eq_add, mul_comm] using
      boostMatrixElement_swap_nat τ (-n) l t

/-- Weighted degree reflection for a nonnegative shift. -/
private theorem boostMatrixElement_reflect_nat (τ : ℂ) (n : ℝ) (k : ℕ) (t : ℝ) :
    boostMatrixElement (-τ - 1) (n + k) n t *
        ((Gamma (τ - (n + k : ℝ) + 1))⁻¹ * (Gamma (τ + (n + k : ℝ) + 1))⁻¹) =
      (-1 : ℂ) ^ k * boostMatrixElement τ (n + k) n t *
        ((Gamma (τ - n + 1))⁻¹ * (Gamma (τ + n + 1))⁻¹) := by
  let m : ℝ := n + k
  have hshift₁ := pochhammer_mul_invGamma_add_nat (τ - (m : ℂ) + 1) k
  rw [show τ - (m : ℂ) + 1 + k = τ - n + 1 by dsimp only [m]; push_cast; ring,
    pochhammer] at hshift₁
  have hshift₂ := pochhammer_mul_invGamma_add_nat (τ + (n : ℂ) + 1) k
  rw [show τ + (n : ℂ) + 1 + k = τ + m + 1 by dsimp only [m]; push_cast; ring,
    pochhammer] at hshift₂
  have hpoch : (ascPochhammer ℂ k).eval (-τ - 1 - m + 1) =
      (-1 : ℂ) ^ k * (ascPochhammer ℂ k).eval (τ + n + 1) := by
    rw [← pochhammer, ← pochhammer, ← pochhammer_reflect]
    congr 1
    dsimp only [m]
    push_cast
    ring
  rw [boostMatrixElement_eq_regularizedGaussHypergeometric,
    boostMatrixElement_eq_regularizedGaussHypergeometric]
  change (ascPochhammer ℂ k).eval (-τ - 1 - m + 1) * _ * _ * _ * _ = _
  rw [hpoch, show -(-τ - 1) - n = τ - n + 1 by ring,
    show -τ - 1 - n + 1 = -τ - n by ring,
    regularizedGaussHypergeometric_symm (τ - n + 1) (-τ - n) _
      (by simpa only [← Complex.ofReal_sinh] using Complex.neg_sinh_sq_mem_gaussCutPlane (t / 2))]
  let D : ℂ := (Real.sinh (t / 2) : ℂ) ^ k *
    (Real.cosh (t / 2) : ℂ) ^ (-((m + n : ℝ) : ℂ)) *
    regularizedGaussHypergeometric (-τ - n) (τ - n + 1) ((k : ℂ) + 1)
      (-((Real.sinh (t / 2) : ℂ) ^ 2))
  calc
    _ = ((ascPochhammer ℂ k).eval (τ + n + 1) * (Gamma (τ + m + 1))⁻¹) *
        (Gamma (τ - m + 1))⁻¹ * ((-1 : ℂ) ^ k * D) := by dsimp only [D, m]; ring
    _ = ((ascPochhammer ℂ k).eval (τ - m + 1) * (Gamma (τ - n + 1))⁻¹) *
        (Gamma (τ + n + 1))⁻¹ * ((-1 : ℂ) ^ k * D) := by
      rw [hshift₂, hshift₁, mul_comm (Gamma (τ + n + 1))⁻¹]
    _ = _ := by dsimp only [D, m]; ring

/-- **Reflection of the degree** (Vilenkin–Klimyk, Vol. 1, §6.5.5 (5), pp. 318–320):
`𝔓^{-τ-1}_{mn} / (Γ(τ - m + 1) Γ(τ + m + 1))` equals
`(-1)^{m-n} 𝔓^τ_{mn} / (Γ(τ - n + 1) Γ(τ + n + 1))`. -/
theorem boostMatrixElement_reflect (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    boostMatrixElement (-τ - 1) (n + k) n t *
        ((Gamma (τ - (n + k : ℝ) + 1))⁻¹ * (Gamma (τ + (n + k : ℝ) + 1))⁻¹) =
      (-1 : ℂ) ^ k * boostMatrixElement τ (n + k) n t *
        ((Gamma (τ - n + 1))⁻¹ * (Gamma (τ + n + 1))⁻¹) := by
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    simpa only [Int.cast_natCast, zpow_natCast] using boostMatrixElement_reflect_nat τ n k t
  · let l : ℕ := (-k).toNat
    have hl : (l : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have hm : -n + (l : ℝ) = -(n + k) := by
      rw [← Int.cast_natCast, hl, Int.cast_neg]
      ring
    have hpow : (-1 : ℂ) ^ l = (-1 : ℂ) ^ k := by
      rw [← zpow_natCast, hl, zpow_neg, ← inv_zpow, inv_neg, inv_one]
    simpa only [hm, boostMatrixElement_neg_neg, ofReal_neg, ← sub_eq_add_neg, sub_neg_eq_add,
      hpow, mul_comm] using boostMatrixElement_reflect_nat τ (-n) l t

/-- **Conjugation.** `conj 𝔓^τ_{mn} = 𝔓^{conj τ}_{mn}` for `m - n ∈ ℤ`. -/
theorem conj_boostMatrixElement (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    conj (boostMatrixElement τ (n + k) n t) = boostMatrixElement (conj τ) (n + k) n t := by
  rw [boostMatrixElement_eq_circleIntegral, boostMatrixElement_eq_circleIntegral, ← integral_conj,
    ← integral_neg_angle (fun θ => conj (fourier k θ * boostKernel τ n t (fourier 1 θ)))]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun θ => ?_
  have hb (w : ℂ) (hw : ‖w‖ = 1) : (boostBase t w).arg ≠ π :=
    (arg_lt_pi_iff.mpr (Or.inl (boostBase_re_pos t hw).le)).ne
  have hw := norm_fourier_one θ
  have hwc : ‖conj (fourier 1 θ)‖ = 1 := (norm_conj _).trans hw
  simp only [fourier_neg_angle, boostKernel, map_mul, conj_conj]
  have hc (z w : ℂ) (hz : ‖z‖ = 1) :
      conj (boostBase t (conj z) ^ w) = boostBase t z ^ conj w := by
    rw [boostBase_conj, ← Complex.cpow_conj _ _ (hb z hz)]
  have hminus : conj (boostBase t (fourier 1 θ) ^ (τ - n)) =
      boostBase t (conj (fourier 1 θ)) ^ conj (τ - n) := by
    simpa only [conj_conj] using hc (conj (fourier 1 θ)) (τ - n) hwc
  rw [hc _ _ hw, hminus, map_add, map_sub, conj_ofReal]

/-- **Vanishing at integral degree.** For `ℓ = N/2` and `m, n ∈ ℓ + ℤ`, `𝔓^ℓ_{mn} = 0` when
`|n| ≤ ℓ < |m|`. -/
theorem boostMatrixElement_eq_zero_of_lt (N : ℕ) (a b : ℤ) (t : ℝ)
    (hn : |(N / 2 + b : ℝ)| ≤ N / 2) (hm : (N / 2 : ℝ) < |(N / 2 + a : ℝ)|) :
    boostMatrixElement ((N : ℂ) / 2) (N / 2 + a) (N / 2 + b) t = 0 := by
  have hb_lower : -(N : ℤ) ≤ b := by
    have h : -(N : ℝ) ≤ b := by linarith [(abs_le.mp hn).1]
    exact_mod_cast h
  have hb_upper : b ≤ 0 := by
    have h : (b : ℝ) ≤ 0 := by linarith [(abs_le.mp hn).2]
    exact_mod_cast h
  let p := ((N : ℤ) + b).toNat
  let q := (-b).toNat
  have hp : ((p : ℕ) : ℤ) = (N : ℤ) + b := Int.toNat_of_nonneg (by omega)
  have hq : ((q : ℕ) : ℤ) = -b := Int.toNat_of_nonneg (by omega)
  have hhp : (p : ℂ) = (N : ℂ) + b := by exact_mod_cast hp
  have hhq : (q : ℂ) = -(b : ℂ) := by exact_mod_cast hq
  have hmshift : (N / 2 + a : ℝ) = (N / 2 + b : ℝ) + ((a - b : ℤ) : ℝ) := by
    push_cast
    ring
  have hplus : (N : ℂ) / 2 + ((N / 2 + b : ℝ) : ℂ) = (p : ℂ) := by
    rw [hhp]
    push_cast
    ring
  have hminus : (N : ℂ) / 2 - ((N / 2 + b : ℝ) : ℂ) = (q : ℂ) := by
    rw [hhq]
    push_cast
    ring
  rw [hmshift, boostMatrixElement_eq_laurent, boostLaurentCoefficient]
  refine (tsum_congr (fun j => ?_)).trans tsum_zero
  by_cases hj : p < j.1.1
  · simp only [boostBinomialCoefficient, hplus, pochhammer_neg_nat_eq_zero hj, zero_div,
      mul_zero, zero_mul]
  · have hk : q < j.1.2 := by
      by_contra! h
      have hdiff := j.2
      have ha : -(N : ℤ) ≤ a := by omega
      have ha' : a ≤ 0 := by omega
      have hreal₁ : -(N : ℝ) ≤ a := by exact_mod_cast ha
      have hreal₂ : (a : ℝ) ≤ 0 := by exact_mod_cast ha'
      exact (not_le_of_gt hm) (abs_le.mpr ⟨by linarith, by linarith⟩)
    simp only [boostBinomialCoefficient, hminus, pochhammer_neg_nat_eq_zero hk, zero_div,
      mul_zero, zero_mul]

end SFVK.SU11
