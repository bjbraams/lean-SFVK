/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU11.Basic.MatrixElementsBasic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
import SFVK.SU11.MatrixElements
import SFVK.SU11.MatrixElementKernels
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The Mehler–Fock transform

The Mehler–Fock transform `ρ ↦ ∫₀^∞ f(t) 𝔓^{-1/2+iρ}_{00}(cosh t) sinh t dt` is unitary from
`L²((0, ∞), sinh t dt)` onto `L²((0, ∞), ρ tanh(πρ) dρ)`, with inversion
`f(t) = ∫₀^∞ F(ρ) 𝔓^{-1/2+iρ}_{00}(cosh t) ρ tanh(πρ) dρ` (Vilenkin–Klimyk, *Representation of
Lie Groups and Special Functions*, Vol. 1, §7.8.4 (15)–(17), pp. 485–486). In the variable
`x = cosh t` it is Wawrzyńczyk, *Group Representations and Special Functions*, (10.5.11)–(10.5.12),
p. 373, whose printed inversion constant `1/(2π²)` is `1` for the transform (10.5.11) as
printed. The same statements hold for the transform of integer order `m` with kernel
`conj 𝔓^{-1/2+iρ}_{m0}(cosh t)` and the same Plancherel density.

The Mehler–Dirichlet formula follows by substituting the logarithm of the positive base in the
Laplace integral. Its angular weight is integrable with uniformly bounded total mass.
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate Real ContDiff

namespace SFVK.SU11

/-- The Mehler–Dirichlet integral for the spherical boost coefficient on the principal line. -/
theorem boostMatrixElement_zero_zero_eq_mehlerDirichlet (ρ t : ℝ) (ht : 0 < t) :
    boostMatrixElement (-1 / 2 + ρ * I) 0 0 t =
      ((π : ℂ) * (Real.sqrt 2 : ℝ))⁻¹ *
        ∫ u in Ioo (-t) t, exp ((ρ : ℂ) * u * I) /
          (Real.sqrt (Real.cosh t - Real.cosh u) : ℝ) := by
  let C := Real.cosh t
  let S := Real.sinh t
  let x : ℝ → ℝ := fun θ => C + S * Real.cos θ
  let τ : ℂ := -1 / 2 + ρ * I
  let G : ℝ → ℂ := fun x => (x : ℂ) ^ τ /
    (Real.sqrt ((Real.exp t - x) * (x - Real.exp (-t))) : ℝ)
  let H : ℝ → ℂ := fun u => exp ((ρ : ℂ) * u * I) /
    (Real.sqrt (Real.cosh t - Real.cosh u) : ℝ)
  have hS : 0 < S := Real.sinh_pos_iff.mpr ht
  have ha : C - S = Real.exp (-t) := Real.cosh_sub_sinh _
  have hb : C + S = Real.exp t := Real.cosh_add_sinh _
  have hxa : StrictAntiOn x (Icc 0 π) := by
    intro u hu v hv huv
    exact add_lt_add_right (mul_lt_mul_of_pos_left (Real.strictAntiOn_cos hu hv huv) hS) C
  have hxc : Continuous x := by dsimp only [x]; fun_prop
  have hximage : x '' Ioo 0 π = Ioo (Real.exp (-t)) (Real.exp t) := by
    rw [hxc.continuousOn.image_Ioo_of_strictAntiOn Real.pi_pos.le hxa, ← ha, ← hb]
    simp [x, sub_eq_add_neg]
  have hdx (θ : ℝ) : HasDerivAt x (-(S * Real.sin θ)) θ := by
    simpa only [x, mul_neg] using ((Real.hasDerivAt_cos θ).const_mul S).const_add C
  have hd := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 π) (f := x) measurableSet_Ioo
    (fun θ _ => (hdx θ).hasDerivWithinAt) (hxa.injOn.mono Ioo_subset_Icc_self) G
  rw [hximage] at hd
  have hangles : (∫ θ in Ioo (0 : ℝ) π, (x θ : ℂ) ^ τ) =
      ∫ x in Ioo (Real.exp (-t)) (Real.exp t), G x := by
    rw [hd]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro θ hθ
    have hpos := mul_pos hS (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
    have hrad : Real.sqrt ((Real.exp t - x θ) * (x θ - Real.exp (-t))) = S * Real.sin θ := by
      rw [← ha, ← hb, ← Real.sqrt_sq hpos.le]
      congr 1
      dsimp only [x]
      linear_combination -(S ^ 2) * Real.sin_sq_add_cos_sq θ
    change (x θ : ℂ) ^ τ = |-(S * Real.sin θ)| • G (x θ)
    rw [abs_neg, abs_of_pos hpos, real_smul]
    dsimp only [G]
    rw [hrad]
    have hposC : ((S * Real.sin θ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
    rw [mul_comm, div_mul_cancel₀ _ hposC]
  have hlog := integral_image_eq_integral_abs_deriv_smul (s := Ioo (-t) t) (f := Real.exp)
    measurableSet_Ioo (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    Real.exp_injective.injOn G
  rw [Real.continuous_exp.image_Ioo_of_strictMono Real.exp_strictMono] at hlog
  have hpoint (u : ℝ) (hu : u ∈ Ioo (-t) t) :
      |Real.exp u| • G (Real.exp u) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * H u := by
    have hpos : 0 < C - Real.cosh u :=
      sub_pos.mpr (Real.cosh_lt_cosh.mpr (by rw [abs_of_pos ht]; exact abs_lt.mpr hu))
    have hE : (Real.exp t - Real.exp u) * (Real.exp u - Real.exp (-t)) =
        2 * Real.exp u * (C - Real.cosh u) := by
      have h₁ : Real.exp t * Real.exp (-t) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h₂ : Real.exp u * Real.exp (-u) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      dsimp only [C]
      rw [Real.cosh_eq, Real.cosh_eq]
      linear_combination -h₁ + h₂
    have hsqrt : Real.sqrt ((Real.exp t - Real.exp u) * (Real.exp u - Real.exp (-t))) =
        Real.sqrt 2 * Real.exp (u / 2) * Real.sqrt (C - Real.cosh u) := by
      rw [hE, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * Real.exp u),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      rw [← Real.sqrt_sq (Real.exp_pos (u / 2)).le, ← Real.exp_nat_mul]
      congr 2
      ring_nf
    have hpow :
        ((Real.exp u : ℝ) : ℂ) ^ τ = ((Real.exp (-(u / 2)) : ℝ) : ℂ) * exp ((ρ : ℂ) * u * I) := by
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos u).ne'),
        ← ofReal_log (Real.exp_pos u).le, Real.log_exp, ofReal_exp, ← exp_add]
      congr 1
      push_cast
      dsimp only [τ]
      ring
    have hhalf : (Real.exp u : ℂ) * (Real.exp (-(u / 2)) : ℂ) =
      (Real.exp (u / 2) : ℂ) := by
      rw [← ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    rw [abs_of_pos (Real.exp_pos u), real_smul]
    dsimp only [G, H]
    rw [hpow, hsqrt, ofReal_mul, ofReal_mul]
    calc
      _ = ((Real.exp u : ℂ) * (Real.exp (-(u / 2)) : ℂ)) *
          exp ((ρ : ℂ) * u * I) /
          (((Real.sqrt 2 : ℝ) : ℂ) * Real.exp (u / 2) * Real.sqrt (C - Real.cosh u)) := by ring
      _ = _ := by
        rw [hhalf]
        have hne : (Real.exp (u / 2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.exp_pos _).ne'
        have hf : ((Real.sqrt (C - Real.cosh u) : ℝ) : ℂ) ≠ 0 :=
          ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hpos).ne'
        have hg : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
          ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos (by norm_num)).ne'
        change (Real.exp (u / 2) : ℂ) * exp ((ρ : ℂ) * u * I) /
          (((Real.sqrt 2 : ℝ) : ℂ) * Real.exp (u / 2) * Real.sqrt (C - Real.cosh u)) =
          ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
            (exp ((ρ : ℂ) * u * I) / (Real.sqrt (C - Real.cosh u) : ℝ))
        field_simp
  rw [boostMatrixElement_zero_zero, intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_Ioc_eq_integral_Ioo]
  change _ * (∫ θ in Ioo (0 : ℝ) π, (x θ : ℂ) ^ τ) =
    _ * ∫ u in Ioo (-t) t, H u
  rw [hangles, hlog, setIntegral_congr_fun measurableSet_Ioo hpoint, integral_const_mul,
    mul_inv_rev]
  ring

/-- At zero spectral parameter, the principal spherical coefficient is strictly positive. -/
private theorem re_boostMatrixElement_neg_half_pos (t : ℝ) :
    0 < (boostMatrixElement (-1 / 2) 0 0 t).re := by
  let a := fun θ => Real.cosh t + Real.sinh t * Real.cos θ
  let f := fun θ => a θ ^ (-1 / 2 : ℝ)
  have ha (θ : ℝ) : 0 < a θ := FourierExpansion.laplaceKernel_pos t θ
  have hf : Continuous f :=
    (by dsimp only [a]; fun_prop : Continuous a).rpow_const (fun θ => Or.inl (ha θ).ne')
  have hpos (θ : ℝ) : 0 < f θ := Real.rpow_pos_of_pos (ha θ) _
  have hint := intervalIntegral.intervalIntegral_pos_of_pos
    (hf.intervalIntegrable 0 π) hpos Real.pi_pos
  rw [boostMatrixElement_zero_zero]
  have hEq (θ : ℝ) : (a θ : ℂ) ^ (-1 / 2 : ℂ) = (f θ : ℂ) := by
    rw [show (-1 / 2 : ℂ) = (((-1 / 2 : ℝ)) : ℂ) by norm_num, ← ofReal_cpow (ha θ).le]
  change 0 < (((π : ℝ) : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, (a θ : ℂ) ^ (-1 / 2 : ℂ)).re
  simp_rw [hEq]
  rw [intervalIntegral.integral_ofReal, ← ofReal_inv, ← ofReal_mul, ofReal_re]
  exact mul_pos (inv_pos.mpr Real.pi_pos) hint

/-- The real Mehler–Dirichlet weight is integrable despite its endpoint singularities. -/
theorem integrableOn_mehlerDirichletWeight (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u => (Real.sqrt (Real.cosh t - Real.cosh u))⁻¹) (Ioo (-t) t) := by
  have h := boostMatrixElement_zero_zero_eq_mehlerDirichlet 0 t ht
  simp only [ofReal_zero, zero_mul, exp_zero, one_div, ← ofReal_inv, integral_complex_ofReal] at h
  have hne : ∫ u in Ioo (-t) t, (Real.sqrt (Real.cosh t - Real.cosh u))⁻¹ ≠ 0 := by
    intro hz
    rw [hz, ofReal_zero, mul_zero, add_zero] at h
    simpa only [h, zero_re, lt_self_iff_false] using re_boostMatrixElement_neg_half_pos t
  exact Integrable.of_integral_ne_zero hne

/-- The total mass of the Mehler–Dirichlet weight is bounded uniformly in the boost parameter. -/
theorem integral_mehlerDirichletWeight_le (t : ℝ) (ht : 0 < t) :
    ∫ u in Ioo (-t) t, (Real.sqrt (Real.cosh t - Real.cosh u))⁻¹ ≤ π * Real.sqrt 2 := by
  let M := ∫ u in Ioo (-t) t, (Real.sqrt (Real.cosh t - Real.cosh u))⁻¹
  have hM : 0 ≤ M := integral_nonneg (fun _ => inv_nonneg.mpr (Real.sqrt_nonneg _))
  have h := boostMatrixElement_zero_zero_eq_mehlerDirichlet 0 t ht
  simp only [ofReal_zero, zero_mul, add_zero, exp_zero, one_div, ← ofReal_inv,
    integral_complex_ofReal, ← ofReal_mul] at h
  change boostMatrixElement (-1 / 2) 0 0 t = ((((π * Real.sqrt 2)⁻¹ * M : ℝ)) : ℂ) at h
  have hb : ‖boostMatrixElement (-1 / 2) 0 0 t‖ ≤ 1 := by
    simpa only [Int.cast_zero, Fin.val_zero, Nat.cast_zero, zero_div, sub_zero] using
      norm_boostMatrixElement_le_one (-1 / 2) (by norm_num [div_re]) 0 0 0 t
  have hπ : 0 < π * Real.sqrt 2 := by positivity
  rw [h, norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_pos.mpr hπ).le hM)] at hb
  simpa only [mul_one] using (inv_mul_le_iff₀ hπ).mp hb

/-- **Parseval for the Mehler–Fock transform.** For continuous `f` with compact support in
`(0, ∞)`, `∫ |f|² sinh t dt = ∫ |F(ρ)|² ρ tanh(πρ) dρ`. -/
theorem lintegral_mehlerFock (f : ℝ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi 0) :
    ∫⁻ t, ‖f t‖ₑ ^ 2 ∂sinhMeasure = ∫⁻ ρ, ‖mehlerFock f ρ‖ₑ ^ 2 ∂plancherelMeasure := by
  sorry

/-- **Inversion of the Mehler–Fock transform.** For smooth `f` with compact support in
`(0, ∞)` and `t > 0`, `f(t) = ∫₀^∞ F(ρ) 𝔓^{-1/2+iρ}_{00}(cosh t) ρ tanh(πρ) dρ`. -/
theorem mehlerFock_inversion (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioi 0) (t : ℝ) (ht : 0 < t) :
    f t = ∫ ρ, mehlerFock f ρ * boostMatrixElement (-1 / 2 + ρ * I) 0 0 t ∂plancherelMeasure := by
  sorry

/-- **Unitarity of the Mehler–Fock transform.** There is a unitary
`L²(sinh t dt) ≃ L²(ρ tanh(πρ) dρ)` that agrees with `mehlerFock` on continuous functions with
compact support in `(0, ∞)`. -/
theorem exists_mehlerFock_unitary :
    ∃ U : Lp ℂ 2 sinhMeasure ≃ₗᵢ[ℂ] Lp ℂ 2 plancherelMeasure,
      ∀ (f : ℝ → ℂ), Continuous f → HasCompactSupport f → tsupport f ⊆ Ioi 0 →
        ∀ hm : MemLp f 2 sinhMeasure,
          (U (hm.toLp f) : ℝ → ℂ) =ᵐ[plancherelMeasure] mehlerFock f := by
  sorry

/-- **Parseval for the Mehler–Fock transform of order `m`.** -/
theorem lintegral_mehlerFockOrder (m : ℤ) (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi 0) :
    ∫⁻ t, ‖f t‖ₑ ^ 2 ∂sinhMeasure = ∫⁻ ρ, ‖mehlerFockOrder m f ρ‖ₑ ^ 2 ∂plancherelMeasure := by
  sorry

/-- **Inversion of the Mehler–Fock transform of order `m`.** For smooth `f` with compact support
in `(0, ∞)` and `t > 0`, `f(t) = ∫₀^∞ F_m(ρ) 𝔓^{-1/2+iρ}_{m0}(cosh t) ρ tanh(πρ) dρ`. -/
theorem mehlerFockOrder_inversion (m : ℤ) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioi 0) (t : ℝ) (ht : 0 < t) :
    f t = ∫ ρ, mehlerFockOrder m f ρ * boostMatrixElement (-1 / 2 + ρ * I) m 0 t
      ∂plancherelMeasure := by
  sorry

end SFVK.SU11
