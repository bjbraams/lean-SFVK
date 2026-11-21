/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bessel.Basic.Definitions
public import DLMF.Legendre.Basic.Harmonics
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import SFVK.MotionGroups.Basic.Zonal
public import SFVK.MotionGroups.MatrixElements
import DLMF.Bessel.Asymptotics.RightHalfPlane
import DLMF.Bessel.Basic.RegularizedSeries
import DLMF.Bessel.HankelAndNormalConvergence
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import DLMF.Bessel.Basic.RealModified
import DLMF.Bessel.RegularizedSeries
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Probability.Distributions.Uniform.Sphere.OneDimensional
import TauCeti.Probability.Distributions.VonMisesFisher.Normalizer

/-!
# The Gel'fand pair `(M(n), SO(n))` and the zonal Bessel functions

The zonal Bessel function `Ω_n(λ, r)` is `Γ(n/2) (2/(λr))^{n/2-1} J_{n/2-1}(λr)`, the mean of
the plane wave `e^{iλ⟨a, ξ⟩}` over the unit sphere, and the solution of the radial equation
regular at the origin; for `n ≥ 2` the spherical functions of `(M(n), SO(n))` are exactly the
`φ_λ`, `λ` determined up to sign, bounded exactly for real `λ`; at `n = 2` the zonal matrix
element of the circle model is `φ_R`; and in `ℝ³` the plane wave expands in spherical
harmonics. Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2,
§9.3.2 (8)–(10), p. 48, and §9.3.3 (3), pp. 48–49; Dieudonné, *Special Functions and Linear
Representations of Lie Groups*, §16, (188)–(193), pp. 55–57; DLMF 10.60.7 and 14.30.9.
The sphere mean follows by analytic continuation of Tau Ceti's von Mises–Fisher normalizer,
with the two-point sphere handled by its Rademacher projection formula. The boundedness
criterion uses lean-DLMF's modified Bessel asymptotics on a right-half-plane sector.
-/

public noncomputable section

open Complex MeasureTheory Set Filter Asymptotics
open scoped Real InnerProductSpace ComplexConjugate Topology

namespace SFVK.MotionGroups

local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The zonal series is a regularized hypergeometric function of the squared radius. -/
private theorem besselZonal_eq_regularized (n : ℕ) (lam : ℂ) (r : ℝ) :
    besselZonal n lam r = Complex.Gamma (n / 2) *
      regularizedHGFun (∅ : Multiset ℂ) {(n : ℂ) / 2} (-(lam * r) ^ 2 / 4) := by
  rw [besselZonal_def, DLMF.Bessel.regularized0F1_eq_tsum]
  congr 1
  apply tsum_congr
  intro k
  rw [mul_pow, neg_mul, add_comm ((n : ℂ) / 2)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Bessel form of the zonal function (Vilenkin–Klimyk Vol. 2 §9.3.2 (8)–(10), p. 48): for `λ`
in the slit plane and `r > 0`, `Ω_n(λ, r) = Γ(n/2) (2/(λr))^{n/2-1} J_{n/2-1}(λr)`. -/
theorem besselZonal_eq_besselJ {n : ℕ} {lam : ℂ} (hlam : lam ∈ slitPlane) {r : ℝ}
    (hr : 0 < r) :
    besselZonal n lam r =
      Complex.Gamma (n / 2) * (2 / (lam * r)) ^ ((n : ℂ) / 2 - 1) *
        besselJ ((n : ℂ) / 2 - 1) (lam * r) := by
  let z : ℂ := lam * r / 2
  let order : ℂ := (n : ℂ) / 2 - 1
  have hz : z = ((r / 2 : ℝ) : ℂ) * lam := by
    dsimp [z]
    push_cast
    ring
  have hz₀ : z ≠ 0 := by
    rw [hz]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hr two_pos).ne')
      (slitPlane_ne_zero hlam)
  have hzarg : z.arg ≠ π := by
    rw [hz, Complex.arg_real_mul _ (by positivity : 0 < r / 2)]
    exact (Complex.mem_slitPlane_iff_arg.mp hlam).1
  have horder : order + 1 = (n : ℂ) / 2 := by dsimp [order]; ring
  have hzinv : 2 / (lam * r) = z⁻¹ := by dsimp [z]; rw [inv_div]
  rw [besselZonal_eq_regularized, DLMF.Bessel.besselJ_eq_regularized]
  change _ = Complex.Gamma (↑n / 2) * (2 / (lam * r)) ^ order *
    (z ^ order * regularizedHGFun (∅ : Multiset ℂ) {order + 1} (-((lam * r) ^ 2 / 4)))
  rw [hzinv, Complex.inv_cpow _ _ hzarg, horder, mul_assoc, ← mul_assoc (z ^ order)⁻¹,
    inv_mul_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hz₀)), one_mul, neg_div]

/-- `Ω_n(λ, 0) = 1` for `n ≥ 1`. -/
@[simp]
theorem besselZonal_zero_right {n : ℕ} (hn : 1 ≤ n) (lam : ℂ) : besselZonal n lam 0 = 1 := by
  have hG : Complex.Gamma ((n : ℂ) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simpa [div_re] using (show 0 < (n : ℝ) / 2 by exact div_pos (by exact_mod_cast hn) two_pos)
  rw [besselZonal_eq_regularized, DLMF.Bessel.regularized0F1_eq_tsum]
  simp only [Complex.ofReal_zero, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero, zero_div]
  rw [tsum_eq_single 0]
  · simp [hG]
  · intro k hk
    simp [zero_pow hk]

/-- Integral over the sphere (Vilenkin–Klimyk Vol. 2 §9.3.2, p. 48): `Ω_n(λ, |a|)` is the mean
of `e^{iλ⟨a, ξ⟩}` over the unit sphere. -/
theorem besselZonal_eq_integral_sphere {n : ℕ} (hn : 1 ≤ n) (lam : ℂ)
    (a : EuclideanSpace ℝ (Fin n)) :
    besselZonal n lam ‖a‖ =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere univ).toReal⁻¹ *
        ∫ ξ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          Complex.exp (I * lam * (⟪a, (ξ : EuclideanSpace ℝ (Fin n))⟫_ℝ : ℝ))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  let μ := TauCeti.Probability.uniformSphereMeasure E
  have hnorm (f : S → ℂ) :
      ∫ x, f x ∂μ =
        ((volume : Measure E).toSphere univ).toReal⁻¹ *
          ∫ x, f x ∂(volume : Measure E).toSphere := by
    dsimp only [μ]
    rw [TauCeti.Probability.uniformSphereMeasure_def, integral_smul_measure,
      ENNReal.toReal_inv, Complex.real_smul]
  change besselZonal n lam ‖a‖ = _
  rw [← hnorm]
  have hdim : Module.finrank ℝ E = n := by simp [E]
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank ℝ E by omega)
  by_cases ha : a = 0
  · subst a
    simp [besselZonal_zero_right hn]
  let F (z : ℂ) := ∫ x : S, Complex.exp (z * (⟪a, (x : E)⟫_ℝ : ℝ)) ∂μ
  let G (z : ℂ) := Complex.Gamma (n / 2) *
    regularizedHGFun (∅ : Multiset ℂ) {(n : ℂ) / 2} ((z * (‖a‖ : ℂ)) ^ 2 / 4)
  have hF : AnalyticOnNhd ℂ F univ := by
    intro z _
    let σ (x : S) : ℂ := (⟪a, (x : E)⟫_ℝ : ℝ)
    have hs : Continuous σ := Complex.continuous_ofReal.comp
      (continuous_const.inner continuous_subtype_val)
    have hK : IsCompact (Set.range σ) := isCompact_range hs
    have hkernel (w : ℂ) (_ : w ∈ Set.range σ) :
        AnalyticAt ℂ (fun p : ℂ × ℂ => Complex.exp (p.1 * p.2)) (z, w) :=
      (analyticAt_fst.mul analyticAt_snd).cexp
    have h := TauCeti.analyticAt_integral_smul (μ := μ) (g := fun _ : S => (1 : ℂ))
      hK hs (fun x => mem_range_self x) hkernel (integrable_const 1)
    simpa only [one_smul] using h
  have hG : AnalyticOnNhd ℂ G univ := by
    intro z _
    exact analyticAt_const.mul <|
      (DLMF.Bessel.analyticAt_regularized0F1 _ _).comp (by fun_prop)
  have hreal (t : ℝ) (ht : 0 < t) : F (t : ℂ) = G t := by
    let b : E := t • a
    have hb : b ≠ 0 := smul_ne_zero ht.ne' ha
    have hbNorm : ‖b‖ = t * ‖a‖ := by
      rw [show b = t • a from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hFlift : F (t : ℂ) = Complex.ofReal (∫ x : S, Real.exp ⟪b, (x : E)⟫_ℝ ∂μ) := by
      rw [← integral_complex_ofReal (f := fun x : S => Real.exp ⟪b, (x : E)⟫_ℝ)]
      apply integral_congr_ae
      filter_upwards with x
      simp [b, real_inner_smul_left, Complex.ofReal_exp]
    by_cases h₁ : n = 1
    · have hm :=
        TauCeti.Probability.map_inner_uniformSphereMeasure_eq_map_rademacher_of_finrank_eq_one
          (hdim.trans h₁) b
      have hExp : ∫ x : S, Real.exp ⟪b, (x : E)⟫_ℝ ∂μ = Real.cosh ‖b‖ := by
        rw [← integral_map (f := Real.exp) (by fun_prop) (by fun_prop)]
        change (∫ y, Real.exp y ∂μ.map (fun x : S => ⟪b, (x : E)⟫_ℝ)) = _
        rw [hm, integral_map (by fun_prop) (by fun_prop),
          TauCeti.Probability.integral_rademacherMeasure]
        simp [Real.cosh_eq, smul_eq_mul]
        ring
      rw [hFlift, hExp, hbNorm]
      dsimp only [G]
      have hnC : (n : ℂ) = 1 := by exact_mod_cast h₁
      rw [hnC]
      have harg : (((t : ℂ) * ‖a‖) ^ 2 / 4) = -((((t : ℂ) * ‖a‖ * I) ^ 2) / 4) := by
        rw [mul_pow ((t : ℂ) * ‖a‖) I, Complex.I_sq]
        ring
      rw [harg, DLMF.Bessel.regularized0F1_half_eq_cos, Complex.cos_mul_I]
      have hΓ : Complex.Gamma (1 / 2 : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
      rw [← mul_div_assoc, mul_comm (Complex.Gamma (1 / 2)), mul_div_cancel_right₀ _ hΓ,
        Complex.ofReal_cosh, Complex.ofReal_mul]
    · have h₂ : 2 ≤ Module.finrank ℝ E := by omega
      have h := TauCeti.Probability.integral_exp_inner_uniformSphereMeasure_eq_besselI h₂ hb
      let ν : ℝ := (n : ℝ) / 2 - 1
      let x : ℝ := t * ‖a‖
      have hx : 0 < x := mul_pos ht (norm_pos_iff.mpr ha)
      have hnC : (ν : ℂ) + 1 = (n : ℂ) / 2 := by simp [ν]
      rw [hFlift, h, hdim, hbNorm]
      change (((Real.Gamma ((n : ℝ) / 2) * ((x / 2) ^ (-ν) * Real.besselI ν x)) : ℝ) : ℂ) =
        G t
      rw [Complex.ofReal_mul, Complex.ofReal_mul, ← Complex.Gamma_ofReal,
        ← DLMF.Bessel.besselI_ofReal ν hx.le, DLMF.Bessel.besselI,
        Complex.ofReal_cpow (by positivity : 0 ≤ x / 2) (-ν)]
      push_cast
      have hbase : (x : ℂ) / 2 ≠ 0 :=
        div_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne') (by norm_num)
      have hpow : ((x : ℂ) / 2) ^ (ν : ℂ) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr (Or.inl hbase)
      rw [Complex.cpow_neg, ← mul_assoc (((x : ℂ) / 2) ^ (ν : ℂ))⁻¹,
        inv_mul_cancel₀ hpow, one_mul, hnC]
      dsimp only [G, x]
      push_cast
      rfl
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hmap : Filter.Tendsto Complex.ofReal (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hpos.mono fun t ht => ?_⟩
    · simpa using (Complex.continuous_ofReal.continuousAt (x := 0)).tendsto.mono_left
        nhdsWithin_le_nhds
    · simp [ht.ne']
  have hf : ∃ᶠ z in 𝓝[≠] (0 : ℂ), F z = G z :=
    hmap.frequently (hpos.mono hreal).frequently
  have h := congrFun (AnalyticOnNhd.eq_of_frequently_eq hF hG hf) (I * lam)
  change besselZonal n lam ‖a‖ = F (I * lam)
  rw [h, besselZonal_eq_regularized]
  dsimp only [G]
  congr 2
  rw [mul_assoc I lam, mul_pow I, Complex.I_sq]
  ring

/-- The zonal function is real analytic in `r`. -/
theorem contDiff_besselZonal (n : ℕ) (lam : ℂ) : ContDiff ℝ ⊤ (besselZonal n lam) := by
  have hcomplex : ContDiff ℂ ⊤ (regularizedHGFun (∅ : Multiset ℂ) {(n : ℂ) / 2}) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (analyticAt_regularizedHGFun_zero x).contDiffAt
  change ContDiff ℝ ⊤ (fun r => besselZonal n lam r)
  simp_rw [besselZonal_eq_regularized]
  have hreal : ContDiff ℝ ⊤ (fun r : ℝ => (r : ℂ)) := Complex.ofRealCLM.contDiff
  have harg : ContDiff ℝ ⊤ (fun r : ℝ => -(lam * r) ^ 2 / 4) :=
    ((contDiff_const.mul hreal).pow 2).neg.div_const 4
  exact contDiff_const.mul ((hcomplex.restrict_scalars ℝ).comp harg)

/-- The derivative of the regularized series composed with the squared radius. -/
private theorem hasDerivAt_regularized_radial (c A : ℂ) (r : ℝ) :
    HasDerivAt (fun t : ℝ => regularizedHGFun (∅ : Multiset ℂ) {c} (A * (t : ℂ) ^ 2))
      (2 * A * r * regularizedHGFun ∅ {c + 1} (A * (r : ℂ) ^ 2)) r := by
  have h := ((DLMF.Bessel.hasDerivAt_regularized0F1 c (A * (r : ℂ) ^ 2)).comp
    (r : ℂ) ((hasDerivAt_pow 2 (r : ℂ)).const_mul A)).comp_ofReal
  convert h using 1
  simp only [Function.comp_apply]
  ring

/-- The second radial derivative, before applying the contiguous identity. -/
private theorem deriv_deriv_besselZonal (n : ℕ) (lam : ℂ) (r : ℝ) :
    let A : ℂ := -(lam ^ 2) / 4
    let c : ℂ := n / 2
    deriv (deriv (besselZonal n lam)) r =
      Complex.Gamma c * (2 * A * regularizedHGFun (∅ : Multiset ℂ) {c + 1} (A * (r : ℂ) ^ 2) +
        (2 * A * r) ^ 2 * regularizedHGFun ∅ {c + 1 + 1} (A * (r : ℂ) ^ 2)) := by
  dsimp only
  let A : ℂ := -(lam ^ 2) / 4
  let c : ℂ := n / 2
  have hform (t : ℝ) :
      besselZonal n lam t = Complex.Gamma c * regularizedHGFun (∅ : Multiset ℂ) {c}
        (A * (t : ℂ) ^ 2) := by
    rw [besselZonal_eq_regularized]
    congr 3
    dsimp [A]
    ring
  have hderiv : deriv (besselZonal n lam) = fun t : ℝ =>
      Complex.Gamma c * (2 * A * t *
        regularizedHGFun (∅ : Multiset ℂ) {c + 1} (A * (t : ℂ) ^ 2)) := by
    rw [funext hform]
    funext t
    exact ((hasDerivAt_regularized_radial c A t).const_mul _).deriv
  rw [hderiv]
  have hlin : HasDerivAt (fun t : ℝ => 2 * A * (t : ℂ)) (2 * A) r := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id (r : ℂ)).const_mul (2 * A)).comp_ofReal
  have h := ((hlin.mul (hasDerivAt_regularized_radial (c + 1) A r)).const_mul
    (Complex.Gamma c)).deriv
  change _ = Complex.Gamma c * _
  simp only [Pi.mul_apply] at h
  rw [h]
  ring

/-- Radial equation: `Ω″ + (n-1)/r Ω′ = -λ² Ω` for `r > 0`. -/
theorem besselZonal_ode (n : ℕ) (lam : ℂ) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (besselZonal n lam)) r + ((n : ℂ) - 1) / r * deriv (besselZonal n lam) r =
      -lam ^ 2 * besselZonal n lam r := by
  let A : ℂ := -(lam ^ 2) / 4
  let c : ℂ := n / 2
  have hform (t : ℝ) :
      besselZonal n lam t = Complex.Gamma c * regularizedHGFun (∅ : Multiset ℂ) {c}
        (A * (t : ℂ) ^ 2) := by
    rw [besselZonal_eq_regularized]
    congr 3
    dsimp [A]
    ring
  have hd : deriv (besselZonal n lam) r =
      Complex.Gamma c * (2 * A * r *
        regularizedHGFun (∅ : Multiset ℂ) {c + 1} (A * (r : ℂ) ^ 2)) := by
    rw [funext hform]
    exact ((hasDerivAt_regularized_radial c A r).const_mul _).deriv
  have hj := DLMF.Bessel.regularized0F1_contiguous c (A * (r : ℂ) ^ 2)
  rw [deriv_deriv_besselZonal, hd, hform, hj]
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  dsimp only [A, c]
  field_simp [hr']
  ring

/-- The spherical functions of `(M(n), SO(n))`, `n ≥ 2` (Dieudonné §16, (188)–(193),
pp. 55–57): for the Haar probability measure `ν` of `K`, `φ` is spherical exactly when it is
`φ_λ` for some `λ ∈ ℂ`. -/
theorem isSphericalFunction_motion_iff {n : ℕ} (hn : 2 ≤ n) (ν : Measure (rotationSubgroup n))
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (φ : MotionGroup n → ℂ) :
    Subgroup.IsSphericalFunction (rotationSubgroup n) ν φ ↔
      ∃ lam : ℂ, φ = motionSphericalFunction n lam := by
  sorry

/-- The zonal Bessel function depends only on the absolute value of the radius. -/
theorem besselZonal_abs (n : ℕ) (lam : ℂ) (r : ℝ) :
    besselZonal n lam |r| = besselZonal n lam r := by
  rw [besselZonal_eq_regularized, besselZonal_eq_regularized, mul_pow, mul_pow,
    show ((|r| : ℝ) : ℂ) ^ 2 = (r : ℂ) ^ 2 by exact_mod_cast sq_abs r]

/-- The parameter is determined up to sign: `φ_λ = φ_μ` exactly when `λ² = μ²`. -/
theorem motionSphericalFunction_inj {n : ℕ} (hn : 1 ≤ n) (lam μ : ℂ) :
    motionSphericalFunction n lam = motionSphericalFunction n μ ↔ lam ^ 2 = μ ^ 2 := by
  constructor
  · intro h
    let i : Fin n := ⟨0, by omega⟩
    have hnorm (z : ℂ) (r : ℝ) : besselZonal n z ‖EuclideanSpace.single i r‖ =
        besselZonal n z r := by
      rw [EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs, besselZonal_abs]
    have hg : besselZonal n lam = besselZonal n μ := by
      funext r
      have hr := congrFun h (⟨EuclideanSpace.single i r, 1⟩ : MotionGroup n)
      simpa only [motionSphericalFunction_def, hnorm] using hr
    let c : ℂ := (n : ℂ) / 2
    have hc : 0 < c.re := by
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      simpa [c, Complex.div_re] using div_pos hn' two_pos
    have hg₀ : Complex.Gamma c ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hc
    have hg₁ : Complex.Gamma (c + 1) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.one_re]; linarith)
    have hd (z : ℂ) : deriv (deriv (besselZonal n z)) 0 =
        Complex.Gamma c * (-(z ^ 2) / 2) * (Complex.Gamma (c + 1))⁻¹ := by
      rw [deriv_deriv_besselZonal]
      simp only [Complex.ofReal_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero,
        regularizedHGFun_zero, DLMF.Bessel.regularizedHGFunCoeff_empty,
        Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, one_div]
      dsimp [c]
      ring
    have hd' := congrArg (fun f : ℝ → ℂ => deriv (deriv f) 0) hg
    change deriv (deriv (besselZonal n lam)) 0 = deriv (deriv (besselZonal n μ)) 0 at hd'
    rw [hd, hd] at hd'
    have hcancel := mul_left_cancel₀ hg₀
      (mul_right_cancel₀ (inv_ne_zero hg₁) hd')
    linear_combination -2 * hcancel
  · intro h
    funext g
    simp only [motionSphericalFunction_def, besselZonal_eq_regularized, mul_pow, h]

/-- For real `λ` the zonal function is bounded by `1`. -/
theorem norm_besselZonal_le_one {n : ℕ} (hn : 1 ≤ n) {lam : ℂ}
    (hlam : lam.im = 0) (r : ℝ) : ‖besselZonal n lam r‖ ≤ 1 := by
  let E := EuclideanSpace ℝ (Fin n)
  let i : Fin n := ⟨0, by omega⟩
  let a : E := EuclideanSpace.single i r
  let μ := (volume : Measure E).toSphere
  have heven : besselZonal n lam ‖a‖ = besselZonal n lam r := by
    rw [show a = EuclideanSpace.single i r from rfl, EuclideanSpace.single, PiLp.norm_single,
      Real.norm_eq_abs, besselZonal_abs]
  rw [← heven, besselZonal_eq_integral_sphere hn]
  let f (ξ : Metric.sphere (0 : E) 1) : ℂ := Complex.exp (I * lam * (⟪a, (ξ : E)⟫_ℝ : ℝ))
  let v := (μ univ).toReal
  change ‖(v⁻¹ : ℝ) * ∫ ξ, f ξ ∂μ‖ ≤ 1
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hf (ξ : Metric.sphere (0 : E) 1) : ‖f ξ‖ = 1 := by
    simp [f, Complex.norm_exp, Complex.mul_re, Complex.mul_im, hlam]
  have hI : ‖∫ ξ, f ξ ∂μ‖ ≤ v := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp only [hf, integral_const, smul_eq_mul, mul_one, Measure.real_def, v]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hv)]
  refine (mul_le_mul_of_nonneg_left hI (inv_nonneg.mpr hv)).trans ?_
  by_cases h : v = 0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

/-- The zonal matrix element of the circle model is the spherical function at `n = 2`:
`D_{00}(g) = J₀(R|a|) = Ω₂(R, |a|)`. -/
theorem matrixElement_circleRep_zero_zero (R : ℂ) (g : MotionGroup 2) :
    (circleRep R).matrixElement fourierBasis 0 0 g = motionSphericalFunction 2 R g := by
  obtain ⟨φ, α, hg⟩ := exists_polar g
  conv_lhs => rw [hg, matrixElement_circleRep_polar]
  simp only [sub_self, zpow_zero, Int.cast_zero, zero_mul, neg_zero, Complex.exp_zero, one_mul,
    motionSphericalFunction_def]
  rw [besselZonal_eq_regularized, DLMF.Bessel.besselJ_eq_regularized]
  norm_num
  congr 1
  ring

/-- Bounded spherical functions: `Ω_n(λ, ·)` is bounded on `[0, ∞)` exactly for real `λ`. -/
theorem bounded_besselZonal_iff {n : ℕ} (hn : 1 ≤ n) (lam : ℂ) :
    (∃ C, ∀ r : ℝ, 0 ≤ r → ‖besselZonal n lam r‖ ≤ C) ↔ lam.im = 0 := by
  constructor
  swap
  · intro h
    exact ⟨1, fun r _ => norm_besselZonal_le_one hn h r⟩
  rintro ⟨C, hC⟩
  by_contra him
  let w : ℂ := if 0 < (I * lam).re then I * lam else -(I * lam)
  have hw : 0 < w.re := by
    dsimp only [w]
    split
    · assumption
    · rename_i h
      simp only [Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub] at h
      have hi : -lam.im < 0 := lt_of_le_of_ne (le_of_not_gt h) (neg_ne_zero.mpr him)
      simpa [Complex.mul_re] using neg_pos.mpr hi
  have hw₀ : w ≠ 0 := by intro h; simp [h] at hw
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw₀
  have hsq : w ^ 2 = -(lam ^ 2) := by
    dsimp only [w]
    split <;> simp only [neg_sq, mul_pow, I_sq, neg_one_mul]
  let Z (r : ℝ) : ℂ := w * r
  have hre (r : ℝ) : (Z r).re = w.re * r := by simp [Z, Complex.mul_re]
  have hpow (r : ℝ) : (Z r) ^ 2 / 4 = -(lam * r) ^ 2 / 4 := by
    simp only [Z, mul_pow, hsq, neg_mul]
  have hform (r : ℝ) :
      besselZonal n lam r = Complex.Gamma (n / 2) *
        regularizedHGFun (∅ : Multiset ℂ) {(n : ℂ) / 2} ((Z r) ^ 2 / 4) := by
    rw [hpow, besselZonal_eq_regularized]
  by_cases h₁ : n = 1
  · have hcosh (r : ℝ) : besselZonal n lam r = Complex.cosh (Z r) := by
      have hnC : (n : ℂ) = 1 := by exact_mod_cast h₁
      have hi : (Z r) ^ 2 / 4 = -((Z r * I) ^ 2 / 4) := by
        rw [mul_pow (Z r) I, I_sq]
        ring
      have hΓ : Complex.Gamma (1 / 2 : ℂ) ≠ 0 :=
        Complex.Gamma_ne_zero_of_re_pos (by norm_num)
      rw [hform, hnC, hi, DLMF.Bessel.regularized0F1_half_eq_cos, Complex.cos_mul_I,
        ← mul_div_assoc, mul_comm (Complex.Gamma (1 / 2)), mul_div_cancel_right₀ _ hΓ]
    have hl := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hw)
    obtain ⟨r, he, hr⟩ :=
      ((hl.eventually_gt_atTop (2 * C + 1)).and (eventually_gt_atTop (0 : ℝ))).exists
    have hneg : ‖Complex.exp (-Z r)‖ ≤ 1 := by
      rw [Complex.norm_exp, Complex.neg_re, hre, ← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_pos hw hr).le)
    have hi : Complex.exp (Z r) = 2 * Complex.cosh (Z r) - Complex.exp (-Z r) := by
      unfold Complex.cosh
      ring
    have hle := norm_sub_le (2 * Complex.cosh (Z r)) (Complex.exp (-Z r))
    rw [← hi, Complex.norm_exp, hre, norm_mul, Complex.norm_ofNat, ← hcosh] at hle
    change 2 * C + 1 < Real.exp (w.re * r) at he
    linarith [hC r hr.le]
  · let ν : ℝ := (n : ℝ) / 2 - 1
    have hν : -1 / 2 < (ν : ℂ).re := by
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
      rw [Complex.ofReal_re]
      dsimp only [ν]
      linarith
    let δ := w.re / ‖w‖
    have hδ : 0 < δ := div_pos hw hwn
    have hZ : Tendsto Z atTop (sectorAtTop δ) := by
      refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
      · apply (tendsto_id.const_mul_atTop hwn).congr'
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
        simp [Z, abs_of_nonneg hr]
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
        simp only [hre, Z, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr, δ]
        field_simp [hwn.ne']
        exact le_rfl
    let A (z : ℂ) := Complex.Gamma (n / 2) * (z / 2) ^ (-(ν : ℂ))
    let B (z : ℂ) := Complex.exp z * (2 * z) ^ (-1 / 2 : ℂ) / (Real.sqrt π : ℂ)
    have hA (r : ℝ) (hr : 0 < r) : A (Z r) * DLMF.Bessel.besselI ν (Z r) =
        besselZonal n lam r := by
      have hz : Z r / 2 ≠ 0 :=
        div_ne_zero (mul_ne_zero hw₀ (Complex.ofReal_ne_zero.mpr hr.ne')) (by norm_num)
      rw [hform, DLMF.Bessel.besselI]
      dsimp only [A]
      rw [Complex.cpow_neg, mul_assoc (Complex.Gamma _), ← mul_assoc ((Z r / 2) ^ (ν : ℂ))⁻¹,
        inv_mul_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl hz)), one_mul]
      congr 3
      simp [ν]
    have hbig := (((IsEquivalent.refl (u := A) (l := sectorAtTop δ)).mul
      (DLMF.Bessel.besselI_isEquivalent_sector hν hδ)).comp_tendsto hZ).isBigO_symm
    obtain ⟨K, hK, hbound⟩ := hbig.exists_pos
    let D := ‖Complex.Gamma ((n : ℂ) / 2)‖ * (‖w‖ / 2) ^ (-ν) *
      (2 * ‖w‖) ^ (-1 / 2 : ℝ) / Real.sqrt π
    have hΓ : Complex.Gamma ((n : ℂ) / 2) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      simpa [Complex.div_re] using half_pos hn'
    have hD : 0 < D := by dsimp only [D]; positivity
    have hnorm (r : ℝ) (hr : 0 < r) :
        ‖A (Z r) * B (Z r)‖ = D * (Real.exp (w.re * r) / r ^ (ν + 1 / 2)) := by
      have hz : ‖Z r‖ = ‖w‖ * r := by simp [Z, Complex.norm_real, abs_of_pos hr]
      have hhalf : (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by norm_num
      simp only [A, B, norm_mul, norm_div, Complex.norm_exp, hre, ← Complex.ofReal_neg,
        hhalf, Complex.norm_cpow_real, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Complex.norm_ofNat, hz]
      rw [show ‖w‖ * r / 2 = (‖w‖ / 2) * r by ring, ← mul_assoc (2 : ℝ),
        Real.mul_rpow (by positivity : 0 ≤ ‖w‖ / 2) hr.le,
        Real.mul_rpow (by positivity : 0 ≤ 2 * ‖w‖) hr.le,
        Real.rpow_add hr, ← div_div, ← mul_div_assoc]
      dsimp only [D]
      have hhalf' := Real.rpow_neg hr.le (1 / 2 : ℝ)
      rw [← neg_div] at hhalf'
      rw [Real.rpow_neg hr.le ν, hhalf']
      ring
    have hl := (tendsto_exp_mul_div_rpow_atTop (ν + 1 / 2) w.re hw).const_mul_atTop hD
    have he := hl.eventually_gt_atTop (K * C)
    have hx : ∃ r : ℝ, 0 < r ∧ ‖A (Z r) * B (Z r)‖ ≤
        K * ‖A (Z r) * DLMF.Bessel.besselI ν (Z r)‖ ∧
        K * C < D * (Real.exp (w.re * r) / r ^ (ν + 1 / 2)) :=
      ((eventually_gt_atTop 0).and (hbound.bound.and he)).exists
    obtain ⟨r, hr, hb, he⟩ := hx
    rw [hnorm r hr, hA r hr] at hb
    exact (not_lt_of_ge (hb.trans (mul_le_mul_of_nonneg_left (hC r hr.le) hK.le))) he

/-- Plane-wave expansion in `ℝ³` (DLMF 10.60.7 with 14.30.9), with lean-DLMF's spherical Bessel
function `j_l` and spherical harmonics `Y_{l,m}`: for `κ, r > 0` and the angle `γ` between the
directions `(θ, φ)` and `(θ', φ')` with polar angles in `[0, π]`,
`e^{iκr cos γ} = 4π Σ_l i^l j_l(κr) Σ_m Y_{l,m}(θ, φ) conj Y_{l,m}(θ', φ')`. -/
theorem hasSum_planeWave_sphericalHarmonic {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (θ φ θ' φ' : ℝ) (hθ : θ ∈ Set.Icc 0 π) (hθ' : θ' ∈ Set.Icc 0 π) :
    HasSum (fun l : ℕ => 4 * π * I ^ l * DLMF.Bessel.sphericalJ l (κ * r) *
        ∑ m ∈ Finset.Icc (-(l : ℤ)) l,
          DLMF.Legendre.sphericalHarmonic l m θ φ *
            conj (DLMF.Legendre.sphericalHarmonic l m θ' φ'))
      (Complex.exp (I * (κ * r * (Real.sin θ * Real.sin θ' * Real.cos (φ - φ') +
        Real.cos θ * Real.cos θ') : ℝ))) := by
  sorry

end SFVK.MotionGroups
