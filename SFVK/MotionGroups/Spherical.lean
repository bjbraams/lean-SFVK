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
import DLMF.Bessel.Basic.RegularizedSeries
import DLMF.Bessel.HankelAndNormalConvergence
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

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
-/

public noncomputable section

open Complex MeasureTheory Set
open scoped Real InnerProductSpace ComplexConjugate

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
theorem besselZonal_eq_besselJ {n : ℕ} (hn : 1 ≤ n) {lam : ℂ} (hlam : lam ∈ slitPlane) {r : ℝ}
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
  sorry

/-- The zonal function is smooth in `r`. -/
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

/-- The parameter is determined up to sign: `φ_λ = φ_μ` exactly when `λ² = μ²`. -/
theorem motionSphericalFunction_inj {n : ℕ} (hn : 1 ≤ n) (lam μ : ℂ) :
    motionSphericalFunction n lam = motionSphericalFunction n μ ↔ lam ^ 2 = μ ^ 2 := by
  constructor
  · intro h
    let i : Fin n := ⟨0, by omega⟩
    have hnorm (z : ℂ) (r : ℝ) : besselZonal n z ‖EuclideanSpace.single i r‖ =
        besselZonal n z r := by
      rw [besselZonal_eq_regularized, besselZonal_eq_regularized, EuclideanSpace.single,
        PiLp.norm_single, Real.norm_eq_abs]
      have hr : ((|r| : ℝ) : ℂ) ^ 2 = (r : ℂ) ^ 2 := by exact_mod_cast sq_abs r
      rw [mul_pow, mul_pow, hr]
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

/-- Bounded spherical functions: `Ω_n(λ, ·)` is bounded on `[0, ∞)` exactly for real `λ`. -/
theorem bounded_besselZonal_iff {n : ℕ} (hn : 1 ≤ n) (lam : ℂ) :
    (∃ C, ∀ r : ℝ, 0 ≤ r → ‖besselZonal n lam r‖ ≤ C) ↔ lam.im = 0 := by
  sorry

/-- For real `λ` the zonal function is bounded by `1`. -/
theorem norm_besselZonal_le_one {n : ℕ} (hn : 1 ≤ n) {lam : ℂ} (hlam : lam.im = 0) (r : ℝ) :
    ‖besselZonal n lam r‖ ≤ 1 := by
  have hlam' : lam = (lam.re : ℂ) := by
    apply Complex.ext <;> simp [hlam]
  let x := |lam.re * r|
  have hx : 0 ≤ x := abs_nonneg _
  have hz : besselZonal n lam r = besselZonal n 1 x := by
    rw [besselZonal_eq_regularized, besselZonal_eq_regularized, one_mul, hlam']
    have he : (x : ℂ) ^ 2 = ((lam.re : ℂ) * (r : ℂ)) ^ 2 := by
      norm_cast
      exact sq_abs (lam.re * r)
    rw [he]
  rw [hz]
  rcases hx.eq_or_lt with hx | hx
  · simp [← hx, besselZonal_zero_right hn]
  have hnpos : 0 < (n : ℝ) / 2 := by exact div_pos (by exact_mod_cast hn) two_pos
  let ν := (n : ℝ) / 2 - 1
  have hνbound : -(1 / 2 : ℝ) ≤ ν := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [ν]
    linarith
  have hΓ : ‖Complex.Gamma (n / 2)‖ = Real.Gamma ((n : ℝ) / 2) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
      Complex.Gamma_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos hnpos).le]
  have hν : (ν : ℂ) = (n : ℂ) / 2 - 1 := by simp [ν]
  have hpow : ‖(2 / (1 * (x : ℂ))) ^ (ν : ℂ)‖ = ((x / 2) ^ ν)⁻¹ := by
    rw [one_mul, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
      ← Complex.ofReal_cpow (by positivity), Complex.norm_real, Real.norm_of_nonneg (by positivity),
      ← inv_div, Real.inv_rpow (by positivity)]
  have h := DLMF.Bessel.norm_besselJ_le_exp_abs_im hνbound
    (z := (x : ℂ)) (Complex.ofReal_ne_zero.mpr hx.ne')
  rw [Complex.ofReal_im, abs_zero, Real.exp_zero, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hx.le] at h
  rw [besselZonal_eq_besselJ hn (by simp) hx, ← hν, norm_mul, norm_mul, hΓ, hpow]
  simp only [one_mul]
  calc
    _ ≤ Real.Gamma ((n : ℝ) / 2) * ((x / 2) ^ ν)⁻¹ *
          ((x / 2) ^ ν / Real.Gamma (ν + 1)) := by gcongr
    _ = 1 := by
      rw [show ν + 1 = (n : ℝ) / 2 by dsimp [ν]; ring]
      field_simp [ne_of_gt (Real.Gamma_pos_of_pos hnpos), ne_of_gt (Real.rpow_pos_of_pos
        (div_pos hx two_pos) ν)]

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

/-- Plane-wave expansion in `ℝ³` (DLMF 10.60.7 with 14.30.9), with lean-DLMF's spherical Bessel
function `j_l` and spherical harmonics `Y_{l,m}`: for `κ, r > 0` and the angle `γ` between the
directions `(θ, φ)` and `(θ', φ')`,
`e^{iκr cos γ} = 4π Σ_l i^l j_l(κr) Σ_m Y_{l,m}(θ, φ) conj Y_{l,m}(θ', φ')`. -/
theorem hasSum_planeWave_sphericalHarmonic {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (θ φ θ' φ' : ℝ) :
    HasSum (fun l : ℕ => 4 * π * I ^ l * DLMF.Bessel.sphericalJ l (κ * r) *
        ∑ m ∈ Finset.Icc (-(l : ℤ)) l,
          DLMF.Legendre.sphericalHarmonic l m θ φ *
            conj (DLMF.Legendre.sphericalHarmonic l m θ' φ'))
      (Complex.exp (I * (κ * r * (Real.sin θ * Real.sin θ' * Real.cos (φ - φ') +
        Real.cos θ * Real.cos θ') : ℝ))) := by
  sorry

end SFVK.MotionGroups
