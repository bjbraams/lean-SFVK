/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.RankOne.Hyperbolic
public import SFVK.RankOne.JacobiTransform
import DLMF.Hypergeometric.Basic.CutPlane
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Spherical functions and harmonic analysis on real hyperbolic space

The spherical functions `φ_λ(x) = φ_λ^{(n/2−1, −1/2)}(arcosh x₀)` of `ℍⁿ`, Harish-Chandra's
integral over the boundary sphere, the eigenvalue equation, the spherical functions of the
Gel'fand pair `(SO₀(n, 1), SO(n))` and their classification, the spherical transform as a Jacobi
transform with its inversion and Plancherel constant `C_n = 2^{n−1}/(2π ω_{n−1})`, the Abel
transform, and the Helgason–Fourier transform with its inversion and Plancherel formulas.

Sources: Wawrzyńczyk, *Group Representations and Special Functions*, §11.3, (11.3.1),
(11.3.5)–(11.3.6), Theorem 11.3.1, pp. 401–402; §18.1, Example 1, pp. 611–613; Theorem 18.3.5,
p. 622; Theorem 18.6.1, p. 631; §18.7, (18.7.12)–(18.7.13), p. 640; Heckman–Schlichtkrull,
*Harmonic Analysis and Special Functions on Symmetric Spaces*, Part I §5.4, (5.4.2)–(5.4.5),
Theorem 5.4.2, pp. 83–84. The spherical eigenvalue proof uses the Gauss equation from
lean-DLMF.

## Main definitions

* `SFVK.RankOne.sphericalFunction`, `SFVK.RankOne.sphericalTransform`.

## Main results

* `SFVK.RankOne.sphericalFunction_basePoint`: `φ_λ(o) = 1` for `n ≥ 1`.
* `SFVK.RankOne.hyperbolicLaplacian_sphericalFunction`: the spherical eigenvalue equation.
* `SFVK.RankOne.sphericalTransform_radial`: the radial transform is a Jacobi transform.
* `SFVK.RankOne.abelTransform_neg` and `SFVK.RankOne.abelTransform_two`: the Abel transform.
-/

public noncomputable section

open Complex Filter Topology MeasureTheory Set DLMF.Hypergeometric DLMF.Legendre
open scoped Real Matrix ContDiff

namespace SFVK.RankOne

/-- The spherical function of `ℍⁿ`: `φ_λ(x) = φ_λ^{(n/2−1, −1/2)}(arcosh x₀)`. -/
@[expose]
def sphericalFunction (n : ℕ) (lam : ℂ) (x : Fin (n + 1) → ℝ) : ℂ :=
  jacobiFunction ((n : ℂ) / 2 - 1) (-1 / 2) lam (Real.arcosh (x 0))

theorem sphericalFunction_def (n : ℕ) (lam : ℂ) (x : Fin (n + 1) → ℝ) :
    sphericalFunction n lam x =
      jacobiFunction ((n : ℂ) / 2 - 1) (-1 / 2) lam (Real.arcosh (x 0)) :=
  rfl

/-- `φ_λ(o) = 1` for `n ≥ 1`. -/
theorem sphericalFunction_basePoint (n : ℕ) (hn : 1 ≤ n) (lam : ℂ) :
    sphericalFunction n lam (basePoint n) = 1 := by
  rw [sphericalFunction_def]
  have h0 : basePoint n 0 = 1 := by simp [basePoint_def]
  rw [h0, Real.arcosh_zero, Complex.ofReal_zero]
  refine jacobiFunction_zero _ _ _ fun k hk => ?_
  have h := congrArg Complex.re hk
  simp only [add_re, sub_re, div_re, natCast_re, natCast_im, one_re, neg_re] at h
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num at h
  nlinarith [h, (k.cast_nonneg : (0 : ℝ) ≤ k)]

/-- **Harish-Chandra's integral** (Wawrzyńczyk §18.1, Example 1, pp. 611–613): for `2 ≤ n` and
`x ∈ ℍⁿ`, `φ_λ(x) = ∫ [x, b̃]^{−(iλ + ρ)} dσ(b)`, `ρ = (n − 1)/2`. -/
theorem sphericalFunction_eq_average (n : ℕ) (hn : 2 ≤ n) (lam : ℂ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ hyperboloid n) :
    sphericalFunction n lam x =
      ⨍ b, (lorentz x (boundaryVector n b) : ℂ) ^ (-(I * lam + ((n : ℂ) - 1) / 2))
        ∂sphereMeasure n := by
  sorry

set_option maxHeartbeats 1500000 in
set_option linter.unusedVariables false in
/-- **Eigenfunction**: `Δφ_λ = −(λ² + ρ²) φ_λ` on `ℍⁿ`. -/
theorem hyperbolicLaplacian_sphericalFunction (n : ℕ) (hn : 2 ≤ n) (lam : ℂ)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ hyperboloid n) :
    hyperbolicLaplacian n (sphericalFunction n lam) x =
      -(lam ^ 2 + (((n : ℂ) - 1) / 2) ^ 2) * sphericalFunction n lam x := by
  have hL (y : Fin (n + 1) → ℝ) : lorentz y (basePoint n) = y 0 := by
    rw [lorentz_comm, lorentz_basePoint_left]
  let c := (n : ℂ) / 2
  let ρ := ((n : ℂ) - 1) / 2
  let a := (ρ + I * lam) / 2
  let b := (ρ - I * lam) / 2
  -- Express the eigenfunction in the time coordinate, which also works at the base point.
  let w (s : ℂ) := 1 - s ^ 2
  let G (s : ℝ) := Gamma c * regularizedGaussHypergeometric a b c (w s)
  have hArg (s : ℝ) (hs : 1 ≤ s) : -(Complex.sinh (Real.arcosh s)) ^ 2 = w s := by
    have hsq : 0 ≤ s ^ 2 - 1 := by nlinarith
    rw [← ofReal_sinh, Real.sinh_arcosh hs, ← ofReal_pow, Real.sq_sqrt hsq]
    simp only [w, ofReal_sub, ofReal_pow, ofReal_one, neg_sub]
  have hSphere {y : Fin (n + 1) → ℝ} (hy : y ∈ hyperboloid n) :
      sphericalFunction n lam y = G (y 0) := by
    have hρ : (n : ℂ) / 2 - 1 + -1 / 2 + 1 = ρ := by dsimp only [ρ]; ring
    have hc : (n : ℂ) / 2 - 1 + 1 = c := by dsimp only [c]; ring
    rw [sphericalFunction_def, jacobiFunction, hArg _ (one_le_apply_zero_of_mem_hyperboloid n hy),
      hc, hρ]
  have hC : EqOn (sphericalFunction n lam) (fun y => G (lorentz y (basePoint n))) (hyperboloid n) :=
    fun y hy => (hSphere hy).trans (congrArg G (hL y).symm)
  let s := x 0
  have hs : 0 < s := hx.2
  have hCut (t : ℝ) (ht : 0 < t) : w t ∈ cutPlane := by
    rw [mem_cutPlane, show 1 - w t = ((t ^ 2 : ℝ) : ℂ) by simp [w]]
    exact ofReal_mem_slitPlane.mpr (sq_pos_of_pos ht)
  have hW (z : ℂ) : HasDerivAt w (-2 * z) z := by
    have hd := (((hasDerivAt_id z).pow 2).const_sub (1 : ℂ))
    refine hd.congr_deriv ?_
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, neg_mul]
  have hGauss (a b c : ℂ) (t : ℝ) (ht : 0 < t) :
      HasDerivAt (fun r : ℝ => regularizedGaussHypergeometric a b c (w r))
        ((a * b * regularizedGaussHypergeometric (a + 1) (b + 1) (c + 1) (w t)) *
          (-2 * (t : ℂ))) t := by
    have hd := (differentiableAt_regularizedGaussHypergeometric a b c (hCut t ht)).hasDerivAt
    rw [deriv_regularizedGaussHypergeometric a b c (hCut t ht)] at hd
    exact (hd.comp (t : ℂ) (hW t)).comp_ofReal
  have hCont : ContDiffAt ℝ 2 G s := by
    have hWa : AnalyticAt ℂ w s := by dsimp only [w]; fun_prop
    exact (analyticAt_comp_ofReal (analyticAt_const.mul
      ((analyticAt_regularizedGaussHypergeometric a b c (hCut s hs)).comp hWa))).contDiffAt
  let g (t : ℝ) := regularizedGaussHypergeometric a b c (w t)
  let g₁ (t : ℝ) := a * b * regularizedGaussHypergeometric (a + 1) (b + 1) (c + 1) (w t)
  let g₂ (t : ℝ) := pochhammer a 2 * pochhammer b 2 *
    regularizedGaussHypergeometric (a + 2) (b + 2) (c + 2) (w t)
  have hFirst (t : ℝ) (ht : 0 < t) :
      HasDerivAt G (Gamma c * (g₁ t * (-2 * (t : ℂ)))) t :=
    (hGauss a b c t ht).const_mul (Gamma c)
  have hG₁ : HasDerivAt g₁ (g₂ s * (-2 * (s : ℂ))) s := by
    have h := (hGauss (a + 1) (b + 1) (c + 1) s hs).const_mul (a * b)
    refine h.congr_deriv ?_
    simp only [g₂, pochhammer_succ, pochhammer_zero, Nat.cast_one, Nat.cast_zero, add_zero, one_mul]
    ring_nf
  have hSecond : iteratedDeriv 2 G s = Gamma c *
      (4 * (s : ℂ) ^ 2 * g₂ s - 2 * g₁ s) := by
    have heq : deriv G =ᶠ[𝓝 s] fun t : ℝ => Gamma c * (g₁ t * (-2 * (t : ℂ))) := by
      filter_upwards [Ioi_mem_nhds hs] with t ht
      exact (hFirst t ht).deriv
    have hLinear : HasDerivAt (fun t : ℝ => -2 * (t : ℂ)) (-2) s := by
      simpa only [Complex.ofRealCLM_apply, ofReal_one, mul_one] using
        (Complex.ofRealCLM.hasDerivAt).const_mul (-2 : ℂ)
    have h := (hG₁.mul hLinear).const_mul (Gamma c)
    rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
    refine h.deriv.trans ?_
    ring_nf
  have hBase : lorentz (basePoint n) (basePoint n) = 1 := (basePoint_mem_hyperboloid n).1
  have hCN : ContDiffAt ℝ 2 G (lorentz x (basePoint n)) := by rwa [hL]
  have hLap := hyperbolicLaplacian_comp_lorentz n G (basePoint n) x hx hCN
  rw [hBase, hL] at hLap
  rw [hyperbolicLaplacian_congr hC hx, hLap, hSphere hx]
  change (s ^ 2 - 1) • iteratedDeriv 2 G s + ((n : ℝ) * s) • deriv G s = _ * G s
  rw [hSecond, (hFirst s hs).deriv]
  simp only [Complex.real_smul, ofReal_sub, ofReal_mul, ofReal_pow, ofReal_natCast, ofReal_one]
  have hGaussODE : w s * (1 - w s) * g₂ s +
      (c - (a + b + 1) * w s) * g₁ s - a * b * g s = 0 :=
    regularizedGaussHypergeometric_ode a b c (hCut s hs)
  have hEigen : lam ^ 2 + ρ ^ 2 = 4 * a * b := by
    dsimp only [a, b]
    linear_combination lam ^ 2 * Complex.I_sq
  have hParam : a + b + 1 = c + 1 / 2 := by dsimp only [a, b, ρ, c]; ring
  rw [hParam] at hGaussODE
  change _ = -(lam ^ 2 + ρ ^ 2) * (Gamma c * g s)
  rw [hEigen]
  dsimp only [w, c] at hGaussODE ⊢
  linear_combination (-4 * Gamma ((n : ℂ) / 2)) * hGaussODE

section Gelfand

attribute [local instance] borel

/-- **`φ_λ ∘ (g ↦ g o)` is a spherical function** of the Gel'fand pair. -/
theorem isSphericalFunction_sphericalFunction (n : ℕ) (hn : 2 ≤ n) (lam : ℂ)
    (ν : Measure (rotationSubgroup n)) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] :
    Subgroup.IsSphericalFunction (rotationSubgroup n) ν
      fun g => sphericalFunction n lam (orbitMap n g) := by
  sorry

/-- **Classification** (Wawrzyńczyk Theorem 18.3.5, p. 622): every spherical function is a
`φ_λ ∘ (g ↦ g o)`. -/
theorem isSphericalFunction_iff (n : ℕ) (hn : 2 ≤ n) (ν : Measure (rotationSubgroup n))
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (φ : lorentzGroup n → ℂ) :
    Subgroup.IsSphericalFunction (rotationSubgroup n) ν φ ↔
      ∃ lam : ℂ, φ = fun g => sphericalFunction n lam (orbitMap n g) := by
  sorry

/-- **`φ_λ = φ_μ` exactly when `μ = ±λ`.** -/
theorem sphericalFunction_comp_orbitMap_eq_iff (n : ℕ) (hn : 2 ≤ n) (lam μ : ℂ) :
    ((fun g => sphericalFunction n lam (orbitMap n g)) =
      fun g => sphericalFunction n μ (orbitMap n g)) ↔ (μ = lam ∨ μ = -lam) := by
  sorry

end Gelfand

/-- The spherical transform `Sf(λ) = ∫ f(x) φ_λ(x) dm(x)`. -/
@[expose]
def sphericalTransform (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℂ) (lam : ℂ) : ℂ :=
  ∫ x, f x * sphericalFunction n lam x ∂hyperbolicMeasure n

theorem sphericalTransform_def (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℂ) (lam : ℂ) :
    sphericalTransform n f lam = ∫ x, f x * sphericalFunction n lam x ∂hyperbolicMeasure n :=
  rfl

set_option linter.unusedVariables false in
/-- **The spherical transform is a Jacobi transform**: for radial `f = F ∘ d(o, ·)`,
`Sf(λ) = ω_{n−1} 2^{1−n} F̃(λ)` at `(α, β) = (n/2 − 1, −1/2)`. -/
theorem sphericalTransform_radial (n : ℕ) (hn : 2 ≤ n) (F : ℝ → ℂ) (hF : Continuous F)
    (hFs : HasCompactSupport F) (lam : ℂ) :
    sphericalTransform n (fun x => F (Real.arcosh (x 0))) lam =
      (sphereArea n / 2 ^ (n - 1) : ℝ) * jacobiTransform ((n : ℝ) / 2 - 1) (-1 / 2) F lam := by
  let φ (r : ℝ) := jacobiFunction ((n : ℂ) / 2 - 1) (-1 / 2) lam r
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr
    (fun r => (analyticAt_jacobiFunction_radius ((n : ℂ) / 2 - 1) (-1 / 2) lam r).continuousAt)
  have h := integral_hyperbolicMeasure_radial n (by omega) (fun r => F r * φ r)
    (hF.measurable.mul hφ.measurable)
  simp only [sphericalTransform_def, sphericalFunction_def, φ] at h ⊢
  rw [h, jacobiTransform_def]
  have hcast : (((n : ℝ) / 2 - 1 : ℝ) : ℂ) = (n : ℂ) / 2 - 1 := by push_cast; ring
  have hhalf : ((-1 / 2 : ℝ) : ℂ) = -1 / 2 := by push_cast; ring
  have hpow : 2 * ((n : ℝ) / 2 - 1) + 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hwt (t : ℝ) :
      jacobiWeight ((n : ℝ) / 2 - 1) (-1 / 2) t = (2 : ℝ) ^ (n - 1) *
        Real.sinh t ^ (n - 1) := by
    rw [jacobiWeight_def, hpow, Real.rpow_natCast, mul_pow]
    norm_num
  simp only [hwt, hcast, hhalf, ofReal_mul, ofReal_pow, ofReal_ofNat]
  have hc : (2 : ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  simp_rw [ofReal_div, ofReal_pow, ofReal_ofNat, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by field_simp [hc]

/-- **Inversion for radial functions**: `F(t) = C_n ∫₀^∞ Sf(λ) φ_λ(t) |c(λ)|⁻² dλ`. -/
theorem sphericalTransform_inversion (n : ℕ) (hn : 2 ≤ n) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hFs : HasCompactSupport F) (heven : ∀ t, F (-t) = F t) (t : ℝ) :
    F t = plancherelConstant n * ∫ lam in Ioi (0 : ℝ),
      sphericalTransform n (fun x => F (Real.arcosh (x 0))) lam *
        jacobiFunction ((n : ℝ) / 2 - 1) (-1 / 2) lam t *
        (‖cFunction ((n : ℝ) / 2 - 1) (-1 / 2) lam‖⁻¹ ^ 2 : ℝ) := by
  sorry

/-- **Plancherel for radial functions**: `∫ |f|² dm = C_n ∫₀^∞ |Sf(λ)|² |c(λ)|⁻² dλ`. -/
theorem sphericalTransform_plancherel (n : ℕ) (hn : 2 ≤ n) (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hFs : HasCompactSupport F) (heven : ∀ t, F (-t) = F t) :
    ∫ x, ‖F (Real.arcosh (x 0))‖ ^ 2 ∂hyperbolicMeasure n =
      plancherelConstant n * ∫ lam in Ioi (0 : ℝ),
        ‖sphericalTransform n (fun x => F (Real.arcosh (x 0))) lam‖ ^ 2 *
          ‖cFunction ((n : ℝ) / 2 - 1) (-1 / 2) lam‖⁻¹ ^ 2 := by
  sorry

/-- **The Abel transform is even.** -/
theorem abelTransform_neg (m : ℕ) (F : ℝ → ℂ) (s : ℝ) :
    abelTransform m F (-s) = abelTransform m F s := by
  let g (v : Fin m → ℝ) :=
    F (Real.arcosh (Real.cosh s + (∑ i, v i ^ 2) * Real.exp (-s) / 2))
  have hfun : (fun v : Fin m → ℝ =>
      F (Real.arcosh (Real.cosh (-s) + (∑ i, v i ^ 2) * Real.exp (- -s) / 2))) =
      fun v => g (Real.exp s • v) := by
    funext v
    have hsum : (∑ i, (Real.exp s • v : Fin m → ℝ) i ^ 2) =
        Real.exp s ^ 2 * ∑ i, v i ^ 2 := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
    simp only [g, Real.cosh_neg, neg_neg, hsum]
    have he : Real.exp s ^ 2 * Real.exp (-s) = Real.exp s := by
      rw [pow_two, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    congr 3
    calc
      _ = (∑ i, v i ^ 2) * (Real.exp s ^ 2 * Real.exp (-s)) / 2 := by rw [he]
      _ = _ := by ring
  simp only [abelTransform_def, hfun]
  rw [Measure.integral_comp_smul_of_nonneg volume g (Real.exp s) (hR := (Real.exp_pos s).le),
    Module.finrank_pi, Fintype.card_fin]
  have hexp : (Real.exp s ^ m)⁻¹ = Real.exp (-(m * s)) := by
    rw [Real.exp_neg, Real.exp_nat_mul]
  rw [hexp, Complex.real_smul, ← mul_assoc, ← ofReal_mul, ← Real.exp_add]
  congr 2
  ring_nf

/-- **Spherical transform = Fourier ∘ Abel**: `S(F ∘ d(o, ·))(λ) = ∫ 𝒜F(s) e^{iλs} ds`. -/
theorem sphericalTransform_eq_integral_abelTransform (m : ℕ) (F : ℝ → ℂ) (hF : Continuous F)
    (hFs : HasCompactSupport F) (lam : ℂ) :
    sphericalTransform (m + 1) (fun x => F (Real.arcosh (x 0))) lam =
      ∫ s, abelTransform m F s * exp (I * lam * s) := by
  sorry

set_option linter.unusedVariables false in
/-- **The Abel transform of `ℍ³`**: `𝒜F(s) = 2π ∫_{cosh s}^∞ F(arcosh u) du`. -/
theorem abelTransform_two (F : ℝ → ℂ) (hF : Continuous F) (hFs : HasCompactSupport F) (s : ℝ) :
    abelTransform 2 F s = 2 * π * ∫ u in Ioi (Real.cosh s), F (Real.arcosh u) := by
  let u (r : ℝ) := Real.cosh s + r ^ 2 * Real.exp (-s) / 2
  let g (r : ℝ) := F (Real.arcosh (u r))
  have hunorm (v : Fin 2 → ℝ) :
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = ∑ i, v i ^ 2 :=
    EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 v)
  have hVol : (volume : Measure (EuclideanSpace ℝ (Fin 2))).real (Metric.ball 0 1) = π := by
    rw [Measure.real_def, EuclideanSpace.volume_ball_fin_two]
    simp [ENNReal.toReal_ofReal Real.pi_pos.le]
  have hchange : u '' Ioi 0 = Ioi (Real.cosh s) := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact lt_add_of_pos_right _
        (div_pos (mul_pos (sq_pos_of_pos hr) (Real.exp_pos _)) (two_pos : (0 : ℝ) < 2))
    · intro hx
      have hpos : 0 < (x - Real.cosh s) * 2 / Real.exp (-s) := by
        exact div_pos (mul_pos (sub_pos.mpr hx) (by norm_num)) (Real.exp_pos _)
      refine ⟨Real.sqrt ((x - Real.cosh s) * 2 / Real.exp (-s)),
        Real.sqrt_pos.mpr hpos, ?_⟩
      dsimp only [u]
      rw [Real.sq_sqrt hpos.le]
      field_simp
      ring
  have hMono : MonotoneOn u (Ioi 0) := by
    intro r hr q hq hle
    dsimp only [u]
    apply add_le_add_right
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (le_of_lt hr) hle _) (Real.exp_pos _).le
  have hDeriv (r : ℝ) : HasDerivAt u (r * Real.exp (-s)) r := by
    have h := ((((hasDerivAt_id r).pow 2).mul_const (Real.exp (-s))).div_const 2).const_add
      (Real.cosh s)
    convert h using 1
    all_goals simp [u]
    all_goals ring_nf
  have hIntegral :
      ∫ x in Ioi (Real.cosh s), F (Real.arcosh x) =
        Real.exp (-s) • ∫ r in Ioi (0 : ℝ), r • g r := by
    conv_lhs => rw [← hchange, integral_image_eq_integral_deriv_smul_of_monotoneOn
      measurableSet_Ioi (fun r _ => (hDeriv r).hasDerivWithinAt) hMono]
    rw [← integral_smul]
    apply integral_congr_ae
    exact ae_of_all _ fun r => by simp only [g, smul_smul, mul_comm]
  rw [abelTransform_def, hIntegral]
  have hpow : -(↑(2 : ℕ) * s / 2) = -s := by push_cast; ring
  rw [hpow]
  have hLp : (∫ v : Fin 2 → ℝ, F (Real.arcosh
      (Real.cosh s + (∑ i, v i ^ 2) * Real.exp (-s) / 2))) =
      ∫ v : EuclideanSpace ℝ (Fin 2), g ‖v‖ := by
    simpa only [Function.comp_apply, g, u, hunorm] using
      (PiLp.volume_preserving_toLp (Fin 2)).integral_comp
        ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurableEmbedding)
        (fun v : EuclideanSpace ℝ (Fin 2) => g ‖v‖)
  rw [hLp, integral_fun_norm_addHaar volume g, finrank_euclideanSpace, Fintype.card_fin, hVol]
  simp only [Nat.reduceSub, pow_one, nsmul_eq_mul, Complex.real_smul]
  ring

/-- **Inversion for the Helgason–Fourier transform**:
`f(x) = C_n ∫₀^∞ ∫ f̂(λ, b) [x, b̃]^{−iλ−ρ} dσ(b) |c(λ)|⁻² dλ` on `ℍⁿ`. -/
theorem helgasonFourier_inversion (n : ℕ) (hn : 2 ≤ n) (f : (Fin (n + 1) → ℝ) → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ hyperboloid n) :
    f x = plancherelConstant n * ∫ lam in Ioi (0 : ℝ),
      (⨍ b, helgasonFourier n f lam b *
          (lorentz x (boundaryVector n b) : ℂ) ^ (-(I * lam) - ((n : ℂ) - 1) / 2)
        ∂sphereMeasure n) *
        (‖cFunction ((n : ℝ) / 2 - 1) (-1 / 2) lam‖⁻¹ ^ 2 : ℝ) := by
  sorry

/-- **Plancherel for the Helgason–Fourier transform**:
`∫ |f|² dm = C_n ∫₀^∞ ∫ |f̂(λ, b)|² dσ(b) |c(λ)|⁻² dλ`. -/
theorem helgasonFourier_plancherel (n : ℕ) (hn : 2 ≤ n) (f : (Fin (n + 1) → ℝ) → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) :
    ∫ x, ‖f x‖ ^ 2 ∂hyperbolicMeasure n =
      plancherelConstant n * ∫ lam in Ioi (0 : ℝ),
        (⨍ b, ‖helgasonFourier n f lam b‖ ^ 2 ∂sphereMeasure n) *
          ‖cFunction ((n : ℝ) / 2 - 1) (-1 / 2) lam‖⁻¹ ^ 2 := by
  sorry

/-- **The transform diagonalizes `Δ`**: `(Δf)^(λ, b) = −(λ² + ρ²) f̂(λ, b)`. -/
theorem helgasonFourier_hyperbolicLaplacian (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℂ)
    (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) (lam : ℂ)
    (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    helgasonFourier n (hyperbolicLaplacian n f) lam b =
      -(lam ^ 2 + (((n : ℂ) - 1) / 2) ^ 2) * helgasonFourier n f lam b := by
  sorry

end SFVK.RankOne
