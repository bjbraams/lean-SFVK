/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

import DLMF.Gamma.MellinBarnes
import DLMF.Gamma.Integrals.ExponentialMellin
import DLMFMathlib.Analysis.MellinCubicLaplace
import DLMFMathlib.Analysis.MellinParseval
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import SFVK.AffineHeisenberg.Basic

/-!
# The affine group, the Mellin transform and the Gamma function

The affine action multiplies by `e^{λ b x}` and dilates by `a > 0`. The Mellin transform
diagonalizes dilation, converts the infinitesimal operators to shifts and multipliers,
and yields a Gamma kernel on a vertical contour. The addition identities are forms
of the beta integral.

Sources: Vilenkin–Klimyk Vol. 1 §3.4, pp. 128–135; Klimyk–Vilenkin Ch. 4 §1.2, p. 204, §3.1, p. 218.
The two beta integrals use lean-DLMF's Mellin and Mellin–Barnes formulas.
-/

public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open scoped Real ComplexConjugate InnerProductSpace ENNReal

/-- The affine action of a product is the composition of the two affine actions. -/
theorem affineAction_mul (lam : ℂ) (g h : AxB) (f : ℝ → ℂ) :
    affineAction lam (g * h) f = affineAction lam g (affineAction lam h f) := by
  funext x
  simp only [affineAction, AxB.dilation_mul, AxB.translation_mul]
  rw [show lam * ((g.a * h.b + g.b : ℝ) : ℂ) * x =
      lam * g.b * x + lam * h.b * ((g.a * x : ℝ) : ℂ) by push_cast; ring, Complex.exp_add,
    mul_assoc, mul_comm g.a h.a, mul_assoc]
  rw [mul_assoc h.a]

/-- The identity affine transformation acts as the identity operator. -/
@[simp]
theorem affineAction_one (lam : ℂ) (f : ℝ → ℂ) : affineAction lam 1 f = f := by
  funext x
  simp [affineAction]

/-- An imaginary affine parameter gives the pointwise action of the affine cocycle. -/
theorem affineAction_mul_I (ρ : ℝ) :
    affineAction (ρ * Complex.I) = multiplierAction (axbCocycle ρ) := by
  funext g f x
  simp only [affineAction, multiplierAction, axbCocycle]
  have hx : g⁻¹ • x = g.a * x := by
    show x / g⁻¹.a = g.a * x
    rw [AxB.dilation_inv, div_inv_eq_mul, mul_comm]
  rw [hx]
  congr 2
  push_cast
  ring

/-- The Mellin transform of a dilation by `a > 0` is multiplied by `a^{-w}`. -/
theorem mellin_affineAction_dilation (lam : ℂ) (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ) (w : ℂ) :
    mellin (affineAction lam ⟨a, 0, ha⟩ f) w = (a : ℂ) ^ (-w) * mellin f w := by
  have : affineAction lam ⟨a, 0, ha⟩ f = fun x => f (a * x) := by
    funext x
    simp [affineAction]
  rw [this, mellin_comp_mul_left f w ha, smul_eq_mul]

/-- Multiplication by the variable shifts the Mellin parameter by one. -/
theorem mellin_mul_variable (f : ℝ → ℂ) (w : ℂ) :
    mellin (fun x => (x : ℂ) * f x) w = mellin f (w + 1) := by
  simpa only [cpow_one, smul_eq_mul] using mellin_cpow_smul f w 1

/-- Compact support disjoint from zero stays compact on the positive half-line. -/
theorem isCompact_tsupport_inter_Ioi {f : ℝ → ℂ}
    (hfc : HasCompactSupport f) (hf0 : (0 : ℝ) ∉ tsupport f) :
    IsCompact (tsupport f ∩ Ioi 0) := by
  have he : tsupport f ∩ Ioi 0 = tsupport f ∩ Ici 0 := by
    ext x
    constructor
    · rintro ⟨hx, hp⟩
      exact ⟨hx, hp.le⟩
    · rintro ⟨hx, hp⟩
      have hn : x ≠ 0 := by
        rintro rfl
        exact hf0 hx
      exact ⟨hx, lt_of_le_of_ne hp hn.symm⟩
  rw [he]
  exact hfc.inter_right isClosed_Ici

/-- The logarithmic coordinate transports compact positive support to compact support. -/
theorem hasCompactSupport_mellinLog (f : ℝ → ℂ) (w : ℂ)
    (hc : IsCompact (tsupport f ∩ Ioi 0)) :
    HasCompactSupport (fun u : ℝ => Complex.exp (-w * u) * f (Real.exp (-u))) := by
  have hlog : ContinuousOn (fun x : ℝ => -Real.log x) (tsupport f ∩ Ioi 0) :=
    Real.continuousOn_log.neg.mono (fun _ hx => hx.2.ne')
  have hbound : IsCompact ((fun x : ℝ => -Real.log x) '' (tsupport f ∩ Ioi 0)) :=
    hc.image_of_continuousOn hlog
  apply hbound.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hbound.isClosed
  intro u hu
  refine ⟨Real.exp (-u), ⟨?_, Real.exp_pos _⟩, by simp⟩
  refine subset_closure ?_
  intro hf
  exact hu (by dsimp only; rw [hf, mul_zero])

/-- The Euler derivative is diagonal in the Mellin transform. -/
theorem mellin_mul_deriv (f : ℝ → ℂ) (w : ℂ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (hf0 : (0 : ℝ) ∉ tsupport f) :
    mellin (fun x => (x : ℂ) * deriv f x) w = -w * mellin f w := by
  let H : ℝ → ℂ := fun u => Complex.exp (-w * u) * f (Real.exp (-u))
  have hHc : ContDiff ℝ 1 H := by
    dsimp only [H]
    have he : ContDiff ℝ 1 (fun u : ℝ => Complex.exp (-w * u)) :=
      ((contDiff_const (c := -w)).mul
        (Complex.ofRealCLM.contDiff : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ)))).cexp
    exact he.mul (hf.comp (by fun_prop))
  have hHcs : HasCompactSupport H :=
    hasCompactSupport_mellinLog f w (isCompact_tsupport_inter_Ioi hfc hf0)
  have hd (u : ℝ) : deriv H u = -w * H u -
      Complex.exp (-w * u) * ((Real.exp (-u) : ℂ) * deriv f (Real.exp (-u))) := by
    have hleft : HasDerivAt (fun u : ℝ => Complex.exp (-w * u))
        (Complex.exp (-w * u) * -w) u := by
      simpa only [id_eq, mul_one] using
        ((hasDerivAt_id (u : ℂ)).const_mul (-w)).comp_ofReal.cexp
    have hright : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) u := by
      simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using ((hasDerivAt_id u).neg).exp
    have hdiff := ((hf.differentiable (by norm_num) (Real.exp (-u))).hasDerivAt.scomp u hright)
    have hderiv : HasDerivAt H
        ((Complex.exp (-w * u) * -w) * f (Real.exp (-u)) +
          Complex.exp (-w * u) * (-Real.exp (-u) • deriv f (Real.exp (-u)))) u := by
      convert hleft.mul hdiff using 1 <;> rfl
    rw [hderiv.deriv]
    simp only [H, Complex.real_smul, ofReal_neg]
    ring
  have hDi : Integrable (deriv H) :=
    (hHc.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport hHcs.deriv
  have hHi : Integrable H := hHc.continuous.integrable_of_hasCompactSupport hHcs
  have hint : ∫ u, deriv H u = 0 := by
    rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hDi,
      compl_Ioi, hHcs.integral_Ioi_deriv_eq hHc, hHcs.integral_Iic_deriv_eq hHc, neg_add_cancel]
  have hfun (u : ℝ) : Complex.exp (-w * u) *
        ((Real.exp (-u) : ℂ) * deriv f (Real.exp (-u))) = -w * H u - deriv H u := by
    rw [hd]
    ring
  rw [mellin_eq_integral_exp_mul, mellin_eq_integral_exp_mul]
  simp_rw [hfun]
  rw [integral_sub (hHi.const_mul _) hDi, integral_const_mul, hint, sub_zero]

/-- A differentiation without the factor of the variable lowers the Mellin parameter. -/
theorem mellin_deriv (f : ℝ → ℂ) (w : ℂ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (hf0 : (0 : ℝ) ∉ tsupport f) :
    mellin (deriv f) w = -(w - 1) * mellin f (w - 1) := by
  calc
    mellin (deriv f) w = mellin (deriv f) ((w - 1) + 1) := by rw [sub_add_cancel]
    _ = _ := by rw [← mellin_mul_variable, mellin_mul_deriv f (w - 1) hf hfc hf0]

/-- The Mellin transform of the affine action is a vertical integral with the Gamma kernel
when the exponential factor decays and `c < Re w`. -/
theorem mellin_affineAction_eq_integral (lam : ℂ) (a b : ℝ) (ha : 0 < a)
    (hlam : 0 < (-lam * b).re) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Ioi 0) (w : ℂ) (c : ℝ) (hc : c < w.re) :
    mellin (affineAction lam ⟨a, b, ha⟩ f) w =
      Complex.I * ∫ s : ℝ, affineGammaKernel lam a b w (c + s * Complex.I) *
        mellin f (c + s * Complex.I) := by
  let q : ℂ := -lam * b / a
  let E : ℝ → ℂ := fun x => Complex.exp (-(q * x))
  let F : ℝ → ℂ := fun x => (x : ℂ) ^ (w - 1) * E x
  have hq : 0 < q.re := by
    dsimp only [q]
    rw [div_ofReal_re]
    exact div_pos hlam ha
  have hW : 0 < w.re - c := sub_pos.mpr hc
  have hM : MellinConvergent F (1 - (c : ℂ)) := by
    change MellinConvergent (fun x => (x : ℂ) ^ (w - 1) • E x) (1 - (c : ℂ))
    rw [MellinConvergent.cpow_smul]
    apply Complex.CubicLaplace.mellinConvergent_exp_neg_mul (hq := hq)
    simpa only [add_re, sub_re, one_re, ofReal_re] using
      (show 0 < 1 - c + (w.re - 1) by linarith)
  have h0 : (0 : ℝ) ∉ tsupport f := fun h => lt_irrefl (0 : ℝ) (hfs h)
  have hMf : MellinConvergent f (c : ℂ) := by
    apply (mellinConvergent_iff_integrable_exp_mul f c).mpr
    have he : Continuous (fun u : ℝ => Complex.exp (-(c : ℂ) * u) * f (Real.exp (-u))) :=
      (by fun_prop : Continuous (fun u : ℝ => Complex.exp (-(c : ℂ) * u))).mul
        (hf.continuous.comp (by fun_prop))
    exact he.integrable_of_hasCompactSupport
      (hasCompactSupport_mellinLog f c (isCompact_tsupport_inter_Ioi hfc h0))
  have hMellin (s : ℝ) : mellin F (1 - (c + s * I)) =
      Gamma (w - (c + s * I)) * q ^ ((c + s * I) - w) := by
    change mellin (fun x => (x : ℂ) ^ (w - 1) • E x) _ = _
    rw [mellin_cpow_smul,
      show (1 : ℂ) - (c + s * I) + (w - 1) = w - (c + s * I) by ring,
      Complex.CubicLaplace.mellin_exp_neg_mul _ hq, neg_sub]
    simpa only [sub_re, add_re, mul_I_re, ofReal_im, neg_zero, add_zero, ofReal_re] using hW
  have hg := DLMF.Gamma.integrable_Gamma_mul_cpow_neg hW hq
  have hshift (s : ℝ) : w - (c + s * I) = ((w.re - c : ℝ) : ℂ) + (w.im - s : ℝ) * I := by
    apply Complex.ext <;> simp
  have hVert : Integrable (fun s : ℝ => mellin F (1 - (c + s * I))) := by
    have ht := (volume.measurePreserving_sub_left w.im).integrable_comp_of_integrable hg
    refine ht.congr (Filter.Eventually.of_forall fun s => ?_)
    dsimp only [Function.comp_apply]
    rw [hMellin, show (c + s * I : ℂ) - w = -(w - (c + s * I)) by ring, hshift]
  let G : ℝ → ℂ := fun x => E x * f x
  have hfun : affineAction lam ⟨a, b, ha⟩ f = fun x => G (a * x) := by
    funext x
    simp only [affineAction, G, E, q, ofReal_mul]
    congr 2
    field_simp [ofReal_ne_zero.mpr ha.ne']
  have hprod : mellin G w = ∫ x in Ioi (0 : ℝ), F x * f x := by
    simp only [mellin, F, G, smul_eq_mul, mul_assoc]
  rw [hfun, mellin_comp_mul_left G w ha, smul_eq_mul, hprod,
    integral_mul_eq_mellin_parseval hM hMf (Or.inr hVert)]
  simp_rw [hMellin]
  rw [← mul_assoc, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  dsimp only [affineGammaKernel, q]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [Complex.I_ne_zero, hπ]

/-- §1.3. **Addition formula for the Gamma function.** -/
theorem Gamma_mul_div_add_one_cpow (w : ℂ) (t c : ℝ) (ht : 0 < t) (hc : 0 < c)
    (hcw : c < w.re) :
    Gamma w * ((t / (t + 1) : ℝ) : ℂ) ^ w =
      (1 / (2 * π) : ℂ) * ∫ s : ℝ, Gamma (w - (c + s * Complex.I)) * Gamma (c + s * Complex.I) *
        (t : ℂ) ^ (c + s * Complex.I) := by
  have h := DLMF.Gamma.Gamma_mul_one_add_cpow_neg hc hcw (inv_pos.mpr ht)
  have hquot : (t / (t + 1) : ℝ) = (1 + t⁻¹)⁻¹ := by
    field_simp [ht.ne', (show t + 1 ≠ 0 by positivity)]
  rw [hquot, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_ne_zero.symm),
    ← Complex.cpow_neg]
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_ne_zero.symm),
    ← Complex.cpow_neg, neg_neg]
  ring

/-- §1.3. **Dual form.** -/
theorem mellin_div_add_one_cpow (w u : ℂ) (hu : u.re < 0) (hwu : 0 < (w + u).re) :
    mellin (fun t : ℝ => ((t / (t + 1) : ℝ) : ℂ) ^ w) u =
      Gamma (w + u) * Gamma (-u) / Gamma w := by
  have hu' : 0 < (-u).re := by simpa using neg_pos.mpr hu
  have hwu' : (-u).re < w.re := by simp only [Complex.neg_re]; rw [Complex.add_re] at hwu; linarith
  have h := DLMF.Gamma.mellin_one_add_cpow_neg (a := w) hu' hwu'
  rw [← mellin_comp_inv] at h
  rw [sub_neg_eq_add, mul_comm] at h
  refine Eq.trans ?_ h
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hpos : 0 < t := ht
  have hquot : (t / (t + 1) : ℝ) = (1 + t⁻¹)⁻¹ := by
    field_simp [hpos.ne', (show t + 1 ≠ 0 by positivity)]
  dsimp only
  rw [hquot, Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg (by positivity)]
      exact Real.pi_ne_zero.symm),
    ← Complex.cpow_neg]

end SFVK.AffineHeisenberg
