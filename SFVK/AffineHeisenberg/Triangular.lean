/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.AffineHeisenberg.Basic
public import SFVK.AffineHeisenberg.TriangularKernels
import SFVK.AffineHeisenberg.Affine
import DLMFMathlib.Analysis.Complex.VerticalLineShift
import DLMFMathlib.Analysis.MellinParseval
import DLMFMathlib.Analysis.SpecialFunctions.Pow.ComplexReal
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import TauCeti.Analysis.MellinTransform.Decay
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The triangular group and its signed Mellin transform

Statements of §2 of the roadmap `Roadmaps/AffineHeisenbergGroups/README.md` (section numbers
`§x.y`).
Sources: Vilenkin–Klimyk Vol. 1 §§5.1–5.2, pp. 207–220; Klimyk–Vilenkin Ch. 4 §1.4 (11)–(21), pp.
205–207.
The kernel realization uses Mellin inversion and vertical decay of the Mellin transform.
-/

@[expose] public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open scoped Real ComplexConjugate InnerProductSpace ENNReal FourierTransform

/-- §2.1. **Cocycle.** -/
theorem isMultiplierCocycle_triangularCocycle (σ ω : ℂ) :
    IsMultiplierCocycle (triangularCocycle σ ω) ∧
      multiplierAction (triangularCocycle σ ω) = triangularAction σ ω := by
  have hx : ∀ (g : TriangularGroup) (x : ℝ), g⁻¹ • x = Real.exp g.τ * x + g.a := by
    intro g x
    show Real.exp (-g⁻¹.τ) * (x - g⁻¹.a) = _
    simp only [TriangularGroup.inv_τ, TriangularGroup.inv_a, neg_neg]
    have : Real.exp g.τ * Real.exp (-g.τ) = 1 := by rw [← Real.exp_add]; simp
    linear_combination g.a * this
  refine ⟨⟨fun x => by simp [triangularCocycle], fun g h x => ?_⟩, ?_⟩
  · rw [hx]
    simp only [triangularCocycle, TriangularGroup.mul_τ, TriangularGroup.mul_d,
      TriangularGroup.mul_b, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · funext g f x
    simp only [multiplierAction, triangularAction, hx]

/-- The extended norm of the exponential multiplier, squared. -/
private theorem eNorm_cexp_sq (z : ℂ) :
    ‖Complex.exp z‖ₑ ^ 2 = ENNReal.ofReal (Real.exp (2 * z.re)) := by
  rw [← ofReal_norm, norm_exp, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← Real.exp_nat_mul]
  norm_num

/-- The derivative of the affine map determines its constant volume change. -/
private theorem lintegral_affine_change (r a : ℝ) (hr : 0 < r) (F : ℝ → ℝ≥0∞) :
    (∫⁻ x, ENNReal.ofReal r * F (r * x + a)) = ∫⁻ x, F x := by
  let f : ℝ → ℝ := fun x => r * x + a
  have hinj : Function.Injective f := by
    intro x y h
    dsimp only [f] at h
    exact mul_left_cancel₀ hr.ne' (add_right_cancel h)
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨(x - a) / r, ?_⟩
    dsimp only [f]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hr.ne', sub_add_cancel]
  have hd (x : ℝ) : HasDerivAt f r x := by
    simpa only [f, mul_one, id_eq] using ((hasDerivAt_id x).const_mul r).add_const a
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := univ) (f := f) MeasurableSet.univ
    (fun x _ => (hd x).hasDerivWithinAt) hinj.injOn F
  simpa only [image_univ, hsurj.range_eq, Measure.restrict_univ, abs_of_pos hr] using h.symm

/-- For a purely imaginary central character, the norm change depends only on the dilation. -/
private theorem lintegral_triangularAction_eq (σ ω : ℂ) (hσ : σ.re = 0)
    (g : TriangularGroup) (f : ℝ → ℂ) :
    (∫⁻ x, ‖triangularAction σ ω g f x‖ₑ ^ 2) =
      ENNReal.ofReal (Real.exp ((2 * ω.re - 1) * g.τ)) * ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  rw [← lintegral_affine_change (Real.exp g.τ) g.a (Real.exp_pos g.τ)
    (fun x => ‖f x‖ₑ ^ 2), ← lintegral_const_mul']
  · apply lintegral_congr
    intro x
    simp only [triangularAction, triangularCocycle, eNorm_mul, mul_pow, eNorm_cexp_sq,
      add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, mul_zero, sub_zero, hσ,
      zero_mul, add_zero]
    have hfactor : ENNReal.ofReal (Real.exp ((2 * ω.re - 1) * g.τ)) *
        ENNReal.ofReal (Real.exp g.τ) = ENNReal.ofReal (Real.exp (2 * (ω.re * g.τ))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    rw [← hfactor, mul_assoc]
  · exact ENNReal.ofReal_ne_top

/-- §2.1. **Unitarity range.** -/
theorem lintegral_triangularAction_iff (σ ω : ℂ) :
    (∀ (g : TriangularGroup) (f : ℝ → ℂ), Measurable f →
      ∫⁻ x, ‖triangularAction σ ω g f x‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2) ↔
      σ.re = 0 ∧ ω.re = 1 / 2 := by
  constructor
  · intro h
    let test : ℝ → ℂ := (Icc (0 : ℝ) 1).indicator (fun _ => 1)
    have htM : Measurable test := measurable_const.indicator measurableSet_Icc
    have htest : ∫⁻ x, ‖test x‖ₑ ^ 2 = 1 := by
      have hpt (x : ℝ) : ‖test x‖ₑ ^ 2 = (Icc (0 : ℝ) 1).indicator (fun _ => 1) x := by
        by_cases hx : x ∈ Icc (0 : ℝ) 1
        · simp [test, hx]
        · simp [test, hx]
      simp_rw [hpt]
      rw [lintegral_indicator_const measurableSet_Icc]
      simp [Real.volume_Icc]
    have hs := h (centreElt 1) test htM
    have hcentre (x : ℝ) : ‖triangularAction σ ω (centreElt 1) test x‖ₑ ^ 2 =
        ENNReal.ofReal (Real.exp (2 * σ.re)) * ‖test x‖ₑ ^ 2 := by
      simp only [triangularAction, triangularCocycle, centreElt, ofReal_zero, ofReal_one,
        mul_zero, zero_mul, zero_add, mul_one, Real.exp_zero, one_mul, add_zero, eNorm_mul,
        mul_pow, eNorm_cexp_sq]
    simp_rw [hcentre] at hs
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, htest, mul_one] at hs
    have hs' := congrArg ENNReal.toReal hs
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_one] at hs'
    have hσ : σ.re = 0 := by linarith [Real.exp_injective (hs'.trans Real.exp_zero.symm)]
    have hω := h (dilation 1) test htM
    rw [lintegral_triangularAction_eq σ ω hσ (dilation 1) test, htest, mul_one] at hω
    have hω' := congrArg ENNReal.toReal hω
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_one] at hω'
    have he : (2 * ω.re - 1) * 1 = 0 := Real.exp_injective (hω'.trans Real.exp_zero.symm)
    exact ⟨hσ, by linarith⟩
  · rintro ⟨hσ, hω⟩ g f _
    rw [lintegral_triangularAction_eq σ ω hσ g f, hω]
    norm_num

/-- §2.1. **Unitary representations.** -/
theorem triangularRep_spec (γ ρ γ' ρ' : ℝ) :
    (∀ g f, (triangularRep γ ρ g f : ℝ → ℂ) =ᵐ[volume]
      triangularAction (γ * Complex.I) (1 / 2 + ρ * Complex.I) g f) ∧
    (triangularRep γ ρ).IsUnitary ∧
    (γ ≠ 0 → ∀ W : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)),
      IsClosed (W : Set (Lp ℂ 2 (volume : Measure ℝ))) →
      (∀ g, ∀ v ∈ W, triangularRep γ ρ g v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
    (γ ≠ 0 → γ' ≠ 0 →
      ((∃ U : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ),
        ∀ g v, U (triangularRep γ ρ g v) = triangularRep γ' ρ' g (U v)) ↔
        γ = γ' ∧ ρ = ρ')) := by
  sorry

/-- §2.1. **Restriction to the Heisenberg group.** -/
theorem triangularAction_heisenberg (ω : ℂ) (p : TauCeti.HeisenbergGroup ℝ) (f : ℝ → ℂ) :
    triangularAction Complex.I ω (heisenbergToTriangular p) f =
      multiplierAction schrodingerCocycle p f := by
  funext x
  have hx : p⁻¹ • x = x + p.x := by
    show x - p⁻¹.x = x + p.x
    simp
  simp only [triangularAction, triangularCocycle, multiplierAction, schrodingerCocycle,
    heisenbergToTriangular, MonoidHom.coe_mk, OneHom.coe_mk, hx, Real.exp_zero, one_mul]
  congr 1
  push_cast
  ring_nf

/-- Differentiating a complex exponential along a real parameter at zero. -/
private theorem hasDerivAt_exp_mul_real (a : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.exp (a * t)) a 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).const_mul a).comp_ofReal.cexp

/-- §2.2. **Infinitesimal operators.** -/
theorem hasDerivAt_triangularAction (σ ω : ℂ) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (x : ℝ) :
    HasDerivAt (fun t => triangularAction σ ω (gPlus t) f x) (deriv f x) 0 ∧
    HasDerivAt (fun t => triangularAction σ ω (gMinus t) f x) (σ * x * f x) 0 ∧
    HasDerivAt (fun t => triangularAction σ ω (centreElt t) f x) (σ * f x) 0 ∧
    HasDerivAt (fun t => triangularAction σ ω (dilation t) f x)
      (ω * f x + x * deriv f x) 0 := by
  have hdiff (y : ℝ) : HasDerivAt f (deriv f y) y :=
    (hf.differentiable (by norm_num) y).hasDerivAt
  constructor
  · have hbase : HasDerivAt f (deriv f x) ((fun t : ℝ => x + t) 0) := by simpa using hdiff x
    simpa [triangularAction, triangularCocycle, gPlus, add_comm, Function.comp_def] using
      hbase.scomp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add x)
  constructor
  · have h := (hasDerivAt_exp_mul_real (σ * x)).mul_const (f x)
    convert h using 1
    funext t
    simp only [triangularAction, triangularCocycle, gMinus, Complex.ofReal_zero,
      mul_zero, zero_add, Real.exp_zero, one_mul, add_zero]
    congr 2
    ring
  constructor
  · simpa [triangularAction, triangularCocycle, centreElt] using
      (hasDerivAt_exp_mul_real σ).mul_const (f x)
  · have hbase : HasDerivAt f (deriv f x) ((fun t : ℝ => Real.exp t * x) 0) := by
      simpa using hdiff x
    have hf' := hbase.scomp (0 : ℝ) ((Real.hasDerivAt_exp 0).mul_const x)
    convert (hasDerivAt_exp_mul_real ω).mul hf' using 1
    · funext t
      simp [triangularAction, triangularCocycle, dilation, Function.comp_def]
    · simp [Complex.real_smul]

/-- §2.3. **Diagonal and central elements.** -/
theorem signedMellin_dilation_centre (σ ω : ℂ) (f : ℝ → ℂ) (ε : ℤˣ) (lam : ℂ) (τ b : ℝ) :
    signedMellin (triangularAction σ ω (dilation τ) f) ε lam =
      Complex.exp ((ω - lam) * τ) * signedMellin f ε lam ∧
    signedMellin (triangularAction σ ω (centreElt b) f) ε lam =
      Complex.exp (σ * b) * signedMellin f ε lam := by
  have hpow : ((Real.exp τ : ℝ) : ℂ) ^ (-lam) = Complex.exp (-lam * τ) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero τ)),
      ← Complex.ofReal_log (Real.exp_pos τ).le, Real.log_exp, mul_comm]
  constructor
  · simp only [signedMellin, triangularAction, triangularCocycle, dilation, Complex.ofReal_zero,
      mul_zero, zero_mul, add_zero]
    let F : ℝ → ℂ := fun x => f (((ε : ℤ) : ℝ) * x)
    have hF : (fun x : ℝ => Complex.exp (ω * τ) * f (Real.exp τ * (((ε : ℤ) : ℝ) * x))) =
        fun x => Complex.exp (ω * τ) • F (Real.exp τ * x) := by
      funext x
      simp only [F, smul_eq_mul]
      congr 2
      ring
    rw [hF, mellin_const_smul, mellin_comp_mul_left _ _ (Real.exp_pos τ), hpow,
      smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    congr 3
    ring
  · simp only [signedMellin, triangularAction, triangularCocycle, centreElt, Complex.ofReal_zero,
      mul_zero, zero_mul, add_zero, zero_add, Real.exp_zero, one_mul]
    simpa only [smul_eq_mul] using
      mellin_const_smul (fun x : ℝ => f (((ε : ℤ) : ℝ) * x)) lam (Complex.exp (σ * b))

/-- §2.3. **Infinitesimal operators** in the signed Mellin realization. -/
theorem signedMellin_infinitesimal (f : ℝ → ℂ) (ε : ℤˣ) (lam : ℂ) :
    (ContDiff ℝ 1 f → HasCompactSupport f → (0 : ℝ) ∉ tsupport f →
      signedMellin (deriv f) ε lam = -(((ε : ℤ) : ℂ) * (lam - 1)) * signedMellin f ε (lam - 1)) ∧
    signedMellin (fun x => (x : ℂ) * f x) ε lam = ((ε : ℤ) : ℂ) * signedMellin f ε (lam + 1) := by
  let r : ℝ := ((ε : ℤ) : ℝ)
  let F : ℝ → ℂ := fun x => f (r * x)
  have hr2 : (r : ℂ) * r = 1 := by
    dsimp only [r]
    rcases Int.units_eq_one_or ε with h | h <;> rw [h] <;> norm_num
  have hr0 : r ≠ 0 := by
    intro h
    simp [h] at hr2
  have hcoord : (r : ℂ) = ((ε : ℤ) : ℂ) := ofReal_intCast _
  constructor
  · intro hf hfc hf0
    let e := Homeomorph.mulLeft₀ r hr0
    have hFe : F = f ∘ e := rfl
    have hFc : ContDiff ℝ 1 F := by
      dsimp only [F]
      exact hf.comp (by fun_prop)
    have hFcs : HasCompactSupport F := hFe.symm ▸ hfc.comp_homeomorph e
    have hF0 : (0 : ℝ) ∉ tsupport F := by
      rw [hFe, tsupport_comp_eq_preimage]
      simpa only [mem_preimage, e, Homeomorph.coe_mulLeft₀, mul_zero] using hf0
    have hder (x : ℝ) : deriv F x = r * deriv f (r * x) := by
      have hm : HasDerivAt (fun x : ℝ => r * x) r x := by
        simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul r
      have hd := (hf.differentiable (by norm_num) (r * x)).hasDerivAt.scomp x hm
      simpa only [F, Function.comp_def, Complex.real_smul] using hd.deriv
    have hfun : (fun x => deriv f (r * x)) = fun x => (r : ℂ) • deriv F x := by
      funext x
      rw [hder, smul_eq_mul, ← mul_assoc, hr2, one_mul]
    change mellin (fun x => deriv f (r * x)) lam =
      -(((ε : ℤ) : ℂ) * (lam - 1)) * mellin F (lam - 1)
    rw [hfun, mellin_const_smul, mellin_deriv F lam hFc hFcs hF0, smul_eq_mul, ← hcoord]
    ring
  · have hfun : (fun x : ℝ => ((r * x : ℝ) : ℂ) * f (r * x)) =
        fun x : ℝ => (r : ℂ) • ((x : ℂ) * F x) := by
      funext x
      simp only [F, ofReal_mul, smul_eq_mul, mul_assoc]
    change mellin (fun x => ((r * x : ℝ) : ℂ) * f (r * x)) lam =
      ((ε : ℤ) : ℂ) * mellin F (lam + 1)
    rw [hfun, mellin_const_smul, smul_eq_mul, mellin_mul_variable, hcoord]

private theorem mellinConvergent_of_isCompact_support (f : ℝ → ℂ) (c : ℝ)
    (hf : ContinuousOn f (Ioi 0)) (hc : IsCompact (tsupport f ∩ Ioi 0)) :
    MellinConvergent f c := by
  rw [mellinConvergent_iff_integrable_exp_mul]
  let G : ℝ → ℂ := fun u => cexp (-(c : ℂ) * u) * f (Real.exp (-u))
  have hGc : Continuous G :=
    (by fun_prop : Continuous (fun u : ℝ => cexp (-(c : ℂ) * u))).mul
      (hf.comp_continuous (by fun_prop) (fun u => Real.exp_pos _))
  exact hGc.integrable_of_hasCompactSupport (hasCompactSupport_mellinLog f c hc)

private theorem continuous_mellin_vertical (f : ℝ → ℂ) (c : ℝ)
    (hf : MellinConvergent f c) : Continuous (fun s : ℝ => mellin f (c + s * I)) := by
  simp_rw [mellin_vertical_eq_fourier, Real.fourier_eq]
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf.integrable_log_weight).comp (by fun_prop)

private theorem verticalIntegrable_mellin_of_isCompact_support (f : ℝ → ℂ) (c : ℝ)
    (hf : ContDiffOn ℝ 2 f (Ioi 0)) (hc : IsCompact (tsupport f ∩ Ioi 0)) :
    VerticalIntegrable (mellin f) c := by
  have hm := mellinConvergent_of_isCompact_support f c hf.continuousOn hc
  obtain ⟨C, _, hC⟩ := TauCeti.exists_one_add_abs_im_pow_mul_norm_mellin_le
    (N := 2) hf hc (isCompact_singleton (x := c))
  apply Complex.integrable_of_norm_le_inv_one_add_abs_sq (continuous_mellin_vertical f c hm)
  intro s
  have h := hC ((c : ℂ) + s * I) (by simp)
  simp only [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add] at h
  have hd : 0 < (1 + |s|) ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hd]
  simpa only [mul_comm] using h

private theorem measurable_complexPower {α : Type*} [MeasurableSpace α]
    {f g : α → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x ^ g x) := by
  simp_rw [Complex.cpow_def]
  exact Measurable.ite (measurableSet_eq_fun hf measurable_const)
    (Measurable.ite (measurableSet_eq_fun hg measurable_const) measurable_const measurable_const)
    (Complex.continuous_exp.measurable.comp ((Complex.measurable_log.comp hf).mul hg))

private def signedRegion (a r : ℝ) (ε η : ℤˣ) : Set ℝ :=
  Ioi 0 ∩ {x | 0 < ((η : ℤ) : ℝ) * (r * ((ε : ℤ) : ℝ) * x + a)}

private theorem measurableSet_signedRegion (a r : ℝ) (ε η : ℤˣ) :
    MeasurableSet (signedRegion a r ε η) := by
  unfold signedRegion
  exact measurableSet_Ioi.inter (measurableSet_lt measurable_const (by fun_prop))

private theorem integrableOn_signedRegion_gPlus (t alpha c : ℝ) (ht : 0 < t)
    (ha : 0 < alpha) (hac : alpha < c) (hc : c < 1) (ε η : ℤˣ) :
    IntegrableOn (fun x => x ^ (alpha - 1) *
      |((ε : ℤ) : ℝ) * x + t| ^ (-c)) (signedRegion t 1 ε η) := by
  let G : ℝ → ℂ := fun x => (x : ℂ) ^ ((alpha : ℂ) - 1) *
    ((|((ε : ℤ) : ℝ) * x + t| : ℝ) : ℂ) ^ (-(c : ℂ))
  have hConvert : (∫ x in signedRegion t 1 ε η, G x) =
      (2 * π * I) * triangularKernel 0 0 ε η alpha c (gPlus t) := by
    simp only [triangularKernel, gPlus, G, signedRegion, ofReal_zero, mul_zero, zero_mul,
      add_zero, Complex.exp_zero, Real.exp_zero, one_mul, mul_one,
      one_div, ← mul_assoc]
    rw [mul_inv_cancel₀ (by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero),
      one_mul]
  have hΓ (s : ℂ) (hs : 0 < s.re) : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  have htW : (t : ℂ) ^ ((alpha : ℂ) - c) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr ht.ne'))
  have hA : 0 < (alpha : ℂ).re := by simpa only [ofReal_re] using ha
  have hAC : (alpha : ℂ).re < (c : ℂ).re := by simpa only [ofReal_re] using hac
  have hC : (c : ℂ).re < 1 := by simpa only [ofReal_re] using hc
  by_cases hbad : ε = 1 ∧ η = -1
  · rcases hbad with ⟨rfl, rfl⟩
    have hE : signedRegion t 1 1 (-1) = ∅ := by
      ext x
      simp only [signedRegion, mem_inter_iff, mem_Ioi, mem_ofPred_eq, mem_empty_iff_false,
        Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul, one_mul]
      constructor
      · rintro ⟨hx, hy⟩
        linarith
      · exact False.elim
    exact hE.symm ▸ integrableOn_empty
  · have hK : triangularKernel 0 0 ε η alpha c (gPlus t) ≠ 0 := by
      have h := triangularKernel_gPlus 0 0 (alpha : ℂ) (c : ℂ) t ht
      rcases Int.units_eq_one_or ε with rfl | rfl <;> rcases Int.units_eq_one_or η with rfl | rfl
      · rw [h.1 hAC hA]
        exact mul_ne_zero (div_ne_zero (mul_ne_zero (hΓ _ (by simp only [sub_re]; linarith))
          (hΓ _ hA)) (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
            (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero) (hΓ _ (by linarith)))) htW
      · exact (hbad ⟨rfl, rfl⟩).elim
      · rw [h.2.1 hA hC]
        exact mul_ne_zero (div_ne_zero (mul_ne_zero (hΓ _ hA)
          (hΓ _ (by simp only [sub_re, one_re]; linarith)))
          (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
            (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)
            (hΓ _ (by simp only [add_re, sub_re, one_re]; linarith)))) htW
      · rw [h.2.2.1 hAC hC]
        exact mul_ne_zero (div_ne_zero (mul_ne_zero (hΓ _ (by simp only [sub_re, one_re]; linarith))
          (hΓ _ (by simp only [sub_re]; linarith))) (mul_ne_zero (mul_ne_zero
            (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero)
            (hΓ _ (by simp only [sub_re, one_re]; linarith)))) htW
    have hInt : IntegrableOn G (signedRegion t 1 ε η) := by
      apply Integrable.of_integral_ne_zero
      rw [hConvert]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero) hK
    refine IntegrableOn.congr_fun hInt.norm (fun x hx => ?_) (measurableSet_signedRegion ..)
    have hX : 0 < x := hx.1
    have hY : 0 < |((ε : ℤ) : ℝ) * x + t| := by
      have hs := hx.2
      by_contra! h
      have hz : ((ε : ℤ) : ℝ) * x + t = 0 := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      simp only [one_mul, mem_ofPred_eq, hz, mul_zero, lt_irrefl] at hs
    dsimp only [G]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hX, norm_cpow_eq_rpow_re_of_pos hY,
      sub_re, neg_re, ofReal_re, ofReal_re, one_re]

private theorem integrableOn_signedRegion {a r alpha c : ℝ} (ha : a ≠ 0) (hr : 0 < r)
    (hα : 0 < alpha) (hαc : alpha < c) (hc : c < 1) (ε η : ℤˣ) :
    IntegrableOn (fun x => x ^ (alpha - 1) *
      |r * ((ε : ℤ) : ℝ) * x + a| ^ (-c)) (signedRegion a r ε η) := by
  have hnorm (ε η : ℤˣ) :
      IntegrableOn (fun x => x ^ (alpha - 1) *
        |((ε : ℤ) : ℝ) * x + a| ^ (-c)) (signedRegion a 1 ε η) := by
    rcases lt_or_gt_of_ne ha with ha' | ha'
    · have h := integrableOn_signedRegion_gPlus (-a) alpha c (neg_pos.mpr ha') hα hαc hc (-ε) (-η)
      have hE : signedRegion (-a) 1 (-ε) (-η) = signedRegion a 1 ε η := by
        ext x
        simp only [signedRegion, mem_inter_iff, mem_ofPred_eq, Units.val_neg, Int.cast_neg,
          one_mul]
        have hEq : -((η : ℤ) : ℝ) * (-((ε : ℤ) : ℝ) * x + -a) =
            ((η : ℤ) : ℝ) * (((ε : ℤ) : ℝ) * x + a) := by ring
        rw [hEq]
      rw [hE] at h
      simpa only [Units.val_neg, Int.cast_neg, neg_mul, ← neg_add, abs_neg] using h
    · exact integrableOn_signedRegion_gPlus a alpha c ha' hα hαc hc ε η
  let W (x : ℝ) := x ^ (alpha - 1) * |((ε : ℤ) : ℝ) * x + a| ^ (-c)
  have hImage : (fun x : ℝ => r * x) '' signedRegion a r ε η = signedRegion a 1 ε η := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, hy'⟩, rfl⟩
      refine ⟨mul_pos hr hy, ?_⟩
      dsimp only [signedRegion, mem_ofPred_eq] at hy' ⊢
      convert hy' using 3
      ring
    · rintro ⟨hx, hx'⟩
      have hRx : r * (x / r) = x := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hr.ne']
      refine ⟨x / r, ⟨div_pos hx hr, ?_⟩, hRx⟩
      dsimp only [mem_ofPred_eq] at hx' ⊢
      have hs : r * ((ε : ℤ) : ℝ) * (x / r) = ((ε : ℤ) : ℝ) * x := by
        rw [mul_comm r, mul_assoc, hRx]
      simpa only [hs, one_mul] using hx'
  have hD (x : ℝ) : HasDerivAt (fun x : ℝ => r * x) r x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul r
  have hScale := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := fun x : ℝ => r * x) (measurableSet_signedRegion a r ε η)
    (fun x _ => (hD x).hasDerivWithinAt) (mul_right_injective₀ hr.ne').injOn W
  rw [hImage] at hScale
  have h := (hScale.mp (hnorm ε η)).const_mul ((r * r ^ (alpha - 1))⁻¹)
  refine IntegrableOn.congr_fun h (fun x hx => ?_) (measurableSet_signedRegion ..)
  dsimp only [W, smul_eq_mul]
  rw [abs_of_pos hr, Real.mul_rpow hr.le hx.1.le]
  have hShift : ((ε : ℤ) : ℝ) * (r * x) = r * ((ε : ℤ) : ℝ) * x := by ring
  rw [hShift]
  have hP : r * r ^ (alpha - 1) ≠ 0 := mul_ne_zero hr.ne' (Real.rpow_pos_of_pos hr _).ne'
  field_simp [hP]

/-- §2.3. **Kernel realization.** -/
theorem signedMellin_triangularAction (σ ω : ℂ) (hσ : σ.re = 0) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : (0 : ℝ) ∉ tsupport f)
    (g : TriangularGroup) (hg : g.a ≠ 0) (ε : ℤˣ) (lam : ℂ) (c : ℝ) (hlam : 0 < lam.re)
    (hlc : lam.re < c) (hc : c < 1) :
    signedMellin (triangularAction σ ω g f) ε lam =
      ∑ η : ℤˣ, Complex.I * ∫ s : ℝ, triangularKernel σ ω ε η lam (c + s * Complex.I) g *
        signedMellin f η (c + s * Complex.I) := by
  let r := Real.exp g.τ
  let X (x : ℝ) : ℝ := r * ((ε : ℤ) : ℝ) * x + g.a
  let S (η : ℤˣ) : Set ℝ := signedRegion g.a r ε η
  let B (x : ℝ) : ℂ := (x : ℂ) ^ (lam - 1) * cexp (σ * g.d * ((ε : ℤ) : ℂ) * x)
  let C : ℂ := cexp (ω * g.τ + σ * g.b)
  let z (s : ℝ) : ℂ := (c : ℂ) + s * I
  let F (η : ℤˣ) (x : ℝ) : ℂ := f (((η : ℤ) : ℝ) * x)
  let E (η : ℤˣ) (p : ℝ × ℝ) : ℂ :=
    B p.1 * ((|X p.1| : ℝ) : ℂ) ^ (-z p.2) * mellin (F η) (z p.2)
  let V (x : ℝ) := B x * f (X x)
  let D : ℂ := ((1 / (2 * π) : ℝ) : ℂ)
  have hSm (η : ℤˣ) : MeasurableSet (S η) := measurableSet_signedRegion ..
  have hX (η : ℤˣ) (x : ℝ) (hx : x ∈ S η) :
      0 < |X x| ∧ ((η : ℤ) : ℝ) * |X x| = X x := by
    have h := hx.2
    change 0 < ((η : ℤ) : ℝ) * X x at h
    rcases Int.units_eq_one_or η with rfl | rfl
    · simp only [Units.val_one, Int.cast_one, one_mul] at h ⊢
      rw [abs_of_pos h]
      exact ⟨h,rfl⟩
    · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul] at h ⊢
      rw [abs_of_neg (neg_pos.mp h), neg_neg]
      exact ⟨h,rfl⟩
  have hCdiff (η : ℤˣ) : ContDiff ℝ 2 (F η) := hf.comp (by fun_prop)
  have hFcomp (η : ℤˣ) : IsCompact (tsupport (F η) ∩ Ioi 0) := by
    have hn : ((η : ℤ) : ℝ) ≠ 0 := by
      rcases Int.units_eq_one_or η with rfl | rfl <;> norm_num
    let e := Homeomorph.mulLeft₀ (((η : ℤ) : ℝ)) hn
    have hFe : F η = f ∘ e := rfl
    apply isCompact_tsupport_inter_Ioi (hFe.symm ▸ hfc.comp_homeomorph e)
    rw [hFe, tsupport_comp_eq_preimage]
    simpa only [mem_preimage, e, Homeomorph.coe_mulLeft₀, mul_zero] using hf0
  have hM (η : ℤˣ) : MellinConvergent (F η) c :=
    mellinConvergent_of_isCompact_support _ _ (hCdiff η).continuous.continuousOn (hFcomp η)
  have hVert (η : ℤˣ) : VerticalIntegrable (mellin (F η)) c :=
    verticalIntegrable_mellin_of_isCompact_support _ _ (hCdiff η).contDiffOn (hFcomp η)
  have hFour (η : ℤˣ) : Continuous (fun s : ℝ => mellin (F η) (z s)) :=
    continuous_mellin_vertical _ _ (hM η)
  have hPoint (η : ℤˣ) (x : ℝ) (hx : x ∈ S η) :
      V x = D * ∫ s : ℝ, E η (x,s) := by
    have h := mellinInv_mellin_eq c (F η) (hX η x hx).1 (hM η) (hVert η)
      (hCdiff η).continuous.continuousAt
    change mellinInv c (mellin (F η)) |X x| = f (((η : ℤ) : ℝ) * |X x|) at h
    rw [(hX η x hx).2, mellinInv, real_smul] at h
    dsimp only [V, E, D, z]
    rw [← h, mul_left_comm, ← integral_const_mul]
    congr 2
    funext s
    simp only [smul_eq_mul, mul_assoc]
  have hEint (η : ℤˣ) : Integrable (E η)
      ((volume.restrict (S η)).prod (volume : Measure ℝ)) := by
    let W (x : ℝ) := x ^ (lam.re - 1) * |X x| ^ (-c)
    have hW : IntegrableOn W (S η) :=
      integrableOn_signedRegion hg (Real.exp_pos g.τ) hlam hlc hc ε η
    have hgV : Integrable (fun s : ℝ => ‖mellin (F η) (z s)‖) := (hVert η).norm
    have hMj : Integrable (fun p : ℝ × ℝ => W p.1 * ‖mellin (F η) (z p.2)‖)
        ((volume.restrict (S η)).prod (volume : Measure ℝ)) := hW.mul_prod hgV
    have hXmeas : Measurable (fun p : ℝ × ℝ => ((|X p.1| : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        (((continuous_abs.comp (by fun_prop : Continuous X)).comp continuous_fst).measurable)
    have hBmeas : Measurable (fun p : ℝ × ℝ => B p.1) :=
      (measurable_complexPower (Complex.continuous_ofReal.measurable.comp measurable_fst)
        measurable_const).mul (by fun_prop)
    have hMeas : Measurable (E η) :=
      (hBmeas.mul (measurable_complexPower hXmeas (by dsimp only [z]; fun_prop))).mul
        ((hFour η).measurable.comp measurable_snd)
    have hAE : ∀ᵐ p ∂(volume.restrict (S η)).prod (volume : Measure ℝ),
        (p : ℝ × ℝ).1 ∈ S η := by
      apply (Measure.ae_prod_iff_ae_ae ((hSm η).preimage measurable_fst)).2
      filter_upwards [ae_restrict_mem (hSm η)] with x hx
      exact Filter.Eventually.of_forall (fun _ => hx)
    refine hMj.mono' hMeas.aestronglyMeasurable ?_
    filter_upwards [hAE] with ⟨x, s⟩ hx
    apply le_of_eq
    have hNorm : ‖cexp (σ * g.d * ((ε : ℤ) : ℂ) * x)‖ = 1 := by
      rw [norm_exp]
      simp only [mul_re, mul_im, ofReal_im, intCast_im, mul_zero, sub_zero, hσ, zero_mul,
        Real.exp_zero]
    dsimp only [E, B, W]
    rw [norm_mul, norm_mul, norm_mul, hNorm, mul_one,
      norm_cpow_eq_rpow_re_of_pos hx.1,
      norm_cpow_eq_rpow_re_of_pos (hX η x hx).1]
    simp only [sub_re, one_re, neg_re, z, add_re, mul_I_re, ofReal_im, neg_zero, add_zero,
      ofReal_re]
  have hVi (η : ℤˣ) : IntegrableOn V (S η) := by
    have h := ((hEint η).integral_prod_left).const_mul D
    exact IntegrableOn.congr_fun h (fun x hx => (hPoint η x hx).symm) (hSm η)
  have hEval (η : ℤˣ) :
      C * (∫ x in S η, V x) =
        I * ∫ s : ℝ, triangularKernel σ ω ε η lam (c + s * I) g * signedMellin f η (c + s * I) := by
    rw [setIntegral_congr_fun (hSm η) (hPoint η), integral_const_mul,
      integral_integral_swap (hEint η), ← mul_assoc]
    have hAssoc (s : ℝ) : (∫ x in S η, E η (x,s)) =
        (∫ x in S η, B x * ((|X x| : ℝ) : ℂ) ^ (-z s)) * signedMellin f η (z s) := by
      dsimp only [E, signedMellin, F]
      rw [integral_mul_const]
    simp_rw [hAssoc]
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with s
    dsimp only [triangularKernel, signedRegion, S, B, C, D, X, z, r]
    push_cast
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [hπ, I_ne_zero]
  have hZero : f 0 = 0 := image_eq_zero_of_notMem_tsupport hf0
  have hPos (x : ℝ) : x ∈ S 1 ↔ 0 < x ∧ 0 < X x := by
    change (0 < x ∧ 0 < ((↑(1 : ℤˣ) : ℤ) : ℝ) * X x) ↔ _
    simp
  have hNeg (x : ℝ) : x ∈ S (-1) ↔ 0 < x ∧ X x < 0 := by
    change (0 < x ∧ 0 < ((↑(-1 : ℤˣ) : ℤ) : ℝ) * X x) ↔ _
    simp
  have hPart : (Ioi (0 : ℝ)).indicator V = (S 1).indicator V + (S (-1)).indicator V := by
    funext x
    rw [Pi.add_apply]
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
      rcases lt_trichotomy (X x) 0 with hn | hz | hp
      · rw [indicator_of_notMem (fun h => hn.not_gt ((hPos x).1 h).2),
          indicator_of_mem ((hNeg x).2 ⟨hx, hn⟩), zero_add]
      · rw [indicator_of_notMem (fun h => (ne_of_gt ((hPos x).1 h).2) hz),
          indicator_of_notMem (fun h => (ne_of_lt ((hNeg x).1 h).2) hz), zero_add]
        simp [V, hz, hZero]
      · rw [indicator_of_mem ((hPos x).2 ⟨hx, hp⟩),
          indicator_of_notMem (fun h => hp.not_gt ((hNeg x).1 h).2), add_zero]
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
        indicator_of_notMem (fun h => hx ((hPos x).1 h).1),
        indicator_of_notMem (fun h => hx ((hNeg x).1 h).1), add_zero]
  have hI : (∫ x in Ioi (0 : ℝ), V x) = (∫ x in S 1, V x) + ∫ x in S (-1), V x := by
    rw [← integral_indicator measurableSet_Ioi, hPart]
    simp only [Pi.add_apply]
    rw [integral_add ((hVi 1).integrable_indicator (hSm 1))
      ((hVi (-1)).integrable_indicator (hSm (-1))),
      integral_indicator (hSm 1), integral_indicator (hSm (-1))]
  have hFin : (Finset.univ : Finset ℤˣ) = {1, -1} := by
    ext η
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun _ => Int.units_eq_one_or η, fun _ => trivial⟩
  have hL : signedMellin (triangularAction σ ω g f) ε lam =
      C * ∫ x in Ioi (0 : ℝ), V x := by
    rw [signedMellin, mellin, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    have hPhase : cexp (ω * g.τ + σ * (g.d * (((ε : ℤ) : ℂ) * x) + g.b)) =
        C * cexp (σ * g.d * ((ε : ℤ) : ℂ) * x) := by
      dsimp only [C]
      rw [← Complex.exp_add]
      congr 1
      ring
    simp only [smul_eq_mul, triangularAction, triangularCocycle, V, B, X, r,
      ofReal_mul, ofReal_intCast, hPhase, mul_assoc]
    ring
  rw [hL, hI, mul_add, hEval, hEval, hFin, Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]

end SFVK.AffineHeisenberg
