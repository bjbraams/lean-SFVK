/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

import DLMF.Gamma.MellinBarnes
public import SFVK.AffineHeisenberg.Basic

/-!
# the `ax + b` group, the Mellin transform and the Gamma function

Statements of §1 of the roadmap `Roadmaps/AffineHeisenbergGroups/README.md` (section numbers
`§x.y`).
Sources: Vilenkin–Klimyk Vol. 1 §3.4, pp. 128–135; Klimyk–Vilenkin Ch. 4 §1.2, p. 204, §3.1, p. 218.
The two beta integrals use lean-DLMF's Mellin and Mellin–Barnes formulas.
-/

@[expose] public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open scoped Real ComplexConjugate InnerProductSpace ENNReal

/-- §1.1. **Representation law.** -/
theorem affineAction_mul (lam : ℂ) :
    (∀ g h : AxB, ∀ f, affineAction lam (g * h) f = affineAction lam g (affineAction lam h f)) ∧
      ∀ f, affineAction lam 1 f = f := by
  refine ⟨fun g h f => ?_, fun f => ?_⟩
  · funext x
    simp only [affineAction, AxB.mul_a, AxB.mul_b]
    rw [show lam * ((g.a * h.b + g.b : ℝ) : ℂ) * x =
        lam * g.b * x + lam * h.b * ((g.a * x : ℝ) : ℂ) by push_cast; ring, Complex.exp_add,
      mul_assoc, mul_comm g.a h.a, mul_assoc]
    rw [mul_assoc h.a]
  · funext x
    simp [affineAction]

/-- §1.1. **Dictionary** to SpecialFunctionsGroupModels §2.4. -/
theorem affineAction_mul_I (ρ : ℝ) :
    affineAction (ρ * Complex.I) = multiplierAction (axbCocycle ρ) := by
  funext g f x
  simp only [affineAction, multiplierAction, axbCocycle]
  have hx : g⁻¹ • x = g.a * x := by
    show x / g⁻¹.a = g.a * x
    rw [AxB.inv_a, div_inv_eq_mul, mul_comm]
  rw [hx]
  congr 2
  push_cast
  ring

/-- §1.1. **Dilations are diagonal.** -/
theorem mellin_affineAction_dilation (lam : ℂ) (a : ℝ) (ha : 0 < a) (f : ℝ → ℂ) (w : ℂ) :
    mellin (affineAction lam ⟨a, 0, ha⟩ f) w = (a : ℂ) ^ (-w) * mellin f w := by
  have : affineAction lam ⟨a, 0, ha⟩ f = fun x => f (a * x) := by
    funext x
    simp [affineAction]
  rw [this, mellin_comp_mul_left f w ha, smul_eq_mul]

/-- §1.1. **Infinitesimal operators.** -/
theorem mellin_infinitesimal :
    (∀ (f : ℝ → ℂ) (w : ℂ), mellin (fun x => (x : ℂ) * f x) w = mellin f (w + 1)) ∧
    ∀ (f : ℝ → ℂ) (w : ℂ), ContDiff ℝ 1 f → HasCompactSupport f → tsupport f ⊆ Ioi 0 →
      mellin (fun x => (x : ℂ) * deriv f x) w = -w * mellin f w := by
  sorry

/-- §1.2. **Gamma kernel.** -/
theorem mellin_affineAction_eq_integral (lam : ℂ) (a b : ℝ) (ha : 0 < a)
    (hlam : 0 < (-lam * b).re) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (hfs : tsupport f ⊆ Ioi 0) (w : ℂ) (c : ℝ) (hc : c < w.re) :
    mellin (affineAction lam ⟨a, b, ha⟩ f) w =
      Complex.I * ∫ s : ℝ, affineGammaKernel lam a b w (c + s * Complex.I) *
        mellin f (c + s * Complex.I) := by
  sorry

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
