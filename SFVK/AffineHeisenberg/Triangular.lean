/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.AffineHeisenberg.Basic
public import DLMF.Confluent.Basic.Whittaker

/-!
# the triangular group and the Whittaker functions

Statements of §2 of the roadmap `Roadmaps/AffineHeisenbergGroups/README.md` (section numbers
`§x.y`).
Sources: Vilenkin–Klimyk Vol. 1 §§5.1–5.2, pp. 207–220; Klimyk–Vilenkin Ch. 4 §1.4 (11)–(21), pp.
205–207.
Theorems not yet proved are stated with `sorry`.
-/

@[expose] public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open DLMF.Confluent
open scoped Real ComplexConjugate InnerProductSpace ENNReal

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

/-- §2.1. **Unitarity range.** -/
theorem lintegral_triangularAction_iff (σ ω : ℂ) :
    (∀ (g : TriangularGroup) (f : ℝ → ℂ), Measurable f →
      ∫⁻ x, ‖triangularAction σ ω g f x‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2) ↔
      σ.re = 0 ∧ ω.re = 1 / 2 := by
  sorry

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
  sorry

/-- §2.3. **Kernel realization.** -/
theorem signedMellin_triangularAction (σ ω : ℂ) (hσ : σ.re = 0) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hf0 : (0 : ℝ) ∉ tsupport f)
    (g : TriangularGroup) (hg : g.a ≠ 0) (ε : ℤˣ) (lam : ℂ) (c : ℝ) (hlam : 0 < lam.re)
    (hlc : lam.re < c) (hc : c < 1) :
    signedMellin (triangularAction σ ω g f) ε lam =
      ∑ η : ℤˣ, Complex.I * ∫ s : ℝ, triangularKernel σ ω ε η lam (c + s * Complex.I) g *
        signedMellin f η (c + s * Complex.I) := by
  sorry

/-- §2.4. **Kernels of `g_+(t)`.** -/
theorem triangularKernel_gPlus (σ ω lam μ : ℂ) (t : ℝ) (ht : 0 < t) :
    (lam.re < μ.re → 0 < lam.re →
      triangularKernel σ ω 1 1 lam μ (gPlus t) =
        Gamma (μ - lam) * Gamma lam / (2 * π * Complex.I * Gamma μ) * (t : ℂ) ^ (lam - μ)) ∧
    (0 < lam.re → μ.re < 1 →
      triangularKernel σ ω (-1) 1 lam μ (gPlus t) =
        Gamma lam * Gamma (1 - μ) / (2 * π * Complex.I * Gamma (lam - μ + 1)) *
          (t : ℂ) ^ (lam - μ)) ∧
    (lam.re < μ.re → μ.re < 1 →
      triangularKernel σ ω (-1) (-1) lam μ (gPlus t) =
        Gamma (1 - μ) * Gamma (μ - lam) / (2 * π * Complex.I * Gamma (1 - lam)) *
          (t : ℂ) ^ (lam - μ)) ∧
    triangularKernel σ ω 1 (-1) lam μ (gPlus t) = 0 := by
  sorry

/-- §2.4. **Kernel of `g_-(t)`.** -/
theorem triangularKernel_gMinus (σ ω lam μ : ℂ) (t : ℝ) (hσt : (σ * t).re < 0)
    (hlm : μ.re < lam.re) :
    triangularKernel σ ω 1 1 lam μ (gMinus t) =
      Gamma (lam - μ) * (-σ * t) ^ (μ - lam) / (2 * π * Complex.I) ∧
    triangularKernel σ ω 1 (-1) lam μ (gMinus t) = 0 ∧
    triangularKernel σ ω (-1) 1 lam μ (gMinus t) = 0 := by
  sorry

/-- §2.5. **Whittaker kernels of `g_1(t)`** (at `σ = -1`). -/
theorem triangularKernel_gOne (ω lam μ : ℂ) (t : ℝ) (ht : 0 < t) :
    (0 < lam.re →
      triangularKernel (-1) ω 1 1 lam μ (gOne t) =
        Gamma lam * whittakerW ((1 - lam - μ) / 2) ((lam - μ) / 2) ((t : ℂ) ^ 2) /
          (2 * π * Complex.I * t)) ∧
    (0 < lam.re → μ.re < 1 →
      triangularKernel (-1) ω (-1) 1 lam μ (gOne t) =
        Gamma lam * Gamma (1 - μ) * whittakerM ((1 - lam - μ) / 2) ((lam - μ) / 2) ((t : ℂ) ^ 2) /
          (2 * π * Complex.I * t * Gamma (lam - μ + 1))) ∧
    triangularKernel (-1) ω 1 (-1) lam μ (gOne t) = 0 := by
  sorry

/-- §2.5. **Whittaker kernels of `g_2(t)`** (at `σ = -1`). -/
theorem triangularKernel_gTwo (ω lam μ : ℂ) (t : ℝ) (ht : 0 < t) :
    (μ.re < 1 →
      triangularKernel (-1) ω 1 1 lam μ (gTwo t) =
        Gamma (1 - μ) * whittakerW ((lam + μ - 1) / 2) ((lam - μ) / 2) ((t : ℂ) ^ 2) /
          (2 * π * Complex.I * t)) ∧
    (0 < lam.re → μ.re < 1 →
      triangularKernel (-1) ω 1 (-1) lam μ (gTwo t) =
        Gamma lam * Gamma (1 - μ) * whittakerM ((lam + μ - 1) / 2) ((lam - μ) / 2) ((t : ℂ) ^ 2) /
          (2 * π * Complex.I * t * Gamma (lam - μ + 1))) ∧
    triangularKernel (-1) ω (-1) 1 lam μ (gTwo t) = 0 := by
  sorry

/-- §2.5. **Reflection.** -/
theorem triangularKernel_reflect (σ ω : ℂ) (ε η : ℤˣ) (lam μ : ℂ) (g : TriangularGroup) :
    triangularKernel σ ω ε η lam μ ⟨-g.a, g.b, -g.d, g.τ⟩ =
      triangularKernel σ ω (-ε) (-η) lam μ g := by
  simp only [triangularKernel, Units.val_neg, Int.cast_neg, Complex.ofReal_neg]
  congr 1
  have h (x : ℝ) :
      Real.exp g.τ * -((ε : ℤ) : ℝ) * x + g.a =
        -(Real.exp g.τ * ((ε : ℤ) : ℝ) * x + -g.a) := by ring
  simp_rw [h, mul_neg, neg_mul, neg_neg, abs_neg]

end SFVK.AffineHeisenberg
