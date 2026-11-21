/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.AffineHeisenberg.Basic

/-!
# the groups in coordinates

Statements of §0 of the roadmap `Roadmaps/AffineHeisenbergGroups/README.md` (section numbers
`§x.y`).
Sources: Vilenkin–Klimyk Vol. 1 §5.1.1, pp. 207–208, §5.2.1 (1)–(3), pp. 213–214, §5.2.4 (2), p.
219; Miller §4-11, p. 113.
-/

public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open scoped Real ComplexConjugate InnerProductSpace ENNReal

/-- §0.1. **Matrix realization.** -/
theorem TriangularGroup.toMatrix_mul :
    (∀ g h : TriangularGroup, toMatrix (g * h) = toMatrix g * toMatrix h) ∧
      Function.Injective toMatrix := by
  constructor
  · intro g h
    ext i j : 2
    fin_cases i <;> fin_cases j <;>
      simp [toMatrix, Matrix.mul_apply, Fin.sum_univ_three, Real.exp_add, add_comm,
        add_left_comm, add_assoc]
  · intro g h heq
    apply TriangularGroup.ext
    · exact congrArg (fun m : Matrix (Fin 3) (Fin 3) ℝ => m 0 1) heq
    · exact congrArg (fun m : Matrix (Fin 3) (Fin 3) ℝ => m 0 2) heq
    · exact congrArg (fun m : Matrix (Fin 3) (Fin 3) ℝ => m 1 2) heq
    · exact Real.exp_injective (congrArg (fun m : Matrix (Fin 3) (Fin 3) ℝ => m 1 1) heq)

/-- §0.1. **Centre.** The centre is the subgroup `z(t) = (0, t, 0, 0)`. -/
theorem TriangularGroup.mem_center_iff (g : TriangularGroup) :
    g ∈ Subgroup.center TriangularGroup ↔ g.a = 0 ∧ g.d = 0 ∧ g.τ = 0 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have hminus := h (modulationElement 1)
    have hplus := h (translationElement 1)
    have ha := congrArg TriangularGroup.b hminus
    have hd := congrArg TriangularGroup.b hplus
    have ht := congrArg TriangularGroup.d hminus
    simp only [TriangularGroup.centralCoordinate_mul, TriangularGroup.modulation_mul,
      modulationElement, translationElement,
      zero_mul, mul_zero, mul_one, zero_add, add_zero, Real.exp_zero, one_mul] at ha hd ht
    refine ⟨by linarith, by linarith, Real.exp_injective ?_⟩
    simpa using (show Real.exp g.τ = 1 by linarith)
  · rintro ⟨ha, hd, ht⟩ h
    apply TriangularGroup.ext <;> simp [ha, hd, ht, add_comm]

/-- §0.1. **Factorizations.** -/
theorem TriangularGroup.factorizations :
    (∀ b d τ : ℝ,
      (⟨0, b, d, τ⟩ : TriangularGroup) =
         dilation τ * modulationElement (d * Real.exp (-τ)) * centralElement b) ∧
    (∀ t : ℝ, equalTranslationModulation t =
       modulationElement t * translationElement t * centralElement (t ^ 2 / 2)) ∧
    ∀ t x : ℝ, 0 < x → 0 < x + t →
      translationElement t * equalTranslationModulation x =
        dilation (Real.log (x / (x + t)) / 2) *
           equalTranslationModulation (Real.sqrt (x * (x + t))) *
          dilation (-(Real.log (x / (x + t)) / 2)) * centralElement (t * x / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b d τ
    have hexp : Real.exp τ * Real.exp (-τ) = 1 := by rw [← Real.exp_add]; simp
    apply TriangularGroup.ext <;> simp [dilation, modulationElement, centralElement]
    calc d = (Real.exp τ * Real.exp (-τ)) * d := by rw [hexp, one_mul]
      _ = Real.exp τ * (d * Real.exp (-τ)) := by ring
  · intro t
    apply TriangularGroup.ext <;> simp [equalTranslationModulation, modulationElement,
      translationElement, centralElement]
  · intro t x hx hxt
    let angle := Real.log (x / (x + t)) / 2
    let radius := Real.sqrt (x * (x + t))
    have hr : 0 ≤ radius := Real.sqrt_nonneg _
    have hr_sq : radius ^ 2 = x * (x + t) := Real.sq_sqrt (mul_nonneg hx.le hxt.le)
    have hangle_sq : Real.exp angle ^ 2 = x / (x + t) := by
      rw [← Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      have heq : 2 * angle = Real.log (x / (x + t)) := by dsimp [angle]; ring
      rw [heq, Real.exp_log (div_pos hx hxt)]
    have hfirst : radius = (x + t) * Real.exp angle := by
      apply (sq_eq_sq₀ hr (by positivity)).mp
      rw [mul_pow, hangle_sq, hr_sq]
      field_simp [hxt.ne']
    have hsecond : Real.exp angle * radius = x := by
      rw [hfirst]
      calc
        _ = (x + t) * Real.exp angle ^ 2 := by ring
        _ = x := by rw [hangle_sq]; field_simp [hxt.ne']
    have hthird : radius * Real.exp (-angle) = x + t := by
      rw [Real.exp_neg, hfirst, mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _), mul_one]
    apply TriangularGroup.ext
    · simpa [dilation, equalTranslationModulation, translationElement, centralElement,
      angle, radius, add_comm] using hthird.symm
    · simp only [dilation, equalTranslationModulation, translationElement, centralElement,
      TriangularGroup.centralCoordinate_mul,
        TriangularGroup.translation_mul, Real.exp_zero, zero_mul, mul_zero,
        add_zero, zero_add, mul_one]
      change x ^ 2 / 2 + t * x = radius ^ 2 / 2 + t * x / 2
      rw [hr_sq]
      ring
    · simpa [dilation, equalTranslationModulation, translationElement,
      centralElement] using hsecond.symm
    · simp [dilation, equalTranslationModulation, translationElement, centralElement]

/-- §0.1. **Heisenberg subgroup.** -/
theorem heisenbergToTriangular_injective : Function.Injective heisenbergToTriangular := by
  intro p q h
  have ha := congrArg TriangularGroup.a h
  have hb := congrArg TriangularGroup.b h
  have hd := congrArg TriangularGroup.d h
  simp only [heisenbergToTriangular, MonoidHom.coe_mk, OneHom.coe_mk] at ha hb hd
  exact TauCeti.HeisenbergGroup.ext ha hd hb

/-- The oscillator matrix in terms of its rotation factor. -/
private theorem oscillator_toMatrix (g : Oscillator) :
    Oscillator.toMatrix g =
      !![(1 : ℂ), rotationFactor g.α * conj g.w / 2, (g.δ : ℂ) * I - (normSq g.w : ℂ) / 8;
        0, rotationFactor g.α, -g.w / 2; 0, 0, 1] := rfl

/-- §0.2. **Matrix realization.** -/
theorem Oscillator.toMatrix_mul (g h : Oscillator) :
    toMatrix (g * h) = toMatrix g * toMatrix h := by
  have hnorm (z : ℂ) : (normSq z : ℂ) = z * conj z := (mul_conj z).symm
  have hphase := rotationFactor_mul_conj g.α
  have himag (z : ℂ) : z - conj z = 2 * (z.im : ℂ) * I := by
    apply Complex.ext
    · simp [Complex.mul_re]
    · simp [Complex.mul_im]
      ring
  rw [oscillator_toMatrix, oscillator_toMatrix, oscillator_toMatrix]
  ext i j : 2
  fin_cases i <;> fin_cases j
  all_goals simp [rotationFactor_add, Matrix.mul_apply, Fin.sum_univ_three, -Complex.mul_im]
  · linear_combination (rotationFactor h.α * conj h.w / 2) * hphase
  · simp only [hnorm, map_add, map_mul]
    have hcross := himag (rotationFactor g.α * conj g.w * h.w)
    simp only [map_mul, Complex.conj_conj] at hcross
    linear_combination -(h.w * conj h.w / 8) * hphase + hcross / 8
  · ring

/-- §0.2. **Kernel of the matrix realization.** -/
theorem Oscillator.toMatrix_eq_one_iff (g : Oscillator) :
    toMatrix g = 1 ↔ g.w = 0 ∧ g.δ = 0 ∧ ∃ k : ℤ, g.α = 2 * π * k := by
  rw [oscillator_toMatrix]
  constructor
  · intro h
    have hw := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℂ => m 1 2) h
    have hd := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℂ => m 0 2) h
    have he := congrArg (fun m : Matrix (Fin 3) (Fin 3) ℂ => m 1 1) h
    have hz : g.w = 0 := by simpa using hw
    have hδ : g.δ = 0 := by simpa [hz] using hd
    have hphase : rotationFactor g.α = 1 := by simpa using he
    have hcircle : Circle.exp (-g.α) = 1 := by
      apply Circle.ext
      simpa only [Circle.coe_exp, rotationFactor, Complex.ofReal_neg, Circle.coe_one] using hphase
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp hcircle
    exact ⟨hz, hδ, -n, by push_cast; linarith⟩
  · rintro ⟨hw, hd, k, hk⟩
    have hcircle : Circle.exp (-g.α) = 1 := Circle.exp_eq_one.mpr
      ⟨-k, by rw [hk]; push_cast; ring⟩
    have he : rotationFactor g.α = 1 := by
      simpa only [Circle.coe_exp, rotationFactor, Complex.ofReal_neg, Circle.coe_one]
        using congrArg (fun z : Circle => (z : ℂ)) hcircle
    ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [hw, hd, he]

/-- §0.2. **Heisenberg subgroup.** -/
theorem heisenbergToOscillator_injective : Function.Injective heisenbergToOscillator := by
  intro p q h
  have hw := congrArg Oscillator.w h
  have hδ := congrArg Oscillator.δ h
  simp only [heisenbergToOscillator, MonoidHom.coe_mk, OneHom.coe_mk, Complex.mk.injEq] at hw hδ
  obtain ⟨hx, hy⟩ := hw
  refine TauCeti.HeisenbergGroup.ext hx hy ?_
  rw [hx, hy] at hδ
  linarith

end SFVK.AffineHeisenberg
