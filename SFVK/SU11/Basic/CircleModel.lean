/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import SFVKMathlib.MeasureTheory.Group.Multiplier
public import SFVK.SU11.Basic.Coordinates

/-!
# The circle model of the principal series of `SU(1,1)`

The fractional linear right action `z ↦ (a z + conj b) / (b z + conj a)` on the unit circle and
its multiplier give the model of Vilenkin–Klimyk, *Representation of Lie Groups and Special
Functions*, Vol. 1, §6.4.1 (1)–(5), pp. 298–299. The circle is `AddCircle (2π)`, with Mathlib's
Haar probability measure and Fourier basis, and a point `θ` corresponds to `fourier 1 θ`.

The multiplier is `|u|^(2τ) (u/|u|)^e` for the denominator `u`: the complex power is taken only
on the positive real modulus, and the phase has the natural-number exponent `e ∈ {0, 1}`.

## Main definitions

* `SFVK.SU11.circleAct`: the right action on the circle, and `circleMulAction` the associated
  left action `g • θ = circleAct g⁻¹ θ`.
* `SFVK.SU11.principalAction`: the principal-series operator on pointwise functions.
* `SFVK.SU11.principalSeries`: the representation on `L²` that agrees almost everywhere with
  `principalAction` and has continuous orbit maps, when one exists, and the trivial
  representation otherwise. Its existence is `SFVK.SU11.exists_principalSeries`.
-/

public noncomputable section

open AddCircle Complex MeasureTheory MulAction
open scoped ComplexConjugate InnerProductSpace Real

namespace SFVK.SU11

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The denominator of the fractional linear action on complex coordinates. -/
@[expose]
def circleDenominator (g : SU11) (z : ℂ) : ℂ := entryB g * z + conj (entryA g)

/-- The denominator of the circle action in terms of the two upper entries. -/
theorem circleDenominator_def (g : SU11) (z : ℂ) :
    circleDenominator g z = entryB g * z + conj (entryA g) :=
  (rfl)

/-- The numerator of the fractional linear action on complex coordinates. -/
@[expose]
def circleNumerator (g : SU11) (z : ℂ) : ℂ := entryA g * z + conj (entryB g)

/-- The numerator of the circle action in terms of the two upper entries. -/
theorem circleNumerator_def (g : SU11) (z : ℂ) :
    circleNumerator g z = entryA g * z + conj (entryB g) :=
  (rfl)

/-- The fractional linear right action on complex coordinates. -/
@[expose]
def circleMobius (g : SU11) (z : ℂ) : ℂ := circleNumerator g z / circleDenominator g z

/-- The fractional linear map as a quotient. -/
theorem circleMobius_def (g : SU11) (z : ℂ) :
    circleMobius g z = circleNumerator g z / circleDenominator g z :=
  (rfl)

/-- The denominator cannot vanish at a point of the unit circle. -/
theorem circleDenominator_ne_zero (g : SU11) {z : ℂ} (hz : ‖z‖ = 1) :
    circleDenominator g z ≠ 0 := by
  intro h
  rw [circleDenominator_def] at h
  have he : entryB g * z = -conj (entryA g) := eq_neg_of_add_eq_zero_left h
  have hn := congrArg norm he
  rw [norm_mul, hz, mul_one, norm_neg, Complex.norm_conj] at hn
  have hdet := normSq_entryA_sub_normSq_entryB g
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hn, sub_self] at hdet
  exact zero_ne_one hdet

/-- On the unit circle the numerator is `z` times the conjugate of the denominator. -/
theorem circleNumerator_eq_mul_conj (g : SU11) {z : ℂ} (hz : ‖z‖ = 1) :
    circleNumerator g z = z * conj (circleDenominator g z) := by
  have hzz : z * conj z = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, hz]
    norm_num
  simp only [circleNumerator_def, circleDenominator_def, map_add, map_mul, conj_conj]
  linear_combination (-conj (entryB g)) * hzz

/-- The fractional linear map preserves the unit circle. -/
theorem norm_circleMobius (g : SU11) {z : ℂ} (hz : ‖z‖ = 1) : ‖circleMobius g z‖ = 1 := by
  rw [circleMobius_def, circleNumerator_eq_mul_conj g hz, norm_div, norm_mul, hz, one_mul,
    Complex.norm_conj, div_self (norm_ne_zero_iff.2 (circleDenominator_ne_zero g hz))]

/-- The denominator of a product is the product of the denominators along the action. -/
theorem circleDenominator_mul (g h : SU11) {z : ℂ} (hz : ‖z‖ = 1) :
    circleDenominator (g * h) z =
      circleDenominator g z * circleDenominator h (circleMobius g z) := by
  have hD := circleDenominator_ne_zero g hz
  simp only [circleMobius_def, circleNumerator_def, circleDenominator_def, entryA_mul,
    entryB_mul, map_add, map_mul, conj_conj] at hD ⊢
  field_simp
  ring

/-- The numerator of a product, along the action. -/
theorem circleNumerator_mul (g h : SU11) {z : ℂ} (hz : ‖z‖ = 1) :
    circleNumerator (g * h) z = circleDenominator g z * circleNumerator h (circleMobius g z) := by
  have hD := circleDenominator_ne_zero g hz
  simp only [circleMobius_def, circleNumerator_def, circleDenominator_def, entryA_mul,
    entryB_mul, map_add, map_mul, conj_conj] at hD ⊢
  field_simp
  ring

/-- The fractional linear maps compose as a right action on the unit circle. -/
theorem circleMobius_mul (g h : SU11) {z : ℂ} (hz : ‖z‖ = 1) :
    circleMobius (g * h) z = circleMobius h (circleMobius g z) := by
  rw [circleMobius_def, circleDenominator_mul g h hz, circleNumerator_mul g h hz,
    mul_div_mul_left _ _ (circleDenominator_ne_zero g hz)]
  rfl

/-- On the circle of period `2π`, the Fourier character has angular frequency `n`. -/
theorem fourier_coe_two_pi (n : ℤ) (x : ℝ) :
    fourier n (x : 𝕋) = Complex.exp ((n : ℂ) * x * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  have hp : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- A translation multiplies a Fourier character by its value at the translation. -/
theorem fourier_add_angle (n : ℤ) (x y : 𝕋) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]

/-- The point of the unit circle at an angle has norm one. -/
theorem norm_fourier_one (θ : 𝕋) : ‖fourier 1 θ‖ = 1 := by
  rw [fourier_one]
  exact Circle.norm_coe _

/-- A point of the unit circle is the Fourier character at its argument. -/
theorem fourier_one_arg {w : ℂ} (hw : ‖w‖ = 1) : fourier 1 ((arg w : ℝ) : 𝕋) = w := by
  rw [fourier_coe_apply]
  have h : 2 * π * I * ((1 : ℤ) : ℂ) * (arg w : ℂ) / ((2 * π : ℝ) : ℂ) = arg w * I := by
    push_cast
    field_simp
  rw [h]
  have := norm_mul_exp_arg_mul_I w
  rwa [hw, ofReal_one, one_mul] at this

/-- The fractional linear right action on angles, using the complex argument modulo `2π`. -/
@[expose]
def circleAct (g : SU11) (θ : 𝕋) : 𝕋 :=
  (Complex.arg (circleMobius g (fourier 1 θ)) : 𝕋)

/-- The formula for the angular right action. -/
theorem circleAct_def (g : SU11) (θ : 𝕋) :
    circleAct g θ = (Complex.arg (circleMobius g (fourier 1 θ)) : 𝕋) :=
  (rfl)

/-- The angular action is the fractional linear action on the unit circle. -/
theorem fourier_circleAct (g : SU11) (θ : 𝕋) :
    fourier 1 (circleAct g θ) = circleMobius g (fourier 1 θ) :=
  fourier_one_arg (norm_circleMobius g (norm_fourier_one θ))

/-- The upper diagonal matrix entry is continuous. -/
private theorem continuous_entryA : Continuous entryA := by
  unfold entryA
  fun_prop

/-- The upper off-diagonal matrix entry is continuous. -/
private theorem continuous_entryB : Continuous entryB := by
  unfold entryB
  fun_prop

/-- The complex denominator is jointly continuous in the model coordinates. -/
theorem continuous_circleDenominator :
    Continuous fun p : SU11 × 𝕋 => circleDenominator p.1 (fourier 1 p.2) := by
  have ha := continuous_entryA
  have hb := continuous_entryB
  simp only [circleDenominator_def]
  fun_prop

/-- The fractional linear action is jointly continuous in the matrix and angle. -/
theorem continuous_circleAct : Continuous fun p : SU11 × 𝕋 => circleAct p.1 p.2 := by
  have hfourier := (fourier (T := 2 * π) 1).continuous
  have hdiv : Continuous fun p : SU11 × 𝕋 => circleMobius p.1 (fourier 1 p.2) := by
    simp only [circleMobius_def, circleNumerator_def]
    have ha := continuous_entryA
    have hb := continuous_entryB
    apply Continuous.div (by fun_prop) continuous_circleDenominator
    intro p
    exact circleDenominator_ne_zero p.1 (norm_fourier_one p.2)
  rw [continuous_iff_continuousAt]
  intro p
  refine (Complex.continuousAt_arg_coe_angle ?_).comp hdiv.continuousAt
  apply norm_ne_zero_iff.mp
  rw [norm_circleMobius p.1 (norm_fourier_one p.2)]
  exact one_ne_zero

/-- The identity element acts trivially on angles. -/
@[simp]
theorem circleAct_one (θ : 𝕋) : circleAct 1 θ = θ := by
  rw [circleAct_def, circleMobius_def, circleNumerator_def, circleDenominator_def, entryA_one,
    entryB_one]
  simp only [one_mul, map_zero, add_zero, zero_mul, map_one, zero_add, div_one, fourier_one]
  have h : AddCircle.toCircle θ = Real.Angle.toCircle θ := by
    induction θ using QuotientAddGroup.induction_on with
    | _ x =>
      rw [AddCircle.toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul]
      exact (Real.Angle.toCircle_coe x).symm
  rw [h]
  exact Real.Angle.arg_toCircle θ

/-- The action is on the right, so the second factor acts last. -/
theorem circleAct_mul (g h : SU11) (θ : 𝕋) :
    circleAct (g * h) θ = circleAct h (circleAct g θ) := by
  rw [circleAct_def, circleAct_def h, fourier_circleAct, circleMobius_mul g h (norm_fourier_one θ)]

/-- The left action associated to the fractional linear right action by inversion. -/
scoped instance circleMulAction : MulAction SU11 𝕋 where
  smul g θ := circleAct g⁻¹ θ
  one_smul θ := by
    -- Unfold scalar multiplication to use the right-action identity.
    change circleAct (1 : SU11)⁻¹ θ = θ
    rw [inv_one, circleAct_one]
  mul_smul g h θ := by
    -- Inversion reverses the order of composition in the right action.
    change circleAct (g * h)⁻¹ θ = circleAct g⁻¹ (circleAct h⁻¹ θ)
    rw [mul_inv_rev, circleAct_mul]

/-- The left action sends an angle to its image under the inverse matrix in the right action. -/
theorem circleMulAction_smul (g : SU11) (θ : 𝕋) :
    g • θ = circleAct g⁻¹ θ :=
  (rfl)

/-- The multiplier `|u|^(2τ) (u/|u|)^e` for the denominator `u`, with parity `e ∈ {0,1}`. -/
@[expose]
def principalMultiplier (τ : ℂ) (e : Fin 2) (g : SU11) (θ : 𝕋) : ℂ :=
  let u := circleDenominator g (fourier 1 θ)
  ((‖u‖ : ℂ) ^ (2 * τ)) * (u / (‖u‖ : ℂ)) ^ (e : ℕ)

/-- The modulus and phase expression for the circle multiplier. -/
theorem principalMultiplier_def (τ : ℂ) (e : Fin 2) (g : SU11) (θ : 𝕋) :
    let u := circleDenominator g (fourier 1 θ)
    principalMultiplier τ e g θ = ((‖u‖ : ℂ) ^ (2 * τ)) * (u / (‖u‖ : ℂ)) ^ (e : ℕ) :=
  (rfl)

/-- The circle multiplier depends continuously on the element and the angle. -/
theorem continuous_principalMultiplier (τ : ℂ) (e : Fin 2) :
    Continuous fun p : SU11 × 𝕋 => principalMultiplier τ e p.1 p.2 := by
  have hn (p : SU11 × 𝕋) : ‖circleDenominator p.1 (fourier 1 p.2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (circleDenominator_ne_zero p.1 (norm_fourier_one p.2))
  simp only [principalMultiplier_def]
  apply Continuous.mul
  · rw [continuous_iff_continuousAt]
    intro p
    let u := fun q : SU11 × 𝕋 => ‖circleDenominator q.1 (fourier 1 q.2)‖
    have hu : ContinuousAt u p := continuous_circleDenominator.norm.continuousAt
    exact (Complex.continuousAt_ofReal_cpow_const (u p) (2 * τ) (Or.inr (hn p))).comp hu
  · exact (continuous_circleDenominator.div
      (Complex.continuous_ofReal.comp continuous_circleDenominator.norm)
      (fun p => Complex.ofReal_ne_zero.mpr (hn p))).pow _

/-- The multiplier of a product factors along the right action. -/
theorem principalMultiplier_mul (τ : ℂ) (e : Fin 2) (g h : SU11) (θ : 𝕋) :
    principalMultiplier τ e (g * h) θ =
      principalMultiplier τ e g θ * principalMultiplier τ e h (circleAct g θ) := by
  simp only [principalMultiplier_def, fourier_circleAct]
  rw [circleDenominator_mul g h (norm_fourier_one θ)]
  set u := circleDenominator g (fourier 1 θ)
  set v := circleDenominator h (circleMobius g (fourier 1 θ))
  have hu : u ≠ 0 := circleDenominator_ne_zero g (norm_fourier_one θ)
  have hv : v ≠ 0 := circleDenominator_ne_zero h (norm_circleMobius g (norm_fourier_one θ))
  rw [norm_mul, ofReal_mul, mul_cpow_ofReal_nonneg (norm_nonneg u) (norm_nonneg v)]
  have hnu : (‖u‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hu)
  have hnv : (‖v‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 hv)
  rw [show u * v / ((‖u‖ : ℂ) * ‖v‖) = (u / ‖u‖) * (v / ‖v‖) by field_simp, mul_pow]
  ring

/-- The principal-series operator on pointwise functions on the circle. -/
@[expose]
def principalAction (τ : ℂ) (e : Fin 2) (g : SU11) (f : 𝕋 → ℂ) (θ : 𝕋) : ℂ :=
  principalMultiplier τ e g θ * f (circleAct g θ)

/-- The pointwise operator is weighted pullback along the right action. -/
theorem principalAction_def (τ : ℂ) (e : Fin 2) (g : SU11) (f : 𝕋 → ℂ) (θ : 𝕋) :
    principalAction τ e g f θ = principalMultiplier τ e g θ * f (circleAct g θ) :=
  (rfl)

/-- The identity acts trivially in the pointwise principal-series model. -/
@[simp]
theorem principalAction_one (τ : ℂ) (e : Fin 2) (f : 𝕋 → ℂ) :
    principalAction τ e 1 f = f := by
  funext θ
  simp [principalAction_def, principalMultiplier_def, circleDenominator_def]

/-- The pointwise principal-series operators satisfy the representation law. -/
theorem principalAction_mul (τ : ℂ) (e : Fin 2) (g h : SU11) (f : 𝕋 → ℂ) :
    principalAction τ e (g * h) f = principalAction τ e g (principalAction τ e h f) := by
  funext θ
  simp only [principalAction_def, principalMultiplier_mul, circleAct_mul]
  ring

/-- The principal-series multiplier is a cocycle for the associated left action. -/
theorem isMultiplierCocycle_principalMultiplier (τ : ℂ) (e : Fin 2) :
    IsMultiplierCocycle (principalMultiplier τ e) := by
  apply (multiplierAction_law_iff _).mp
  have heq (g : SU11) (f : 𝕋 → ℂ) (θ : 𝕋) :
      multiplierAction (principalMultiplier τ e) g f θ = principalAction τ e g f θ := by
    simp only [multiplierAction_def, circleMulAction_smul, inv_inv, principalAction_def]
  refine ⟨fun f θ => by rw [heq, principalAction_one], ?_⟩
  intro g h f θ
  have hh : multiplierAction (principalMultiplier τ e) h f = principalAction τ e h f :=
    funext (heq h f)
  rw [heq (g * h) f θ, heq g _ θ, hh, principalAction_mul]

/-- A representation on `L²` realizes the principal series when it agrees almost everywhere
with the pointwise formula and has continuous orbit maps. -/
@[expose]
def IsPrincipalSeriesRealization (τ : ℂ) (e : Fin 2)
    (U : ContRepresentation ℂ SU11 (Lp ℂ 2 (haarAddCircle (T := 2 * π)))) : Prop :=
  (∀ g f, (U g f : 𝕋 → ℂ) =ᵐ[haarAddCircle] principalAction τ e g f) ∧
    ∀ f, Continuous fun g => U g f

/-- The principal series on `L²`: the realization of the pointwise formula when one exists,
and the trivial representation otherwise. -/
@[expose]
def principalSeries (τ : ℂ) (e : Fin 2) :
    ContRepresentation ℂ SU11 (Lp ℂ 2 (haarAddCircle (T := 2 * π))) :=
  open Classical in
  if h : ∃ U, IsPrincipalSeriesRealization τ e U then h.choose
  else ContRepresentation.trivial ℂ SU11 _

/-- When a realization exists, `principalSeries` is one. -/
theorem isPrincipalSeriesRealization_principalSeries {τ : ℂ} {e : Fin 2}
    (h : ∃ U, IsPrincipalSeriesRealization τ e U) :
    IsPrincipalSeriesRealization τ e (principalSeries τ e) := by
  unfold principalSeries
  split_ifs with h'
  · exact h'.choose_spec
  · exact absurd h h'

end SFVK.SU11
