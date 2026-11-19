/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import SFVK.RepresentationTheory.Multipliers
public import SFVK.SU11.Coordinates

/-!
# The circle model of the principal series of `SU(1,1)`

The fractional linear right action on the circle and its multiplier give the model of
Vilenkin–Klimyk, Vol. 1, §6.4.1 (1)–(5), pp. 298–299. The complex power is taken only
on the positive real modulus of the denominator; the phase has a natural-number
exponent given by the parity parameter. The circle carries Mathlib's Haar probability
measure and Fourier basis.
-/

public noncomputable section

open AddCircle MeasureTheory
open scoped ComplexConjugate InnerProductSpace Real

namespace SFVK.SU11

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The denominator of the fractional linear action on complex coordinates. -/
def circleDenom (g : Group) (z : ℂ) : ℂ := entryB g * z + conj (entryA g)

/-- The denominator of the circle action in terms of the two upper entries. -/
theorem circleDenom_def (g : Group) (z : ℂ) :
    circleDenom g z = entryB g * z + conj (entryA g) :=
  (rfl)

/-- The fractional linear right action on angles, using the complex argument modulo `2π`. -/
def circleAct (g : Group) (θ : 𝕋) : 𝕋 :=
  (Complex.arg ((entryA g * fourier 1 θ + conj (entryB g)) / circleDenom g (fourier 1 θ)) : 𝕋)

/-- The formula for the angular right action. -/
theorem circleAct_def (g : Group) (θ : 𝕋) :
    circleAct g θ =
      (Complex.arg ((entryA g * fourier 1 θ + conj (entryB g)) /
        circleDenom g (fourier 1 θ)) : 𝕋) :=
  (rfl)

/-- The denominator cannot vanish at a point of the unit circle. -/
theorem circleDenom_ne_zero (g : Group) {z : ℂ} (hz : ‖z‖ = 1) :
    circleDenom g z ≠ 0 := by
  intro h
  rw [circleDenom_def] at h
  have he : entryB g * z = -conj (entryA g) := eq_neg_of_add_eq_zero_left h
  have hn := congrArg norm he
  rw [norm_mul, hz, mul_one, norm_neg, Complex.norm_conj] at hn
  have hdet := normSq_entryA_sub_normSq_entryB g
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hn, sub_self] at hdet
  exact zero_ne_one hdet

/-- The identity element acts trivially on angles. -/
@[simp]
theorem circleAct_one (θ : 𝕋) : circleAct 1 θ = θ := by
  rw [circleAct_def, circleDenom_def, entryA_one, entryB_one]
  simp only [one_mul, map_zero, add_zero, zero_mul, map_one, zero_add, div_one, fourier_one]
  have h : AddCircle.toCircle θ = Real.Angle.toCircle θ := by
    induction θ using QuotientAddGroup.induction_on with
    | _ x =>
      rw [AddCircle.toCircle_apply_mk, div_self Real.two_pi_pos.ne', one_mul]
      exact (Real.Angle.toCircle_coe x).symm
  rw [h]
  exact Real.Angle.arg_toCircle θ

/-- The action is on the right, so the second factor acts last. -/
theorem circleAct_mul (g h : Group) (θ : 𝕋) :
    circleAct (g * h) θ = circleAct h (circleAct g θ) := by
  sorry

/-- The left action associated to the fractional linear right action by inversion. -/
scoped instance circleMulAction : MulAction Group 𝕋 where
  smul g θ := circleAct g⁻¹ θ
  one_smul θ := by
    -- Unfold scalar multiplication to use the right-action identity.
    change circleAct (1 : Group)⁻¹ θ = θ
    rw [inv_one, circleAct_one]
  mul_smul g h θ := by
    -- Inversion reverses the order of composition in the right action.
    change circleAct (g * h)⁻¹ θ = circleAct g⁻¹ (circleAct h⁻¹ θ)
    rw [mul_inv_rev, circleAct_mul]

/-- The left action sends an angle to its image under the inverse matrix in the right action. -/
theorem circleMulAction_smul (g : Group) (θ : 𝕋) :
    g • θ = circleAct g⁻¹ θ :=
  (rfl)

/-- The pushforward of circle Haar probability by the right action has the Poisson density. -/
theorem map_circleAct_haar (g : Group) :
    Measure.map (circleAct g) (haarAddCircle (T := 2 * π)) =
      (haarAddCircle (T := 2 * π)).withDensity
        (fun θ => ENNReal.ofReal (‖entryA g - entryB g * fourier 1 θ‖ ^ 2)⁻¹) := by
  sorry

/-- The multiplier `|u|^(2τ) (u/|u|)^e` for the denominator `u`, with parity `e ∈ {0,1}`. -/
def principalMultiplier (τ : ℂ) (e : Fin 2) (g : Group) (θ : 𝕋) : ℂ :=
  let u := circleDenom g (fourier 1 θ)
  ((‖u‖ : ℂ) ^ (2 * τ)) * (u / (‖u‖ : ℂ)) ^ (e : ℕ)

/-- The modulus and phase expression for the circle multiplier. -/
theorem principalMultiplier_def (τ : ℂ) (e : Fin 2) (g : Group) (θ : 𝕋) :
    let u := circleDenom g (fourier 1 θ)
    principalMultiplier τ e g θ = ((‖u‖ : ℂ) ^ (2 * τ)) * (u / (‖u‖ : ℂ)) ^ (e : ℕ) :=
  (rfl)

/-- The principal-series operator on pointwise functions on the circle. -/
def principalAction (τ : ℂ) (e : Fin 2) (g : Group) (f : 𝕋 → ℂ) (θ : 𝕋) : ℂ :=
  principalMultiplier τ e g θ * f (circleAct g θ)

/-- The pointwise operator is weighted pullback along the right action. -/
theorem principalAction_def (τ : ℂ) (e : Fin 2) (g : Group) (f : 𝕋 → ℂ) (θ : 𝕋) :
    principalAction τ e g f θ = principalMultiplier τ e g θ * f (circleAct g θ) :=
  (rfl)

/-- The identity acts trivially in the pointwise principal-series model. -/
@[simp]
theorem principalAction_one (τ : ℂ) (e : Fin 2) (f : 𝕋 → ℂ) :
    principalAction τ e 1 f = f := by
  funext θ
  simp [principalAction_def, principalMultiplier_def, circleDenom_def]

/-- The pointwise principal-series operators satisfy the representation law. -/
theorem principalAction_mul (τ : ℂ) (e : Fin 2) (g h : Group) (f : 𝕋 → ℂ) :
    principalAction τ e (g * h) f = principalAction τ e g (principalAction τ e h f) := by
  sorry

/-- The principal-series multiplier is a cocycle for the associated left action. -/
theorem principalMultiplier_isCocycle (τ : ℂ) (e : Fin 2) :
    IsMultiplierCocycle (principalMultiplier τ e) := by
  apply (multiplierAction_law_iff _).mp
  have heq (g : Group) (f : 𝕋 → ℂ) (θ : 𝕋) :
      multiplierAction (principalMultiplier τ e) g f θ = principalAction τ e g f θ := by
    simp only [multiplierAction_def, circleMulAction_smul, inv_inv, principalAction_def]
  refine ⟨fun f θ => by rw [heq, principalAction_one], ?_⟩
  intro g h f θ
  have hh : multiplierAction (principalMultiplier τ e) h f = principalAction τ e h f :=
    funext (heq h f)
  rw [heq (g * h) f θ, heq g _ θ, hh, principalAction_mul]

/-- The pointwise formula extends to a representation on `L²` with continuous orbit maps. -/
theorem exists_principalSeries (τ : ℂ) (e : Fin 2) :
    ∃ U : ContRepresentation ℂ Group (Lp ℂ 2 (haarAddCircle (T := 2 * π))),
      (∀ g f, (U g f : 𝕋 → ℂ) =ᵐ[haarAddCircle] principalAction τ e g f) ∧
        ∀ f, Continuous fun g => U g f := by
  sorry

/-- The principal series on `L²` obtained from the existence of the pointwise realization. -/
def principalSeries (τ : ℂ) (e : Fin 2) :
    ContRepresentation ℂ Group (Lp ℂ 2 (haarAddCircle (T := 2 * π))) :=
  (exists_principalSeries τ e).choose

/-- The `L²` action agrees almost everywhere with the pointwise formula. -/
theorem principalSeries_ae_eq (τ : ℂ) (e : Fin 2) (g : Group)
    (f : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    (principalSeries τ e g f : 𝕋 → ℂ) =ᵐ[haarAddCircle] principalAction τ e g f :=
  (exists_principalSeries τ e).choose_spec.1 g f

/-- Every orbit map of the principal series on `L²` is continuous. -/
theorem continuous_principalSeries_apply (τ : ℂ) (e : Fin 2)
    (f : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    Continuous fun g => principalSeries τ e g f :=
  (exists_principalSeries τ e).choose_spec.2 f

/-- The principal series is unitary on the circle exactly on the line `Re τ = -1/2`. -/
theorem principalSeries_isUnitary_iff (τ : ℂ) (e : Fin 2) :
    (principalSeries τ e).IsUnitary ↔ τ.re = -1 / 2 := by
  sorry

/-- The Hermitian adjoint has parameter `-conj τ - 1` and the inverse group argument. -/
theorem inner_principalSeries (τ : ℂ) (e : Fin 2) (g : Group)
    (f h : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    ⟪principalSeries τ e g f, h⟫_ℂ = ⟪f, principalSeries (-conj τ - 1) e g⁻¹ h⟫_ℂ := by
  sorry

/-- The Fourier mode of index `n` has magnetic weight `n - e/2` under diagonal rotations. -/
theorem principalSeries_rot (τ : ℂ) (e : Fin 2) (n : ℤ) (α : ℝ) :
    principalSeries τ e (rot α) (fourierLp (T := 2 * π) 2 n) =
      Complex.exp (((n : ℂ) - (e : ℂ) / 2) * α * Complex.I) • fourierLp (T := 2 * π) 2 n := by
  sorry

end SFVK.SU11
