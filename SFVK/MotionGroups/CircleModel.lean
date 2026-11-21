/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import SFVK.MotionGroups.Basic.CircleModel
public import SFVK.MotionGroups.Polar
import SFVKMathlib.MeasureTheory.Group.MultiplierRepresentation
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The circle models of `M(2)`: representation law, realization and unitarity

For complex `R`, the operators `T_R(g)` of `circleAction` form a representation; it agrees with
the sphere model at real `R`; it has an `L²(𝕋)` realization for every `R`; it is unitary
exactly for real `R`; `T_{-R}` and `T_R` are equivalent through the half-turn; and `T_R` is
irreducible for `R ≠ 0`. Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*,
Vol. 1, §4.1.2 (1)–(4), pp. 166–167; Miller, *Lie Theory and Special Functions*, §3-8, p. 73.
-/

public noncomputable section

open AddCircle Complex MeasureTheory MulAction
open scoped Real InnerProductSpace

namespace SFVK.MotionGroups

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- A rotation may be moved across the Euclidean inner product by taking its inverse. -/
theorem inner_rotE_left {n : ℕ} (k : SOn n) (a b : EuclideanSpace ℝ (Fin n)) :
    ⟪rotE k a, b⟫_ℝ = ⟪a, rotE k⁻¹ b⟫_ℝ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, rotE_def, Matrix.toLpLin_apply,
    star_trivial, ← Matrix.star_eq_inv, Matrix.specialUnitaryGroup.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

/-- The plane vector coordinate map into `ℂ` is injective. -/
private theorem toComplex_injective : Function.Injective toComplex := by
  intro a b h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  apply PiLp.ext
  intro i
  fin_cases i
  · simpa [toComplex_def] using hr
  · simpa [toComplex_def] using hi

/-- The complex coordinate of the circle vector is the first Fourier character. -/
theorem toComplex_unitVec (ψ : 𝕋) : toComplex (unitVec ψ) = fourier 1 ψ := by
  simp [toComplex_def, unitVec_def, Complex.re_add_im]

/-- Fourier characters on real angular representatives at period `2π`. -/
theorem fourier_circle_coe (n : ℤ) (x : ℝ) :
    fourier n (x : 𝕋) = Complex.exp (n * x * I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Fourier characters are the integer powers of the character of index one. -/
theorem fourier_eq_zpow (k : ℤ) (ψ : 𝕋) :
    (fourier k ψ : ℂ) = (fourier 1 ψ : ℂ) ^ k := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective ψ
  rw [fourier_circle_coe, fourier_circle_coe, Int.cast_one, one_mul, ← Complex.exp_int_mul]
  congr 1
  ring

/-- The inverse of a plane rotation negates its angle. -/
theorem rotation_neg (α : ℝ) : rotation (-α) = (rotation α)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← rotation_add, neg_add_cancel, rotation_zero]

/-- Applying the inverse rotation to the circle vector subtracts its angle. -/
theorem unitVec_sub_rotAngle (k : SOn 2) (ψ : 𝕋) :
    unitVec (ψ - rotAngle k) = rotE k⁻¹ (unitVec ψ) := by
  obtain ⟨α, rfl⟩ := exists_rotation_eq k
  apply toComplex_injective
  rw [rotAngle_rotation, ← rotation_neg, toComplex_rotE_rotation, toComplex_unitVec,
    toComplex_unitVec, sub_eq_add_neg]
  have hn : -(α : 𝕋) = ((-α : ℝ) : 𝕋) := (AddCircle.coe_neg (2 * π) (x := α)).symm
  rw [hn]
  have h (x y : 𝕋) : fourier 1 (x + y) = fourier 1 x * fourier 1 y := by
    rw [fourier_one, fourier_one, fourier_one, AddCircle.toCircle_add, Circle.coe_mul]
  rw [h, fourier_circle_coe]
  push_cast
  simp [mul_comm]

/-- Shifting a circle vector by half a period negates it. -/
theorem unitVec_add_pi (ψ : 𝕋) : unitVec (ψ + (π : 𝕋)) = -unitVec ψ := by
  apply toComplex_injective
  have h (x y : 𝕋) : fourier 1 (x + y) = fourier 1 x * fourier 1 y := by
    rw [fourier_one, fourier_one, fourier_one, AddCircle.toCircle_add, Circle.coe_mul]
  have hneg (a : EuclideanSpace ℝ (Fin 2)) : toComplex (-a) = -toComplex a := by
    simp only [toComplex_def, PiLp.neg_apply, Complex.ofReal_neg]
    ring
  rw [hneg, toComplex_unitVec, toComplex_unitVec, h, fourier_circle_coe]
  simp [Complex.exp_pi_mul_I]

/-- Representation law of the circle model. -/
theorem circleAction_mul (R : ℂ) (g h : MotionGroup 2) (f : 𝕋 → ℂ) :
    circleAction R (g * h) f = circleAction R g (circleAction R h f) := by
  funext ψ
  simp only [circleAction_def, MotionGroup.mul_a, MotionGroup.mul_k, rotAngle_mul,
    inner_add_left, inner_rotE_left, ← unitVec_sub_rotAngle, Complex.ofReal_add,
    mul_add, Complex.exp_add]
  rw [show ψ - (rotAngle g.k + rotAngle h.k) = ψ - rotAngle g.k - rotAngle h.k by abel,
    mul_assoc]

/-- The identity acts trivially in the circle model. -/
@[simp]
theorem circleAction_one (R : ℂ) (f : 𝕋 → ℂ) : circleAction R 1 f = f := by
  funext ψ
  simp [circleAction_def, ← rotation_zero]

/-- Agreement with the sphere model at `n = 2` and real `R`. -/
theorem circleAction_eq_motionAction (R : ℝ) (g : MotionGroup 2)
    (F : EuclideanSpace ℝ (Fin 2) → ℂ) (ψ : 𝕋) :
    circleAction R g (F ∘ unitVec) ψ = motionAction R g F (unitVec ψ) := by
  rw [circleAction_def, motionAction_def, Function.comp_apply, unitVec_sub_rotAngle]
  push_cast
  congr 2
  ring

/-- Size of the multiplier: `|e^{iR⟨a, e(ψ)⟩}| = e^{-Im R ⟨a, e(ψ)⟩}`. -/
theorem norm_circleAction (R : ℂ) (g : MotionGroup 2) (f : 𝕋 → ℂ) (ψ : 𝕋) :
    ‖circleAction R g f ψ‖ = Real.exp (-R.im * ⟪g.a, unitVec ψ⟫_ℝ) * ‖f (ψ - rotAngle g.k)‖ := by
  rw [circleAction_def, norm_mul, Complex.norm_exp]
  congr 2
  simp [Complex.mul_re]

namespace CircleRealization

/-- The argument of the first rotation column, viewed modulo a full turn, is continuous. -/
theorem continuous_rotAngle : Continuous rotAngle := by
  let column (k : SOn 2) : ℂ := (k.1 0 0 : ℂ) + (k.1 1 0 : ℂ) * I
  have hcircle (k : SOn 2) : column k ∈ Submonoid.unitSphere ℂ := by
    obtain ⟨α, rfl⟩ := exists_rotation_eq k
    rw [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Metric.mem_sphere, dist_zero_right]
    simp only [column, coe_rotation]
    simp [← Complex.exp_mul_I]
  have hcolumn : Continuous column := by
    have hentry (i j : Fin 2) : Continuous (fun k : SOn 2 => k.1 i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    exact (Complex.continuous_ofReal.comp (hentry 0 0)).add
      ((Complex.continuous_ofReal.comp (hentry 1 0)).mul continuous_const)
  exact AddCircle.homeomorphCircle'.symm.continuous.comp (hcolumn.subtype_mk hcircle)

/-- The unit plane vector depends continuously on its circle parameter. -/
theorem continuous_unitVec : Continuous unitVec := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re.comp (fourier 1).continuous
  · exact Complex.continuous_im.comp (fourier 1).continuous

/-- The rotation angle of a motion group element depends continuously on the element. -/
theorem continuous_motionRotation : Continuous (fun g : MotionGroup 2 => rotAngle g.k) := by
  have h : Continuous (fun g : MotionGroup 2 => (g.a, g.k)) := continuous_induced_dom
  exact continuous_rotAngle.comp h.snd

/-- The action of the motion group on the circle is the addition of its rotation angle. -/
scoped instance : MulAction (MotionGroup 2) 𝕋 where
  smul g ψ := ψ + rotAngle g.k
  one_smul ψ := by
    change ψ + rotAngle (1 : SOn 2) = ψ
    simp [← rotation_zero]
  mul_smul g h ψ := by
    change ψ + rotAngle ((g * h).k) = (ψ + rotAngle h.k) + rotAngle g.k
    rw [MotionGroup.mul_k, rotAngle_mul]
    abel

/-- The inverse group action subtracts the rotation angle. -/
private theorem inv_smul_circle (g : MotionGroup 2) (ψ : 𝕋) :
    g⁻¹ • ψ = ψ - rotAngle g.k := by
  have h (k : SOn 2) : rotAngle k⁻¹ = -rotAngle k := by
    apply eq_neg_of_add_eq_zero_left
    rw [← rotAngle_mul, inv_mul_cancel]
    simp [← rotation_zero]
  change ψ + rotAngle g.k⁻¹ = ψ - rotAngle g.k
  rw [h, sub_eq_add_neg]

/-- Circle Haar probability is preserved by the rotation part of every motion. -/
private theorem measurePreserving_smul_circle (g : MotionGroup 2) :
    MeasurePreserving (fun ψ : 𝕋 => g • ψ) haarAddCircle haarAddCircle :=
  measurePreserving_add_right haarAddCircle (rotAngle g.k)

/-- The exponential multiplier of the circle model. -/
private def circleWeight (R : ℂ) (g : MotionGroup 2) (ψ : 𝕋) : ℂ :=
  Complex.exp (I * R * (⟪g.a, unitVec ψ⟫_ℝ : ℝ))

/-- The multiplier and the inverse circle action give the pointwise circle model. -/
private theorem circleWeight_action (R : ℂ) (g : MotionGroup 2) (f : 𝕋 → ℂ) :
    multiplierAction (circleWeight R) g f = circleAction R g f := by
  funext ψ
  rw [multiplierAction_def, inv_smul_circle, circleWeight, circleAction_def]

/-- The group law for the circle model gives the multiplier cocycle. -/
private theorem isMultiplierCocycle_circleWeight (R : ℂ) :
    IsMultiplierCocycle (circleWeight R) := by
  apply (multiplierAction_law_iff _).mp
  constructor
  · intro f x
    rw [circleWeight_action, circleAction_one]
  · intro g h f x
    rw [circleWeight_action, circleWeight_action, circleWeight_action, circleAction_mul]

/-- The circle multiplier is jointly continuous. -/
private theorem continuous_circleWeight (R : ℂ) :
    Continuous (fun p : MotionGroup 2 × 𝕋 => circleWeight R p.1 p.2) := by
  have hp : Continuous (fun g : MotionGroup 2 => (g.a, g.k)) := continuous_induced_dom
  have ha : Continuous (fun g : MotionGroup 2 => g.a) := hp.fst
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    ((ha.comp continuous_fst).inner (continuous_unitVec.comp continuous_snd)))).cexp

end CircleRealization

open CircleRealization
open scoped CircleRealization

/-- `L²` realization of `T_R` for every complex `R`. -/
theorem exists_circleRealization (R : ℂ) : ∃ U, IsCircleRealization R U := by
  have hpull : Continuous (fun p : MotionGroup 2 × 𝕋 => p.1⁻¹ • p.2) := by
    simp_rw [inv_smul_circle]
    exact continuous_snd.sub (continuous_motionRotation.comp continuous_fst)
  obtain ⟨U, hU, hc⟩ := exists_stronglyContinuous_multiplierRepresentation haarAddCircle
    (isMultiplierCocycle_circleWeight R) (continuous_circleWeight R) hpull
    measurePreserving_smul_circle
  exact ⟨U, fun g f => by simpa only [circleWeight_action] using hU g f, hc⟩

/-- The circle representation agrees almost everywhere with the pointwise action. -/
theorem circleRep_ae_eq (R : ℂ) (g : MotionGroup 2) (f : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    (circleRep R g f : 𝕋 → ℂ) =ᵐ[haarAddCircle] circleAction R g f :=
  (isCircleRealization_circleRep (exists_circleRealization R)).1 g f

/-- The inner product with a polar translation uses the two real coordinates of the first
circle character. -/
theorem inner_planePoint_unitVec (r β : ℝ) (ψ : 𝕋) :
    ⟪planePoint r β, unitVec ψ⟫_ℝ =
      r * (Real.cos β * (fourier 1 ψ : ℂ).re + Real.sin β * (fourier 1 ψ : ℂ).im) := by
  simp [planePoint, unitVec_def, PiLp.inner_apply, Fin.sum_univ_two]
  ring

set_option maxHeartbeats 6000000 in
/-- Unitarity range: `T_R` is unitary exactly for real `R` (Vilenkin–Klimyk Vol. 1 §4.1.2,
p. 166). -/
theorem isUnitary_circleRep_iff (R : ℂ) : (circleRep R).IsUnitary ↔ R.im = 0 := by
  let μ : Measure 𝕋 := haarAddCircle
  let _ : MeasurableConstSMul (MotionGroup 2) 𝕋 := ⟨fun g =>
    (measurePreserving_smul_circle g).measurable⟩
  have hquasi : μ.IsQuasiInvariantWith (fun (_ : MotionGroup 2) (_ : 𝕋) => 1) := by
    intro g
    change μ.map (fun ψ : 𝕋 => g • ψ) = μ.withDensity 1
    rw [withDensity_one]
    exact (measurePreserving_smul_circle g).map_eq
  have hmeas (g : MotionGroup 2) : Continuous (circleWeight R g) :=
    (continuous_circleWeight R).comp (continuous_const.prodMk continuous_id)
  have hformula (g : MotionGroup 2) (f : Lp ℂ 2 μ) :
      (circleRep R g f : 𝕋 → ℂ) =ᵐ[μ] multiplierAction (circleWeight R) g f := by
    rw [circleWeight_action]
    exact circleRep_ae_eq R g f
  have hiff :
      (∃ U : ContRepresentation ℂ (MotionGroup 2) (Lp ℂ 2 μ),
        U.IsUnitary ∧ ∀ g f, (U g f : 𝕋 → ℂ) =ᵐ[μ] multiplierAction (circleWeight R) g f) ↔
        ∀ g, ∀ᵐ ψ ∂μ, ‖circleWeight R g ψ‖ₑ ^ 2 = 1 :=
    exists_isUnitary_multiplierAction_iff (μ := μ)
      (ρ := fun (_ : MotionGroup 2) (_ : 𝕋) => 1) (isMultiplierCocycle_circleWeight R)
      (fun g => (hmeas g).measurable) (fun _ => measurable_const) hquasi
  have hnorm (g : MotionGroup 2) (ψ : 𝕋) :
      ‖circleWeight R g ψ‖ = Real.exp (-R.im * ⟪g.a, unitVec ψ⟫_ℝ) := by
    rw [circleWeight, Complex.norm_exp]
    congr 2
    simp [Complex.mul_re]
  constructor
  · intro hU
    let g : MotionGroup 2 := ⟨planePoint 1 0, 1⟩
    have h : ∀ᵐ ψ ∂μ, ‖circleWeight R g ψ‖ₑ ^ 2 = 1 := hiff.mp ⟨circleRep R, hU, hformula⟩ g
    have h' : (fun ψ : 𝕋 => ‖circleWeight R g ψ‖ ^ 2) =ᵐ[μ] fun _ => 1 := by
      filter_upwards [h] with x hx
      simpa only [ENNReal.toReal_pow, toReal_eNorm, ENNReal.toReal_one]
        using congrArg ENNReal.toReal hx
    have heq := Measure.eq_of_ae_eq h' ((hmeas g).norm.pow 2) continuous_const
    have hzero := congrFun heq (0 : 𝕋)
    rw [hnorm] at hzero
    have hinner : ⟪g.a, unitVec (0 : 𝕋)⟫_ℝ = 1 := by
      simp [g, inner_planePoint_unitVec]
    rw [hinner, mul_one, ← Real.exp_nat_mul] at hzero
    have hzero' : (2 : ℝ) * -R.im = 0 := Real.exp_injective (by simpa using hzero)
    linarith
  · intro hR
    have hweight (g : MotionGroup 2) : ∀ᵐ ψ ∂μ, ‖circleWeight R g ψ‖ₑ ^ 2 = 1 :=
      Filter.Eventually.of_forall fun ψ => by
        rw [← ofReal_norm, hnorm, hR]
        simp
    obtain ⟨U, hUnitary, hU⟩ := hiff.mpr hweight
    rw [multiplierRep_unique hformula hU]
    exact hUnitary

/-- `T_{-R}` and `T_R` are equivalent through the half-turn `f ↦ f(· + π)`. -/
theorem circleAction_neg (R : ℂ) (g : MotionGroup 2) (f : 𝕋 → ℂ) :
    circleAction (-R) g (fun ψ => f (ψ + (π : 𝕋))) =
      fun ψ => circleAction R g f (ψ + (π : 𝕋)) := by
  funext ψ
  simp only [circleAction_def, unitVec_add_pi, inner_neg_right, Complex.ofReal_neg]
  rw [show (ψ + (π : 𝕋) - rotAngle g.k) = ψ - rotAngle g.k + (π : 𝕋) by abel]
  simp only [mul_neg, neg_mul]

/-- Irreducibility of `T_R` for `R ≠ 0` (Vilenkin–Klimyk Vol. 1 §4.1.2, p. 167): a closed
invariant subspace is `0` or everything. -/
theorem circleRep_irreducible {R : ℂ} (hR : R ≠ 0)
    (V : Submodule ℂ (Lp ℂ 2 (haarAddCircle (T := 2 * π))))
    (hV : IsClosed (V : Set (Lp ℂ 2 (haarAddCircle (T := 2 * π)))))
    (hinv : ∀ g, ∀ v ∈ V, circleRep R g v ∈ V) : V = ⊥ ∨ V = ⊤ := by
  sorry

/-- Differentiate the pointwise model along a line of pure translations. -/
theorem hasDerivAt_circleAction_translation (R : ℂ) (β t : ℝ) (f : 𝕋 → ℂ) (ψ : 𝕋) :
    HasDerivAt (fun x : ℝ => circleAction R ⟨planePoint x β, 1⟩ f ψ)
      ((I * R * (⟪planePoint 1 β, unitVec ψ⟫_ℝ : ℝ)) *
        circleAction R ⟨planePoint t β, 1⟩ f ψ) t := by
  let c : ℂ := I * R * ((⟪planePoint 1 β, unitVec ψ⟫_ℝ : ℝ) : ℂ)
  have hformula (x : ℝ) :
      circleAction R ⟨planePoint x β, 1⟩ f ψ = Complex.exp (c * x) * f ψ := by
    have hangle : rotAngle (1 : SOn 2) = (0 : 𝕋) := by simp [← rotation_zero]
    simp only [circleAction_def, hangle, sub_zero, c, inner_planePoint_unitVec, one_mul,
      Complex.ofReal_mul]
    congr 2
    ring
  simp_rw [hformula]
  have hd := (((hasDerivAt_id (t : ℂ)).const_mul c).comp_ofReal).cexp.mul_const (f ψ)
  change HasDerivAt (fun x : ℝ => Complex.exp (c * x) * f ψ)
    (c * (Complex.exp (c * t) * f ψ)) t
  convert hd using 1
  · rfl
  · simp only [id_eq, mul_one]
    ring

/-- Casimir value `-R²`: the second derivatives along the two coordinate translations add up
to `-R² f` (Vilenkin–Klimyk Vol. 1 §4.1.2 (4)–(9), p. 167). -/
theorem circleAction_casimir (R : ℂ) (f : 𝕋 → ℂ) (ψ : 𝕋) :
    deriv (deriv fun t : ℝ => circleAction R ⟨planePoint t 0, 1⟩ f ψ) 0 +
        deriv (deriv fun t : ℝ => circleAction R ⟨planePoint t (π / 2), 1⟩ f ψ) 0 =
      -R ^ 2 * f ψ := by
  have hgen (β : ℝ) :
      deriv (deriv fun t : ℝ => circleAction R ⟨planePoint t β, 1⟩ f ψ) 0 =
        (I * R * (⟪planePoint 1 β, unitVec ψ⟫_ℝ : ℝ)) ^ 2 * f ψ := by
    let c : ℂ := I * R * ((⟪planePoint 1 β, unitVec ψ⟫_ℝ : ℝ) : ℂ)
    have hd (t : ℝ) : deriv (fun x : ℝ => circleAction R ⟨planePoint x β, 1⟩ f ψ) t =
        c * circleAction R ⟨planePoint t β, 1⟩ f ψ :=
      (hasDerivAt_circleAction_translation R β t f ψ).deriv
    rw [funext hd, ((hasDerivAt_circleAction_translation R β 0 f ψ).const_mul c).deriv]
    have hzero : (⟨planePoint 0 β, 1⟩ : MotionGroup 2) = 1 := by
      apply MotionGroup.ext
      · rw [MotionGroup.one_a]
        apply PiLp.ext
        intro i
        fin_cases i <;> simp
      · exact MotionGroup.one_k.symm
    rw [hzero, circleAction_one]
    change c * (c * f ψ) = c ^ 2 * f ψ
    ring
  rw [hgen, hgen]
  have hnorm : (fourier 1 ψ : ℂ).re ^ 2 + (fourier 1 ψ : ℂ).im ^ 2 = 1 := by
    rw [pow_two, pow_two, ← Complex.normSq_apply, ← Complex.sq_norm,
      fourier_apply, Circle.norm_coe, one_pow]
  have hcast : ((fourier 1 ψ : ℂ).re : ℂ) ^ 2 + ((fourier 1 ψ : ℂ).im : ℂ) ^ 2 = 1 := by
    exact_mod_cast hnorm
  simp only [inner_planePoint_unitVec, Real.cos_zero, Real.sin_zero, Real.cos_pi_div_two,
    Real.sin_pi_div_two, zero_mul, one_mul, zero_add, add_zero]
  linear_combination (I ^ 2 * R ^ 2 * f ψ) * hcast + (R ^ 2 * f ψ) * Complex.I_sq

end SFVK.MotionGroups
