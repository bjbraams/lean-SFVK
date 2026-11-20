/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU11.Basic.Coordinates
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim
import SFVK.SU11.HaarShell
import SFVKMathlib.Analysis.Complex.EulerPhases

/-!
# Coordinates on `SU(1,1)`: Euler bijection and Haar measure

On the positive-boost box the Euler coordinates are a bijection onto the elements with a
nonzero off-diagonal entry, and `eulerHaar` is a two-sided Haar measure (Vilenkin–Klimyk,
*Representation of Lie Groups and Special Functions*, Vol. 1, §6.1.1 (10)–(12), p. 271, and
§6.1.4 (2), p. 275). The measure comparison computes the polar integral of the ambient
determinant shell using Mathlib's complex polar coordinates and one-dimensional substitution.
-/

public section

open Complex MeasureTheory Set TauCeti
open scoped ComplexConjugate ENNReal Real

namespace SFVK.SU11

open HaarShell

/-- The first entry has phase given by the half-sum of the Euler angles. -/
private theorem entryA_euler (α t γ : ℝ) :
    entryA (euler α t γ) = (Real.cosh (t / 2) : ℂ) * (Circle.exp ((α + γ) / 2) : ℂ) := by
  rw [euler_def, entryA_mul, entryA_mul, add_div, Circle.exp_add, Circle.coe_mul]
  simp only [entryA_rotation, entryA_boost, entryB_rotation, map_zero, mul_zero, add_zero,
    zero_mul, Circle.coe_exp]
  ring

/-- The second entry has phase given by the half-difference of the Euler angles. -/
private theorem entryB_euler (α t γ : ℝ) :
    entryB (euler α t γ) = (Real.sinh (t / 2) : ℂ) * (Circle.exp ((α - γ) / 2) : ℂ) := by
  rw [euler_def, entryB_mul, entryB_mul, sub_div, sub_eq_add_neg, Circle.exp_add, Circle.coe_mul,
    Circle.exp_neg, Circle.coe_inv_eq_conj]
  simp only [entryA_rotation, entryB_rotation, entryB_boost, mul_zero, zero_mul,
    add_zero, zero_add, Circle.coe_exp]
  ring

/-- The top row determines an element of the group. -/
private theorem eq_of_entries_eq {g h : SU11} (ha : entryA g = entryA h)
    (hb : entryB g = entryB h) : g = h := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_eq_matrix, coe_eq_matrix, ha, hb]

/-- A positive boost is uniquely determined by the norm of its second entry. -/
private theorem norm_entryB_euler (α γ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ‖entryB (euler α t γ)‖ = Real.sinh (t / 2) := by
  rw [entryB_euler, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sinh_nonneg_iff.mpr (by positivity))]

/-- The positive-boost Euler box parametrizes exactly the elements with a nonzero
off-diagonal entry, with unique angles in that box. -/
theorem bijOn_euler :
    BijOn (fun p : ℝ × ℝ × ℝ => euler p.1 p.2.1 p.2.2) eulerDomain
      {g : SU11 | entryB g ≠ 0} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨α, t, γ⟩ hp
    have ht := (mem_eulerDomain.mp hp).2.1
    simp only [mem_ofPred_eq, entryB_euler, mul_ne_zero_iff, Complex.ofReal_ne_zero]
    exact ⟨(Real.sinh_pos_iff.mpr (by positivity)).ne', Circle.coe_ne_zero _⟩
  · rintro ⟨α, t, γ⟩ hp ⟨α', t', γ'⟩ hp' heq
    obtain ⟨hα, ht, hγ⟩ := mem_eulerDomain.mp hp
    obtain ⟨hα', ht', hγ'⟩ := mem_eulerDomain.mp hp'
    have heqB := congrArg entryB heq
    have heqA := congrArg entryA heq
    have heqT : t = t' := by
      have hnorm := congrArg norm heqB
      simp only [norm_entryB_euler α γ ht.le, norm_entryB_euler α' γ' ht'.le] at hnorm
      have hh := Real.sinh_injective hnorm
      linarith
    subst t'
    have hphaseA : Circle.exp ((α + γ) / 2) = Circle.exp ((α' + γ') / 2) := by
      apply Subtype.ext
      rw [entryA_euler, entryA_euler] at heqA
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne') heqA
    have hphaseB : Circle.exp ((α - γ) / 2) = Circle.exp ((α' - γ') / 2) := by
      apply Subtype.ext
      rw [entryB_euler, entryB_euler] at heqB
      exact mul_left_cancel₀
        (Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr (by positivity : 0 < t / 2)).ne') heqB
    have hangles : (α, γ) = (α', γ') :=
      @Circle.injOn_exp_add_half_sub_half (α, γ) ⟨hα, hγ⟩ (α', γ') ⟨hα', hγ'⟩
        (Prod.ext hphaseA hphaseB)
    exact congrArg (fun p : ℝ × ℝ => (p.1, t, p.2)) hangles
  · intro g hg
    let t := 2 * Real.arsinh ‖entryB g‖
    have ht : 0 < t := mul_pos (by norm_num) (Real.arsinh_pos_iff.mpr (norm_pos_iff.mpr hg))
    have hsin : Real.sinh (t / 2) = ‖entryB g‖ := by
      rw [show t / 2 = Real.arsinh ‖entryB g‖ by dsimp [t]; ring, Real.sinh_arsinh]
    have hcos : Real.cosh (t / 2) = ‖entryA g‖ := by
      have hh := normSq_entryA_sub_normSq_entryB g
      rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at hh
      nlinarith [Real.cosh_sq_sub_sinh_sq (t / 2), Real.cosh_pos (t / 2), norm_nonneg (entryA g),
        congrArg (· ^ 2) hsin]
    obtain ⟨α, hα, γ, hγ, ha, hb⟩ := Circle.exists_exp_add_half_eq_and_exp_sub_half_eq
      (Circle.exp (arg (entryA g))) (Circle.exp (arg (entryB g)))
    refine ⟨(α, t, γ), mem_eulerDomain.mpr ⟨hα, ht, hγ⟩, eq_of_entries_eq ?_ ?_⟩
    · rw [entryA_euler, hcos, ha, Circle.coe_exp, norm_mul_exp_arg_mul_I]
    · rw [entryB_euler, hsin, hb, Circle.coe_exp, norm_mul_exp_arg_mul_I]

namespace HaarShell

/-- Changing the first polar radius to the squared radial scale. -/
private theorem lintegral_shell_first_radius (y : ℝ) (hy : 0 < y) (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioo y (Real.sqrt (1 + y ^ 2)),
      ENNReal.ofReal x * ENNReal.ofReal y * f (y / Real.sqrt (x ^ 2 - y ^ 2))) =
    ∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (y / 2) * f (y / Real.sqrt s) := by
  let upper := Real.sqrt (1 + y ^ 2)
  have hu : upper ^ 2 = 1 + y ^ 2 := Real.sq_sqrt (by positivity)
  have huy : y ≤ upper := by
    nlinarith [Real.sqrt_nonneg (1 + y ^ 2)]
  have hmono : StrictMonoOn (fun x : ℝ => x ^ 2 - y ^ 2) (Icc y upper) := by
    intro x hx x' hx' hlt
    exact sub_lt_sub_right ((sq_lt_sq₀ (hy.le.trans hx.1) (hy.le.trans hx'.1)).mpr hlt) _
  have himage : (fun x : ℝ => x ^ 2 - y ^ 2) '' Ioo y upper = Ioo 0 1 := by
    have hc : Continuous (fun x : ℝ => x ^ 2 - y ^ 2) := by fun_prop
    rw [hc.continuousOn.image_Ioo_of_strictMonoOn huy hmono, sub_self, hu]
    congr 1
    ring
  rw [← himage, lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioo
    (f' := fun x => 2 * x) _ (hmono.monotoneOn.mono Ioo_subset_Icc_self)]
  · apply setLIntegral_congr_fun measurableSet_Ioo
    intro x hx
    have hx0 : 0 ≤ x := hy.le.trans hx.1.le
    have hprod : ENNReal.ofReal (2 * x) * ENNReal.ofReal (y / 2) =
        ENNReal.ofReal x * ENNReal.ofReal y := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hx0]
      congr 1
      ring
    simp only [← mul_assoc, hprod]
  · intro x _
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (((hasDerivAt_pow 2 x).sub_const (y ^ 2)).hasDerivWithinAt (s := Ioo y upper))

/-- At fixed squared radial scale, normalizing the second radius contributes that scale. -/
private theorem lintegral_shell_second_radius (s : ℝ) (hs : 0 < s) (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y / 2) * f (y / Real.sqrt s)) =
      ENNReal.ofReal (s / 2) * ∫⁻ q in Ioi (0 : ℝ), ENNReal.ofReal q * f q := by
  let root := Real.sqrt s
  have hr : 0 < root := Real.sqrt_pos.2 hs
  have hsq : root ^ 2 = s := Real.sq_sqrt hs.le
  have himage : (root * ·) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact mul_pos hr hq
    · intro hy
      exact ⟨y / root, div_pos hy hr, by field_simp⟩
  conv_lhs => rw [← himage]
  rw [lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioi
    (f' := fun _ => root) _ (fun _ _ _ _ h => mul_le_mul_of_nonneg_left h hr.le),
    ← lintegral_const_mul'' _ (by fun_prop)]
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro q hq
    have hq0 : 0 ≤ q := hq.le
    have hcancel : root * q / Real.sqrt s = q := by
      change root * q / root = q
      field_simp
    have hprod : ENNReal.ofReal root * ENNReal.ofReal (root * q / 2) =
        ENNReal.ofReal (s / 2) * ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_mul hr.le, ← ENNReal.ofReal_mul (by positivity : 0 ≤ s / 2), ← hsq]
      congr 1
      ring
    simp only [hcancel, ← mul_assoc, hprod]
  · intro q _
    simpa only [mul_one, id_eq] using
      (((hasDerivAt_id q).const_mul root).hasDerivWithinAt (s := Ioi 0))

/-- The substitution `q = sinh (t/2)` transforms the normalized radius to the boost angle. -/
private theorem lintegral_radius_eq_lintegral_boost (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ q in Ioi (0 : ℝ), ENNReal.ofReal q * f q) =
      ENNReal.ofReal (1 / 4 : ℝ) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh t) * f (Real.sinh (t / 2)) := by
  let radius (t : ℝ) := Real.sinh (t / 2)
  have himage : radius '' Ioi 0 = Ioi 0 := by
    ext q
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Real.sinh_pos_iff.mpr (div_pos ht (by norm_num))
    · intro hq
      refine ⟨2 * Real.arsinh q,
        mul_pos (by norm_num : (0 : ℝ) < 2) (Real.arsinh_pos_iff.mpr hq), ?_⟩
      rw [show radius (2 * Real.arsinh q) = Real.sinh (Real.arsinh q) by unfold radius; ring_nf,
        Real.sinh_arsinh]
  conv_lhs => rw [← himage]
  rw [lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioi
    (f' := fun t => Real.cosh (t / 2) / 2) _
    (fun _ _ _ _ h => Real.sinh_le_sinh.mpr (div_le_div_of_nonneg_right h (by norm_num))),
    ← lintegral_const_mul'' _ (by fun_prop)]
  · apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hs : Real.sinh t = 2 * Real.sinh (t / 2) * Real.cosh (t / 2) := by
      simpa only [mul_div_cancel₀ t (two_ne_zero : (2 : ℝ) ≠ 0)] using Real.sinh_two_mul (t / 2)
    have hprod : ENNReal.ofReal (Real.cosh (t / 2) / 2) * ENNReal.ofReal (Real.sinh (t / 2)) =
        ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (Real.sinh t) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num), hs]
      congr 1
      ring
    simp only [← mul_assoc, hprod]
  · intro t _
    simpa only [div_eq_mul_inv, one_mul, mul_comm, id_eq] using
      (((hasDerivAt_id t).div_const 2).sinh.hasDerivWithinAt (s := Ioi 0))

/-- The polar radial density on the shell induces a multiple of the Euler boost density. -/
private theorem lintegral_shell_radii (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y in Ioi (0 : ℝ), ∫⁻ x in Ioo y (Real.sqrt (1 + y ^ 2)),
      ENNReal.ofReal x * ENNReal.ofReal y * f (y / Real.sqrt (x ^ 2 - y ^ 2))) =
      ENNReal.ofReal (1 / 16 : ℝ) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh t) * f (Real.sinh (t / 2)) := by
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (p.1 / 2) * f (p.1 / Real.sqrt p.2)) := by fun_prop
  have hscale :
      (∫⁻ s in Ioo (0 : ℝ) 1, ENNReal.ofReal (s / 2)) = ENNReal.ofReal (1 / 4 : ℝ) := by
    have hi : IntervalIntegrable (fun s : ℝ => s / 2) volume 0 1 :=
      (continuous_id.div_const 2).intervalIntegrable 0 1
    rw [restrict_Ioo_eq_restrict_Ioc, ← ofReal_integral_eq_lintegral_ofReal hi.1,
      ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_div, integral_id]
    · norm_num
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact div_nonneg hs.1.le (by norm_num)
  calc
    _ = ∫⁻ y in Ioi (0 : ℝ), ∫⁻ s in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (y / 2) * f (y / Real.sqrt s) := by
      exact setLIntegral_congr_fun measurableSet_Ioi fun y hy => lintegral_shell_first_radius y hy f
    _ = ∫⁻ s in Ioo (0 : ℝ) 1, ∫⁻ y in Ioi (0 : ℝ),
        ENNReal.ofReal (y / 2) * f (y / Real.sqrt s) :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ s in Ioo (0 : ℝ) 1,
        ENNReal.ofReal (s / 2) * ∫⁻ q in Ioi (0 : ℝ), ENNReal.ofReal q * f q := by
      exact setLIntegral_congr_fun measurableSet_Ioo fun s hs =>
        lintegral_shell_second_radius s hs.1 f hf
    _ = _ := by
      rw [lintegral_mul_const'' _ (by fun_prop), hscale, lintegral_radius_eq_lintegral_boost f hf,
        ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      norm_num

/-- Build a matrix with normalized second radius and two independent phases. -/
private noncomputable def normalizedPolar (q : ℝ) (z w : Circle) : SU11 :=
  ofPair ((Real.sqrt (1 + q ^ 2) : ℂ) * (z : ℂ)) ((q : ℂ) * (w : ℂ)) (by
    rw [normSq_mul, normSq_mul, Circle.normSq_coe, Circle.normSq_coe, mul_one, mul_one,
      normSq_ofReal, normSq_ofReal, ← sq, Real.sq_sqrt (by positivity), ← sq]
    ring)

/-- The polar parametrization is measurable jointly in its coordinates. -/
private theorem measurable_normalizedPolar :
    Measurable (fun p : ℝ × Circle × Circle => normalizedPolar p.1 p.2.1 p.2.2) := by
  apply Continuous.measurable
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    dsimp [normalizedPolar, ofPair] <;> fun_prop

/-- In polar coordinates, the ambient shell condition restricts the first radius. -/
private theorem polar_shell_condition (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (φ ψ : ℝ) :
    ![Complex.polarCoord.symm (x, φ), Complex.polarCoord.symm (y, ψ)] ∈ ambientShell ↔
      x ∈ Ioo y (Real.sqrt (1 + y ^ 2)) := by
  rw [mem_ambientShell, ambientDeterminant_def]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, normSq_eq_norm_sq,
    Complex.norm_polarCoord_symm, abs_of_pos hx, abs_of_pos hy]
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 1 + y ^ 2)
  simp only [mem_Ioo, sub_pos]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨(sq_lt_sq₀ hy.le hx.le).1 h₁,
      (sq_lt_sq₀ hx.le (Real.sqrt_nonneg _)).1 (by linarith)⟩
  · rintro ⟨h₁, h₂⟩
    have h₂' := (sq_lt_sq₀ hx.le (Real.sqrt_nonneg _)).2 h₂
    exact ⟨(sq_lt_sq₀ hy.le hx.le).2 h₁, by linarith⟩

/-- The shell projection of a polar column normalizes the radii and conjugates the second phase. -/
private theorem ambientProject_polar (x y φ ψ : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x ∈ Ioo y (Real.sqrt (1 + y ^ 2))) :
    ambientProject ![Complex.polarCoord.symm (x, φ), Complex.polarCoord.symm (y, ψ)] =
      normalizedPolar (y / Real.sqrt (x ^ 2 - y ^ 2)) (Circle.exp φ) (Circle.exp ψ)⁻¹ := by
  let column : Fin 2 → ℂ := ![Complex.polarCoord.symm (x, φ), Complex.polarCoord.symm (y, ψ)]
  have hd : ambientDeterminant column = x ^ 2 - y ^ 2 := by
    simp [column, ambientDeterminant_def, normSq_eq_norm_sq,
      abs_of_pos hx, abs_of_pos hy]
  have hpos : 0 < ambientDeterminant column :=
    (mem_ambientShell.mp ((polar_shell_condition x y hx hy φ ψ).2 hxy)).1
  have hr : 0 < Real.sqrt (x ^ 2 - y ^ 2) := Real.sqrt_pos.mpr (by rwa [← hd])
  have hroot : Real.sqrt (1 + (y / Real.sqrt (x ^ 2 - y ^ 2)) ^ 2) =
      x / Real.sqrt (x ^ 2 - y ^ 2) := by
    have hs : (Real.sqrt (x ^ 2 - y ^ 2)) ^ 2 = x ^ 2 - y ^ 2 :=
      Real.sq_sqrt (Real.sqrt_pos.mp hr).le
    have he : 1 + (y / Real.sqrt (x ^ 2 - y ^ 2)) ^ 2 =
        (x / Real.sqrt (x ^ 2 - y ^ 2)) ^ 2 := by
      rw [div_pow, div_pow, hs]
      field_simp [ne_of_gt (Real.sqrt_pos.mp hr)]
      ring
    rw [he, Real.sqrt_sq (div_nonneg hx.le hr.le)]
  have hrep (u θ : ℝ) : Complex.polarCoord.symm (u, θ) =
      (u : ℂ) * (Circle.exp θ : ℂ) := by
    simp [Complex.exp_mul_I]
  apply eq_of_entries_eq
  · rw [entryA_ambientProject column hpos, hd, normalizedPolar, entryA_ofPair, hroot,
      Complex.ofReal_div]
    simp only [column, Matrix.cons_val_zero, hrep]
    ring
  · rw [entryB_ambientProject column hpos, hd, normalizedPolar, entryB_ofPair,
      Circle.coe_inv_eq_conj, Complex.ofReal_div]
    simp only [column, Matrix.cons_val_zero, Matrix.cons_val_one, hrep, map_mul,
      Complex.conj_ofReal]
    ring

/-- Interchange the second and third coordinates of a product of four real lines. -/
private theorem measurePreserving_polar_reorder :
    MeasurePreserving (fun p : (ℝ × ℝ) × (ℝ × ℝ) => ((p.1.1, p.2.1), (p.1.2, p.2.2))) := by
  let v : Measure ℝ := volume
  have h₁ := measurePreserving_prodAssoc v v (v.prod v)
  have h₂ := (measurePreserving_prodAssoc v v v).symm MeasurableEquiv.prodAssoc
  have h₃ := (Measure.measurePreserving_swap (μ := v) (ν := v)).prod (MeasurePreserving.id v)
  have h₄ := measurePreserving_prodAssoc v v v
  have h₅ := (measurePreserving_prodAssoc v v (v.prod v)).symm MeasurableEquiv.prodAssoc
  exact h₅.comp (((MeasurePreserving.id v).prod (h₄.comp (h₃.comp h₂))).comp h₁)

set_option maxHeartbeats 350000 in
/-- In ambient polar coordinates the projection depends radially only on the normalized
second radius. -/
private theorem lintegral_ambient_shell
    (f : SU11 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, f g ∂ambientShellMeasure) =
      ENNReal.ofReal (1 / 16 : ℝ) * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh t) *
        ∫⁻ θ in Ioo (-π) π ×ˢ Ioo (-π) π,
          f (normalizedPolar (Real.sinh (t / 2)) (Circle.exp θ.1) (Circle.exp θ.2)⁻¹) := by
  let angleBox : Set (ℝ × ℝ) := Ioo (-π) π ×ˢ Ioo (-π) π
  let radiusBox : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0
  let polarBox : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
    Complex.polarCoord.target ×ˢ Complex.polarCoord.target
  let polarColumns (p : (ℝ × ℝ) × (ℝ × ℝ)) : Fin 2 → ℂ :=
    ![Complex.polarCoord.symm p.1, Complex.polarCoord.symm p.2]
  let integrand (p : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ≥0∞ :=
    ENNReal.ofReal p.1.1 * ENNReal.ofReal p.2.1 *
      ambientShell.indicator (fun z => f (ambientProject z)) (polarColumns p)
  have hindicator : Measurable (ambientShell.indicator (fun z => f (ambientProject z))) :=
    (hf.comp measurable_ambientProject).indicator isOpen_ambientShell.measurableSet
  have hcol : Measurable polarColumns := by
    have hpolar : Measurable Complex.polarCoord.symm := by
      have hrep : (fun p : ℝ × ℝ => (p.1 : ℂ) * (Circle.exp p.2 : ℂ)) =
          Complex.polarCoord.symm := by
        funext p
        simp [Complex.exp_mul_I]
      rw [← hrep]
      exact (Complex.continuous_ofReal.comp continuous_fst).mul
        (continuous_subtype_val.comp (Circle.exp.continuous.comp continuous_snd)) |>.measurable
    exact measurable_pi_iff.mpr (Fin.forall_fin_two.mpr
      ⟨hpolar.comp measurable_fst, hpolar.comp measurable_snd⟩)
  have hmeas : Measurable integrand :=
    ((measurable_fst.fst.ennreal_ofReal).mul measurable_snd.fst.ennreal_ofReal).mul
      (hindicator.comp hcol)
  have hpolar :
      (∫⁻ z, ambientShell.indicator (fun z => f (ambientProject z)) z) =
      ∫⁻ p in polarBox, integrand p := by
    rw [← Complex.lintegral_comp_pi_polarCoord_symm]
    let e := @MeasurableEquiv.finTwoArrow (ℝ × ℝ) _
    rw [← (volume_preserving_finTwoArrow (ℝ × ℝ)).setLIntegral_comp_preimage_emb
      e.measurableEmbedding integrand polarBox]
    have hset : (univ.pi fun _ : Fin 2 => Complex.polarCoord.target) =
        e ⁻¹' polarBox := by
      ext p
      simp only [mem_preimage, polarBox, mem_prod, mem_univ_pi, Fin.forall_fin_two]
      rfl
    rw [hset]
    simp only [Fin.prod_univ_two]
    apply lintegral_congr
    intro p
    have hp : (fun i => Complex.polarCoord.symm (p i)) = polarColumns (e p) := by
      funext i
      fin_cases i <;> rfl
    rw [hp]
    rfl
  let reorder (p : (ℝ × ℝ) × (ℝ × ℝ)) := ((p.1.1, p.2.1), (p.1.2, p.2.2))
  have hs : reorder ⁻¹' polarBox = radiusBox ×ˢ angleBox := by
    simp only [reorder, polarBox, radiusBox, angleBox, Complex.polarCoord_target]
    ext p
    simp only [mem_preimage, mem_prod]
    tauto
  have hreorder :
      (∫⁻ p in polarBox, integrand p) =
      ∫⁻ p in radiusBox ×ˢ angleBox, integrand (reorder p) := by
    rw [← hs]
    have hp : MeasurableSet polarBox :=
      (measurableSet_Ioi.prod measurableSet_Ioo).prod (measurableSet_Ioi.prod measurableSet_Ioo)
    exact (measurePreserving_polar_reorder.setLIntegral_comp_preimage hp hmeas).symm
  let phaseIntegral (q : ℝ) :=
    ∫⁻ θ in angleBox, f (normalizedPolar q (Circle.exp θ.1) (Circle.exp θ.2)⁻¹)
  have expPhase : Measurable Circle.exp := Circle.exp.continuous.measurable
  have hphaseMap : Measurable (fun p : ℝ × (ℝ × ℝ) =>
      (p.1, Circle.exp p.2.1, (Circle.exp p.2.2)⁻¹)) := by
    exact measurable_fst.prodMk ((expPhase.comp measurable_snd.fst).prodMk
      (expPhase.comp measurable_snd.snd).inv)
  have hphase := hf.comp (measurable_normalizedPolar.comp hphaseMap)
  have phaseMeas : Measurable phaseIntegral := hphase.lintegral_prod_right'
  have phaseAt (q : ℝ) : Measurable (fun θ : ℝ × ℝ =>
      f (normalizedPolar q (Circle.exp θ.1) (Circle.exp θ.2)⁻¹)) := by
    have h : Measurable (fun θ : ℝ × ℝ => (q, θ)) := measurable_const.prodMk measurable_id
    have hcomp := hphase.comp h
    exact hcomp
  have hradial (p : ℝ × ℝ) (hp : p ∈ radiusBox) :
      (∫⁻ θ in angleBox, integrand (reorder (p, θ))) =
      (Ioo p.2 (Real.sqrt (1 + p.2 ^ 2))).indicator (fun x =>
        ENNReal.ofReal x * ENNReal.ofReal p.2 *
          phaseIntegral (p.2 / Real.sqrt (x ^ 2 - p.2 ^ 2))) p.1 := by
    by_cases h : p.1 ∈ Ioo p.2 (Real.sqrt (1 + p.2 ^ 2))
    · rw [indicator_of_mem h]
      dsimp only [phaseIntegral]
      rw [← lintegral_const_mul'' _ (phaseAt _).aemeasurable]
      apply lintegral_congr
      intro θ
      have hmem := (polar_shell_condition p.1 p.2 hp.1 hp.2 θ.1 θ.2).2 h
      simp only [integrand, reorder, polarColumns, indicator_of_mem hmem,
        ambientProject_polar p.1 p.2 θ.1 θ.2 hp.1 hp.2 h]
    · rw [indicator_of_notMem h]
      have hz (θ : ℝ × ℝ) :
          polarColumns (reorder (p, θ)) ∉ ambientShell :=
        fun hmem => h ((polar_shell_condition p.1 p.2 hp.1 hp.2 θ.1 θ.2).1 hmem)
      simp only [integrand, indicator_of_notMem (hz _), mul_zero, lintegral_zero]
  rw [ambientShellMeasure_def, lintegral_map hf measurable_ambientProject,
    ← lintegral_indicator isOpen_ambientShell.measurableSet, hpolar, hreorder,
    Measure.volume_eq_prod, setLIntegral_prod]
  · calc
      _ = ∫⁻ y in Ioi (0 : ℝ), ∫⁻ x in Ioo y (Real.sqrt (1 + y ^ 2)),
          ENNReal.ofReal x * ENNReal.ofReal y * phaseIntegral (y / Real.sqrt (x ^ 2 - y ^ 2)) := by
        rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi) hradial,
          Measure.volume_eq_prod, setLIntegral_prod_symm]
        · apply setLIntegral_congr_fun measurableSet_Ioi
          intro y hy
          have hsubset : Ioo y (Real.sqrt (1 + y ^ 2)) ⊆ Ioi (0 : ℝ) :=
            fun _ hx => hy.trans hx.1
          dsimp only [Prod.fst, Prod.snd]
          rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
            inter_eq_left.mpr hsubset]
        · exact Measurable.aemeasurable ((by fun_prop : Measurable (fun p : ℝ × ℝ =>
            ENNReal.ofReal p.1 * ENNReal.ofReal p.2 *
              phaseIntegral (p.2 / Real.sqrt (p.1 ^ 2 - p.2 ^ 2)))).indicator
            (measurableSet_lt measurable_snd measurable_fst |>.inter
              (measurableSet_lt measurable_fst (by fun_prop))))
      _ = _ := lintegral_shell_radii phaseIntegral phaseMeas
  · exact (hmeas.comp measurePreserving_polar_reorder.measurable).aemeasurable

/-- Two polar angles, conjugating the second phase, give independent circle Haar measures
up to the two angular period lengths. -/
private theorem lintegral_polar_angles (f : Circle × Circle → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ θ in Ioo (-π) π ×ˢ Ioo (-π) π, f (Circle.exp θ.1, (Circle.exp θ.2)⁻¹)) =
      (ENNReal.ofReal (2 * π)) ^ 2 * ∫⁻ w, f w ∂(haarProb Circle).prod (haarProb Circle) := by
  let interval := Ioo (-π) π
  let ν := (volume : Measure ℝ).restrict interval
  let invertedPhase : ℝ → Circle := Inv.inv ∘ Circle.exp
  have hExp : Measurable Circle.exp := Circle.exp.continuous.measurable
  have hInv : Measurable invertedPhase := measurable_inv.comp hExp
  have hmap : ν.map Circle.exp = ENNReal.ofReal (2 * π) • haarProb Circle := by
    have ha : -π + 2 * π = π := by ring
    simpa only [ha] using Circle.map_exp_restrict_Ioo (-π)
  have hmapInv : ν.map invertedPhase = ENNReal.ofReal (2 * π) • haarProb Circle := by
    dsimp only [invertedPhase]
    rw [← Measure.map_map measurable_inv hExp, hmap,
      Measure.map_smul _ measurable_inv.aemeasurable, Measure.map_inv_eq_self]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  calc
    _ = ∫⁻ w, f w ∂Measure.map (Prod.map Circle.exp invertedPhase) (ν.prod ν) :=
      (lintegral_map hf (hExp.prodMap hInv)).symm
    _ = _ := by
      rw [← Measure.map_prod_map ν ν hExp hInv, hmap, hmapInv, Measure.prod_smul_left,
        Measure.prod_smul_right, smul_smul, ← sq, lintegral_smul_measure, smul_eq_mul]

/-- The normalized polar parametrization specializes to Euler coordinates. -/
private theorem normalizedPolar_euler (α t γ : ℝ) :
    normalizedPolar (Real.sinh (t / 2)) (Circle.exp ((α + γ) / 2)) (Circle.exp ((α - γ) / 2)) =
      euler α t γ := by
  have hcos : Real.sqrt (1 + Real.sinh (t / 2) ^ 2) = Real.cosh (t / 2) := by
    rw [← Real.cosh_sq', Real.sqrt_sq (Real.cosh_pos _).le]
  apply eq_of_entries_eq
  · simp only [normalizedPolar, entryA_ofPair, hcos, entryA_euler]
  · simp only [normalizedPolar, entryB_ofPair, entryB_euler]

/-- The normalized polar map remains measurable with the boost as radial parameter. -/
private theorem measurable_boostPolar :
    Measurable (fun p : ℝ × Circle × Circle =>
      normalizedPolar (Real.sinh (p.1 / 2)) p.2.1 p.2.2) := by
  have hsinh : Measurable (fun x : ℝ => Real.sinh (x / 2)) :=
    (Real.continuous_sinh.comp (continuous_id.div_const 2)).measurable
  have h : Measurable (fun p : ℝ × Circle × Circle =>
      (Real.sinh (p.1 / 2), p.2)) :=
    (hsinh.comp measurable_fst).prodMk measurable_snd
  have hcomp := measurable_normalizedPolar.comp h
  exact hcomp

/-- Integration against the Euler normalization separates the boost and the two phases. -/
private theorem lintegral_eulerHaar (f : SU11 → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, f g ∂eulerHaar) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.sinh t) *
        ∫⁻ w, f (normalizedPolar (Real.sinh (t / 2)) w.1 w.2)
          ∂(haarProb Circle).prod (haarProb Circle) := by
  let H (p : ℝ × Circle × Circle) := f (normalizedPolar (Real.sinh (p.1 / 2)) p.2.1 p.2.2)
  have hH : Measurable H := hf.comp measurable_boostPolar
  let phase (p : ℝ × ℝ × ℝ) : ℝ × Circle × Circle :=
    (p.2.1, Circle.exp ((p.1 + p.2.2) / 2), Circle.exp ((p.1 - p.2.2) / 2))
  have hphase : Measurable phase := by
    have hleft : Continuous (fun p : ℝ × ℝ × ℝ => (p.1 + p.2.2) / 2) := by fun_prop
    have hright : Continuous (fun p : ℝ × ℝ × ℝ => (p.1 - p.2.2) / 2) := by fun_prop
    exact measurable_snd.fst.prodMk ((Circle.exp.continuous.comp hleft).measurable.prodMk
      (Circle.exp.continuous.comp hright).measurable)
  have heq : (fun p : ℝ × ℝ × ℝ => euler p.1 p.2.1 p.2.2) =
      (fun p => normalizedPolar (Real.sinh (p.1 / 2)) p.2.1 p.2.2) ∘ phase :=
    funext fun p => (normalizedPolar_euler p.1 p.2.1 p.2.2).symm
  have hEuler : Measurable (fun p : ℝ × ℝ × ℝ => euler p.1 p.2.1 p.2.2) := by
    rw [heq]
    exact measurable_boostPolar.comp hphase
  rw [eulerHaar_def, lintegral_map hf hEuler]
  simp_rw [← normalizedPolar_euler]
  exact Circle.lintegral_eulerPhases_angleMeasure (fun t => ENNReal.ofReal (Real.sinh t))
    (by fun_prop) H hH

/-- The shell projection gives the Euler normalization up to the polar volume factor. -/
private theorem ambientShellMeasure_eq_smul_eulerHaar :
    ambientShellMeasure = ENNReal.ofReal (π ^ 2 / 4) • eulerHaar := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_ambient_shell f hf, lintegral_smul_measure, lintegral_eulerHaar f hf]
  let h (p : ℝ × Circle × Circle) := f (normalizedPolar (Real.sinh (p.1 / 2)) p.2.1 p.2.2)
  have hh : Measurable h := hf.comp measurable_boostPolar
  have phaseAt (t : ℝ) : Measurable (fun w : Circle × Circle => h (t, w)) := by
    have hi : Measurable (fun w : Circle × Circle => (t, w)) :=
      measurable_const.prodMk measurable_id
    exact hh.comp hi
  have hangular (t : ℝ) :
      (∫⁻ θ in Ioo (-π) π ×ˢ Ioo (-π) π,
        f (normalizedPolar (Real.sinh (t / 2)) (Circle.exp θ.1) (Circle.exp θ.2)⁻¹)) =
      (ENNReal.ofReal (2 * π)) ^ 2 * ∫⁻ w, h (t, w) ∂(haarProb Circle).prod (haarProb Circle) :=
    lintegral_polar_angles (fun w => h (t, w)) (phaseAt t)
  have hmeas : Measurable (fun t : ℝ => ENNReal.ofReal (Real.sinh t) *
      ∫⁻ w, h (t, w) ∂(haarProb Circle).prod (haarProb Circle)) :=
    Real.continuous_sinh.measurable.ennreal_ofReal.mul hh.lintegral_prod_right'
  simp_rw [hangular,
    mul_left_comm (ENNReal.ofReal (Real.sinh _)) ((ENNReal.ofReal (2 * π)) ^ 2)]
  rw [lintegral_const_mul'' _ hmeas.aemeasurable, ← mul_assoc, smul_eq_mul]
  congr 1
  rw [pow_two, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Rescale the ambient shell measure to the Euler normalization. -/
private theorem eulerHaar_eq_smul_ambientShellMeasure :
    eulerHaar = (ENNReal.ofReal (π ^ 2 / 4))⁻¹ • ambientShellMeasure := by
  rw [ambientShellMeasure_eq_smul_eulerHaar, smul_smul, ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top, one_smul]

end HaarShell

/-- The Euler normalization is a left Haar measure. -/
theorem isHaarMeasure_eulerHaar : eulerHaar.IsHaarMeasure := by
  let _ : ambientShellMeasure.IsHaarMeasure := isHaarMeasure_ambientShellMeasure
  rw [HaarShell.eulerHaar_eq_smul_ambientShellMeasure]
  exact Measure.IsHaarMeasure.smul ambientShellMeasure (by simp)
    (by simpa only [ENNReal.inv_ne_top] using (ENNReal.ofReal_pos.mpr (by positivity)).ne')

/-- The Euler normalization is right invariant, so `SU(1,1)` is unimodular. -/
theorem isMulRightInvariant_eulerHaar : eulerHaar.IsMulRightInvariant := by
  let _ : ambientShellMeasure.IsMulRightInvariant := isMulRightInvariant_ambientShellMeasure
  rw [HaarShell.eulerHaar_eq_smul_ambientShellMeasure]
  infer_instance

end SFVK.SU11
