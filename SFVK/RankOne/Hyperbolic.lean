/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.RankOne.Horospherical
public import SFVK.RankOne.LorentzInvariance
public import SFVKMathlib.MeasureTheory.Group.GelfandPair
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real hyperbolic space: geometry, volume and Laplacian

Transitivity of `SO₀(n, 1)` on `ℍⁿ`, invariance of the distance, invariance of the volume and its
polar and horospherical forms, invariance and radial part of the Laplace–Beltrami operator, plane
waves and Poisson integrals, and the Gel'fand pair `(SO₀(n, 1), SO(n))`. The transitivity proof
uses the determinant of a rank-one perturbation of the identity from Tau Ceti.

Sources: Wawrzyńczyk, *Group Representations and Special Functions*, §11.1, (11.1.6), p. 392;
§11.5, (11.5.1)–(11.5.8), Theorem 11.5.1, pp. 411–412; §18.1, Proposition 18.1.6,
(18.1.12)–(18.1.15), Lemma 18.1.7, pp. 610–611; Heckman–Schlichtkrull, *Harmonic Analysis and
Special Functions on Symmetric Spaces*, Part I §5.4, (5.4.3), p. 83.

## Main results

* `SFVK.RankOne.exists_orbitMap_eq`: transitivity of the Lorentz action.
* `SFVK.RankOne.hyperbolicDist_mulVec`: the distance is invariant.
* `SFVK.RankOne.lintegral_hyperbolicMeasure_radial`: polar integration of radial functions.
* `SFVK.RankOne.hyperbolicLaplacian_comp_lorentz`: the Laplacian of a function of a Lorentz
  projection.
* `SFVK.RankOne.hyperbolicLaplacian_radial`: the radial Laplacian.
* `SFVK.RankOne.hyperbolicLaplacian_planeWave`: the plane-wave eigenvalue.
-/

public noncomputable section

open Complex Filter Topology MeasureTheory Set
open scoped Real Matrix ENNReal ContDiff

namespace SFVK.RankOne

namespace LorentzGeometry

/-- Additivity of the Lorentz pairing in its first argument. -/
private theorem lorentz_add_left {n : ℕ} (x y b : Fin (n + 1) → ℝ) :
    lorentz (x + y) b = lorentz x b + lorentz y b := by
  simp only [lorentz_def, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- Subtraction in the first argument of the Lorentz pairing. -/
private theorem lorentz_sub_left {n : ℕ} (x y b : Fin (n + 1) → ℝ) :
    lorentz (x - y) b = lorentz x b - lorentz y b := by
  simp only [lorentz_def, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

/-- Linearity under scaling of the first argument of the Lorentz pairing. -/
private theorem lorentz_smul_left {n : ℕ} (c : ℝ) (x y : Fin (n + 1) → ℝ) :
    lorentz (c • x) y = c * lorentz x y := by
  simp only [lorentz_def, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_sub]

/-- Subtraction in the second argument of the Lorentz pairing. -/
private theorem lorentz_sub_right {n : ℕ} (b x y : Fin (n + 1) → ℝ) :
    lorentz b (x - y) = lorentz b x - lorentz b y := by
  rw [lorentz_comm b (x - y), lorentz_sub_left, lorentz_comm x b, lorentz_comm y b]

/-- Linearity under scaling of the second argument of the Lorentz pairing. -/
private theorem lorentz_smul_right {n : ℕ} (c : ℝ) (x y : Fin (n + 1) → ℝ) :
    lorentz x (c • y) = c * lorentz x y := by
  rw [lorentz_comm x (c • y), lorentz_smul_left, lorentz_comm y x]

/-- The Euclidean covector of a Lorentz vector. -/
private noncomputable def signedCoordinates {n : ℕ} (x : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  Fin.cons (x 0) (fun i => -x i.succ)

/-- The Euclidean pairing with this covector is the Lorentz pairing. -/
private theorem signedCoordinates_dotProduct {n : ℕ} (x y : Fin (n + 1) → ℝ) :
    signedCoordinates x ⬝ᵥ y = lorentz x y := by
  simp only [signedCoordinates, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    neg_mul, Finset.sum_neg_distrib, lorentz_def, sub_eq_add_neg]

/-- The Lorentz reflection reversing a non-null vector and fixing its orthogonal complement. -/
private noncomputable def reflection {n : ℕ} (u : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  1 - Matrix.vecMulVec u ((2 / lorentz u u) • signedCoordinates u)

/-- The rank-one formula for the action of a Lorentz reflection. -/
private theorem reflection_mulVec {n : ℕ} (u v : Fin (n + 1) → ℝ) :
    reflection u *ᵥ v = v - ((2 / lorentz u u) * lorentz u v) • u := by
  rw [reflection, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    smul_dotProduct, signedCoordinates_dotProduct, smul_eq_mul, op_smul_eq_smul]

/-- The determinant of a reflection along a non-null vector. -/
private theorem det_reflection {n : ℕ} (u : Fin (n + 1) → ℝ) (hu : lorentz u u ≠ 0) :
    (reflection u).det = -1 := by
  rw [reflection, TauCeti.det_one_sub_vecMulVec, smul_dotProduct, signedCoordinates_dotProduct,
    smul_eq_mul]
  field_simp
  ring

/-- A reflection along a non-null vector preserves the Lorentz pairing. -/
private theorem lorentz_reflection_mulVec {n : ℕ} (u : Fin (n + 1) → ℝ)
    (hu : lorentz u u ≠ 0) (v w : Fin (n + 1) → ℝ) :
    lorentz (reflection u *ᵥ v) (reflection u *ᵥ w) = lorentz v w := by
  simp only [reflection_mulVec, lorentz_sub_left, lorentz_sub_right, lorentz_smul_left,
    lorentz_smul_right, lorentz_comm v u]
  field_simp
  ring

/-- A reflection along a non-null vector is an involution. -/
private theorem reflection_mulVec_reflection_mulVec {n : ℕ} (u : Fin (n + 1) → ℝ)
    (hu : lorentz u u ≠ 0) (v : Fin (n + 1) → ℝ) :
    reflection u *ᵥ (reflection u *ᵥ v) = v := by
  simp only [reflection_mulVec, lorentz_sub_right, lorentz_smul_right]
  have hcoeff : 2 / lorentz u u * (lorentz u v - 2 / lorentz u u * lorentz u v * lorentz u u) =
      -(2 / lorentz u u * lorentz u v) := by
    field_simp
    ring
  rw [hcoeff, neg_smul, sub_neg_eq_add, sub_add_cancel]

/-- The Lorentz pairing of two points of the upper sheet is positive. -/
private theorem lorentz_pos_of_mem_hyperboloid {n : ℕ} {x y : Fin (n + 1) → ℝ}
    (hx : x ∈ hyperboloid n) (hy : y ∈ hyperboloid n) :
    0 < lorentz x y := by
  have hnorm {z : Fin (n + 1) → ℝ} (hz : z ∈ hyperboloid n) :
      Real.sqrt (∑ i : Fin n, z i.succ ^ 2) < z 0 := by
    have h := hz.1
    rw [lorentz_def] at h
    exact (Real.sqrt_lt' hz.2).mpr (by simpa only [pow_two] using
      (show (∑ i : Fin n, z i.succ * z i.succ) < z 0 * z 0 by linarith))
  have hC := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i : Fin n => x i.succ)
    (fun i : Fin n => y i.succ)
  rw [lorentz_def, sub_pos]
  apply hC.trans_lt
  exact mul_lt_mul'' (hnorm hx) (hnorm hy) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- A Lorentz unit vector pairing positively with an upper-sheet point lies on that sheet. -/
private theorem mem_hyperboloid_of_lorentz_pos {n : ℕ} {x y : Fin (n + 1) → ℝ}
    (hx : x ∈ hyperboloid n) (hy : lorentz y y = 1) (hxy : 0 < lorentz x y) :
    y ∈ hyperboloid n := by
  refine ⟨hy, ?_⟩
  by_contra! h
  have hne : y 0 ≠ 0 := by
    intro hy0
    have hself := hy
    rw [lorentz_def, hy0, zero_mul, zero_sub] at hself
    have hn : 0 ≤ ∑ i : Fin n, y i.succ * y i.succ :=
      Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
    linarith
  have hneg : -y ∈ hyperboloid n := by
    refine ⟨?_, ?_⟩
    · simp only [← neg_one_smul ℝ y, lorentz_smul_left, lorentz_smul_right, hy, neg_mul, one_mul,
        neg_neg]
    · simp only [Pi.neg_apply, Left.neg_pos_iff]
      exact lt_of_le_of_ne h hne
  have hp := lorentz_pos_of_mem_hyperboloid hx hneg
  rw [← neg_one_smul ℝ y, lorentz_smul_right, neg_one_mul] at hp
  linarith

end LorentzGeometry

set_option maxHeartbeats 1000000 in
/-- **Transitivity**: every point of `ℍⁿ` is `g o` for some `g ∈ SO₀(n, 1)`. -/
theorem exists_orbitMap_eq (n : ℕ) {x : Fin (n + 1) → ℝ} (hx : x ∈ hyperboloid n) :
    ∃ g : lorentzGroup n, orbitMap n g = x := by
  open LorentzGeometry in
  let o := basePoint n
  let u := x + o
  have ho : o ∈ hyperboloid n := basePoint_mem_hyperboloid n
  have hoo : lorentz o o = 1 := ho.1
  have hxo : lorentz o x = x 0 := lorentz_basePoint_left x
  have hx' : 0 < x 0 := hx.2
  have huo : lorentz u o = x 0 + 1 := by
    dsimp only [u]
    rw [lorentz_add_left, lorentz_comm x o, hxo, hoo]
  have huu : lorentz u u = 2 * (x 0 + 1) := by
    dsimp only [u]
    rw [lorentz_add_left, lorentz_comm x (x + o), lorentz_comm o (x + o),
      lorentz_add_left, lorentz_add_left, hx.1, lorentz_comm x o, hxo, hoo]
    ring
  have ho₀ : lorentz o o ≠ 0 := by rw [hoo]; norm_num
  have hu₀ : lorentz u u ≠ 0 := by rw [huu]; positivity
  -- Compose the reflection reversing the base vector with the reflection in their sum.
  let A := reflection u * reflection o
  let B := reflection o * reflection u
  have hA (y z : Fin (n + 1) → ℝ) : lorentz (A *ᵥ y) (A *ᵥ z) = lorentz y z := by
    simp only [A, ← Matrix.mulVec_mulVec, lorentz_reflection_mulVec u hu₀,
      lorentz_reflection_mulVec o ho₀]
  have hAB (z : Fin (n + 1) → ℝ) : A *ᵥ (B *ᵥ z) = z := by
    simp only [A, B, ← Matrix.mulVec_mulVec,
      reflection_mulVec_reflection_mulVec o ho₀, reflection_mulVec_reflection_mulVec u hu₀]
  have hAo : A *ᵥ o = x := by
    have hRo : reflection o *ᵥ o = -o := by
      rw [reflection_mulVec, hoo]
      norm_num
      module
    have hRu : reflection u *ᵥ o = -x := by
      rw [reflection_mulVec, huu, huo]
      have hc : 2 / (2 * (x 0 + 1)) * (x 0 + 1) = 1 := by field_simp
      simp only [hc, one_smul, u]
      abel
    dsimp only [A]
    rw [← Matrix.mulVec_mulVec, hRo, Matrix.mulVec_neg, hRu, neg_neg]
  have hImage : (fun z => A *ᵥ z) '' hyperboloid n = hyperboloid n := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      apply mem_hyperboloid_of_lorentz_pos hx ((hA z z).trans hz.1)
      rw [← hAo, hA]
      exact lorentz_pos_of_mem_hyperboloid ho hz
    · intro z hz
      refine ⟨B *ᵥ z, ⟨?_, ?_⟩, hAB z⟩
      · rw [← hA, hAB]
        exact hz.1
      · have h : lorentz o (B *ᵥ z) = lorentz x z := by rw [← hA, hAo, hAB]
        rw [lorentz_basePoint_left] at h
        rw [h]
        exact lorentz_pos_of_mem_hyperboloid hx hz
  have hDet : A.det = 1 := by
    dsimp only [A]
    rw [Matrix.det_mul, det_reflection u hu₀, det_reflection o ho₀]
    norm_num
  let g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ := ⟨A, hDet⟩
  exact ⟨⟨g, hA, hImage⟩, hAo⟩

/-- **Invariance of the distance**: `d(g x, g y) = d(x, y)`. -/
theorem hyperbolicDist_mulVec (n : ℕ) (g : lorentzGroup n) (x y : Fin (n + 1) → ℝ) :
    hyperbolicDist ((g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ x)
      ((g : Matrix.SpecialLinearGroup (Fin (n + 1)) ℝ).1 *ᵥ y) = hyperbolicDist x y := by
  rw [hyperbolicDist_def, hyperbolicDist_def, lorentz_mulVec]

/-- The surface measure of the unit sphere has total mass `sphereArea n`. -/
theorem sphereMeasure_univ (n : ℕ) (hn : 1 ≤ n) :
    sphereMeasure n univ = ENNReal.ofReal (sphereArea n) := by
  let : NeZero n := ⟨by omega⟩
  have hn' : 0 < (n : ℝ) / 2 := by positivity
  rw [sphereMeasure_def, Measure.toSphere_apply_univ, finrank_euclideanSpace, Fintype.card_fin,
    EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast Real.pi_pos.le,
    sphereArea_def, Real.Gamma_add_one hn'.ne']
  congr 1
  rw [show 1 / 2 * (n : ℝ) = (n : ℝ) / 2 by ring]
  field_simp [hn'.ne', (Real.Gamma_pos_of_pos hn').ne']

namespace RadialCoordinates

/-- Euclidean radial integration against Lebesgue measure in dimension `n`. -/
theorem lintegral_fun_norm (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y : EuclideanSpace ℝ (Fin n), f ‖y‖) =
      ENNReal.ofReal (sphereArea n) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * f r := by
  let : NeZero n := ⟨by omega⟩
  let E := EuclideanSpace ℝ (Fin n)
  let μ : Measure E := volume
  have h := μ.measurePreserving_homeomorphUnitSphereProd
  rw [finrank_euclideanSpace, Fintype.card_fin] at h
  have hh : Measurable (fun p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => f (p.2 : ℝ)) :=
    hf.comp (measurable_subtype_coe.comp measurable_snd)
  calc
    _ = ∫⁻ y : ({(0 : E)}ᶜ : Set E), f ‖(y : E)‖ ∂(μ.comap (↑)) := by
      rw [lintegral_subtype_comap (μ := μ) (measurableSet_singleton (0 : E)).compl
        (fun y : E => f ‖y‖), restrict_compl_singleton]
    _ = ∫⁻ p, f (p.2 : ℝ) ∂μ.toSphere.prod (Measure.volumeIoiPow (n - 1)) := by
      simpa only [homeomorphUnitSphereProd_apply_snd_coe] using h.lintegral_comp hh
    _ = _ := by
      simp only [lintegral_prod _ hh.aemeasurable]
      rw [lintegral_const, mul_comm,
        ← sphereMeasure_def, sphereMeasure_univ n hn, Measure.volumeIoiPow,
        lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
          (show Measurable (fun y : Ioi (0 : ℝ) => f (y : ℝ)) from hf.comp measurable_subtype_coe)]
      congr 1
      exact lintegral_subtype_comap measurableSet_Ioi (fun r => ENNReal.ofReal (r ^ (n - 1)) * f r)

end RadialCoordinates

/-- **Polar coordinates**: for `1 ≤ n` and measurable `F ≥ 0`,
`∫ F(d(o, x)) dm(x) = ω_{n−1} ∫₀^∞ F(t) sinh^{n−1} t dt`. -/
theorem lintegral_hyperbolicMeasure_radial (n : ℕ) (hn : 1 ≤ n) (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ x, F (Real.arcosh (x 0)) ∂hyperbolicMeasure n =
      ENNReal.ofReal (sphereArea n) *
        ∫⁻ t in Ioi 0, F t * ENNReal.ofReal (Real.sinh t ^ (n - 1)) := by
  have hchart := (continuous_hyperboloidChart n).measurable
  let f (r : ℝ) := ENNReal.ofReal ((Real.sqrt (1 + r ^ 2))⁻¹) *
    F (Real.arcosh (Real.sqrt (1 + r ^ 2)))
  have harcosh : Measurable Real.arcosh := by unfold Real.arcosh; fun_prop
  have hf : Measurable f := by
    dsimp only [f]
    exact (by fun_prop : Measurable (fun r : ℝ =>
      ENNReal.ofReal ((Real.sqrt (1 + r ^ 2))⁻¹))).mul
      (hF.comp (harcosh.comp (by fun_prop)))
  have hnrm (y : EuclideanSpace ℝ (Fin n)) :
      ‖y‖ ^ 2 = ∑ i, y i ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.real_norm_sq_eq y
  have hsum (y : Fin n → ℝ) : ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin n))‖ ^ 2 =
      ∑ i, y i ^ 2 := hnrm _
  have hd : Measurable (fun y : Fin n → ℝ =>
      ENNReal.ofReal (Real.sqrt (1 + ∑ i, y i ^ 2))⁻¹) := by fun_prop
  have harg : Measurable (fun x : Fin (n + 1) → ℝ => F (Real.arcosh (x 0))) :=
    hF.comp (harcosh.comp (measurable_pi_apply 0))
  have hchF : Measurable (fun y => F (Real.arcosh (hyperboloidChart n y 0))) :=
    harg.comp hchart
  rw [hyperbolicMeasure_def, lintegral_map harg hchart,
    lintegral_withDensity_eq_lintegral_mul _ hd hchF]
  simp only [Pi.mul_apply, hyperboloidChart_def, Fin.cons_zero, ← hsum]
  have htoLp : (∫⁻ r : Fin n → ℝ, ENNReal.ofReal (Real.sqrt
      (1 + ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖ ^ 2))⁻¹ *
        F (Real.arcosh (Real.sqrt (1 + ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖ ^ 2)))) =
      ∫⁻ r : EuclideanSpace ℝ (Fin n), f ‖r‖ :=
    (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp
      (show Measurable (fun r : EuclideanSpace ℝ (Fin n) => f ‖r‖) from hf.comp measurable_norm)
  rw [htoLp, RadialCoordinates.lintegral_fun_norm n hn f hf]
  congr 1
  have himage : Real.sinh '' Ioi 0 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact Real.sinh_pos_iff.mpr ht
    · intro hx
      exact ⟨Real.arsinh x, Real.arsinh_pos_iff.mpr hx, Real.sinh_arsinh x⟩
  conv_lhs => rw [← himage,
    lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn measurableSet_Ioi
      (fun t _ => (Real.hasDerivAt_sinh t).hasDerivWithinAt)
      (Real.sinh_strictMono.monotone.monotoneOn (Ioi 0))]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hroot : Real.sqrt (1 + Real.sinh t ^ 2) = Real.cosh t := by
    rw [← Real.cosh_sq', Real.sqrt_sq (Real.cosh_pos t).le]
  have hcancel : ENNReal.ofReal (Real.cosh t) * ENNReal.ofReal (Real.cosh t)⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul (Real.cosh_pos t).le, mul_inv_cancel₀ (Real.cosh_pos t).ne',
      ENNReal.ofReal_one]
  simp only [f, hroot, Real.arcosh_cosh ht.le]
  calc
    _ = (ENNReal.ofReal (Real.cosh t) * ENNReal.ofReal (Real.cosh t)⁻¹) *
        (F t * ENNReal.ofReal (Real.sinh t ^ (n - 1))) := by ac_rfl
    _ = _ := by rw [hcancel, one_mul]

/-- The radial pushforward of hyperbolic volume has the hyperbolic polar density. -/
theorem map_hyperbolicMeasure_arcosh (n : ℕ) (hn : 1 ≤ n) :
    (hyperbolicMeasure n).map (fun x => Real.arcosh (x 0)) =
      ENNReal.ofReal (sphereArea n) •
        ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
          (fun t => ENNReal.ofReal (Real.sinh t ^ (n - 1))) := by
  have harcosh : Measurable Real.arcosh := by unfold Real.arcosh; fun_prop
  have hmap : Measurable (fun x : Fin (n + 1) → ℝ => Real.arcosh (x 0)) :=
    harcosh.comp (measurable_pi_apply 0)
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal (Real.sinh t ^ (n - 1))) := by fun_prop
  apply Measure.ext_of_lintegral _
  intro F hF
  rw [lintegral_map hF hmap, lintegral_hyperbolicMeasure_radial n hn F hF,
    lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hw hF]
  simp only [smul_eq_mul, Pi.mul_apply, mul_comm (F _)]

/-- Bochner integration of radial functions on real hyperbolic space. -/
theorem integral_hyperbolicMeasure_radial (n : ℕ) (hn : 1 ≤ n) (F : ℝ → ℂ)
    (hF : Measurable F) :
    (∫ x, F (Real.arcosh (x 0)) ∂hyperbolicMeasure n) =
      (sphereArea n : ℂ) * ∫ t in Ioi 0, F t * (Real.sinh t ^ (n - 1) : ℝ) := by
  have harcosh : Measurable Real.arcosh := by unfold Real.arcosh; fun_prop
  have hmap : Measurable (fun x : Fin (n + 1) → ℝ => Real.arcosh (x 0)) :=
    harcosh.comp (measurable_pi_apply 0)
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal (Real.sinh t ^ (n - 1))) := by fun_prop
  have hA : 0 ≤ sphereArea n := by
    rw [sphereArea_def]
    have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    positivity
  rw [← integral_map hmap.aemeasurable hF.aestronglyMeasurable, map_hyperbolicMeasure_arcosh n hn,
    integral_smul_measure, ENNReal.toReal_ofReal hA, Complex.real_smul,
    integral_withDensity_eq_integral_toReal_smul hw (Filter.Eventually.of_forall fun _ =>
      ENNReal.ofReal_lt_top)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.toReal_ofReal ((pow_nonneg (Real.sinh_nonneg_iff.mpr ht.le) _ :
    0 ≤ Real.sinh t ^ (n - 1))), Complex.real_smul, mul_comm]

namespace HyperbolicLaplacian

private theorem lorentz_single_zero {n : ℕ} (x : Fin (n + 1) → ℝ) :
    lorentz (Pi.single 0 1) x = x 0 :=
  lorentz_basePoint_left x

private theorem lorentz_single_succ {n : ℕ} (i : Fin n) (x : Fin (n + 1) → ℝ) :
    lorentz (Pi.single i.succ 1) x = -x i.succ := by
  simp only [lorentz_def, Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm, zero_mul, zero_sub]
  congr 1
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp
  · intro j hj hji
    rw [Pi.single_eq_of_ne (fun h => hji (Fin.succ_inj.mp h)), zero_mul]

set_option maxHeartbeats 800000 in
private theorem derivatives_normalizedProjection (u v a d : ℝ) :
    let z (s : ℝ) := (u + v * s) * (Real.sqrt (1 + 2 * a * s + d * s ^ 2))⁻¹
    z 0 = u ∧ ContDiffAt ℝ 2 z 0 ∧ deriv z 0 = v - u * a ∧
      iteratedDeriv 2 z 0 = u * (3 * a ^ 2 - d) - 2 * a * v := by
  let p (s : ℝ) := 1 + 2 * a * s + d * s ^ 2
  let l (s : ℝ) := u + v * s
  let z (s : ℝ) := l s * (Real.sqrt (p s))⁻¹
  let r (s : ℝ) := p s ^ (-(1 : ℝ) / 2)
  have hp0 : p 0 = 1 := by simp [p]
  have hpc : ContDiff ℝ 2 p := by dsimp only [p]; fun_prop
  have hlc : ContDiff ℝ 2 l := by dsimp only [l]; fun_prop
  have hpPos : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < p s := by
    refine hpc.continuous.continuousAt.eventually (Ioi_mem_nhds ?_)
    rw [hp0]
    norm_num
  have hzer : z =ᶠ[𝓝 (0 : ℝ)] (fun s => l s * r s) := by
    filter_upwards [hpPos] with s hs
    dsimp only [z, r]
    rw [Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hs.le]
  have hzc : ContDiffAt ℝ 2 z 0 := by
    apply ContDiffAt.congr_of_eventuallyEq _ hzer
    exact hlc.contDiffAt.mul (hpc.contDiffAt.rpow_const_of_ne (by simp [hp0]))
  have hl (s : ℝ) : HasDerivAt l v s := by
    have h := ((hasDerivAt_id s).const_mul v).const_add u
    simpa only [l, id_eq, mul_one] using h
  have hp (s : ℝ) : HasDerivAt p (2 * a + 2 * d * s) s := by
    have h := ((((hasDerivAt_id s).const_mul (2 * a)).const_add 1).add
      (((hasDerivAt_id s).pow 2).const_mul d))
    refine h.congr_deriv ?_
    simp only [id_eq, mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have hr (s : ℝ) (hs : 0 < p s) : HasDerivAt r
      ((-(1 : ℝ) / 2) * p s ^ (-(3 : ℝ) / 2) * (2 * a + 2 * d * s)) s := by
    have h := (hp s).rpow_const (p := (-(1 : ℝ) / 2)) (Or.inl hs.ne')
    refine h.congr_deriv ?_
    rw [show -(1 : ℝ) / 2 - 1 = -(3 : ℝ) / 2 by ring]
    ring
  let r' (s : ℝ) := (-(1 : ℝ) / 2) * p s ^ (-(3 : ℝ) / 2) * (2 * a + 2 * d * s)
  have hr' : HasDerivAt r' (3 * a ^ 2 - d) 0 := by
    have h := (((hp 0).rpow_const (p := (-(3 : ℝ) / 2))
      (Or.inl (by simp [hp0]))).const_mul (-(1 : ℝ) / 2)).mul
      (((hasDerivAt_id (0 : ℝ)).const_mul (2 * d)).const_add (2 * a))
    refine h.congr_deriv ?_
    simp only [hp0, Real.one_rpow, id_eq, mul_zero, add_zero, mul_one]
    ring
  have hrZero : r 0 = 1 := by simp [r, hp0]
  have hr'Zero : r' 0 = -a := by simp [r', hp0]; ring
  have hlZero : l 0 = u := by simp [l]
  have hp0pos : 0 < p 0 := by simp [hp0]
  have heq : deriv z =ᶠ[𝓝 (0 : ℝ)] fun s => v * r s + l s * r' s := by
    filter_upwards [hzer.eventuallyEq_nhds, hpPos] with s hs hpos
    rw [hs.deriv_eq]
    exact ((hl s).mul (hr s hpos)).deriv
  change z 0 = u ∧ ContDiffAt ℝ 2 z 0 ∧ deriv z 0 = _ ∧ iteratedDeriv 2 z 0 = _
  refine ⟨by simp [z, hp0, hlZero], hzc, ?_, ?_⟩
  · rw [heq.eq_of_nhds, hrZero, hr'Zero, hlZero]
    ring
  · rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
    have h := ((hr 0 hp0pos).const_mul v).add ((hl 0).mul hr')
    have h' : HasDerivAt (fun s => v * r s + l s * r' s)
        (v * r' 0 + (v * r' 0 + l 0 * (3 * a ^ 2 - d))) 0 := h
    rw [h'.deriv, hr'Zero, hlZero]
    ring

end HyperbolicLaplacian

set_option maxHeartbeats 1400000 in
/-- The Laplacian of `F([·, b])` on the hyperboloid, in terms of the first two derivatives of
`F` and the Lorentz norms of the projection and its axis. -/
theorem hyperbolicLaplacian_comp_lorentz (n : ℕ) (F : ℝ → ℂ)
    (b x : Fin (n + 1) → ℝ) (hx : x ∈ hyperboloid n)
    (hF : ContDiffAt ℝ 2 F (lorentz x b)) :
    hyperbolicLaplacian n (fun y => F (lorentz y b)) x =
      (lorentz x b ^ 2 - lorentz b b) • iteratedDeriv 2 F (lorentz x b) +
        ((n : ℝ) * lorentz x b) • deriv F (lorentz x b) := by
  let m := lorentz x b
  let hessian := iteratedDeriv 2 F m
  let grad := deriv F m
  have hline (e : Fin (n + 1) → ℝ) :
      iteratedDeriv 2 (fun s : ℝ => F (lorentz
        ((Real.sqrt (lorentz (x + s • e) (x + s • e)))⁻¹ • (x + s • e)) b)) 0 =
        (lorentz e b - m * lorentz e x) ^ 2 • hessian +
          (m * (3 * lorentz e x ^ 2 - lorentz e e) - 2 * lorentz e x * lorentz e b) • grad := by
    let z (s : ℝ) := (m + lorentz e b * s) *
      (Real.sqrt (1 + 2 * lorentz e x * s + lorentz e e * s ^ 2))⁻¹
    have hz (s : ℝ) :
        lorentz ((Real.sqrt (lorentz (x + s • e) (x + s • e)))⁻¹ • (x + s • e)) b =
          z s := by
      have hsq : lorentz (x + s • e) (x + s • e) =
          1 + 2 * lorentz e x * s + lorentz e e * s ^ 2 := by
        rw [LorentzGeometry.lorentz_add_left, lorentz_comm x (x + s • e),
          LorentzGeometry.lorentz_add_left, LorentzGeometry.lorentz_smul_left,
          LorentzGeometry.lorentz_smul_left, lorentz_comm e (x + s • e),
          LorentzGeometry.lorentz_add_left, LorentzGeometry.lorentz_smul_left,
          lorentz_comm x e, hx.1]
        ring
      rw [hsq, LorentzGeometry.lorentz_smul_left, LorentzGeometry.lorentz_add_left,
        LorentzGeometry.lorentz_smul_left]
      simp only [z, m, mul_comm]
    obtain ⟨hz0, hzc, hz₁, hz₂⟩ :=
      HyperbolicLaplacian.derivatives_normalizedProjection m (lorentz e b)
        (lorentz e x) (lorentz e e)
    rw [show (fun s : ℝ => F (lorentz
      ((Real.sqrt (lorentz (x + s • e) (x + s • e)))⁻¹ • (x + s • e)) b)) = F ∘ z from
      funext fun s => congrArg F (hz s)]
    change z 0 = m at hz0
    change ContDiffAt ℝ 2 z 0 at hzc
    change deriv z 0 = _ at hz₁
    change iteratedDeriv 2 z 0 = _ at hz₂
    have hF' : ContDiffAt ℝ 2 F (z 0) := by rwa [hz0]
    rw [iteratedDeriv_scomp_two hF' hzc, hz0, hz₁, hz₂]
  -- Sum the second-order chain rule with the Lorentz signs.
  have hsq : ∑ i : Fin n, (-b i.succ + m * x i.succ) ^ 2 -
      (b 0 - m * x 0) ^ 2 = m ^ 2 - lorentz b b := by
    have hf (X B : ℝ) : (-B + m * X) ^ 2 = B ^ 2 - (2 * m) * (X * B) + m ^ 2 * X ^ 2 := by
      ring
    have h₁ := hx.1
    have h₂ : lorentz x b = m := rfl
    rw [lorentz_def] at h₁ h₂ ⊢
    simp only [hf, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, pow_two]
    linear_combination -m ^ 2 * h₁ + 2 * m * h₂
  have hlin : ∑ i : Fin n, (m * (3 * x i.succ ^ 2 + 1) - 2 * x i.succ * b i.succ) -
      (m * (3 * x 0 ^ 2 - 1) - 2 * x 0 * b 0) = (n : ℝ) * m := by
    have h₁ := hx.1
    have h₂ : lorentz x b = m := rfl
    rw [lorentz_def] at h₁ h₂
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, pow_two,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linear_combination (norm := ring_nf) -(m * 3) * h₁ + 2 * h₂
    rw [Finset.sum_mul, neg_add_cancel]
  have hsp (i : Fin n) := hline (Pi.single i.succ 1)
  simp only [HyperbolicLaplacian.lorentz_single_succ, Pi.single_eq_same] at hsp
  have hspFirst (i : Fin n) : -b i.succ - m * -x i.succ = -b i.succ + m * x i.succ := by ring
  have hspSecond (i : Fin n) : m * (3 * (-x i.succ) ^ 2 - -1) - 2 * -x i.succ * -b i.succ =
      m * (3 * x i.succ ^ 2 + 1) - 2 * x i.succ * b i.succ := by ring
  simp only [hspFirst, hspSecond] at hsp
  have htime := hline (Pi.single 0 1)
  simp only [HyperbolicLaplacian.lorentz_single_zero, Pi.single_eq_same] at htime
  rw [hyperbolicLaplacian_def]
  simp only [hsp, htime, Finset.sum_add_distrib, ← Finset.sum_smul]
  calc
    _ = (∑ i : Fin n, (-b i.succ + m * x i.succ) ^ 2 - (b 0 - m * x 0) ^ 2) • hessian +
        (∑ i : Fin n, (m * (3 * x i.succ ^ 2 + 1) - 2 * x i.succ * b i.succ) -
          (m * (3 * x 0 ^ 2 - 1) - 2 * x 0 * b 0)) • grad := by
      simp only [sub_smul]
      abel
    _ = _ := by rw [hsq, hlin]

/-- The time coordinate of a point on the upper hyperboloid is at least one. -/
theorem one_le_apply_zero_of_mem_hyperboloid (n : ℕ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ hyperboloid n) : 1 ≤ x 0 := by
  have hform := hx.1
  rw [lorentz_def] at hform
  have hnonneg := Finset.sum_nonneg
    (s := Finset.univ) (f := fun i : Fin n => x i.succ * x i.succ) (fun _ _ => mul_self_nonneg _)
  nlinarith [hx.2]

/-- At a point of the hyperboloid, the Laplacian depends only on the restriction of the function
to the hyperboloid. -/
theorem hyperbolicLaplacian_congr {n : ℕ} {f g : (Fin (n + 1) → ℝ) → ℂ}
    (hfg : EqOn f g (hyperboloid n)) {x : Fin (n + 1) → ℝ} (hx : x ∈ hyperboloid n) :
    hyperbolicLaplacian n f x = hyperbolicLaplacian n g x := by
  have heq (v : Fin (n + 1) → ℝ) :
      let z (s : ℝ) := (Real.sqrt (lorentz (x + s • v) (x + s • v)))⁻¹ • (x + s • v)
      iteratedDeriv 2 (fun s : ℝ => f (z s)) 0 = iteratedDeriv 2 (fun s : ℝ => g (z s)) 0 := by
    let y (s : ℝ) := x + s • v
    let q (s : ℝ) := lorentz (y s) (y s)
    let z (s : ℝ) := (Real.sqrt (q s))⁻¹ • y s
    have hqCont : Continuous q := by
      dsimp only [q, y, lorentz_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    have htimeCont : Continuous (fun s => y s 0) := by
      dsimp only [y, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      fun_prop
    have hq0 : 0 < q 0 := by simp [q, y, hx.1]
    have htime : 0 < y 0 0 := by simpa [y] using hx.2
    change iteratedDeriv 2 (fun s : ℝ => f (z s)) 0 = iteratedDeriv 2 (fun s : ℝ => g (z s)) 0
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [hqCont.continuousAt.eventually (Ioi_mem_nhds hq0),
      htimeCont.continuousAt.eventually (Ioi_mem_nhds htime)] with s hqs hts
    apply hfg
    have hqs' : 0 < q s := hqs
    have hsqrt := Real.sqrt_pos.2 hqs'
    constructor
    · calc
        lorentz (z s) (z s) = (Real.sqrt (q s))⁻¹ ^ 2 * q s := by
          dsimp only [z]
          rw [LorentzGeometry.lorentz_smul_left,
            lorentz_comm (y s) ((Real.sqrt (q s))⁻¹ • y s),
            LorentzGeometry.lorentz_smul_left]
          change (Real.sqrt (q s))⁻¹ * ((Real.sqrt (q s))⁻¹ * q s) = _
          ring
        _ = ((Real.sqrt (q s))⁻¹ * Real.sqrt (q s)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hqs'.le]
        _ = 1 := by rw [inv_mul_cancel₀ hsqrt.ne', one_pow]
    · change 0 < z s 0
      simpa only [z, Pi.smul_apply, smul_eq_mul] using mul_pos (inv_pos.mpr hsqrt) hts
  rw [hyperbolicLaplacian_def, hyperbolicLaplacian_def, heq (Pi.single 0 1)]
  exact congrArg (· - _) (Finset.sum_congr rfl fun i _ => heq (Pi.single i.succ 1))

set_option maxHeartbeats 900000 in
/-- **Radial part of the Laplacian**: for `x ∈ ℍⁿ \ {o}` and `t = arcosh x₀`,
`Δ(F ∘ d(o, ·))(x) = F''(t) + (n − 1) coth t F'(t)`. -/
theorem hyperbolicLaplacian_radial (n : ℕ) (F : ℝ → ℂ) (hF : ContDiffOn ℝ 2 F (Ioi 0))
    {x : Fin (n + 1) → ℝ} (hx : x ∈ hyperboloid n) (hxo : x ≠ basePoint n) :
    hyperbolicLaplacian n (fun y => F (Real.arcosh (y 0))) x =
      deriv (deriv F) (Real.arcosh (x 0)) +
        ((n - 1) * (Real.cosh (Real.arcosh (x 0)) / Real.sinh (Real.arcosh (x 0))) : ℝ) *
          deriv F (Real.arcosh (x 0)) := by
  let a := x 0
  let t := Real.arcosh a
  have hxEq : a ^ 2 = 1 + ∑ i : Fin n, x i.succ ^ 2 := by
    have h := hx.1
    rw [lorentz_def] at h
    simp only [a, pow_two]
    linarith
  have ha : 1 < a := by
    apply lt_of_le_of_ne (show 1 ≤ a from one_le_apply_zero_of_mem_hyperboloid n hx)
    intro h
    have hz : ∑ i : Fin n, x i.succ ^ 2 = 0 := by rw [← h] at hxEq; nlinarith
    have hzero (i : Fin n) : x i.succ = 0 :=
      eq_zero_of_pow_eq_zero ((Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ => sq_nonneg _)).mp hz i (Finset.mem_univ i))
    apply hxo
    ext j
    cases j using Fin.cases with
    | zero => simpa [basePoint_def] using h.symm
    | succ i => simpa [basePoint_def, Fin.succ_ne_zero i] using hzero i
  have ht : 0 < t := Real.arcosh_pos ha
  have hFlat : ContDiffAt ℝ 2 F t := hF.contDiffAt (Ioi_mem_nhds ht)
  have hArc : ContDiffAt ℝ 2 Real.arcosh a := Real.contDiffAt_arcosh ha
  have hq : 0 < a ^ 2 - 1 := by nlinarith
  let p := Real.sqrt (a ^ 2 - 1)
  have hp : p ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hpSq : p ^ 2 = a ^ 2 - 1 := Real.sq_sqrt hq.le
  have hArcFirst : HasDerivAt Real.arcosh p⁻¹ a := Real.hasDerivAt_arcosh ha
  have hArcSecond : iteratedDeriv 2 Real.arcosh a = -a / p ^ 3 := by
    have heq : deriv Real.arcosh =ᶠ[𝓝 a] fun s : ℝ => (Real.sqrt (s ^ 2 - 1))⁻¹ := by
      filter_upwards [Ioi_mem_nhds ha] with s hs
      exact (Real.hasDerivAt_arcosh hs).deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq]
    have hpoly := ((hasDerivAt_id a).pow 2).sub_const 1
    have hsqrt := ((Real.hasDerivAt_sqrt hq.ne').comp a hpoly).inv hp
    refine hsqrt.deriv.trans ?_
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, Function.comp_apply,
      Pi.pow_apply, mul_one]
    change -((1 / (2 * p)) * (2 * a)) / p ^ 2 = _
    field_simp
  have hfirst : deriv (F ∘ Real.arcosh) a = p⁻¹ • deriv F t := by
    exact ((hFlat.differentiableAt (by norm_num)).hasDerivAt.scomp a hArcFirst).deriv
  have hsecond : iteratedDeriv 2 (F ∘ Real.arcosh) a =
      p⁻¹ ^ 2 • deriv (deriv F) t + (-a / p ^ 3) • deriv F t := by
    rw [iteratedDeriv_scomp_two hFlat hArc, hArcFirst.deriv, hArcSecond,
      iteratedDeriv_succ, iteratedDeriv_one]
  have hL (y : Fin (n + 1) → ℝ) : lorentz y (basePoint n) = y 0 := by
    rw [lorentz_comm, lorentz_basePoint_left]
  have hB : lorentz (basePoint n) (basePoint n) = 1 := (basePoint_mem_hyperboloid n).1
  have hFlat' : ContDiffAt ℝ 2 (F ∘ Real.arcosh) (lorentz x (basePoint n)) := by
    rw [hL]
    exact hFlat.comp a hArc
  have hh := hyperbolicLaplacian_comp_lorentz n (F ∘ Real.arcosh) (basePoint n) x hx hFlat'
  rw [hB] at hh
  simp only [hL, Function.comp_apply] at hh
  change _ = (a ^ 2 - 1) • iteratedDeriv 2 (F ∘ Real.arcosh) a +
    ((n : ℝ) * a) • deriv (F ∘ Real.arcosh) a at hh
  have hcoef₁ : (a ^ 2 - 1) * (p⁻¹ ^ 2) = 1 := by
    rw [← hpSq, ← mul_pow, mul_inv_cancel₀ hp, one_pow]
  have hcoef₂ : (a ^ 2 - 1) * (-a / p ^ 3) + ((n : ℝ) * a) * p⁻¹ =
      ((n : ℝ) - 1) * (a / p) := by
    rw [← hpSq]
    field_simp
    ring
  rw [hh, hfirst, hsecond, smul_add, ← mul_smul, ← mul_smul, ← mul_smul, add_assoc, ← add_smul,
    hcoef₁, hcoef₂, one_smul]
  have hEq : Real.cosh t = a := Real.cosh_arcosh ha.le
  have hSq : Real.sinh t = p := Real.sinh_arcosh ha.le
  change _ = deriv (deriv F) t +
    (((n : ℝ) - 1) * (Real.cosh t / Real.sinh t) : ℝ) * deriv F t
  rw [hEq, hSq, Complex.real_smul]

namespace HyperbolicLaplacian

private theorem lorentz_boundaryVector_pos (n : ℕ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ hyperboloid n) (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    0 < lorentz x (boundaryVector n b) := by
  let y := boundaryVector n b
  have hy : y 0 = 1 := by simp [y, boundaryVector_def]
  have hnorm : ∑ i : Fin n, y i.succ ^ 2 = 1 := by
    have h := lorentz_boundaryVector_self n b
    change lorentz y y = 0 at h
    rw [lorentz_def, hy, one_mul] at h
    simpa only [pow_two] using sub_eq_zero.mp h |>.symm
  have hC := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i : Fin n => x i.succ)
    (fun i : Fin n => y i.succ)
  simp only [hnorm, Real.sqrt_one, mul_one] at hC
  have hxpos := hx.2
  have hxform := hx.1
  rw [lorentz_def] at hxform
  have hrad : Real.sqrt (∑ i : Fin n, x i.succ ^ 2) < x 0 := by
    refine (Real.sqrt_lt' hxpos).2 ?_
    simp only [pow_two]
    linarith
  change 0 < lorentz x y
  rw [lorentz_def, hy, mul_one, sub_pos]
  exact hC.trans_lt hrad

private theorem hasDerivAt_ofReal_cpow (σ : ℂ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ σ) (σ * (s : ℂ) ^ (σ - 1)) s := by
  have h := ((hasDerivAt_id (s : ℂ)).cpow_const (c := σ)
    (ofReal_mem_slitPlane.mpr hs)).comp_ofReal
  simpa only [id_eq, one_mul, mul_one] using h

end HyperbolicLaplacian

set_option maxHeartbeats 800000 in
/-- **Plane waves** (Wawrzyńczyk Theorem 11.5.1, (11.5.6), p. 412):
`Δ [x, b̃]^{−μ} = μ(μ − n + 1) [x, b̃]^{−μ}` on `ℍⁿ`. -/
theorem hyperbolicLaplacian_planeWave (n : ℕ) (μ : ℂ)
    (b : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ hyperboloid n) :
    hyperbolicLaplacian n (fun y => (lorentz y (boundaryVector n b) : ℂ) ^ (-μ)) x =
      μ * (μ - n + 1) * (lorentz x (boundaryVector n b) : ℂ) ^ (-μ) := by
  let v := boundaryVector n b
  let a := lorentz x v
  let σ := -μ
  let u (s : ℝ) := (s : ℂ) ^ σ
  have ha : 0 < a := HyperbolicLaplacian.lorentz_boundaryVector_pos n hx b
  have hu : ContDiffAt ℝ 2 u a := by
    have heq : u =ᶠ[𝓝 a] fun s : ℝ => Complex.exp ((Real.log s : ℂ) * σ) := by
      filter_upwards [Ioi_mem_nhds ha] with s hs
      dsimp only [u]
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hs.ne'), ofReal_log hs.le]
    apply ContDiffAt.congr_of_eventuallyEq _ heq
    have hlog : ContDiffAt ℝ 2 Real.log a := Real.contDiffAt_log.mpr ha.ne'
    exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp a hlog).mul contDiffAt_const).cexp
  have hu₁ : deriv u a = σ * (a : ℂ) ^ (σ - 1) :=
    (HyperbolicLaplacian.hasDerivAt_ofReal_cpow σ ha).deriv
  have hu₂ : iteratedDeriv 2 u a = σ * (σ - 1) * (a : ℂ) ^ (σ - 2) := by
    have heq : deriv u =ᶠ[𝓝 a] fun s : ℝ => σ * (s : ℂ) ^ (σ - 1) := by
      filter_upwards [Ioi_mem_nhds ha] with s hs
      exact (HyperbolicLaplacian.hasDerivAt_ofReal_cpow σ hs).deriv
    rw [iteratedDeriv_succ, iteratedDeriv_one, heq.deriv_eq,
      ((HyperbolicLaplacian.hasDerivAt_ofReal_cpow (σ - 1) ha).const_mul σ).deriv,
      show σ - 1 - 1 = σ - 2 by ring]
    ring
  have hV : lorentz v v = 0 := lorentz_boundaryVector_self n b
  have h := hyperbolicLaplacian_comp_lorentz n u v x hx hu
  change _ = (a ^ 2 - lorentz v v) • iteratedDeriv 2 u a + ((n : ℝ) * a) • deriv u a at h
  rw [hV, sub_zero] at h
  change hyperbolicLaplacian n (fun y => u (lorentz y v)) x = _ * u a
  rw [h, hu₁, hu₂]
  simp only [Complex.real_smul, ofReal_mul, ofReal_pow, ofReal_natCast]
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hm (k : ℕ) : (a : ℂ) ^ k * (a : ℂ) ^ (σ - k) = u a := by
    rw [← cpow_natCast, ← cpow_add _ _ ha']
    congr 1
    ring
  calc
    _ = σ * (σ - 1) * ((a : ℂ) ^ 2 * (a : ℂ) ^ (σ - (2 : ℕ))) +
        (n : ℂ) * σ * ((a : ℂ) ^ 1 * (a : ℂ) ^ (σ - (1 : ℕ))) := by
      simp only [Nat.cast_ofNat, Nat.cast_one, pow_one]
      ring
    _ = _ := by rw [hm 2, hm 1]; dsimp only [σ]; ring

/-- **Poisson integrals are harmonic**: `Δ ∫ [x, b̃]^{1−n} F(b) dσ(b) = 0` on `ℍⁿ`. -/
theorem hyperbolicLaplacian_poisson (n : ℕ) (hn : 2 ≤ n)
    (F : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℂ) (hF : Continuous F)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ hyperboloid n) :
    hyperbolicLaplacian n
        (fun y => ⨍ b, (lorentz y (boundaryVector n b) : ℂ) ^ (1 - (n : ℂ)) * F b ∂sphereMeasure n)
        x = 0 := by
  sorry

section Gelfand

attribute [local instance] borel

/-- **`(SO₀(n, 1), SO(n))` is a Gel'fand pair**, by the involution `g ↦ J (gᵀ)⁻¹ J`. -/
theorem isGelfandPair_lorentzGroup (n : ℕ) (μ : Measure (lorentzGroup n)) [μ.IsHaarMeasure] :
    Subgroup.IsGelfandPair (rotationSubgroup n) μ := by
  sorry

end Gelfand

end SFVK.RankOne
