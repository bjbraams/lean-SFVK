/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.Spheres.SphereMeasure
public import SFVK.Spheres.Zonal
import DLMF.OrthogonalPolynomials.BoundsZeros.PointwiseAndZeroBounds
import DLMF.OrthogonalPolynomials.Integrals.AngularRepresentations
import DLMF.OrthogonalPolynomials.Integrals.ConvolutionsAndFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# Addition theorem, Funk–Hecke formula and zonal spherical functions of `SO(n)`

The addition theorem `∑ᵢ Yᵢ(x) Yᵢ(y) = dim H_l · ω_{n,l}(⟪x, y⟫)` for an orthonormal basis of the
spherical harmonics of degree `l` in `L²` of the normalized sphere measure; the reproducing
property; the bound `|ω_{n,l}| ≤ 1`; the orthogonality of the zonal polynomials; the Funk–Hecke
formula; the zonal spherical functions of `(SO(n), K_η)` with their classification; and the
product formula. The scalar formulas use lean-DLMF's Gegenbauer bound, orthogonality and
product integral, and Mathlib's Chebyshev orthogonality.

The Gegenbauer addition theorem (Vilenkin–Klimyk, Vol. 2, §9.4.3 (5), p. 71) is lean-DLMF's
`DLMF.SphericalHarmonics.ultrasphericalPolynomial_addition` and is not restated here.

Sources: Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2, §10.2.1
(2)–(6), pp. 174–175 (the convolution and addition theorems with the normalized measure and the
Funk–Hecke formula), §9.3.8 (1)–(3), pp. 62–63 (orthogonality), §9.4.5 (1), p. 76 (product
formula); Wawrzyńczyk, *Group Representations and Special Functions*, (9.4.9)–(9.4.10) and
Theorem 9.4.1, p. 335, and (9.5.1)–(9.5.2), p. 337; Dieudonné, *Special Functions and Linear
Representations of Lie Groups*, §7, (101), p. 23.
-/

public noncomputable section

open MeasureTheory Polynomial Real Set
open DLMF.Hypergeometric DLMF.OrthogonalPolynomials
open scoped InnerProductSpace

namespace SFVK.Spheres

/-- **Addition theorem** (Vilenkin–Klimyk, Vol. 2, §10.2.1 (3), pp. 174–175). For `n ≥ 2` and an
`L²(sphereMeasure n)`-orthonormal basis `Y` of `H_l`,
`∑ᵢ Yᵢ(x) Yᵢ(y) = dim H_l · ω_{n,l}(⟪x, y⟫)` on the sphere. -/
theorem sum_sphereEval_mul_sphereEval_eq {n : ℕ} (hn : 2 ≤ n) (l : ℕ)
    (Y : Fin (Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l)) →
      MvPolynomial.harmonicSubmodule (Fin n) ℝ l)
    (hY : ∀ i j, ∫ x : Sphere n, MvPolynomial.sphereEval (Y i : MvPolynomial (Fin n) ℝ) x *
      MvPolynomial.sphereEval (Y j : MvPolynomial (Fin n) ℝ) x ∂sphereMeasure n =
        if i = j then 1 else 0)
    (x y : Sphere n) :
    ∑ i, MvPolynomial.sphereEval (Y i : MvPolynomial (Fin n) ℝ) x *
        MvPolynomial.sphereEval (Y i : MvPolynomial (Fin n) ℝ) y =
      Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l) *
        (zonalPolynomial n l).eval ⟪(x : EuclideanSpace ℝ (Fin n)), y⟫_ℝ := by
  sorry

/-- **Reproducing property** (Vilenkin–Klimyk, Vol. 2, §10.2.1 (2), p. 174). For `n ≥ 2`,
`p ∈ H_l` and `y` on the sphere, `∫ p(x) ω_{n,l}(⟪x, y⟫) dσ(x) = p(y)/dim H_l`. -/
theorem integral_sphereEval_mul_zonalPolynomial {n : ℕ} (hn : 2 ≤ n) {l : ℕ}
    {p : MvPolynomial (Fin n) ℝ} (hp : p ∈ MvPolynomial.harmonicSubmodule (Fin n) ℝ l)
    (y : Sphere n) :
    ∫ x : Sphere n, MvPolynomial.sphereEval p x *
        (zonalPolynomial n l).eval ⟪(x : EuclideanSpace ℝ (Fin n)), y⟫_ℝ ∂sphereMeasure n =
      MvPolynomial.sphereEval p y /
        Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l) := by
  sorry

namespace ZonalBounds

private theorem zonalPolynomial_bound_of_three_le {n : ℕ} (hn : 3 ≤ n) (l : ℕ) {t : ℝ}
    (ht : |t| ≤ 1) : |(zonalPolynomial n l).eval t| ≤ 1 := by
  let lam := ((n : ℝ) - 2) / 2
  have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlam : 0 < lam := by dsimp [lam]; linarith
  have hcast : (lam : ℂ) = ((n : ℂ) - 2) / 2 := by dsimp [lam]; push_cast; rfl
  have hBound := ultrasphericalPolynomial_bound_at_one hlam ht l
  have hOne : ultrasphericalPolynomial lam l 1 ≠ 0 := by
    rw [ultrasphericalPolynomial_at_one]
    exact div_ne_zero (pochhammer_ne_zero_of_re_pos (by simp; linarith) l)
      (Nat.cast_ne_zero.mpr l.factorial_ne_zero)
  have hNorm : ‖ultrasphericalPolynomial lam l t‖ ≤ ‖ultrasphericalPolynomial lam l 1‖ := by
    refine hBound.trans ?_
    rw [← Complex.div_natCast_re, ← ultrasphericalPolynomial_at_one]
    exact Complex.re_le_norm _
  have he := zonalPolynomial_eq_ultrasphericalPolynomial_div hn l t
  rw [← hcast] at he
  have h := congrArg norm he
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_div] at h
  exact h.trans_le ((div_le_one (norm_pos_iff.mpr hOne)).mpr hNorm)

end ZonalBounds

open ZonalBounds in
/-- **Bound.** `|ω_{n,l}(t)| ≤ 1` on `[-1, 1]` for `n ≥ 2`. -/
theorem abs_zonalPolynomial_eval_le_one {n : ℕ} (hn : 2 ≤ n) (l : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    |(zonalPolynomial n l).eval t| ≤ 1 := by
  by_cases he : n = 2
  · subst n
    rw [zonalPolynomial_two, ← cos_arccos (abs_le.mp ht).1 (abs_le.mp ht).2,
      Chebyshev.T_real_cos]
    exact abs_cos_le_one _
  · exact zonalPolynomial_bound_of_three_le (by omega) l ht

namespace ZonalOrthogonality

private theorem finrank_harmonicSubmodule_two (l : ℕ) :
    Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin 2) ℝ l) = if l = 0 then 1 else 2 := by
  rcases l with _ | _ | l
  · rw [MvPolynomial.finrank_harmonicSubmodule_of_le_one (by decide : 0 ≤ 1)]
    simp
  · rw [MvPolynomial.finrank_harmonicSubmodule_of_le_one (by decide : 1 ≤ 1)]
    simp
  · change Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin 2) ℝ (l + 2)) = 2
    rw [MvPolynomial.finrank_harmonicSubmodule_add_two]
    simp

private theorem orthogonality_two (l l' : ℕ) :
    polarConstant 2 * ∫ t in Ioo (-1 : ℝ) 1,
        (zonalPolynomial 2 l).eval t * (zonalPolynomial 2 l').eval t *
          (1 - t ^ 2) ^ ((((2 : ℕ) : ℝ) - 3) / 2) =
      if l = l' then 1 / (Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin 2) ℝ l) : ℝ)
      else 0 := by
  have hconst : polarConstant 2 = 1 / π := by
    rw [polarConstant_def]
    norm_num [Real.Gamma_one_half_eq, Real.mul_self_sqrt Real.pi_pos.le]
  have hT : (∫ t in Ioo (-1 : ℝ) 1,
      (zonalPolynomial 2 l).eval t * (zonalPolynomial 2 l').eval t *
        (1 - t ^ 2) ^ ((((2 : ℕ) : ℝ) - 3) / 2)) =
      ∫ t, (Chebyshev.T ℝ l).eval t * (Chebyshev.T ℝ l').eval t ∂Chebyshev.measureT := by
    rw [Chebyshev.integral_measureT, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [zonalPolynomial_two, zonalPolynomial_two]
    have hx : 0 ≤ t + 1 := by linarith [ht.1]
    have hy : 0 ≤ 1 - t := by linarith [ht.2]
    have hty : 0 ≤ 1 - t ^ 2 := by nlinarith [mul_nonneg hx hy]
    rw [show ((((2 : ℕ) : ℝ) - 3) / 2) = -(1 / 2) by norm_num, Real.rpow_neg hty,
      ← Real.sqrt_eq_rpow, Real.sqrt_inv]
  rw [hconst, hT, finrank_harmonicSubmodule_two]
  by_cases hll : l = l'
  · rw [ite_eq_left hll]
    subst l'
    by_cases h : l = 0
    · subst l
      rw [Nat.cast_zero, ite_eq_left rfl, Chebyshev.integral_eval_T_real_mul_self_measureT_zero]
      norm_cast
      rw [div_one, div_mul_cancel₀ _ Real.pi_ne_zero]
    · rw [Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero h, ite_eq_right h]
      push_cast
      field_simp [Real.pi_ne_zero]
  · rw [ite_eq_right hll, Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne hll,
      mul_zero]

private theorem sphere_polarWeight_mass {n : ℕ} (hn : 2 ≤ n) :
    polarConstant n * ∫ t in Ioo (-1 : ℝ) 1, (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2) = 1 := by
  let j : Fin n := ⟨0, by omega⟩
  let η : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
  have hη : ‖η‖ = 1 := by simp [η]
  have : Nonempty (Fin n) := ⟨j⟩
  have : IsProbabilityMeasure (sphereMeasure n) := by
    refine ⟨?_⟩
    rw [sphereMeasure_def, smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel
      (Measure.measure_univ_ne_zero.mpr (Measure.toSphere_ne_zero volume)) (measure_ne_top _ _)
  simpa only [integral_const, probReal_univ, one_smul, one_mul] using
    (integral_inner_sphereMeasure hn hη (fun _ => (1 : ℝ)) continuous_const).symm

private theorem dimension_eq_gegenbauerNormalization {n : ℕ} (hn : 3 ≤ n) (l : ℕ) :
    let lam := ((n : ℝ) - 2) / 2
    (Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l) : ℂ) * (lam : ℂ) =
      (l + (lam : ℂ)) * ultrasphericalPolynomial lam l 1 := by
  dsimp only
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [ultrasphericalPolynomial_at_one]
  have hp : 2 * ((((m + 3 : ℕ) : ℝ) - 2) / 2 : ℝ) = (m + 1 : ℕ) := by push_cast; ring
  have hpC : 2 * (((((m + 3 : ℕ) : ℝ) - 2) / 2 : ℝ) : ℂ) = (m + 1 : ℕ) := by exact_mod_cast hp
  rw [hpC]
  have hpoch : pochhammer ((m + 1 : ℕ) : ℂ) l = ((l + m).factorial : ℂ) / m.factorial := by
    rw [show ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 by push_cast; rfl]
    have hm : 0 < ((m : ℂ) + 1).re := by norm_num; positivity
    unfold pochhammer
    rw [← Complex.Gamma_add_nat_div_Gamma_eq _ (not_neg_nat_of_re_pos hm),
      show (m : ℂ) + 1 + l = ((l + m : ℕ) : ℂ) + 1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial]
  rw [hpoch]
  have h := finrank_harmonicSubmodule_mul (n := m + 3) (by omega) l
  rw [show m + 3 - 2 = m + 1 by omega, show 2 * l + (m + 3) - 2 = 2 * l + m + 1 by omega,
    show l + (m + 3) - 3 = l + m by omega, Nat.factorial_succ] at h
  have hC := congrArg (Nat.cast (R := ℂ)) h
  push_cast at hC ⊢
  field_simp [Nat.cast_ne_zero.mpr m.factorial_ne_zero, Nat.cast_ne_zero.mpr l.factorial_ne_zero]
  linear_combination hC

private theorem orthogonality_three_le {n : ℕ} (hn : 3 ≤ n) (l l' : ℕ) :
    polarConstant n * ∫ t in Ioo (-1 : ℝ) 1,
        (zonalPolynomial n l).eval t * (zonalPolynomial n l').eval t *
          (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2) =
      if l = l' then 1 / (Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l) : ℝ)
      else 0 := by
  let lam := ((n : ℝ) - 2) / 2
  have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlam : 0 < lam := by dsimp [lam]; linarith
  have hcast : (lam : ℂ) = ((n : ℂ) - 2) / 2 := by dsimp [lam]; push_cast; rfl
  have hpow : (lam : ℂ) - 1 / 2 = ((((n : ℝ) - 3) / 2 : ℝ) : ℂ) := by
    rw [hcast]
    push_cast
    ring
  let U (k : ℕ) := ultrasphericalPolynomial lam k 1
  let W (t : ℝ) := (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2)
  let I (f : ℝ → ℂ) := ∫ t in Ioo (-1 : ℝ) 1, f t
  let K := (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * (π : ℂ)
  let c : ℂ := polarConstant n
  have hW {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
      W t = ((1 - t ^ 2) ^ (((n : ℝ) - 3) / 2) : ℝ) := by
    dsimp only [W]
    have hx : 0 ≤ t + 1 := by linarith [ht.1]
    have hy : 0 ≤ 1 - t := by linarith [ht.2]
    have hty : 0 ≤ 1 - t ^ 2 := by nlinarith [mul_nonneg hx hy]
    rw [hpow, Complex.ofReal_cpow hty]
    push_cast
    rfl
  have hcastZ (k : ℕ) (t : ℝ) : (((zonalPolynomial n k).eval t : ℝ) : ℂ) =
      ultrasphericalPolynomial lam k t / U k := by
    dsimp only [U]
    rw [hcast]
    exact zonalPolynomial_eq_ultrasphericalPolynomial_div hn k t
  have htransfer (a b : ℕ) :
      ((∫ t in Ioo (-1 : ℝ) 1, (zonalPolynomial n a).eval t * (zonalPolynomial n b).eval t *
        (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2) : ℝ) : ℂ) =
      I (fun t => ultrasphericalPolynomial lam a t * ultrasphericalPolynomial lam b t * W t) /
        (U a * U b) := by
    dsimp only [I]
    rw [← integral_complex_ofReal, div_eq_mul_inv (∫ _, _ ∂_), ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_mul, hcastZ, hcastZ, ← hW ht]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hI (a b : ℕ) :
      I (fun t => ultrasphericalPolynomial lam a t * ultrasphericalPolynomial lam b t * W t) =
      if a = b then K * Complex.Gamma (b + 2 * (lam : ℂ)) /
        ((b + lam) * Complex.Gamma lam ^ 2 * b.factorial) else 0 := by
    have h := ultrasphericalPolynomial_orthogonality hlam a b
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo] at h
    exact h
  have hmass : c * I W = 1 := by
    have h := congrArg Complex.ofReal (sphere_polarWeight_mass (show 2 ≤ n by omega))
    rw [Complex.ofReal_mul, ← integral_complex_ofReal, Complex.ofReal_one] at h
    convert h using 2
    exact setIntegral_congr_fun measurableSet_Ioo fun t ht => hW ht
  have hbase : I W = K * Complex.Gamma (2 * (lam : ℂ)) / ((lam : ℂ) * Complex.Gamma lam ^ 2) := by
    simpa only [ultrasphericalPolynomial_zero, one_mul, ite_true, Nat.cast_zero, zero_add,
      Nat.factorial_zero, Nat.cast_one, mul_one] using hI 0 0
  have hU (k : ℕ) : U k = Complex.Gamma (2 * (lam : ℂ) + k) /
      (Complex.Gamma (2 * (lam : ℂ)) * k.factorial) := by
    dsimp only [U]
    rw [ultrasphericalPolynomial_at_one]
    unfold pochhammer
    rw [← Complex.Gamma_add_nat_div_Gamma_eq _ (not_neg_nat_of_re_pos (by simp; linarith)), div_div]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, htransfer, hI]
  split_ifs with hl
  · subst l'
    have hd := dimension_eq_gegenbauerNormalization hn l
    let d : ℂ := Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l)
    change d * (lam : ℂ) = (l + (lam : ℂ)) * U l at hd
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    change c * (K * Complex.Gamma (l + 2 * (lam : ℂ)) /
      (((l : ℂ) + (lam : ℂ)) * Complex.Gamma lam ^ 2 * l.factorial) / (U l * U l)) = 1 / d
    have hc1 : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam.ne'
    have hf : (l.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr l.factorial_ne_zero
    have hg : Complex.Gamma (lam : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hlam)
    have hg2 : Complex.Gamma (2 * (lam : ℂ)) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hgl : Complex.Gamma (2 * (lam : ℂ) + l) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith [Nat.cast_nonneg (α := ℝ) l])
    have hlp : (l : ℂ) + lam ≠ 0 := Complex.ne_zero_of_re_pos (by
      simp
      linarith [Nat.cast_nonneg (α := ℝ) l])
    have hUnz : U l ≠ 0 := by rw [hU]; exact div_ne_zero hgl (mul_ne_zero hg2 hf)
    have hd0 : d ≠ 0 := by intro e; rw [e, zero_mul] at hd; exact (mul_ne_zero hlp hUnz) hd.symm
    have hu' : Complex.Gamma (2 * (lam : ℂ) + l) =
        U l * (Complex.Gamma (2 * (lam : ℂ)) * l.factorial) :=
      ((eq_div_iff (mul_ne_zero hg2 hf)).mp (hU l)).symm
    calc
      _ = c * (K * Complex.Gamma (2 * (lam : ℂ)) / ((lam : ℂ) * Complex.Gamma lam ^ 2)) *
          ((lam : ℂ) / (((l : ℂ) + (lam : ℂ)) * U l)) := by
        rw [add_comm (l : ℂ), hu']
        field_simp [hc1, hf, hg, hUnz, hlp]
      _ = 1 / d := by
        rw [← hbase, hmass, one_mul, ← hd]
        field_simp
  · simp

end ZonalOrthogonality

open ZonalOrthogonality in
/-- **Orthogonality of the zonal polynomials** (Vilenkin–Klimyk, Vol. 2, §9.3.8 (1), p. 63;
Wawrzyńczyk (9.4.10), p. 335). For `n ≥ 2`,
`c_n ∫_{-1}^{1} ω_{n,l} ω_{n,l'} (1 - t²)^{(n-3)/2} dt = δ_{ll'}/dim H_l`. -/
theorem integral_zonalPolynomial_mul_zonalPolynomial {n : ℕ} (hn : 2 ≤ n) (l l' : ℕ) :
    polarConstant n * ∫ t in Ioo (-1 : ℝ) 1,
        (zonalPolynomial n l).eval t * (zonalPolynomial n l').eval t *
          (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2) =
      if l = l' then 1 / (Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l) : ℝ)
      else 0 := by
  by_cases h : n = 2
  · subst n
    exact orthogonality_two l l'
  · exact orthogonality_three_le (by omega) l l'

/-- **Funk–Hecke formula** (Vilenkin–Klimyk, Vol. 2, §10.2.1 (5)–(6), p. 175). For `n ≥ 2`,
continuous `f`, a unit vector `η` and `p ∈ H_l`, `∫ f(⟪η, x⟫) p(x) dσ(x) = λ p(η)` with
`λ = c_n ∫_{-1}^{1} f(t) ω_{n,l}(t) (1 - t²)^{(n-3)/2} dt`. -/
theorem integral_comp_inner_mul_sphereEval {n : ℕ} (hn : 2 ≤ n) {l : ℕ} (f : ℝ → ℝ)
    (hf : Continuous f) {η : EuclideanSpace ℝ (Fin n)} (hη : ‖η‖ = 1)
    {p : MvPolynomial (Fin n) ℝ} (hp : p ∈ MvPolynomial.harmonicSubmodule (Fin n) ℝ l) :
    ∫ x : Sphere n, f ⟪η, (x : EuclideanSpace ℝ (Fin n))⟫_ℝ * MvPolynomial.sphereEval p x
        ∂sphereMeasure n =
      (polarConstant n * ∫ t in Ioo (-1 : ℝ) 1,
          f t * (zonalPolynomial n l).eval t * (1 - t ^ 2) ^ (((n : ℝ) - 3) / 2)) *
        MvPolynomial.eval (fun i => η i) p := by
  sorry

/-- **Zonal spherical functions** (Vilenkin–Klimyk, Vol. 2, §9.3.2 (4), p. 47;
Wawrzyńczyk (9.4.9), p. 335). For `n ≥ 3`, a unit vector `η` and a left-invariant probability
measure `ν` on `K_η`, `g ↦ ω_{n,l}(⟪η, g η⟫)` is a spherical function of `(SO(n), K_η)`. -/
theorem isSphericalFunction_zonalSpherical {n : ℕ} (hn : 3 ≤ n) (l : ℕ)
    {η : EuclideanSpace ℝ (Fin n)} (hη : ‖η‖ = 1) (ν : Measure (rotationStabilizer η))
    [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] :
    Subgroup.IsSphericalFunction (rotationStabilizer η) ν (zonalSpherical n l η) := by
  sorry

/-- **Classification of the spherical functions** of `(SO(n), K_η)`, `n ≥ 3`: each is
`zonalSpherical n l η` for some `l`. -/
theorem exists_eq_zonalSpherical {n : ℕ} (hn : 3 ≤ n) {η : EuclideanSpace ℝ (Fin n)}
    (hη : ‖η‖ = 1) (ν : Measure (rotationStabilizer η)) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] {φ : RotationGroup n → ℂ}
    (hφ : Subgroup.IsSphericalFunction (rotationStabilizer η) ν φ) :
    ∃ l, φ = zonalSpherical n l η := by
  sorry

/-- **Product formula** (Vilenkin–Klimyk, Vol. 2, §9.4.5 (1), p. 76; Wawrzyńczyk (9.5.2),
p. 337). For `n ≥ 3`, `ω(cos a) ω(cos b) =
c'ₙ ∫_0^π ω(cos a cos b + sin a sin b cos ψ) sin^{n-3} ψ dψ`. -/
theorem zonalPolynomial_eval_cos_mul_eval_cos {n : ℕ} (hn : 3 ≤ n) (l : ℕ) (a b : ℝ) :
    (zonalPolynomial n l).eval (cos a) * (zonalPolynomial n l).eval (cos b) =
      Gamma (((n : ℝ) - 1) / 2) / (√π * Gamma (((n : ℝ) - 2) / 2)) *
        ∫ ψ in (0 : ℝ)..π, (zonalPolynomial n l).eval (cos a * cos b + sin a * sin b * cos ψ) *
          sin ψ ^ (n - 3) := by
  let lam := ((n : ℝ) - 2) / 2
  have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlam : 0 < lam := by dsimp [lam]; linarith
  have hcast : (lam : ℂ) = ((n : ℂ) - 2) / 2 := by dsimp [lam]; push_cast; rfl
  have hshift : (lam + 1 / 2 : ℂ) = ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) := by
    rw [hcast]
    push_cast
    ring
  have hpow : 2 * lam - 1 = (n - 3 : ℕ) := by
    dsimp [lam]
    push_cast [Nat.cast_sub hn]
    ring
  have hbridge (t : ℝ) : (((zonalPolynomial n l).eval t : ℝ) : ℂ) =
      ultrasphericalPolynomial lam l t / ultrasphericalPolynomial lam l 1 := by
    rw [hcast]
    exact zonalPolynomial_eq_ultrasphericalPolynomial_div hn l t
  have h := ultrasphericalPolynomial_product_integral hlam l a b
  have hcoeff : Complex.Gamma (lam + 1 / 2 : ℂ) /
        ((√π : ℂ) * Complex.Gamma lam) =
        ((Gamma (((n : ℝ) - 1) / 2) / (√π * Gamma lam) : ℝ) : ℂ) := by
    rw [hshift, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]
  rw [hcoeff, hpow, ← hbridge, ← hbridge] at h
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, Complex.ofReal_mul, ← intervalIntegral.integral_ofReal, h]
  congr 1
  apply intervalIntegral.integral_congr
  intro ψ _
  beta_reduce
  have he : Real.rpow (sin ψ) ((n - 3 : ℕ) : ℝ) = sin ψ ^ (n - 3) :=
    Real.rpow_natCast _ _
  rw [Complex.ofReal_mul, hbridge, he]
  push_cast
  rfl

end SFVK.Spheres
