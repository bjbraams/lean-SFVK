/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import SFVK.Spheres.Basic.Disk
import DLMF.OrthogonalPolynomials.Explicit
import DLMF.OrthogonalPolynomials.Integrals.AngularRepresentations
import DLMF.OrthogonalPolynomials.Multivariate
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# Jacobi form and orthogonality of disk polynomials

The finite-sum normalization of `diskPolynomial` gives a normalized Jacobi polynomial times a
holomorphic or antiholomorphic power. The comparison with lean-DLMF gives orthogonality between
distinct bidegrees. Integration in the squared radius gives the squared norm from the Jacobi norm.

Source: Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2,
§11.3.2 (6), p. 309, and §11.4.5, p. 345.
-/

public noncomputable section

open MeasureTheory Polynomial Real Set
open scoped Nat ComplexConjugate

namespace SFVK.Spheres

namespace DiskPolynomials

open DLMF.Hypergeometric

/-- The ascending factorial starting at `p - i + 1` gives the binomial coefficient. -/
private theorem pochhammer_nat_sub_add_one_div_factorial {p i : ℕ} (hi : i ≤ p) :
    pochhammer (((p - i : ℕ) : ℂ) + 1) i / i.factorial = p.choose i := by
  rw [show ((p - i : ℕ) : ℂ) + 1 = ((p - i + 1 : ℕ) : ℂ) by push_cast; ring,
    pochhammer, ascPochhammer_nat_eq_natCast_descFactorial,
    show p - i + 1 + i - 1 = p by omega, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr i.factorial_ne_zero]

/-- The real ascending Pochhammer symbol coerces to its complex counterpart. -/
private theorem ofReal_ascPochhammer_real (n : ℕ) (α : ℝ) :
    (((ascPochhammer ℝ n).eval α : ℝ) : ℂ) = pochhammer (α : ℂ) n := by
  rw [pochhammer, ← Complex.ofRealHom_eq_coe, ← Polynomial.eval₂_at_apply,
    ← Polynomial.eval_map, ascPochhammer_map]
  rfl

end DiskPolynomials

open DiskPolynomials DLMF.Hypergeometric in
set_option maxHeartbeats 1000000 in
/-- **Jacobi form** (Vilenkin–Klimyk, Vol. 2, §11.3.2 (6), p. 309, and §11.4.5, p. 345). For
`-1 < α` and `q ≤ p`, `R^α_{p,q}(w) = (q!/(α + 1)_q) P_q^{(α, p-q)}(2|w|² - 1) w^{p-q}`, with
lean-DLMF's Jacobi polynomial. -/
theorem diskPolynomial_eq_jacobiPolynomialP {α : ℝ} (hα : -1 < α) {p q : ℕ} (hqp : q ≤ p)
    (w : ℂ) :
    diskPolynomial α p q w =
      ((q ! / (ascPochhammer ℝ q).eval (α + 1) : ℝ) : ℂ) *
        DLMF.OrthogonalPolynomials.jacobiPolynomialP α ((p - q : ℕ) : ℂ) q
          ((2 * ‖w‖ ^ 2 - 1 : ℝ) : ℂ) * w ^ (p - q) := by
  have hαre : -1 < (α : ℂ).re := by simpa using hα
  let r : ℂ := ‖w‖ ^ 2
  have hr : w * conj w = r := by rw [Complex.mul_conj]; simp [r, Complex.normSq_eq_norm_sq]
  rw [DLMF.OrthogonalPolynomials.jacobi_binomial_sum hαre, diskPolynomial_def, min_eq_right hqp]
  push_cast
  simp only [ofReal_ascPochhammer_real, Complex.ofReal_add, Complex.ofReal_one]
  rw [← mul_assoc (_ / _) (((2 : ℂ) ^ q)⁻¹), Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hiq : i ≤ q := by simpa using hi
  have hip : i ≤ p := hiq.trans hqp
  have hqsub : q + 1 - 1 - i = q - i := by omega
  have hqsub' : q - (q - i) = i := by omega
  rw [hqsub, hqsub']
  rw [show ((α : ℂ) + q - ((q - i : ℕ) : ℂ) + 1) = (α + 1) + i by
    push_cast [Nat.cast_sub hiq]; ring,
    show ((p - q : ℕ) : ℂ) + ((q - i : ℕ) : ℂ) + 1 = ↑(p - i) + 1 by
      push_cast [Nat.cast_sub hqp, Nat.cast_sub hiq, Nat.cast_sub hip]; ring,
    pochhammer_nat_sub_add_one_div_factorial hip]
  have hsplit : pochhammer ((α : ℂ) + 1) q =
      pochhammer (α + 1) i * pochhammer (α + 1 + i) (q - i) := by
    rw [← pochhammer_add, Nat.add_sub_cancel' hiq]
  have hpi : pochhammer ((α : ℂ) + 1) i ≠ 0 :=
    pochhammer_ne_zero_of_re_pos (by simp; linarith) i
  have hpq : pochhammer ((α : ℂ) + 1 + i) (q - i) ≠ 0 :=
    pochhammer_ne_zero_of_re_pos (by simp; linarith [Nat.cast_nonneg (α := ℝ) i]) _
  have h2 : (2 : ℂ) ^ q ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfac : ((q - i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (q - i).factorial_ne_zero
  have hchoose : (q.choose i : ℂ) * i.factorial * (q - i).factorial = q.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hiq
  have hpowers : w ^ (p - i) * conj w ^ (q - i) = r ^ (q - i) * w ^ (p - q) := by
    have hp : p - i = (q - i) + (p - q) := by omega
    rw [hp, pow_add, ← hr, mul_pow]
    ring
  have hr₁ : 2 * r - 1 - 1 = -(2 * (1 - r)) := by ring
  have hr₂ : 2 * r - 1 + 1 = 2 * r := by ring
  change _ * (1 - r) ^ i * w ^ (p - i) * conj w ^ (q - i) =
    ((_ / _ * _) * (_ * _ * (2 * r - 1 - 1) ^ i * (2 * r - 1 + 1) ^ (q - i))) * _
  rw [mul_assoc (_ * _) (w ^ (p - i)), hpowers, hr₁, hr₂,
    neg_pow (2 * (1 - r)), mul_pow (2 : ℂ) (1 - r), mul_pow (2 : ℂ) r, hsplit]
  have hqpow : (2 : ℂ) ^ i * 2 ^ (q - i) = 2 ^ q := by
    rw [← pow_add, Nat.add_sub_cancel' hiq]
  let a := pochhammer ((α : ℂ) + 1) i
  let b := pochhammer ((α : ℂ) + 1 + i) (q - i)
  have hcoeff : (q.factorial : ℂ) / (a * b) * (2 ^ q)⁻¹ * (b / (q - i).factorial) *
      2 ^ i * 2 ^ (q - i) = (q.choose i : ℂ) * i.factorial / a := by
    calc
      _ = ((q.factorial : ℂ) / (a * b) * (b / (q - i).factorial)) *
          ((2 ^ q)⁻¹ * (2 ^ i * 2 ^ (q - i))) := by ring
      _ = _ := by
        rw [hqpow, inv_mul_cancel₀ h2, mul_one, ← hchoose]
        field_simp [show a ≠ 0 from hpi, show b ≠ 0 from hpq, hfac]
  calc
    _ = ((q.choose i : ℂ) * i.factorial / a) *
        ((-1 : ℂ) ^ i * p.choose i * (1 - r) ^ i * r ^ (q - i) * w ^ (p - q)) := by
      simp only [a]
      ring
    _ = _ := by rw [← hcoeff]; ring

namespace DiskPolynomials

open DLMF.Hypergeometric

/-- Comparison with the lean-DLMF disk polynomial for `α > -1`. -/
private theorem diskPolynomial_eq_dlmf {α : ℝ} (hα : -1 < α) (p q : ℕ) (z : ℂ) :
    diskPolynomial α p q z = DLMF.OrthogonalPolynomials.diskPolynomial α p q z := by
  have hαc : -1 < (α : ℂ).re := by simpa using hα
  have hmain {a b : ℕ} (hba : b ≤ a) (w : ℂ) :
      diskPolynomial α a b w = DLMF.OrthogonalPolynomials.diskPolynomial α a b w := by
    rw [diskPolynomial_eq_jacobiPolynomialP hα hba,
      DLMF.OrthogonalPolynomials.diskPolynomial_eq_jacobi_of_le hαc hba,
      DLMF.OrthogonalPolynomials.jacobiPolynomialP_one]
    have hnorm : w * star w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using Complex.mul_conj w
    rw [hnorm]
    push_cast
    rw [ofReal_ascPochhammer_real, Complex.ofReal_add, Complex.ofReal_one]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rcases le_total q p with hqp | hpq
  · exact hmain hqp z
  · have hswap : diskPolynomial α p q z = diskPolynomial α q p (conj z) := by
      simp only [diskPolynomial_def, min_comm p q, Complex.norm_conj, Complex.conj_conj]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm (p.choose i : ℝ) (q.choose i : ℝ)]
      ac_rfl
    rw [hswap, hmain hpq]
    exact (DLMF.OrthogonalPolynomials.diskPolynomial_swap α p q z).symm

/-- Complex conjugation of the polynomial corresponds to conjugation of its argument. -/
private theorem diskPolynomial_conj_eq_dlmf {α : ℝ} (hα : -1 < α) (p q : ℕ) (z : ℂ) :
    conj (diskPolynomial α p q z) = DLMF.OrthogonalPolynomials.diskPolynomial α p q (conj z) := by
  rw [← diskPolynomial_swap, diskPolynomial_eq_dlmf hα,
    DLMF.OrthogonalPolynomials.diskPolynomial_swap]
  rfl

/-- Distinct bidegrees are orthogonal with respect to the disk weight. -/
private theorem integral_diskPolynomial_mul_conj_eq_zero {α : ℝ} (hα : -1 < α)
    {p q p' q' : ℕ} (hne : (p, q) ≠ (p', q')) :
    ∫ w in Metric.ball (0 : ℂ) 1, (((α + 1) / π * (1 - ‖w‖ ^ 2) ^ α : ℝ) : ℂ) *
        diskPolynomial α p q w * conj (diskPolynomial α p' q' w) = 0 := by
  let inclusion : ℝ × ℝ ≃ᵐ ℂ := Complex.measurableEquivRealProd.symm
  let disk : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 < 1}
  let F (w : ℂ) := ((1 - ‖w‖ ^ 2) ^ α : ℝ) *
    diskPolynomial α p q w * conj (diskPolynomial α p' q' w)
  have hpre : inclusion ⁻¹' Metric.ball (0 : ℂ) 1 = disk := by
    ext a
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
    rw [← sq_lt_sq₀ (norm_nonneg _) zero_le_one, one_pow, Complex.sq_norm,
      Complex.normSq_apply]
    simp [inclusion, disk, pow_two]
  have hmap : MeasurePreserving inclusion
      ((volume : Measure (ℝ × ℝ)).restrict disk)
      ((volume : Measure ℂ).restrict (Metric.ball (0 : ℂ) 1)) := by
    rw [← hpre]
    exact (Complex.volume_preserving_equiv_real_prod.symm).restrict_preimage
      Metric.isOpen_ball.measurableSet
  have htransfer := hmap.integral_comp' F
  have hdisk : MeasurableSet disk := by
    rw [← hpre]
    exact inclusion.measurable Metric.isOpen_ball.measurableSet
  have hvanish : ∫ w in Metric.ball (0 : ℂ) 1, F w = 0 := by
    rw [← htransfer, ← DLMF.OrthogonalPolynomials.diskPolynomial_orthogonal hα _ _ _ _ hne]
    refine setIntegral_congr_fun hdisk fun a _ => ?_
    simp only [F]
    rw [diskPolynomial_conj_eq_dlmf hα, diskPolynomial_eq_dlmf hα]
    simp only [Complex.sq_norm,
      Complex.normSq_apply, show (inclusion a).re = a.1 from rfl,
      show (inclusion a).im = a.2 from rfl]
    have hd : inclusion a = ↑a.1 + Complex.I * ↑a.2 := by
      apply Complex.ext <;> simp [inclusion]
    have hcd : conj (inclusion a) = ↑a.1 - Complex.I * ↑a.2 := by simp [hd, sub_eq_add_neg]
    rw [show 1 - (a.1 * a.1 + a.2 * a.2) = 1 - a.1 ^ 2 - a.2 ^ 2 by ring, hcd, hd]
    exact (mul_assoc _ _ _).trans (mul_comm _ _)
  calc
    _ = ((((α + 1) / π : ℝ) : ℂ)) * ∫ w in Metric.ball (0 : ℂ) 1, F w := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun w _ => ?_
      simp only [F, Complex.ofReal_mul]
      ring
    _ = 0 := by rw [hvanish, mul_zero]

/-- Integrate a function of squared radius against area on the unit disk. -/
private theorem integral_norm_sq_ball (f : ℝ → ℂ) :
    ∫ z in Metric.ball (0 : ℂ) 1, f (‖z‖ ^ 2) = (π : ℂ) * ∫ r in Ioo (0 : ℝ) 1, f r := by
  let B := Metric.ball (0 : ℂ) 1
  let A := Ioo (-π) π
  let R := Ioo (0 : ℝ) 1
  let S := Complex.polarCoord.symm ⁻¹' B
  let g (z : ℂ) := f (‖z‖ ^ 2)
  have hequal : R ×ˢ A = S ∩ polarCoord.target := by
    ext p
    simp only [mem_inter_iff, mem_preimage, Metric.mem_ball, dist_zero_right,
      Complex.norm_polarCoord_symm, polarCoord_target, mem_prod, mem_Ioo, mem_Ioi, A, B, R, S]
    constructor
    · exact fun ⟨⟨hp, hpr⟩, hθ⟩ => ⟨by simpa [abs_of_pos hp] using hpr, hp, hθ⟩
    · exact fun ⟨hpr, hp, hθ⟩ => ⟨⟨hp, by simpa [abs_of_pos hp] using hpr⟩, hθ⟩
  have hS : MeasurableSet S := by
    have hsymm : Continuous (Complex.polarCoord.symm : ℝ × ℝ → ℂ) := by
      rw [funext Complex.polarCoord_symm_apply]
      fun_prop
    exact hsymm.measurable Metric.isOpen_ball.measurableSet
  have hpolar : (∫ z in B, g z) = ∫ p in R ×ˢ A, (p.1 : ℂ) * f (p.1 ^ 2) := by
    rw [← integral_indicator Metric.isOpen_ball.measurableSet,
      ← Complex.integral_comp_polarCoord_symm]
    have hind : (fun p : ℝ × ℝ => p.1 • B.indicator g (Complex.polarCoord.symm p)) =
        S.indicator (fun p => p.1 • g (Complex.polarCoord.symm p)) := by
      funext p
      by_cases hp : Complex.polarCoord.symm p ∈ B
      · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ S from hp)]
      · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ S from hp), smul_zero]
    rw [hind, integral_indicator hS, Measure.restrict_restrict hS, ← hequal]
    refine setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun p hp => ?_
    rw [Complex.real_smul]
    simp only [g, Complex.norm_polarCoord_symm, sq_abs]
  have hangular : ∫ _ in A, (1 : ℂ) = (2 * π : ℝ) := by
    rw [setIntegral_const, Complex.real_smul, mul_one, measureReal_def]
    dsimp only [A]
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    push_cast
    ring
  have hsq : (fun r : ℝ => r ^ 2) '' R = R := by
    have hmono : StrictMonoOn (fun r : ℝ => r ^ 2) (Icc 0 1) :=
      fun _ hr _ hs hrs => (sq_lt_sq₀ hr.1 hs.1).mpr hrs
    have hcont : Continuous (fun r : ℝ => r ^ 2) := by fun_prop
    norm_num [R, hcont.continuousOn.image_Ioo_of_strictMonoOn zero_le_one hmono]
  have hradial : (∫ r in R, f r) = (2 : ℂ) * ∫ r in R, (r : ℂ) * f (r ^ 2) := by
    conv_lhs => rw [← hsq, integral_image_eq_integral_deriv_smul_of_monotoneOn
      measurableSet_Ioo (f' := fun r => 2 * r)
        (fun r _ => by simpa using (hasDerivAt_pow 2 r).hasDerivWithinAt)
        (fun r hr s hs hrs => (sq_le_sq₀ hr.1.le hs.1.le).mpr hrs)]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun r _ => ?_
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_assoc]
  calc
    _ = _ := hpolar
    _ = (∫ r in R, (r : ℂ) * f (r ^ 2)) * ∫ _ in A, (1 : ℂ) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      simpa using integral_prod_mul (μ := (volume : Measure ℝ).restrict R)
        (ν := (volume : Measure ℝ).restrict A) (fun r => (r : ℂ) * f (r ^ 2)) (fun _ => (1 : ℂ))
    _ = _ := by rw [hangular, hradial]; push_cast; ring

/-- The Jacobi polynomial at real parameters and argument is real. -/
private theorem conj_jacobiPolynomialP_real {α : ℝ} (hα : -1 < α) (d n : ℕ) (x : ℝ) :
    conj (DLMF.OrthogonalPolynomials.jacobiPolynomialP α d n x) =
      DLMF.OrthogonalPolynomials.jacobiPolynomialP α d n x := by
  have hαc : -1 < (α : ℂ).re := by simpa using hα
  rw [DLMF.OrthogonalPolynomials.jacobi_finite_sum hαc]
  have hp (r : ℝ) (k : ℕ) : conj (pochhammer (r : ℂ) k) = pochhammer (r : ℂ) k := by
    rw [← ofReal_ascPochhammer_real]
    exact Complex.conj_ofReal _
  simp only [map_sum, map_sub, map_mul, map_div₀, map_pow, map_natCast,
    Complex.conj_ofReal, map_one, map_ofNat]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← show (((n : ℝ) + α + d + 1 : ℝ) : ℂ) = (n : ℂ) + α + d + 1 by push_cast; rfl,
    ← show ((α + (k : ℝ) + 1 : ℝ) : ℂ) = (α : ℂ) + k + 1 by push_cast; rfl, hp, hp]

/-- The Jacobi squared norm after shifting the interval to `(0, 1)`. -/
private theorem integral_jacobi_norm_unit {α : ℝ} (hα : -1 < α) (d n : ℕ) :
    ∫ t : ℝ in Ioo 0 1,
      DLMF.OrthogonalPolynomials.jacobiPolynomialP α d n ((2 * t - 1 : ℝ) : ℂ) ^ 2 *
        ((1 - t) ^ α : ℝ) * (t : ℂ) ^ d =
      ((n + d).factorial : ℂ) * pochhammer ((α : ℂ) + 1) n /
        (((2 * n : ℕ) + d + (α : ℂ) + 1) * n.factorial * pochhammer ((α : ℂ) + 1) (n + d)) := by
  let a := ((α : ℂ) + 1)
  let p := n + d
  let b := (a + p : ℂ)
  let c := (a + p + n : ℂ)
  let K := (2 : ℂ) ^ ((α : ℂ) + d + 1)
  have hb : 0 < b.re := by
    simp [b, a]
    linarith [Nat.cast_nonneg (α := ℝ) p]
  have hc : 0 < c.re := by
    simp [c, a]
    linarith [Nat.cast_nonneg (α := ℝ) p, Nat.cast_nonneg (α := ℝ) n]
  have hK : K ≠ 0 := by
    apply Complex.cpow_ne_zero_iff.mpr
    exact Or.inl (by norm_num)
  let P (t : ℝ) := DLMF.OrthogonalPolynomials.jacobiPolynomialP α d n (t : ℂ)
  let J (t : ℝ) := P t ^ 2 * (1 - (t : ℂ)) ^ (α : ℂ) * (1 + (t : ℂ)) ^ ((d : ℕ) : ℂ)
  let F (t : ℝ) := P (2 * t - 1) ^ 2 * ((1 - t) ^ α : ℝ) * (t : ℂ) ^ d
  have hscale : (∫ t : ℝ in (-1)..1, J t) = K * ∫ t in Ioo 0 1, F t := by
    have h := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1) (f := J) 2 (-1)
    norm_num only [mul_zero, zero_add, mul_one] at h
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo] at h
    rw [← h, Complex.real_smul, Complex.ofReal_ofNat, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    dsimp only [J, F]
    simp only [← sub_eq_add_neg]
    have hsub : (1 : ℂ) - ((2 * t - 1 : ℝ) : ℂ) = ((2 * (1 - t) : ℝ) : ℂ) := by push_cast; ring
    have hadd : (1 : ℂ) + ((2 * t - 1 : ℝ) : ℂ) = 2 * (t : ℂ) := by push_cast; ring
    rw [hsub, hadd, ← Complex.ofReal_cpow (mul_nonneg zero_le_two (sub_nonneg.2 ht.2.le)),
      Real.mul_rpow zero_le_two (sub_nonneg.2 ht.2.le), Complex.ofReal_mul,
      Complex.ofReal_cpow zero_le_two, Complex.ofReal_ofNat, Complex.cpow_natCast, mul_pow]
    have hK' : K = (2 : ℂ) * (2 : ℂ) ^ (α : ℂ) * (2 : ℂ) ^ d := by
      dsimp only [K]
      rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one,
        Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_natCast]
      ring
    rw [hK']
    ring
  have hn := DLMF.OrthogonalPolynomials.jacobi_norm_all hα
    (show -1 < (d : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) d]) n
  have hJ : (∫ t : ℝ in (-1)..1, J t) =
      K * Complex.Gamma (a + n) * p.factorial * pochhammer b n /
        (n.factorial * (c * Complex.Gamma c)) := by
    dsimp only [J, P]
    push_cast at hn
    rw [hn]
    have he₁ : (α : ℂ) + n + 1 = a + n := by dsimp [a]; ring
    have he₂ : (d : ℂ) + n + 1 = (p : ℂ) + 1 := by dsimp [p]; push_cast; ring
    have he₃ : (α : ℂ) + d + n + 1 = b := by dsimp [b, a, p]; push_cast; ring
    have he₄ : (α : ℂ) + d + 2 * n + 2 = c + 1 := by dsimp [c, a, p]; push_cast; ring
    rw [he₁, he₂, Complex.Gamma_nat_eq_factorial, he₃, he₄,
      Complex.Gamma_add_one c (Complex.ne_zero_of_re_pos hc)]
  have ha : 0 < a.re := by simp [a]; linarith
  have hΓ_a := Complex.Gamma_ne_zero_of_re_pos ha
  have hΓ_b := Complex.Gamma_ne_zero_of_re_pos hb
  have hΓ_c := Complex.Gamma_ne_zero_of_re_pos hc
  have hΓadd_n : Complex.Gamma (a + n) / Complex.Gamma a = pochhammer a n :=
    Complex.Gamma_add_nat_div_Gamma_eq a (not_neg_nat_of_re_pos ha)
  have hΓadd_p : Complex.Gamma b / Complex.Gamma a = pochhammer a p :=
    Complex.Gamma_add_nat_div_Gamma_eq a (not_neg_nat_of_re_pos ha)
  have hΓadd_c : Complex.Gamma c / Complex.Gamma b = pochhammer b n :=
    Complex.Gamma_add_nat_div_Gamma_eq b (not_neg_nat_of_re_pos hb)
  have hnorm : (∫ t in Ioo (0 : ℝ) 1, F t) =
      (p.factorial : ℂ) * pochhammer a n / (c * n.factorial * pochhammer a p) := by
    apply mul_left_cancel₀ hK
    rw [← hscale, hJ, ← hΓadd_n, ← hΓadd_p, ← hΓadd_c]
    field_simp [Complex.ne_zero_of_re_pos hc, hΓ_a, hΓ_b, hΓ_c,
      Nat.cast_ne_zero.mpr n.factorial_ne_zero]
  rw [hnorm]
  dsimp only [p, a, c]
  push_cast
  ring

/-- The squared norm of a disk polynomial in the normalized area weight. -/
private theorem integral_diskPolynomial_mul_conj_self {α : ℝ} (hα : -1 < α) (p q : ℕ) :
    ∫ w in Metric.ball (0 : ℂ) 1, (((α + 1) / π * (1 - ‖w‖ ^ 2) ^ α : ℝ) : ℂ) *
        diskPolynomial α p q w * conj (diskPolynomial α p q w) =
      (((α + 1) / (p + q + α + 1) * (p ! * q !) /
        ((ascPochhammer ℝ p).eval (α + 1) * (ascPochhammer ℝ q).eval (α + 1)) : ℝ) : ℂ) := by
  have hmain {p q : ℕ} (hpq : q ≤ p) :
      ∫ w in Metric.ball (0 : ℂ) 1, (((α + 1) / π * (1 - ‖w‖ ^ 2) ^ α : ℝ) : ℂ) *
          diskPolynomial α p q w * conj (diskPolynomial α p q w) =
        (((α + 1) / (p + q + α + 1) * (p ! * q !) /
          ((ascPochhammer ℝ p).eval (α + 1) * (ascPochhammer ℝ q).eval (α + 1)) : ℝ) : ℂ) := by
    let d := p - q
    let a := (α : ℂ) + 1
    let D := (p : ℂ) + q + (α : ℂ) + 1
    let F (t : ℝ) := DLMF.OrthogonalPolynomials.jacobiPolynomialP α d q ((2 * t - 1 : ℝ) : ℂ) ^ 2 *
      ((1 - t) ^ α : ℝ) * (t : ℂ) ^ d
    let C := a / (π : ℂ) * ((q.factorial : ℂ) / pochhammer a q) ^ 2
    have hP (n : ℕ) : (((ascPochhammer ℝ n).eval (α + 1) : ℝ) : ℂ) = pochhammer a n := by
      rw [ofReal_ascPochhammer_real, Complex.ofReal_add, Complex.ofReal_one]
    have hformula (w : ℂ) : (((α + 1) / π * (1 - ‖w‖ ^ 2) ^ α : ℝ) : ℂ) *
        diskPolynomial α p q w * conj (diskPolynomial α p q w) = C * F (‖w‖ ^ 2) := by
      rw [diskPolynomial_eq_jacobiPolynomialP hα hpq]
      simp only [map_mul, map_pow, Complex.conj_ofReal, conj_jacobiPolynomialP_real hα]
      simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one,
        Complex.ofReal_natCast]
      rw [hP]
      have hnorm : w ^ d * conj w ^ d = ((‖w‖ ^ 2 : ℝ) : ℂ) ^ d := by
        rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      let J := DLMF.OrthogonalPolynomials.jacobiPolynomialP α d q ((2 * ‖w‖ ^ 2 - 1 : ℝ) : ℂ)
      change _ = C * F (‖w‖ ^ 2)
      calc
        _ = C * (J ^ 2 * ((1 - ‖w‖ ^ 2) ^ α : ℝ)) * (w ^ d * conj w ^ d) := by
          dsimp only [C, a, J, d]
          ring
        _ = _ := by rw [hnorm]; exact mul_assoc _ _ _
    simp_rw [hformula]
    rw [integral_const_mul, integral_norm_sq_ball]
    have hsum : q + d = p := by dsimp [d]; omega
    have hnorm : (∫ t in Ioo (0 : ℝ) 1, F t) = (p.factorial : ℂ) * pochhammer a q /
        (D * q.factorial * pochhammer a p) := by
      dsimp only [F]
      rw [integral_jacobi_norm_unit hα, hsum]
      simp only [Nat.cast_mul, Nat.cast_ofNat]
      have hD : (2 * (q : ℂ) + (d : ℂ) + α + 1) = D := by
        dsimp [D, d]
        push_cast [Nat.cast_sub hpq]
        ring
      rw [hD]
    rw [hnorm]
    push_cast
    rw [hP, hP]
    have hαa : 0 < a.re := by simp [a]; linarith
    have hD : D ≠ 0 := by
      apply Complex.ne_zero_of_re_pos
      simp [D]
      linarith [Nat.cast_nonneg (α := ℝ) p, Nat.cast_nonneg (α := ℝ) q]
    dsimp only [C, a, D] at *
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
      pochhammer_ne_zero_of_re_pos hαa, Nat.cast_ne_zero.mpr q.factorial_ne_zero, hD]
  rcases le_total q p with hqp | hpq
  · exact hmain hqp
  · calc
      _ = ∫ w in Metric.ball (0 : ℂ) 1,
          (((α + 1) / π * (1 - ‖w‖ ^ 2) ^ α : ℝ) : ℂ) *
            diskPolynomial α q p w * conj (diskPolynomial α q p w) := by
        refine setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun w _ => ?_
        rw [diskPolynomial_swap α p q, Complex.conj_conj]
        ring
      _ = _ := (hmain hpq).trans (by push_cast; ring)

end DiskPolynomials

open DiskPolynomials in
/-- **Orthogonality on the disc.** For `-1 < α`,
`((α + 1)/π) ∫_{|w|<1} R^α_{p,q} conj R^α_{p',q'} (1 - |w|²)^α dA = δ h` with
`h = (α + 1)/(p + q + α + 1) · p! q!/((α + 1)_p (α + 1)_q)`. -/
theorem integral_diskPolynomial_mul_conj {α : ℝ} (hα : -1 < α) (p q p' q' : ℕ) :
    ∫ w in Metric.ball (0 : ℂ) 1, (((α + 1) / π * (1 - ‖w‖ ^ 2) ^ α : ℝ) : ℂ) *
        diskPolynomial α p q w * conj (diskPolynomial α p' q' w) =
      if p = p' ∧ q = q' then
        (((α + 1) / (p + q + α + 1) * (p ! * q !) /
          ((ascPochhammer ℝ p).eval (α + 1) * (ascPochhammer ℝ q).eval (α + 1)) : ℝ) : ℂ)
      else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact integral_diskPolynomial_mul_conj_self hα p q
  · exact integral_diskPolynomial_mul_conj_eq_zero hα fun he => h ⟨congrArg Prod.fst he,
      congrArg Prod.snd he⟩

end SFVK.Spheres
