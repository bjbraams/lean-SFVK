/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU2.Basic.Coordinates
public import SFVK.SU2.Basic.MatrixElements
public import SFVK.SU2.Basic.WignerSmallD
public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import DLMF.Legendre.Basic.Harmonics
import DLMF.OrthogonalPolynomials.Differential.ChebyshevAndShifts
import DLMF.OrthogonalPolynomials.Explicit
import Mathlib.Data.Int.NatAbs

/-!
# Wigner's small `d`-functions: Euler factorization and classical forms

The Euler factorization follows Edmonds, *Angular Momentum in Quantum Mechanics*, (4.1.12),
p. 55, and (4.1.15), p. 57. The Jacobi and Legendre forms are (4.1.23)–(4.1.26), pp. 58–59.
The Jacobi and Legendre functions use lean-DLMF's normalizations. In particular, the associated
Legendre form compensates for the Condon–Shortley phase of the Ferrers function in lean-DLMF.
The Jacobi comparison uses the binomial expansion in `DLMF.OrthogonalPolynomials.Explicit`.
The Ferrers comparison uses `DLMF.OrthogonalPolynomials.jacobi_derivative`.
-/

public noncomputable section

open scoped InnerProductSpace Real
open TauCeti

namespace SFVK.SU2

namespace WignerSmallD

/-- The binomial coefficient in complex factorial form. -/
private theorem natCast_choose_eq_factorial_div (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℂ) = n.factorial / ((k.factorial : ℂ) * (n - k).factorial) := by
  apply (eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr k.factorial_ne_zero)
    (Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero))).mpr
  simpa only [Nat.cast_mul, mul_assoc] using
    congrArg (Nat.cast : ℕ → ℂ) (Nat.choose_mul_factorial_mul_factorial hk)

/-- Multiplying the square root of a quotient by its positive denominator. -/
private theorem sqrt_div_mul_eq_sqrt_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Real.sqrt (a / b) * b = Real.sqrt (a * b) := by
  have hsb : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  calc
    Real.sqrt (a / b) * b = (Real.sqrt a / Real.sqrt b) * (Real.sqrt b) ^ 2 := by
      rw [Real.sqrt_div ha, Real.sq_sqrt hb.le]
    _ = Real.sqrt a * Real.sqrt b := by field_simp
    _ = _ := (Real.sqrt_mul ha b).symm

/-- The torus acts on each normalized weight vector by its exponential phase. -/
private theorem unitaryModel_torusExp_single (d : ℕ) (i : Fin (d + 1)) (α : ℝ) :
    unitaryModel d (SU2.torusExp (α / 2)) (EuclideanSpace.single i 1) =
      Complex.exp (Complex.I * (magneticWeight d i * α)) • EuclideanSpace.single i 1 := by
  have hn : (monomialNorm d i : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (monomialNorm_pos d i).ne'
  have hscale : (monomialScale d).symm (EuclideanSpace.single i 1) =
      (monomialNorm d i : ℂ)⁻¹ • EuclideanSpace.single i 1 := by
    apply (monomialScale d).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, map_smul, monomialScale_single, smul_smul,
      inv_mul_cancel₀ hn, one_smul]
  simp only [unitaryModel_apply, hscale, map_smul, SU2.symPowerModel_apply,
    SU2.weightEquiv_symm_single, SU2.torusExp_def, SU2.symPower_torusHom_weightBasis,
    SU2.weightEquiv_weightBasis, monomialScale_single, smul_smul]
  rw [mul_right_comm, inv_mul_cancel₀ hn, one_mul, Circle.coe_exp, ← Complex.exp_int_mul]
  congr 2
  rw [SU2.weight_def, magneticWeight_def]
  push_cast
  ring

/-- The torus matrix is diagonal in the normalized weight basis. -/
private theorem matrixElement_torusExp (d : ℕ) (i k : Fin (d + 1)) (α : ℝ) :
    matrixElement d i k (SU2.torusExp (α / 2)) =
      if i = k then Complex.exp (Complex.I * (magneticWeight d k * α)) else 0 := by
  rw [matrixElement_def, unitaryModel_torusExp_single, inner_smul_right,
    EuclideanSpace.inner_single_left, map_one, one_mul, PiLp.single_apply]
  split_ifs <;> simp

/-- The middle Euler factor has Wigner small `d` entries. -/
private theorem matrixElement_eulerMiddle (d : ℕ) (i k : Fin (d + 1)) (β : ℝ) :
    matrixElement d i k (eulerMiddle β) = wignerSmallD d i k β := by
  have hi : (i : ℕ) ≤ d := Nat.le_of_lt_succ i.isLt
  have hk : (k : ℕ) ≤ d := Nat.le_of_lt_succ k.isLt
  rw [matrixElement_eq_entrySum, entrySum, coe_eulerMiddle]
  simp only [wignerSmallD, ite_eq_left (show (i : ℕ) ≤ d ∧ (k : ℕ) ≤ d from ⟨hi, hk⟩),
    Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum]
  let summand (s : ℕ) : ℂ :=
    (↑(Real.sqrt (↑(i.val.factorial * (d - i.val).factorial) /
      ↑(k.val.factorial * (d - k.val).factorial))) : ℂ) *
      ((k.val.choose (d - i.val - s) * (d - k.val).choose s : ℕ) : ℂ) *
      (-1) ^ (d - i.val - s) * (Real.cos (β / 2) : ℂ) ^ (2 * s + i.val + k.val - d) *
      (Real.sin (β / 2) : ℂ) ^ (2 * d - i.val - k.val - 2 * s)
  have hs : (Finset.range (d - i.val + 1)) ⊆ Finset.range (d + 1) := by
    exact Finset.range_mono (by omega)
  rw [← Finset.sum_subset hs (fun s _ hsmall => by
    simp only [Finset.mem_range, not_lt] at hsmall
    rw [ite_eq_right (by omega : ¬(d ≤ s + i.val + k.val ∧
      s + i.val ≤ d ∧ s + k.val ≤ d))])]
  calc
    _ = ∑ s ∈ Finset.range (d - i.val + 1), summand s := by
      apply Finset.sum_congr rfl
      intro s hsd
      have hsi : s ≤ d - i.val := Nat.le_of_lt_succ (Finset.mem_range.mp hsd)
      by_cases h : d ≤ s + i.val + k.val ∧ s + i.val ≤ d ∧ s + k.val ≤ d
      · rw [ite_eq_left h]
        have hconst : ((Real.sqrt (i.val.factorial * (d - i.val).factorial *
            k.val.factorial * (d - k.val).factorial) : ℝ) : ℂ) =
            (↑(Real.sqrt (↑(i.val.factorial * (d - i.val).factorial) /
              ↑(k.val.factorial * (d - k.val).factorial))) : ℂ) *
                (k.val.factorial * (d - k.val).factorial) := by
          have hr := (sqrt_div_mul_eq_sqrt_mul (by positivity : 0 ≤
            (i.val.factorial : ℝ) * (d - i.val).factorial)
            (by positivity : 0 < (k.val.factorial : ℝ) * (d - k.val).factorial)).symm
          simpa only [Nat.cast_mul, Complex.ofReal_mul, Complex.ofReal_natCast, mul_assoc] using
            congrArg Complex.ofReal hr
        have hchoose₁ := natCast_choose_eq_factorial_div k.val (d - i.val - s) (by omega)
        have hchoose₂ := natCast_choose_eq_factorial_div (d - k.val) s (by omega)
        have hsub : k.val - (d - i.val - s) = s + i.val + k.val - d := by omega
        have hcos : s + i.val + k.val - d + s = 2 * s + i.val + k.val - d := by omega
        have hsin : d - k.val - s + (d - i.val - s) = 2 * d - i.val - k.val - 2 * s := by omega
        simp only [summand, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Nat.cast_mul, hchoose₁, hchoose₂, hsub, Complex.ofReal_div,
          Complex.ofReal_mul, Complex.ofReal_natCast]
        rw [hconst, ← neg_one_mul (↑(Real.sin (β / 2)) : ℂ), mul_pow]
        simp only [Nat.cast_mul, ← hcos, ← hsin, pow_add]
        ring
      · rw [ite_eq_right h]
        dsimp only [summand]
        by_cases hs' : d - k.val < s
        · simp [Nat.choose_eq_zero_of_lt hs']
        have hki : k.val < d - i.val - s := by omega
        simp [Nat.choose_eq_zero_of_lt hki]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [summand, Complex.ofReal_pow, Complex.ofReal_neg,
        Complex.ofReal_one, Complex.ofReal_natCast]
      ring

open DLMF DLMF.OrthogonalPolynomials in
/-- The DLMF Jacobi binomial expansion in half-angle powers. -/
private theorem jacobiPolynomialP_nat_cos (a b r : ℕ) (β : ℝ) :
    jacobiPolynomialP a b r (Real.cos β) =
      ∑ j ∈ Finset.range (r + 1), ((r + a).choose j : ℂ) * (r + b).choose (r - j) *
        (-1) ^ (r - j) * (Real.cos (β / 2) : ℂ) ^ (2 * j) *
          (Real.sin (β / 2) : ℂ) ^ (2 * (r - j)) := by
  have hα : -1 < (a : ℂ).re := by
    rw [Complex.natCast_re]
    exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg a)
  have hβ : 2 * (β / 2) = β := by ring
  have hc : (Real.cos β : ℂ) + 1 = 2 * (Real.cos (β / 2) : ℂ) ^ 2 := by
    have hr := Real.cos_two_mul (β / 2)
    rw [hβ] at hr
    exact_mod_cast (show Real.cos β + 1 = 2 * Real.cos (β / 2) ^ 2 by linarith)
  have hs : (Real.cos β : ℂ) - 1 = -(2 * (Real.sin (β / 2) : ℂ) ^ 2) := by
    have hr := Real.cos_two_mul_eq_one_sub (β / 2)
    rw [hβ] at hr
    exact_mod_cast (show Real.cos β - 1 = -(2 * Real.sin (β / 2) ^ 2) by linarith)
  rw [jacobi_binomial_sum hα, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjr : j ≤ r := by simpa using hj
  have hap : (a : ℂ) + r - j + 1 = (↑(a + (r - j)) : ℂ) + 1 := by
    rw [Nat.cast_add, Nat.cast_sub hjr]
    ring
  have hbp : (b : ℂ) + j + 1 = (↑(b + j) : ℂ) + 1 := by push_cast; rfl
  have ha : a + (r - j) + j = r + a := by omega
  have hb : b + j + (r - j) = r + b := by omega
  rw [hap, hbp, pochhammer_nat_succ_eq_choose_mul_factorial,
    pochhammer_nat_succ_eq_choose_mul_factorial, ha, hb,
    mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr j.factorial_ne_zero),
    mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (r - j).factorial_ne_zero)]
  have hca : r + a - j = a + (r - j) := by omega
  have hcb : r + b - (r - j) = b + j := by omega
  rw [← hca, ← hcb, Nat.choose_symm (show j ≤ r + a by omega),
    Nat.choose_symm (show r - j ≤ r + b by omega), hc, hs, neg_pow, mul_pow, mul_pow,
    ← pow_mul, ← pow_mul]
  have hot : (2 : ℂ) ^ r = (2 : ℂ) ^ (r - j) * (2 : ℂ) ^ j := by
    rw [← pow_add, Nat.sub_add_cancel hjr]
  calc
    _ = ((2 : ℂ) ^ r)⁻¹ * (2 ^ (r - j) * 2 ^ j) *
          (((r + a).choose j : ℂ) * (r + b).choose (r - j) * (-1) ^ (r - j) *
            (Real.cos (β / 2) : ℂ) ^ (2 * j) *
              (Real.sin (β / 2) : ℂ) ^ (2 * (r - j))) := by ring
    _ = _ := by
      rw [← hot, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℂ) ≠ 0)), one_mul]

open DLMF.OrthogonalPolynomials in
/-- The iterated derivative of an equal-parameter Jacobi polynomial raises both parameters. -/
private theorem iteratedDeriv_jacobi_nat_diagonal (a l m : ℕ) (hm : m ≤ l) (z : ℂ) :
    iteratedDeriv m (jacobiPolynomialP a a l) z =
      ((l + 2 * a + m).factorial : ℂ) / ((2 : ℂ) ^ m * (l + 2 * a).factorial) *
        jacobiPolynomialP (a + m : ℕ) (a + m : ℕ) (l - m) z := by
  induction m generalizing z with
  | zero =>
    simp [div_self (Nat.cast_ne_zero.mpr (l + 2 * a).factorial_ne_zero :
      ((l + 2 * a).factorial : ℂ) ≠ 0)]
  | succ m ih =>
    rw [iteratedDeriv_succ, funext (ih (by omega)), deriv_const_mul_field]
    have hdegree : l - m = l - (m + 1) + 1 := by omega
    have hpos : -1 < ((a + m : ℕ) : ℂ).re := by
      rw [Complex.natCast_re]
      exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg (a + m))
    rw [hdegree, jacobi_derivative hpos]
    have hap : ((a + m : ℕ) : ℂ) + 1 = (↑(a + (m + 1)) : ℂ) := by push_cast; ring
    have hc : ((l - (m + 1) : ℕ) : ℂ) + (a + m : ℕ) + (a + m : ℕ) + 2 =
        (↑(l + 2 * a + m) : ℂ) + 1 := by
      rw [Nat.cast_sub (show m + 1 ≤ l by omega)]
      push_cast
      ring
    rw [hap, hc, show l + 2 * a + (m + 1) = (l + 2 * a + m) + 1 by omega,
      Nat.factorial_succ, pow_succ]
    push_cast
    ring

end WignerSmallD

/-- The diagonal weight phases multiply the real small `d`-function in Euler coordinates. -/
theorem matrixElement_euler (d : ℕ) (i k : Fin (d + 1)) (α β γ : ℝ) :
    matrixElement d i k (euler α β γ) =
      Complex.exp (Complex.I * (magneticWeight d i * α)) * wignerSmallD d i k β *
        Complex.exp (Complex.I * (magneticWeight d k * γ)) := by
  rw [euler_def, matrixElement_mul]
  simp only [WignerSmallD.matrixElement_torusExp, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [matrixElement_mul]
  simp only [WignerSmallD.matrixElement_torusExp, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, WignerSmallD.matrixElement_eulerMiddle]

namespace WignerSmallD

/-- The change of indices from the Wigner sum to the Jacobi sum permutes the four factorial
arguments of the normalization. -/
private theorem factorial_product_eq (d i k a b r : ℕ) (hi : i ≤ d) (hk : k ≤ d)
    (ha : a = (k - i) + (i - k)) (hb : b = (d - i - k) + (i + k - d))
    (hr : r = min (min i k) (min (d - i) (d - k))) :
    ((i.factorial : ℝ) * (d - i).factorial) * ((k.factorial : ℝ) * (d - k).factorial) =
      ((r.factorial : ℝ) * (d - r).factorial) *
        (((r + a).factorial : ℝ) * (r + b).factorial) := by
  rcases le_total i k with hik | hki <;> rcases le_total (i + k) d with hikd | hdik
  · have h₁ : r = i := by omega
    have h₂ : r + a = k := by omega
    have h₃ : r + b = d - k := by omega
    rw [h₂, h₃, h₁]
  · have h₁ : r = d - k := by omega
    have h₂ : r + a = d - i := by omega
    have h₃ : r + b = i := by omega
    rw [h₂, h₃, h₁, Nat.sub_sub_self hk]
    ring
  · have h₁ : r = k := by omega
    have h₂ : r + a = i := by omega
    have h₃ : r + b = d - i := by omega
    rw [h₂, h₃, h₁]
    ring
  · have h₁ : r = d - i := by omega
    have h₂ : r + a = d - k := by omega
    have h₃ : r + b = k := by omega
    rw [h₂, h₃, h₁, Nat.sub_sub_self hi]
    ring

end WignerSmallD

set_option maxHeartbeats 1000000 in
/-- The Jacobi form at all real angles, with degree `r` and parameters `a, b`
determined by the two magnetic weights. -/
theorem wignerSmallD_eq_jacobi (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) (β : ℝ) :
    let a := Int.natAbs ((i : ℤ) - k)
    let b := Int.natAbs ((d : ℤ) - i - k)
    let r := min (min i k) (min (d - i) (d - k))
    (wignerSmallD d i k β : ℂ) =
      ((-1 : ℝ) ^ (k - i) *
        Real.sqrt ((r.factorial * (d - r).factorial : ℕ) /
          ((r + a).factorial * (r + b).factorial : ℕ)) *
        Real.sin (β / 2) ^ a * Real.cos (β / 2) ^ b : ℝ) *
        DLMF.OrthogonalPolynomials.jacobiPolynomialP a b r (Real.cos β) := by
  dsimp only
  set a := Int.natAbs ((i : ℤ) - k) with haDef
  set b := Int.natAbs ((d : ℤ) - i - k) with hbDef
  set r := min (min i k) (min (d - i) (d - k)) with hrDef
  have ha : a = (k - i) + (i - k) := by
    rw [haDef]
    rcases le_total i k with h | h
    · rw [Int.natAbs_natCast_sub_natCast_of_le h, Nat.sub_eq_zero_of_le h, Nat.add_zero]
    · rw [Int.natAbs_natCast_sub_natCast_of_ge h, Nat.sub_eq_zero_of_le h, Nat.zero_add]
  have hb : b = (d - i - k) + (i + k - d) := by
    rw [hbDef, sub_sub, ← Int.natCast_add]
    rcases le_total d (i + k) with h | h
    · rw [Int.natAbs_natCast_sub_natCast_of_le h]
      omega
    · rw [Int.natAbs_natCast_sub_natCast_of_ge h]
      omega
  have hr : r = min (d - i) (d - k) - (d - i - k) := by omega
  let leftNorm : ℝ := (i.factorial : ℝ) * (d - i).factorial
  let rightNorm : ℝ := (k.factorial : ℝ) * (d - k).factorial
  let numerator : ℝ := (r.factorial : ℝ) * (d - r).factorial
  let denominator : ℝ := ((r + a).factorial : ℝ) * (r + b).factorial
  have hnorms : leftNorm * rightNorm = numerator * denominator :=
    WignerSmallD.factorial_product_eq d i k a b r hi hk ha hb hrDef
  have hnormalize : Real.sqrt (leftNorm / rightNorm) * rightNorm =
      Real.sqrt (numerator / denominator) * denominator := by
    rw [WignerSmallD.sqrt_div_mul_eq_sqrt_mul (by dsimp [leftNorm]; positivity)
      (by dsimp [rightNorm]; positivity),
      WignerSmallD.sqrt_div_mul_eq_sqrt_mul (by dsimp [numerator]; positivity)
      (by dsimp [denominator]; positivity), hnorms]
  simp only [wignerSmallD, ite_eq_left (show i ≤ d ∧ k ≤ d from ⟨hi, hk⟩),
    Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Nat.cast_mul]
  -- Keep precisely the indices where both binomial coefficients can contribute.
  let support := (Finset.range (d - i + 1)).filter fun s =>
    d - i - k ≤ s ∧ s ≤ d - k
  have hsubset : support ⊆ Finset.range (d - i + 1) := Finset.filter_subset _ _
  rw [← Finset.sum_subset hsubset (fun s hs hs' => by
    simp only [support, Finset.mem_filter, hs, true_and, not_and_or] at hs'
    rcases hs' with hlow | hhigh
    · have hzero := Nat.choose_eq_zero_of_lt (show k < d - i - s by omega)
      simp [hzero]
    · have hzero := Nat.choose_eq_zero_of_lt (show d - k < s by omega)
      simp [hzero])]
  rw [WignerSmallD.jacobiPolynomialP_nat_cos, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_nbij' (fun s => s - (d - i - k)) (fun j => j + (d - i - k))
  · intro s hs
    simp only [support, Finset.mem_filter, Finset.mem_range] at hs ⊢
    omega
  · intro j hj
    simp only [support, Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega
  · intro s hs
    simp only [support, Finset.mem_filter, Finset.mem_range] at hs
    omega
  · intro j _
    omega
  · intro s hs
    simp only [support, Finset.mem_filter, Finset.mem_range] at hs
    set j := s - (d - i - k) with hjDef
    have hj : j ≤ r := by omega
    have ht : d - i - s = (k - i) + (r - j) := by omega
    have h₁ : k - (d - i - s) = (i + k - d) + j := by omega
    have h₂ : s = (d - i - k) + j := by omega
    have h₃ : d - k - s = (i - k) + (r - j) := by omega
    have hcos : 2 * s + i + k - d = b + 2 * j := by omega
    have hsin : 2 * d - i - k - 2 * s = a + 2 * (r - j) := by omega
    have hba : r + a - j = a + (r - j) := by omega
    have hbb : r + b - (r - j) = b + j := by omega
    -- Pair the factorials by the excesses in the two complementary indices.
    have hfirst : (((k - i) + (r - j)).factorial : ℂ) *
          ((i - k) + (r - j)).factorial =
        ((r - j).factorial : ℂ) * (a + (r - j)).factorial := by
      rw [ha]
      rcases le_total i k with hh | hh
      · simp [Nat.sub_eq_zero_of_le hh, mul_comm]
      · simp [Nat.sub_eq_zero_of_le hh]
    have hsecond : (((i + k - d) + j).factorial : ℂ) *
          ((d - i - k) + j).factorial =
        (j.factorial : ℂ) * (b + j).factorial := by
      rw [hb]
      rcases le_total (i + k) d with hh | hh
      · have hzero : i + k - d = 0 := by omega
        simp [hzero]
      · have hzero : d - i - k = 0 := by omega
        simp [hzero, mul_comm]
    have hcoeff : (Real.sqrt (leftNorm / rightNorm) : ℂ) *
          (k.choose (d - i - s) : ℂ) * (d - k).choose s =
        (Real.sqrt (numerator / denominator) : ℂ) *
          ((r + a).choose j : ℂ) * (r + b).choose (r - j) := by
      rw [WignerSmallD.natCast_choose_eq_factorial_div k _ (by omega),
        WignerSmallD.natCast_choose_eq_factorial_div (d - k) _ (by omega),
        WignerSmallD.natCast_choose_eq_factorial_div (r + a) _ (by omega),
        WignerSmallD.natCast_choose_eq_factorial_div (r + b) _ (by omega), h₁, h₃, hba, hbb, ht]
      rw [congrArg Nat.factorial h₂]
      have hnormalize' : (Real.sqrt (leftNorm / rightNorm) : ℂ) *
            ((k.factorial : ℂ) * (d - k).factorial) =
          (Real.sqrt (numerator / denominator) : ℂ) *
            (((r + a).factorial : ℂ) * (r + b).factorial) := by
        simpa only [rightNorm, denominator, Complex.ofReal_mul, Complex.ofReal_natCast]
          using congrArg Complex.ofReal hnormalize
      calc
        _ = (Real.sqrt (leftNorm / rightNorm) : ℂ) *
            ((k.factorial : ℂ) * (d - k).factorial) /
            ((((k - i) + (r - j)).factorial : ℂ) * ((i - k) + (r - j)).factorial *
              ((((i + k - d) + j).factorial : ℂ) * ((d - i - k) + j).factorial)) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ = _ := by
          rw [hfirst, hsecond, hnormalize']
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
    have hsign : (-1 : ℂ) ^ (d - i - s) = (-1) ^ (k - i) * (-1) ^ (r - j) := by
      rw [ht, pow_add]
    rw [hcos, hsin, hsign, pow_add, pow_add]
    simp only [Complex.ofReal_natCast]
    calc
      _ = (Real.sqrt (leftNorm / rightNorm) : ℂ) *
          (k.choose (d - i - s) : ℂ) * (d - k).choose s *
          ((-1 : ℂ) ^ (k - i) * (-1) ^ (r - j) *
          ((Real.cos (β / 2) : ℂ) ^ b * (Real.cos (β / 2) : ℂ) ^ (2 * j)) *
          ((Real.sin (β / 2) : ℂ) ^ a * (Real.sin (β / 2) : ℂ) ^ (2 * (r - j)))) := by
        dsimp only [leftNorm, rightNorm]
        ring
      _ = _ := by
        rw [hcoeff]
        dsimp only [numerator, denominator]
        ring

/-- The zero-weight coefficient of integral spin is the Legendre polynomial of the cosine. -/
theorem wignerSmallD_two_mul_self (l : ℕ) (β : ℝ) :
    (wignerSmallD (2 * l) l l β : ℂ) =
      DLMF.OrthogonalPolynomials.legendrePolynomialP l (Real.cos β) := by
  have h := wignerSmallD_eq_jacobi (2 * l) l l (by omega) (by omega) β
  have hdiff : 2 * l - l = l := by omega
  have hint : (((2 * l : ℕ) : ℤ) - l - l) = 0 := by push_cast; ring
  have hfact : ((l.factorial * l.factorial : ℕ) : ℝ) ≠ 0 := by positivity
  rw [show DLMF.OrthogonalPolynomials.legendrePolynomialP l =
    DLMF.OrthogonalPolynomials.jacobiPolynomialP 0 0 l from rfl]
  dsimp only at h
  simpa only [sub_self, Nat.sub_self, hint, Int.natAbs_zero, hdiff, min_self, add_zero,
    div_self hfact, pow_zero, Real.sqrt_one, mul_one, one_mul, Complex.ofReal_one,
    Nat.cast_zero] using h

open DLMF.OrthogonalPolynomials in
/-- The column of weight zero in integral spin is given by the integer Ferrers function,
with the Condon–Shortley phase removed, on the polar-angle interval. -/
theorem wignerSmallD_eq_ferrers (l n : ℕ) (hn : n ≤ l) {β : ℝ} (hβ : β ∈ Set.Icc 0 π) :
    (wignerSmallD (2 * l) (l + n) l β : ℂ) =
      ((-1 : ℝ) ^ n * Real.sqrt ((l - n).factorial / (l + n).factorial) : ℝ) *
        DLMF.Legendre.ferrersPNat l n (Real.cos β) := by
  have h := wignerSmallD_eq_jacobi (2 * l) (l + n) l (by omega) (by omega) β
  have hleft : Int.natAbs (((l + n : ℕ) : ℤ) - l) = n := by
    rw [Nat.cast_add, add_sub_cancel_left, Int.natAbs_natCast]
  have hright : Int.natAbs (((2 * l : ℕ) : ℤ) - ↑(l + n : ℕ) - l) = n := by
    have he : (((2 * l : ℕ) : ℤ) - ↑(l + n : ℕ) - l) = -(n : ℤ) := by push_cast; ring
    rw [he, Int.natAbs_neg, Int.natAbs_natCast]
  have hmin : min (min (l + n) l) (min (2 * l - (l + n)) (2 * l - l)) = l - n := by omega
  have hdif : 2 * l - (l - n) = l + n := by omega
  have hadd : l - n + n = l := by omega
  have hzero : l - (l + n) = 0 := by omega
  dsimp only at h
  rw [hleft, hright, hmin, hdif, hadd, hzero, pow_zero, one_mul] at h
  rw [h, DLMF.Legendre.ferrersPNat]
  have hderivative : iteratedDeriv n (legendrePolynomialP l) (Real.cos β) =
      ((l + n).factorial : ℂ) / ((2 : ℂ) ^ n * l.factorial) *
        jacobiPolynomialP n n (l - n) (Real.cos β) := by
    rw [show legendrePolynomialP l = jacobiPolynomialP 0 0 l from rfl]
    simpa only [Nat.cast_zero, zero_add, mul_zero, add_zero] using
      WignerSmallD.iteratedDeriv_jacobi_nat_diagonal 0 l n hn (Real.cos β)
  rw [hderivative]
  have hsin : Real.sqrt (1 - Real.cos β ^ 2) = Real.sin β := by
    rw [← Real.sin_sq, Real.sqrt_sq (Real.sin_nonneg_of_mem_Icc hβ)]
  have hhalf : Real.sin β = 2 * Real.sin (β / 2) * Real.cos (β / 2) := by
    rw [← Real.sin_two_mul]
    congr 1
    ring
  have hphase : (-1 : ℂ) ^ (n * 2) = 1 := by
    rw [mul_comm n 2, pow_mul]
    norm_num
  have hroot : Real.sqrt (((l - n).factorial * (l + n).factorial : ℕ) /
      ((l.factorial * l.factorial : ℕ) : ℝ)) =
        Real.sqrt ((l - n).factorial / (l + n).factorial) * (l + n).factorial /
          l.factorial := by
    rw [Nat.cast_mul, Nat.cast_mul, Real.sqrt_div (by positivity), ← pow_two,
      Real.sqrt_sq (by positivity), WignerSmallD.sqrt_div_mul_eq_sqrt_mul
        (by positivity : (0 : ℝ) ≤ (l - n).factorial)
        (by positivity : (0 : ℝ) < (l + n).factorial)]
  simp only [hsin, hhalf, hroot,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_neg, Complex.ofReal_one]
  simp only [Complex.ofReal_ofNat, mul_pow]
  have htwo' : ((2 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfact : (l.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr l.factorial_ne_zero
  field_simp
  ring_nf
  rw [hphase, mul_one]

end SFVK.SU2
