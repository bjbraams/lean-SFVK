/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.ClebschGordan.Basic.Coefficients
public import DLMF.WignerSymbols.Basic.Definitions
public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import DLMF.WignerSymbols.LegendreProducts
import DLMF.WignerSymbols.ThreeJ
import SFVK.ClebschGordan.Coefficients

/-!
# The 3-j symbol

Layer 3 of the roadmap ClebschGordan: symmetries, orthogonality, special values and the
Legendre product formulas. Locators: Edmonds, *Angular Momentum in Quantum Mechanics*,
(3.7.3)–(3.7.6), pp. 46–47; (3.7.7)–(3.7.8), p. 47; (3.7.14), p. 49; (3.7.17), p. 50;
(4.6.4), p. 63; DLMF 34.1.1, 34.3.1, 34.3.5, 34.3.8–34.3.10, 34.3.16–34.3.17, 34.3.19, 34.3.21.
The Legendre polynomial is lean-DLMF's `DLMF.OrthogonalPolynomials.legendrePolynomialP`.
The rational-spin comparison transports lean-DLMF's Wigner symmetries, special values, and
Legendre product identities to the natural-index encoding.
-/

public noncomputable section

namespace SFVK.ClebschGordan

/-! ### Comparison with lean-DLMF -/

open DLMF.WignerSymbols hiding IsTriad clebschGordan

open RationalSpins in
/-- **Conversion to lean-DLMF's rational-spin 3-j symbol** (DLMF 34.1.1, 34.2.4): for indices in
range, `threeJ d₁ d₂ d₃ i₁ i₂ i₃` is `DLMF.WignerSymbols.wigner3j j₁ j₂ j₃ m₁ m₂ m₃` with
`j_r = d_r/2` and `m_r = i_r - d_r/2`. -/
theorem threeJ_eq_wigner3j {d₁ d₂ d₃ i₁ i₂ i₃ : ℕ} (h₁ : i₁ ≤ d₁) (h₂ : i₂ ≤ d₂)
    (h₃ : i₃ ≤ d₃) :
    threeJ d₁ d₂ d₃ i₁ i₂ i₃ =
      DLMF.WignerSymbols.wigner3j ((d₁ : ℚ) / 2) ((d₂ : ℚ) / 2) ((d₃ : ℚ) / 2)
        ((i₁ : ℚ) - (d₁ : ℚ) / 2) ((i₂ : ℚ) - (d₂ : ℚ) / 2) ((i₃ : ℚ) - (d₃ : ℚ) / 2) := by
  rw [threeJ_def, ite_eq_left h₃]
  by_cases ht : IsTriad d₁ d₂ d₃
  · rw [clebschGordan_eq_dlmf h₁ h₂ (Nat.sub_le _ _), ← negate_projection h₃,
      DLMF.WignerSymbols.clebschGordan, neg_neg, ← sub_eq_add_neg, two_mul_natCast_half]
    let phase : ℚ := (d₁ : ℚ) / 2 - (d₂ : ℚ) / 2 - ((i₃ : ℚ) - (d₃ : ℚ) / 2)
    have heq : phase + ((2 * d₃ : ℕ) : ℤ) =
        ((((d₁ + d₃ - d₂) / 2 + 2 * d₃ - i₃) : ℕ) : ℚ) := by
      dsimp only [phase]
      rw [Nat.cast_sub (by omega), Nat.cast_add, ← half_sum_sub_right ht]
      push_cast
      ring
    have hpow : signPow phase = (-1 : ℝ) ^ ((d₁ + d₃ - d₂) / 2 + 2 * d₃ - i₃) := by
      rw [← DLMF.WignerSymbols.signPow_natCast, ← heq, signPow_add_intCast, zpow_natCast, pow_mul]
      norm_num
    have hr := Real.sqrt_pos.2 (by positivity : 0 < (d₃ : ℝ) + 1)
    rw [← hpow]
    have hcancel (x : ℝ) :
        signPow phase / Real.sqrt ((d₃ : ℝ) + 1) *
          (signPow phase * Real.sqrt ((d₃ : ℝ) + 1) * x) = x := by
      calc
        _ = (signPow phase * signPow phase) *
            (Real.sqrt ((d₃ : ℝ) + 1) / Real.sqrt ((d₃ : ℝ) + 1)) * x := by ring
        _ = x := by rw [signPow_sq, div_self hr.ne', mul_one, one_mul]
    exact hcancel _
  · rw [clebschGordan_eq_zero_of_not_isTriad ht, mul_zero,
      wigner3j_of_not fun h => ht ((RationalSpins.isTriad_iff d₁ d₂ d₃).mp h.1)]

/-- Any out-of-range index makes the natural-spin 3-j symbol vanish. -/
private theorem threeJ_eq_zero_of_out_of_range {d₁ d₂ d₃ i₁ i₂ i₃ : ℕ}
    (h : ¬ (i₁ ≤ d₁ ∧ i₂ ≤ d₂ ∧ i₃ ≤ d₃)) : threeJ d₁ d₂ d₃ i₁ i₂ i₃ = 0 := by
  rw [threeJ_def]
  split_ifs with h₃ <;> try rfl
  rw [clebschGordan_def]
  have hn : ¬ (IsTriad d₁ d₂ d₃ ∧ i₁ ≤ d₁ ∧ i₂ ≤ d₂ ∧ d₃ - i₃ ≤ d₃ ∧
      2 * (d₃ - i₃) + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d₃) :=
    fun hh => h ⟨hh.2.1, hh.2.2.1, h₃⟩
  rw [ite_eq_right hn, mul_zero]

/-- For integral spins, the middle indices are the zero projections. -/
private theorem threeJ_even_degrees (l₁ l₂ l₃ : ℕ) :
    threeJ (2 * l₁) (2 * l₂) (2 * l₃) l₁ l₂ l₃ = wigner3j l₁ l₂ l₃ 0 0 0 := by
  rw [threeJ_eq_wigner3j (by omega) (by omega) (by omega)]
  have hh (l : ℕ) : ((2 * l : ℕ) : ℚ) / 2 = l := by
    push_cast
    ring
  simp only [hh, sub_self]

/-! ### Symmetries -/

/-- **Even permutations** (Edmonds (3.7.4), p. 46; DLMF 34.3.8). -/
theorem threeJ_cycle (d₁ d₂ d₃ i₁ i₂ i₃ : ℕ) :
    threeJ d₁ d₂ d₃ i₁ i₂ i₃ = threeJ d₂ d₃ d₁ i₂ i₃ i₁ := by
  by_cases hr : i₁ ≤ d₁ ∧ i₂ ≤ d₂ ∧ i₃ ≤ d₃
  · rw [threeJ_eq_wigner3j hr.1 hr.2.1 hr.2.2, threeJ_eq_wigner3j hr.2.1 hr.2.2 hr.1,
      wigner3j_cycle]
  · rw [threeJ_eq_zero_of_out_of_range hr,
      threeJ_eq_zero_of_out_of_range (fun h => hr ⟨h.2.2, h.1, h.2.1⟩)]

/-- **Odd permutations** (Edmonds (3.7.5), p. 47; DLMF 34.3.9): a factor `(-1)^{j₁ + j₂ + j₃}`.
-/
theorem threeJ_swap {d₁ d₂ d₃ : ℕ} (h : Even (d₁ + d₂ + d₃)) (i₁ i₂ i₃ : ℕ) :
    threeJ d₁ d₂ d₃ i₁ i₂ i₃ = (-1) ^ ((d₁ + d₂ + d₃) / 2) * threeJ d₂ d₁ d₃ i₂ i₁ i₃ := by
  by_cases hr : i₁ ≤ d₁ ∧ i₂ ≤ d₂ ∧ i₃ ≤ d₃
  · rw [threeJ_eq_wigner3j hr.1 hr.2.1 hr.2.2, threeJ_eq_wigner3j hr.2.1 hr.1 hr.2.2,
      wigner3j_swap, RationalSpins.half_sum_natCast h, signPow_natCast]
  · rw [threeJ_eq_zero_of_out_of_range hr,
      threeJ_eq_zero_of_out_of_range (fun h => hr ⟨h.2.1, h.1, h.2.2⟩), mul_zero]

/-- **Reversal of the magnetic quantum numbers** (Edmonds (3.7.6), p. 47; DLMF 34.3.10). -/
theorem threeJ_reflect {d₁ d₂ d₃ i₁ i₂ i₃ : ℕ} (h : Even (d₁ + d₂ + d₃)) (h₁ : i₁ ≤ d₁)
    (h₂ : i₂ ≤ d₂) (h₃ : i₃ ≤ d₃) :
    threeJ d₁ d₂ d₃ i₁ i₂ i₃ =
      (-1) ^ ((d₁ + d₂ + d₃) / 2) * threeJ d₁ d₂ d₃ (d₁ - i₁) (d₂ - i₂) (d₃ - i₃) := by
  rw [threeJ_eq_wigner3j h₁ h₂ h₃,
    threeJ_eq_wigner3j (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _),
    ← RationalSpins.negate_projection h₁, ← RationalSpins.negate_projection h₂,
    ← RationalSpins.negate_projection h₃, wigner3j_neg,
    RationalSpins.half_sum_natCast h, signPow_natCast]

/-! ### Orthogonality -/

/-- **Orthogonality in `(j₃, m₃)`** (Edmonds (3.7.7), p. 47; DLMF 34.3.16). -/
theorem sum_threeJ_mul_threeJ {d₁ d₂ d₃ d₃' i₃ i₃' : ℕ} (h₃ : i₃ ≤ d₃) (h₃' : i₃' ≤ d₃') :
    ((d₃ + 1 : ℕ) : ℝ) * ∑ i₁ ∈ Finset.range (d₁ + 1), ∑ i₂ ∈ Finset.range (d₂ + 1),
        threeJ d₁ d₂ d₃ i₁ i₂ i₃ * threeJ d₁ d₂ d₃' i₁ i₂ i₃' =
      if d₃ = d₃' ∧ i₃ = i₃' ∧ IsTriad d₁ d₂ d₃ then 1 else 0 := by
  sorry

/-- **Orthogonality in `(m₁, m₂)`** (Edmonds (3.7.8), p. 47; DLMF 34.3.17). -/
theorem sum_threeJ_mul_threeJ_right {d₁ d₂ i₁ i₂ i₁' i₂' : ℕ} (h₁ : i₁ ≤ d₁) (h₂ : i₂ ≤ d₂)
    (h₁' : i₁' ≤ d₁) (h₂' : i₂' ≤ d₂) :
    ∑ d₃ ∈ Finset.range (d₁ + d₂ + 1), ∑ i₃ ∈ Finset.range (d₃ + 1),
        ((d₃ + 1 : ℕ) : ℝ) * threeJ d₁ d₂ d₃ i₁ i₂ i₃ * threeJ d₁ d₂ d₃ i₁' i₂' i₃ =
      if i₁ = i₁' ∧ i₂ = i₂' then 1 else 0 := by
  sorry

/-! ### Special values -/

/-- **Spin zero** (DLMF 34.3.1): `(j j 0; m -m 0) = (-1)^{j - m}/√(2j + 1)`. -/
theorem threeJ_spin_zero {d i : ℕ} (h : i ≤ d) :
    threeJ d d 0 i (d - i) 0 = (-1) ^ (d - i) / Real.sqrt (d + 1) := by
  rw [threeJ_eq_wigner3j h (Nat.sub_le _ _) (by omega), Nat.cast_zero, zero_div, sub_zero,
    ← RationalSpins.negate_projection h, wigner3j_j_j_zero (RationalSpins.isProjection h),
    RationalSpins.two_mul_natCast_half]
  have hp : (d : ℚ) / 2 - ((i : ℚ) - (d : ℚ) / 2) = ((d - i : ℕ) : ℚ) := by
    rw [Nat.cast_sub h]
    ring
  rw [hp, signPow_natCast]

/-- **Vanishing magnetic numbers, odd sum** (Edmonds (3.7.14), p. 49; DLMF 34.3.5). -/
theorem threeJ_zero_zero_zero_of_odd {l₁ l₂ l₃ : ℕ} (h : Odd (l₁ + l₂ + l₃)) :
    threeJ (2 * l₁) (2 * l₂) (2 * l₃) l₁ l₂ l₃ = 0 := by
  obtain ⟨n, hn⟩ := h
  rw [threeJ_even_degrees]
  exact wigner3j_zero_zero_zero_of_odd n (by exact_mod_cast hn)

/-- **Vanishing magnetic numbers, even sum** (Edmonds (3.7.17), p. 50; DLMF 34.3.5). -/
theorem threeJ_zero_zero_zero_of_even {l₁ l₂ l₃ g : ℕ} (h : IsTriad (2 * l₁) (2 * l₂) (2 * l₃))
    (hg : l₁ + l₂ + l₃ = 2 * g) :
    threeJ (2 * l₁) (2 * l₂) (2 * l₃) l₁ l₂ l₃ =
      (-1) ^ g * Real.sqrt ((((2 * g - 2 * l₁).factorial * (2 * g - 2 * l₂).factorial *
          (2 * g - 2 * l₃).factorial : ℕ) : ℝ) / ((2 * g + 1).factorial : ℕ)) *
        (g.factorial / ((g - l₁).factorial * (g - l₂).factorial * (g - l₃).factorial : ℕ)) := by
  rw [threeJ_even_degrees]
  have hspin (k : ℕ) : ((2 * k : ℕ) : ℚ) / 2 = k := by
    push_cast
    ring
  have htri := (RationalSpins.isTriad_iff (2 * l₁) (2 * l₂) (2 * l₃)).mpr h
  simp only [hspin] at htri
  rw [wigner3j_zero_zero_zero_of_even htri (isNatQ_natCast l₁) (isNatQ_natCast l₂)
    (isNatQ_natCast l₃) g (by exact_mod_cast hg)]
  have h₁ : l₁ ≤ g := by have := h.2.1; omega
  have h₂ : l₂ ≤ g := by have := h.2.2.1; omega
  have h₃ : l₃ ≤ g := by have := h.1; omega
  have hr (k : ℕ) (hk : k ≤ g) : (2 * (g : ℚ) - 2 * k) = ((2 * g - 2 * k : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_mul]
    norm_num
  rw [ratFactorial_of_eq (hr l₁ h₁), ratFactorial_of_eq (hr l₂ h₂), ratFactorial_of_eq (hr l₃ h₃),
    ratFactorial_of_eq (n := 2 * g + 1) (by push_cast; ring),
    ratFactorial_of_eq (Nat.cast_sub h₁).symm, ratFactorial_of_eq (Nat.cast_sub h₂).symm,
    ratFactorial_of_eq (Nat.cast_sub h₃).symm]
  push_cast
  rfl

/-! ### Legendre polynomials -/

/-- **Linearization of products of Legendre polynomials** (DLMF 34.3.19). -/
theorem legendrePolynomialP_mul_legendrePolynomialP (l₁ l₂ : ℕ) (x : ℂ) :
    DLMF.OrthogonalPolynomials.legendrePolynomialP l₁ x *
        DLMF.OrthogonalPolynomials.legendrePolynomialP l₂ x =
      ∑ l ∈ Finset.range (l₁ + l₂ + 1),
        (((2 * l + 1 : ℝ) * threeJ (2 * l₁) (2 * l₂) (2 * l) l₁ l₂ l ^ 2 : ℝ) : ℂ) *
          DLMF.OrthogonalPolynomials.legendrePolynomialP l x := by
  simp_rw [threeJ_even_degrees]
  exact DLMF.WignerSymbols.LegendreProducts.linearization l₁ l₂ x

/-- **The integral of three Legendre polynomials** (Edmonds (4.6.4), p. 63; DLMF 34.3.21, in the
variable `x = cos θ`). -/
theorem integral_legendrePolynomialP_mul_mul (l₁ l₂ l₃ : ℕ) :
    ∫ x in (-1 : ℝ)..1, DLMF.OrthogonalPolynomials.legendrePolynomialP l₁ x *
        DLMF.OrthogonalPolynomials.legendrePolynomialP l₂ x *
        DLMF.OrthogonalPolynomials.legendrePolynomialP l₃ x =
      ((2 * threeJ (2 * l₁) (2 * l₂) (2 * l₃) l₁ l₂ l₃ ^ 2 : ℝ) : ℂ) := by
  rw [threeJ_even_degrees]
  exact DLMF.WignerSymbols.LegendreProducts.triple_integral l₁ l₂ l₃

end SFVK.ClebschGordan
