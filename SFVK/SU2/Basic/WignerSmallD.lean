/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Wigner's small `d`-functions

Edmonds's finite binomial sum for `d^j_{m'm}(β)`, *Angular Momentum in Quantum Mechanics*,
(4.1.15), p. 57, with `d = 2j`, row index `i` and column index `k` of magnetic weights
`i - d/2` and `k - d/2`. The function is total in `β` and zero for an index beyond `d`.
-/

public noncomputable section

open scoped Real

namespace SFVK.SU2

/-- Edmonds's finite binomial sum for the small `d`-function of spin `d/2`.
The totalized value for an index beyond `d` is zero. -/
@[expose]
def wignerSmallD (d i k : ℕ) (β : ℝ) : ℝ :=
  if i ≤ d ∧ k ≤ d then
    Real.sqrt ((i.factorial * (d - i).factorial : ℕ) / (k.factorial * (d - k).factorial : ℕ)) *
      ∑ s ∈ Finset.range (d - i + 1),
        ((k.choose (d - i - s) * (d - k).choose s : ℕ) : ℝ) * (-1) ^ (d - i - s) *
          Real.cos (β / 2) ^ (2 * s + i + k - d) * Real.sin (β / 2) ^ (2 * d - i - k - 2 * s)
  else 0

/-- The small `d`-function is zero when either weight index is out of range. -/
theorem wignerSmallD_eq_zero_of_out_of_range {d i k : ℕ} (h : d < i ∨ d < k) (β : ℝ) :
    wignerSmallD d i k β = 0 := by
  rcases h with h | h
  · simp [wignerSmallD, not_le.mpr h]
  · simp [wignerSmallD, not_le.mpr h]

/-- At spin zero the small `d`-function is constant. -/
@[simp]
theorem wignerSmallD_zero_zero_zero (β : ℝ) : wignerSmallD 0 0 0 β = 1 := by
  norm_num [wignerSmallD, Finset.sum_range_succ]

/-- The top-right entry of the spin one half middle factor is `sin (β/2)`. -/
theorem wignerSmallD_one_one_zero (β : ℝ) : wignerSmallD 1 1 0 β = Real.sin (β / 2) := by
  norm_num [wignerSmallD, Finset.sum_range_succ, Nat.factorial]

/-- The bottom-left entry of the spin one half middle factor is `-sin (β/2)`. -/
theorem wignerSmallD_one_zero_one (β : ℝ) : wignerSmallD 1 0 1 β = -Real.sin (β / 2) := by
  norm_num [wignerSmallD, Finset.sum_range_succ, Nat.factorial, Nat.choose]

/-- The zero-weight entry of spin one is the cosine of the middle angle. -/
theorem wignerSmallD_two_one_one (β : ℝ) : wignerSmallD 2 1 1 β = Real.cos β := by
  have h := Real.cos_two_mul' (β / 2)
  have hβ : 2 * (β / 2) = β := by ring
  rw [hβ] at h
  rw [h]
  norm_num [wignerSmallD, Finset.sum_range_succ, Nat.factorial, Nat.choose]
  ring

/-- At angle zero the small `d`-matrix is the identity. -/
theorem wignerSmallD_zero (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) :
    wignerSmallD d i k 0 = if i = k then 1 else 0 := by
  simp only [wignerSmallD, ite_eq_left (show i ≤ d ∧ k ≤ d from ⟨hi, hk⟩), zero_div,
    Real.cos_zero, Real.sin_zero, one_pow, mul_one]
  split_ifs with heq
  · subst k
    rw [Finset.sum_eq_single (d - i)]
    · rw [Nat.sub_self]
      have hp : 2 * d - i - i - 2 * (d - i) = 0 := by omega
      rw [hp]
      simp [div_self (by positivity : (i.factorial : ℝ) * (d - i).factorial ≠ 0)]
    · intro s hs hne
      have hsd := Finset.mem_range.mp hs
      have he : 2 * d - i - i - 2 * s ≠ 0 := by omega
      simp [zero_pow he]
    · simp
  · rw [Finset.sum_eq_zero]
    · rw [mul_zero]
    · intro s hs
      have hsd := Finset.mem_range.mp hs
      by_cases hs' : d - k < s
      · simp [Nat.choose_eq_zero_of_lt hs']
      by_cases ht : k < d - i - s
      · simp [Nat.choose_eq_zero_of_lt ht]
      have he : 2 * d - i - k - 2 * s ≠ 0 := by omega
      simp [zero_pow he]

/-- At angle `π` the small `d`-matrix is the signed reversal. -/
theorem wignerSmallD_pi (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) :
    wignerSmallD d i k π = if i + k = d then (-1) ^ k else 0 := by
  simp only [wignerSmallD, ite_eq_left (show i ≤ d ∧ k ≤ d from ⟨hi, hk⟩),
    Real.cos_pi_div_two, Real.sin_pi_div_two,
    one_pow, mul_one]
  split_ifs with heq
  · rw [Finset.sum_eq_single 0]
    · have hi' : d - i = k := by omega
      have hk' : d - k = i := by omega
      simp [hi', hk', heq, mul_comm, div_self (by positivity :
        (i.factorial : ℝ) * k.factorial ≠ 0)]
    · intro s _ hne
      have hp : 2 * s + i + k - d ≠ 0 := by omega
      simp [zero_pow hp]
    · simp
  · rw [Finset.sum_eq_zero]
    · rw [mul_zero]
    · intro s hs
      have hsd := Finset.mem_range.mp hs
      by_cases ht : k < d - i - s
      · simp [Nat.choose_eq_zero_of_lt ht]
      have he : 2 * s + i + k - d ≠ 0 := by omega
      simp [zero_pow he]

end SFVK.SU2
