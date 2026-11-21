/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.ClebschGordan.Basic.SixJ
public import DLMF.WignerSymbols.Basic.Definitions
import DLMF.WignerSymbols.SixJ
import SFVK.ClebschGordan.Coefficients

/-!
# Recoupling and the 6-j symbol

Layer 5 of the roadmap ClebschGordan. Locators: Edmonds, *Angular Momentum in Quantum
Mechanics*, (6.1.4), p. 91; (6.1.5), p. 92; (6.2.4), p. 94; (6.2.5) and (6.2.8), p. 95;
(6.2.9) and (6.2.11), p. 96; (6.2.12), p. 97; (6.3.2), p. 98; (6.3.7), p. 99. DLMF 34.4.1,
34.4.2, 34.5.1, 34.5.8, 34.5.14–34.5.16, 34.5.23. Spins are doubled throughout.
The normalization bridge permits the use of lean-DLMF's Wigner symmetries and zero-spin value.
-/

public noncomputable section

namespace SFVK.ClebschGordan

/-! ### Comparison with lean-DLMF -/

namespace RationalSpins

open DLMF.WignerSymbols hiding IsTriad

/-- Two triples sharing their last entry give an even sum of the four remaining entries. -/
private theorem even_quadruple {a b c d e : ℕ}
    (h₁ : IsTriad a b c) (h₂ : IsTriad d e c) : Even (a + b + d + e) := by
  obtain ⟨n, hn⟩ := h₁.2.2.2
  obtain ⟨m, hm⟩ := h₂.2.2.2
  exact ⟨n + m - c, by omega⟩

/-- The half-sum of four doubled spins agrees with natural-number division when it is integral. -/
private theorem half_quadruple_natCast {a b c d : ℕ} (h : Even (a + b + c + d)) :
    (a : ℚ) / 2 + (b : ℚ) / 2 + (c : ℚ) / 2 + (d : ℚ) / 2 =
      (((a + b + c + d) / 2 : ℕ) : ℚ) := by
  rw [← half_natCast h]
  push_cast
  ring

/-- The lower cutoffs of the two summands are the half-sums of their four triples. -/
private theorem ratInvFactorial_sub_half_sum (a b c z : ℕ)
    (h : Even (a + b + c)) :
    ratInvFactorial ((z : ℚ) - (a : ℚ) / 2 - (b : ℚ) / 2 - (c : ℚ) / 2) =
      if (a + b + c) / 2 ≤ z then ((z - (a + b + c) / 2).factorial : ℝ)⁻¹ else 0 := by
  have heq : (z : ℚ) - (a : ℚ) / 2 - (b : ℚ) / 2 - (c : ℚ) / 2 =
      (z : ℚ) - ((a : ℚ) / 2 + (b : ℚ) / 2 + (c : ℚ) / 2) := by ring
  rw [heq, half_sum_natCast h, ratInvFactorial_natCast_sub]

/-- Racah's summand in the doubled-spin encoding agrees with the rational-spin summand within
the natural summation range. -/
private theorem sixJTerm_eq_racahTerm6j {a b c d e f z : ℕ}
    (habc : IsTriad a b c) (haef : IsTriad a e f) (hdbf : IsTriad d b f) (hdec : IsTriad d e c)
    (hz : z ≤ (a + b + d + e) / 2) :
    sixJTerm a b c d e f z = racahTerm6j ((a : ℚ) / 2) ((b : ℚ) / 2) ((c : ℚ) / 2)
      ((d : ℚ) / 2) ((e : ℚ) / 2) ((f : ℚ) / 2) z := by
  rw [sixJTerm, racahTerm6j, ratInvFactorial_sub_half_sum _ _ _ _ habc.2.2.2,
    ratInvFactorial_sub_half_sum _ _ _ _ haef.2.2.2,
    ratInvFactorial_sub_half_sum _ _ _ _ hdbf.2.2.2,
    ratInvFactorial_sub_half_sum _ _ _ _ hdec.2.2.2,
    half_quadruple_natCast (even_quadruple habc hdec)]
  have heven₁ : Even (b + c + e + f) := by
    have h₁ := habc.2.2.2
    have h₂ := haef.2.2.2
    obtain ⟨n, hn⟩ := h₁
    obtain ⟨m, hm⟩ := h₂
    exact ⟨n + m - a, by omega⟩
  have heven₂ : Even (c + a + f + d) := by
    obtain ⟨n, hn⟩ := habc.2.2.2
    obtain ⟨m, hm⟩ := hdbf.2.2.2
    exact ⟨n + m - b, by omega⟩
  rw [half_quadruple_natCast heven₁, half_quadruple_natCast heven₂,
    ratInvFactorial_natCast_sub, ratInvFactorial_natCast_sub, ratInvFactorial_natCast_sub,
    ite_eq_left hz]
  by_cases h : (a + b + c) / 2 ≤ z ∧ (a + e + f) / 2 ≤ z ∧ (d + b + f) / 2 ≤ z ∧
      (d + e + c) / 2 ≤ z ∧ z ≤ (b + c + e + f) / 2 ∧ z ≤ (c + a + f + d) / 2
  · simp only [ite_eq_left h, ite_eq_left h.1, ite_eq_left h.2.1, ite_eq_left h.2.2.1,
      ite_eq_left h.2.2.2.1, ite_eq_left h.2.2.2.2.1, ite_eq_left h.2.2.2.2.2, Nat.cast_mul,
      div_eq_mul_inv, mul_inv_rev]
    ring
  · rw [ite_eq_right h]
    have hn : ¬ (a + b + c) / 2 ≤ z ∨ ¬ (a + e + f) / 2 ≤ z ∨ ¬ (d + b + f) / 2 ≤ z ∨
        ¬ (d + e + c) / 2 ≤ z ∨ ¬ z ≤ (b + c + e + f) / 2 ∨ ¬ z ≤ (c + a + f + d) / 2 := by
      tauto
    rcases hn with hn | hn | hn | hn | hn | hn <;> simp only [hn, ↓reduceIte, zero_mul, mul_zero]

end RationalSpins

open RationalSpins in
open DLMF.WignerSymbols hiding IsTriad in
/-- **Conversion to lean-DLMF's rational-spin 6-j symbol** (DLMF 34.4.2). -/
theorem sixJ_eq_wigner6j (a b c d e f : ℕ) :
    sixJ a b c d e f =
      DLMF.WignerSymbols.wigner6j ((a : ℚ) / 2) ((b : ℚ) / 2) ((c : ℚ) / 2) ((d : ℚ) / 2)
        ((e : ℚ) / 2) ((f : ℚ) / 2) := by
  have h : IsAdmissible6j ((a : ℚ) / 2) ((b : ℚ) / 2) ((c : ℚ) / 2) ((d : ℚ) / 2)
      ((e : ℚ) / 2) ((f : ℚ) / 2) ↔
      IsTriad a b c ∧ IsTriad a e f ∧ IsTriad d b f ∧ IsTriad d e c := by
    simp only [IsAdmissible6j, RationalSpins.isTriad_iff]
  by_cases hi : IsTriad a b c ∧ IsTriad a e f ∧ IsTriad d b f ∧ IsTriad d e c
  · obtain ⟨habc, haef, hdbf, hdec⟩ := hi
    rw [sixJ, ite_eq_left ⟨habc, haef, hdbf, hdec⟩, wigner6j,
      ite_eq_left (h.mpr ⟨habc, haef, hdbf, hdec⟩),
      triangleCoefficient_eq_triangleDelta habc, triangleCoefficient_eq_triangleDelta haef,
      triangleCoefficient_eq_triangleDelta hdbf, triangleCoefficient_eq_triangleDelta hdec,
      half_quadruple_natCast (even_quadruple habc hdec), Int.floor_natCast, Int.toNat_natCast]
    congr 1
    exact Finset.sum_congr rfl fun z hz =>
      sixJTerm_eq_racahTerm6j habc haef hdbf hdec (by simpa using hz)
  · rw [sixJ_eq_zero_of_not hi, wigner6j_of_not (mt h.mp hi)]

/-! ### Recoupling -/

/-- **The recoupling theorem** (Edmonds (6.1.5), p. 92): for admissible couplings and every `M`,
`((j₁ j₂) j₁₂, j₃; J | j₁, (j₂ j₃) j₂₃; J) = (-1)^{j₁+j₂+j₃+J} √((2j₁₂+1)(2j₂₃+1))
{j₁ j₂ j₁₂; j₃ J j₂₃}`. -/
theorem recouplingCoefficient_eq_sixJ {d₁ d₂ d₃ d₁₂ d₂₃ D I : ℕ} (h₁₂ : IsTriad d₁ d₂ d₁₂)
    (h₁₂₃ : IsTriad d₁₂ d₃ D) (h₂₃ : IsTriad d₂ d₃ d₂₃) (h₁₂₃' : IsTriad d₁ d₂₃ D)
    (hI : I ≤ D) :
    recouplingCoefficient d₁ d₂ d₃ d₁₂ d₂₃ D I =
      (-1) ^ ((d₁ + d₂ + d₃ + D) / 2) * Real.sqrt ((d₁₂ + 1) * (d₂₃ + 1)) *
        sixJ d₁ d₂ d₁₂ d₃ D d₂₃ := by
  sorry

/-- **The 6-j symbol from four 3-j symbols** (DLMF 34.4.1), with `m_r = i_r - j_r`,
`m'_r = k_r - l_r` and the sign `(-1)^{Σ (l_r + m'_r)} = (-1)^{k₁ + k₂ + k₃}`. -/
theorem sixJ_eq_sum_threeJ (a b c d e f : ℕ) :
    sixJ a b c d e f =
      ∑ i₁ ∈ Finset.range (a + 1), ∑ i₂ ∈ Finset.range (b + 1), ∑ i₃ ∈ Finset.range (c + 1),
        ∑ k₁ ∈ Finset.range (d + 1), ∑ k₂ ∈ Finset.range (e + 1), ∑ k₃ ∈ Finset.range (f + 1),
          (-1) ^ (k₁ + k₂ + k₃) * threeJ a b c i₁ i₂ i₃ * threeJ a e f i₁ k₂ (f - k₃) *
            threeJ d b f (d - k₁) i₂ k₃ * threeJ d e c k₁ (e - k₂) i₃ := by
  sorry

/-- **A 3-j symbol times a 6-j symbol** (Edmonds (6.2.8), p. 95; DLMF 34.5.23). -/
theorem threeJ_mul_sixJ (a b c d e f i₁ i₂ i₃ : ℕ) :
    threeJ a b c i₁ i₂ i₃ * sixJ a b c d e f =
      ∑ k₁ ∈ Finset.range (d + 1), ∑ k₂ ∈ Finset.range (e + 1), ∑ k₃ ∈ Finset.range (f + 1),
        (-1) ^ (k₁ + k₂ + k₃) * threeJ a e f i₁ k₂ (f - k₃) * threeJ d b f (d - k₁) i₂ k₃ *
          threeJ d e c k₁ (e - k₂) i₃ := by
  sorry

/-! ### Symmetries -/

/-- **Exchange of two columns** (Edmonds (6.2.4), p. 94; DLMF 34.5.8). -/
theorem sixJ_swap_columns (a b c d e f : ℕ) : sixJ a b c d e f = sixJ b a c e d f := by
  simpa only [sixJ_eq_wigner6j] using
    DLMF.WignerSymbols.wigner6j_swap_columns ((a : ℚ) / 2) ((b : ℚ) / 2) ((c : ℚ) / 2)
      ((d : ℚ) / 2) ((e : ℚ) / 2) ((f : ℚ) / 2)

/-- **Cyclic permutation of the columns** (Edmonds (6.2.4), p. 94). -/
theorem sixJ_cycle_columns (a b c d e f : ℕ) : sixJ a b c d e f = sixJ b c a e f d := by
  rw [sixJ_swap_columns]
  simpa only [sixJ_eq_wigner6j] using
    DLMF.WignerSymbols.wigner6j_swap_columns_two_three ((b : ℚ) / 2) ((a : ℚ) / 2) ((c : ℚ) / 2)
      ((e : ℚ) / 2) ((d : ℚ) / 2) ((f : ℚ) / 2)

/-- **Interchange of upper and lower entries in two columns** (Edmonds (6.2.5), p. 95;
DLMF 34.5.8). -/
theorem sixJ_swap_rows (a b c d e f : ℕ) : sixJ a b c d e f = sixJ d e c a b f := by
  simpa only [sixJ_eq_wigner6j] using
    DLMF.WignerSymbols.wigner6j_flip_first_two ((a : ℚ) / 2) ((b : ℚ) / 2) ((c : ℚ) / 2)
      ((d : ℚ) / 2) ((e : ℚ) / 2) ((f : ℚ) / 2)

/-! ### Sum rules and special values -/

/-- **Orthogonality** (Edmonds (6.2.9), p. 96; DLMF 34.5.14). -/
theorem sum_sixJ_mul_sixJ (a b d e f f' : ℕ)
    (h : ∃ c, IsTriad a b c ∧ IsTriad a e f ∧ IsTriad d b f ∧ IsTriad d e c) :
    ∑ c ∈ Finset.range (a + b + 1),
        ((c + 1) * (f + 1) : ℝ) * sixJ a b c d e f * sixJ a b c d e f' =
      if f = f' then 1 else 0 := by
  sorry

/-- **The Racah sum rule** (Edmonds (6.2.11), p. 96; DLMF 34.5.15), for doubled spins. -/
theorem sum_sixJ_racah (a b c d e f : ℕ) :
    ∑ x ∈ Finset.range (a + b + 1),
        (-1) ^ ((x + e + f) / 2) * ((x + 1 : ℕ) : ℝ) * sixJ a b x c d e * sixJ a b x d c f =
      sixJ a d e b c f := by
  sorry

/-- **The Biedenharn–Elliott identity** (Edmonds (6.2.12), p. 97; DLMF 34.5.16), for doubled
spins, with `Φ = j₁ + j₂ + j₃ + j₁' + j₂' + l₁ + l₂`. -/
theorem sixJ_mul_sixJ_biedenharnElliott (j₁ j₂ j₃ l₁ l₂ l₃ j₁' j₂' l₃' : ℕ)
    (hΦ : Even (j₁ + j₂ + j₃ + j₁' + j₂' + l₁ + l₂)) :
    (-1) ^ ((j₁ + j₂ + j₃ + j₁' + j₂' + l₁ + l₂) / 2) * sixJ j₁ j₂ j₃ l₁ l₂ l₃ *
        sixJ j₁' j₂' j₃ l₁ l₂ l₃' =
      ∑ x ∈ Finset.range (j₁ + j₁' + 1),
        (-1) ^ ((l₃ + l₃' + x) / 2) * ((x + 1 : ℕ) : ℝ) * sixJ j₁ j₁' x j₂' j₂ j₃ *
          sixJ l₃ l₃' x j₁' j₁ l₂ * sixJ l₃ l₃' x j₂' j₂ l₁ := by
  sorry

/-- **A vanishing entry** (Edmonds (6.3.2), p. 98; DLMF 34.5.1). -/
theorem sixJ_zero {a b c : ℕ} (h : IsTriad a b c) :
    sixJ a b c 0 c b = (-1) ^ ((a + b + c) / 2) / Real.sqrt ((b + 1) * (c + 1)) := by
  rw [sixJ_eq_wigner6j, Nat.cast_zero, zero_div,
    DLMF.WignerSymbols.wigner6j_zero ((RationalSpins.isTriad_iff a b c).mpr h),
    RationalSpins.half_sum_natCast h.2.2.2, DLMF.WignerSymbols.signPow_natCast,
    RationalSpins.two_mul_natCast_half, RationalSpins.two_mul_natCast_half]

end SFVK.ClebschGordan
