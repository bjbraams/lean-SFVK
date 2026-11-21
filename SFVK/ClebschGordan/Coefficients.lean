/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.ClebschGordan.Basic.Coefficients
public import DLMF.WignerSymbols.Basic.Definitions
import DLMF.WignerSymbols.ThreeJ
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Clebsch–Gordan coefficients: selection rules, orthogonality, symmetries, recursions

Layer 1 of the roadmap ClebschGordan, the statements about the coefficients alone. The
locators are to Edmonds, *Angular Momentum in Quantum Mechanics*: orthogonality (3.5.5)–(3.5.6),
p. 38; the recursions (3.5.9)–(3.5.10), p. 39; special values (3.5.11)–(3.5.13), p. 40, and the
stretched formula, p. 45; the symmetries (3.5.14), p. 41, and (3.5.15)–(3.5.17), p. 42. The
comparison with lean-DLMF's `DLMF.WignerSymbols.clebschGordan` (DLMF 34.1.1, rational spins)
is `clebschGordan_eq_dlmf`. The dimension count reindexes Tau Ceti's
`Finset.sum_range_min_add_one_sub_two_mul`. The symmetry proofs use lean-DLMF's proved
permutation and sign-reversal identities for the rational-spin Wigner symbol.
-/

public noncomputable section

namespace SFVK.ClebschGordan

/-! ### Admissible triples -/

/-- Admissibility is symmetric in the first two spins. -/
theorem isTriad_comm (d₁ d₂ d : ℕ) : IsTriad d₁ d₂ d ↔ IsTriad d₂ d₁ d := by
  simp only [isTriad_def, Nat.add_comm d₁ d₂]
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;> exact ⟨by omega, by omega, by omega, h₄⟩

/-- **The dimension count** `Σ_j (2j + 1) = (2j₁ + 1)(2j₂ + 1)` over the admissible `j`
(Wawrzyńczyk, *Group Representations and Special Functions*, (8.7.2), p. 305). -/
theorem sum_isTriad_succ (d₁ d₂ : ℕ) :
    ∑ d ∈ (Finset.range (d₁ + d₂ + 1)).filter (IsTriad d₁ d₂), (d + 1) =
      (d₁ + 1) * (d₂ + 1) := by
  rw [← Finset.sum_range_min_add_one_sub_two_mul]
  refine Finset.sum_nbij' (fun d : ℕ => (d₁ + d₂ - d) / 2)
    (fun k : ℕ => d₁ + d₂ - 2 * k) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_range, isTriad_def] at hd ⊢
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, isTriad_def] at hk ⊢
    refine ⟨by omega, by omega, by omega, by omega, ⟨d₁ + d₂ - k, by omega⟩⟩
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_range, isTriad_def] at hd
    obtain ⟨_, _, _, _, ⟨p, hp⟩⟩ := hd
    omega
  · intro k hk
    simp only [Finset.mem_range] at hk
    omega
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_range, isTriad_def] at hd
    obtain ⟨_, _, _, _, ⟨p, hp⟩⟩ := hd
    omega

/-! ### Comparison with lean-DLMF -/

namespace RationalSpins

open DLMF.WignerSymbols hiding IsTriad clebschGordan

/-- An even natural number has the same half in the rational and natural encodings. -/
theorem half_natCast {n : ℕ} (hn : Even n) : (n : ℚ) / 2 = ((n / 2 : ℕ) : ℚ) := by
  obtain ⟨k, hk⟩ := hn
  have heq : n / 2 = k := by omega
  rw [heq, hk, Nat.cast_add]
  ring

/-- An admissible triangle gap is the corresponding natural half-difference. -/
theorem half_sum_sub_natCast {a b c : ℕ} (h : c ≤ a + b)
    (hEven : Even (a + b + c)) :
    (a : ℚ) / 2 + (b : ℚ) / 2 - (c : ℚ) / 2 = (((a + b - c) / 2 : ℕ) : ℚ) := by
  have hdiff : Even (a + b - c) := by
    obtain ⟨n, hn⟩ := hEven
    exact ⟨n - c, by omega⟩
  rw [← half_natCast hdiff, Nat.cast_sub h, Nat.cast_add]
  ring

/-- The half-sum of an even triple equals its natural half-sum. -/
theorem half_sum_natCast {a b c : ℕ} (hEven : Even (a + b + c)) :
    (a : ℚ) / 2 + (b : ℚ) / 2 + (c : ℚ) / 2 = (((a + b + c) / 2 : ℕ) : ℚ) := by
  rw [← half_natCast hEven, Nat.cast_add, Nat.cast_add]
  ring

/-- Admissibility agrees in the natural-spin and rational-spin encodings. -/
theorem isTriad_iff (a b c : ℕ) :
    DLMF.WignerSymbols.IsTriad ((a : ℚ) / 2) ((b : ℚ) / 2) ((c : ℚ) / 2) ↔
      IsTriad a b c := by
  rw [DLMF.WignerSymbols.IsTriad, isTriad_def]
  constructor
  · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩⟩
    have hp' : a + b = c + 2 * p := by
      exact_mod_cast (by linarith : (a : ℚ) + b = c + 2 * p)
    have hq' : a + c = b + 2 * q := by
      exact_mod_cast (by linarith : (a : ℚ) + c = b + 2 * q)
    have hr' : b + c = a + 2 * r := by
      exact_mod_cast (by linarith : (b : ℚ) + c = a + 2 * r)
    exact ⟨by omega, by omega, by omega, ⟨p + c, by omega⟩⟩
  · rintro ⟨hc, ha, hb, he⟩
    have he' : Even (a + c + b) := by rwa [add_right_comm]
    have he'' : Even (b + c + a) := by rwa [add_comm b c, add_comm _ a, ← add_assoc]
    refine ⟨⟨_, half_sum_sub_natCast hc he⟩, ⟨(a + c - b) / 2, ?_⟩, ⟨(b + c - a) / 2, ?_⟩⟩
    · trans (a : ℚ) / 2 + (c : ℚ) / 2 - (b : ℚ) / 2
      · ring
      · exact half_sum_sub_natCast hb he'
    · trans (b : ℚ) / 2 + (c : ℚ) / 2 - (a : ℚ) / 2
      · ring
      · exact half_sum_sub_natCast ha he''

/-- An in-range index defines a rational-spin projection. -/
theorem isProjection {d i : ℕ} (hi : i ≤ d) :
    IsProjection ((d : ℚ) / 2) ((i : ℚ) - (d : ℚ) / 2) := by
  refine ⟨⟨d - i, ?_⟩, ⟨i, by ring⟩⟩
  rw [Nat.cast_sub hi]
  ring

/-- A reciprocal factorial of a difference vanishes past its cutoff. -/
theorem ratInvFactorial_natCast_sub (a b : ℕ) :
    ratInvFactorial ((a : ℚ) - b) = if b ≤ a then ((a - b).factorial : ℝ)⁻¹ else 0 := by
  split_ifs with h
  · exact ratInvFactorial_of_eq (Nat.cast_sub h).symm
  · exact ratInvFactorial_of_neg (sub_neg.mpr (by exact_mod_cast Nat.lt_of_not_ge h))

/-- The triangle factors agree on admissible triples. -/
theorem triangleCoefficient_eq_triangleDelta {a b c : ℕ} (h : IsTriad a b c) :
    triangleCoefficient a b c =
      triangleDelta ((a : ℚ) / 2) ((b : ℚ) / 2) ((c : ℚ) / 2) := by
  obtain ⟨hc, ha, hb, he⟩ := (isTriad_def _ _ _).mp h
  have he' : Even (a + c + b) := by rwa [add_right_comm]
  have he'' : Even (b + c + a) := by rwa [add_comm b c, add_comm _ a, ← add_assoc]
  have hs₂ : (a : ℚ) / 2 - (b : ℚ) / 2 + (c : ℚ) / 2 = (((a + c - b) / 2 : ℕ) : ℚ) := by
    rw [sub_add_eq_add_sub, half_sum_sub_natCast hb he']
  have hs₃ : -((a : ℚ) / 2) + (b : ℚ) / 2 + (c : ℚ) / 2 =
      (((b + c - a) / 2 : ℕ) : ℚ) := by
    rw [neg_add_eq_sub, sub_add_eq_add_sub, half_sum_sub_natCast ha he'']
  rw [triangleCoefficient_def, triangleDelta, ratFactorial_of_eq (half_sum_sub_natCast hc he),
    ratFactorial_of_eq hs₂, ratFactorial_of_eq hs₃, half_sum_natCast he, ← Nat.cast_succ,
    ratFactorial_of_eq rfl]
  push_cast
  rfl


/-- The third triangle gap in doubled-spin coordinates. -/
theorem half_sum_sub_right {a b c : ℕ} (h : IsTriad a b c) :
    (a : ℚ) / 2 - (b : ℚ) / 2 + (c : ℚ) / 2 = (((a + c - b) / 2 : ℕ) : ℚ) := by
  rw [sub_add_eq_add_sub]
  exact half_sum_sub_natCast h.2.2.1 (by simpa only [add_right_comm a c b] using h.2.2.2)

/-- The first triangle gap in doubled-spin coordinates. -/
theorem half_sum_sub_left {a b c : ℕ} (h : IsTriad a b c) :
    -((a : ℚ) / 2) + (b : ℚ) / 2 + (c : ℚ) / 2 = (((b + c - a) / 2 : ℕ) : ℚ) := by
  rw [neg_add_eq_sub, sub_add_eq_add_sub]
  exact half_sum_sub_natCast h.2.1 (by simpa only [add_comm _ a, add_assoc] using h.2.2.2)

/-- Negating a projection reverses its index. -/
theorem negate_projection {d i : ℕ} (hi : i ≤ d) :
    -((i : ℚ) - (d : ℚ) / 2) = ((d - i : ℕ) : ℚ) - (d : ℚ) / 2 := by
  rw [Nat.cast_sub hi]
  ring

/-- The Racah summand in the natural and rational encodings agrees throughout the sum. -/
private theorem clebschGordanTerm_eq_racahTerm3j {a b c i j z : ℕ}
    (htri : IsTriad a b c) (hi : i ≤ a) (hj : j ≤ b) (hz : z ≤ (a + b - c) / 2) :
    clebschGordanTerm a b c i j z =
      racahTerm3j ((a : ℚ) / 2) ((b : ℚ) / 2) ((c : ℚ) / 2)
        ((i : ℚ) - (a : ℚ) / 2) ((j : ℚ) - (b : ℚ) / 2) z := by
  let gap := (a + b - c) / 2
  have hgap : (a : ℚ) / 2 + (b : ℚ) / 2 - (c : ℚ) / 2 = gap :=
    half_sum_sub_natCast htri.1 htri.2.2.2
  have hfirst : (a : ℚ) / 2 - ((i : ℚ) - (a : ℚ) / 2) = ((a - i : ℕ) : ℚ) := by
    rw [Nat.cast_sub hi]
    ring
  have hsecond : (b : ℚ) / 2 + ((j : ℚ) - (b : ℚ) / 2) = j := by ring
  have hthird : (c : ℚ) / 2 - (b : ℚ) / 2 + ((i : ℚ) - (a : ℚ) / 2) + (z : ℚ) =
      ((z + i : ℕ) : ℚ) - gap := by
    rw [← hgap, Nat.cast_add]
    ring
  have hfourth : (c : ℚ) / 2 - (a : ℚ) / 2 - ((j : ℚ) - (b : ℚ) / 2) + (z : ℚ) =
      ((z + (b - j) : ℕ) : ℚ) - gap := by
    rw [← hgap, Nat.cast_add, Nat.cast_sub hj]
    ring
  rw [clebschGordanTerm, racahTerm3j, hgap, hfirst, hsecond, hthird, hfourth,
    ratInvFactorial_of_eq (n := z) rfl, ratInvFactorial_natCast_sub,
    ratInvFactorial_natCast_sub, ratInvFactorial_natCast_sub, ratInvFactorial_natCast_sub,
    ratInvFactorial_natCast_sub, ite_eq_left hz]
  have hgap_def : gap = (a + b - c) / 2 := rfl
  rw [← hgap_def]
  by_cases hg : gap ≤ z + i ∧ gap ≤ z + (b - j) ∧ z ≤ a - i ∧ z ≤ j
  · simp only [ite_eq_left hg, ite_eq_left hg.1, ite_eq_left hg.2.1, ite_eq_left hg.2.2.1,
      ite_eq_left hg.2.2.2, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  · rw [ite_eq_right hg]
    have hne : ¬ gap ≤ z + i ∨ ¬ gap ≤ z + (b - j) ∨ ¬ z ≤ a - i ∨ ¬ z ≤ j := by
      tauto
    rcases hne with h | h | h | h <;> simp only [h, ↓reduceIte, mul_zero, zero_mul]

/-- The square root in the finite formula is the triangle factor times the six projection
factorials and the dimension factor. -/
private theorem sqrt_prefactor_eq (a b c i j k : ℕ) :
    Real.sqrt (clebschGordanPrefactor a b c i j k) =
      Real.sqrt ((c : ℝ) + 1) * triangleCoefficient a b c *
        Real.sqrt ((i.factorial : ℝ) * (a - i).factorial * j.factorial *
          (b - j).factorial * (c - k).factorial * k.factorial) := by
  simp only [clebschGordanPrefactor, triangleCoefficient_def]
  push_cast
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  ring

/-- Doubling a half-spin cast back into the reals recovers its natural degree. -/
theorem two_mul_natCast_half (d : ℕ) : 2 * (((d : ℚ) / 2 : ℚ) : ℝ) = (d : ℝ) := by
  push_cast
  ring

end RationalSpins

open RationalSpins in
open DLMF.WignerSymbols hiding IsTriad clebschGordan in
/-- **Conversion to lean-DLMF's rational-spin coefficient** (DLMF 34.1.1): for indices in range,
`clebschGordan d₁ d₂ d i₁ i₂ i` is `DLMF.WignerSymbols.clebschGordan j₁ m₁ j₂ m₂ j m` with
`j_r = d_r/2` and `m_r = i_r - d_r/2`. -/
theorem clebschGordan_eq_dlmf {d₁ d₂ d i₁ i₂ i : ℕ} (h₁ : i₁ ≤ d₁) (h₂ : i₂ ≤ d₂) (h : i ≤ d) :
    clebschGordan d₁ d₂ d i₁ i₂ i =
      DLMF.WignerSymbols.clebschGordan ((d₁ : ℚ) / 2) ((i₁ : ℚ) - (d₁ : ℚ) / 2) ((d₂ : ℚ) / 2)
        ((i₂ : ℚ) - (d₂ : ℚ) / 2) ((d : ℚ) / 2) ((i : ℚ) - (d : ℚ) / 2) := by
  let aspin := (d₁ : ℚ) / 2
  let bspin := (d₂ : ℚ) / 2
  let cspin := (d : ℚ) / 2
  let aweight := (i₁ : ℚ) - aspin
  let bweight := (i₂ : ℚ) - bspin
  let cweight := (i : ℚ) - cspin
  have hAdm : IsAdmissible3j aspin bspin cspin aweight bweight (-cweight) ↔
      IsTriad d₁ d₂ d ∧ 2 * i + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d := by
    unfold IsAdmissible3j
    have hneg : -cweight = ((d - i : ℕ) : ℚ) - cspin := negate_projection h
    have hcp : IsProjection cspin (-cweight) := hneg.symm ▸ isProjection (Nat.sub_le d i)
    rw [RationalSpins.isTriad_iff, and_iff_right (isProjection h₁), and_iff_right (isProjection h₂),
      and_iff_right hcp]
    apply and_congr_right
    intro _
    dsimp only [aweight, bweight, cweight, aspin, bspin, cspin]
    constructor
    · intro h
      exact_mod_cast (by linarith : (2 : ℚ) * i + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d)
    · intro h
      have he : (2 : ℚ) * i + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d := by exact_mod_cast h
      linarith
  by_cases htri : IsTriad d₁ d₂ d
  · by_cases hweight : 2 * i + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d
    · have hadm := hAdm.mpr ⟨htri, hweight⟩
      have ha_pos : aspin + aweight = i₁ := by dsimp [aweight]; ring
      have ha_neg : aspin - aweight = ((d₁ - i₁ : ℕ) : ℚ) := by
        dsimp [aweight, aspin]
        rw [Nat.cast_sub h₁]
        ring
      have hb_pos : bspin + bweight = i₂ := by dsimp [bweight]; ring
      have hb_neg : bspin - bweight = ((d₂ - i₂ : ℕ) : ℚ) := by
        dsimp [bweight, bspin]
        rw [Nat.cast_sub h₂]
        ring
      have hc_pos : cspin + -cweight = ((d - i : ℕ) : ℚ) := by
        dsimp [cweight, cspin]
        rw [Nat.cast_sub h]
        ring
      have hc_neg : cspin - -cweight = i := by dsimp [cweight]; ring
      have hdim : 2 * (cspin : ℝ) + 1 = (d : ℝ) + 1 := by
        dsimp [cspin]
        push_cast
        ring
      have hGap : aspin + bspin - cspin = (((d₁ + d₂ - d) / 2 : ℕ) : ℚ) :=
        half_sum_sub_natCast htri.1 htri.2.2.2
      have hSum :
          ∑ z ∈ Finset.range ((d₁ + d₂ - d) / 2 + 1), clebschGordanTerm d₁ d₂ d i₁ i₂ z =
            ∑ z ∈ Finset.range (⌊aspin + bspin - cspin⌋.toNat + 1),
              racahTerm3j aspin bspin cspin aweight bweight z := by
        rw [hGap, Int.floor_natCast, Int.toNat_natCast]
        exact Finset.sum_congr rfl fun z hz =>
          clebschGordanTerm_eq_racahTerm3j htri h₁ h₂ (by simpa using hz)
      calc
        _ = Real.sqrt (clebschGordanPrefactor d₁ d₂ d i₁ i₂ i) *
            ∑ z ∈ Finset.range ((d₁ + d₂ - d) / 2 + 1), clebschGordanTerm d₁ d₂ d i₁ i₂ z := by
          rw [clebschGordan_def, ite_eq_left ⟨htri, h₁, h₂, h, hweight⟩]
        _ = DLMF.WignerSymbols.clebschGordan aspin aweight bspin bweight cspin cweight := by
          rw [DLMF.WignerSymbols.clebschGordan, wigner3j, ite_eq_left hadm, hdim,
            sqrt_prefactor_eq d₁ d₂ d i₁ i₂ i, triangleCoefficient_eq_triangleDelta htri,
            ratFactorial_of_eq ha_pos, ratFactorial_of_eq ha_neg,
            ratFactorial_of_eq hb_pos, ratFactorial_of_eq hb_neg,
            ratFactorial_of_eq hc_pos, ratFactorial_of_eq hc_neg, hSum, sub_neg_eq_add]
          linear_combination -(Real.sqrt ((d : ℝ) + 1) * triangleDelta aspin bspin cspin *
            Real.sqrt ((i₁.factorial : ℝ) * (d₁ - i₁).factorial * i₂.factorial *
              (d₂ - i₂).factorial * (d - i).factorial * i.factorial) *
            ∑ z ∈ Finset.range (⌊aspin + bspin - cspin⌋.toNat + 1),
              racahTerm3j aspin bspin cspin aweight bweight z) *
            signPow_sq (aspin - bspin + cweight)
    · have hn : ¬ IsAdmissible3j aspin bspin cspin aweight bweight (-cweight) :=
        fun h => hweight (hAdm.mp h).2
      rw [clebschGordan_eq_zero_of_ne hweight, DLMF.WignerSymbols.clebschGordan,
        wigner3j_of_not hn, mul_zero]
  · have hn : ¬ IsAdmissible3j aspin bspin cspin aweight bweight (-cweight) :=
      fun h => htri (hAdm.mp h).1
    rw [clebschGordan_eq_zero_of_not_isTriad htri, DLMF.WignerSymbols.clebschGordan,
      wigner3j_of_not hn, mul_zero]

/-! ### Orthogonality -/

/-- **Orthogonality in the coupled indices** (Edmonds (3.5.5), p. 38). -/
theorem sum_clebschGordan_mul_clebschGordan {d₁ d₂ d d' i i' : ℕ} (h : IsTriad d₁ d₂ d)
    (h' : IsTriad d₁ d₂ d') (hi : i ≤ d) (hi' : i' ≤ d') :
    ∑ i₁ ∈ Finset.range (d₁ + 1), ∑ i₂ ∈ Finset.range (d₂ + 1),
        clebschGordan d₁ d₂ d i₁ i₂ i * clebschGordan d₁ d₂ d' i₁ i₂ i' =
      if d = d' ∧ i = i' then 1 else 0 := by
  sorry

/-- **Orthogonality in the product indices** (Edmonds (3.5.6), p. 38). -/
theorem sum_clebschGordan_mul_clebschGordan_right {d₁ d₂ i₁ i₂ i₁' i₂' : ℕ} (h₁ : i₁ ≤ d₁)
    (h₂ : i₂ ≤ d₂) (h₁' : i₁' ≤ d₁) (h₂' : i₂' ≤ d₂) :
    ∑ d ∈ Finset.range (d₁ + d₂ + 1), ∑ i ∈ Finset.range (d + 1),
        clebschGordan d₁ d₂ d i₁ i₂ i * clebschGordan d₁ d₂ d i₁' i₂' i =
      if i₁ = i₁' ∧ i₂ = i₂' then 1 else 0 := by
  sorry

/-! ### Symmetries -/

namespace Symmetry

open DLMF.WignerSymbols hiding IsTriad clebschGordan

/-- The spin written as a rational number. -/
private def spin (d : ℕ) : ℚ := (d : ℚ) / 2

/-- The magnetic weight written as a rational number. -/
private def projection (d i : ℕ) : ℚ := (i : ℚ) - spin d

/-- Reflection of indices negates the projection. -/
private theorem projection_reflect {d i : ℕ} (h : i ≤ d) :
    projection d (d - i) = -projection d i :=
  (RationalSpins.negate_projection h).symm

/-- The rational-spin 3-j expression for the coefficient. -/
private theorem expansion {a b c i j k : ℕ} (hi : i ≤ a) (hj : j ≤ b) (hk : k ≤ c) :
    clebschGordan a b c i j k =
      signPow (spin a - spin b + projection c k) * Real.sqrt ((c : ℝ) + 1) *
        wigner3j (spin a) (spin b) (spin c) (projection a i) (projection b j)
          (-projection c k) := by
  dsimp only [spin, projection]
  rw [clebschGordan_eq_dlmf hi hj hk, DLMF.WignerSymbols.clebschGordan,
    RationalSpins.two_mul_natCast_half]

/-- Rotating a phase by an even integer leaves it unchanged. -/
private theorem phase_eq_of_even_shift {a b : ℚ} (u v : ℕ) (k : ℤ)
    (h : a + (u : ℚ) = b + (v : ℚ) + (2 * (k : ℚ))) :
    signPow a * (-1 : ℝ) ^ u = signPow b * (-1 : ℝ) ^ v := by
  have h₁ := signPow_add_intCast a (u : ℤ)
  have h₂ := signPow_add_intCast b (v : ℤ)
  rw [Int.cast_natCast, zpow_natCast] at h₁ h₂
  rw [← h₁, ← h₂, h]
  have hk : (2 * (k : ℚ)) = (((2 * k : ℤ)) : ℚ) := by push_cast; rfl
  rw [hk, signPow_add_intCast, zpow_mul]
  norm_num

/-- Swap the last two columns and record the odd permutation phase. -/
private theorem wigner3j_swap_last (a b c i j k : ℚ) :
    wigner3j a b c i j k = signPow (a + b + c) * wigner3j a c b i k j := by
  rw [wigner3j_cycle a b c i j k, wigner3j_swap b c a j k i, ← wigner3j_cycle a c b i k j]
  congr 2
  ring

end Symmetry

open Symmetry in
open DLMF.WignerSymbols hiding IsTriad clebschGordan in
/-- **Exchange of the two spins** (Edmonds (3.5.14), p. 41):
`(j₁ m₁ j₂ m₂ | j m) = (-1)^{j₁ + j₂ - j} (j₂ m₂ j₁ m₁ | j m)`. -/
theorem clebschGordan_swap (d₁ d₂ d i₁ i₂ i : ℕ) :
    clebschGordan d₁ d₂ d i₁ i₂ i =
      (-1) ^ ((d₁ + d₂ - d) / 2) * clebschGordan d₂ d₁ d i₂ i₁ i := by
  by_cases hr : i₁ ≤ d₁ ∧ i₂ ≤ d₂ ∧ i ≤ d
  · by_cases ht : IsTriad d₁ d₂ d
    · rw [expansion hr.1 hr.2.1 hr.2.2, expansion hr.2.1 hr.1 hr.2.2, wigner3j_swap]
      let left := spin d₁ - spin d₂ + projection d i
      let right := spin d₂ - spin d₁ + projection d i
      let total := (d₁ + d₂ + d) / 2
      let gap := (d₁ + d₂ - d) / 2
      have htotal : spin d₁ + spin d₂ + spin d = (total : ℚ) :=
        RationalSpins.half_sum_natCast ht.2.2.2
      have hgap : spin d₁ + spin d₂ - spin d = (gap : ℚ) :=
        RationalSpins.half_sum_sub_natCast ht.1 ht.2.2.2
      have hphase : left + (total : ℚ) = right + (gap : ℚ) +
          2 * (((d₁ + d - d₂) / 2 : ℕ) : ℚ) := by
        rw [← htotal, ← hgap, ← RationalSpins.half_sum_sub_right ht]
        dsimp only [left, right, spin]
        ring
      have h := phase_eq_of_even_shift (a := left) (b := right) total gap
        (((d₁ + d - d₂) / 2 : ℕ) : ℤ) (by simpa only [Int.cast_natCast] using hphase)
      rw [htotal, signPow_natCast]
      linear_combination (Real.sqrt ((d : ℝ) + 1) *
        wigner3j (spin d₂) (spin d₁) (spin d) (projection d₂ i₂) (projection d₁ i₁)
          (-projection d i)) * h
    · rw [clebschGordan_eq_zero_of_not_isTriad ht,
        clebschGordan_eq_zero_of_not_isTriad (mt (isTriad_comm _ _ _).mpr ht), mul_zero]
  · rw [clebschGordan_eq_zero_of_out_of_range hr,
      clebschGordan_eq_zero_of_out_of_range (fun h => hr ⟨h.2.1, h.1, h.2.2⟩), mul_zero]

open Symmetry in
open DLMF.WignerSymbols hiding IsTriad clebschGordan in
/-- **Reversal of the magnetic quantum numbers** (Edmonds (3.5.17), p. 42). -/
theorem clebschGordan_reflect {d₁ d₂ d i₁ i₂ i : ℕ} (h₁ : i₁ ≤ d₁) (h₂ : i₂ ≤ d₂) (h : i ≤ d) :
    clebschGordan d₁ d₂ d i₁ i₂ i =
      (-1) ^ ((d₁ + d₂ - d) / 2) * clebschGordan d₁ d₂ d (d₁ - i₁) (d₂ - i₂) (d - i) := by
  by_cases ht : IsTriad d₁ d₂ d
  · rw [expansion h₁ h₂ h, expansion (Nat.sub_le _ _) (Nat.sub_le _ _) (Nat.sub_le _ _),
      projection_reflect h₁, projection_reflect h₂, projection_reflect h, wigner3j_neg]
    let left := spin d₁ - spin d₂ + projection d i
    let right := spin d₁ - spin d₂ + -projection d i
    let total := (d₁ + d₂ + d) / 2
    let gap := (d₁ + d₂ - d) / 2
    have htotal : spin d₁ + spin d₂ + spin d = (total : ℚ) :=
      RationalSpins.half_sum_natCast ht.2.2.2
    have hgap : spin d₁ + spin d₂ - spin d = (gap : ℚ) :=
      RationalSpins.half_sum_sub_natCast ht.1 ht.2.2.2
    have hphase : left + (total : ℚ) = right + (gap : ℚ) + 2 * (i : ℚ) := by
      rw [← htotal, ← hgap]
      dsimp only [left, right, spin, projection]
      ring
    have hp := phase_eq_of_even_shift (a := left) (b := right) total gap (i : ℤ)
      (by simpa only [Int.cast_natCast] using hphase)
    rw [htotal, signPow_natCast]
    linear_combination (Real.sqrt ((d : ℝ) + 1) *
      wigner3j (spin d₁) (spin d₂) (spin d) (-projection d₁ i₁) (-projection d₂ i₂)
        (-(-projection d i))) * hp
  · rw [clebschGordan_eq_zero_of_not_isTriad ht, clebschGordan_eq_zero_of_not_isTriad ht, mul_zero]

open Symmetry in
open DLMF.WignerSymbols hiding IsTriad clebschGordan in
/-- **Exchange of the second and the coupled spin** (Edmonds (3.5.15), p. 42):
`(j₁ m₁ j₂ m₂ | j₃ m₃) = (-1)^{j₁ - m₁} √((2j₃ + 1)/(2j₂ + 1)) (j₁ m₁ j₃ -m₃ | j₂ -m₂)`. -/
theorem clebschGordan_rotate {d₁ d₂ d i₁ i₂ i : ℕ} (h₁ : i₁ ≤ d₁) (h₂ : i₂ ≤ d₂) (h : i ≤ d) :
    clebschGordan d₁ d₂ d i₁ i₂ i =
      (-1) ^ (d₁ - i₁) * Real.sqrt ((d + 1) / (d₂ + 1)) *
        clebschGordan d₁ d d₂ i₁ (d - i) (d₂ - i₂) := by
  by_cases ht : IsTriad d₁ d₂ d
  · by_cases hm : 2 * i + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d
    · rw [expansion h₁ h₂ h, expansion h₁ (Nat.sub_le _ _) (Nat.sub_le _ _),
        projection_reflect h, projection_reflect h₂, neg_neg, wigner3j_swap_last]
      let left := spin d₁ - spin d₂ + projection d i
      let right := spin d₁ - spin d - projection d₂ i₂
      let total := (d₁ + d₂ + d) / 2
      have htotal : spin d₁ + spin d₂ + spin d = (total : ℚ) :=
        RationalSpins.half_sum_natCast ht.2.2.2
      have hm' : (2 : ℚ) * i + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d := by exact_mod_cast hm
      have hphase : left + (total : ℚ) = right + (d₁ - i₁ : ℕ) + 2 * (i : ℚ) := by
        rw [← htotal, Nat.cast_sub h₁]
        dsimp only [left, right, spin, projection]
        linarith
      have hp := phase_eq_of_even_shift (a := left) (b := right) total (d₁ - i₁) (i : ℤ)
        (by simpa only [Int.cast_natCast] using hphase)
      rw [htotal, signPow_natCast, ← sub_eq_add_neg, Real.sqrt_div (by positivity)]
      have hr : Real.sqrt ((d₂ : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
      field_simp [hr]
      linear_combination (wigner3j (spin d₁) (spin d) (spin d₂) (projection d₁ i₁) (-projection d i)
          (projection d₂ i₂)) * hp
    · rw [clebschGordan_eq_zero_of_ne hm,
        clebschGordan_eq_zero_of_ne (d₁ := d₁) (d₂ := d) (d := d₂) (i₁ := i₁)
          (i₂ := d - i) (i := d₂ - i₂) (by omega), mul_zero]
  · have hn : ¬ IsTriad d₁ d d₂ := by
      intro hc
      obtain ⟨h₂', h₁', h', hpar⟩ := (isTriad_def _ _ _).mp hc
      apply ht
      rw [isTriad_def]
      exact ⟨h', by omega, h₂', by simpa only [add_right_comm d₁ d₂ d] using hpar⟩
    rw [clebschGordan_eq_zero_of_not_isTriad ht, clebschGordan_eq_zero_of_not_isTriad hn, mul_zero]

/-! ### Special values -/

/-- **The Condon–Shortley phase** (Edmonds (3.5.11), p. 40): `(j₁ j₁ j₂ (j - j₁) | j j) > 0`. -/
theorem clebschGordan_pos {d₁ d₂ d : ℕ} (h : IsTriad d₁ d₂ d) :
    0 < clebschGordan d₁ d₂ d d₁ ((d + d₂ - d₁) / 2) d := by
  let j := (d + d₂ - d₁) / 2
  let gap := (d₁ + d₂ - d) / 2
  have hz : d₂ - j = gap := by
    obtain ⟨n, hn⟩ := h.2.2.2
    have := h.1
    have := h.2.1
    dsimp [j, gap]
    omega
  have hj : j ≤ d₂ := by
    have := h.1
    dsimp [j]
    omega
  have hgap : gap ≤ d₁ := by
    have := h.2.2.1
    dsimp [gap]
    omega
  have hweight : 2 * d + d₁ + d₂ = 2 * d₁ + 2 * j + d := by
    obtain ⟨n, hn⟩ := h.2.2.2
    have := h.2.1
    dsimp [j]
    omega
  rw [clebschGordan_def, ite_eq_left ⟨h, le_rfl, hj, le_rfl, hweight⟩]
  have hsum :
      (∑ z ∈ Finset.range (gap + 1), clebschGordanTerm d₁ d₂ d d₁ j z) =
        clebschGordanTerm d₁ d₂ d d₁ j 0 := by
    apply Finset.sum_eq_single 0
    · intro z _ hne
      rw [clebschGordanTerm]
      apply ite_eq_right
      intro hh
      exact hne (by have := hh.2.2.1; omega)
    · simp
  rw [hsum]
  apply mul_pos (Real.sqrt_pos.2 ?_) ?_
  · unfold clebschGordanPrefactor
    positivity
  · rw [clebschGordanTerm]
    have hselect : gap ≤ 0 + d₁ ∧ gap ≤ 0 + (d₂ - j) ∧ 0 ≤ d₁ - d₁ ∧ 0 ≤ j :=
      ⟨by simpa only [zero_add] using hgap, by rw [zero_add, hz], Nat.zero_le _, Nat.zero_le _⟩
    rw [ite_eq_left hselect, pow_zero]
    positivity

/-- **The stretched coefficient** `j = j₁ + j₂` (Edmonds, p. 45). -/
theorem clebschGordan_stretched {d₁ d₂ i₁ i₂ : ℕ} (h₁ : i₁ ≤ d₁) (h₂ : i₂ ≤ d₂) :
    clebschGordan d₁ d₂ (d₁ + d₂) i₁ i₂ (i₁ + i₂) =
      Real.sqrt (((d₁.factorial * d₂.factorial * (i₁ + i₂).factorial *
          (d₁ + d₂ - i₁ - i₂).factorial : ℕ) : ℝ) /
        (((d₁ + d₂).factorial * i₁.factorial * (d₁ - i₁).factorial * i₂.factorial *
          (d₂ - i₂).factorial : ℕ) : ℝ)) := by
  have ht : IsTriad d₁ d₂ (d₁ + d₂) := by
    rw [isTriad_def]
    exact ⟨le_rfl, by omega, by omega, ⟨_, rfl⟩⟩
  rw [clebschGordan_def, ite_eq_left ⟨ht, h₁, h₂, by omega, by omega⟩, Nat.sub_self, Nat.zero_div,
    Finset.sum_range_one, clebschGordanTerm]
  simp only [Nat.sub_self, Nat.zero_div, Nat.zero_le, and_self, ↓reduceIte,
    Nat.factorial_zero, one_mul, pow_zero, Nat.sub_zero, zero_add]
  apply DLMF.WignerSymbols.sqrt_mul_eq_sqrt_of_eq
  · unfold clebschGordanPrefactor
    positivity
  · positivity
  · have hgap₁ : (d₁ + (d₁ + d₂) - d₂) / 2 = d₁ := by omega
    have hgap₂ : (d₂ + (d₁ + d₂) - d₁) / 2 = d₂ := by omega
    have hsum : (d₁ + d₂ + (d₁ + d₂)) / 2 = d₁ + d₂ := by omega
    rw [clebschGordanPrefactor, Nat.sub_self, Nat.zero_div, hgap₁, hgap₂, hsum,
      Nat.factorial_succ, ← Nat.sub_sub]
    simp only [Nat.factorial_zero, mul_one]
    push_cast
    field_simp

/-- **Coupling with spin zero** (Edmonds (3.5.12), p. 40). -/
theorem clebschGordan_zero_right {d i : ℕ} (h : i ≤ d) : clebschGordan d 0 d i 0 i = 1 := by
  have he := clebschGordan_stretched h (Nat.le_refl 0)
  simp only [add_zero, Nat.sub_zero, Nat.factorial_zero, mul_one] at he
  rw [he]
  have heq : d.factorial * i.factorial * (d - i).factorial ≠ 0 := by positivity
  rw [div_self (Nat.cast_ne_zero.2 heq), Real.sqrt_one]

open DLMF.WignerSymbols hiding IsTriad clebschGordan in
/-- **Coupling to spin zero** (Edmonds (3.5.13), p. 40). -/
theorem clebschGordan_spin_zero {d i : ℕ} (h : i ≤ d) :
    clebschGordan d d 0 i (d - i) 0 = (-1) ^ (d - i) / Real.sqrt (d + 1) := by
  rw [SFVK.ClebschGordan.clebschGordan_eq_dlmf h (Nat.sub_le _ _) le_rfl,
    DLMF.WignerSymbols.clebschGordan]
  have hs : signPow 0 = 1 := by simpa only [Nat.cast_zero, pow_zero] using signPow_natCast 0
  simp only [Nat.cast_zero, Rat.cast_zero, zero_div, add_zero, neg_zero, sub_self, zero_add,
    hs, one_mul, mul_zero, Real.sqrt_one]
  rw [← RationalSpins.negate_projection h, wigner3j_j_j_zero (RationalSpins.isProjection h),
    RationalSpins.two_mul_natCast_half]
  have hp : (d : ℚ) / 2 - ((i : ℚ) - (d : ℚ) / 2) = ((d - i : ℕ) : ℚ) := by
    rw [Nat.cast_sub h]
    ring
  rw [hp, DLMF.WignerSymbols.signPow_natCast]

/-- **Spin one half:** `(j₁ m₁ ½ ½ | j₁ + ½, m) = √((j₁ + m + ½)/(2j₁ + 1))`, from the stretched
formula. -/
theorem clebschGordan_spinHalf {d i : ℕ} (h : i ≤ d) :
    clebschGordan d 1 (d + 1) i 1 (i + 1) = Real.sqrt ((i + 1) / (d + 1)) := by
  rw [clebschGordan_stretched h (Nat.le_refl 1)]
  have he : d + 1 - i - 1 = d - i := by omega
  rw [he, Nat.factorial_succ i, Nat.factorial_succ d]
  norm_num
  congr 1
  field_simp

/-! ### Recursions -/

/-- **The lowering recursion** (Edmonds (3.5.9), p. 39), with `m` shifted by one. -/
theorem clebschGordan_lowering (d₁ d₂ d i₁ i₂ i : ℕ) :
    Real.sqrt (((i + 1) * (d - i) : ℕ) : ℝ) * clebschGordan d₁ d₂ d i₁ i₂ i =
      Real.sqrt (((i₁ + 1) * (d₁ - i₁) : ℕ) : ℝ) * clebschGordan d₁ d₂ d (i₁ + 1) i₂ (i + 1) +
        Real.sqrt (((i₂ + 1) * (d₂ - i₂) : ℕ) : ℝ) *
          clebschGordan d₁ d₂ d i₁ (i₂ + 1) (i + 1) := by
  sorry

/-- **The raising recursion** (Edmonds (3.5.10), p. 39), with `m` shifted by one. -/
theorem clebschGordan_raising (d₁ d₂ d i₁ i₂ i : ℕ) :
    Real.sqrt (((i + 1) * (d - i) : ℕ) : ℝ) * clebschGordan d₁ d₂ d (i₁ + 1) (i₂ + 1) (i + 1) =
      Real.sqrt (((i₁ + 1) * (d₁ - i₁) : ℕ) : ℝ) * clebschGordan d₁ d₂ d i₁ (i₂ + 1) i +
        Real.sqrt (((i₂ + 1) * (d₂ - i₂) : ℕ) : ℝ) * clebschGordan d₁ d₂ d (i₁ + 1) i₂ i := by
  sorry

end SFVK.ClebschGordan
