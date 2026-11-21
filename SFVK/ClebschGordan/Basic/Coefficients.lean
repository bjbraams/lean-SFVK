/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Clebsch–Gordan coefficients and 3-j symbols

Spins and magnetic quantum numbers are encoded by natural numbers: the spin `j = d/2` by `d`,
and `m = i - d/2` by the index `i ≤ d`, as for the unitary model of `SFVK.SU2`.

* `IsTriad d₁ d₂ d`: the admissible triples, Edmonds, *Angular Momentum in Quantum Mechanics*,
  (3.1.5), p. 35; DLMF 34.2.1.
* `clebschGordan d₁ d₂ d i₁ i₂ i`: Edmonds's `(j₁ m₁ j₂ m₂ | j₁ j₂ j m)` by Racah's formula,
  Edmonds (3.6.11), p. 45; `0` outside the admissible range.
* `threeJ`: the 3-j symbol, Edmonds (3.7.3), p. 46; DLMF 34.1.1.
* `triangleCoefficient`: DLMF's `Δ(j₁ j₂ j₃)` (34.2.5), for doubled spins.
-/

public noncomputable section

namespace SFVK.ClebschGordan

/-- The spins `d₁/2`, `d₂/2`, `d/2` form an admissible triple: the triangle inequalities hold
and `j₁ + j₂ + j` is an integer (Edmonds (3.1.5), p. 35; DLMF 34.2.1). -/
@[expose]
def IsTriad (d₁ d₂ d : ℕ) : Prop :=
  d ≤ d₁ + d₂ ∧ d₁ ≤ d₂ + d ∧ d₂ ≤ d₁ + d ∧ Even (d₁ + d₂ + d)

instance (d₁ d₂ d : ℕ) : Decidable (IsTriad d₁ d₂ d) := by
  unfold IsTriad; infer_instance

/-- The doubled-spin triangle condition consists of the triangle inequalities and even total degree.
-/
theorem isTriad_def (d₁ d₂ d : ℕ) :
    IsTriad d₁ d₂ d ↔ d ≤ d₁ + d₂ ∧ d₁ ≤ d₂ + d ∧ d₂ ≤ d₁ + d ∧ Even (d₁ + d₂ + d) :=
  Iff.rfl

/-- The summand of Racah's formula (3.6.11) at the summation index `z`, with `L = j₁ + j₂ - j`;
it is `0` unless every factorial argument is nonnegative. -/
@[expose]
def clebschGordanTerm (d₁ d₂ d i₁ i₂ z : ℕ) : ℝ :=
  if (d₁ + d₂ - d) / 2 ≤ z + i₁ ∧ (d₁ + d₂ - d) / 2 ≤ z + (d₂ - i₂) ∧ z ≤ d₁ - i₁ ∧
      z ≤ i₂ then
    (-1) ^ z / ((z.factorial * ((d₁ + d₂ - d) / 2 - z).factorial *
      (d₁ - i₁ - z).factorial * (i₂ - z).factorial *
      (z + i₁ - (d₁ + d₂ - d) / 2).factorial *
      (z + (d₂ - i₂) - (d₁ + d₂ - d) / 2).factorial : ℕ) : ℝ)
  else 0

/-- The factor under the square root in Racah's formula (3.6.11):
`(2j+1) (j₁+j₂-j)! (j₁-j₂+j)! (-j₁+j₂+j)!/(j₁+j₂+j+1)! · Π (j_r + m_r)! (j_r - m_r)!`. -/
@[expose]
def clebschGordanPrefactor (d₁ d₂ d i₁ i₂ i : ℕ) : ℝ :=
  (((d + 1) * ((d₁ + d₂ - d) / 2).factorial * ((d₁ + d - d₂) / 2).factorial *
      ((d₂ + d - d₁) / 2).factorial * i₁.factorial * (d₁ - i₁).factorial * i₂.factorial *
      (d₂ - i₂).factorial * i.factorial * (d - i).factorial : ℕ) : ℝ) /
    (((d₁ + d₂ + d) / 2 + 1).factorial : ℕ)

/-- The Clebsch–Gordan coefficient `(j₁ m₁ j₂ m₂ | j₁ j₂ j m)`, Edmonds (3.6.11), p. 45, with
`j_r = d_r/2` and `m_r = i_r - d_r/2`. It is `0` unless the triple is admissible, the indices are
in range and `m = m₁ + m₂`. -/
@[expose]
def clebschGordan (d₁ d₂ d i₁ i₂ i : ℕ) : ℝ :=
  if IsTriad d₁ d₂ d ∧ i₁ ≤ d₁ ∧ i₂ ≤ d₂ ∧ i ≤ d ∧ 2 * i + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d then
    Real.sqrt (clebschGordanPrefactor d₁ d₂ d i₁ i₂ i) *
      ∑ z ∈ Finset.range ((d₁ + d₂ - d) / 2 + 1), clebschGordanTerm d₁ d₂ d i₁ i₂ z
  else 0

/-- The coefficient is the factorial sum on admissible indices and zero outside that range. -/
theorem clebschGordan_def (d₁ d₂ d i₁ i₂ i : ℕ) :
    clebschGordan d₁ d₂ d i₁ i₂ i =
      if IsTriad d₁ d₂ d ∧ i₁ ≤ d₁ ∧ i₂ ≤ d₂ ∧ i ≤ d ∧
          2 * i + d₁ + d₂ = 2 * i₁ + 2 * i₂ + d then
        Real.sqrt (clebschGordanPrefactor d₁ d₂ d i₁ i₂ i) *
          ∑ z ∈ Finset.range ((d₁ + d₂ - d) / 2 + 1), clebschGordanTerm d₁ d₂ d i₁ i₂ z
      else 0 :=
  rfl

/-- **Selection rule:** the coefficient vanishes for an inadmissible triple. -/
theorem clebschGordan_eq_zero_of_not_isTriad {d₁ d₂ d : ℕ} (h : ¬ IsTriad d₁ d₂ d)
    (i₁ i₂ i : ℕ) : clebschGordan d₁ d₂ d i₁ i₂ i = 0 := by
  simp [clebschGordan, h]

/-- **Selection rule:** the coefficient vanishes unless `m = m₁ + m₂` (Edmonds (3.5.4), p. 38).
-/
theorem clebschGordan_eq_zero_of_ne {d₁ d₂ d i₁ i₂ i : ℕ}
    (h : 2 * i + d₁ + d₂ ≠ 2 * i₁ + 2 * i₂ + d) : clebschGordan d₁ d₂ d i₁ i₂ i = 0 := by
  simp [clebschGordan, h]

/-- The coefficient vanishes if an index lies outside the weight range. -/
theorem clebschGordan_eq_zero_of_out_of_range {a b c i j k : ℕ}
    (h : ¬ (i ≤ a ∧ j ≤ b ∧ k ≤ c)) : clebschGordan a b c i j k = 0 := by
  rw [clebschGordan_def]
  exact ite_eq_right fun hh => h ⟨hh.2.1, hh.2.2.1, hh.2.2.2.1⟩

/-- The 3-j symbol `(j₁ j₂ j₃; m₁ m₂ m₃) = (-1)^{j₁-j₂-m₃} (2j₃+1)^{-1/2}
(j₁ m₁ j₂ m₂ | j₁ j₂ j₃, -m₃)` (Edmonds (3.7.3), p. 46; DLMF 34.1.1). The index of `-m₃` is
`d₃ - i₃`; `2d₃` is added to the exponent to keep it a natural number of the same parity. It is
`0` for `i₃ > d₃`. -/
@[expose]
def threeJ (d₁ d₂ d₃ i₁ i₂ i₃ : ℕ) : ℝ :=
  if i₃ ≤ d₃ then
    (-1) ^ ((d₁ + d₃ - d₂) / 2 + 2 * d₃ - i₃) / Real.sqrt (d₃ + 1) *
      clebschGordan d₁ d₂ d₃ i₁ i₂ (d₃ - i₃)
  else 0

/-- The Wigner 3-j symbol is the signed coefficient with the last weight reversed and the dimension
factor divided out. -/
theorem threeJ_def (d₁ d₂ d₃ i₁ i₂ i₃ : ℕ) :
    threeJ d₁ d₂ d₃ i₁ i₂ i₃ =
      if i₃ ≤ d₃ then
        (-1) ^ ((d₁ + d₃ - d₂) / 2 + 2 * d₃ - i₃) / Real.sqrt (d₃ + 1) *
          clebschGordan d₁ d₂ d₃ i₁ i₂ (d₃ - i₃)
      else 0 :=
  rfl

/-- The triangle coefficient `Δ(j₁ j₂ j₃)` of DLMF 34.2.5, for doubled spins. -/
@[expose]
def triangleCoefficient (d₁ d₂ d₃ : ℕ) : ℝ :=
  Real.sqrt ((((d₁ + d₂ - d₃) / 2).factorial * ((d₁ + d₃ - d₂) / 2).factorial *
    ((d₂ + d₃ - d₁) / 2).factorial : ℕ) / (((d₁ + d₂ + d₃) / 2 + 1).factorial : ℕ))

/-- The triangle coefficient is the ratio of the three triangle factorials to the total-degree
factorial. -/
theorem triangleCoefficient_def (d₁ d₂ d₃ : ℕ) :
    triangleCoefficient d₁ d₂ d₃ =
      Real.sqrt ((((d₁ + d₂ - d₃) / 2).factorial * ((d₁ + d₃ - d₂) / 2).factorial *
        ((d₂ + d₃ - d₁) / 2).factorial : ℕ) / (((d₁ + d₂ + d₃) / 2 + 1).factorial : ℕ)) :=
  rfl

/-- The triangle coefficient is nonnegative. -/
theorem triangleCoefficient_nonneg (d₁ d₂ d₃ : ℕ) : 0 ≤ triangleCoefficient d₁ d₂ d₃ :=
  Real.sqrt_nonneg _

end SFVK.ClebschGordan
