/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.ClebschGordan.Basic.Coefficients

/-!
# The 6-j symbol and the recoupling coefficient

* `sixJ a b c d e f`: the 6-j symbol `{j₁ j₂ j₃; l₁ l₂ l₃}` for doubled spins
  `(a, b, c, d, e, f) = 2(j₁, j₂, j₃, l₁, l₂, l₃)`, by Racah's formula, Edmonds, *Angular
  Momentum in Quantum Mechanics*, (6.3.7), p. 99; DLMF 34.4.2.
* `recouplingCoefficient`: `((j₁ j₂) j₁₂, j₃; J M | j₁, (j₂ j₃) j₂₃; J M)`, Edmonds (6.1.4),
  p. 91, written with four Clebsch–Gordan coefficients.
-/

public noncomputable section

namespace SFVK.ClebschGordan

/-- The summand of Racah's formula (6.3.7) at the summation index `z`; `0` unless every
factorial argument is nonnegative. -/
@[expose]
def sixJTerm (a b c d e f z : ℕ) : ℝ :=
  if (a + b + c) / 2 ≤ z ∧ (a + e + f) / 2 ≤ z ∧ (d + b + f) / 2 ≤ z ∧
      (d + e + c) / 2 ≤ z ∧ z ≤ (b + c + e + f) / 2 ∧ z ≤ (c + a + f + d) / 2 then
    (-1) ^ z * ((z + 1).factorial : ℝ) /
      (((z - (a + b + c) / 2).factorial * (z - (a + e + f) / 2).factorial *
        (z - (d + b + f) / 2).factorial * (z - (d + e + c) / 2).factorial *
        ((a + b + d + e) / 2 - z).factorial * ((b + c + e + f) / 2 - z).factorial *
        ((c + a + f + d) / 2 - z).factorial : ℕ) : ℝ)
  else 0

/-- The 6-j symbol `{j₁ j₂ j₃; l₁ l₂ l₃}` by Racah's formula (Edmonds (6.3.7), p. 99;
DLMF 34.4.2), for doubled spins. It is `0` unless the four triples `(j₁ j₂ j₃)`, `(j₁ l₂ l₃)`,
`(l₁ j₂ l₃)`, `(l₁ l₂ j₃)` are admissible. -/
@[expose]
def sixJ (a b c d e f : ℕ) : ℝ :=
  if IsTriad a b c ∧ IsTriad a e f ∧ IsTriad d b f ∧ IsTriad d e c then
    triangleCoefficient a b c * triangleCoefficient a e f * triangleCoefficient d b f *
      triangleCoefficient d e c *
      ∑ z ∈ Finset.range ((a + b + d + e) / 2 + 1), sixJTerm a b c d e f z
  else 0

theorem sixJ_def (a b c d e f : ℕ) :
    sixJ a b c d e f =
      if IsTriad a b c ∧ IsTriad a e f ∧ IsTriad d b f ∧ IsTriad d e c then
        triangleCoefficient a b c * triangleCoefficient a e f * triangleCoefficient d b f *
          triangleCoefficient d e c *
          ∑ z ∈ Finset.range ((a + b + d + e) / 2 + 1), sixJTerm a b c d e f z
      else 0 :=
  rfl

theorem sixJ_eq_zero_of_not {a b c d e f : ℕ}
    (h : ¬ (IsTriad a b c ∧ IsTriad a e f ∧ IsTriad d b f ∧ IsTriad d e c)) :
    sixJ a b c d e f = 0 := by
  simp [sixJ_def, h]

/-- The recoupling coefficient `((j₁ j₂) j₁₂, j₃; J M | j₁, (j₂ j₃) j₂₃; J M)` of three spins
(Edmonds (6.1.4), p. 91), with `M = I - D/2`: the inner product of the two coupled vectors of
`V₁ ⊗ V₂ ⊗ V₃`, written in the product basis. -/
@[expose]
def recouplingCoefficient (d₁ d₂ d₃ d₁₂ d₂₃ D I : ℕ) : ℝ :=
  ∑ i₁ ∈ Finset.range (d₁ + 1), ∑ i₂ ∈ Finset.range (d₂ + 1), ∑ i₃ ∈ Finset.range (d₃ + 1),
    ∑ i₁₂ ∈ Finset.range (d₁₂ + 1), ∑ i₂₃ ∈ Finset.range (d₂₃ + 1),
      clebschGordan d₁ d₂ d₁₂ i₁ i₂ i₁₂ * clebschGordan d₁₂ d₃ D i₁₂ i₃ I *
        clebschGordan d₂ d₃ d₂₃ i₂ i₃ i₂₃ * clebschGordan d₁ d₂₃ D i₁ i₂₃ I

theorem recouplingCoefficient_def (d₁ d₂ d₃ d₁₂ d₂₃ D I : ℕ) :
    recouplingCoefficient d₁ d₂ d₃ d₁₂ d₂₃ D I =
      ∑ i₁ ∈ Finset.range (d₁ + 1), ∑ i₂ ∈ Finset.range (d₂ + 1), ∑ i₃ ∈ Finset.range (d₃ + 1),
        ∑ i₁₂ ∈ Finset.range (d₁₂ + 1), ∑ i₂₃ ∈ Finset.range (d₂₃ + 1),
          clebschGordan d₁ d₂ d₁₂ i₁ i₂ i₁₂ * clebschGordan d₁₂ d₃ D i₁₂ i₃ I *
            clebschGordan d₂ d₃ d₂₃ i₂ i₃ i₂₃ * clebschGordan d₁ d₂₃ D i₁ i₂₃ I :=
  rfl

end SFVK.ClebschGordan
