/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Hahn and Racah polynomials

Real-variable forms, by the terminating sums:

* `hahn N n α β x = Q_n(x; α, β, N) = ₃F₂(-n, n + α + β + 1, -x; α + 1, -N; 1)`, DLMF 18.20.5;
* `racahPolynomial n α β γ δ y = R_n(λ(y); α, β, γ, δ)
  = ₄F₃(-n, n + α + β + 1, -y, y + γ + δ + 1; α + 1, β + δ + 1, γ + 1; 1)`, with
  `λ(y) = y (y + γ + δ + 1)`, DLMF 18.26.3.

A vanishing denominator gives Lean's value `0` for that term; the theorems assume the
denominators nonzero. The complex forms of lean-DLMF are `DLMF.OrthogonalPolynomials.hahn` and
`DLMF.OrthogonalPolynomials.racah`, the latter in the variable `λ(y)`.
-/

public noncomputable section

namespace SFVK.ClebschGordan

/-- The Hahn polynomial `Q_n(x; α, β, N)` (DLMF 18.20.5), by the terminating sum. -/
@[expose]
def hahn (N n : ℕ) (α β x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval (n + α + β + 1) *
        (ascPochhammer ℝ k).eval (-x) /
      ((ascPochhammer ℝ k).eval (α + 1) * (ascPochhammer ℝ k).eval (-(N : ℝ)) * k.factorial)

/-- The Hahn polynomial is a finite terminating hypergeometric sum on the integer lattice. -/
theorem hahn_def (N n : ℕ) (α β x : ℝ) :
    hahn N n α β x =
      ∑ k ∈ Finset.range (n + 1),
        (ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval (n + α + β + 1) *
            (ascPochhammer ℝ k).eval (-x) /
          ((ascPochhammer ℝ k).eval (α + 1) * (ascPochhammer ℝ k).eval (-(N : ℝ)) *
            k.factorial) :=
  rfl

/-- `Q_0 = 1`. -/
theorem hahn_zero (N : ℕ) (α β x : ℝ) : hahn N 0 α β x = 1 := by
  simp [hahn]

/-- The Racah polynomial `R_n(λ(y); α, β, γ, δ)` (DLMF 18.26.3), as a function of `y`, by the
terminating sum. -/
@[expose]
def racahPolynomial (n : ℕ) (α β γ δ y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval (n + α + β + 1) *
        (ascPochhammer ℝ k).eval (-y) * (ascPochhammer ℝ k).eval (y + γ + δ + 1) /
      ((ascPochhammer ℝ k).eval (α + 1) * (ascPochhammer ℝ k).eval (β + δ + 1) *
        (ascPochhammer ℝ k).eval (γ + 1) * k.factorial)

/-- The Racah polynomial is written as a finite sum in the quadratic lattice coordinate. -/
theorem racahPolynomial_def (n : ℕ) (α β γ δ y : ℝ) :
    racahPolynomial n α β γ δ y =
      ∑ k ∈ Finset.range (n + 1),
        (ascPochhammer ℝ k).eval (-(n : ℝ)) * (ascPochhammer ℝ k).eval (n + α + β + 1) *
            (ascPochhammer ℝ k).eval (-y) * (ascPochhammer ℝ k).eval (y + γ + δ + 1) /
          ((ascPochhammer ℝ k).eval (α + 1) * (ascPochhammer ℝ k).eval (β + δ + 1) *
            (ascPochhammer ℝ k).eval (γ + 1) * k.factorial) :=
  rfl

/-- `R_0 = 1`. -/
theorem racahPolynomial_zero (α β γ δ y : ℝ) : racahPolynomial 0 α β γ δ y = 1 := by
  simp [racahPolynomial]

end SFVK.ClebschGordan
