/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Miller's complex group `T₃` and its multiplier representation

Miller, *Lie Theory and Special Functions*, §3-1, (3.4)–(3.11), pp. 53–55: the group `T₃` in
the coordinates `(b, c, τ)`, with `(b, c, τ)(b', c', τ') = (b + e^τ b', c + e^{-τ} c', τ + τ')`,
acts on functions of `z` by `(A(g) f)(z) = exp(ω b z + ω c / z + m₀ τ) f(e^τ z)` (3.6), and its
matrix elements on the Laurent monomials `z^k` are the coefficients (3.11).

## Main definitions

* `SFVK.MotionGroups.T3`: the group `T₃`.
* `SFVK.MotionGroups.millerAction`: the multiplier representation (3.6).
* `SFVK.MotionGroups.millerMatrix`: the matrix elements (3.11).
* `SFVK.MotionGroups.besselJEntire`: the entire function `E_m(u²) = u^{-m} J_m(u)`.
-/

public noncomputable section

open Complex

namespace SFVK.MotionGroups

/-- Miller's group `T₃` in the coordinates `(b, c, τ)`. -/
@[ext]
structure T3 where
  /-- The coordinate of the raising direction. -/
  b : ℂ
  /-- The coordinate of the lowering direction. -/
  c : ℂ
  /-- The coordinate of the diagonal direction. -/
  τ : ℂ

namespace T3

instance : Mul T3 :=
  ⟨fun g h => ⟨g.b + Complex.exp g.τ * h.b, g.c + Complex.exp (-g.τ) * h.c, g.τ + h.τ⟩⟩

instance : One T3 := ⟨⟨0, 0, 0⟩⟩

instance : Inv T3 := ⟨fun g => ⟨-(Complex.exp (-g.τ) * g.b), -(Complex.exp g.τ * g.c), -g.τ⟩⟩

/-- The raising coordinate of a product in `T3`. -/
@[simp] theorem mul_b (g h : T3) : (g * h).b = g.b + Complex.exp g.τ * h.b := rfl

/-- The lowering coordinate of a product in `T3`. -/
@[simp] theorem mul_c (g h : T3) : (g * h).c = g.c + Complex.exp (-g.τ) * h.c := rfl

/-- The diagonal coordinate of a product in `T3`. -/
@[simp] theorem mul_τ (g h : T3) : (g * h).τ = g.τ + h.τ := rfl

/-- The raising coordinate of the identity in `T3`. -/
@[simp] theorem one_b : (1 : T3).b = 0 := rfl

/-- The lowering coordinate of the identity in `T3`. -/
@[simp] theorem one_c : (1 : T3).c = 0 := rfl

/-- The diagonal coordinate of the identity in `T3`. -/
@[simp] theorem one_τ : (1 : T3).τ = 0 := rfl

/-- The raising coordinate of the inverse in `T3`. -/
@[simp] theorem inv_b (g : T3) : g⁻¹.b = -(Complex.exp (-g.τ) * g.b) := rfl

/-- The lowering coordinate of the inverse in `T3`. -/
@[simp] theorem inv_c (g : T3) : g⁻¹.c = -(Complex.exp g.τ * g.c) := rfl

/-- The diagonal coordinate of the inverse in `T3`. -/
@[simp] theorem inv_τ (g : T3) : g⁻¹.τ = -g.τ := rfl

instance : Group T3 where
  mul_assoc g h l := by
    ext <;> simp only [mul_b, mul_c, mul_τ, Complex.exp_add, neg_add] <;> ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    ext
    · simp
    · simp
    · simp

end T3

/-- Miller's multiplier representation of `T₃`,
`(A(g) f)(z) = exp(ω b z + ω c / z + m₀ τ) f(e^τ z)` (Miller (3.6), p. 54). -/
@[expose]
def millerAction (ω m₀ : ℂ) (g : T3) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (ω * g.b * z + ω * g.c / z + m₀ * g.τ) * f (Complex.exp g.τ * z)

/-- Miller's `T₃` acts by an exponential multiplier and rescales the complex argument. -/
theorem millerAction_def (ω m₀ : ℂ) (g : T3) (f : ℂ → ℂ) (z : ℂ) :
    millerAction ω m₀ g f z =
      Complex.exp (ω * g.b * z + ω * g.c / z + m₀ * g.τ) * f (Complex.exp g.τ * z) :=
  rfl

/-- The representation law of Miller's model (Miller (3.7), p. 54). -/
theorem millerAction_mul (ω m₀ : ℂ) (g h : T3) (f : ℂ → ℂ) :
    millerAction ω m₀ (g * h) f = millerAction ω m₀ g (millerAction ω m₀ h f) := by
  funext z
  simp only [millerAction_def, T3.mul_b, T3.mul_c, T3.mul_τ]
  have hz : Complex.exp h.τ * (Complex.exp g.τ * z) = Complex.exp (g.τ + h.τ) * z := by
    rw [Complex.exp_add]
    ring
  rw [hz, ← mul_assoc, ← Complex.exp_add]
  congr 2
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
    ring
  · rw [Complex.exp_neg]
    field_simp
    ring

/-- The identity acts trivially in Miller's model. -/
@[simp]
theorem millerAction_one (ω m₀ : ℂ) (f : ℂ → ℂ) : millerAction ω m₀ 1 f = f := by
  funext z
  simp [millerAction]

/-- Miller's matrix elements (3.11), p. 55:
`A_{lk}(g) = e^{(k+m₀)τ} Σₛ (ωb)^{s+(l-k)⁺} (ωc)^{s+(k-l)⁺} / ((s+(l-k)⁺)! (s+(k-l)⁺)!)`. -/
@[expose]
def millerMatrix (ω m₀ : ℂ) (l k : ℤ) (g : T3) : ℂ :=
  Complex.exp ((k + m₀) * g.τ) *
    ∑' s : ℕ, (ω * g.b) ^ (s + (l - k).toNat) * (ω * g.c) ^ (s + (k - l).toNat) /
      (((s + (l - k).toNat).factorial : ℂ) * ((s + (k - l).toNat).factorial : ℂ))

/-- The matrix entry is the Laurent coefficient in Miller's `T₃` model, with the diagonal
exponential factor. -/
theorem millerMatrix_def (ω m₀ : ℂ) (l k : ℤ) (g : T3) :
    millerMatrix ω m₀ l k g =
      Complex.exp ((k + m₀) * g.τ) *
        ∑' s : ℕ, (ω * g.b) ^ (s + (l - k).toNat) * (ω * g.c) ^ (s + (k - l).toNat) /
          (((s + (l - k).toNat).factorial : ℂ) * ((s + (k - l).toNat).factorial : ℂ)) :=
  rfl

/-- The entire function `E_m(y) = Σₖ (-y/4)^k / (2^m k! Γ(m+k+1))`, with `E_m(u²) = u^{-m} J_m(u)`
(the function of Miller (3.36)–(3.38), pp. 64–65). -/
@[expose]
def besselJEntire (m y : ℂ) : ℂ :=
  ∑' k : ℕ, (-y / 4) ^ k / ((2 : ℂ) ^ m * (k.factorial : ℂ) * Complex.Gamma (m + k + 1))

/-- The entire Bessel normalization is the power series in the squared argument with reciprocal
Gamma coefficients. -/
theorem besselJEntire_def (m y : ℂ) :
    besselJEntire m y =
      ∑' k : ℕ, (-y / 4) ^ k / ((2 : ℂ) ^ m * (k.factorial : ℂ) * Complex.Gamma (m + k + 1)) :=
  rfl

end SFVK.MotionGroups
