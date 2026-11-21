/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Basic

/-!
# Affine, triangular, oscillator and Miller groups in coordinates

The `ax + b` group (`AxB`), the group of real triangular matrices
`[[1, a, b], [0, e^τ, d], [0, 0, 1]]` (`TriangularGroup`) of Vilenkin–Klimyk, *Representation of
Lie Groups and Special Functions*, Vol. 1, §5.1.1 (1), p. 207, with its one-parameter subgroups,
the oscillator group (`Oscillator`) with the law of the oscillator matrix of Klimyk–Vilenkin
(corrected form) and an unreduced real angle, Miller's complex group `G(0, 1)` (`MillerGroup`,
Miller, *Lie Theory and Special Functions*, §4-2, p. 86), and the embeddings of Tau Ceti's
Heisenberg group into the triangular and oscillator groups. Section numbers `§x.y` refer to
the roadmap `Roadmaps/AffineHeisenbergGroups/README.md`. Everything here is fully proved.
-/

@[expose] public section

noncomputable section

namespace SFVK.AffineHeisenberg

open Complex
open scoped Real ComplexConjugate

/-- SpecialFunctionsGroupModels §0.2. The oscillator-group matrix `s(w, α, δ)`. -/
def oscillatorMatrix (w : ℂ) (α δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, Complex.exp (-(α : ℂ) * Complex.I) * conj w / 2,
      (δ : ℂ) * Complex.I - (Complex.normSq w : ℂ) / 8;
    0, Complex.exp (-(α : ℂ) * Complex.I), -w / 2;
    0, 0, 1]

/-- SpecialFunctionsGroupModels §0.2. The `ax + b` group. -/
@[ext]
structure AxB where
  /-- The dilation `a > 0`. -/
  a : ℝ
  /-- The translation `b`. -/
  b : ℝ
  a_pos : 0 < a

namespace AxB

instance : Mul AxB := ⟨fun g h => ⟨g.a * h.a, g.a * h.b + g.b, mul_pos g.a_pos h.a_pos⟩⟩

instance : One AxB := ⟨⟨1, 0, one_pos⟩⟩

instance : Inv AxB := ⟨fun g => ⟨g.a⁻¹, -(g.a⁻¹ * g.b), inv_pos.2 g.a_pos⟩⟩

@[simp] theorem mul_a (g h : AxB) : (g * h).a = g.a * h.a := rfl
@[simp] theorem mul_b (g h : AxB) : (g * h).b = g.a * h.b + g.b := rfl
@[simp] theorem one_a : (1 : AxB).a = 1 := rfl
@[simp] theorem one_b : (1 : AxB).b = 0 := rfl
@[simp] theorem inv_a (g : AxB) : g⁻¹.a = g.a⁻¹ := rfl
@[simp] theorem inv_b (g : AxB) : g⁻¹.b = -(g.a⁻¹ * g.b) := rfl

instance : Group AxB where
  mul_assoc g h k := by ext <;> simp <;> ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by ext <;> simp [g.a_pos.ne']

/-- Function-space models §2.4 convention. `g • x = x / a`. -/
instance : MulAction AxB ℝ where
  smul g x := x / g.a
  one_smul x := div_one x
  mul_smul g h x := by
    show x / (g.a * h.a) = x / h.a / g.a
    rw [div_div, mul_comm]

end AxB

/-- §0.1. The triangular group, coordinates `(a, b, d, τ)` of the matrix
`[[1, a, b], [0, e^τ, d], [0, 0, 1]]`. -/
@[ext]
structure TriangularGroup where
  /-- The `(1, 2)` entry. -/
  a : ℝ
  /-- The `(1, 3)` entry. -/
  b : ℝ
  /-- The `(2, 3)` entry. -/
  d : ℝ
  /-- The logarithm of the `(2, 2)` entry. -/
  τ : ℝ

namespace TriangularGroup

instance : Mul TriangularGroup :=
  ⟨fun g h => ⟨h.a + g.a * Real.exp h.τ, g.b + h.b + g.a * h.d, g.d + Real.exp g.τ * h.d,
    g.τ + h.τ⟩⟩

instance : One TriangularGroup := ⟨⟨0, 0, 0, 0⟩⟩

instance : Inv TriangularGroup :=
  ⟨fun g => ⟨-(g.a * Real.exp (-g.τ)), g.a * g.d * Real.exp (-g.τ) - g.b,
    -(g.d * Real.exp (-g.τ)), -g.τ⟩⟩

@[simp] theorem mul_a (g h : TriangularGroup) : (g * h).a = h.a + g.a * Real.exp h.τ := rfl
@[simp] theorem mul_b (g h : TriangularGroup) : (g * h).b = g.b + h.b + g.a * h.d := rfl
@[simp] theorem mul_d (g h : TriangularGroup) : (g * h).d = g.d + Real.exp g.τ * h.d := rfl
@[simp] theorem mul_τ (g h : TriangularGroup) : (g * h).τ = g.τ + h.τ := rfl
@[simp] theorem one_a : (1 : TriangularGroup).a = 0 := rfl
@[simp] theorem one_b : (1 : TriangularGroup).b = 0 := rfl
@[simp] theorem one_d : (1 : TriangularGroup).d = 0 := rfl
@[simp] theorem one_τ : (1 : TriangularGroup).τ = 0 := rfl
@[simp] theorem inv_a (g : TriangularGroup) : g⁻¹.a = -(g.a * Real.exp (-g.τ)) := rfl
@[simp] theorem inv_b (g : TriangularGroup) : g⁻¹.b = g.a * g.d * Real.exp (-g.τ) - g.b := rfl
@[simp] theorem inv_d (g : TriangularGroup) : g⁻¹.d = -(g.d * Real.exp (-g.τ)) := rfl
@[simp] theorem inv_τ (g : TriangularGroup) : g⁻¹.τ = -g.τ := rfl

instance : Group TriangularGroup where
  mul_assoc g h k := by
    ext <;> simp [Real.exp_add] <;> ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    ext <;> simp [Real.exp_neg] <;> field_simp <;> ring

/-- §0.1. The matrix `[[1, a, b], [0, e^τ, d], [0, 0, 1]]`. -/
def toMatrix (g : TriangularGroup) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, g.a, g.b; 0, Real.exp g.τ, g.d; 0, 0, 1]

/-- §0.1. The triangular group acts on `ℝ` by `g • x = e^{-τ}(x - a)`, so that
`g⁻¹ • x = e^τ x + a`. -/
instance : MulAction TriangularGroup ℝ where
  smul g x := Real.exp (-g.τ) * (x - g.a)
  one_smul x := by
    show Real.exp (-0) * (x - 0) = x
    simp
  mul_smul g h x := by
    show Real.exp (-(g.τ + h.τ)) * (x - (h.a + g.a * Real.exp h.τ)) =
      Real.exp (-g.τ) * (Real.exp (-h.τ) * (x - h.a) - g.a)
    rw [neg_add, Real.exp_add]
    have : Real.exp (-h.τ) * Real.exp h.τ = 1 := by rw [← Real.exp_add]; simp
    linear_combination (-(Real.exp (-g.τ) * g.a)) * this

end TriangularGroup

open TriangularGroup

/-- §0.1. `g_+(t) = (t, 0, 0, 0)`. -/
def gPlus (t : ℝ) : TriangularGroup := ⟨t, 0, 0, 0⟩

/-- §0.1. `g_-(t) = (0, 0, t, 0)`. -/
def gMinus (t : ℝ) : TriangularGroup := ⟨0, 0, t, 0⟩

/-- §0.1. The central element `z(t) = (0, t, 0, 0)`. -/
def centreElt (t : ℝ) : TriangularGroup := ⟨0, t, 0, 0⟩

/-- §0.1. The diagonal element `ε(t) = (0, 0, 0, t)`. -/
def dilation (t : ℝ) : TriangularGroup := ⟨0, 0, 0, t⟩

/-- §0.1. `g_1(t) = [[1, t, t²/2], [0, 1, t], [0, 0, 1]]`. -/
def gOne (t : ℝ) : TriangularGroup := ⟨t, t ^ 2 / 2, t, 0⟩

/-- §0.1. `g_2(t) = [[1, -t, -t²/2], [0, 1, t], [0, 0, 1]]`. -/
def gTwo (t : ℝ) : TriangularGroup := ⟨-t, -(t ^ 2 / 2), t, 0⟩

/-- §0.1. The Heisenberg group as the subgroup `τ = 0`: `(x, y, z) ↦ (x, z, y, 0)`. -/
def heisenbergToTriangular : TauCeti.HeisenbergGroup ℝ →* TriangularGroup where
  toFun p := ⟨p.x, p.z, p.y, 0⟩
  map_one' := by ext <;> simp
  map_mul' p q := by ext <;> simp [add_comm]

/-- §0.2. The oscillator group: coordinates `(w, α, δ)` with real, unreduced angle `α`. -/
@[ext]
structure Oscillator where
  /-- The translation part. -/
  w : ℂ
  /-- The rotation angle. -/
  α : ℝ
  /-- The central coordinate. -/
  δ : ℝ

/-- §0.2. The rotation factor `e^{-iα}`. -/
def rotFactor (α : ℝ) : ℂ := Complex.exp (-(α : ℂ) * Complex.I)

theorem rotFactor_add (α β : ℝ) : rotFactor (α + β) = rotFactor α * rotFactor β := by
  simp only [rotFactor, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rotFactor_mul_conj (α : ℝ) : rotFactor α * conj (rotFactor α) = 1 := by
  rw [Complex.mul_conj, rotFactor, Complex.normSq_eq_norm_sq]
  have : -(α : ℂ) * Complex.I = ((-α : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]
  simp

theorem rotFactor_zero : rotFactor 0 = 1 := by simp [rotFactor]

namespace Oscillator

instance : Mul Oscillator :=
  ⟨fun g h => ⟨g.w + rotFactor g.α * h.w, g.α + h.α,
    g.δ + h.δ - (rotFactor g.α * conj g.w * h.w).im / 4⟩⟩

instance : One Oscillator := ⟨⟨0, 0, 0⟩⟩

instance : Inv Oscillator := ⟨fun g => ⟨-(rotFactor (-g.α) * g.w), -g.α, -g.δ⟩⟩

@[simp] theorem mul_w (g h : Oscillator) : (g * h).w = g.w + rotFactor g.α * h.w := rfl
@[simp] theorem mul_α (g h : Oscillator) : (g * h).α = g.α + h.α := rfl
@[simp] theorem mul_δ (g h : Oscillator) :
    (g * h).δ = g.δ + h.δ - (rotFactor g.α * conj g.w * h.w).im / 4 := rfl
@[simp] theorem one_w : (1 : Oscillator).w = 0 := rfl
@[simp] theorem one_α : (1 : Oscillator).α = 0 := rfl
@[simp] theorem one_δ : (1 : Oscillator).δ = 0 := rfl
@[simp] theorem inv_w (g : Oscillator) : g⁻¹.w = -(rotFactor (-g.α) * g.w) := rfl
@[simp] theorem inv_α (g : Oscillator) : g⁻¹.α = -g.α := rfl
@[simp] theorem inv_δ (g : Oscillator) : g⁻¹.δ = -g.δ := rfl

instance : Group Oscillator where
  mul_assoc g h k := by
    have key : rotFactor (g.α + h.α) * conj (g.w + rotFactor g.α * h.w) * k.w =
        rotFactor (g.α + h.α) * conj g.w * k.w + rotFactor h.α * conj h.w * k.w := by
      rw [map_add, map_mul, rotFactor_add]
      linear_combination (rotFactor h.α * conj h.w * k.w) * rotFactor_mul_conj g.α
    ext
    · simp only [mul_w, mul_α, rotFactor_add]; ring
    · simp only [mul_α]; ring
    · simp only [mul_δ, mul_w, mul_α]
      rw [key]
      simp only [mul_add, Complex.add_im, rotFactor_add]
      ring_nf
  one_mul g := by ext <;> simp [rotFactor_zero]
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    have h1 : rotFactor (-g.α) * rotFactor g.α = 1 := by
      rw [← rotFactor_add]; simp [rotFactor_zero]
    have h2 : (rotFactor (-g.α) * conj (-(rotFactor (-g.α) * g.w)) * g.w).im = 0 := by
      rw [map_neg, map_mul, show rotFactor (-g.α) * -(conj (rotFactor (-g.α)) * conj g.w) * g.w
        = -((rotFactor (-g.α) * conj (rotFactor (-g.α))) * (conj g.w * g.w)) by ring,
        rotFactor_mul_conj, one_mul, ← Complex.normSq_eq_conj_mul_self]
      simp
    ext
    · simp only [mul_w, inv_w, inv_α, one_w]
      linear_combination (-g.w) * h1 + g.w * h1
    · simp
    · simp only [mul_δ, inv_δ, inv_w, inv_α, one_δ, h2]; ring

/-- §0.2. The matrix realization `oscillatorMatrix w α δ`. -/
def toMatrix (g : Oscillator) : Matrix (Fin 3) (Fin 3) ℂ := oscillatorMatrix g.w g.α g.δ

/-- §4.1. `Oscillator` acts on `ℂ` by `g • ζ = e^{-iα} ζ - w/√2`, so that
`g⁻¹ • ζ = e^{iα}(ζ + w/√2)`. -/
instance : MulAction Oscillator ℂ where
  smul g ζ := rotFactor g.α * ζ - g.w / (Real.sqrt 2 : ℂ)
  one_smul ζ := by
    show rotFactor 0 * ζ - 0 / (Real.sqrt 2 : ℂ) = ζ
    simp [rotFactor_zero]
  mul_smul g h ζ := by
    show rotFactor (g.α + h.α) * ζ - (g.w + rotFactor g.α * h.w) / (Real.sqrt 2 : ℂ) =
      rotFactor g.α * (rotFactor h.α * ζ - h.w / (Real.sqrt 2 : ℂ)) - g.w / (Real.sqrt 2 : ℂ)
    rw [rotFactor_add]
    ring

end Oscillator

/-- §0.2. The Heisenberg group in the oscillator group:
`(x, y, z) ↦ (x + iy, 0, -(z - xy/2)/2)`. -/
def heisenbergToOscillator : TauCeti.HeisenbergGroup ℝ →* Oscillator where
  toFun p := ⟨⟨p.x, p.y⟩, 0, -((p.z - p.x * p.y / 2) / 2)⟩
  map_one' := by
    ext
    · apply Complex.ext <;> simp
    · simp
    · simp
  map_mul' p q := by
    ext
    · apply Complex.ext <;> simp [rotFactor_zero]
    · simp
    · simp [rotFactor_zero]; ring

/-- §5.1. Miller's complex group `G(0, 1)` with coordinates `(a, b, c, τ)`. -/
@[ext]
structure MillerGroup where
  /-- The central coordinate. -/
  a : ℂ
  /-- The raising coordinate. -/
  b : ℂ
  /-- The lowering coordinate. -/
  c : ℂ
  /-- The diagonal coordinate. -/
  τ : ℂ

namespace MillerGroup

instance : Mul MillerGroup :=
  ⟨fun g h => ⟨g.a + h.a + Complex.exp g.τ * g.c * h.b, g.b + Complex.exp g.τ * h.b,
    g.c + Complex.exp (-g.τ) * h.c, g.τ + h.τ⟩⟩

instance : One MillerGroup := ⟨⟨0, 0, 0, 0⟩⟩

instance : Inv MillerGroup :=
  ⟨fun g => ⟨g.c * g.b - g.a, -(Complex.exp (-g.τ) * g.b), -(Complex.exp g.τ * g.c), -g.τ⟩⟩

@[simp] theorem mul_a (g h : MillerGroup) :
    (g * h).a = g.a + h.a + Complex.exp g.τ * g.c * h.b := rfl
@[simp] theorem mul_b (g h : MillerGroup) : (g * h).b = g.b + Complex.exp g.τ * h.b := rfl
@[simp] theorem mul_c (g h : MillerGroup) : (g * h).c = g.c + Complex.exp (-g.τ) * h.c := rfl
@[simp] theorem mul_τ (g h : MillerGroup) : (g * h).τ = g.τ + h.τ := rfl
@[simp] theorem one_a : (1 : MillerGroup).a = 0 := rfl
@[simp] theorem one_b : (1 : MillerGroup).b = 0 := rfl
@[simp] theorem one_c : (1 : MillerGroup).c = 0 := rfl
@[simp] theorem one_τ : (1 : MillerGroup).τ = 0 := rfl
@[simp] theorem inv_a (g : MillerGroup) : g⁻¹.a = g.c * g.b - g.a := rfl
@[simp] theorem inv_b (g : MillerGroup) : g⁻¹.b = -(Complex.exp (-g.τ) * g.b) := rfl
@[simp] theorem inv_c (g : MillerGroup) : g⁻¹.c = -(Complex.exp g.τ * g.c) := rfl
@[simp] theorem inv_τ (g : MillerGroup) : g⁻¹.τ = -g.τ := rfl

instance : Group MillerGroup where
  mul_assoc g h k := by
    have h1 : Complex.exp g.τ * Complex.exp (-g.τ) = 1 := by rw [← Complex.exp_add]; simp
    ext
    · simp only [mul_a, mul_b, mul_c, mul_τ, Complex.exp_add]
      linear_combination (Complex.exp h.τ * h.c * k.b) * h1
    · simp only [mul_b, mul_τ, Complex.exp_add]; ring
    · simp only [mul_c, mul_τ, neg_add, Complex.exp_add]; ring
    · simp only [mul_τ]; ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    have h0 : Complex.exp (-g.τ) * Complex.exp g.τ = 1 := by rw [← Complex.exp_add]; simp
    ext
    · simp only [mul_a, inv_a, inv_c, inv_τ, one_a]
      linear_combination (-(g.c * g.b)) * h0
    · simp only [mul_b, inv_b, inv_τ, one_b]; ring
    · simp only [mul_c, inv_c, inv_τ, neg_neg, one_c]; ring
    · simp

end MillerGroup

/-- The real points of `G(0, 1)` in the triangular group: `(a, b, c, τ) ↦ (e^τ c, a, b, τ)`. -/
def millerToTriangular (a b c τ : ℝ) : TriangularGroup := ⟨Real.exp τ * c, a, b, τ⟩

end SFVK.AffineHeisenberg
