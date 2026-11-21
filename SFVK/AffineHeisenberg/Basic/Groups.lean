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
the roadmap `Roadmaps/AffineHeisenbergGroups/README.md`. The coordinate fields use the
letters of the corresponding matrix entries. The group laws use descriptive lemma names.
-/

public section

noncomputable section

namespace SFVK.AffineHeisenberg

open Complex
open scoped Real ComplexConjugate

/-- SpecialFunctionsGroupModels §0.2. The oscillator-group matrix `s(w, α, δ)`. -/
@[expose]
def oscillatorMatrix (w : ℂ) (α δ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, Complex.exp (-(α : ℂ) * Complex.I) * conj w / 2,
      (δ : ℂ) * Complex.I - (Complex.normSq w : ℂ) / 8;
    0, Complex.exp (-(α : ℂ) * Complex.I), -w / 2;
    0, 0, 1]

/-- The oscillator matrix in the coordinates `(w, α, δ)`. -/
theorem oscillatorMatrix_def (w : ℂ) (α δ : ℝ) :
    oscillatorMatrix w α δ =
      !![1, Complex.exp (-(α : ℂ) * Complex.I) * conj w / 2,
        (δ : ℂ) * Complex.I - (Complex.normSq w : ℂ) / 8;
      0, Complex.exp (-(α : ℂ) * Complex.I), -w / 2;
      0, 0, 1] :=
  rfl

/-- SpecialFunctionsGroupModels §0.2. The `ax + b` group. -/
@[ext]
structure AxB where
  /-- The dilation `a > 0`. -/
  a : ℝ
  /-- The translation `b`. -/
  b : ℝ
  /-- The dilation is strictly positive. -/
  dilation_pos : 0 < a

namespace AxB

instance : Mul AxB :=
  ⟨fun g h => ⟨g.a * h.a, g.a * h.b + g.b, mul_pos g.dilation_pos h.dilation_pos⟩⟩

instance : One AxB := ⟨⟨1, 0, one_pos⟩⟩

instance : Inv AxB := ⟨fun g => ⟨g.a⁻¹, -(g.a⁻¹ * g.b), inv_pos.2 g.dilation_pos⟩⟩

/-- The positive dilation of a product in `AxB`. -/
@[simp] theorem dilation_mul (g h : AxB) : (g * h).a = g.a * h.a := rfl

/-- The translation of a product in `AxB`. -/
@[simp] theorem translation_mul (g h : AxB) : (g * h).b = g.a * h.b + g.b := rfl

/-- The positive dilation of the identity in `AxB`. -/
@[simp] theorem dilation_one : (1 : AxB).a = 1 := rfl

/-- The translation of the identity in `AxB`. -/
@[simp] theorem translation_one : (1 : AxB).b = 0 := rfl

/-- The positive dilation of the inverse in `AxB`. -/
@[simp] theorem dilation_inv (g : AxB) : g⁻¹.a = g.a⁻¹ := rfl

/-- The translation of the inverse in `AxB`. -/
@[simp] theorem translation_inv (g : AxB) : g⁻¹.b = -(g.a⁻¹ * g.b) := rfl

instance : Group AxB where
  mul_assoc g h k := by ext <;> simp <;> ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by ext <;> simp [g.dilation_pos.ne']

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

/-- The upper left off-diagonal entry of a product in `TriangularGroup`. -/
@[simp]
theorem translation_mul (g h : TriangularGroup) : (g * h).a = h.a + g.a * Real.exp h.τ := rfl

/-- The central entry of a product in `TriangularGroup`. -/
@[simp]
theorem centralCoordinate_mul (g h : TriangularGroup) : (g * h).b = g.b + h.b + g.a * h.d := rfl

/-- The upper right off-diagonal entry in the second row of a product in `TriangularGroup`. -/
@[simp] theorem modulation_mul (g h : TriangularGroup) : (g * h).d = g.d + Real.exp g.τ * h.d := rfl

/-- The logarithmic dilation of a product in `TriangularGroup`. -/
@[simp] theorem logDilation_mul (g h : TriangularGroup) : (g * h).τ = g.τ + h.τ := rfl

/-- The upper left off-diagonal entry of the identity in `TriangularGroup`. -/
@[simp] theorem translation_one : (1 : TriangularGroup).a = 0 := rfl

/-- The central entry of the identity in `TriangularGroup`. -/
@[simp] theorem centralCoordinate_one : (1 : TriangularGroup).b = 0 := rfl

/-- The upper right off-diagonal entry in the second row of the identity in `TriangularGroup`. -/
@[simp] theorem modulation_one : (1 : TriangularGroup).d = 0 := rfl

/-- The logarithmic dilation of the identity in `TriangularGroup`. -/
@[simp] theorem logDilation_one : (1 : TriangularGroup).τ = 0 := rfl

/-- The upper left off-diagonal entry of the inverse in `TriangularGroup`. -/
@[simp] theorem translation_inv (g : TriangularGroup) : g⁻¹.a = -(g.a * Real.exp (-g.τ)) := rfl

/-- The central entry of the inverse in `TriangularGroup`. -/
@[simp]
theorem centralCoordinate_inv (g : TriangularGroup) :
    g⁻¹.b = g.a * g.d * Real.exp (-g.τ) - g.b := rfl

/-- The upper right off-diagonal entry in the second row of the inverse in `TriangularGroup`. -/
@[simp] theorem modulation_inv (g : TriangularGroup) : g⁻¹.d = -(g.d * Real.exp (-g.τ)) := rfl

/-- The logarithmic dilation of the inverse in `TriangularGroup`. -/
@[simp] theorem logDilation_inv (g : TriangularGroup) : g⁻¹.τ = -g.τ := rfl

instance : Group TriangularGroup where
  mul_assoc g h k := by
    ext <;> simp [Real.exp_add] <;> ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    ext <;> simp [Real.exp_neg] <;> field_simp <;> ring

/-- §0.1. The matrix `[[1, a, b], [0, e^τ, d], [0, 0, 1]]`. -/
@[expose]
def toMatrix (g : TriangularGroup) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, g.a, g.b; 0, Real.exp g.τ, g.d; 0, 0, 1]

/-- The group element as an upper triangular matrix. -/
theorem toMatrix_def (g : TriangularGroup) :
    toMatrix g = !![1, g.a, g.b; 0, Real.exp g.τ, g.d; 0, 0, 1] :=
  rfl

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
@[expose]
def translationElement (t : ℝ) : TriangularGroup := ⟨t, 0, 0, 0⟩

/-- The subgroup in the translation coordinate. -/
theorem translationElement_def (t : ℝ) :
    translationElement t = (⟨t, 0, 0, 0⟩ : TriangularGroup) :=
  rfl

/-- §0.1. `g_-(t) = (0, 0, t, 0)`. -/
@[expose]
def modulationElement (t : ℝ) : TriangularGroup := ⟨0, 0, t, 0⟩

/-- The subgroup in the modulation coordinate. -/
theorem modulationElement_def (t : ℝ) :
    modulationElement t = (⟨0, 0, t, 0⟩ : TriangularGroup) :=
  rfl

/-- §0.1. The central element `z(t) = (0, t, 0, 0)`. -/
@[expose]
def centralElement (t : ℝ) : TriangularGroup := ⟨0, t, 0, 0⟩

/-- The subgroup in the central coordinate. -/
theorem centralElement_def (t : ℝ) :
    centralElement t = (⟨0, t, 0, 0⟩ : TriangularGroup) :=
  rfl

/-- §0.1. The diagonal element `ε(t) = (0, 0, 0, t)`. -/
@[expose]
def dilation (t : ℝ) : TriangularGroup := ⟨0, 0, 0, t⟩

/-- The subgroup in the log-dilation coordinate. -/
theorem dilation_def (t : ℝ) :
    dilation t = (⟨0, 0, 0, t⟩ : TriangularGroup) :=
  rfl

/-- §0.1. `g_1(t) = [[1, t, t²/2], [0, 1, t], [0, 0, 1]]`. -/
@[expose]
def equalTranslationModulation (t : ℝ) : TriangularGroup := ⟨t, t ^ 2 / 2, t, 0⟩

/-- The subgroup with equal translation and modulation coordinates. -/
theorem equalTranslationModulation_def (t : ℝ) :
    equalTranslationModulation t = (⟨t, t ^ 2 / 2, t, 0⟩ : TriangularGroup) :=
  rfl

/-- §0.1. `g_2(t) = [[1, -t, -t²/2], [0, 1, t], [0, 0, 1]]`. -/
@[expose]
def oppositeTranslationModulation (t : ℝ) : TriangularGroup := ⟨-t, -(t ^ 2 / 2), t, 0⟩

/-- The subgroup with opposite translation and modulation coordinates. -/
theorem oppositeTranslationModulation_def (t : ℝ) :
    oppositeTranslationModulation t = (⟨-t, -(t ^ 2 / 2), t, 0⟩ : TriangularGroup) :=
  rfl

/-- §0.1. The Heisenberg group as the subgroup `τ = 0`: `(x, y, z) ↦ (x, z, y, 0)`. -/
@[expose]
def heisenbergToTriangular : TauCeti.HeisenbergGroup ℝ →* TriangularGroup where
  toFun p := ⟨p.x, p.z, p.y, 0⟩
  map_one' := by ext <;> simp
  map_mul' p q := by ext <;> simp [add_comm]

/-- The coordinates of the Heisenberg group homomorphism into the triangular group. -/
theorem heisenbergToTriangular_apply (g : TauCeti.HeisenbergGroup ℝ) :
    heisenbergToTriangular g = ⟨g.x, g.z, g.y, 0⟩ :=
  rfl

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
@[expose]
def rotationFactor (α : ℝ) : ℂ := Complex.exp (-(α : ℂ) * Complex.I)

/-- The rotation factor uses the negative angular coordinate. -/
theorem rotationFactor_def (α : ℝ) :
    rotationFactor α = Complex.exp (-(α : ℂ) * Complex.I) :=
  rfl

/-- Adding angles multiplies the rotation factors. -/
theorem rotationFactor_add (α β : ℝ) :
    rotationFactor (α + β) = rotationFactor α * rotationFactor β := by
  simp only [rotationFactor, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A rotation factor times its complex conjugate is one. -/
theorem rotationFactor_mul_conj (α : ℝ) : rotationFactor α * conj (rotationFactor α) = 1 := by
  rw [Complex.mul_conj, rotationFactor, Complex.normSq_eq_norm_sq]
  have : -(α : ℂ) * Complex.I = ((-α : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]
  simp

/-- The rotation factor at angle zero is one. -/
theorem rotationFactor_zero : rotationFactor 0 = 1 := by simp [rotationFactor]

namespace Oscillator

instance : Mul Oscillator :=
  ⟨fun g h => ⟨g.w + rotationFactor g.α * h.w, g.α + h.α,
    g.δ + h.δ - (rotationFactor g.α * conj g.w * h.w).im / 4⟩⟩

instance : One Oscillator := ⟨⟨0, 0, 0⟩⟩

instance : Inv Oscillator := ⟨fun g => ⟨-(rotationFactor (-g.α) * g.w), -g.α, -g.δ⟩⟩

/-- The complex displacement of a product in `Oscillator`. -/
@[simp]
theorem translation_mul (g h : Oscillator) : (g * h).w = g.w + rotationFactor g.α * h.w := rfl

/-- The rotation angle of a product in `Oscillator`. -/
@[simp] theorem angle_mul (g h : Oscillator) : (g * h).α = g.α + h.α := rfl

/-- The central coordinate of a product in `Oscillator`. -/
@[simp] theorem centralCoordinate_mul (g h : Oscillator) :
    (g * h).δ = g.δ + h.δ - (rotationFactor g.α * conj g.w * h.w).im / 4 := rfl

/-- The complex displacement of the identity in `Oscillator`. -/
@[simp] theorem translation_one : (1 : Oscillator).w = 0 := rfl

/-- The rotation angle of the identity in `Oscillator`. -/
@[simp] theorem angle_one : (1 : Oscillator).α = 0 := rfl

/-- The central coordinate of the identity in `Oscillator`. -/
@[simp] theorem centralCoordinate_one : (1 : Oscillator).δ = 0 := rfl

/-- The complex displacement of the inverse in `Oscillator`. -/
@[simp] theorem translation_inv (g : Oscillator) : g⁻¹.w = -(rotationFactor (-g.α) * g.w) := rfl

/-- The rotation angle of the inverse in `Oscillator`. -/
@[simp] theorem angle_inv (g : Oscillator) : g⁻¹.α = -g.α := rfl

/-- The central coordinate of the inverse in `Oscillator`. -/
@[simp] theorem centralCoordinate_inv (g : Oscillator) : g⁻¹.δ = -g.δ := rfl

instance : Group Oscillator where
  mul_assoc g h k := by
    have key : rotationFactor (g.α + h.α) * conj (g.w + rotationFactor g.α * h.w) * k.w =
        rotationFactor (g.α + h.α) * conj g.w * k.w + rotationFactor h.α * conj h.w * k.w := by
      rw [map_add, map_mul, rotationFactor_add]
      linear_combination (rotationFactor h.α * conj h.w * k.w) * rotationFactor_mul_conj g.α
    ext
    · simp only [translation_mul, angle_mul, rotationFactor_add]; ring
    · simp only [angle_mul]; ring
    · simp only [centralCoordinate_mul, translation_mul, angle_mul]
      rw [key]
      simp only [mul_add, Complex.add_im, rotationFactor_add]
      ring_nf
  one_mul g := by ext <;> simp [rotationFactor_zero]
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    have h1 : rotationFactor (-g.α) * rotationFactor g.α = 1 := by
      rw [← rotationFactor_add]; simp [rotationFactor_zero]
    have h2 : (rotationFactor (-g.α) * conj (-(rotationFactor (-g.α) * g.w)) * g.w).im = 0 := by
      rw [map_neg, map_mul,
        show rotationFactor (-g.α) * -(conj (rotationFactor (-g.α)) * conj g.w) * g.w
        = -((rotationFactor (-g.α) * conj (rotationFactor (-g.α))) * (conj g.w * g.w)) by ring,
        rotationFactor_mul_conj, one_mul, ← Complex.normSq_eq_conj_mul_self]
      simp
    ext
    · simp only [translation_mul, translation_inv, angle_inv, translation_one]
      linear_combination (-g.w) * h1 + g.w * h1
    · simp
    · simp only [centralCoordinate_mul, centralCoordinate_inv, translation_inv, angle_inv,
      centralCoordinate_one, h2]; ring

/-- §0.2. The matrix realization `oscillatorMatrix w α δ`. -/
@[expose]
def toMatrix (g : Oscillator) : Matrix (Fin 3) (Fin 3) ℂ := oscillatorMatrix g.w g.α g.δ

/-- The matrix of an oscillator group element in its three coordinates. -/
theorem toMatrix_def (g : Oscillator) :
    toMatrix g = oscillatorMatrix g.w g.α g.δ :=
  rfl

/-- §4.1. `Oscillator` acts on `ℂ` by `g • ζ = e^{-iα} ζ - w/√2`, so that
`g⁻¹ • ζ = e^{iα}(ζ + w/√2)`. -/
instance : MulAction Oscillator ℂ where
  smul g ζ := rotationFactor g.α * ζ - g.w / (Real.sqrt 2 : ℂ)
  one_smul ζ := by
    show rotationFactor 0 * ζ - 0 / (Real.sqrt 2 : ℂ) = ζ
    simp [rotationFactor_zero]
  mul_smul g h ζ := by
    show rotationFactor (g.α + h.α) * ζ - (g.w + rotationFactor g.α * h.w) / (Real.sqrt 2 : ℂ) =
      rotationFactor g.α * (rotationFactor h.α * ζ - h.w / (Real.sqrt 2 : ℂ)) -
        g.w / (Real.sqrt 2 : ℂ)
    rw [rotationFactor_add]
    ring

end Oscillator

/-- §0.2. The Heisenberg group in the oscillator group:
`(x, y, z) ↦ (x + iy, 0, -(z - xy/2)/2)`. -/
@[expose]
def heisenbergToOscillator : TauCeti.HeisenbergGroup ℝ →* Oscillator where
  toFun p := ⟨⟨p.x, p.y⟩, 0, -((p.z - p.x * p.y / 2) / 2)⟩
  map_one' := by
    ext
    · apply Complex.ext <;> simp
    · simp
    · simp
  map_mul' p q := by
    ext
    · apply Complex.ext <;> simp [rotationFactor_zero]
    · simp
    · simp [rotationFactor_zero]; ring

/-- The coordinates of the Heisenberg group homomorphism into the oscillator group. -/
theorem heisenbergToOscillator_apply (g : TauCeti.HeisenbergGroup ℝ) :
    heisenbergToOscillator g = ⟨⟨g.x, g.y⟩, 0, -((g.z - g.x * g.y / 2) / 2)⟩ :=
  rfl

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

/-- The central coordinate of a product in `MillerGroup`. -/
@[simp] theorem centralCoordinate_mul (g h : MillerGroup) :
    (g * h).a = g.a + h.a + Complex.exp g.τ * g.c * h.b := rfl

/-- The raising coordinate of a product in `MillerGroup`. -/
@[simp] theorem modulation_mul (g h : MillerGroup) : (g * h).b = g.b + Complex.exp g.τ * h.b := rfl

/-- The lowering coordinate of a product in `MillerGroup`. -/
@[simp]
theorem translation_mul (g h : MillerGroup) : (g * h).c = g.c + Complex.exp (-g.τ) * h.c := rfl

/-- The diagonal coordinate of a product in `MillerGroup`. -/
@[simp] theorem logDilation_mul (g h : MillerGroup) : (g * h).τ = g.τ + h.τ := rfl

/-- The central coordinate of the identity in `MillerGroup`. -/
@[simp] theorem centralCoordinate_one : (1 : MillerGroup).a = 0 := rfl

/-- The raising coordinate of the identity in `MillerGroup`. -/
@[simp] theorem modulation_one : (1 : MillerGroup).b = 0 := rfl

/-- The lowering coordinate of the identity in `MillerGroup`. -/
@[simp] theorem translation_one : (1 : MillerGroup).c = 0 := rfl

/-- The diagonal coordinate of the identity in `MillerGroup`. -/
@[simp] theorem logDilation_one : (1 : MillerGroup).τ = 0 := rfl

/-- The central coordinate of the inverse in `MillerGroup`. -/
@[simp] theorem centralCoordinate_inv (g : MillerGroup) : g⁻¹.a = g.c * g.b - g.a := rfl

/-- The raising coordinate of the inverse in `MillerGroup`. -/
@[simp] theorem modulation_inv (g : MillerGroup) : g⁻¹.b = -(Complex.exp (-g.τ) * g.b) := rfl

/-- The lowering coordinate of the inverse in `MillerGroup`. -/
@[simp] theorem translation_inv (g : MillerGroup) : g⁻¹.c = -(Complex.exp g.τ * g.c) := rfl

/-- The diagonal coordinate of the inverse in `MillerGroup`. -/
@[simp] theorem logDilation_inv (g : MillerGroup) : g⁻¹.τ = -g.τ := rfl

instance : Group MillerGroup where
  mul_assoc g h k := by
    have h1 : Complex.exp g.τ * Complex.exp (-g.τ) = 1 := by rw [← Complex.exp_add]; simp
    ext
    · simp only [centralCoordinate_mul, modulation_mul, translation_mul, logDilation_mul,
      Complex.exp_add]
      linear_combination (Complex.exp h.τ * h.c * k.b) * h1
    · simp only [modulation_mul, logDilation_mul, Complex.exp_add]; ring
    · simp only [translation_mul, logDilation_mul, neg_add, Complex.exp_add]; ring
    · simp only [logDilation_mul]; ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by
    have h0 : Complex.exp (-g.τ) * Complex.exp g.τ = 1 := by rw [← Complex.exp_add]; simp
    ext
    · simp only [centralCoordinate_mul, centralCoordinate_inv, translation_inv,
      logDilation_inv, centralCoordinate_one]
      linear_combination (-(g.c * g.b)) * h0
    · simp only [modulation_mul, modulation_inv, logDilation_inv, modulation_one]; ring
    · simp only [translation_mul, translation_inv, logDilation_inv, neg_neg, translation_one]; ring
    · simp

end MillerGroup

/-- The real points of `G(0, 1)` in the triangular group: `(a, b, c, τ) ↦ (e^τ c, a, b, τ)`. -/
@[expose]
def millerToTriangular (a b c τ : ℝ) : TriangularGroup := ⟨Real.exp τ * c, a, b, τ⟩

/-- The real Miller coordinates in the triangular model. -/
theorem millerToTriangular_def (a b c τ : ℝ) :
    millerToTriangular a b c τ = (⟨Real.exp τ * c, a, b, τ⟩ : TriangularGroup) :=
  rfl

end SFVK.AffineHeisenberg
