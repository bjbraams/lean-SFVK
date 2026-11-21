/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# Gel'fand pairs and spherical functions

Bi-invariant functions, convolution, Gel'fand pairs and spherical functions for a subgroup `K` of
a topological group `G` with a measure. A spherical function is continuous, bi-`K`-invariant,
takes the value `1` at the identity and satisfies the functional equation
`∫_K φ(x k y) dk = φ(x) φ(y)`; no boundedness is required (the bounded ones are the characters of
the convolution algebra of integrable bi-invariant functions).

## Main definitions

* `Subgroup.IsBiInvariant`: `f(k₁ x k₂) = f(x)` for `k₁, k₂ ∈ K`.
* `MeasureTheory.groupConvolution`: the convolution `(f * h)(x) = ∫ f(y) h(y⁻¹ x) dμ(y)`.
* `Subgroup.IsGelfandPair`: convolution of continuous compactly supported bi-invariant
  functions is commutative.
* `Subgroup.IsSphericalFunction`: the spherical functions of `(G, K)` for a measure on `K`.

## Main result

* `Subgroup.isGelfandPair_of_measurePreserving_anti`: Gel'fand's criterion via a
  measure-preserving anti-automorphism that preserves every double coset.
-/

public noncomputable section

open MeasureTheory

variable {G : Type*} [Group G]

namespace MeasureTheory

variable [MeasurableSpace G]

/-- The convolution `(f * h)(x) = ∫ f(y) h(y⁻¹ x) dμ(y)` of functions on a group. -/
@[expose]
def groupConvolution (μ : Measure G) (f h : G → ℂ) (x : G) : ℂ := ∫ y, f y * h (y⁻¹ * x) ∂μ

/-- Group convolution integrates the first function at the integration variable and the second at
its inverse times the output point. -/
theorem groupConvolution_def (μ : Measure G) (f h : G → ℂ) (x : G) :
    groupConvolution μ f h x = ∫ y, f y * h (y⁻¹ * x) ∂μ :=
  rfl

end MeasureTheory

namespace Subgroup

/-- A function on `G` is bi-invariant under `K` when `f(k₁ x k₂) = f(x)` for `k₁, k₂ ∈ K`. -/
@[expose]
def IsBiInvariant {V : Type*} (K : Subgroup G) (f : G → V) : Prop :=
  ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ x, f (k₁ * x * k₂) = f x

/-- Bi-invariance means that multiplication on either side by elements of the subgroup leaves the
function unchanged. -/
theorem isBiInvariant_def {V : Type*} (K : Subgroup G) (f : G → V) :
    K.IsBiInvariant f ↔ ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ x, f (k₁ * x * k₂) = f x :=
  Iff.rfl

variable [MeasurableSpace G]

/-- The convolution of two bi-invariant functions is bi-invariant. -/
theorem IsBiInvariant.groupConvolution [MeasurableMul G] {K : Subgroup G} {μ : Measure G}
    [μ.IsMulLeftInvariant] {f h : G → ℂ} (hf : K.IsBiInvariant f) (hh : K.IsBiInvariant h) :
    K.IsBiInvariant (MeasureTheory.groupConvolution μ f h) := by
  intro a ha b hb x
  unfold MeasureTheory.groupConvolution
  rw [← integral_mul_left_eq_self (μ := μ)
    (fun y => f y * h (y⁻¹ * (a * x * b))) a]
  refine integral_congr_ae <| Filter.Eventually.of_forall fun y => ?_
  beta_reduce
  have ha' : f (a * y) = f y := by simpa using hf a ha 1 K.one_mem y
  have hb' : h (y⁻¹ * x * b) = h (y⁻¹ * x) := by simpa using hh 1 K.one_mem b hb (y⁻¹ * x)
  rw [ha', show (a * y)⁻¹ * (a * x * b) = y⁻¹ * x * b by group, hb']

variable [TopologicalSpace G]

/-- `(G, K)` is a Gel'fand pair for the measure `μ` when convolution of continuous compactly
supported bi-`K`-invariant functions is commutative. -/
@[expose]
def IsGelfandPair (K : Subgroup G) (μ : Measure G) : Prop :=
  ∀ f h : G → ℂ, Continuous f → HasCompactSupport f → K.IsBiInvariant f →
    Continuous h → HasCompactSupport h → K.IsBiInvariant h →
      groupConvolution μ f h = groupConvolution μ h f

/-- A Gel'fand pair has commutative convolution on continuous compactly supported bi-invariant
functions. -/
theorem isGelfandPair_def (K : Subgroup G) (μ : Measure G) :
    K.IsGelfandPair μ ↔ ∀ f h : G → ℂ, Continuous f → HasCompactSupport f → K.IsBiInvariant f →
      Continuous h → HasCompactSupport h → K.IsBiInvariant h →
        groupConvolution μ f h = groupConvolution μ h f :=
  Iff.rfl

/-- Gel'fand's criterion. A measure-preserving anti-automorphism that preserves each double
coset gives commutativity of the bi-invariant convolution algebra. -/
theorem isGelfandPair_of_measurePreserving_anti {K : Subgroup G} {μ : Measure G}
    [MeasurableMul G] [MeasurableInv G] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    {τ : G ≃ᵐ G} (hμ : MeasurePreserving τ μ μ) (hτ : ∀ x y, τ (x * y) = τ y * τ x)
    (hK : ∀ x, ∃ a ∈ K, ∃ b ∈ K, a * x * b = τ x) : K.IsGelfandPair μ := by
  have hone : τ 1 = 1 := by
    apply mul_left_cancel (a := τ 1)
    simpa only [mul_one] using (hτ 1 1).symm
  have hinv (x : G) : (τ x)⁻¹ = τ x⁻¹ := by
    apply mul_right_cancel (b := τ x)
    rw [inv_mul_cancel, ← hτ, mul_inv_cancel, hone]
  intro f h _ _ hf _ _ hh
  have hfix {v : G → ℂ} (hv : K.IsBiInvariant v) (x : G) : v (τ x) = v x := by
    obtain ⟨a, ha, b, hb, he⟩ := hK x
    rw [← he, hv a ha b hb]
  funext x
  calc
    groupConvolution μ f h x = groupConvolution μ f h (τ x) :=
      (hfix (hf.groupConvolution hh) x).symm
    _ = ∫ y, f (τ y) * h ((τ y)⁻¹ * τ x) ∂μ :=
      (hμ.integral_comp' (fun y => f y * h (y⁻¹ * τ x))).symm
    _ = ∫ y, f y * h (x * y⁻¹) ∂μ := by
      refine integral_congr_ae <| Filter.Eventually.of_forall fun y => ?_
      beta_reduce
      rw [hfix hf, hinv, ← hτ, hfix hh]
    _ = ∫ y, f y⁻¹ * h (x * y) ∂μ := by
      simpa only [inv_inv] using
        integral_inv_eq_self (fun y => f y⁻¹ * h (x * y)) μ
    _ = groupConvolution μ h f x := by
      unfold MeasureTheory.groupConvolution
      rw [← integral_mul_left_eq_self (μ := μ) (fun y => h y * f (y⁻¹ * x)) x]
      refine integral_congr_ae <| Filter.Eventually.of_forall fun y => ?_
      beta_reduce
      rw [show (x * y)⁻¹ * x = y⁻¹ by group, mul_comm]

/-- `φ` is a spherical function of `(G, K)` for the measure `ν` on `K`: continuous,
bi-`K`-invariant, `φ(1) = 1`, and `∫_K φ(x k y) dν(k) = φ(x) φ(y)`. Boundedness is not
required. -/
@[expose]
def IsSphericalFunction (K : Subgroup G) (ν : Measure K) (φ : G → ℂ) : Prop :=
  Continuous φ ∧ K.IsBiInvariant φ ∧ φ 1 = 1 ∧ ∀ x y, ∫ k : K, φ (x * k * y) ∂ν = φ x * φ y

/-- A spherical function is continuous, bi-invariant, normalized at the identity, and satisfies the
subgroup mean identity. -/
theorem isSphericalFunction_def (K : Subgroup G) (ν : Measure K) (φ : G → ℂ) :
    K.IsSphericalFunction ν φ ↔
      Continuous φ ∧ K.IsBiInvariant φ ∧ φ 1 = 1 ∧
        ∀ x y, ∫ k : K, φ (x * k * y) ∂ν = φ x * φ y :=
  Iff.rfl

end Subgroup
