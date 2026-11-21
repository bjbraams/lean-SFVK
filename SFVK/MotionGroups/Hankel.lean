/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import TauCeti.Analysis.Matrix.EuclideanLin
public import SFVK.MotionGroups.Basic.Zonal
public import SFVK.MotionGroups.CircleModel

/-!
# The quasi-regular representation of `M(n)` and the Hankel transform

Mathlib's Fourier transform `𝓕f(ξ) = ∫ e^{-2πi⟨x, ξ⟩} f(x) dx` carries the quasi-regular
representation `L(g) f = f ∘ g⁻¹` of `M(n)` to `e^{-2πi⟨a, ξ⟩} 𝓕f(k⁻¹ξ)`, which on the circle
`|ξ| = ρ` of `ℝ²` is the circle model `T_{-2πρ}`. On angular modes it is the Hankel transform,
which is self-inverse and isometric for real `ν > -1` and has the Laguerre functions as
eigenfunctions; on radial functions of `ℝⁿ` it is the Hankel transform of order `n/2 - 1`.
Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 1, §4.4.1 (1)–(7),
pp. 193–195, and §4.4.2 (1)–(7), pp. 196–197; Vol. 2, §10.2.6 (1)–(7), pp. 186–187, and
(13)–(17), p. 188; Dieudonné, *Special Functions and Linear Representations of Lie Groups*, §16,
p. 57.
-/

public noncomputable section

open AddCircle Complex MeasureTheory Set
open scoped Real InnerProductSpace FourierTransform Laplacian

namespace SFVK.MotionGroups

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- Fourier transform of a translate-rotate (Vilenkin–Klimyk Vol. 1 §4.4.1, pp. 193–195):
`𝓕(f ∘ g⁻¹)(ξ) = e^{-2πi⟨a, ξ⟩} 𝓕f(k⁻¹ ξ)`. -/
theorem fourier_comp_motionApply {n : ℕ} (g : MotionGroup n)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : Integrable f) (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (fun x => f (motionApply g⁻¹ x)) ξ =
      Complex.exp (-(2 * π * ⟪g.a, ξ⟫_ℝ : ℝ) * I) * 𝓕 f (rotE g.k⁻¹ ξ) := by
  let V := EuclideanSpace ℝ (Fin n)
  let k := g.k⁻¹
  let A := Matrix.UnitaryGroup.toLinearIsometryEquiv
    (⟨k.1, (Matrix.mem_specialOrthogonalGroup_iff.mp k.2).1⟩ :
      Matrix.orthogonalGroup (Fin n) ℝ)
  have hA (x : V) : A x = rotE k x := by
    rw [Matrix.UnitaryGroup.toLinearIsometryEquiv_apply, rotE_def, Matrix.toLpLin_apply]
  have hfun : (fun x : V => f (motionApply g⁻¹ x)) =
      (f ∘ A) ∘ fun x : V => x + -g.a := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, hA, rotE_add, motionApply_def,
      MotionGroup.inv_a, MotionGroup.inv_k, rotE_neg]
    exact congrArg f (add_comm _ _)
  rw [hfun]
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ V)
    ((f ∘ A) ∘ fun x : V => x + -g.a) ξ = _
  rw [VectorFourier.fourierIntegral_comp_add_right]
  change Real.fourierChar ⟪-g.a, ξ⟫_ℝ • (𝓕 (f ∘ A) ξ) = _
  rw [Real.fourier_comp_linearIsometry, hA, inner_neg_left, Circle.smul_def,
    Real.fourierChar_apply]
  push_cast
  congr 2
  ring

/-- On the circle `|ξ| = ρ` the quasi-regular representation is `T_{-2πρ}`. -/
theorem fourier_comp_motionApply_circle (g : MotionGroup 2)
    (f : EuclideanSpace ℝ (Fin 2) → ℂ) (hf : Integrable f) (ρ : ℝ) (ψ : 𝕋) :
    𝓕 (fun x => f (motionApply g⁻¹ x)) (ρ • unitVec ψ) =
      circleAction (-(2 * π * ρ)) g (fun ψ' => 𝓕 f (ρ • unitVec ψ')) ψ := by
  rw [fourier_comp_motionApply g f hf, circleAction_def, unitVec_sub_rotAngle, rotE_def, map_smul,
    ← rotE_def, real_inner_smul_right]
  push_cast
  congr 2
  ring

/-- Cylindrical waves: `u(x) = Jₙ(R|x|) (x/|x|)ⁿ` (complex coordinate) satisfies `Δu = -R² u`
away from the origin. -/
theorem laplacian_cylindricalWave (R : ℂ) (n : ℤ) {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    Δ (fun y : EuclideanSpace ℝ (Fin 2) => besselJ n (R * ‖y‖) * (toComplex y / ‖y‖) ^ n) x =
      -R ^ 2 * (besselJ n (R * ‖x‖) * (toComplex x / ‖x‖) ^ n) := by
  sorry

/-- Fourier transform of an angular mode (Vilenkin–Klimyk Vol. 1 §4.4.2 (3), p. 196, in
Mathlib's normalization): `𝓕(φ(|x|) e^{inα})(ρ e(ψ)) = 2π (-i)ⁿ e^{inψ} (Hₙφ)(2πρ)`. -/
theorem fourier_angularMode (n : ℤ) (φ : ℝ → ℂ)
    (hφ : IntegrableOn (fun r => φ r * r) (Ioi 0)) (ρ : ℝ) (hρ : 0 < ρ) (ψ : 𝕋) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin 2) => φ ‖x‖ * (toComplex x / ‖x‖) ^ n) (ρ • unitVec ψ) =
      2 * π * (-I) ^ n * fourier n ψ * hankelTransform n φ (2 * π * ρ) := by
  sorry

/-- Hankel inversion for real `ν > -1` on smooth functions with compact support in `(0, ∞)`
(Vilenkin–Klimyk Vol. 1 §4.4.2, pp. 196–197; Vol. 2 §10.2.6 (3)–(4), pp. 186–187). -/
theorem hankelTransform_hankelTransform {ν : ℝ} (hν : -1 < ν) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ⊤ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 0) {r : ℝ} (hr : 0 < r) :
    hankelTransform ν (hankelTransform ν φ) r = φ r := by
  sorry

/-- Plancherel for the Hankel transform (Vilenkin–Klimyk Vol. 1 §4.4.2, pp. 196–197; Vol. 2
§10.2.6 (5), pp. 186–187). -/
theorem lintegral_hankelTransform {ν : ℝ} (hν : -1 < ν) (φ : ℝ → ℂ) (hφ : ContDiff ℝ ⊤ φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ioi 0) :
    ∫⁻ R in Ioi (0 : ℝ), ‖hankelTransform ν φ R‖ₑ ^ 2 * ENNReal.ofReal R =
      ∫⁻ r in Ioi (0 : ℝ), ‖φ r‖ₑ ^ 2 * ENNReal.ofReal r := by
  sorry

/-- Laguerre functions are eigenfunctions of the Hankel transform (Vilenkin–Klimyk Vol. 2
§10.2.6 (16), p. 188), with lean-DLMF's Laguerre polynomials:
`H_ν(x^ν e^{-x²/2} L_k^ν(x²))(λ) = (-1)^k λ^ν e^{-λ²/2} L_k^ν(λ²)`. -/
theorem hankelTransform_laguerre {ν : ℝ} (hν : -1 < ν) (k : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    hankelTransform ν
        (fun x => ((x ^ ν * Real.exp (-x ^ 2 / 2) : ℝ) : ℂ) *
          DLMF.OrthogonalPolynomials.laguerrePolynomialL ν k ((x ^ 2 : ℝ) : ℂ)) lam =
      (-1) ^ k * ((lam ^ ν * Real.exp (-lam ^ 2 / 2) : ℝ) : ℂ) *
        DLMF.OrthogonalPolynomials.laguerrePolynomialL ν k ((lam ^ 2 : ℝ) : ℂ) := by
  sorry

/-- Fourier transform of a radial function on `ℝⁿ` (Vilenkin–Klimyk Vol. 2 §10.2.6 (1)–(2),
p. 186): `𝓕f(ξ) = 2π |ξ|^{1-n/2} ∫₀^∞ φ(r) J_{n/2-1}(2π|ξ| r) r^{n/2} dr` for `f(x) = φ(|x|)`,
`ξ ≠ 0`. -/
theorem fourier_radial {n : ℕ} (hn : 1 ≤ n) (φ : ℝ → ℂ)
    (hφ : IntegrableOn (fun r => φ r * r ^ (n - 1)) (Ioi 0)) {ξ : EuclideanSpace ℝ (Fin n)}
    (hξ : ξ ≠ 0) :
    𝓕 (fun x : EuclideanSpace ℝ (Fin n) => φ ‖x‖) ξ =
      2 * π * ((‖ξ‖ ^ (1 - (n : ℝ) / 2) : ℝ) : ℂ) *
        ∫ r in Ioi (0 : ℝ), φ r * besselJ ((n : ℂ) / 2 - 1) (2 * π * ‖ξ‖ * r) *
          ((r ^ ((n : ℝ) / 2) : ℝ) : ℂ) := by
  sorry

end SFVK.MotionGroups
