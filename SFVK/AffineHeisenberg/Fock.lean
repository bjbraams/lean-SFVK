/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.AffineHeisenberg.Basic
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.HilbertBasis

/-!
# Fock space and the Bargmann transform

In the complex Gaussian measure `π⁻¹ e^{-|ζ|²} dζ`, the Fock space is the closed
span of the normalized monomials `ζⁿ / √n!`. The Bargmann kernel defines a map
from the real-line Schrödinger model to this space. This file states the Hilbert
basis, projection, and intertwining properties of the two models.

Miller, *Lie Theory and Special Functions*, §4-13, pp. 117–118; Vilenkin–Klimyk,
*Representation of Lie Groups and Special Functions*, Vol. 2, §12.1.7, pp. 418–420.
-/

public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open scoped Real ComplexConjugate InnerProductSpace ENNReal

/-- The normalized monomials are orthonormal, and the Fock space consists of the Gaussian
`L²` classes with an entire representative. -/
theorem fockSpace_spec :
    Orthonormal ℂ fockMonomial ∧
      ∀ F : Lp ℂ 2 fockMeasure,
        F ∈ fockSpace ↔ ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (F : ℂ → ℂ) =ᵐ[fockMeasure] G := by
  sorry

/-- The Bargmann isometry maps the Hermite basis to normalized monomials, has image the
Fock space, agrees with the integral kernel on integrable inputs, and intertwines
the two Heisenberg actions. -/
theorem bargmann_spec :
    ∃ B : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 fockMeasure,
      LinearMap.range B.toLinearMap = fockSpace ∧
      (∀ n, B (TauCeti.hermiteFunctionLp ℂ n) = fockMonomial n) ∧
      (∀ f : Lp ℂ 2 (volume : Measure ℝ), Integrable (f : ℝ → ℂ) →
        (B f : ℂ → ℂ) =ᵐ[fockMeasure] fun ζ => ∫ u, bargmannKernel ζ u * f u) ∧
      ∀ p f, (B (schrodinger p f) : ℂ → ℂ) =ᵐ[fockMeasure] fockHeisenbergAction p (B f) := by
  sorry

end SFVK.AffineHeisenberg
