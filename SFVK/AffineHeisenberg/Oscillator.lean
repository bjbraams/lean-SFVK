/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.AffineHeisenberg.Basic
public import SFVK.AffineHeisenberg.Fock
public import SFVK.AffineHeisenberg.Schrodinger

/-!
# The oscillator group on the Fock space

The oscillator cocycle acts on the holomorphic subspace of `L²` for the normalized
Gaussian measure. The stated properties are unitarity, invariance and irreducibility
of the Fock subspace, restriction to the Heisenberg action, and a formula for the
matrix elements in the monomial basis.

Sources: Miller §4-14 (4.119)–(4.121), Theorem 4.2, pp. 121–122, §4-15 (4.122)–(4.123), Lemma 4.5,
pp. 122–123.
-/

public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open scoped Real ComplexConjugate InnerProductSpace ENNReal

/-- The (L²) oscillator action is unitary, realizes the cocycle, preserves the Fock subspace,
acts irreducibly there, and restricts to the Heisenberg action. -/
theorem oscillatorFock_spec (lam : ℝ) :
    (∀ g F, (oscillatorFock lam g F : ℂ → ℂ) =ᵐ[fockMeasure]
      multiplierAction (oscillatorCocycle lam) g F) ∧
    (oscillatorFock lam).IsUnitary ∧
    (∀ g, ∀ F ∈ fockSpace, oscillatorFock lam g F ∈ fockSpace) ∧
    (∀ W : Submodule ℂ (Lp ℂ 2 fockMeasure), W ≤ fockSpace →
      IsClosed (W : Set (Lp ℂ 2 fockMeasure)) →
      (∀ g, ∀ v ∈ W, oscillatorFock lam g v ∈ W) → W = ⊥ ∨ W = fockSpace) ∧
    ∀ p F, multiplierAction (oscillatorCocycle lam) (heisenbergToOscillator p) F =
      fockHeisenbergAction p F := by
  sorry

/-- The oscillator matrix element is the Heisenberg Hermite coefficient times the rotational
and central phase. -/
theorem inner_fockMonomial_oscillatorFock (lam : ℝ) (g : Oscillator) (m n : ℕ) :
    ⟪fockMonomial m, oscillatorFock lam g (fockMonomial n)⟫_ℂ =
      Complex.exp ((lam * g.α - 2 * g.δ + n * g.α : ℝ) * Complex.I) *
        hermiteMatrixElement m n g.w.re g.w.im (g.w.re * g.w.im / 2) := by
  sorry

end SFVK.AffineHeisenberg
