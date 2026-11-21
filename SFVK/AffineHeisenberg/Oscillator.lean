/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.AffineHeisenberg.Basic
public import SFVK.AffineHeisenberg.Heisenberg

/-!
# the oscillator group on the Fock space

Statements of §4 of the roadmap `Roadmaps/AffineHeisenbergGroups/README.md` (section numbers
`§x.y`).
Sources: Miller §4-14 (4.119)–(4.121), Theorem 4.2, pp. 121–122, §4-15 (4.122)–(4.123), Lemma 4.5,
pp. 122–123.
Theorems not yet proved are stated with `sorry`.
-/

@[expose] public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open scoped Real ComplexConjugate InnerProductSpace ENNReal

/-- §4.1. **Oscillator representations.** -/
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

/-- §4.1. **Oscillator matrix elements.** -/
theorem inner_fockMonomial_oscillatorFock (lam : ℝ) (g : Oscillator) (m n : ℕ) :
    ⟪fockMonomial m, oscillatorFock lam g (fockMonomial n)⟫_ℂ =
      Complex.exp ((lam * g.α - 2 * g.δ + n * g.α : ℝ) * Complex.I) *
        hermiteMatrixElement m n g.w.re g.w.im (g.w.re * g.w.im / 2) := by
  sorry

end SFVK.AffineHeisenberg
