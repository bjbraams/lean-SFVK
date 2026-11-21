/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.AffineHeisenberg.Basic
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.HilbertBasis
public import SFVKMathlib.RepresentationTheory.Continuous.MatrixElement
public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import DLMF.OrthogonalPolynomials.Basic.AskeyScheme
import DLMF.OrthogonalPolynomials.Hahn.HahnAndMeixner
import DLMF.OrthogonalPolynomials.LaguerreContinuation

/-!
# the Heisenberg group, Hermite and Laguerre functions

Statements of §3 of the roadmap `Roadmaps/AffineHeisenbergGroups/README.md` (section numbers
`§x.y`).
Sources: Vilenkin–Klimyk Vol. 2 §12.1.6–12.1.8, pp. 415–421; Wawrzyńczyk §§12.1–12.2, pp. 425–430;
Miller §§4-13–4-15, pp. 117–125; Klimyk–Vilenkin Ch. 6 §1.4 (5)–(7), p. 239.
Theorems not yet proved are stated with `sorry`.
-/

@[expose] public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open DLMF.Hypergeometric DLMF.OrthogonalPolynomials
open scoped Real ComplexConjugate InnerProductSpace ENNReal

/-- §3.1. The matrix element of `U(x, y, z)` in the Hermite basis: with
`α = (-x + iy)/√2` and `A = (x² + y²)/2`, `e^{i(z - xy/2)} e^{-A/2}` times
`(n!/m!)^{1/2} α^{m-n} L_n^{(m-n)}(A)` for `n ≤ m` and `(m!/n!)^{1/2} (-conj α)^{n-m}
L_m^{(n-m)}(A)` for `m < n`. -/
def hermiteMatrixElement (m n : ℕ) (x y z : ℝ) : ℂ :=
  let α : ℂ := (-x + y * Complex.I) / (Real.sqrt 2 : ℂ)
  let A : ℝ := (x ^ 2 + y ^ 2) / 2
  Complex.exp ((z - x * y / 2 : ℝ) * Complex.I) * (Real.exp (-A / 2) : ℂ) *
    if n ≤ m then
      (Real.sqrt (n.factorial / m.factorial) : ℂ) * α ^ (m - n) *
        laguerreExtended ((m : ℂ) - n) n (A : ℂ)
    else
      (Real.sqrt (m.factorial / n.factorial) : ℂ) * (-conj α) ^ (n - m) *
        laguerreExtended ((n : ℂ) - m) m (A : ℂ)

/-- §3.1. **Hermite matrix elements.** -/
theorem matrixElement_schrodinger_hermite (m n : ℕ) (g : TauCeti.HeisenbergGroup ℝ) :
    ContRepresentation.matrixElement schrodinger (TauCeti.hermiteHilbertBasis ℂ) m n g =
      hermiteMatrixElement m n g.x g.y g.z := by
  sorry

/-- §3.1. **Unitarity bound.** -/
theorem norm_laguerre_le (m n : ℕ) (hnm : n ≤ m) (A : ℝ) (hA : 0 ≤ A) :
    Real.sqrt (n.factorial / m.factorial) * A ^ (((m : ℝ) - n) / 2) * Real.exp (-A / 2) *
      ‖laguerreExtended ((m : ℂ) - n) n (A : ℂ)‖ ≤ 1 := by
  sorry

/-- §3.2. **Addition theorem.** -/
theorem hasSum_hermiteMatrixElement_mul (m n : ℕ) (g h : TauCeti.HeisenbergGroup ℝ) :
    HasSum (fun k => hermiteMatrixElement m k g.x g.y g.z * hermiteMatrixElement k n h.x h.y h.z)
      (hermiteMatrixElement m n (g * h).x (g * h).y (g * h).z) := by
  sorry

/-- §3.2. **Orthogonality.** -/
theorem integral_hermiteMatrixElement (m n m' n' : ℕ) :
    ∫ p : ℝ × ℝ, hermiteMatrixElement m n p.1 p.2 0 * conj (hermiteMatrixElement m' n' p.1 p.2 0) =
      if m = m' ∧ n = n' then (2 * π : ℂ) else 0 := by
  sorry

/-- §3.2. **Completeness.** -/
theorem hermiteMatrixElement_hilbertBasis :
    ∃ b : HilbertBasis (ℕ × ℕ) ℂ (Lp ℂ 2 (volume : Measure (ℝ × ℝ))),
      ∀ i, (b i : ℝ × ℝ → ℂ) =ᵐ[volume]
        fun p => ((2 * π) ^ (-(1 / 2 : ℝ)) : ℝ) * hermiteMatrixElement i.1 i.2 p.1 p.2 0 := by
  sorry

/-- §3.3. **Charlier matrix elements.** -/
theorem hermiteMatrixElement_charlier (x : ℝ) (hx : x ≠ 0) (k n : ℕ) :
    hermiteMatrixElement k n x 0 0 =
      (((-1) ^ k / Real.sqrt (k.factorial * n.factorial) * (x ^ 2 / 2) ^ (((k : ℝ) + n) / 2) *
        Real.exp (-(x ^ 2 / 4)) * (charlier (x ^ 2 / 2) k).eval (n : ℝ) : ℝ) : ℂ) := by
  sorry

/-- §3.3. Bridge to lean-DLMF's Charlier polynomial `₂F₀(-n, -x; ; -1/a)` (DLMF 18.20.8). -/
theorem charlier_eq_dlmf_charlier (a : ℝ) (ha : a ≠ 0) (n : ℕ) (x : ℝ) :
    (((charlier a n).eval x : ℝ) : ℂ) = DLMF.OrthogonalPolynomials.charlier a n x := by
  unfold charlier DLMF.OrthogonalPolynomials.charlier terminatingHypergeometric
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_inv, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, div_one]
  apply Finset.sum_congr rfl
  intro k hk
  have hdesc : (((descPochhammer ℝ k).eval x : ℝ) : ℂ) =
      (descPochhammer ℂ k).eval (x : ℂ) := by
    simp only [descPochhammer_eval_eq_prod_range, Complex.ofReal_prod, Complex.ofReal_sub,
      Complex.ofReal_natCast]
  rw [hdesc, pochhammer_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, pochhammer, ascPochhammer_eval_neg_eq_descPochhammer]
  have hfact : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  field_simp
  rw [show ((-1 : ℂ) ^ k) ^ 2 = 1 by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
  ring

/-- §3.3. **Charlier and Laguerre.** -/
theorem charlier_eq_laguerre (a : ℝ) (ha : a ≠ 0) (n x : ℕ) :
    (((charlier a n).eval (x : ℝ) : ℝ) : ℂ) =
      (-1) ^ n * n.factorial * ((a : ℂ) ^ n)⁻¹ * laguerreExtended ((x : ℂ) - n) n a := by
  unfold charlier
  rw [laguerreExtended_eq_reverse_sum, Finset.mul_sum]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_inv]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hs : ((x : ℂ) - n) + (n - k : ℕ) + 1 = (x : ℂ) - k + 1 := by
    rw [Nat.cast_sub hkn]
    ring
  have hdesc : (((descPochhammer ℝ k).eval (x : ℝ) : ℝ) : ℂ) =
      pochhammer ((x : ℂ) - k + 1) k := by
    rw [pochhammer, ← descPochhammer_eval_eq_ascPochhammer]
    simp only [descPochhammer_eval_eq_prod_range, Complex.ofReal_prod, Complex.ofReal_sub,
      Complex.ofReal_natCast]
  rw [hs, hdesc]
  have hchoose : (n.choose k : ℂ) * k.factorial * (n - k).factorial = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hfactor : (-1 : ℂ) ^ n * ((a : ℂ) ^ n)⁻¹ * (-(a : ℂ)) ^ (n - k) =
      (-(a : ℂ)⁻¹) ^ k := by
    have hpow : (-1 : ℂ) ^ n * ((a : ℂ) ^ n)⁻¹ = (-(a : ℂ)⁻¹) ^ n := by
      rw [neg_eq_neg_one_mul ((a : ℂ)⁻¹), mul_pow, inv_pow]
    have hsplit : (-(a : ℂ)⁻¹) ^ n = (-(a : ℂ)⁻¹) ^ k * (-(a : ℂ)⁻¹) ^ (n - k) := by
      rw [← pow_add, Nat.add_sub_of_le hkn]
    have hunit : (-(a : ℂ)⁻¹) * (-(a : ℂ)) = 1 := by
      rw [neg_mul_neg, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ha)]
    rw [hpow, hsplit, mul_assoc, ← mul_pow, hunit, one_pow, mul_one]
  have h1 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have h2 : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  rw [← hchoose]
  calc
    _ = ((n.choose k : ℂ) * pochhammer ((x : ℂ) - k + 1) k) * (-(a : ℂ)⁻¹) ^ k := by ring
    _ = _ := by rw [← hfactor]; field_simp

/-- §3.3. **Duality.** -/
theorem charlier_symm (a : ℝ) (n x : ℕ) :
    (charlier a n).eval (x : ℝ) = (charlier a x).eval (n : ℝ) := by
  have haux (n : ℕ) (t : ℝ) : (charlier 0 n).eval t = 1 := by
    simp only [charlier, inv_zero, neg_zero, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      simp [zero_pow hk]
    · simp
  by_cases ha : a = 0
  · simp [ha, haux]
  apply Complex.ofReal_injective
  rw [charlier_eq_dlmf_charlier a ha, charlier_eq_dlmf_charlier a ha]
  push_cast
  exact DLMF.OrthogonalPolynomials.charlier_duality a n x

/-- §3.3. **Orthogonality and completeness** of the Charlier polynomials. -/
theorem charlier_orthogonality (a : ℝ) (ha : 0 < a) :
    (∀ k p : ℕ, HasSum (fun x : ℕ => a ^ k * Real.exp (-a) / k.factorial *
        (a ^ x / x.factorial * (charlier a k).eval (x : ℝ) * (charlier a p).eval (x : ℝ)))
      (if k = p then 1 else 0)) ∧
    ∃ b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2),
      ∀ k x : ℕ, b k x = Real.sqrt (a ^ (k + x) * Real.exp (-a) / (k.factorial * x.factorial)) *
        (charlier a k).eval (x : ℝ) := by
  sorry

/-- §3.4. **Fock space.** -/
theorem fockSpace_spec :
    Orthonormal ℂ fockMonomial ∧
      ∀ F : Lp ℂ 2 fockMeasure,
        F ∈ fockSpace ↔ ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (F : ℂ → ℂ) =ᵐ[fockMeasure] G := by
  sorry

/-- §3.4. **Bargmann transform.** -/
theorem bargmann_spec :
    ∃ B : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 fockMeasure,
      LinearMap.range B.toLinearMap = fockSpace ∧
      (∀ n, B (TauCeti.hermiteFunctionLp ℂ n) = fockMonomial n) ∧
      (∀ f : Lp ℂ 2 (volume : Measure ℝ), Integrable (f : ℝ → ℂ) →
        (B f : ℂ → ℂ) =ᵐ[fockMeasure] fun ζ => ∫ u, bargmannKernel ζ u * f u) ∧
      ∀ p f, (B (schrodinger p f) : ℂ → ℂ) =ᵐ[fockMeasure] fockHeisenbergAction p (B f) := by
  sorry

end SFVK.AffineHeisenberg
