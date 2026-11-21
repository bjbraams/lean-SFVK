/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.ClebschGordan.Basic.Polynomials
public import SFVK.ClebschGordan.Basic.SixJ
public import DLMF.OrthogonalPolynomials.Basic.AskeyScheme
import DLMF.GeneralizedHypergeometric.ClearedTerminating
import DLMF.OrthogonalPolynomials.Wilson
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Hahn and Racah polynomials from the coupling coefficients

Layers 4 and 6 of the roadmap ClebschGordan. Locators: DLMF 18.20.5, Table 18.19.1, 18.25.9,
18.25.11–18.25.12, 18.26.3, 18.26.10; Klimyk–Vilenkin, *Representations of Lie groups and
special functions* (Encyclopaedia of Mathematical Sciences 59), §2.2, (17), p. 243;
Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 1, §8.5.1, p. 546,
and §8.5.4, p. 552 (the identification of the Racah parameters there is corrected in
`sixJ_eq_racahPolynomial`). Hahn reflection uses lean-DLMF's denominator-cleared Sheppard
transformation, and the Racah-to-Hahn limit uses its complex-variable counterpart.
-/

public noncomputable section

open Filter Topology

namespace SFVK.ClebschGordan

/-- The Pochhammer symbol commutes with the coercion `ℝ → ℂ`. -/
theorem ofReal_ascPochhammer_eval (k : ℕ) (r : ℝ) :
    (((ascPochhammer ℝ k).eval r : ℝ) : ℂ) = (ascPochhammer ℂ k).eval (r : ℂ) := by
  rw [← Complex.ofRealHom_eq_coe, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
    ascPochhammer_map]
  rfl

/-- The product `(u)_k (v)_k` as a product over `j < k` of `(u + j)(v + j)`. -/
theorem ascPochhammer_eval_mul_eq_prod (u v : ℂ) (k : ℕ) :
    (ascPochhammer ℂ k).eval u * (ascPochhammer ℂ k).eval v =
      ∏ j ∈ Finset.range k, (u + j) * (v + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, Finset.prod_range_succ, ← ih]
    ring

/-! ### Hahn polynomials -/

/-- **Clebsch–Gordan coefficients are Hahn polynomials** (Klimyk–Vilenkin §2.2, (17), p. 243;
Vilenkin–Klimyk §8.5.1), in Edmonds's normalization: with `j₁ = N/2`, `j₂ = (N + a + b)/2`,
`j = n + (a + b)/2`, `m₁ = N/2 - x` and `m = (a - b)/2`. -/
theorem clebschGordan_eq_hahn {N n x : ℕ} (a b : ℕ) (hn : n ≤ N) (hx : x ≤ N) :
    clebschGordan N (N + a + b) (2 * n + a + b) (N - x) (x + a) (n + a) =
      (-1) ^ x * (N.factorial / a.factorial : ℝ) *
        Real.sqrt ((((2 * n + a + b + 1) * (a + x).factorial * (N + b - x).factorial *
            (n + a).factorial * (n + a + b).factorial : ℕ) : ℝ) /
          ((x.factorial * (N - x).factorial * (n + b).factorial * (N - n).factorial *
            (N + n + a + b + 1).factorial * n.factorial : ℕ) : ℝ)) *
        hahn N n a b x := by
  sorry

/-- **Hahn orthogonality** (DLMF Table 18.19.1), for `α, β > -1`, multiplied by
`2n + α + β + 1`. -/
theorem sum_hahn_mul_hahn {N n m : ℕ} (hn : n ≤ N) (hm : m ≤ N) {α β : ℝ} (hα : -1 < α)
    (hβ : -1 < β) :
    (2 * n + α + β + 1) * ∑ x ∈ Finset.range (N + 1),
        (ascPochhammer ℝ x).eval (α + 1) * (ascPochhammer ℝ (N - x)).eval (β + 1) /
          (x.factorial * (N - x).factorial) * hahn N n α β x * hahn N m α β x =
      if n = m then
        (-1) ^ n * (ascPochhammer ℝ (N + 1)).eval (n + α + β + 1) *
            (ascPochhammer ℝ n).eval (β + 1) * n.factorial /
          ((ascPochhammer ℝ n).eval (α + 1) * (ascPochhammer ℝ n).eval (-(N : ℝ)) *
            N.factorial)
      else 0 := by
  sorry

/-- **Conversion to lean-DLMF's complex Hahn polynomial** (DLMF 18.20.5). -/
theorem hahn_eq_dlmf (N n : ℕ) (α β x : ℝ) :
    (hahn N n α β x : ℂ) = DLMF.OrthogonalPolynomials.hahn α β N n x := by
  simp only [hahn, DLMF.OrthogonalPolynomials.hahn,
    DLMF.OrthogonalPolynomials.terminatingHypergeometric, DLMF.Hypergeometric.pochhammer]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [ofReal_ascPochhammer_eval]
  ring

namespace HahnPolynomials

open DLMF.Hypergeometric

/-- Clear the two lower Pochhammer symbols in the finite Hahn series. -/
private theorem clearedHypergeometric_eq_hahn {N n : ℕ} (hn : n ≤ N) {α β x : ℂ}
    (hα : pochhammer (α + 1) n ≠ 0) :
    genClearedFiniteHG n {(-(n : ℂ)), -x, n + α + β + 1} {(-(N : ℂ)), α + 1} =
      pochhammer (-(N : ℂ)) n * pochhammer (α + 1) n *
        DLMF.OrthogonalPolynomials.hahn α β N n x := by
  rw [genClearedFiniteHG_eq_mul _ _ (by
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
      rintro y (rfl | rfl)
      · exact pochhammer_neg_natCast_ne_zero hn
      · exact hα)]
  simp only [pochhammerProduct, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton]
  apply congrArg (fun z => pochhammer (-(N : ℂ)) n * pochhammer (α + 1) n * z)
  unfold generalizedHypergeometricTruncated DLMF.OrthogonalPolynomials.hahn
    DLMF.OrthogonalPolynomials.terminatingHypergeometric
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [generalizedHypergeometricCoeff, pochhammerProduct,
    Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  ring

end HahnPolynomials

open HahnPolynomials DLMF.Hypergeometric in
/-- **The reflection `x ↦ N - x`** (Vilenkin–Klimyk §8.5.1). -/
theorem hahn_reflect {N n : ℕ} (hn : n ≤ N) {α β : ℝ}
    (hα : (ascPochhammer ℝ n).eval (α + 1) ≠ 0) (hβ : (ascPochhammer ℝ n).eval (β + 1) ≠ 0)
    (x : ℝ) :
    (ascPochhammer ℝ n).eval (α + 1) * hahn N n α β x =
      (-1) ^ n * (ascPochhammer ℝ n).eval (β + 1) * hahn N n β α (N - x) := by
  have hp (a : ℝ) : (((ascPochhammer ℝ n).eval (a + 1) : ℝ) : ℂ) =
      pochhammer ((a : ℂ) + 1) n := by
    rw [ofReal_ascPochhammer_eval, pochhammer, Complex.ofReal_add, Complex.ofReal_one]
  have hαc : pochhammer ((α : ℂ) + 1) n ≠ 0 := by
    rw [← hp α]; exact_mod_cast hα
  have hβc : pochhammer ((β : ℂ) + 1) n ≠ 0 := by
    rw [← hp β]; exact_mod_cast hβ
  have h := genClearedFiniteHG_sheppard n ((n : ℂ) + α + β + 1) (-x) (-(N : ℂ)) (α + 1)
  rw [show (1 : ℂ) + ((n : ℂ) + α + β + 1) - (α + 1) - n = β + 1 by ring,
    show (-(N : ℂ)) - -x = -((N : ℂ) - x) by ring,
    show ({(-(n : ℂ)), (n : ℂ) + α + β + 1, -((N : ℂ) - x)} : Multiset ℂ) =
      {(-(n : ℂ)), -((N : ℂ) - x), (n : ℂ) + β + α + 1} by
        rw [show (n : ℂ) + α + β + 1 = n + β + α + 1 by ring]
        change -(n : ℂ) ::ₘ ((n : ℂ) + β + α + 1) ::ₘ (-((N : ℂ) - x)) ::ₘ 0 =
          -(n : ℂ) ::ₘ (-((N : ℂ) - x)) ::ₘ ((n : ℂ) + β + α + 1) ::ₘ 0
        rw [Multiset.cons_swap ((n : ℂ) + β + α + 1) (-((N : ℂ) - x))],
    clearedHypergeometric_eq_hahn hn hαc, clearedHypergeometric_eq_hahn hn hβc] at h
  have hc : pochhammer ((α : ℂ) + 1) n * DLMF.OrthogonalPolynomials.hahn α β N n x =
      (-1 : ℂ) ^ n * pochhammer ((β : ℂ) + 1) n *
        DLMF.OrthogonalPolynomials.hahn β α N n (N - x) := by
    apply mul_left_cancel₀ (pochhammer_neg_natCast_ne_zero hn)
    linear_combination h
  rw [← hp, ← hp, ← hahn_eq_dlmf] at hc
  have hx : (((N : ℝ) - x : ℝ) : ℂ) = (N : ℂ) - x := by push_cast; rfl
  rw [← hx, ← hahn_eq_dlmf] at hc
  exact_mod_cast hc

/-! ### Racah polynomials -/

/-- **6-j symbols are Racah polynomials** (Vilenkin–Klimyk §8.5.4, corrected). For doubled
spins `(e₁, e₂, e₃, e) = 2(l₁, l₂, l₃, l)`,
`{l₁ l₂ l + l₃ - x; l₃ l l₂ + l₃ - n} = C_n W_x R_n(λ(x); α, β, γ, δ)` with `α = -2l₃ - 1`,
`β = -2l₂ - 1`, `γ = -l₁ - l₂ - l₃ - l - 2` and `δ = l₁ + l₂ - l₃ - l`. -/
theorem sixJ_eq_racahPolynomial {e₁ e₂ e₃ e x n : ℕ} (hpar : Even (e₁ + e₂ + e₃ + e))
    (hx : x ≤ e₃) (hn : n ≤ e₃) (hx₁ : e₃ + e ≤ e₁ + e₂ + 2 * x)
    (hx₂ : e₁ + 2 * x ≤ e₂ + e₃ + e) (hn₁ : e₂ + e₃ ≤ e₁ + e + 2 * n)
    (hn₂ : e₁ + 2 * n ≤ e + e₂ + e₃) (hx₃ : 2 * x ≤ e + e₃) (hn₃ : 2 * n ≤ e₂ + e₃) :
    sixJ e₁ e₂ (e + e₃ - 2 * x) e₃ e (e₂ + e₃ - 2 * n) =
      (-1) ^ ((e₁ + e₂ + e₃ + e) / 2) *
        triangleCoefficient e₁ e (e₂ + e₃ - 2 * n) *
        triangleCoefficient e₂ e₃ (e₂ + e₃ - 2 * n) *
        (((e₂ + e₃ + e - e₁) / 2).factorial * ((e₁ + e₂ + e₃ + e) / 2 + 1).factorial *
          e₃.factorial : ℕ) /
        (((e₁ + e + 2 * n - e₂ - e₃) / 2).factorial *
          ((e + e₂ + e₃ - e₁ - 2 * n) / 2).factorial * (e₃ - n).factorial * n.factorial : ℕ) *
      (triangleCoefficient e₃ e (e + e₃ - 2 * x) * triangleCoefficient e₁ e₂ (e + e₃ - 2 * x) /
        (((e₃ - x).factorial * x.factorial * ((e₁ + e₂ + 2 * x - e₃ - e) / 2).factorial *
          ((e₂ + e₃ + e - e₁ - 2 * x) / 2).factorial : ℕ) : ℝ)) *
      racahPolynomial n (-(e₃ : ℝ) - 1) (-(e₂ : ℝ) - 1) (-((e₁ + e₂ + e₃ + e : ℕ) : ℝ) / 2 - 2)
        (((e₁ + e₂ : ℕ) : ℝ) / 2 - ((e₃ + e : ℕ) : ℝ) / 2) x := by
  sorry

/-- **Racah orthogonality** (DLMF 18.25.9, 18.25.11–18.25.12) in the case `α + 1 = -N`, for real
`β, γ, δ` keeping every Pochhammer symbol in a denominator nonzero. -/
theorem sum_racahPolynomial_mul {N n m : ℕ} (hn : n ≤ N) (hm : m ≤ N) {β γ δ : ℝ}
    (hpar : ∀ k : ℕ, k ≤ 2 * N + 1 → β + δ + 1 + k ≠ 0 ∧ γ + 1 + k ≠ 0 ∧ γ + δ + 1 + k ≠ 0 ∧
      N + γ + δ + 2 + k ≠ 0 ∧ γ - β + 1 + k ≠ 0 ∧ δ + 1 + k ≠ 0 ∧ β - N + 1 + k ≠ 0) :
    ∑ y ∈ Finset.range (N + 1),
        racahPolynomial n (-(N : ℝ) - 1) β γ δ y * racahPolynomial m (-(N : ℝ) - 1) β γ δ y *
          ((γ + δ + 1 + 2 * y) / (γ + δ + 1 + y)) *
          ((ascPochhammer ℝ y).eval (-(N : ℝ)) * (ascPochhammer ℝ y).eval (β + δ + 1) *
              (ascPochhammer ℝ y).eval (γ + 1) * (ascPochhammer ℝ y).eval (γ + δ + 2) /
            ((ascPochhammer ℝ y).eval (N + γ + δ + 2) * (ascPochhammer ℝ y).eval (γ - β + 1) *
              (ascPochhammer ℝ y).eval (δ + 1) * y.factorial)) =
      if n = m then
        (ascPochhammer ℝ N).eval (-β) * (ascPochhammer ℝ N).eval (γ + δ + 2) /
            ((ascPochhammer ℝ N).eval (γ - β + 1) * (ascPochhammer ℝ N).eval (δ + 1)) *
          ((ascPochhammer ℝ n).eval (n + β - N) * n.factorial /
            (ascPochhammer ℝ (2 * n)).eval (β - N + 1)) *
          ((ascPochhammer ℝ n).eval (β - N - γ) * (ascPochhammer ℝ n).eval (-(N : ℝ) - δ) *
              (ascPochhammer ℝ n).eval (β + 1) /
            ((ascPochhammer ℝ n).eval (-(N : ℝ)) * (ascPochhammer ℝ n).eval (β + δ + 1) *
              (ascPochhammer ℝ n).eval (γ + 1)))
      else 0 := by
  sorry

/-- **Conversion to lean-DLMF's complex Racah polynomial** (DLMF 18.26.3), whose variable is
`λ(y) = y (y + γ + δ + 1)`. -/
theorem racahPolynomial_eq_dlmf (n : ℕ) (α β γ δ y : ℝ) :
    (racahPolynomial n α β γ δ y : ℂ) =
      DLMF.OrthogonalPolynomials.racah α β γ δ n (y * (y + γ + δ + 1)) := by
  simp only [racahPolynomial, DLMF.OrthogonalPolynomials.racah]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  have hprod : (∏ j ∈ Finset.range k, ((j : ℂ) * (j + γ + δ + 1) - y * (y + γ + δ + 1))) =
      (ascPochhammer ℂ k).eval (-(y : ℂ)) * (ascPochhammer ℂ k).eval ((y : ℂ) + γ + δ + 1) := by
    rw [ascPochhammer_eval_mul_eq_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  rw [hprod]
  simp only [DLMF.Hypergeometric.pochhammer, ofReal_ascPochhammer_eval]
  push_cast
  ring

/-- **Hahn polynomials as limits of Racah polynomials** (DLMF 18.26.10). The complex limit
in lean-DLMF holds for the full domain of the totalized finite sums. -/
theorem tendsto_racahPolynomial_hahn {N n : ℕ} {α : ℝ} (β x : ℝ) :
    Tendsto (fun δ ↦ racahPolynomial n α β (-(N : ℝ) - 1) δ x) atTop
      (𝓝 (hahn N n α β x)) := by
  apply Filter.tendsto_ofReal_iff.mp
  rw [hahn_eq_dlmf]
  refine (DLMF.OrthogonalPolynomials.racah_limit_hahn (α := (α : ℂ)) (β := (β : ℂ))
    (N := N) (n := n) (x : ℂ)).congr' (Eventually.of_forall fun δ => ?_)
  beta_reduce
  rw [racahPolynomial_eq_dlmf]
  push_cast
  congr 1
  ring

end SFVK.ClebschGordan
