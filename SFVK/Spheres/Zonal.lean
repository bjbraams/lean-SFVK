/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

import Mathlib.Algebra.MvPolynomial.Funext
import SFVK.Spheres.SphereMeasure
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import TauCeti.Analysis.MvPolynomial.Laplacian
import TauCeti.Analysis.InnerProductSpace.Laplacian.Zonal
import DLMF.OrthogonalPolynomials.Topics
import DLMF.OrthogonalPolynomials.Integrals.GegenbauerAndLegendre
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import TauCeti.Analysis.MvPolynomial.Sphere
public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import SFVK.Spheres.Basic

/-!
# Spherical harmonics, zonal polynomials and Gegenbauer polynomials

The closed dimension of the harmonic polynomials of degree `l` on `ℝⁿ`; the parity, degree,
hypergeometric, Gegenbauer, Chebyshev and Legendre forms of the normalized zonal polynomial
`ω_{n,l}`; its derivative and differential equation; the zonal harmonic `Z_{l,η}`, its
harmonicity, its values on the sphere, its invariance under `K_η` and its uniqueness; and the
Laplace integral. The proofs use the lean-DLMF terminating Gauss series, the Chebyshev and
Gegenbauer comparisons, and the Gauss differential equation. The dimension and harmonicity proofs
use Tau Ceti's harmonic dimension formula and its Laplacian formulas for Euclidean polynomial
evaluation and for functions of the radius and the zonal coordinate.

The value at one, the generating function and the derivative of the Gegenbauer polynomials are
lean-DLMF's `DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_at_one`,
`DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_generating_function` and
`DLMF.OrthogonalPolynomials.ultrasphericalPolynomial_derivative`; they are not restated here.

Sources: Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2, §9.2.3
(3)–(5), p. 30 (the harmonic projection and the dimension; the printed dimension of the
homogeneous polynomials is corrected in erratum E09.2.01 of the project's errata file), §9.3.2
(2)–(4), p. 47 (the zonal spherical function, its Laplace integral and its Gegenbauer form), and
§10.2.1, p. 173 (uniqueness of the zonal harmonic; the denominator of the second display is
`C_l^{(n-2)/2}(1)`, erratum E10.2.01); Wawrzyńczyk, *Group Representations and Special
Functions*, (9.2.9)–(9.2.11), p. 330, and §9.4, p. 335; Dieudonné, *Special Functions and Linear
Representations of Lie Groups*, §7, (99) and (103), pp. 23–24.
-/

public noncomputable section

open Filter Polynomial Real Set
open DLMF.Hypergeometric DLMF.OrthogonalPolynomials
open scoped Nat InnerProductSpace Topology

namespace SFVK.Spheres

/-! ### Dimension -/

/-- **Closed dimension formula** (Vilenkin–Klimyk, Vol. 2, §9.2.3 (4), p. 30; Wawrzyńczyk §9.4,
p. 335). For `n ≥ 3`, `dim H_l(ℝⁿ) = (2l + n - 2)(l + n - 3)!/((n - 2)! l!)`. -/
theorem finrank_harmonicSubmodule_mul {n : ℕ} (hn : 3 ≤ n) (l : ℕ) :
    Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin n) ℝ l) * ((n - 2)! * l !) =
      (2 * l + n - 2) * (l + n - 3)! := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rcases l with _ | _ | l
  · rw [MvPolynomial.finrank_harmonicSubmodule_of_le_one (by decide : 0 ≤ 1)]
    simp only [Fintype.card_fin, Nat.multichoose_zero_right, Nat.factorial_zero, mul_one, one_mul,
      mul_zero, zero_add, Nat.add_sub_cancel]
    rw [show m + 3 - 2 = m + 1 by omega, Nat.factorial_succ]
  · rw [MvPolynomial.finrank_harmonicSubmodule_of_le_one (by decide : 1 ≤ 1)]
    simp only [Fintype.card_fin, Nat.multichoose_one_right]
    rw [show m + 3 - 2 = m + 1 by omega, show 2 * (0 + 1) + (m + 3) - 2 = m + 3 by omega,
      show (0 + 1) + (m + 3) - 3 = m + 1 by omega]
    simp
  · change Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (m + 3)) ℝ (l + 2)) *
        ((m + 3 - 2)! * (l + 2)!) = (2 * (l + 2) + (m + 3) - 2) * (l + 2 + (m + 3) - 3)!
    rw [show m + 3 - 2 = m + 1 by omega,
      show 2 * (l + 2) + (m + 3) - 2 = 2 * l + m + 5 by omega,
      show l + 2 + (m + 3) - 3 = l + m + 2 by omega]
    have hdim := MvPolynomial.finrank_harmonicSubmodule_add_finrank
      (σ := Fin (m + 3)) (K := ℝ) l
    rw [TauCeti.finrank_homogeneousSubmodule_eq_multichoose,
      TauCeti.finrank_homogeneousSubmodule_eq_multichoose, Fintype.card_fin, Nat.multichoose_eq,
      Nat.multichoose_eq, show m + 3 + l - 1 = l + m + 2 by omega,
      show m + 3 + (l + 2) - 1 = l + m + 4 by omega] at hdim
    have hfirst := Nat.choose_mul_factorial_mul_factorial (n := l + m + 4) (k := l + 2)
      (by omega)
    rw [show l + m + 4 - (l + 2) = m + 2 by omega,
      show l + m + 4 = (l + m + 2) + 1 + 1 by omega,
      Nat.factorial_succ (l + m + 2 + 1), Nat.factorial_succ (l + m + 2),
      show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ (m + 1)] at hfirst
    have hsecond := Nat.choose_mul_factorial_mul_factorial (n := l + m + 2) (k := l) (by omega)
    rw [show l + m + 2 - l = (m + 1) + 1 by omega, Nat.factorial_succ (m + 1)] at hsecond
    let d := Module.finrank ℝ (MvPolynomial.harmonicSubmodule (Fin (m + 3)) ℝ (l + 2))
    change d * ((m + 1)! * (l + 2)!) = (2 * l + m + 5) * (l + m + 2)!
    have hd : (d : ℝ) + (l + m + 2).choose l = (l + m + 4).choose (l + 2) := by
      exact_mod_cast hdim
    have hf : ((l + m + 4).choose (l + 2) : ℝ) * (l + 2)! * ((m + 2) * (m + 1)!) =
        (l + m + 4) * ((l + m + 3) * (l + m + 2)!) := by
      have h := congrArg (Nat.cast (R := ℝ)) hfirst
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
      rw [show l + m + 2 + 1 + 1 = l + m + 4 by omega] at h
      linear_combination h
    have hs : ((l + m + 2).choose l : ℝ) * l ! * ((m + 2) * (m + 1)!) = (l + m + 2)! := by
      have h := congrArg (Nat.cast (R := ℝ)) hsecond
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
      linear_combination h
    have hsucc : ((l + 2)! : ℝ) = ((l : ℝ) + 2) * (l + 1) * l ! := by
      rw [show l + 2 = (l + 1) + 1 by omega, Nat.factorial_succ (l + 1), Nat.factorial_succ l]
      push_cast
      ring
    apply Nat.cast_inj (R := ℝ).mp
    push_cast
    apply mul_left_cancel₀ (show (m : ℝ) + 2 ≠ 0 by positivity)
    rw [hsucc] at hf ⊢
    linear_combination hf - ((l : ℝ) + 2) * (l + 1) * hs +
      ((m : ℝ) + 2) * ((m + 1)! : ℝ) * (l + 2) * (l + 1) * l ! * hd

/-! ### The zonal polynomial -/

namespace ZonalPolynomials

/-- Coercion of the real rising factorial to the complex normalization. -/
private theorem ofReal_ascPochhammer_eval (k : ℕ) (r : ℝ) :
    (((ascPochhammer ℝ k).eval r : ℝ) : ℂ) = pochhammer (r : ℂ) k := by
  rw [pochhammer, ← Complex.ofRealHom_eq_coe, ← Polynomial.eval₂_at_apply,
    ← Polynomial.eval_map, ascPochhammer_map]
  rfl

/-- Evaluation of the complexification of the zonal polynomial by the terminating Gauss series. -/
private theorem eval_map_zonalPolynomial_eq_gauss (n l : ℕ) (x : ℂ) :
    ((zonalPolynomial n l).map Complex.ofRealHom).eval x =
      ₂F₁ (-(l : ℂ)) ((l : ℂ) + n - 2) (((n : ℂ) - 1) / 2) ((1 - x) / 2) := by
  rw [ordinaryHypergeometric_eq_sum_neg_nat, ← Polynomial.eval₂_eq_eval_map, zonalPolynomial_def,
    Polynomial.eval₂_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_X, Complex.ofRealHom_eq_coe,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat,
    ofReal_ascPochhammer_eval, gaussHypergeometricCoeff]
  ring

/-- The terminating Gauss series on the real axis. -/
private theorem eval_zonalPolynomial_eq_gauss (n l : ℕ) (x : ℝ) :
    (((zonalPolynomial n l).eval x : ℝ) : ℂ) =
      ₂F₁ (-(l : ℂ)) ((l : ℂ) + n - 2) (((n : ℂ) - 1) / 2) ((1 - (x : ℂ)) / 2) := by
  rw [← Complex.ofRealHom_eq_coe, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
  exact eval_map_zonalPolynomial_eq_gauss n l x

/-- The positive lower Gauss parameter avoids every nonpositive integer. -/
private theorem zonalParameter_ne_neg_nat {n : ℕ} (hn : 2 ≤ n) :
    ∀ k : ℕ, (((n : ℂ) - 1) / 2) ≠ -(k : ℂ) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact not_neg_nat_of_re_pos (by simp; linarith)

end ZonalPolynomials

open ZonalPolynomials

/-- **Gegenbauer form** (Vilenkin–Klimyk, Vol. 2, §9.3.2 (4), p. 47; Wawrzyńczyk (9.2.11),
p. 330). For `n ≥ 3` and `λ = (n - 2)/2`, `ω_{n,l}(x) = C_l^{(λ)}(x)/C_l^{(λ)}(1)` with lean-DLMF's
Gegenbauer polynomial. -/
theorem zonalPolynomial_eq_ultrasphericalPolynomial_div {n : ℕ} (hn : 3 ≤ n) (l : ℕ) (x : ℝ) :
    (((zonalPolynomial n l).eval x : ℝ) : ℂ) =
      DLMF.OrthogonalPolynomials.ultrasphericalPolynomial (((n : ℂ) - 2) / 2) l x /
        DLMF.OrthogonalPolynomials.ultrasphericalPolynomial (((n : ℂ) - 2) / 2) l 1 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlambda : 0 < (((n : ℂ) - 2) / 2).re := by simp; linarith
  rw [ultrasphericalPolynomial_div_at_one hlambda, eval_zonalPolynomial_eq_gauss]
  congr 1 <;> ring

/-- **Chebyshev.** `ω_{2,l} = T_l`. -/
theorem zonalPolynomial_two (l : ℕ) : zonalPolynomial 2 l = Chebyshev.T ℝ l := by
  apply Polynomial.funext
  intro x
  apply Complex.ofReal_injective
  have hT : (((Chebyshev.T ℝ (l : ℤ)).eval x : ℝ) : ℂ) =
      (Chebyshev.T ℂ (l : ℤ)).eval (x : ℂ) := Chebyshev.algebraMap_eval_T x l
  rw [eval_zonalPolynomial_eq_gauss, hT, chebyshevT_hypergeometric]
  norm_num

/-- **Legendre.** `ω_{3,l} = P_l`, with lean-DLMF's Legendre polynomial. -/
theorem zonalPolynomial_three (l : ℕ) (x : ℝ) :
    (((zonalPolynomial 3 l).eval x : ℝ) : ℂ) =
      DLMF.OrthogonalPolynomials.legendrePolynomialP l x := by
  rw [zonalPolynomial_eq_ultrasphericalPolynomial_div (by decide : 3 ≤ 3),
    legendre_eq_ultrasphericalPolynomial]
  norm_num
  rw [ultrasphericalPolynomial_at_one, show (2 : ℂ) * (1 / 2) = 1 by norm_num,
    pochhammer_nat_one, div_self (Nat.cast_ne_zero.mpr l.factorial_ne_zero), div_one]

/-- **`n = 4`.** `(l + 1) ω_{4,l} = U_l`, the Chebyshev polynomial of the second kind. -/
theorem zonalPolynomial_four (l : ℕ) :
    C ((l : ℝ) + 1) * zonalPolynomial 4 l = Chebyshev.U ℝ l := by
  apply Polynomial.funext
  intro x
  apply Complex.ofReal_injective
  have hU : (((Chebyshev.U ℝ (l : ℤ)).eval x : ℝ) : ℂ) =
      (Chebyshev.U ℂ (l : ℤ)).eval (x : ℂ) := Chebyshev.algebraMap_eval_U x l
  rw [Polynomial.eval_mul, Polynomial.eval_C, Complex.ofReal_mul, eval_zonalPolynomial_eq_gauss,
    hU, eval_U_eq_ultrasphericalPolynomial,
    ultrasphericalPolynomial_param_one_eq]
  push_cast
  congr 2 <;> ring

/-- **Parity.** `ω_{n,l}(-t) = (-1)ˡ ω_{n,l}(t)` for `n ≥ 2`. -/
theorem zonalPolynomial_comp_neg {n : ℕ} (hn : 2 ≤ n) (l : ℕ) :
    (zonalPolynomial n l).comp (-X) = (-1) ^ l * zonalPolynomial n l := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_one]
  by_cases h : n = 2
  · subst n
    rw [zonalPolynomial_two, Chebyshev.T_eval_neg, Int.cast_negOnePow_natCast]
  · have hn' : 3 ≤ n := by omega
    have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn'
    have hlambda : -1 / 2 < (((n : ℂ) - 2) / 2).re := by simp; linarith
    apply Complex.ofReal_injective
    push_cast
    rw [zonalPolynomial_eq_ultrasphericalPolynomial_div hn',
      zonalPolynomial_eq_ultrasphericalPolynomial_div hn',
      Complex.ofReal_neg, ultrasphericalPolynomial_reflection hlambda, mul_div_assoc]

/-- **Degree.** `ω_{n,l}` has degree `l` for `n ≥ 2`. -/
theorem natDegree_zonalPolynomial {n : ℕ} (hn : 2 ≤ n) (l : ℕ) :
    (zonalPolynomial n l).natDegree = l := by
  cases l with
  | zero => simp
  | succ l =>
    have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlReal : (1 : ℝ) ≤ l + 1 := by linarith [Nat.cast_nonneg (α := ℝ) l]
    let s (k : ℕ) := (ascPochhammer ℝ k).eval (-(↑(l + 1 : ℕ) : ℝ)) *
      (ascPochhammer ℝ k).eval ((↑(l + 1 : ℕ) : ℝ) + n - 2) /
        ((ascPochhammer ℝ k).eval (((n : ℝ) - 1) / 2) * k.factorial)
    let p : ℝ[X] := C (1 / 2) * (1 - X)
    have hp : p.natDegree = 1 := by
      dsimp only [p]
      rw [natDegree_C_mul (by norm_num), natDegree_sub_eq_right_of_natDegree_lt (by simp),
        natDegree_X]
    have hs : s (l + 1) ≠ 0 := by
      have hpos (k : ℕ) (r : ℝ) (hr : 0 < r) : (ascPochhammer ℝ k).eval r ≠ 0 := by
        intro hz
        obtain ⟨j, _, hj⟩ := (ascPochhammer_eval_eq_zero_iff ..).mp hz
        linarith [Nat.cast_nonneg (α := ℝ) j]
      refine div_ne_zero (mul_ne_zero ?_ (hpos _ _ (by push_cast; linarith)))
        (mul_ne_zero (hpos _ _ (by linarith)) (Nat.cast_ne_zero.mpr (l + 1).factorial_ne_zero))
      intro hz
      obtain ⟨j, hj, he⟩ := (ascPochhammer_eval_eq_zero_iff ..).mp hz
      rw [neg_neg] at he
      exact (Nat.ne_of_lt hj) (by exact_mod_cast he)
    change (∑ k ∈ Finset.range (l + 1 + 1), C (s k) * p ^ k).natDegree = l + 1
    rw [Finset.sum_range_succ, natDegree_add_eq_right_of_natDegree_lt,
      natDegree_C_mul hs, natDegree_pow, hp, mul_one]
    rw [natDegree_C_mul hs, natDegree_pow, hp, mul_one]
    calc
      _ ≤ (Finset.range (l + 1)).sup (fun k => (C (s k) * p ^ k).natDegree) :=
        natDegree_sum_le _ _
      _ ≤ l := Finset.sup_le fun k hk => by
        refine (natDegree_C_mul_le _ _).trans ?_
        rw [natDegree_pow, hp, mul_one]
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      _ < l + 1 := Nat.lt_succ_self _

/-- **Derivative.** `ω_{n,l+1}' = ((l + 1)(l + n - 1)/(n - 1)) ω_{n+2,l}` for `n ≥ 2`. -/
theorem derivative_zonalPolynomial {n : ℕ} (hn : 2 ≤ n) (l : ℕ) :
    derivative (zonalPolynomial n (l + 1)) =
      C (((l : ℝ) + 1) * ((l : ℝ) + n - 1) / ((n : ℝ) - 1)) * zonalPolynomial (n + 2) l := by
  apply Polynomial.map_injective (f := Complex.ofRealHom) Complex.ofReal_injective
  apply Polynomial.funext
  intro x
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C,
    ← Polynomial.derivative_map, ← Polynomial.deriv, Complex.ofRealHom_eq_coe,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_natCast, Complex.ofReal_one, eval_map_zonalPolynomial_eq_gauss]
  rw [deriv_half_shift, deriv_gauss_neg_nat_succ _ _ (zonalParameter_ne_neg_nat hn)]
  push_cast
  have hb : ((l : ℂ) + 1 + n - 2) + 1 = (l : ℂ) + (n + 2) - 2 := by ring
  have hc : (((n : ℂ) - 1) / 2) + 1 = ((n : ℂ) + 2 - 1) / 2 := by ring
  rw [hb, hc]
  have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hne : (n : ℂ) - 1 ≠ 0 := Complex.ne_zero_of_re_pos (by simp; linarith)
  field_simp [hne]; ring

/-- **Differential equation.** For `n ≥ 2`,
`(1 - t²) ω'' - (n - 1) t ω' + l(l + n - 2) ω = 0`. -/
theorem zonalPolynomial_ode {n : ℕ} (hn : 2 ≤ n) (l : ℕ) :
    (1 - X ^ 2) * derivative (derivative (zonalPolynomial n l)) -
        C ((n : ℝ) - 1) * X * derivative (zonalPolynomial n l) +
      C ((l : ℝ) * ((l : ℝ) + n - 2)) * zonalPolynomial n l = 0 := by
  let f : ℂ → ℂ := ordinaryHypergeometric (-(l : ℂ)) ((l : ℂ) + n - 2) (((n : ℂ) - 1) / 2)
  let p : ℂ[X] := (zonalPolynomial n l).map Complex.ofRealHom
  have hf : (fun x : ℂ => p.eval x) = fun x => f ((1 - x) / 2) :=
    funext (eval_map_zonalPolynomial_eq_gauss n l)
  have hd : (fun x : ℂ => p.derivative.eval x) =
      fun x => (-1 / 2 : ℂ) * deriv f ((1 - x) / 2) := by
    have he : (fun x : ℂ => p.derivative.eval x) = deriv (fun x : ℂ => p.eval x) :=
      funext fun x => (p.deriv (x := x)).symm
    rw [he, hf, deriv_half_shift]
  have hdd : (fun x : ℂ => p.derivative.derivative.eval x) =
      fun x => (-1 / 2 : ℂ) * (-1 / 2) * deriv (deriv f) ((1 - x) / 2) := by
    have he : (fun x : ℂ => p.derivative.derivative.eval x) =
        deriv (fun x : ℂ => p.derivative.eval x) :=
      funext fun x => (p.derivative.deriv (x := x)).symm
    rw [he, hd, deriv_const_mul_field', deriv_half_shift]
    funext x
    ring
  apply Polynomial.map_injective (f := Complex.ofRealHom) Complex.ofReal_injective
  apply Polynomial.funext
  intro x
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_one, Polynomial.map_zero,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_zero,
    ← Polynomial.derivative_map, Complex.ofRealHom_eq_coe, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  have h := gauss_neg_nat_ode l ((l : ℂ) + n - 2) (zonalParameter_ne_neg_nat hn) ((1 - x) / 2)
  change (1 - x ^ 2) * p.derivative.derivative.eval x -
    ((n : ℂ) - 1) * x * p.derivative.eval x + (l : ℂ) * ((l : ℂ) + n - 2) * p.eval x = 0
  rw [congrFun hdd x, congrFun hd x, congrFun hf x]
  exact (by dsimp only [f]; linear_combination h)

/-! ### The zonal harmonic -/

/-- The zonal polynomial has no coefficients of parity opposite to its degree. -/
theorem coeff_zonalPolynomial_eq_zero_of_not_even {n l j : ℕ} (hn : 2 ≤ n) (hj : j ≤ l)
    (hpar : ¬Even (l - j)) : (zonalPolynomial n l).coeff j = 0 := by
  have he := congrArg (fun p : ℝ[X] => p.coeff j) (zonalPolynomial_comp_neg hn l)
  have hneg : (-(X : ℝ[X])) = C (-1) * X := by simp
  simp only [hneg, comp_C_mul_X_coeff, ← C_neg, ← C_1, ← map_pow, coeff_C_mul] at he
  have hl : (-1 : ℝ) ^ l = -((-1 : ℝ) ^ j) := by
    calc
      _ = (-1 : ℝ) ^ (j + (l - j)) := by rw [Nat.add_sub_of_le hj]
      _ = _ := by rw [pow_add, (Nat.not_even_iff_odd.mp hpar).neg_one_pow, mul_neg_one]
  rw [hl] at he
  rcases neg_one_pow_eq_or ℝ j with hh | hh <;> rw [hh] at he <;> linarith

private theorem eval_zonalHarmonic_of_ne_zero {n : ℕ} (hn : 2 ≤ n) (l : ℕ)
    (η : EuclideanSpace ℝ (Fin n)) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    MvPolynomial.eval (fun i => x i) (zonalHarmonic n l η) =
      ‖x‖ ^ l * (zonalPolynomial n l).eval (⟪η, x⟫_ℝ / ‖x‖) := by
  have hp := (zonalPolynomial n l).as_sum_range_C_mul_X_pow
  rw [natDegree_zonalPolynomial hn] at hp
  conv_rhs => congr; rfl; rw [hp]
  simp only [zonalHarmonic_def, map_sum, apply_ite (MvPolynomial.eval _), map_zero, map_mul,
    map_pow, MvPolynomial.eval_C, eval_linearForm, MvPolynomial.eval_normSq,
    ← EuclideanSpace.real_norm_sq_eq, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjl : j ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  by_cases hpar : Even (l - j)
  · rw [ite_eq_left hpar, div_pow, ← pow_mul]
    have he : l = 2 * ((l - j) / 2) + j := by
      obtain ⟨t, ht⟩ := hpar
      omega
    conv_rhs => lhs; rw [he, pow_add]
    field_simp [pow_ne_zero j (norm_ne_zero_iff.mpr hx)]
  · rw [ite_eq_right hpar, coeff_zonalPolynomial_eq_zero_of_not_even hn hjl hpar,
      zero_mul, mul_zero]

private theorem isHomogeneous_zonalHarmonic (n l : ℕ) (η : EuclideanSpace ℝ (Fin n)) :
    (zonalHarmonic n l η).IsHomogeneous l := by
  have hL : (linearForm η).IsHomogeneous 1 := by
    rw [linearForm_def]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_
    exact (MvPolynomial.isHomogeneous_C _ _).mul (MvPolynomial.isHomogeneous_X ℝ j)
  rw [zonalHarmonic_def]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hjl : j ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  split_ifs with hpar
  · have hdegree : 0 + 1 * j + 2 * ((l - j) / 2) = l := by
      obtain ⟨t, ht⟩ := hpar
      omega
    have hstep := ((MvPolynomial.isHomogeneous_C (Fin n) ((zonalPolynomial n l).coeff j)).mul
      (hL.pow j)).mul ((MvPolynomial.isHomogeneous_normSq (Fin n) ℝ).pow ((l - j) / 2))
    rw [hdegree] at hstep
    exact hstep
  · exact MvPolynomial.isHomogeneous_zero _ _ _

set_option maxHeartbeats 1000000 in
/-- **The zonal harmonic is harmonic of degree `l`**, for `n ≥ 2` and a unit vector `η`
(Vilenkin–Klimyk, Vol. 2, §10.2.1, p. 173; Wawrzyńczyk (9.2.9)–(9.2.11), p. 330). -/
theorem zonalHarmonic_mem_harmonicSubmodule {n : ℕ} (hn : 2 ≤ n) (l : ℕ)
    {η : EuclideanSpace ℝ (Fin n)} (hη : ‖η‖ = 1) :
    zonalHarmonic n l η ∈ MvPolynomial.harmonicSubmodule (Fin n) ℝ l := by
  rw [MvPolynomial.mem_harmonicSubmodule_iff]
  refine ⟨isHomogeneous_zonalHarmonic n l η, ?_⟩
  let E := EuclideanSpace ℝ (Fin n)
  let p := zonalHarmonic n l η
  let P := zonalPolynomial n l
  let F (x : E) := MvPolynomial.eval (fun i => x i) p
  let G (x : E) := ‖x‖ ^ (l : ℝ) * P.eval (⟪η, x⟫_ℝ / ‖x‖)
  have hFG {x : E} (hx : x ≠ 0) : F x = G x := by
    dsimp only [F, G, p, P]
    rw [Real.rpow_natCast, eval_zonalHarmonic_of_ne_zero hn l η hx]
  have hLap {x : E} (hx : x ≠ 0) : Laplacian.laplacian F x = 0 := by
    have ho : F =ᶠ[𝓝 x] G := (isOpen_compl_singleton.eventually_mem (by simpa using hx)).mono
      fun y hy => hFG (by simpa using hy)
    rw [(InnerProductSpace.laplacian_congr_nhds ho).self_of_nhds]
    have hd : ContDiffAt ℝ 2 (fun y : ℝ => P.eval y) (⟪η, x⟫_ℝ / ‖x‖) := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        (P.contDiff_aeval (𝕜 := ℝ) 2).contDiffAt (x := ⟪η, x⟫_ℝ / ‖x‖)
    have h := TauCeti.laplacian_norm_rpow_mul_comp_inner_div_norm (F := fun y => P.eval y)
      hη hx (l : ℝ) hd
    dsimp only [G]
    rw [h]
    have hderiv : deriv (fun t : ℝ => P.eval t) = fun t : ℝ => P.derivative.eval t :=
      funext fun t => P.deriv (x := t)
    rw [hderiv]
    simp only [finrank_euclideanSpace_fin, Polynomial.deriv]
    have he := congrArg (fun q : ℝ[X] => q.eval (⟪η, x⟫_ℝ / ‖x‖))
      (zonalPolynomial_ode hn l)
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_one, eval_X, eval_C, eval_zero] at he
    have hzero : (l : ℝ) * ((l : ℝ) + n - 2) * P.eval (⟪η, x⟫_ℝ / ‖x‖) +
        (1 - (⟪η, x⟫_ℝ / ‖x‖) ^ 2) * P.derivative.derivative.eval (⟪η, x⟫_ℝ / ‖x‖) -
        ((n : ℝ) - 1) * (⟪η, x⟫_ℝ / ‖x‖) * P.derivative.eval (⟪η, x⟫_ℝ / ‖x‖) = 0 := by
      dsimp only [P]
      linear_combination he
    rw [hzero, mul_zero]
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hdense : Dense ({0}ᶜ : Set E) := dense_compl_singleton _
  have hlap : Laplacian.laplacian F = fun _ => 0 := by
    refine Continuous.ext_on hdense ?_ continuous_const fun x hx => hLap (by simpa using hx)
    change Continuous (Laplacian.laplacian (fun x : E => MvPolynomial.eval x p))
    rw [MvPolynomial.laplacian_eval_euclidean]
    exact (AnalyticOnNhd.eval_continuousLinearMap
      (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap (MvPolynomial.laplacian p)).continuous
  apply MvPolynomial.funext
  intro y
  change MvPolynomial.eval y (MvPolynomial.laplacian p) = _
  let x : E := WithLp.toLp 2 y
  have he := congrFun hlap x
  have hcomm := congrFun (MvPolynomial.laplacian_eval_euclidean p) x
  exact hcomm.symm.trans he

/-- **Values on the sphere.** For `n ≥ 2` and `|x| = 1`, `Z_{l,η}(x) = ω_{n,l}(⟪η, x⟫)`. -/
theorem eval_zonalHarmonic {n : ℕ} (hn : 2 ≤ n) (l : ℕ) (η : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ = 1) :
    MvPolynomial.eval (fun i => x i) (zonalHarmonic n l η) =
      (zonalPolynomial n l).eval ⟪η, x⟫_ℝ := by
  rw [eval_zonalHarmonic_of_ne_zero hn l η (norm_ne_zero_iff.mp (by rw [hx]; norm_num)), hx]
  simp

/-- **`K_η`-invariance of the zonal harmonic.** -/
theorem eval_rotate_zonalHarmonic {n : ℕ} (l : ℕ) (η : EuclideanSpace ℝ (Fin n))
    {k : RotationGroup n} (hk : k ∈ rotationStabilizer η) (x : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial.eval (fun i => rotate k x i) (zonalHarmonic n l η) =
      MvPolynomial.eval (fun i => x i) (zonalHarmonic n l η) := by
  have hη : rotate k η = η := mem_rotationStabilizer.mp hk
  have hinner : ⟪η, rotate k x⟫_ℝ = ⟪η, x⟫_ℝ := by
    simpa only [hη] using inner_rotate_rotate k η x
  have hnorm : MvPolynomial.eval (fun i => rotate k x i) (MvPolynomial.normSq (Fin n) ℝ) =
      MvPolynomial.eval (fun i => x i) (MvPolynomial.normSq (Fin n) ℝ) := by
    rw [MvPolynomial.eval_normSq, MvPolynomial.eval_normSq]
    change ∑ i, (rotate k x).ofLp i ^ 2 = ∑ i, x.ofLp i ^ 2
    rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
    simpa only [real_inner_self_eq_norm_sq] using inner_rotate_rotate k x x
  simp only [zonalHarmonic_def, map_sum, apply_ite (MvPolynomial.eval _), map_zero, map_mul,
    map_pow, MvPolynomial.eval_C, eval_linearForm, hinner, hnorm]

/-- **Uniqueness of the zonal harmonic** (Vilenkin–Klimyk, Vol. 2, §10.2.1, Lemma, p. 173;
Dieudonné §7, p. 23). For `n ≥ 3` and a unit vector `η`, a `K_η`-invariant harmonic polynomial
of degree `l` is `p(η) Z_{l,η}`. -/
theorem eq_smul_zonalHarmonic {n : ℕ} (hn : 3 ≤ n) {l : ℕ} {η : EuclideanSpace ℝ (Fin n)}
    (hη : ‖η‖ = 1) {p : MvPolynomial (Fin n) ℝ}
    (hp : p ∈ MvPolynomial.harmonicSubmodule (Fin n) ℝ l)
    (hinv : ∀ k ∈ rotationStabilizer η, ∀ x : EuclideanSpace ℝ (Fin n),
      MvPolynomial.eval (fun i => rotate k x i) p = MvPolynomial.eval (fun i => x i) p) :
    p = MvPolynomial.eval (fun i => η i) p • zonalHarmonic n l η := by
  sorry

/-! ### The Laplace integral -/

/-- **Laplace integral** (Vilenkin–Klimyk, Vol. 2, §9.3.2 (2), p. 47). For `n ≥ 3`,
`ω_{n,l}(cos φ) = c'ₙ ∫_0^π (cos φ + i sin φ cos θ)ˡ sin^{n-3} θ dθ` with
`c'ₙ = Γ((n - 1)/2)/(√π Γ((n - 2)/2))`. -/
theorem zonalPolynomial_eval_cos_eq_integral {n : ℕ} (hn : 3 ≤ n) (l : ℕ) (ϕ : ℝ) :
    (((zonalPolynomial n l).eval (cos ϕ) : ℝ) : ℂ) =
      ((Gamma (((n : ℝ) - 1) / 2) / (√π * Gamma (((n : ℝ) - 2) / 2)) : ℝ) : ℂ) *
        ∫ θ in (0 : ℝ)..π, ((cos ϕ : ℂ) + Complex.I * sin ϕ * cos θ) ^ l *
          ((sin θ ^ (n - 3) : ℝ) : ℂ) := by
  let lam := ((n : ℝ) - 2) / 2
  have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hlam : 0 < lam := by dsimp [lam]; linarith
  have hcast : (lam : ℂ) = ((n : ℂ) - 2) / 2 := by dsimp [lam]; push_cast; rfl
  have hshift : (lam + 1 / 2 : ℂ) = ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) := by
    rw [hcast]
    push_cast
    ring
  have hpow : 2 * lam - 1 = (n - 3 : ℕ) := by
    dsimp [lam]
    push_cast [Nat.cast_sub hn]
    ring
  have h := ultrasphericalPolynomial_laplace_integral hlam l ϕ
  rw [hshift, hpow] at h
  have hcoeff : Complex.Gamma ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) /
        ((√π : ℂ) * Complex.Gamma lam) =
        ((Gamma (((n : ℝ) - 1) / 2) / (√π * Gamma lam) : ℝ) : ℂ) := by
    rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]
  rw [hcoeff, hcast, ← zonalPolynomial_eq_ultrasphericalPolynomial_div hn] at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  have he : Real.rpow (sin θ) ((n - 3 : ℕ) : ℝ) = sin θ ^ (n - 3) :=
    Real.rpow_natCast _ _
  beta_reduce
  rw [he]

end SFVK.Spheres
