/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.AffineHeisenberg.Basic
public import DLMF.OrthogonalPolynomials.Basic.Definitions
import DLMF.OrthogonalPolynomials.LaguerreContinuation
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Miller's group `G(0, 1)` and the Laguerre addition theorem

Statements of §5 of the roadmap `Roadmaps/AffineHeisenbergGroups/README.md` (section numbers
`§x.y`).
Sources: Miller §4-2 (4.17)–(4.28), pp. 85–88; Wawrzyńczyk (12.2.1), p. 429.
Theorems not yet proved are stated with `sorry`.
-/

@[expose] public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open DLMF.Hypergeometric DLMF.OrthogonalPolynomials
open scoped Real ComplexConjugate InnerProductSpace ENNReal

/-- §5.1. **Representation law.** -/
theorem millerAction_mul (μ ω : ℂ) (g h : MillerGroup) (f : ℂ → ℂ) :
    millerAction μ ω (g * h) f = millerAction μ ω g (millerAction μ ω h f) := by
  funext z
  have h1 : Complex.exp g.τ * Complex.exp (-g.τ) = 1 := by rw [← Complex.exp_add]; simp
  simp only [millerAction, MillerGroup.mul_a, MillerGroup.mul_b, MillerGroup.mul_c,
    MillerGroup.mul_τ]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  · congr 1
    ring
  · congr 1
    rw [Complex.exp_add]
    linear_combination (Complex.exp h.τ * h.c) * h1

/-- §5.1. **Real points.** -/
theorem millerAction_eq_triangularAction (μ ω : ℂ) :
    (∀ (a b c τ a' b' c' τ' : ℝ),
      millerToTriangular (a + a' + Real.exp τ * c * b') (b + Real.exp τ * b')
          (c + Real.exp (-τ) * c') (τ + τ') =
        millerToTriangular a b c τ * millerToTriangular a' b' c' τ') ∧
    ∀ (a b c τ : ℝ) (f : ℂ → ℂ) (x : ℝ),
      millerAction μ ω ⟨a, b, c, τ⟩ f x =
        triangularAction μ (-ω) (millerToTriangular a b c τ) (fun y => f y) x := by
  refine ⟨fun a b c τ a' b' c' τ' => ?_, fun a b c τ f x => ?_⟩
  · have h1 : Real.exp τ * Real.exp (-τ) = 1 := by rw [← Real.exp_add]; simp
    ext
    · simp only [millerToTriangular, TriangularGroup.mul_a, Real.exp_add]
      linear_combination (Real.exp τ' * c') * h1
    · simp only [millerToTriangular, TriangularGroup.mul_b]
    · simp only [millerToTriangular, TriangularGroup.mul_d]
    · simp only [millerToTriangular, TriangularGroup.mul_τ]
  · simp only [millerAction, triangularAction, triangularCocycle, millerToTriangular]
    push_cast
    congr 1
    congr 1
    ring

/-- Coefficients of the product of an exponential and a finite binomial expansion. -/
private theorem hasSum_exp_mul_add_pow (k : ℕ) (c u z : ℂ) :
    HasSum (fun l : ℕ =>
      (∑ j ∈ Finset.range (min k l + 1),
        (k.choose j : ℂ) * c ^ (k - j) * u ^ (l - j) / (l - j).factorial) * z ^ l)
      (Complex.exp (u * z) * (z + c) ^ k) := by
  let b (j : ℕ) := (k.choose j : ℂ) * c ^ (k - j) * z ^ j
  let e (j : ℕ) := (u * z) ^ j / (j.factorial : ℂ)
  have hz (j : ℕ) (hj : j ∉ Finset.range (k + 1)) : b j = 0 := by
    have hkj : k < j := by simpa using hj
    simp [b, Nat.choose_eq_zero_of_lt hkj]
  have hb : HasSum b ((z + c) ^ k) := by
    have hb' : HasSum b (∑ j ∈ Finset.range (k + 1), b j) :=
      hasSum_sum_of_ne_finset_zero (fun j hj => hz j hj)
    rw [add_pow]
    convert hb' using 1
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [b]
    ring
  have he : HasSum e (Complex.exp (u * z)) := by
    simpa only [e, Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (u * z)
  have h := hasSum_sum_range_mul_of_summable_norm hb.summable.norm he.summable.norm
  rw [hb.tsum_eq, he.tsum_eq, mul_comm] at h
  apply h.congr_fun
  intro l
  rw [Finset.sum_mul]
  have hsubset : Finset.range (min k l + 1) ⊆ Finset.range (l + 1) :=
    Finset.range_mono (Nat.succ_le_succ (min_le_right _ _))
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjl : j ≤ l := by have := Finset.mem_range.mp hj; omega
    have hp : z ^ l = z ^ j * z ^ (l - j) := by rw [← pow_add, Nat.add_sub_of_le hjl]
    dsimp [b, e]
    rw [hp, mul_pow]
    ring
  · intro j hj hj'
    have hjl : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hkj : k < j := by simp only [Finset.mem_range] at hj'; omega
    simp [b, Nat.choose_eq_zero_of_lt hkj]

/-- The degree-dependent Laguerre parameter gives a binomial coefficient in each term. -/
private theorem laguerreExtended_eq_choose_sum (k l : ℕ) (x : ℂ) :
    laguerreExtended ((k : ℂ) - l) l x =
      ∑ j ∈ Finset.range (min k l + 1), (k.choose j : ℂ) * (-x) ^ (l - j) /
        (l - j).factorial := by
  rw [laguerreExtended_eq_reverse_sum]
  have hsubset : Finset.range (min k l + 1) ⊆ Finset.range (l + 1) :=
    Finset.range_mono (Nat.succ_le_succ (min_le_right _ _))
  have hpoch (j : ℕ) (hj : j ≤ l) :
      pochhammer ((k : ℂ) - l + (l - j : ℕ) + 1) j = (k.descFactorial j : ℂ) := by
    rw [Nat.cast_sub hj, show (k : ℂ) - l + (l - j) + 1 = (k : ℂ) - j + 1 by ring,
      pochhammer, ← descPochhammer_eval_eq_ascPochhammer,
      descPochhammer_eval_eq_descFactorial]
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjl : j ≤ l := by have := Finset.mem_range.mp hj; omega
    rw [hpoch j hjl, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    field_simp [show (j.factorial : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr j.factorial_ne_zero]
  · intro j hj hj'
    have hjl : j ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hkj : k < j := by simp only [Finset.mem_range] at hj'; omega
    simp [hpoch j hjl, Nat.descFactorial_eq_zero_iff_lt.mpr hkj]

/-- §5.1. **Matrix elements.** -/
theorem hasSum_millerAction_monomial (μ ω : ℂ) (g : MillerGroup) (k : ℕ) (z : ℂ) :
    HasSum (fun l => millerMatrixElement μ ω l k g * z ^ l)
      (millerAction μ ω g (fun z => z ^ k) z) := by
  have h := (hasSum_exp_mul_add_pow k g.c (μ * g.b) z).mul_left
    (Complex.exp (μ * g.a + (k - ω) * g.τ))
  have he : Complex.exp (μ * (g.b * z + g.a) - ω * g.τ) *
      (Complex.exp g.τ * z + Complex.exp g.τ * g.c) ^ k =
      Complex.exp (μ * g.a + (k - ω) * g.τ) *
        (Complex.exp ((μ * g.b) * z) * (z + g.c) ^ k) := by
    rw [← mul_add, mul_pow, ← Complex.exp_nat_mul, ← mul_assoc, ← Complex.exp_add,
      ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [millerAction, he]
  convert h using 1
  funext l
  rw [millerMatrixElement]
  ring

/-- §5.1. **Laguerre form.** -/
theorem millerMatrixElement_eq_laguerre (μ ω : ℂ) (g : MillerGroup) (hc : g.c ≠ 0) (l k : ℕ) :
    millerMatrixElement μ ω l k g =
      Complex.exp (μ * g.a + (k - ω) * g.τ) * g.c ^ ((k : ℤ) - l) *
        laguerreExtended ((k : ℂ) - l) l (-(μ * g.b * g.c)) := by
  rw [millerMatrixElement, laguerreExtended_eq_choose_sum, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hmin := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hkl : j ≤ k := hmin.trans (min_le_left _ _)
  have hjl : j ≤ l := hmin.trans (min_le_right _ _)
  have hpow : g.c ^ ((k : ℤ) - l) * g.c ^ (l - j) = g.c ^ (k - j) := by
    rw [← zpow_natCast, ← zpow_add₀ hc, ← zpow_natCast]
    congr 1
    omega
  simp only [neg_neg, mul_pow]
  calc
    _ = (k.choose j : ℂ) * (g.c ^ ((k : ℤ) - l) * g.c ^ (l - j)) *
      (μ ^ (l - j) * g.b ^ (l - j)) / (l - j).factorial := by rw [hpow]
    _ = _ := by ring

/-- The coefficient majorant obtained by replacing both polynomial variables by their norms. -/
private noncomputable def millerCoefficientMajorant (j l : ℕ) (c b : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (min j l + 1), (j.choose s : ℝ) * c ^ (j - s) * b ^ (l - s) /
    (l - s).factorial

/-- The majorant has an exponential generating sum at every nonnegative radius. -/
private theorem hasSum_millerCoefficientMajorant (j : ℕ) (c b R : ℝ) :
    HasSum (fun l => millerCoefficientMajorant j l c b * R ^ l)
      (Real.exp (b * R) * (R + c) ^ j) := by
  have h := (hasSum_exp_mul_add_pow j (c : ℂ) (b : ℂ) (R : ℂ)).map
    Complex.reCLM Complex.reCLM.continuous
  convert h using 1
  · funext l
    have he : ((millerCoefficientMajorant j l c b * R ^ l : ℝ) : ℂ) =
        (∑ s ∈ Finset.range (min j l + 1), (j.choose s : ℂ) * (c : ℂ) ^ (j - s) *
          (b : ℂ) ^ (l - s) / (l - s).factorial) * (R : ℂ) ^ l := by
      push_cast [millerCoefficientMajorant]
      rfl
    simpa only [ofReal_re, reCLM_apply, Function.comp_apply] using congrArg Complex.re he
  · have he : ((Real.exp (b * R) * (R + c) ^ j : ℝ) : ℂ) =
        Complex.exp ((b : ℂ) * R) * ((R : ℂ) + c) ^ j := by push_cast; rfl
    simpa only [ofReal_re, reCLM_apply] using congrArg Complex.re he

/-- The exponential and finite polynomial factors give a pointwise majorant for each coefficient. -/
private theorem norm_millerMatrixElement_le_majorant (μ ω : ℂ) (g : MillerGroup) (l j : ℕ) :
    ‖millerMatrixElement μ ω l j g‖ ≤
      Real.exp (μ * g.a - ω * g.τ).re * Real.exp (j * g.τ.re) *
        millerCoefficientMajorant j l ‖g.c‖ ‖μ * g.b‖ := by
  rw [millerMatrixElement, norm_mul, norm_exp,
    show μ * g.a + (j - ω) * g.τ = μ * g.a - ω * g.τ + j * g.τ by ring,
    add_re, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (norm_sum_le _ _).trans_eq ?_
  simp only [millerCoefficientMajorant, norm_mul, norm_div, norm_natCast, norm_pow]

/-- The coefficients of the composed double series are absolutely summable at every radius. -/
private theorem summable_norm_millerMatrixElement_comp (μ ω : ℂ) (g h : MillerGroup) (k : ℕ)
    (z : ℂ) :
    Summable (fun p : ℕ × ℕ =>
      ‖millerMatrixElement μ ω p.1 k h * millerMatrixElement μ ω p.2 p.1 g * z ^ p.2‖) := by
  let R := ‖z‖
  let C := Real.exp (μ * g.a - ω * g.τ).re
  let H (j : ℕ) := ‖millerMatrixElement μ ω j k h‖
  let M (p : ℕ × ℕ) := (H p.1 * (C * Real.exp (p.1 * g.τ.re))) *
    (millerCoefficientMajorant p.1 p.2 ‖g.c‖ ‖μ * g.b‖ * R ^ p.2)
  have hSplit (j : ℕ) : HasSum (fun l => M (j,l))
      (H j * (C * Real.exp (j * g.τ.re)) *
        (Real.exp (‖μ * g.b‖ * R) * (R + ‖g.c‖) ^ j)) :=
    (hasSum_millerCoefficientMajorant j ‖g.c‖ ‖μ * g.b‖ R).mul_left _
  have hM : Summable M := by
    rw [summable_prod_of_nonneg]
    · refine ⟨fun j => (hSplit j).summable, ?_⟩
      simp_rw [(hSplit _).tsum_eq]
      let T := Real.exp g.τ.re * (R + ‖g.c‖)
      have hS := (hasSum_millerAction_monomial μ ω h k (T : ℂ)).summable.norm
      have ht : 0 ≤ T := by dsimp only [T,R]; positivity
      have hv : Summable (fun j => H j * T ^ j) := by
        simpa only [H, norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_nonneg ht] using hS
      refine (hv.mul_left (C * Real.exp (‖μ * g.b‖ * R))).congr fun j => ?_
      dsimp only [T]
      rw [mul_pow, ← Real.exp_nat_mul]
      ring
    · intro p
      unfold M millerCoefficientMajorant C H R
      positivity
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hM
  simp only [norm_mul, norm_pow, M, H, R]
  have hle := norm_millerMatrixElement_le_majorant μ ω g p.2 p.1
  calc
    _ ≤ H p.1 * (C * Real.exp (p.1 * g.τ.re) *
        millerCoefficientMajorant p.1 p.2 ‖g.c‖ ‖μ * g.b‖) * ‖z‖ ^ p.2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (norm_nonneg _)) (by positivity)
    _ = _ := by dsimp only [H]; rw [norm_mul μ g.b]; ring

/-- An everywhere convergent scalar power series uniquely determines its coefficients. -/
private theorem millerCoefficients_unique {a b : ℕ → ℂ} {f : ℂ → ℂ}
    (ha : ∀ z : ℂ, HasSum (fun n => a n * z ^ n) (f z))
    (hb : ∀ z : ℂ, HasSum (fun n => b n * z ^ n) (f z)) : a = b := by
  have series {c : ℕ → ℂ} (hc : ∀ z : ℂ, HasSum (fun n => c n * z ^ n) (f z)) :
      HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
    refine ⟨1, ?_, by norm_num, ?_⟩
    · refine (FormalMultilinearSeries.ofScalars ℂ c).le_radius_of_summable_norm ?_
      simpa only [FormalMultilinearSeries.ofScalars_norm, NNReal.coe_one, one_pow, mul_one] using
        (hc 1).summable.norm
    · intro z _
      simpa only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hc z
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    ((series ha).eq_formalMultilinearSeries (series hb))


/-- §5.1. **Addition theorem.** -/
theorem hasSum_millerMatrixElement_mul (μ ω : ℂ) (g h : MillerGroup) (l k : ℕ) :
    HasSum (fun j => millerMatrixElement μ ω l j g * millerMatrixElement μ ω j k h)
      (millerMatrixElement μ ω l k (g * h)) := by
  let A : ℕ → ℕ → ℂ := fun l j =>
      millerMatrixElement μ ω j k h * millerMatrixElement μ ω l j g
  let C : ℕ → ℂ := fun l => ∑' j, A l j
  have hA : ∀ l, Summable (A l) := by
    intro l
    have h := (summable_norm_millerMatrixElement_comp μ ω g h k 1).of_norm
    let pair : ℕ → ℕ × ℕ := fun j => (j,l)
    have hp : Function.Injective pair := fun _ _ e => congrArg Prod.fst e
    convert h.comp_injective hp using 1
    funext j
    simp only [A, pair, Function.comp_def, one_pow, mul_one]
  have hC (z : ℂ) :
      HasSum (fun l => C l * z ^ l) (millerAction μ ω (g * h) (fun z => z ^ k) z) := by
    let D : ℕ × ℕ → ℂ := fun p => A p.2 p.1 * z ^ p.2
    have hD : Summable D := (summable_norm_millerMatrixElement_comp μ ω g h k z).of_norm
    have hRow (j : ℕ) : HasSum (fun l => D (j,l))
        (millerMatrixElement μ ω j k h * millerAction μ ω g (fun z => z ^ j) z) := by
      simpa only [D, A, mul_assoc] using
        (hasSum_millerAction_monomial μ ω g j z).mul_left (millerMatrixElement μ ω j k h)
    have hValue := hD.hasSum.prod_fiberwise hRow
    have hComp :
        HasSum (fun j => millerMatrixElement μ ω j k h * millerAction μ ω g (fun z => z ^ j) z)
          (millerAction μ ω (g * h) (fun z => z ^ k) z) := by
      have hs := (hasSum_millerAction_monomial μ ω h k
        (Complex.exp g.τ * z + Complex.exp g.τ * g.c)).mul_left
          (Complex.exp (μ * (g.b * z + g.a) - ω * g.τ))
      rw [millerAction_mul]
      simpa only [millerAction, mul_left_comm] using hs
    have hTot : HasSum D (millerAction μ ω (g * h) (fun z => z ^ k) z) :=
      (hValue.unique hComp) ▸ hD.hasSum
    have hSwap := (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hTot
    have hCol (l : ℕ) : HasSum (fun j => D ((Equiv.prodComm ℕ ℕ) (l,j))) (C l * z ^ l) :=
      (hA l).hasSum.mul_right _
    exact hSwap.prod_fiberwise hCol
  have hcoeff := millerCoefficients_unique hC (hasSum_millerAction_monomial μ ω (g * h) k)
  have hs := (hA l).hasSum
  rw [show (∑' j, A l j) = millerMatrixElement μ ω l k (g * h) from congrFun hcoeff l] at hs
  simpa only [A, mul_comm] using hs

/-- §5.1. **Generating function.** -/
theorem hasSum_laguerre_generating (m : ℕ) (x z : ℂ) :
    HasSum (fun n : ℕ => laguerreExtended ((m : ℂ) - n) n x * z ^ n)
      (Complex.exp (-x * z) * (1 + z) ^ m) := by
  have h := hasSum_exp_mul_add_pow m 1 (-x) z
  rw [add_comm z 1] at h
  apply h.congr_fun
  intro n
  simp [laguerreExtended_eq_choose_sum]

end SFVK.AffineHeisenberg
