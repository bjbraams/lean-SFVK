/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.AffineHeisenberg.Schrodinger
import DLMF.OrthogonalPolynomials.Hahn.HahnAndMeixner
import DLMF.OrthogonalPolynomials.Hahn.Orthogonality
import DLMF.OrthogonalPolynomials.LaguerreContinuation

/-!
# Charlier polynomials and Heisenberg translations

The Charlier polynomial is normalized by `₂F₀(-n, -x; ; -1/a)` (DLMF 18.20.8).
The file relates it to Laguerre polynomials and to the Hermite coefficients of
positive translations. It also gives duality in the degree and nonnegative
integer argument, and discrete orthogonality for `a > 0`. The Hermite comparison
uses the Laguerre normalization of the Schrödinger matrix elements.
-/

public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction Polynomial
open DLMF.Hypergeometric DLMF.OrthogonalPolynomials
open scoped Real ComplexConjugate InnerProductSpace ENNReal FourierTransform SchwartzMap

/-- §3.3. Bridge to lean-DLMF's Charlier polynomial `₂F₀(-n, -x; ; -1/a)` (DLMF 18.20.8). -/
theorem charlier_eq_dlmf_charlier (a : ℝ) (n : ℕ) (x : ℝ) :
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

/-- At a nonnegative integer argument and nonzero parameter, the Charlier polynomial has its
Laguerre form. -/
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

/-- Charlier evaluation is symmetric in the nonnegative integer degree and argument. -/
theorem charlier_symm (a : ℝ) (n x : ℕ) :
    (charlier a n).eval (x : ℝ) = (charlier a x).eval (n : ℝ) := by
  apply Complex.ofReal_injective
  rw [charlier_eq_dlmf_charlier a, charlier_eq_dlmf_charlier a]
  push_cast
  exact DLMF.OrthogonalPolynomials.charlier_duality a n x

namespace HermiteTranslation

/-- The two equivalent factorial normalizations in the Charlier and Laguerre formulas. -/
private theorem sqrt_div_factorial (j k : ℕ) :
    Real.sqrt ((j.factorial : ℝ) / k.factorial) =
      (j.factorial : ℝ) / Real.sqrt ((j.factorial : ℝ) * k.factorial) := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
  field_simp [ne_of_gt (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < j.factorial)),
    ne_of_gt (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < k.factorial))]
  rw [Real.sq_sqrt (by positivity)]

/-- The positive power of the squared translation matches the integer Laguerre powers. -/
private theorem rpow_translation_square (s : ℝ) (hs : 0 < s) {j k : ℕ} (h : j ≤ k) :
    (s ^ 2) ^ (((j : ℝ) + k) / 2) = s ^ (k - j) * (s ^ 2) ^ j := by
  calc
    _ = s ^ ((j : ℝ) + k) := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_mul hs.le]
      norm_num
      ring_nf
    _ = s ^ ((k - j : ℕ) : ℝ) * s ^ (2 * (j : ℝ)) := by
      rw [← Real.rpow_add hs, Nat.cast_sub h]
      congr 1
      ring
    _ = _ := by rw [Real.rpow_mul hs.le, Real.rpow_natCast, Real.rpow_two, Real.rpow_natCast]

/-- The common Laguerre factor for the two orders of the Hermite indices. -/
private theorem laguerre_translation_factor {s : ℝ} (hs : 0 < s) {j k : ℕ} (h : j ≤ k) :
    (Real.sqrt ((j.factorial : ℝ) / k.factorial) : ℂ) * (s : ℂ) ^ (k - j) *
        laguerreExtended ((k : ℂ) - j) j (s ^ 2 : ℝ) =
      (-1 : ℂ) ^ j / (Real.sqrt ((j.factorial : ℝ) * k.factorial) : ℂ) *
        (((s ^ 2 : ℝ) ^ (((j : ℝ) + k) / 2) : ℝ) : ℂ) *
        (((charlier (s ^ 2) j).eval (k : ℝ) : ℝ) : ℂ) := by
  rw [charlier_eq_laguerre _ (pow_ne_zero _ hs.ne') j k,
    sqrt_div_factorial, rpow_translation_square s hs h]
  push_cast
  have hsign : (-1 : ℂ) ^ j * (-1) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  have hpow : ((s : ℂ) ^ 2) ^ j ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (ofReal_ne_zero.mpr hs.ne'))
  symm
  calc
    _ = ((-1 : ℂ) ^ j * (-1) ^ j) * (((s : ℂ) ^ 2) ^ j * (((s : ℂ) ^ 2) ^ j)⁻¹) *
        ((j.factorial : ℂ) / (Real.sqrt ((j.factorial : ℝ) * k.factorial) : ℂ) *
          (s : ℂ) ^ (k - j) * laguerreExtended ((k : ℂ) - j) j ((s : ℂ) ^ 2)) := by ring
    _ = _ := by rw [hsign, mul_inv_cancel₀ hpow, one_mul, one_mul]

end HermiteTranslation

open HermiteTranslation in
/-- The Charlier form of the Hermite matrix element for a positive translation. -/
theorem hermiteMatrixElement_charlier (x : ℝ) (hx : 0 < x) (k n : ℕ) :
    hermiteMatrixElement k n x 0 0 =
      (((-1) ^ k / Real.sqrt (k.factorial * n.factorial) * (x ^ 2 / 2) ^ (((k : ℝ) + n) / 2) *
        Real.exp (-(x ^ 2 / 4)) * (charlier (x ^ 2 / 2) k).eval (n : ℝ) : ℝ) : ℂ) := by
  let s := x / Real.sqrt 2
  have hs : 0 < s := div_pos hx (by positivity)
  have hsquare : s ^ 2 = x ^ 2 / 2 := by
    dsimp only [s]
    rw [div_pow, Real.sq_sqrt (by norm_num)]
  have harg : -(x : ℂ) / (Real.sqrt 2 : ℂ) = -(s : ℂ) := by
    simp [s, neg_div]
  simp only [hermiteMatrixElement, mul_zero, ofReal_zero, zero_mul, zero_pow (by decide :
    2 ≠ 0), add_zero, zero_div, sub_zero, exp_zero, one_mul, ← hsquare, harg,
    map_neg, conj_ofReal, neg_neg]
  have hexp : -(s ^ 2) / 2 = -(x ^ 2 / 4) := by rw [hsquare]; ring
  rw [hexp]
  simp only [ofReal_mul, ofReal_div, ofReal_pow, ofReal_neg, ofReal_one]
  by_cases h : n ≤ k
  · rw [ite_eq_left h, neg_pow]
    have he := laguerre_translation_factor hs h
    rw [charlier_symm (s ^ 2) n k, mul_comm (n.factorial : ℝ), add_comm (n : ℝ)] at he
    have hsign : (-1 : ℂ) ^ (k - n) * (-1) ^ n = (-1) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel h]
    calc
      _ = (-1 : ℂ) ^ (k - n) * (Real.exp (-(x ^ 2 / 4)) : ℂ) *
          ((Real.sqrt ((n.factorial : ℝ) / k.factorial) : ℂ) * (s : ℂ) ^ (k - n) *
            laguerreExtended ((k : ℂ) - n) n (s ^ 2 : ℝ)) := by
        simp only [ofReal_pow]
        ring
      _ = _ := by
        rw [he, ← hsign]
        ring
  · rw [ite_eq_right h]
    have he := laguerre_translation_factor hs (Nat.le_of_not_ge h)
    simp only [ofReal_pow] at he
    rw [he]
    ring
/-- §3.3. **Orthogonality and completeness** of the Charlier polynomials. -/
theorem charlier_orthogonality (a : ℝ) (ha : 0 < a) :
    (∀ k p : ℕ, HasSum (fun x : ℕ => a ^ k * Real.exp (-a) / k.factorial *
        (a ^ x / x.factorial * (charlier a k).eval (x : ℝ) * (charlier a p).eval (x : ℝ)))
      (if k = p then 1 else 0)) ∧
    ∃ b : HilbertBasis ℕ ℝ (lp (fun _ : ℕ => ℝ) 2),
      ∀ k x : ℕ, b k x = Real.sqrt (a ^ (k + x) * Real.exp (-a) / (k.factorial * x.factorial)) *
        (charlier a k).eval (x : ℝ) := by
  let coeff (k : ℕ) : ℝ := a ^ k * Real.exp (-a) / k.factorial
  let weight (x : ℕ) : ℝ := a ^ x / x.factorial
  let P (k x : ℕ) : ℝ := (charlier a k).eval (x : ℝ)
  have hc (k : ℕ) : 0 < coeff k := by dsimp only [coeff]; positivity
  have hw (x : ℕ) : 0 < weight x := by dsimp only [weight]; positivity
  have hnorm (k : ℕ) :
      coeff k * (a⁻¹ ^ k * Real.exp a * k.factorial) = 1 := by
    have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
    dsimp only [coeff]
    rw [inv_pow, Real.exp_neg]
    field_simp [pow_ne_zero _ ha.ne', (Real.exp_pos _).ne', hfac]
  have hMoment (k p : ℕ) :
      HasSum (fun x => weight x * P k x * P p x)
        (if k = p then (a⁻¹) ^ p * Real.exp a * p.factorial else 0) := by
    have h := DLMF.OrthogonalPolynomials.charlier_orthogonality ha k p
    have hR := h.map Complex.reCLM Complex.reCLM.continuous
    convert hR using 1
    · funext x
      have hcoe : (((weight x * P k x * P p x : ℝ)) : ℂ) =
          DLMF.OrthogonalPolynomials.charlier a k x * DLMF.OrthogonalPolynomials.charlier a p x *
            (a : ℂ) ^ x / x.factorial := by
        dsimp only [P]
        rw [ofReal_mul, ofReal_mul, charlier_eq_dlmf_charlier a,
          charlier_eq_dlmf_charlier a]
        simp only [weight, ofReal_div, ofReal_pow, ofReal_natCast]
        ring
      simpa only [Function.comp_apply, Complex.reCLM_apply, ofReal_re] using
        congrArg Complex.re hcoe
    · split_ifs <;> simp [Complex.reCLM_apply, ← Complex.ofReal_exp,
        ← Complex.ofReal_mul, ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_natCast]
  have hOrtho (k p : ℕ) : HasSum (fun x => coeff k * (weight x * P k x * P p x))
      (if k = p then 1 else 0) := by
    have h := (hMoment k p).mul_left (coeff k)
    convert h using 1
    split_ifs with hp
    · subst p
      exact (hnorm k).symm
    · simp
  refine ⟨hOrtho, ?_⟩
  let V (k x : ℕ) : ℝ := Real.sqrt (coeff k * weight x) * P k x
  have hVprod (k p x : ℕ) : V k x * V p x =
      (Real.sqrt (coeff k) * Real.sqrt (coeff p)) * (weight x * P k x * P p x) := by
    dsimp only [V]
    rw [Real.sqrt_mul (hc k).le, Real.sqrt_mul (hc p).le]
    calc
      _ = (Real.sqrt (coeff k) * Real.sqrt (coeff p)) *
          ((Real.sqrt (weight x) * Real.sqrt (weight x)) * P k x * P p x) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (hw x).le]
  have hInner (k p : ℕ) : HasSum (fun x => V k x * V p x) (if k = p then 1 else 0) := by
    simp_rw [hVprod]
    have h := (hMoment k p).mul_left (Real.sqrt (coeff k) * Real.sqrt (coeff p))
    convert h using 1
    split_ifs with hp
    · subst p
      rw [Real.mul_self_sqrt (hc k).le, hnorm]
    · simp
  have hLp (k : ℕ) : Memℓp (V k) 2 := by
    apply memℓp_gen
    have hs : Summable (fun x => V k x ^ 2) := by
      simpa only [pow_two] using (hInner k k).summable
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hs
  let v (k : ℕ) : lp (fun _ : ℕ => ℝ) 2 := ⟨V k, hLp k⟩
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro k p
    rw [lp.inner_eq_tsum]
    simpa only [v, Subtype.coe_mk, real_inner_comm, RCLike.inner_apply, RCLike.conj_to_real,
      mul_comm] using (hInner k p).tsum_eq
  have hV (k x : ℕ) :
      V k x = Real.sqrt (a ^ (k + x) * Real.exp (-a) / (k.factorial * x.factorial)) * P k x := by
    dsimp only [V, coeff, weight]
    rw [pow_add]
    congr 2
    ring
  have hSym (k x : ℕ) : V k x = V x k := by
    rw [hV, hV, Nat.add_comm x k, mul_comm (x.factorial : ℝ)]
    dsimp only [P]
    rw [charlier_symm a k x]
  let K := (Submodule.span ℝ (Set.range v)).topologicalClosure
  have hK : IsClosed (K : Set (lp (fun _ : ℕ => ℝ) 2)) :=
    Submodule.isClosed_topologicalClosure _
  have hSingle (i : ℕ) : lp.single 2 i (1 : ℝ) ∈ K := by
    have h := hv.orthogonalFamily.hasSum_linearIsometry (v i)
    have hval : hv.orthogonalFamily.linearIsometry (v i) = lp.single 2 i (1 : ℝ) := by
      ext j
      let ev := lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 j
      have hj := h.map ev ev.continuous
      have hconverted : HasSum (fun k => V i k * V j k)
          ((hv.orthogonalFamily.linearIsometry (v i)) j) := by
        refine hj.congr_fun fun k => ?_
        change V i k * V j k = V i k * V k j
        rw [hSym j k]
      rw [hconverted.unique (hInner i j), lp.single_apply]
      split_ifs <;> simp_all [eq_comm]
    rw [hval] at h
    apply mem_closure_of_tendsto h (Filter.Eventually.of_forall fun s => ?_)
    apply Submodule.sum_mem
    intro k _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hspan : ⊤ ≤ K := by
    intro f _
    have h := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) f
    apply hK.mem_of_tendsto h (Filter.Eventually.of_forall fun s => ?_)
    apply Submodule.sum_mem
    intro i _
    have he : lp.single 2 i (f i) =
        f i • lp.single (E := fun _ : ℕ => ℝ) 2 i (1 : ℝ) := by
      ext j
      by_cases hij : j = i
      · subst j
        simp
      · simp [lp.single_apply, hij]
    rw [he]
    exact K.smul_mem _ (hSingle i)
  refine ⟨HilbertBasis.mk hv hspan, fun k x => ?_⟩
  rw [HilbertBasis.coe_mk]
  exact hV k x

end SFVK.AffineHeisenberg
