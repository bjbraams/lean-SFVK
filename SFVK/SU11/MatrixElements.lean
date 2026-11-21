/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU11.Basic.MatrixElementsBasic
public import SFVK.SU11.Basic.CircleModel
import SFVK.SU11.CircleModel
import SFVK.SU11.Coordinates
import SFVK.SU11.MatrixElementKernels
public import SFVK.SU11.MatrixElementRecurrences
public import SFVK.SU11.MatrixElementSpecialFunctions
public import SFVKMathlib.RepresentationTheory.Continuous.MatrixElement
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Fourier.AddCircle
import DLMFMathlib.Analysis.Complex.ParametricHolomorphy
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The matrix elements `𝔓^τ_{mn}` of `SU(1,1)`

Statements about `SFVK.SU11.boostMatrixElement`, Vilenkin–Klimyk's `𝔓^τ_{mn}(cosh t)`
(*Representation of Lie Groups and Special Functions*, Vol. 1), as a function of `t`: the
matrix elements of the principal series in Euler angles (§6.5.1 (1)–(4), p. 311), special values
and smoothness, the hypergeometric forms (§6.5.3 (1)–(3), p. 313), the Legendre functions
(§6.5.7 (1)–(4), pp. 322–323), the symmetries (§6.5.5 (1)–(9), pp. 318–320), the vanishing at
integral degree (§6.5.6 (1)–(4), pp. 320–321), unitarity of the principal and complementary
series (§6.5.1 (8), p. 312), the addition theorem (§6.6.1 (1)–(2), pp. 326–327) and
multiplication formulas (§6.6.3 (1)–(8), pp. 327–329), the generating function and the degree
identities (§6.7.1 (6)–(9), pp. 332–333, §6.7.3 (2)–(5), pp. 336–337), derivatives, ladder
relations and recurrences (§6.7.2 (5), (8)–(13), pp. 335–336), and the parabolic subgroup.

Analytic identities take a real index `n` and an integer shift `k`, with `m = n + k`; statements
that pass through `principalSeries τ e` take integer Fourier indices with weights `n - e/2`.
Gamma quotients are written with reciprocal Gamma functions, which are entire, so no pole of
`Γ` needs to be excluded. Holomorphic differentiation under the finite integral uses the
parametric integral theorem of lean-DLMF.
-/

public section

open AddCircle Complex MeasureTheory Set
open scoped ComplexConjugate Real InnerProductSpace

namespace SFVK.SU11

local notation "𝕋" => AddCircle (2 * π)
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-! ### Definition, Euler angles and special values -/

open FourierExpansion

/-- **Principal-series matrix elements in Euler angles.** With `m' = n' - e/2` and
`m = n - e/2`, `D_{m'm}(g(α, t, γ)) = e^{i(m'α + mγ)} 𝔓^τ_{m'm}(cosh t)` (Vilenkin–Klimyk,
Vol. 1, §6.5.1 (1)–(4), p. 311). -/
theorem principalSeries_matrixElement_euler_eq (τ : ℂ) (e : Fin 2) (n' n : ℤ) (α t γ : ℝ) :
    ContRepresentation.matrixElement (principalSeries τ e) (fourierBasis (T := 2 * π)) n' n
        (euler α t γ) =
      exp ((((n' - (e : ℕ) / 2 : ℝ) * α + (n - (e : ℕ) / 2 : ℝ) * γ : ℝ) : ℂ) * I) *
        boostMatrixElement τ (n' - (e : ℕ) / 2) (n - (e : ℕ) / 2) t := by
  rw [euler_def, matrixElement_mul_rotation, matrixElement_rotation_mul,
    principalSeries_matrixElement_boost_eq, ← mul_assoc, ← exp_add]
  congr 2
  push_cast
  ring

/-- At `t = 0`, `𝔓^τ_{n+k,n}(1) = δ_{k0}`. -/
theorem boostMatrixElement_zero (τ : ℂ) (n : ℝ) (k : ℤ) :
    boostMatrixElement τ (n + k) n 0 = if k = 0 then 1 else 0 := by
  rw [boostMatrixElement_eq_fourierCoeff]
  have h : (fun θ : 𝕋 => boostKernel τ n 0 (fourier 1 θ)) = fun _ => (1 : ℂ) := by
    funext θ
    simp [boostKernel, boostBase]
  rw [h, fourierCoeff_const]
  simp [Pi.single_apply]

/-- `𝔓^τ_{mn}(cosh t)` is entire in the degree `τ`. -/
theorem differentiable_boostMatrixElement (m n t : ℝ) :
    Differentiable ℂ fun τ => boostMatrixElement τ m n t := by
  let A (θ : ℝ) := boostBase t (exp ((θ : ℂ) * I))
  let F (τ : ℂ) (θ : ℝ) :=
    A θ ^ (τ + n) * A (-θ) ^ (τ - n) * exp (((m - n : ℝ) : ℂ) * θ * I)
  have hA : Continuous A := by
    unfold A boostBase
    fun_prop
  have hbranch (θ : ℝ) : A θ ∈ slitPlane :=
    boostBase_mem_slitPlane t (norm_exp_ofReal_mul_I θ)
  have hcont : Continuous (fun p : ℂ × ℝ => F p.1 p.2) := by
    unfold F
    exact (((hA.comp continuous_snd).cpow (by fun_prop) (fun p => hbranch p.2)).mul
      ((hA.comp continuous_snd.neg).cpow (by fun_prop) (fun p => hbranch (-p.2)))).mul
      (by fun_prop)
  have hdiff (θ : ℝ) : Differentiable ℂ (fun τ => F τ θ) := by
    unfold F
    exact (((differentiable_id.add_const (n : ℂ)).const_cpow
      (Or.inl (slitPlane_ne_zero (hbranch θ)))).mul
      ((differentiable_id.sub_const (n : ℂ)).const_cpow
        (Or.inl (slitPlane_ne_zero (hbranch (-θ)))))).mul_const _
  have h := Complex.differentiableOn_intervalIntegral_of_continuousOn
    isOpen_univ (ν := volume) 0 (2 * π) hcont.continuousOn
      (fun θ => (hdiff θ).differentiableOn)
  have H := (differentiableOn_univ.mp h).const_mul (((2 * π : ℝ) : ℂ)⁻¹)
  simpa only [boostMatrixElement_def, F, A, boostBase, ofReal_neg, neg_mul] using H

/-- `𝔓^τ_{mn}(cosh t)` is smooth in `t`. -/
theorem contDiff_boostMatrixElement (τ : ℂ) (m n : ℝ) :
    ContDiff ℝ ⊤ fun t => boostMatrixElement τ m n t := by
  let A (z : ℂ) (θ : ℝ) := cosh (z / 2) + sinh (z / 2) * exp ((θ : ℂ) * I)
  let U : Set ℂ := {z | ‖sinh (z / 2)‖ < (cosh (z / 2)).re}
  let F (z : ℂ) (θ : ℝ) :=
    A z θ ^ (τ + n) * A z (-θ) ^ (τ - n) * exp (((m - n : ℝ) : ℂ) * θ * I)
  have hReal (x : ℝ) : (x : ℂ) ∈ U := by
    have hp : 0 < Real.cosh (x / 2) - |Real.sinh (x / 2)| := by
      rw [← Real.cosh_abs (x / 2), Real.abs_sinh, Real.cosh_sub_sinh]
      exact Real.exp_pos _
    have hcast : (x : ℂ) / 2 = (↑(x / 2) : ℂ) := by push_cast; rfl
    simpa only [U, mem_ofPred_eq, hcast, ← ofReal_sinh, ← ofReal_cosh, ofReal_re,
      Complex.norm_real, Real.norm_eq_abs] using sub_pos.mp hp
  have hopen : IsOpen U := isOpen_lt (by fun_prop) (by fun_prop)
  have hbranch {z : ℂ} (hz : z ∈ U) (θ : ℝ) : A z θ ∈ slitPlane := by
    have hb : |(sinh (z / 2) * exp ((θ : ℂ) * I)).re| ≤ ‖sinh (z / 2)‖ := by
      refine (abs_re_le_norm _).trans_eq ?_
      rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
    refine Or.inl ?_
    simp only [A, add_re]
    have hneg := neg_abs_le (sinh (z / 2) * exp ((θ : ℂ) * I)).re
    exact lt_of_lt_of_le (sub_pos.mpr hz) (by linarith)
  have hAc : Continuous (fun p : ℂ × ℝ => A p.1 p.2) := by
    unfold A
    fun_prop
  have hBc : Continuous (fun p : ℂ × ℝ => A p.1 (-p.2)) := by
    unfold A
    fun_prop
  have hcont : ContinuousOn (fun p : ℂ × ℝ => F p.1 p.2) (U ×ˢ univ) := by
    unfold F
    have hAbranch (p : ℂ × ℝ) (hp : p ∈ U ×ˢ (univ : Set ℝ)) : A p.1 p.2 ∈ slitPlane :=
      hbranch hp.1 p.2
    have hBbranch (p : ℂ × ℝ) (hp : p ∈ U ×ˢ (univ : Set ℝ)) : A p.1 (-p.2) ∈ slitPlane :=
      hbranch hp.1 (-p.2)
    exact ((hAc.continuousOn.cpow continuousOn_const hAbranch).mul
      (hBc.continuousOn.cpow continuousOn_const hBbranch)).mul (by fun_prop)
  have hdiff (θ : ℝ) : DifferentiableOn ℂ (fun z => F z θ) U := by
    unfold F
    have hA (φ : ℝ) : Differentiable ℂ (fun z => A z φ) := by
      unfold A
      fun_prop
    exact (((hA θ).differentiableOn.cpow_const (fun _ hz => hbranch hz θ)).mul
      ((hA (-θ)).differentiableOn.cpow_const (fun _ hz => hbranch hz (-θ)))).mul_const _
  have hint := Complex.differentiableOn_intervalIntegral_of_continuousOn
    hopen (ν := volume) 0 (2 * π) hcont hdiff
  rw [contDiff_iff_contDiffAt]
  intro x
  have ha := (hint.const_mul (((2 * π : ℝ) : ℂ)⁻¹)).analyticOnNhd hopen x (hReal x)
  have hRealAnalytic := (ha.restrictScalars (𝕜 := ℝ)).compContinuousLinearMap
    (u := Complex.ofRealCLM)
  have hcast (y : ℝ) : (y : ℂ) / 2 = (↑(y / 2) : ℂ) := by push_cast; rfl
  simpa only [boostMatrixElement_def, Function.comp_def, ofRealCLM_apply, F, A,
    hcast, ← ofReal_cosh, ← ofReal_sinh, ofReal_neg, neg_mul] using
    hRealAnalytic.contDiffAt

/-! ### Unitarity -/

/-- **Rows of the principal series.** For `Re τ = -1/2`, `Σ_k |𝔓^τ_{m+k,m}|² = 1` on the weights
`m ∈ e/2 + ℤ`. -/
theorem hasSum_norm_sq_boostMatrixElement_row (τ : ℂ) (hτ : τ.re = -1 / 2) (e : Fin 2) (n : ℤ)
    (t : ℝ) :
    HasSum (fun k : ℤ =>
      ‖boostMatrixElement τ (n - (e : ℕ) / 2 + k) (n - (e : ℕ) / 2) t‖ ^ 2) 1 := by
  let U := principalSeries τ e
  let basis := fourierBasis (T := 2 * π)
  let f := U (boost t) (basis n)
  have hu : U.IsUnitary := (isUnitary_principalSeries_iff τ e).mpr hτ
  have hnorm : ‖basis.repr f‖ = 1 := by
    rw [basis.repr.norm_map]
    dsimp only [f]
    rw [hu.norm_map, basis.orthonormal.norm_eq_one]
  have hS : HasSum (fun i => ‖basis.repr f i‖ ^ 2) (‖basis.repr f‖ ^ 2) := by
    apply_mod_cast lp.hasSum_norm ?_ (basis.repr f)
    simp
  rw [hnorm, one_pow] at hS
  have hshift := (Equiv.addRight n).hasSum_iff.mpr hS
  refine hshift.congr_fun fun k => ?_
  have heq : (n - (e : ℕ) / 2 + k : ℝ) = ((k + n : ℤ) : ℝ) - (e : ℕ) / 2 := by
    push_cast
    ring
  rw [heq, ← principalSeries_matrixElement_boost_eq, ContRepresentation.matrixElement_def]
  have hadd : Equiv.addRight n k = k + n := rfl
  simp only [Function.comp_apply, hadd, HilbertBasis.repr_apply_apply, f, U, basis]

/-- **Columns of the principal series.** For `Re τ = -1/2`, `Σ_k |𝔓^τ_{m,m+k}|² = 1` on the
weights `m ∈ e/2 + ℤ`. -/
theorem hasSum_norm_sq_boostMatrixElement_column (τ : ℂ) (hτ : τ.re = -1 / 2) (e : Fin 2)
    (n : ℤ) (t : ℝ) :
    HasSum (fun k : ℤ =>
      ‖boostMatrixElement τ (n - (e : ℕ) / 2) (n - (e : ℕ) / 2 + k) t‖ ^ 2) 1 := by
  have hprod : boost t * boost (-t) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_eq_matrix (boost t * boost (-t)), coe_eq_matrix (1 : SU11)]
    have hzero : -t / 2 = -(t / 2) := by ring
    simp only [entryA_mul, entryB_mul, entryA_one, entryB_one, entryA_boost, entryB_boost,
      hzero, Real.cosh_neg, Real.sinh_neg, ofReal_neg, map_neg, conj_ofReal]
    have hc : ((Real.cosh (t / 2) : ℂ)) ^ 2 - ((Real.sinh (t / 2) : ℂ)) ^ 2 = 1 := by
      exact_mod_cast Real.cosh_sq_sub_sinh_sq (t / 2)
    have ha : ↑(Real.cosh (t / 2)) * ↑(Real.cosh (t / 2)) +
        (↑(Real.sinh (t / 2)) : ℂ) * -↑(Real.sinh (t / 2)) = 1 := by
      linear_combination hc
    have hb : ↑(Real.cosh (t / 2)) * -↑(Real.sinh (t / 2)) +
        (↑(Real.sinh (t / 2)) : ℂ) * ↑(Real.cosh (t / 2)) = 0 := by
      ring
    rw [ha, hb]
  have hinv : (boost t)⁻¹ = boost (-t) := (eq_inv_of_mul_eq_one_right hprod).symm
  have hu := (isUnitary_principalSeries_iff τ e).mpr hτ
  refine (hasSum_norm_sq_boostMatrixElement_row τ hτ e n (-t)).congr_fun fun k => ?_
  have heq : (n - (e : ℕ) / 2 + k : ℝ) = ((n + k : ℤ) : ℝ) - (e : ℕ) / 2 := by
    push_cast
    ring
  rw [heq, ← principalSeries_matrixElement_boost_eq, ← principalSeries_matrixElement_boost_eq,
    ← hinv, ContRepresentation.matrixElement_inv _ hu, norm_conj]

/-- **Bound.** `|𝔓^τ_{m'm}(cosh t)| ≤ 1` for `Re τ = -1/2` and weights in `e/2 + ℤ`. -/
theorem norm_boostMatrixElement_le_one (τ : ℂ) (hτ : τ.re = -1 / 2) (e : Fin 2) (n' n : ℤ)
    (t : ℝ) :
    ‖boostMatrixElement τ (n' - (e : ℕ) / 2) (n - (e : ℕ) / 2) t‖ ≤ 1 := by
  rw [← principalSeries_matrixElement_boost_eq, ContRepresentation.matrixElement_def]
  have hu := (isUnitary_principalSeries_iff τ e).mpr hτ
  exact (norm_inner_le_norm _ _).trans (le_of_eq (by
    rw [hu.norm_map, fourierBasis.orthonormal.norm_eq_one,
      fourierBasis.orthonormal.norm_eq_one, one_mul]))

/-! ### The addition theorem and multiplication formulas -/

/-- **The Euler angles of a product.** If `b_{t₁} g(φ, t₂, 0) = g(α, t, γ)` then
`cosh t = cosh t₁ cosh t₂ + sinh t₁ sinh t₂ cos φ`. -/
theorem cosh_of_boost_mul_euler (t₁ t₂ φ α t γ : ℝ)
    (h : boost t₁ * euler φ t₂ 0 = euler α t γ) :
    Real.cosh t = Real.cosh t₁ * Real.cosh t₂ + Real.sinh t₁ * Real.sinh t₂ * Real.cos φ := by
  let c₁ := Real.cosh (t₁ / 2)
  let c₂ := Real.cosh (t₂ / 2)
  let s₁ := Real.sinh (t₁ / 2)
  let s₂ := Real.sinh (t₂ / 2)
  let z : ℂ := exp (((φ / 2 : ℝ) : ℂ) * I)
  have hzn : normSq z = 1 := by
    dsimp only [z]
    rw [normSq_eq_norm_sq, norm_exp_ofReal_mul_I, one_pow]
  have hzsq : z * z = exp ((φ : ℂ) * I) := by
    dsimp only [z]
    rw [← exp_add]
    congr 1
    push_cast
    ring
  have hcross : (((c₁ * c₂ : ℝ) : ℂ) * z *
      conj (((s₁ * s₂ : ℝ) : ℂ) * conj z)).re =
      c₁ * c₂ * (s₁ * s₂) * Real.cos φ := by
    rw [map_mul, conj_ofReal, conj_conj]
    have he : ((c₁ * c₂ : ℝ) : ℂ) * z * (((s₁ * s₂ : ℝ) : ℂ) * z) =
        (((c₁ * c₂ * (s₁ * s₂) : ℝ) : ℂ)) * (z * z) := by push_cast; ring
    rw [he, hzsq, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, exp_ofReal_mul_I_re]
  have he : normSq (((c₁ * c₂ : ℝ) : ℂ) * z + ((s₁ * s₂ : ℝ) : ℂ) * conj z) =
      Real.cosh (t / 2) ^ 2 := by
    have he := congrArg (normSq ∘ entryA) h
    simp only [Function.comp_apply, entryA_mul, entryA_boost, entryB_boost, entryA_euler,
      entryB_euler, add_zero, sub_zero, Circle.coe_exp] at he
    have hphase : normSq (exp ((((α + γ) / 2 : ℝ) : ℂ) * I)) = 1 := by
      rw [normSq_eq_norm_sq, norm_exp_ofReal_mul_I, one_pow]
    rw [normSq_mul, normSq_ofReal, hphase, mul_one, ← sq] at he
    convert he using 1
    rw [map_mul, conj_ofReal]
    dsimp only [c₁, c₂, s₁, s₂, z]
    push_cast
    congr 1
    ring
  rw [normSq_add, hcross, normSq_mul, normSq_mul, normSq_ofReal, normSq_ofReal, hzn,
    normSq_conj, hzn, mul_one, mul_one] at he
  have ht (x : ℝ) : Real.cosh x = 2 * Real.cosh (x / 2) ^ 2 - 1 := by
    have hh := Real.cosh_two_mul (x := x / 2)
    rw [show 2 * (x / 2) = x by ring] at hh
    linarith [Real.cosh_sq_sub_sinh_sq (x / 2)]
  have hs (x : ℝ) : Real.sinh x = 2 * Real.sinh (x / 2) * Real.cosh (x / 2) := by
    simpa only [show 2 * (x / 2) = x by ring] using Real.sinh_two_mul (x := x / 2)
  rw [ht t, ht t₁, ht t₂, hs t₁, hs t₂]
  change _ = (2 * c₁ ^ 2 - 1) * (2 * c₂ ^ 2 - 1) +
    (2 * s₁ * c₁) * (2 * s₂ * c₂) * Real.cos φ
  have h₁ : c₁ ^ 2 - s₁ ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  have h₂ : c₂ ^ 2 - s₂ ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  linear_combination -2 * he - 2 * s₂ ^ 2 * h₁ + (2 - 2 * c₁ ^ 2) * h₂

/-- **Addition theorem** (Vilenkin–Klimyk, Vol. 1, §6.6.1 (1)–(2), pp. 326–327). With
`b_{t₁} g(φ, t₂, 0) = g(α, t, γ)`,
`Σ_k 𝔓^τ_{m'k}(cosh t₁) e^{ikφ} 𝔓^τ_{km}(cosh t₂) = e^{i(m'α + mγ)} 𝔓^τ_{m'm}(cosh t)`. -/
theorem hasSum_boostMatrixElement_addition (τ : ℂ) (e : Fin 2) (n' n : ℤ) (t₁ t₂ φ α t γ : ℝ)
    (h : boost t₁ * euler φ t₂ 0 = euler α t γ) :
    HasSum (fun k : ℤ =>
        boostMatrixElement τ (n' - (e : ℕ) / 2) (k - (e : ℕ) / 2) t₁ *
          exp ((((k - (e : ℕ) / 2 : ℝ) * φ : ℝ) : ℂ) * I) *
          boostMatrixElement τ (k - (e : ℕ) / 2) (n - (e : ℕ) / 2) t₂)
      (exp ((((n' - (e : ℕ) / 2 : ℝ) * α + (n - (e : ℕ) / 2 : ℝ) * γ : ℝ) : ℂ) * I) *
        boostMatrixElement τ (n' - (e : ℕ) / 2) (n - (e : ℕ) / 2) t) := by
  have hs := (principalSeries τ e).hasSum_matrixElement_mul (fourierBasis (T := 2 * π))
    n' n (boost t₁) (euler φ t₂ 0)
  rw [h, principalSeries_matrixElement_euler_eq] at hs
  refine hs.congr_fun fun k => ?_
  rw [principalSeries_matrixElement_boost_eq, principalSeries_matrixElement_euler_eq]
  simp only [mul_zero, add_zero]
  ring

/-- The positive Euler parametrization, with diagonal rotations included at zero boost. -/
private theorem exists_euler_eq (g : SU11) : ∃ α t γ : ℝ, g = euler α t γ := by
  by_cases h : entryB g = 0
  · have ha := normSq_entryA_sub_normSq_entryB g
    rw [h, map_zero, sub_zero, normSq_eq_norm_sq] at ha
    have hn : ‖entryA g‖ = 1 := by nlinarith [norm_nonneg (entryA g)]
    refine ⟨2 * arg (entryA g), 0, 0, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_eq_matrix g, coe_eq_matrix (euler _ _ _)]
    have he : entryA (euler (2 * arg (entryA g)) 0 0) = entryA g := by
      rw [entryA_euler, add_zero, zero_div, Real.cosh_zero, ofReal_one, one_mul,
        show 2 * (entryA g).arg / 2 = (entryA g).arg by ring, Circle.coe_exp]
      simpa only [hn, ofReal_one, one_mul] using norm_mul_exp_arg_mul_I (entryA g)
    rw [he, entryB_euler, zero_div, Real.sinh_zero, ofReal_zero, zero_mul, h]
  · obtain ⟨p, _, hp⟩ := bijOn_euler.surjOn h
    exact ⟨p.1, p.2.1, p.2.2, hp.symm⟩

/-- **Multiplication formula** (Vilenkin–Klimyk, Vol. 1, §6.6.3 (1)–(8), pp. 327–329).
`𝔓^τ_{0k}(cosh t₁) 𝔓^τ_{k0}(cosh t₂) = (2π)⁻¹ ∫₀^{2π} e^{-ikφ} 𝔓^τ_{00}(x(φ)) dφ` with
`x(φ) = cosh t₁ cosh t₂ + sinh t₁ sinh t₂ cos φ`. -/
theorem boostMatrixElement_mul_boostMatrixElement (τ : ℂ) (k : ℤ) (t₁ t₂ : ℝ) :
    boostMatrixElement τ 0 k t₁ * boostMatrixElement τ k 0 t₂ =
      ((2 * π : ℝ) : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..2 * π,
        exp (-(((k * φ : ℝ) : ℂ) * I)) *
          boostMatrixElement τ 0 0
            (Real.arcosh (Real.cosh t₁ * Real.cosh t₂ +
              Real.sinh t₁ * Real.sinh t₂ * Real.cos φ)) := by
  let f : 𝕋 → ℂ := fun φ => boostMatrixElement τ 0 0
    (Real.arcosh (Real.cosh t₁ * Real.cosh t₂ +
      Real.sinh t₁ * Real.sinh t₂ * (fourier 1 φ).re))
  let c : ℤ → ℂ := fun j => boostMatrixElement τ 0 j t₁ * boostMatrixElement τ j 0 t₂
  have hf : ∀ φ : 𝕋, HasSum (fun j : ℤ => fourier j φ • c j) (f φ) := by
    intro φ
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective φ
    obtain ⟨α, t, γ, h⟩ := exists_euler_eq (boost t₁ * euler x t₂ 0)
    have hs := hasSum_boostMatrixElement_addition τ 0 0 0 t₁ t₂ x α t γ h
    simp only [Fin.val_zero, Nat.cast_zero, zero_div, sub_zero, Int.cast_zero, zero_mul,
      add_zero, ofReal_zero, exp_zero, one_mul] at hs
    have hcos : (fourier 1 (x : 𝕋)).re = Real.cos x := by
      rw [fourier_coe_two_pi, Int.cast_one, one_mul, exp_ofReal_mul_I_re]
    have hv : f (x : 𝕋) = boostMatrixElement τ 0 0 t := by
      dsimp only [f]
      rw [hcos, ← cosh_of_boost_mul_euler t₁ t₂ x α t γ h,
        boostMatrixElement_zero_zero_eq_legendreP, boostMatrixElement_zero_zero_eq_legendreP,
        Real.cosh_arcosh (Real.one_le_cosh t)]
    rw [hv]
    refine hs.congr_fun fun j => ?_
    rw [fourier_coe_two_pi, smul_eq_mul, ofReal_mul, ofReal_intCast]
    dsimp only [c]
    ring
  have hc : fourierCoeff f k = c k := congrFun (fourierCoeff_eq_of_hasSum hf) k
  change c k = _
  rw [← hc, fourierCoeff_eq_intervalIntegral f k 0, zero_add, real_smul, ofReal_div,
    ofReal_one, one_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [f, fourier_coe_two_pi, Int.cast_one, one_mul, exp_ofReal_mul_I_re, Int.cast_neg]
  push_cast
  congr 1
  ring_nf

/-- **Product formula with the triangle kernel.** For `t₁, t₂ > 0`,
`P_τ(cosh t₁) P_τ(cosh t₂) = π⁻¹ ∫_{|t₁-t₂|}^{t₁+t₂} P_τ(cosh s) sinh s Δ(s)^{-1/2} ds` with
`Δ(s) = (cosh(t₁ + t₂) - cosh s)(cosh s - cosh(t₁ - t₂))`. -/
theorem boostMatrixElement_product_kernel (τ : ℂ) (t₁ t₂ : ℝ) (h₁ : 0 < t₁) (h₂ : 0 < t₂) :
    boostMatrixElement τ 0 0 t₁ * boostMatrixElement τ 0 0 t₂ =
      ((π : ℝ) : ℂ)⁻¹ * ∫ s in |t₁ - t₂|..(t₁ + t₂),
        boostMatrixElement τ 0 0 s *
          ((Real.sinh s / Real.sqrt ((Real.cosh (t₁ + t₂) - Real.cosh s) *
            (Real.cosh s - Real.cosh (t₁ - t₂))) : ℝ) : ℂ) := by
  let A := Real.cosh t₁ * Real.cosh t₂
  let B := Real.sinh t₁ * Real.sinh t₂
  let a := |t₁ - t₂|
  let b := t₁ + t₂
  let x : ℝ → ℝ := fun φ => A + B * Real.cos φ
  let F : ℝ → ℂ := fun u => boostMatrixElement τ 0 0 (Real.arcosh u)
  let w : ℝ → ℝ := fun u => (Real.sqrt ((A + B - u) * (u - (A - B))))⁻¹
  have hB : 0 < B := mul_pos (Real.sinh_pos_iff.mpr h₁) (Real.sinh_pos_iff.mpr h₂)
  have hab : a ≤ b := (abs_le.mpr ⟨by dsimp only [b]; linarith, by dsimp only [b]; linarith⟩)
  have ha : Real.cosh a = A - B := by
    rw [show a = |t₁ - t₂| from rfl, Real.cosh_abs, Real.cosh_sub]
  have hb : Real.cosh b = A + B := by
    rw [show b = t₁ + t₂ from rfl, Real.cosh_add]
  have hxcont : Continuous x := by dsimp only [x]; fun_prop
  have hx1 (φ : ℝ) : 1 ≤ x φ := by
    have hl := Real.one_le_cosh a
    rw [ha] at hl
    have hv := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos φ) hB.le
    dsimp only [x]
    linarith
  have hFc : Continuous (fun φ => F (x φ)) := by
    rw [← continuousOn_univ]
    apply (contDiff_boostMatrixElement τ 0 0).continuous.continuousOn.comp
      (Real.continuousOn_arcosh.comp hxcont.continuousOn (fun φ _ => hx1 φ))
    exact mapsTo_univ _ _
  have hrefl : (∫ φ in π..2 * π, F (x φ)) = ∫ φ in (0 : ℝ)..π, F (x φ) := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := π)
      (fun φ => F (x φ)) (2 * π)
    rw [show 2 * π - π = π by ring, sub_zero] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro φ _
    simp only [x, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, one_mul, zero_mul, add_zero]
  have hprod := boostMatrixElement_mul_boostMatrixElement τ 0 t₁ t₂
  simp only [Int.cast_zero, zero_mul, ofReal_zero, neg_zero, exp_zero, one_mul] at hprod
  change _ = ((2 * π : ℝ) : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, F (x φ) at hprod
  rw [← intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable 0 π)
    (hFc.intervalIntegrable π (2 * π)), hrefl] at hprod
  have hnorm : ((2 * π : ℝ) : ℂ)⁻¹ * ((∫ φ in (0 : ℝ)..π, F (x φ)) +
      (∫ φ in (0 : ℝ)..π, F (x φ))) = ((π : ℝ) : ℂ)⁻¹ * ∫ φ in (0 : ℝ)..π, F (x φ) := by
    push_cast
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  rw [hnorm] at hprod
  rw [hprod, intervalIntegral.integral_of_le Real.pi_pos.le, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  congr 1
  let G : ℝ → ℂ := fun u => F u * (w u : ℂ)
  have hxa : StrictAntiOn x (Icc 0 π) := by
    intro u hu v hv huv
    exact add_lt_add_right (mul_lt_mul_of_pos_left (Real.strictAntiOn_cos hu hv huv) hB) A
  have hximage : x '' Ioo 0 π = Ioo (A - B) (A + B) := by
    rw [hxcont.continuousOn.image_Ioo_of_strictAntiOn Real.pi_pos.le hxa]
    simp [x, sub_eq_add_neg]
  have hdx (φ : ℝ) : HasDerivAt x (-(B * Real.sin φ)) φ := by
    simpa only [x, mul_neg] using ((Real.hasDerivAt_cos φ).const_mul B).const_add A
  have hchange₁ := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun φ _ => (hdx φ).hasDerivWithinAt) (hxa.injOn.mono Ioo_subset_Icc_self) G
  rw [hximage] at hchange₁
  have hφ : (∫ φ in Ioo (0 : ℝ) π, F (x φ)) = ∫ u in Ioo (A - B) (A + B), G u := by
    rw [hchange₁]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro φ hφ
    have hpos := mul_pos hB (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
    have hwp : Real.sqrt ((A + B - x φ) * (x φ - (A - B))) = B * Real.sin φ := by
      rw [← Real.sqrt_sq hpos.le]
      congr 1
      dsimp only [x]
      linear_combination -(B ^ 2) * (Real.sin_sq_add_cos_sq φ)
    change F (x φ) = |-(B * Real.sin φ)| • G (x φ)
    rw [abs_neg, abs_of_pos hpos, real_smul]
    dsimp only [G, w]
    rw [hwp, ofReal_inv]
    have hposC : ((B * Real.sin φ : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
    field_simp
  have hsmono : StrictMonoOn Real.cosh (Icc a b) :=
    Real.cosh_strictMonoOn.mono (fun s hs => le_trans (abs_nonneg _) hs.1)
  have hsimage : Real.cosh '' Ioo a b = Ioo (A - B) (A + B) := by
    rw [Real.continuous_cosh.continuousOn.image_Ioo_of_strictMonoOn hab hsmono, ha, hb]
  have hchange₂ := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun s _ => (Real.hasDerivAt_cosh s).hasDerivWithinAt)
    (hsmono.injOn.mono Ioo_subset_Icc_self) G
  rw [hsimage] at hchange₂
  rw [hφ, hchange₂]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hs
  have hs0 : 0 ≤ s := (abs_nonneg _).trans hs.1.le
  have hsinh : 0 ≤ Real.sinh s := Real.sinh_nonneg_iff.mpr hs0
  dsimp only
  rw [abs_of_nonneg hsinh, real_smul]
  dsimp only [G, F, w]
  rw [Real.arcosh_cosh hs0, ← hb, ← ha, Real.cosh_abs, ofReal_inv, ofReal_div]
  ring

/-! ### Generating functions and the degree -/

/-- **Generating function** (Vilenkin–Klimyk, Vol. 1, §6.7.1 (6)–(9), pp. 332–333).
`Σ_k 𝔓^τ_{n+k,n}(cosh t) e^{-ikθ} = A(θ)^{τ+n} A(-θ)^{τ-n}` with
`A(θ) = cosh(t/2) + sinh(t/2) e^{iθ}`. -/
theorem hasSum_boostMatrixElement_fourier (τ : ℂ) (n t θ : ℝ) :
    HasSum (fun k : ℤ => boostMatrixElement τ (n + k) n t * exp (-(((k * θ : ℝ) : ℂ) * I)))
      (((Real.cosh (t / 2) : ℂ) + Real.sinh (t / 2) * exp ((θ : ℂ) * I)) ^ (τ + n) *
        ((Real.cosh (t / 2) : ℂ) + Real.sinh (t / 2) * exp (-((θ : ℂ) * I))) ^ (τ - n)) := by
  have h := (Equiv.neg ℤ).hasSum_iff.mpr
    (hasSum_boostLaurentCoefficient τ n t (θ : 𝕋))
  have he : HasSum
      (fun k : ℤ => boostMatrixElement τ (n + k) n t * exp (-(((k * θ : ℝ) : ℂ) * I)))
      (boostKernel τ n t (fourier 1 (θ : 𝕋))) := by
    refine h.congr_fun fun k => ?_
    simp only [Function.comp_apply, Equiv.neg_apply, smul_eq_mul, fourier_coe_two_pi,
      Int.cast_neg, boostMatrixElement_eq_laurent]
    push_cast
    ring_nf
  have hconj : conj (exp ((θ : ℂ) * I)) = exp (-((θ : ℂ) * I)) := by
    rw [← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg]
  simpa only [boostKernel, boostBase, fourier_coe_two_pi, Int.cast_one, one_mul, hconj] using he

/-- **Row sum.** `Σ_k 𝔓^τ_{n+k,n}(cosh t) = e^{τt}`. -/
theorem hasSum_boostMatrixElement_row (τ : ℂ) (n t : ℝ) :
    HasSum (fun k : ℤ => boostMatrixElement τ (n + k) n t) (exp (τ * t)) := by
  have h := hasSum_boostMatrixElement_fourier τ n t 0
  simp only [ofReal_zero, mul_zero, zero_mul, neg_zero, exp_zero, mul_one] at h
  have hbase :
      (Real.cosh (t / 2) : ℂ) + Real.sinh (t / 2) = (Real.exp (t / 2) : ℂ) := by
    rw [← ofReal_add, Real.cosh_add_sinh]
  rw [hbase, ← cpow_add _ _ (ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    ← ofReal_log (Real.exp_pos _).le, Real.log_exp] at h
  have hval : ((t / 2 : ℝ) : ℂ) * ((τ + (n : ℂ)) + (τ - (n : ℂ))) = τ * t := by
    push_cast
    ring
  rw [hval] at h
  exact h

/-- **Alternating row sum.** `Σ_k (-1)^k 𝔓^τ_{n+k,n}(cosh t) = e^{-τt}`. -/
theorem hasSum_boostMatrixElement_row_alternating (τ : ℂ) (n t : ℝ) :
    HasSum (fun k : ℤ => (-1 : ℂ) ^ k * boostMatrixElement τ (n + k) n t) (exp (-(τ * t))) := by
  have h := hasSum_boostMatrixElement_fourier τ n t π
  have hh : exp ((π : ℂ) * I) = -1 := exp_pi_mul_I
  have hm : exp (-((π : ℂ) * I)) = -1 := by rw [exp_neg, hh, inv_neg, inv_one]
  rw [hh, hm] at h
  simp only [mul_neg, mul_one, ← ofReal_neg, ← ofReal_add, ← sub_eq_add_neg,
    Real.cosh_sub_sinh] at h
  rw [← cpow_add _ _ (ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
    ← ofReal_log (Real.exp_pos _).le, Real.log_exp] at h
  have hval : (-(t / 2 : ℝ) : ℂ) * ((τ + (n : ℂ)) + (τ - (n : ℂ))) = -(τ * t) := by
    push_cast
    ring
  rw [ofReal_neg, hval] at h
  refine h.congr_fun fun k => ?_
  have hpow : exp (-(((k * π : ℝ) : ℂ) * I)) = (-1 : ℂ) ^ k := by
    push_cast
    rw [show -((k : ℂ) * π * I) = (k : ℂ) * (-((π : ℂ) * I)) by ring,
      exp_int_mul, hm]
  rw [hpow, mul_comm]

/-- Two absolutely convergent Fourier series multiply by convolution of their coefficients. -/
private theorem hasSum_fourier_mul {a b : ℤ → ℂ} {f g : 𝕋 → ℂ}
    (ha : ∀ θ : 𝕋, HasSum (fun k : ℤ => fourier k θ • a k) (f θ))
    (hb : ∀ θ : 𝕋, HasSum (fun k : ℤ => fourier k θ • b k) (g θ)) (θ : 𝕋) :
    HasSum (fun j : ℤ => fourier j θ • (∑' k : ℤ, a k * b (j - k))) (f θ * g θ) := by
  have hnorm (c : ℤ → ℂ) (h : Summable fun k => ‖c k‖) :
      Summable (fun k : ℤ => ‖fourier k θ • c k‖) := by
    simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using h
  have haN : Summable (fun k : ℤ => ‖a k‖) := by
    simpa only [fourier_eval_zero, one_smul] using (ha 0).summable.norm
  have hbN : Summable (fun k : ℤ => ‖b k‖) := by
    simpa only [fourier_eval_zero, one_smul] using (hb 0).summable.norm
  let addIndex : ℤ × ℤ → ℤ := fun p => p.1 + p.2
  let A : ℤ → ℂ := fun k => fourier k θ • a k
  let B : ℤ → ℂ := fun k => fourier k θ • b k
  let H : ℤ × ℤ → ℂ := fun p => A p.1 * B p.2
  have hA : HasSum A (f θ) := ha θ
  have hB : HasSum B (g θ) := hb θ
  have hab : Summable H := summable_mul_of_summable_norm (f := A) (g := B)
    (hnorm a haN) (hnorm b hbN)
  have hmul : HasSum H (f θ * g θ) := HasSum.mul (α := ℂ) hA hB hab
  have ht : HasSum (fun j => ∑' k : ↥(addIndex ⁻¹' {j}), H k) (f θ * g θ) :=
    HasSum.tsum_fiberwise (α := ℂ) hmul addIndex
  refine ht.congr_fun fun j => ?_
  let fiber : ℤ ≃ ↥(addIndex ⁻¹' {j}) :=
    { toFun := fun k => ⟨(k, j - k), by simp [addIndex, add_sub_cancel]⟩
      invFun := fun k => k.1.1
      left_inv := fun _ => rfl
      right_inv := by
        intro p
        apply Subtype.ext
        refine Prod.ext rfl ?_
        have hp : p.1.1 + p.1.2 = j := p.2
        change j - p.1.1 = p.1.2
        omega }
  rw [← fiber.tsum_eq, smul_eq_mul, ← tsum_mul_left]
  apply tsum_congr
  intro k
  symm
  change (fourier k θ • a k) * (fourier (j - k) θ • b (j - k)) =
    fourier j θ * (a k * b (j - k))
  rw [smul_eq_mul, smul_eq_mul, mul_mul_mul_comm, ← fourier_add, add_sub_cancel]

/-- **Convolution in the degree.**
`𝔓^{τ₁+τ₂}_{n₁+n₂+j, n₁+n₂} = Σ_k 𝔓^{τ₁}_{n₁+k, n₁} 𝔓^{τ₂}_{n₂+j-k, n₂}`. -/
theorem hasSum_boostMatrixElement_degree (τ₁ τ₂ : ℂ) (n₁ n₂ : ℝ) (j : ℤ) (t : ℝ) :
    HasSum (fun k : ℤ => boostMatrixElement τ₁ (n₁ + k) n₁ t *
        boostMatrixElement τ₂ (n₂ + (j - k : ℤ)) n₂ t)
      (boostMatrixElement (τ₁ + τ₂) (n₁ + n₂ + j) (n₁ + n₂) t) := by
  let a : ℤ → ℂ := fun k => boostLaurentCoefficient τ₁ n₁ t k
  let b : ℤ → ℂ := fun k => boostLaurentCoefficient τ₂ n₂ t k
  let H : 𝕋 → ℂ := fun θ => boostKernel (τ₁ + τ₂) (n₁ + n₂) t (fourier 1 θ)
  have ha (θ : 𝕋) : HasSum (fun k : ℤ => fourier k θ • a k)
      (boostKernel τ₁ n₁ t (fourier 1 θ)) :=
    hasSum_boostLaurentCoefficient τ₁ n₁ t θ
  have hb (θ : 𝕋) : HasSum (fun k : ℤ => fourier k θ • b k)
      (boostKernel τ₂ n₂ t (fourier 1 θ)) :=
    hasSum_boostLaurentCoefficient τ₂ n₂ t θ
  have h (θ : 𝕋) : HasSum (fun j : ℤ => fourier j θ • (∑' k : ℤ, a k * b (j - k))) (H θ) := by
    dsimp only [H]
    rw [← boostKernel_mul τ₁ τ₂ n₁ n₂ t (norm_fourier_one θ)]
    exact hasSum_fourier_mul ha hb θ
  have haN : Summable (fun j : ℤ => ‖a j‖) := by
    simpa only [fourier_eval_zero, one_smul] using (ha 0).summable.norm
  have hbN : Summable (fun j : ℤ => ‖b j‖) := by
    simpa only [fourier_eval_zero, one_smul] using (hb 0).summable.norm
  let p : ℤ → ℤ × ℤ := fun k => (-k, -(j - k))
  have hpinj : Function.Injective p := by
    intro k l heq
    exact neg_injective (congrArg Prod.fst heq)
  have hprod : Summable (fun p : ℤ × ℤ => a p.1 * b p.2) :=
    summable_mul_of_summable_norm haN hbN
  simp_rw [boostMatrixElement_eq_laurent τ₁, boostMatrixElement_eq_laurent τ₂]
  change HasSum (fun k : ℤ => a (-k) * b (-(j - k))) _
  rw [boostMatrixElement_eq_fourierCoeff]
  change HasSum (fun k : ℤ => a (-k) * b (-(j - k))) (fourierCoeff H (-j))
  have hcoeff : fourierCoeff H (-j) = ∑' k : ℤ, a k * b (-j - k) :=
    congrFun (fourierCoeff_eq_of_hasSum h) (-j)
  rw [hcoeff]
  have hs : Summable (fun k : ℤ => a (-k) * b (-(j - k))) :=
    hprod.comp_injective hpinj
  convert hs.hasSum using 1
  rw [← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro k
  rw [Equiv.neg_apply, show -j - -k = -(j - k) by omega]

/-- **Shift of the degree by `1/2`.**
`𝔓^{τ+1/2}_{m+1/2, n+1/2} = cosh(t/2) 𝔓^τ_{m,n} + sinh(t/2) 𝔓^τ_{m+1,n}`. -/
theorem boostMatrixElement_degree_shift (τ : ℂ) (n : ℝ) (k : ℤ) (t : ℝ) :
    boostMatrixElement (τ + 1 / 2) (n + 1 / 2 + k) (n + 1 / 2) t =
      Real.cosh (t / 2) * boostMatrixElement τ (n + k) n t +
        Real.sinh (t / 2) * boostMatrixElement τ (n + 1 + k) n t := by
  have hm : (n + 1 + k : ℝ) = n + ((k + 1 : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hm, boostMatrixElement_eq_circleIntegral, boostMatrixElement_eq_circleIntegral,
    boostMatrixElement_eq_circleIntegral, ← integral_const_mul, ← integral_const_mul,
    ← integral_add]
  · apply integral_congr_ae
    refine Filter.Eventually.of_forall fun θ => ?_
    dsimp only
    rw [boostKernel_degree_shift τ n t (norm_fourier_one θ), boostBase, fourier_add]
    ring
  · exact ((continuous_boostKernel_character τ n t k).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  · exact ((continuous_boostKernel_character τ n t (k + 1)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _

/-! ### Unitarity of the complementary series -/

/-- Gamma reflection with an integer shift in its argument. -/
private theorem gamma_add_int_mul_gamma_neg (τ : ℝ) (k : ℤ) :
    Real.Gamma (τ + k + 1) * Real.Gamma (-τ - k) =
      (-1 : ℝ) ^ k * (Real.Gamma (τ + 1) * Real.Gamma (-τ)) := by
  rw [show -τ - k = 1 - (τ + k + 1) by ring, Real.Gamma_mul_Gamma_one_sub,
    show -τ = 1 - (τ + 1) by ring, Real.Gamma_mul_Gamma_one_sub,
    show π * (τ + k + 1) = π * (τ + 1) + (k : ℝ) * π by ring,
    Real.sin_add_int_mul_pi, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, ← inv_zpow,
    inv_neg, inv_one]
  ring

/-- The complementary degree reflection with the Gamma weight ratio. -/
private theorem boostMatrixElement_complementary_weight (τ : ℝ) (hτ : τ ∈ Ioo (-1) 0)
    (k n : ℤ) (t : ℝ) :
    boostMatrixElement (-((τ : ℝ) : ℂ) - 1) k n t =
      ((Real.Gamma (τ - k + 1) / Real.Gamma (-τ - k) /
        (Real.Gamma (τ - n + 1) / Real.Gamma (-τ - n)) : ℝ) : ℂ) *
        boostMatrixElement τ k n t := by
  let C : ℂ := ↑(Real.Gamma (τ + 1) * Real.Gamma (-τ))
  let s : ℤ → ℂ := fun k => (-1 : ℂ) ^ k
  let w : ℤ → ℂ := fun k => ↑(Real.Gamma (τ - k + 1) / Real.Gamma (-τ - k))
  have hC : C ≠ 0 := ofReal_ne_zero.mpr
    (mul_pos (Real.Gamma_pos_of_pos (by linarith [hτ.1]))
      (Real.Gamma_pos_of_pos (by linarith [hτ.2]))).ne'
  have hs (j : ℤ) : s j ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hsSq (j : ℤ) : s j * s j = 1 := by
    simp [s, ← mul_zpow]
  have hΓ (j : ℤ) : (Gamma ((τ : ℂ) + j + 1)) * Gamma (-(τ : ℂ) - j) = s j * C := by
    have h := congrArg Complex.ofReal (gamma_add_int_mul_gamma_neg τ j)
    simpa only [ofReal_mul, ofReal_zpow, ofReal_neg, ofReal_one, s, C, ← Gamma_ofReal,
      ofReal_add, ofReal_sub, ofReal_intCast] using h
  have hnonzero (j : ℤ) : Gamma ((τ : ℂ) + j + 1) ≠ 0 ∧ Gamma (-(τ : ℂ) - j) ≠ 0 := by
    apply mul_ne_zero_iff.mp
    rw [hΓ]
    exact mul_ne_zero (hs j) hC
  have hminus (j : ℤ) : Gamma ((τ : ℂ) - j + 1) ≠ 0 := by
    simpa only [Int.cast_neg, ← sub_eq_add_neg] using (hnonzero (-j)).1
  have hw (j : ℤ) : w j = Gamma ((τ : ℂ) - j + 1) / Gamma (-(τ : ℂ) - j) := by
    simp only [w, ofReal_div, ← Gamma_ofReal, ofReal_add, ofReal_sub, ofReal_intCast, ofReal_one,
      ofReal_neg]
  have hwnz (j : ℤ) : w j ≠ 0 := by
    rw [hw]
    exact div_ne_zero (hminus j) (hnonzero j).2
  have hnormalized (j : ℤ) :
      (Gamma ((τ : ℂ) - j + 1))⁻¹ * (Gamma ((τ : ℂ) + j + 1))⁻¹ =
        s j * (w j)⁻¹ * C⁻¹ := by
    rw [hw, inv_div, div_eq_mul_inv]
    field_simp [hminus j, (hnonzero j).1, hC]
    linear_combination -(s j) * hΓ j - C * hsSq j
  have hk : ((n : ℝ) + ((k - n : ℤ) : ℝ)) = (k : ℝ) := by push_cast; ring
  have h := boostMatrixElement_reflect (τ : ℂ) (n : ℝ) (k - n) t
  rw [hk, ofReal_intCast, ofReal_intCast, hnormalized, hnormalized] at h
  have hsign : (-1 : ℂ) ^ (k - n) = s k * s n := by
    rw [zpow_sub₀ (by norm_num : (-1 : ℂ) ≠ 0), div_eq_mul_inv, ← inv_zpow, inv_neg, inv_one]
  rw [hsign] at h
  change boostMatrixElement (-(τ : ℂ) - 1) k n t = _ * boostMatrixElement τ k n t
  rw [ofReal_div]
  change boostMatrixElement (-(τ : ℂ) - 1) k n t = w k / w n * boostMatrixElement τ k n t
  apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (hs k) (inv_ne_zero (hwnz k))) (inv_ne_zero hC))
  rw [h]
  calc
    _ = s k * (s n * s n) *
        (boostMatrixElement τ k n t * (w n)⁻¹ * C⁻¹) := by ring
    _ = _ := by
      rw [hsSq n, mul_one]
      field_simp [hwnz k]

/-- **Unitarity of the complementary series.** For `-1 < τ < 0`,
`Σ_k w(k)/w(n) |𝔓^τ_{kn}|² = 1` with `w(n) = Γ(τ - n + 1) / Γ(-τ - n)`. -/
theorem hasSum_complementary (τ : ℝ) (hτ : τ ∈ Ioo (-1) 0) (n : ℤ) (t : ℝ) :
    HasSum (fun k : ℤ => Real.Gamma (τ - k + 1) / Real.Gamma (-τ - k) /
        (Real.Gamma (τ - n + 1) / Real.Gamma (-τ - n)) *
        ‖boostMatrixElement τ k n t‖ ^ 2) 1 := by
  have hvalue : boostMatrixElement (-1) 0 0 t = 1 := by
    have h := boostMatrixElement_reflect 0 0 0 t
    norm_num [Gamma_one] at h
    rw [h, boostMatrixElement_zero_zero]
    simp only [cpow_zero, intervalIntegral.integral_const, sub_zero, real_smul, mul_one]
    exact inv_mul_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have h := hasSum_boostMatrixElement_degree (τ : ℂ) (-(τ : ℂ) - 1) (n : ℝ) (-(n : ℝ)) 0 t
  rw [show (τ : ℂ) + (-(τ : ℂ) - 1) = -1 by ring] at h
  simp only [Int.cast_zero, add_neg_cancel, add_zero, zero_sub] at h
  rw [hvalue] at h
  have hs := (Equiv.addRight (-n)).hasSum_iff.mpr h
  have he (k : ℤ) : (n : ℝ) + ((k + -n : ℤ) : ℝ) = (k : ℝ) := by push_cast; ring
  have hc : HasSum (fun k : ℤ => boostMatrixElement τ (k : ℝ) n t *
      boostMatrixElement (-(τ : ℂ) - 1) k n t) (1 : ℂ) := by
    refine hs.congr_fun fun k => ?_
    simp only [Function.comp_apply, Equiv.coe_addRight, he]
    have hh := boostMatrixElement_neg_neg (-(τ : ℂ) - 1) (n : ℝ) (k + -n) t
    rw [he] at hh
    have he' : -(n : ℝ) + ((-(k + -n) : ℤ) : ℝ) = -(k : ℝ) := by
      rw [Int.cast_neg]
      linarith [he k]
    rw [he', hh]
  rw [← ofReal_one] at hc
  have hr : HasSum (fun k : ℤ => (boostMatrixElement τ (k : ℝ) n t *
      boostMatrixElement (-(τ : ℂ) - 1) k n t).re) (1 : ℝ) :=
    by simpa only [one_re, ofReal_one, reCLM_apply, Function.comp_def] using
      hc.map reCLM reCLM.continuous
  refine hr.congr_fun fun k => ?_
  have hconj : conj (boostMatrixElement τ (k : ℝ) n t) = boostMatrixElement τ k n t := by
    simpa only [he, conj_ofReal] using conj_boostMatrixElement (τ : ℂ) (n : ℝ) (k + -n) t
  have hnorm : boostMatrixElement τ (k : ℝ) n t * boostMatrixElement τ k n t =
      ((‖boostMatrixElement τ k n t‖ ^ 2 : ℝ) : ℂ) := by
    nth_rw 2 [← hconj]
    rw [mul_conj, normSq_eq_norm_sq]
  rw [boostMatrixElement_complementary_weight τ hτ, mul_left_comm, hnorm, ← ofReal_mul,
    ofReal_re]

/-! ### Other one-parameter subgroups -/

/-- **The parabolic subgroup in Euler angles.**
`parabolic s = g(β, 2 arsinh(s/2), β)` with `β = arctan(s/2)`. -/
theorem parabolic_eq_euler (s : ℝ) :
    parabolic s =
      euler (Real.arctan (s / 2)) (2 * Real.arsinh (s / 2)) (Real.arctan (s / 2)) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_eq_matrix (parabolic s), coe_eq_matrix (euler _ _ _)]
  have hr : 0 < √(1 + (s / 2) ^ 2) := Real.sqrt_pos_of_pos (by positivity)
  have hA : entryA (parabolic s) =
      entryA (euler (Real.arctan (s / 2)) (2 * Real.arsinh (s / 2)) (Real.arctan (s / 2))) := by
    rw [entryA_parabolic, entryA_euler, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      Real.cosh_arsinh, add_self_div_two, Circle.coe_exp, Complex.exp_ofReal_mul_I,
      Real.cos_arctan, Real.sin_arctan]
    simp only [ofReal_div, ofReal_one]
    let r : ℂ := (√(1 + (s / 2) ^ 2) : ℝ)
    have hr' : r ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    change 1 + (s : ℂ) / (↑(2 : ℝ)) * I =
      r * (1 / r + ((s : ℂ) / (↑(2 : ℝ))) / r * I)
    field_simp
  have hB : entryB (parabolic s) =
      entryB (euler (Real.arctan (s / 2)) (2 * Real.arsinh (s / 2)) (Real.arctan (s / 2))) := by
    rw [entryB_parabolic, entryB_euler, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0),
      Real.sinh_arsinh, sub_self, zero_div, Circle.exp_zero, Circle.coe_one, mul_one]
  rw [hA, hB]

/-- **Matrix elements on the parabolic subgroup.**
`D_{m'm}(parabolic s) = e^{i(m'+m) arctan(s/2)} 𝔓^τ_{m'm}(cosh(2 arsinh(s/2)))`. -/
theorem principalSeries_matrixElement_parabolic (τ : ℂ) (e : Fin 2) (n' n : ℤ) (s : ℝ) :
    ContRepresentation.matrixElement (principalSeries τ e) (fourierBasis (T := 2 * π)) n' n
        (parabolic s) =
      exp ((((n' - (e : ℕ) / 2 + (n - (e : ℕ) / 2) : ℝ) * Real.arctan (s / 2) : ℝ) : ℂ) * I) *
        boostMatrixElement τ (n' - (e : ℕ) / 2) (n - (e : ℕ) / 2) (2 * Real.arsinh (s / 2)) := by
  rw [parabolic_eq_euler, principalSeries_matrixElement_euler_eq]
  congr 3
  push_cast
  ring

end SFVK.SU11
