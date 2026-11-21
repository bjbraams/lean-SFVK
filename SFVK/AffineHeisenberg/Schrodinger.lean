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
import DLMF.OrthogonalPolynomials.Integrals.GegenbauerAndLegendre
import DLMF.OrthogonalPolynomials.Integrals.LaguerreAndHermite
import DLMF.OrthogonalPolynomials.Series.ClassicalGenerating
import DLMF.OrthogonalPolynomials.Series.JacobiParameterSeries
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Schwartz
import DLMF.OrthogonalPolynomials.LaguerreContinuation


/-!
# The Schrödinger representation and Hermite matrix elements

The Schrödinger action of `(x, y, z)` on the real line multiplies by `e^{i(z + yu)}`
and translates the argument by `x`. In the Hermite basis its matrix elements are given
by Laguerre polynomials. The representation law gives their addition formula, and
Plancherel in the modulation variable gives their orthogonality.

Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2,
§12.1.6–12.1.8, pp. 415–421; Klimyk–Vilenkin, *Representations of Lie Groups and Special
Functions* (Kirillov (ed.), EMS 59), Ch. 6 §1.4 (5)–(7), p. 239.
-/

public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction Polynomial
open DLMF.Hypergeometric DLMF.OrthogonalPolynomials
open scoped Real ComplexConjugate InnerProductSpace ENNReal FourierTransform SchwartzMap

/-- §3.1. The matrix element of `U(x, y, z)` in the Hermite basis: with
`α = (-x + iy)/√2` and `A = (x² + y²)/2`, `e^{i(z - xy/2)} e^{-A/2}` times
`(n!/m!)^{1/2} α^{m-n} L_n^{(m-n)}(A)` for `n ≤ m` and `(m!/n!)^{1/2} (-conj α)^{n-m}
L_m^{(n-m)}(A)` for `m < n`. -/
@[expose]
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

local instance : MeasurableConstSMul (TauCeti.HeisenbergGroup ℝ) ℝ where
  measurable_const_smul g := by
    change Measurable (fun x : ℝ => x - g.x)
    fun_prop

/-- The Schrödinger action on the real line gives a unitary representation on Lebesgue `L²`. -/
private theorem schrodinger_realization :
    ∃ U : ContRepresentation ℂ (TauCeti.HeisenbergGroup ℝ) (Lp ℂ 2 (volume : Measure ℝ)),
      U.IsUnitary ∧ ∀ g f, (U g f : ℝ → ℂ) =ᵐ[volume]
        multiplierAction schrodingerCocycle g f := by
  have hcocycle : IsMultiplierCocycle schrodingerCocycle := by
    refine ⟨fun x => by simp [schrodingerCocycle], fun g h x => ?_⟩
    have hx : g⁻¹ • x = x + g.x := by change x - g⁻¹.x = _; simp
    rw [hx]
    simp only [schrodingerCocycle, TauCeti.HeisenbergGroup.mul_y, TauCeti.HeisenbergGroup.mul_z,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hmeas (g : TauCeti.HeisenbergGroup ℝ) : Measurable (schrodingerCocycle g) := by
    unfold schrodingerCocycle
    fun_prop
  have hqi : (volume : Measure ℝ).IsQuasiInvariantWith
      (fun (_ : TauCeti.HeisenbergGroup ℝ) (_ : ℝ) => 1) := by
    intro g
    change Measure.map (fun x : ℝ => x - g.x) volume = volume.withDensity 1
    rw [withDensity_one]
    simpa only [sub_eq_add_neg] using (measurePreserving_add_right volume (-g.x)).map_eq
  refine (exists_isUnitary_multiplierAction_iff hcocycle hmeas (fun _ => measurable_const)
    hqi).2 ?_
  intro g
  filter_upwards [] with x
  rw [← ofReal_norm, schrodingerCocycle, norm_exp, mul_I_re, ofReal_im,
    neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_pow]

/-- The Schrödinger operator is modulation followed by translation in its argument. -/
theorem schrodinger_apply_ae (g : TauCeti.HeisenbergGroup ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (schrodinger g f : ℝ → ℂ) =ᵐ[volume]
      fun x => Complex.exp ((g.z + g.y * x : ℝ) * Complex.I) * f (x + g.x) := by
  obtain ⟨U, _, hU⟩ := schrodinger_realization
  have h := multiplierRepresentation_ae_eq ⟨U, hU⟩ g f
  refine h.trans (Filter.Eventually.of_forall fun x => ?_)
  have hx : g⁻¹ • x = x + g.x := by change x - g⁻¹.x = _; simp
  rw [multiplierAction_def, hx]
  rfl

/-- The Schrödinger operators preserve the `L²` norm. -/
theorem isUnitary_schrodinger : schrodinger.IsUnitary := by
  obtain ⟨U, hU, hformula⟩ := schrodinger_realization
  have he : schrodinger = U :=
    multiplierRep_unique (multiplierRepresentation_ae_eq ⟨U, hformula⟩) hformula
  rw [he]
  exact hU

/-- Choosing disjoint sets of two specified sizes gives the same count in either order. -/
private theorem choose_mul_choose_sub (n i j : ℕ) :
    n.choose i * (n - i).choose j = n.choose j * (n - j).choose i := by
  have hs₁ : i ≤ i + j := by omega
  have hs₂ : j ≤ i + j := by omega
  have h₁ := Nat.choose_mul (n := n) hs₁
  have h₂ := Nat.choose_mul (n := n) hs₂
  rw [show i + j - i = j by omega] at h₁
  rw [show i + j - j = i by omega] at h₂
  rw [← h₁, ← h₂, ← Nat.choose_symm hs₂, show i + j - j = i by omega]

/-- Reindex the Hermite contraction sum by the two uncontracted degrees. -/
private theorem hermiteContraction_sum (m n : ℕ) (p q : ℂ) :
    (∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (min m (n - j) + 1),
      (n.choose j : ℂ) * q ^ j * ((m.choose k : ℂ) * (n - j).choose k * 2 ^ k *
        k.factorial) * p ^ (m + (n - j) - 2 * k)) =
    ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * 2 ^ k *
      k.factorial * p ^ (m - k) * (q + p) ^ (n - k) := by
  let T (j k : ℕ) : ℂ :=
    (n.choose j : ℂ) * q ^ j * ((m.choose k : ℂ) * (n - j).choose k * 2 ^ k *
      k.factorial) * p ^ (m + (n - j) - 2 * k)
  change (∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (min m (n - j) + 1), T j k) = _
  have hFilter (j : ℕ) : Finset.range (min m (n - j) + 1) =
      (Finset.range (min m n + 1)).filter (fun k => k ≤ n - j) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_filter, Nat.lt_succ_iff, le_min_iff]
    omega
  simp_rw [hFilter, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ m ∧ k ≤ n := le_min_iff.mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hFilter' : ((Finset.range (n + 1)).filter (fun j => k ≤ n - j)) =
      Finset.range (n - k + 1) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_filter, Nat.lt_succ_iff]
    omega
  rw [← Finset.sum_filter, hFilter', add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ n - k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hChoose : (n.choose j : ℂ) * (n - j).choose k =
      (n.choose k : ℂ) * (n - k).choose j := by
    exact_mod_cast choose_mul_choose_sub n j k
  dsimp only [T]
  rw [show m + (n - j) - 2 * k = (m - k) + (n - k - j) by omega, pow_add]
  linear_combination (m.choose k : ℂ) * q ^ j * 2 ^ k * k.factorial *
    p ^ (m - k) * p ^ (n - k - j) * hChoose

/-- A Hermite polynomial times the shifted Gaussian Laplace weight is integrable on the real line.
-/
private theorem integrable_hermitePolynomialH_laplace (n : ℕ) (z : ℂ) :
    Integrable (fun x : ℝ => exp (-x * z) * (aeval (x : ℂ) (hermitePolynomialH n) : ℂ) *
      exp (-(x : ℂ) ^ 2)) := by
  refine (integrable_eval_mul_cexp_gauss (hermitePolyHR n) z).congr
    (Filter.Eventually.of_forall fun x => ?_)
  have h : (aeval (x : ℂ) (hermitePolynomialH n) : ℂ) =
      (((hermitePolyHR n).eval x : ℝ) : ℂ) := by
    rw [← aeval_hermitePolynomialH_eq_eval]
    exact aeval_algebraMap_apply ℂ x (hermitePolynomialH n)
  simp only [h, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_pow, mul_assoc]

/-- The Laplace integral of two Hermite polynomials, with the second argument translated, is a
finite contraction sum. -/
private theorem integral_translate_hermitePolynomialH (m n : ℕ) (a z : ℂ) :
    (∫ x : ℝ, exp (-x * z) * (aeval (x : ℂ) (hermitePolynomialH m) : ℂ) *
      aeval (x + a) (hermitePolynomialH n) * exp (-(x : ℂ) ^ 2)) =
    (Real.sqrt Real.pi : ℂ) * exp (z ^ 2 / 4) *
      ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * 2 ^ k *
        k.factorial * (-z) ^ (m - k) * (2 * a - z) ^ (n - k) := by
  let G (j : ℕ) (x : ℝ) : ℂ :=
    exp (-x * z) * (aeval (x : ℂ) (hermitePolynomialH j) : ℂ) * exp (-(x : ℂ) ^ 2)
  let coeff (j k : ℕ) : ℂ := (n.choose j : ℂ) * (2 * a) ^ j *
    ((m.choose k : ℂ) * (n - j).choose k * 2 ^ k * k.factorial)
  have hExpanded (x : ℝ) : exp (-x * z) * (aeval (x : ℂ) (hermitePolynomialH m) : ℂ) *
      aeval (x + a) (hermitePolynomialH n) * exp (-(x : ℂ) ^ 2) =
        ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (min m (n - j) + 1),
          coeff j k * G (m + (n - j) - 2 * k) x := by
    rw [hermitePolynomialH_translation, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    have hSort : exp (-x * z) * (aeval (x : ℂ) (hermitePolynomialH m) : ℂ) *
        ((n.choose j : ℂ) * (2 * a) ^ j * aeval (x : ℂ) (hermitePolynomialH (n - j))) *
        exp (-(x : ℂ) ^ 2) =
        ((n.choose j : ℂ) * (2 * a) ^ j) *
        ((aeval (x : ℂ) (hermitePolynomialH m) : ℂ) *
          aeval (x : ℂ) (hermitePolynomialH (n - j))) * exp (-x * z) *
          exp (-(x : ℂ) ^ 2) := by ring
    rw [hSort, hermitePolynomialH_linearization, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [coeff, G]
    ring
  simp_rw [hExpanded]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ =>
    (integrable_hermitePolynomialH_laplace _ z).const_mul _))]
  simp_rw [integral_finsetSum _ (fun k _ =>
    (integrable_hermitePolynomialH_laplace _ z).const_mul _), integral_const_mul]
  simp only [hermitePolynomialH_laplace_transform]
  have hcontract := hermiteContraction_sum m n (-z) (2 * a)
  rw [sub_eq_add_neg, ← hcontract, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [coeff]
  ring

/-- The Hermite contraction for ordered degrees is a generalized Laguerre polynomial times a power.
-/
private theorem contraction_sum_eq_laguerre (m n : ℕ) (hn : n ≤ m)
    (a b A : ℂ) (hab : a * b = -A) :
    (∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * k.factorial *
      a ^ (m - k) * b ^ (n - k)) =
      n.factorial * a ^ (m - n) * laguerreExtended ((m : ℂ) - n) n A := by
  rw [min_eq_right hn, laguerreExtended_eq_reverse_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hkm : k ≤ m := hkn.trans hn
  have hbase : (m : ℂ) - n + (n - k : ℕ) + 1 = (m - k : ℕ) + 1 := by
    rw [Nat.cast_sub hkn, Nat.cast_sub hkm]
    ring
  have hcoeff : (m.choose k : ℂ) * k.factorial = pochhammer ((m - k : ℕ) + 1) k := by
    have hfac : (m.choose k : ℂ) * k.factorial * (m - k).factorial = m.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkm
    have hp : ((m - k).factorial : ℂ) * pochhammer ((m - k : ℕ) + 1) k = m.factorial := by
      simpa only [pochhammer, Nat.sub_add_cancel hkm] using
        (factorial_mul_ascPochhammer ℂ (m - k) k)
    apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr (m - k).factorial_ne_zero)
    rw [hfac, mul_comm, hp]
  have hcoeff' : (n.choose k : ℂ) * (k.factorial * (n - k).factorial) = n.factorial := by
    rw [← mul_assoc]
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  have hp : a ^ (m - k) * b ^ (n - k) = a ^ (m - n) * (-A) ^ (n - k) := by
    rw [← hab, mul_pow, ← mul_assoc, ← pow_add]
    rw [show m - n + (n - k) = m - k by omega]
  rw [hbase, ← hcoeff, ← hcoeff']
  calc
    _ = (m.choose k : ℂ) * n.choose k * k.factorial * (a ^ (m - k) * b ^ (n - k)) := by ring
    _ = _ := by
      rw [hp]
      have hk₀ : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
      have hnk₀ : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
      field_simp [hk₀, hnk₀]

/-- Scale the two Hermite arguments by a square root of two to remove the powers of two from the
contraction. -/
private theorem scale_hermiteContraction (m n : ℕ) (a b r : ℂ) (hr : r ^ 2 = 2) :
    (∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * 2 ^ k *
        k.factorial * (r * a) ^ (m - k) * (r * b) ^ (n - k)) =
      r ^ (m + n) * ∑ k ∈ Finset.range (min m n + 1),
        (m.choose k : ℂ) * n.choose k * k.factorial * a ^ (m - k) * b ^ (n - k) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ m ∧ k ≤ n := le_min_iff.mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hrk : (2 : ℂ) ^ k * r ^ (m - k) * r ^ (n - k) = r ^ (m + n) := by
    rw [← hr, ← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  rw [mul_pow, mul_pow]
  linear_combination (m.choose k : ℂ) * n.choose k * k.factorial *
    a ^ (m - k) * b ^ (n - k) * hrk

/-- The Hermite matrix-element prefactor reduces to the square root of the factorial ratio. -/
private theorem hermite_factorial_normalization (m n : ℕ) :
    (Real.sqrt Real.pi : ℂ) * n.factorial =
      (Real.sqrt (n.factorial / m.factorial) : ℂ) *
      (Real.sqrt ((m.factorial : ℝ) * Real.sqrt Real.pi) : ℂ) *
      (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) : ℂ) := by
  suffices h : Real.sqrt Real.pi * n.factorial = Real.sqrt (n.factorial / m.factorial) *
      Real.sqrt ((m.factorial : ℝ) * Real.sqrt Real.pi) *
      Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) by exact_mod_cast h
  rw [Real.sqrt_div (Nat.cast_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_mul (Nat.cast_nonneg _)]
  have hm : Real.sqrt (m.factorial : ℝ) ≠ 0 := by positivity
  have hn : Real.sqrt (n.factorial : ℝ) * Real.sqrt (n.factorial : ℝ) = n.factorial :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hp : Real.sqrt (Real.sqrt Real.pi) * Real.sqrt (Real.sqrt Real.pi) = Real.sqrt Real.pi :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  rw [show Real.sqrt (n.factorial : ℝ) / Real.sqrt (m.factorial : ℝ) *
      (Real.sqrt (m.factorial : ℝ) * Real.sqrt (Real.sqrt Real.pi)) *
      (Real.sqrt (n.factorial : ℝ) * Real.sqrt (Real.sqrt Real.pi)) =
      (Real.sqrt (n.factorial : ℝ) * Real.sqrt (n.factorial : ℝ)) *
      (Real.sqrt (Real.sqrt Real.pi) * Real.sqrt (Real.sqrt Real.pi)) by field_simp]
  rw [hn, hp, mul_comm]

/-- The Schrödinger matrix element as an integral of translated Hermite functions. -/
theorem matrixElement_schrodinger_integral (m n : ℕ) (g : TauCeti.HeisenbergGroup ℝ) :
    ContRepresentation.matrixElement schrodinger (TauCeti.hermiteHilbertBasis ℂ) m n g =
    ∫ t : ℝ, (TauCeti.hermiteFunction m t : ℂ) *
      (exp ((g.z + g.y * t : ℝ) * I) * (TauCeti.hermiteFunction n (t + g.x) : ℂ)) := by
  rw [ContRepresentation.matrixElement_def, TauCeti.coe_hermiteHilbertBasis, L2.inner_def]
  have hm := TauCeti.coeFn_hermiteFunctionLp (𝕜 := ℂ) m
  have hn := TauCeti.coeFn_hermiteFunctionLp (𝕜 := ℂ) n
  have hshift := (measurePreserving_add_right volume g.x).quasiMeasurePreserving.ae hn
  apply integral_congr_ae
  filter_upwards [hm, hshift, schrodinger_apply_ae g (TauCeti.hermiteFunctionLp ℂ n)]
    with t hmt hnt hg
  rw [RCLike.inner_apply, hg, hmt, hnt]
  change _ * conj (TauCeti.hermiteFunction m t : ℂ) = _
  rw [conj_ofReal, mul_comm, RCLike.algebraMap_eq_ofReal, RCLike.ofReal_eq_complex_ofReal]

/-- The Schrödinger matrix element in the Hermite basis has the Laguerre form. -/
theorem matrixElement_schrodinger_hermite (m n : ℕ) (g : TauCeti.HeisenbergGroup ℝ) :
    ContRepresentation.matrixElement schrodinger (TauCeti.hermiteHilbertBasis ℂ) m n g =
      hermiteMatrixElement m n g.x g.y g.z := by
  let r : ℂ := (Real.sqrt 2 : ℂ)
  let w : ℂ := g.x - g.y * I
  let a : ℂ := (-g.x + g.y * I) / r
  let b : ℂ := (g.x + g.y * I) / r
  let A : ℝ := (g.x ^ 2 + g.y ^ 2) / 2
  let weight (j : ℕ) : ℂ := (Real.sqrt ((j.factorial : ℝ) * Real.sqrt Real.pi) : ℂ)
  let denominator (j : ℕ) : ℂ :=
    ((2 : ℝ) ^ (j / 2 : ℝ) * Real.sqrt ((j.factorial : ℝ) * Real.sqrt Real.pi) : ℝ)
  let phase := exp ((g.z - g.x * g.y / 2 : ℝ) * I) * (Real.exp (-A / 2) : ℂ)
  have hr : r ≠ 0 := ofReal_ne_zero.mpr (by positivity : Real.sqrt 2 ≠ 0)
  have hr2 : r ^ 2 = 2 := by
    dsimp only [r]
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num), ofReal_ofNat]
  have hd (j : ℕ) : denominator j = r ^ j * weight j := by
    have hj : (Real.sqrt (2 : ℝ)) ^ j = (2 : ℝ) ^ (j / 2 : ℝ) := by
      rw [show Real.sqrt (2 : ℝ) = (2 : ℝ) ^ (1 / 2 : ℝ) from Real.sqrt_eq_rpow _,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    dsimp only [denominator, r, weight]
    rw [ofReal_mul, ← ofReal_pow, hj]
  have hw (j : ℕ) : weight j ≠ 0 :=
    ofReal_ne_zero.mpr (TauCeti.sqrt_factorial_mul_sqrt_pi_ne_zero j)
  have hId : (denominator m * denominator n) *
      ContRepresentation.matrixElement schrodinger (TauCeti.hermiteHilbertBasis ℂ) m n g =
      exp ((g.z : ℂ) * I - (g.x : ℂ) ^ 2 / 2) *
        ∫ t : ℝ, exp (-t * w) * (aeval (t : ℂ) (hermitePolynomialH m) : ℂ) *
          aeval ((t : ℂ) + g.x) (hermitePolynomialH n) * exp (-(t : ℂ) ^ 2) := by
    rw [matrixElement_schrodinger_integral, ← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    have hExp : exp ((g.z + g.y * t : ℝ) * I) * exp (-(t : ℂ) ^ 2 / 2) *
        exp (-((t + g.x : ℝ) : ℂ) ^ 2 / 2) =
        exp ((g.z : ℂ) * I - (g.x : ℂ) ^ 2 / 2) * exp (-t * w) * exp (-(t : ℂ) ^ 2) := by
      simp only [← exp_add, w]
      congr 1
      push_cast
      ring
    calc
      _ = exp ((g.z + g.y * t : ℝ) * I) *
          (denominator m * (TauCeti.hermiteFunction m t : ℂ)) *
          (denominator n * (TauCeti.hermiteFunction n (t + g.x) : ℂ)) := by ring
      _ = _ := by
        rw [← hermitePolynomialH_envelope m t, ← hermitePolynomialH_envelope n (t + g.x)]
        push_cast at hExp ⊢
        linear_combination (aeval (t : ℂ) (hermitePolynomialH m) : ℂ) *
          aeval ((t : ℂ) + g.x) (hermitePolynomialH n) * hExp
  have ha : -w = r * a := by dsimp only [w, a]; field_simp; ring
  have hb : 2 * (g.x : ℂ) - w = r * b := by dsimp only [w, b]; field_simp; ring
  have hph : exp ((g.z : ℂ) * I - (g.x : ℂ) ^ 2 / 2) * exp (w ^ 2 / 4) = phase := by
    dsimp only [phase, w, A]
    rw [ofReal_exp, ← exp_add, ← exp_add]
    congr 1
    push_cast
    linear_combination ((g.y : ℂ) ^ 2 / 4) * Complex.I_sq
  have habs : a * b = -(A : ℂ) := by
    have he : (-g.x + g.y * I : ℂ) * (g.x + g.y * I) = -((g.x : ℂ) ^ 2 + (g.y : ℂ) ^ 2) := by
      linear_combination (g.y : ℂ) ^ 2 * Complex.I_sq
    dsimp only [a, b, A]
    rw [div_mul_div_comm, ← sq, hr2, he]
    push_cast
    ring
  have hconj : b = -conj a := by
    dsimp only [a, b, r]
    simp only [map_div₀, map_add, map_neg, conj_ofReal, map_mul, conj_I]
    ring
  have hScaled : (weight m * weight n) *
      ContRepresentation.matrixElement schrodinger (TauCeti.hermiteHilbertBasis ℂ) m n g =
      phase * (Real.sqrt Real.pi : ℂ) *
        ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * k.factorial *
          a ^ (m - k) * b ^ (n - k) := by
    rw [integral_translate_hermitePolynomialH, ha, hb, scale_hermiteContraction _ _ _ _ _ hr2,
      hd, hd] at hId
    apply mul_left_cancel₀ (pow_ne_zero (m + n) hr)
    calc
      _ = (r ^ m * weight m * (r ^ n * weight n)) *
          ContRepresentation.matrixElement schrodinger (TauCeti.hermiteHilbertBasis ℂ) m n g := by
        rw [pow_add]; ring
      _ = _ := by
        rw [hId]
        linear_combination (r ^ (m + n) * Real.sqrt Real.pi *
          ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * k.factorial *
            a ^ (m - k) * b ^ (n - k)) * hph
  apply mul_left_cancel₀ (mul_ne_zero (hw m) (hw n))
  rw [hScaled]
  change _ = (weight m * weight n) * (phase * if n ≤ m then
      (Real.sqrt (n.factorial / m.factorial) : ℂ) * a ^ (m - n) *
          laguerreExtended ((m : ℂ) - n) n (A : ℂ)
      else (Real.sqrt (m.factorial / n.factorial) : ℂ) * (-conj a) ^ (n - m) *
          laguerreExtended ((n : ℂ) - m) m (A : ℂ))
  split_ifs with hn
  · rw [contraction_sum_eq_laguerre m n hn _ _ _ habs]
    have hNorm := hermite_factorial_normalization m n
    dsimp only [weight]
    linear_combination (phase * a ^ (m - n) * laguerreExtended ((m : ℂ) - n) n (A : ℂ)) * hNorm
  · have hs := contraction_sum_eq_laguerre n m (le_of_not_ge hn) b a A
        ((mul_comm b a).trans habs)
    have hSymm : (∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * k.factorial *
        a ^ (m - k) * b ^ (n - k)) =
        ∑ k ∈ Finset.range (min n m + 1), (n.choose k : ℂ) * m.choose k * k.factorial *
          b ^ (n - k) * a ^ (m - k) := by
      rw [min_comm m n]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hSymm, hs, hconj]
    have hNorm := hermite_factorial_normalization n m
    dsimp only [weight]
    linear_combination
      (phase * (-conj a) ^ (n - m) * laguerreExtended ((n : ℂ) - m) m (A : ℂ)) * hNorm

/-- Unitarity bounds the Laguerre factor of a Hermite matrix element at `A ≥ 0`. -/
theorem norm_laguerre_le (m n : ℕ) (hnm : n ≤ m) (A : ℝ) (hA : 0 ≤ A) :
    Real.sqrt (n.factorial / m.factorial) * A ^ (((m : ℝ) - n) / 2) * Real.exp (-A / 2) *
      ‖laguerreExtended ((m : ℂ) - n) n (A : ℂ)‖ ≤ 1 := by
  let g : TauCeti.HeisenbergGroup ℝ := ⟨-Real.sqrt (2 * A), 0, 0⟩
  let e := TauCeti.hermiteHilbertBasis ℂ
  have hmo : ‖e m‖ = 1 := e.orthonormal.norm_eq_one m
  have hno : ‖e n‖ = 1 := e.orthonormal.norm_eq_one n
  have hnorm : ‖schrodinger.matrixElement e m n g‖ ≤ 1 := by
    rw [ContRepresentation.matrixElement_def]
    simpa only [isUnitary_schrodinger.norm_map, hmo, hno, mul_one] using
      (norm_inner_le_norm (𝕜 := ℂ) (e m) (schrodinger g (e n)))
  change ‖schrodinger.matrixElement (TauCeti.hermiteHilbertBasis ℂ) m n g‖ ≤ 1 at hnorm
  rw [matrixElement_schrodinger_hermite] at hnorm
  have hA' : (g.x ^ 2 + g.y ^ 2) / 2 = A := by
    dsimp only [g]
    rw [neg_sq, Real.sq_sqrt (by positivity)]
    ring
  have hArg : (-(g.x : ℂ) + g.y * I) / (Real.sqrt 2 : ℂ) = (Real.sqrt A : ℂ) := by
    dsimp only [g]
    simp only [ofReal_neg, neg_neg, ofReal_zero, zero_mul, add_zero, ← ofReal_div]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact congrArg (fun t : ℝ => (t : ℂ)) (by field_simp)
  have hg : g.z - g.x * g.y / 2 = 0 := by simp [g]
  have hPow : Real.sqrt A ^ (m - n) = A ^ (((m : ℝ) - n) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hA, Nat.cast_sub hnm]
    congr 1
    ring
  rw [hermiteMatrixElement, ite_eq_left hnm, hArg, hA', hg] at hnorm
  simp only [ofReal_zero, zero_mul, exp_zero, one_mul, norm_mul, norm_real, norm_pow,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos (Real.exp_pos _), hPow]
    at hnorm
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hnorm

/-- The Hermite matrix element of a product sums over the intermediate Hermite degrees. -/
theorem hasSum_hermiteMatrixElement_mul (m n : ℕ) (g h : TauCeti.HeisenbergGroup ℝ) :
    HasSum (fun k => hermiteMatrixElement m k g.x g.y g.z * hermiteMatrixElement k n h.x h.y h.z)
      (hermiteMatrixElement m n (g * h).x (g * h).y (g * h).z) := by
  simpa only [matrixElement_schrodinger_hermite] using
    (schrodinger.hasSum_matrixElement_mul (TauCeti.hermiteHilbertBasis ℂ) m n g h)

/-- The pointwise product of a Hermite function and a translated Hermite function as a Schwartz
function. -/
private def hermiteProductSchwartz (m n : ℕ) (x : ℝ) : 𝓢(ℝ, ℂ) :=
  let shifted : 𝓢(ℝ, ℝ) := SchwartzMap.compCLMOfAntilipschitz ℝ
    (Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const x))
    (show AntilipschitzWith 1 (fun t : ℝ => t + x) from by
      intro t u
      simp only [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq,
        add_sub_add_right_eq_sub, le_refl])
    (TauCeti.hermiteSchwartzMap n)
  SchwartzMap.postcompCLM Complex.ofRealCLM
    (SchwartzMap.smulLeftCLM ℝ (TauCeti.hermiteFunction m) shifted)

/-- The translated Hermite product evaluates to the ordinary product of the two real Hermite
functions. -/
private theorem hermiteProductSchwartz_apply (m n : ℕ) (x t : ℝ) :
    hermiteProductSchwartz m n x t =
      ((TauCeti.hermiteFunction m t * TauCeti.hermiteFunction n (t + x) : ℝ) : ℂ) := by
  have hm : (TauCeti.hermiteFunction m).HasTemperateGrowth := by
    simpa only [TauCeti.coe_hermiteSchwartzMap] using
      (TauCeti.hermiteSchwartzMap m).hasTemperateGrowth
  simp only [hermiteProductSchwartz, SchwartzMap.postcompCLM_apply, Complex.ofRealCLM_apply,
    SchwartzMap.smulLeftCLM_apply hm, SchwartzMap.compCLMOfAntilipschitz_apply,
    Function.comp_apply, smul_eq_mul, TauCeti.hermiteSchwartzMap_apply, Pi.add_apply]

/-- The Hermite matrix element at zero central coordinate is the Fourier transform of a translated
Hermite product, at the rescaled frequency. -/
private theorem hermiteMatrixElement_eq_fourier (m n : ℕ) (x y : ℝ) :
    hermiteMatrixElement m n x y 0 = 𝓕 (hermiteProductSchwartz m n x) (-(2 * π)⁻¹ * y) := by
  let g : TauCeti.HeisenbergGroup ℝ := ⟨x, y, 0⟩
  change hermiteMatrixElement m n g.x g.y g.z = _
  rw [← matrixElement_schrodinger_hermite, matrixElement_schrodinger_integral,
    SchwartzMap.fourier_coe, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [g, zero_add, Circle.smul_def, Real.fourierChar_apply, Real.inner_apply,
    hermiteProductSchwartz_apply, ofReal_mul, smul_eq_mul]
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  have hExp : 2 * π * -(t * (-(2 * π)⁻¹ * y)) = y * t := by field_simp
  have hArg : (2 : ℂ) * π * ((-(t * (-(2 * π)⁻¹ * y)) : ℝ) : ℂ) =
      (y : ℂ) * t := by exact_mod_cast hExp
  simp only [ofReal_ofNat, hArg]
  ring

/-- The Hermite matrix element at zero central coordinate is jointly continuous in displacement and
frequency. -/
private theorem continuous_hermiteMatrixElement_plane (m n : ℕ) :
    Continuous (fun p : ℝ × ℝ => hermiteMatrixElement m n p.1 p.2 0) := by
  unfold hermiteMatrixElement
  split_ifs <;> simp only [DLMF.OrthogonalPolynomials.laguerreExtended, div_eq_mul_inv] <;> fun_prop

/-- The product of two normalized Hermite functions is integrable on the real line. -/
private theorem hermitePair_integrable (m n : ℕ) :
    Integrable (fun t : ℝ => (TauCeti.hermiteFunction m t : ℂ) *
      (TauCeti.hermiteFunction n t : ℂ)) :=
  (TauCeti.memLp_two_algebraMap_hermiteFunction (𝕜 := ℂ) m).integrable_mul
    (TauCeti.memLp_two_algebraMap_hermiteFunction (𝕜 := ℂ) n)

/-- The product of an integrable function in one coordinate and another evaluated at the sum of the
two coordinates is integrable on the plane. -/
private theorem integrable_translationPair {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfi : Integrable f) (hgi : Integrable g) :
    Integrable (fun p : ℝ × ℝ => f p.2 * g (p.2 + p.1)) ((volume : Measure ℝ).prod volume) := by
  apply (integrable_prod_iff'
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (by fun_prop : Continuous (fun p : ℝ × ℝ => f p.2 * g (p.2 + p.1))).aestronglyMeasurable).2
  have ht (t : ℝ) := (measurePreserving_add_left volume t)
  refine ⟨Filter.Eventually.of_forall (fun t => ?_), ?_⟩
  · exact ((ht t).integrable_comp_of_integrable hgi).const_mul (f t)
  refine (hfi.norm.mul_const (∫ u, ‖g u‖)).congr (Filter.Eventually.of_forall fun t => ?_)
  change ‖f t‖ * (∫ u, ‖g u‖) = ∫ u, ‖f t * g (t + u)‖
  simp_rw [norm_mul]
  rw [integral_const_mul]
  have h := (ht t).integral_comp (MeasurableEquiv.addLeft t).measurableEmbedding (fun u => ‖g u‖)
  rw [h]

/-- The matrix elements on the central section are square integrable. -/
theorem memLp_hermiteMatrixElement (m n : ℕ) :
    MemLp (fun p : ℝ × ℝ => hermiteMatrixElement m n p.1 p.2 0) 2 volume := by
  let s : ℝ := -(2 * π)⁻¹
  have hs : s ≠ 0 := by exact neg_ne_zero.mpr (inv_ne_zero (by positivity))
  have hAbs : |s⁻¹| = 2 * π := by
    simp only [s, inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity : 0 < 2 * π)]
  have hCont := continuous_hermiteMatrixElement_plane m n
  apply (memLp_two_iff_integrable_sq_norm hCont.aestronglyMeasurable).2
  refine (integrable_prod_iff (by fun_prop : Continuous
    (fun p : ℝ × ℝ => ‖hermiteMatrixElement m n p.1 p.2 0‖ ^ 2)).aestronglyMeasurable).2 ?_
  have hIntSchwartz (x : ℝ) : Integrable
      (fun y => ‖(𝓕 (hermiteProductSchwartz m n x) : 𝓢(ℝ, ℂ)) y‖ ^ 2) := by
    have h := (𝓕 (hermiteProductSchwartz m n x) : 𝓢(ℝ, ℂ)).memLp 2 (volume : Measure ℝ)
    exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h
  refine ⟨Filter.Eventually.of_forall (fun x => ?_), ?_⟩
  · simp_rw [hermiteMatrixElement_eq_fourier]
    exact (integrable_comp_mul_left_iff _ hs).2 (hIntSchwartz x)
  let f (k : ℕ) (t : ℝ) : ℂ := ((TauCeti.hermiteFunction k t ^ 2 : ℝ) : ℂ)
  have hf (k : ℕ) : Integrable (f k) := by
    simpa only [f, sq, Complex.ofReal_mul] using hermitePair_integrable k k
  have hfc (k : ℕ) : Continuous (f k) :=
    Complex.continuous_ofReal.comp ((TauCeti.continuous_hermiteFunction k).pow 2)
  have hShift := integrable_translationPair (hfc m) (hfc n) (hf m) (hf n)
  refine (hShift.norm.integral_prod_left.const_mul (2 * π)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  let F (y : ℝ) := ‖(𝓕 (hermiteProductSchwartz m n x) : 𝓢(ℝ, ℂ)) y‖ ^ 2
  have hnonneg (y : ℝ) : 0 ≤ F y := sq_nonneg _
  simp only [Real.norm_eq_abs, hermiteMatrixElement_eq_fourier]
  change 2 * π * (∫ t, ‖f m t * f n (t + x)‖) = ∫ y, |F (s * y)|
  simp_rw [abs_of_nonneg (hnonneg _)]
  rw [Measure.integral_comp_mul_left F s, hAbs, smul_eq_mul]
  dsimp only [F]
  rw [SchwartzMap.integral_norm_sq_fourier]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [hermiteProductSchwartz_apply, f, norm_real, norm_mul, Real.norm_eq_abs,
    abs_sq, mul_pow, sq_abs]

/-- The integral of the product of normalized Hermite functions is the Kronecker delta. -/
private theorem integral_hermitePair (m n : ℕ) :
    (∫ t : ℝ, (TauCeti.hermiteFunction m t : ℂ) * (TauCeti.hermiteFunction n t : ℂ)) =
      if m = n then 1 else 0 := by
  simp only [← Complex.ofReal_mul, integral_complex_ofReal,
    TauCeti.integral_hermiteFunction_mul_hermiteFunction]
  split_ifs <;> simp

/-- The normalized Hermite matrix elements are orthogonal in the translation and modulation
coordinates. -/
theorem integral_hermiteMatrixElement (m n m' n' : ℕ) :
    ∫ p : ℝ × ℝ, hermiteMatrixElement m n p.1 p.2 0 * conj (hermiteMatrixElement m' n' p.1 p.2 0) =
      if m = m' ∧ n = n' then (2 * π : ℂ) else 0 := by
  let s : ℝ := -(2 * π)⁻¹
  have hAbs : |s⁻¹| = 2 * π := by
    simp only [s, inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity : 0 < 2 * π)]
  let H (p : ℝ × ℝ) := hermiteMatrixElement m n p.1 p.2 0 *
    conj (hermiteMatrixElement m' n' p.1 p.2 0)
  have hSet : Integrable H ((volume : Measure ℝ).prod volume) :=
    (memLp_hermiteMatrixElement m n).integrable_mul ((memLp_hermiteMatrixElement m' n').star)
  change (∫ p, H p ∂(volume : Measure ℝ).prod volume) = _
  rw [integral_prod _ hSet]
  dsimp only [H]
  have hon (x : ℝ) :
      (∫ y : ℝ, hermiteMatrixElement m n x y 0 * conj (hermiteMatrixElement m' n' x y 0)) =
      (2 * π : ℂ) * ∫ t : ℝ, hermiteProductSchwartz m n x t *
        conj (hermiteProductSchwartz m' n' x t) := by
    let F (y : ℝ) := (𝓕 (hermiteProductSchwartz m n x)) y *
      conj ((𝓕 (hermiteProductSchwartz m' n' x)) y)
    simp_rw [hermiteMatrixElement_eq_fourier]
    change (∫ y, F (s * y)) = _
    rw [Measure.integral_comp_mul_left F s, hAbs, Complex.real_smul]
    push_cast
    congr 1
    simpa only [F, RCLike.inner_apply] using
      SchwartzMap.integral_inner_fourier_fourier
        (hermiteProductSchwartz m' n' x) (hermiteProductSchwartz m n x)
  simp_rw [hon, hermiteProductSchwartz_apply, conj_ofReal, ofReal_mul]
  let f (i j : ℕ) (t : ℝ) : ℂ :=
    (TauCeti.hermiteFunction i t : ℂ) * TauCeti.hermiteFunction j t
  have hfc (i j : ℕ) : Continuous (f i j) :=
    (Complex.continuous_ofReal.comp (TauCeti.continuous_hermiteFunction i)).mul
      (Complex.continuous_ofReal.comp (TauCeti.continuous_hermiteFunction j))
  have hShift := integrable_translationPair (hfc m m') (hfc n n')
    (hermitePair_integrable m m') (hermitePair_integrable n n')
  rw [integral_const_mul]
  have hReorder (x t : ℝ) : (TauCeti.hermiteFunction m t : ℂ) *
      (TauCeti.hermiteFunction n (t + x) : ℂ) *
      ((TauCeti.hermiteFunction m' t : ℂ) * (TauCeti.hermiteFunction n' (t + x) : ℂ)) =
      f m m' t * f n n' (t + x) := by dsimp only [f]; ring
  simp_rw [hReorder]
  rw [integral_integral_swap hShift]
  have hPeriod (t : ℝ) : (∫ x, f m m' t * f n n' (t + x)) =
      f m m' t * ∫ u, f n n' u := by
    rw [integral_const_mul]
    congr 1
    exact (measurePreserving_add_left volume t).integral_comp
      (MeasurableEquiv.addLeft t).measurableEmbedding _
  simp_rw [hPeriod]
  rw [integral_mul_const]
  dsimp only [f]
  rw [integral_hermitePair, integral_hermitePair]
  by_cases hm : m = m' <;> by_cases hn : n = n' <;> simp [hm, hn]

/-- The normalized Hermite matrix elements form a Hilbert basis on the translation-modulation
plane. -/
theorem hermiteMatrixElement_hilbertBasis :
    ∃ b : HilbertBasis (ℕ × ℕ) ℂ (Lp ℂ 2 (volume : Measure (ℝ × ℝ))),
      ∀ i, (b i : ℝ × ℝ → ℂ) =ᵐ[volume]
        fun p => ((2 * π) ^ (-(1 / 2 : ℝ)) : ℝ) * hermiteMatrixElement i.1 i.2 p.1 p.2 0 := by
  sorry

end SFVK.AffineHeisenberg
