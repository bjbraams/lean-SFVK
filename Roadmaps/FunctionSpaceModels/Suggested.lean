/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Roadmaps.FunctionSpaceModels.Coordinates
public import TauCeti.RepresentationTheory.Continuous.MatrixCoefficient
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import TauCeti.RepresentationTheory.Continuous.Unitary.PositiveDefinite
public import TauCeti.RepresentationTheory.Continuous.LeftRegular.Basic
public import TauCeti.RepresentationTheory.Continuous.OneParameter

/-!
# Function-space models of noncompact groups: target signatures

This file and `Roadmaps.FunctionSpaceModels.Coordinates` state, against Mathlib and Tau Ceti,
the headlines of `README.md` that
carry a Lean name, each with every conclusion the README attaches to it. It is not an exhaustive
acceptance test: the other headlines of the README are targets of the same standing, stated in
prose. Discharging this file finishes neither a layer nor the roadmap.

Bold headlines of the README that are not stated here, and what each lacks:
* the irreducibility and inequivalence of the sphere models (README 2.6) need the sphere
  `S^{n-1}` as an `M(n)`-space with its surface measure as a carrier of `multiplierRep`; the
  representation law and unitarity of the sphere model are stated pointwise
  (`motionAction_mul`, `lintegral_motionAction`).

Prose bullets of the README that name objects owned elsewhere are not stated either. The
irreducibility, equivalences, invariant forms, Hilbert completions, `K`-types and Casimir values of
the `SU(1,1)` series are NoncompactQuantumSymmetry M4's; this file states only the concrete models
and the dictionaries to M4 (`sl2rToSU11_spec`, `principalAction_compactPicture`,
`complementaryWeight_ratio`, `discreteAction_rot`). The irreducibility of the Schrödinger
representation is NoncompactQuantumSymmetry M2's; this file states the Fourier dictionary
(`fourier_schrodinger`). The derived action of a general strongly continuous representation
(README 4.1) is owned by SmoothBanachRepresentations and AutomorphicFormsOnReductiveGroups §2.7.

The definitions are stated with real bodies. Representations on `L²` are chosen by uniqueness:
`multiplierRep μ α` and `principalSeries τ e` are the continuous representations whose operators
agree almost everywhere with the pointwise formulas when one exists, and the trivial
representation otherwise; the `_spec` theorems say that one exists. Section numbers in docstrings
are those of the README.
-/

@[expose] public section

noncomputable section

universe u

namespace SFVK.FunctionSpaceModels

open MeasureTheory Filter Topology Set Matrix AddCircle
open scoped Real ComplexConjugate ComplexOrder ENNReal NNReal InnerProductSpace ContDiff

/-! ## Layer 1: G-spaces, quasi-invariant measures and multipliers -/

section Multipliers

variable {G X : Type*} [Group G] [MulAction G X]

/-- README 1.1. `μ` is quasi-invariant with Radon–Nikodym density `ρ`:
`(g • ·)_* μ = ρ g · μ` for every `g`. -/
def IsQuasiInvariantWith [MeasurableSpace X] (μ : Measure X) (ρ : G → X → ℝ≥0∞) : Prop :=
  ∀ g : G, Measure.map (fun x => g • x) μ = μ.withDensity (ρ g)

/-- README 1.2. The multiplier action `(T(g) f)(x) = α(g, x) f(g⁻¹ • x)` on functions. -/
def multiplierAction (α : G → X → ℂ) (g : G) (f : X → ℂ) (x : X) : ℂ :=
  α g x * f (g⁻¹ • x)

/-- README 1.2. The multiplier cocycle identity `α(gh, x) = α(g, x) α(h, g⁻¹ • x)`,
`α(1, x) = 1`. -/
def IsMultiplierCocycle (α : G → X → ℂ) : Prop :=
  (∀ x, α 1 x = 1) ∧ ∀ g h x, α (g * h) x = α g x * α h (g⁻¹ • x)

open scoped Classical in
/-- README 1.3. The multiplier representation on `L²(X, μ)`: the continuous representation
whose operators agree almost everywhere with `multiplierAction α`, when one exists. -/
def multiplierRep [MeasurableSpace X] (μ : Measure X) (α : G → X → ℂ) :
    ContRepresentation ℂ G (Lp ℂ 2 μ) :=
  if h : ∃ U : ContRepresentation ℂ G (Lp ℂ 2 μ),
      ∀ g f, (U g f : X → ℂ) =ᵐ[μ] multiplierAction α g f then h.choose
  else .ofMonoidHom 1

/-- README 1.2. **Representation law.** `multiplierAction α` is an action on functions exactly
when `α` is a multiplier cocycle. -/
theorem multiplierAction_law_iff (α : G → X → ℂ) :
    ((∀ f x, multiplierAction α 1 f x = f x) ∧
      ∀ g h f x, multiplierAction α (g * h) f x =
        multiplierAction α g (multiplierAction α h f) x) ↔ IsMultiplierCocycle α := by
  sorry

/-- README 1.1. **Radon–Nikodym cocycle.** The densities of a quasi-invariant σ-finite measure
satisfy `ρ(gh, x) = ρ(g, x) ρ(h, g⁻¹ • x)` almost everywhere. -/
theorem IsQuasiInvariantWith.cocycle [MeasurableSpace X] [MeasurableConstSMul G X]
    {μ : Measure X} [SigmaFinite μ] {ρ : G → X → ℝ≥0∞} (hρm : ∀ g, Measurable (ρ g))
    (hρ : IsQuasiInvariantWith μ ρ) (g h : G) :
    ∀ᵐ x ∂μ, ρ (g * h) x = ρ g x * ρ h (g⁻¹ • x) := by
  sorry

/-- README 1.3. **Unitarity criterion.** A unitary representation realizing `multiplierAction α`
on `L²(μ)` exists exactly when `|α(g, x)|² = ρ(g, x)` almost everywhere. -/
theorem exists_isUnitary_multiplierAction_iff [MeasurableSpace X] [MeasurableConstSMul G X]
    {μ : Measure X} [SigmaFinite μ] {ρ : G → X → ℝ≥0∞} {α : G → X → ℂ}
    (hα : IsMultiplierCocycle α) (hαm : ∀ g, Measurable (α g)) (hρm : ∀ g, Measurable (ρ g))
    (hρ : IsQuasiInvariantWith μ ρ) :
    (∃ U : ContRepresentation ℂ G (Lp ℂ 2 μ),
        U.IsUnitary ∧ ∀ g f, (U g f : X → ℂ) =ᵐ[μ] multiplierAction α g f) ↔
      ∀ g, ∀ᵐ x ∂μ, ‖α g x‖ₑ ^ 2 = ρ g x := by
  sorry

/-- README 1.3. **The multiplier representation.** Under the unitarity condition,
`multiplierRep μ α` realizes `multiplierAction α` and is unitary. -/
theorem multiplierRep_spec [MeasurableSpace X] [MeasurableConstSMul G X]
    {μ : Measure X} [SigmaFinite μ] {ρ : G → X → ℝ≥0∞} {α : G → X → ℂ}
    (hα : IsMultiplierCocycle α) (hαm : ∀ g, Measurable (α g)) (hρm : ∀ g, Measurable (ρ g))
    (hρ : IsQuasiInvariantWith μ ρ) (hu : ∀ g, ∀ᵐ x ∂μ, ‖α g x‖ₑ ^ 2 = ρ g x) :
    (∀ g f, (multiplierRep μ α g f : X → ℂ) =ᵐ[μ] multiplierAction α g f) ∧
      (multiplierRep μ α).IsUnitary := by
  sorry

/-- README 1.3. **Strong continuity.** For a continuous action of a locally compact group on a
locally compact space with a regular measure and a jointly continuous multiplier, the unitary
multiplier representation has continuous orbit maps. -/
theorem continuous_multiplierRep_apply [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [ContinuousSMul G X]
    {μ : Measure X} [μ.Regular] [SigmaFinite μ] {ρ : G → X → ℝ≥0∞} {α : G → X → ℂ}
    (hα : IsMultiplierCocycle α) (hαc : Continuous fun p : G × X => α p.1 p.2)
    (hρm : ∀ g, Measurable (ρ g)) (hρ : IsQuasiInvariantWith μ ρ)
    (hu : ∀ g, ∀ᵐ x ∂μ, ‖α g x‖ₑ ^ 2 = ρ g x) (f : Lp ℂ 2 μ) :
    Continuous fun g => multiplierRep μ α g f := by
  sorry

/-- README 1.4. The cocycle `β(x) α(g, x) / β(g⁻¹ • x)` cohomologous to `α`. -/
def coboundaryTwist (β : X → ℂ) (α : G → X → ℂ) (g : G) (x : X) : ℂ :=
  β x * α g x / β (g⁻¹ • x)

/-- README 1.4. **Cohomologous multipliers.** Multiplication by a nowhere-vanishing `β`
intertwines `α` with its twist; the twist is a cocycle when `α` is, and has the same modulus
when `|β| = 1`. -/
theorem multiplierAction_coboundaryTwist (β : X → ℂ) (hβ : ∀ x, β x ≠ 0) (α : G → X → ℂ) :
    (∀ g f x, β x * multiplierAction α g f x =
      multiplierAction (coboundaryTwist β α) g (fun y => β y * f y) x) ∧
    (IsMultiplierCocycle α → IsMultiplierCocycle (coboundaryTwist β α)) ∧
    ((∀ x, ‖β x‖ = 1) → ∀ g x, ‖coboundaryTwist β α g x‖ = ‖α g x‖) := by
  sorry

/-- README 1.3. **Quasi-regular representation.** The square root of a Radon–Nikodym cocycle is
a multiplier cocycle of modulus squared `ρ`. -/
theorem isMultiplierCocycle_sqrt (ρ : G → X → ℝ≥0) (h₁ : ∀ x, ρ 1 x = 1)
    (hmul : ∀ g h x, ρ (g * h) x = ρ g x * ρ h (g⁻¹ • x)) :
    IsMultiplierCocycle (fun g x => ((NNReal.sqrt (ρ g x) : ℝ) : ℂ)) ∧
      ∀ g x, ‖((NNReal.sqrt (ρ g x) : ℝ) : ℂ)‖ ^ 2 = ρ g x := by
  sorry

end Multipliers

/-- README 1.3. **Left regular representation.** For a left-invariant measure on `G` acting on
itself, the multiplier representation with `α = 1` is Tau Ceti's left regular representation. -/
theorem multiplierRep_one_eq_leftRegular {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] :
    multiplierRep μ (fun (_ : G) (_ : G) => (1 : ℂ)) = μ.leftRegular ℂ ℂ 2 := by
  sorry

/-! ## Layer 2: function-space models -/

/-- The circle `ℝ / 2πℤ`. -/
instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The circle `ℝ / 2πℤ` carrying the angle `θ`. -/
local notation "𝕋" => AddCircle (2 * π)

/-- The point `e^{iθ}` of the unit circle. -/
def expCircle (θ : 𝕋) : ℂ := fourier 1 θ

/-- README 2.1. The right action `e^{iθ} ↦ (a e^{iθ} + conj b) / (b e^{iθ} + conj a)` of
`SU(1,1)` on the circle, written on angles. -/
def circleAct (g : SU11) (θ : 𝕋) : 𝕋 :=
  ((Complex.arg ((entryA g * expCircle θ + conj (entryB g)) /
    (entryB g * expCircle θ + conj (entryA g))) : ℝ) : 𝕋)

/-- README 2.1. The principal-series multiplier `|u|^{2τ} (u / |u|)^{2ε}`,
`u = b e^{iθ} + conj a`, with `2ε = e ∈ {0, 1}`. -/
def principalMultiplier (τ : ℂ) (e : Fin 2) (g : SU11) (θ : 𝕋) : ℂ :=
  let u := entryB g * expCircle θ + conj (entryA g)
  ((‖u‖ : ℂ) ^ (2 * τ)) * (u / (‖u‖ : ℂ)) ^ (e : ℕ)

/-- README 2.1. The principal-series action on functions on the circle. -/
def principalAction (τ : ℂ) (e : Fin 2) (g : SU11) (f : 𝕋 → ℂ) (θ : 𝕋) : ℂ :=
  principalMultiplier τ e g θ * f (circleAct g θ)

open scoped Classical in
/-- README 2.1. The principal series `T_{(τ, e/2)}` of `SU(1,1)` on `L²(𝕋)`: the continuous
representation realizing `principalAction τ e` almost everywhere. -/
def principalSeries (τ : ℂ) (e : Fin 2) :
    ContRepresentation ℂ SU11 (Lp ℂ 2 (haarAddCircle (T := 2 * π))) :=
  if h : ∃ U : ContRepresentation ℂ SU11 (Lp ℂ 2 (haarAddCircle (T := 2 * π))),
      ∀ g f, (U g f : 𝕋 → ℂ) =ᵐ[haarAddCircle] principalAction τ e g f then h.choose
  else .ofMonoidHom 1

/-- README 2.1. **The circle as an `SU(1,1)`-space.** `circleAct` is a right action, and the
image of the Haar probability measure under `circleAct g` has the Poisson density
`|a - b e^{iθ}|⁻²`. -/
theorem circleAct_mul_map (g h : SU11) :
    (∀ θ, circleAct (g * h) θ = circleAct h (circleAct g θ)) ∧ (∀ θ, circleAct 1 θ = θ) ∧
    Measure.map (circleAct g) (haarAddCircle (T := 2 * π)) =
      (haarAddCircle (T := 2 * π)).withDensity
        fun θ => ENNReal.ofReal (‖entryA g - entryB g * expCircle θ‖ ^ 2)⁻¹ := by
  sorry

/-- README 2.1. **Principal series: representation law.** -/
theorem principalAction_mul (τ : ℂ) (e : Fin 2) (g h : SU11) (f : 𝕋 → ℂ) :
    principalAction τ e (g * h) f = principalAction τ e g (principalAction τ e h f) ∧
      principalAction τ e 1 f = f := by
  sorry

/-- README 2.1. **Principal series on `L²`.** For every `τ` the formula defines a strongly
continuous representation on `L²(𝕋)`. -/
theorem principalSeries_spec (τ : ℂ) (e : Fin 2) :
    (∀ g f, (principalSeries τ e g f : 𝕋 → ℂ) =ᵐ[haarAddCircle] principalAction τ e g f) ∧
      ∀ f, Continuous fun g => principalSeries τ e g f := by
  sorry

/-- README 2.1. **Unitarity of the principal series.** `T_{(τ, e/2)}` is unitary on `L²(𝕋)`
exactly on the line `Re τ = -1/2`. -/
theorem principalSeries_isUnitary_iff (τ : ℂ) (e : Fin 2) :
    (principalSeries τ e).IsUnitary ↔ τ.re = -1 / 2 := by
  sorry

/-- README 2.1. **Hermitian adjoint.** `T_{(τ, ε)}(g)* = T_{(-conj τ - 1, ε)}(g⁻¹)`. -/
theorem inner_principalSeries (τ : ℂ) (e : Fin 2) (g : SU11)
    (f h : Lp ℂ 2 (haarAddCircle (T := 2 * π))) :
    ⟪principalSeries τ e g f, h⟫_ℂ = ⟪f, principalSeries (-conj τ - 1) e g⁻¹ h⟫_ℂ := by
  sorry

/-- README 2.1. **Weights.** `e_m = e^{inθ}`, `m = n - ε`, satisfies `T(k_α) e_m = e^{imα} e_m`,
and `k_{2π} = -1` acts by `(-1)^{2ε}`. -/
theorem principalSeries_rot (τ : ℂ) (e : Fin 2) (n : ℤ) (α : ℝ) :
    principalSeries τ e (rot α) (fourierLp (T := 2 * π) 2 n) =
      Complex.exp (((n : ℂ) - (e : ℂ) / 2) * α * Complex.I) •
        fourierLp (T := 2 * π) 2 n ∧
    (rot (2 * π)).1.1 = -1 ∧
    principalSeries τ e (rot (2 * π)) =
      ((-1 : ℂ) ^ (e : ℕ)) • ContinuousLinearMap.id ℂ (Lp ℂ 2 (haarAddCircle (T := 2 * π))) := by
  sorry

/-- README 2.1. The rotation `k_t = [[cos t, -sin t], [sin t, cos t]]` of `SL(2, ℝ)`. -/
def rotR (t : ℝ) : SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![Real.cos t, -Real.sin t; Real.sin t, Real.cos t], by
    rw [Matrix.det_fin_two_of]
    linear_combination Real.cos_sq_add_sin_sq t⟩

/-- README 2.1. Conjugation `h ↦ C₀ h C₀⁻¹` by `C₀ = ((1 + i)/2) [[1, i], [1, -i]]`, the fixed
conjugacy of NoncompactQuantumSymmetry M4: `[[p, q], [r, s]]` goes to
`a = (p + s)/2 - i (q - r)/2`, `b = (p - s)/2 + i (q + r)/2`. -/
def sl2rToSU11 (h : SpecialLinearGroup (Fin 2) ℝ) : SU11 :=
  su11Mk ⟨(h.1 0 0 + h.1 1 1) / 2, -(h.1 0 1 - h.1 1 0) / 2⟩
    ⟨(h.1 0 0 - h.1 1 1) / 2, (h.1 0 1 + h.1 1 0) / 2⟩ (by
      have h2 := h.2
      rw [Matrix.det_fin_two] at h2
      simp only [Complex.normSq_mk]
      linear_combination h2)

/-- README 2.1. **The fixed conjugacy `SL(2, ℝ) ≅ SU(1,1)`.** `sl2rToSU11` is a bijective
homomorphism given by conjugation with `C₀`, and it maps `k_t` to `k_{2t}`. -/
theorem sl2rToSU11_spec :
    let C₀ : Matrix (Fin 2) (Fin 2) ℂ := ((1 + Complex.I) / 2) • !![1, Complex.I; 1, -Complex.I]
    (∀ h h', sl2rToSU11 (h * h') = sl2rToSU11 h * sl2rToSU11 h') ∧
    (∀ h, (sl2rToSU11 h).1.1 = C₀ * h.1.map (↑) * C₀⁻¹) ∧
    (∀ t, sl2rToSU11 (rotR t) = rot (2 * t)) ∧ Function.Bijective sl2rToSU11 := by
  sorry

/-- README 2.1. The transport `(W F)(k_t) = e^{i e t} F(π - 2t)` of a function on the circle to a
function on `SO(2)`. -/
def compactTransport (e : Fin 2) (F : 𝕋 → ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((e : ℂ) * t * Complex.I) * F ((π - 2 * t : ℝ) : 𝕋)

/-- README 2.1. **Agreement with normalized parabolic induction.** Under `W` and `sl2rToSU11`,
`T_{(τ, e/2)}` is the compact picture `f ↦ r(h⁻¹ k_t)^{-(1 + ν)} f(θ(h⁻¹ k_t))` with
`ν = -(2τ + 1)`, where `h⁻¹ k_t` has first column `r (cos θ, sin θ)`; and `W F` has parity `e`. -/
theorem principalAction_compactPicture (τ : ℂ) (e : Fin 2) (h : SpecialLinearGroup (Fin 2) ℝ)
    (F : 𝕋 → ℂ) :
    (∀ t : ℝ,
      let x := (h⁻¹ * rotR t).1
      compactTransport e (principalAction τ e (sl2rToSU11 h) F) t =
        ((√(x 0 0 ^ 2 + x 1 0 ^ 2) : ℝ) : ℂ) ^ (2 * τ) *
          compactTransport e F (Complex.arg ⟨x 0 0, x 1 0⟩)) ∧
    ∀ t : ℝ, compactTransport e F (t + π) = (-1) ^ (e : ℕ) * compactTransport e F t := by
  sorry

/-- README 2.2. The complementary-series weight `Γ(τ - n + 1) / Γ(-τ - n)`. -/
def complementaryWeight (τ : ℝ) (n : ℤ) : ℝ :=
  Real.Gamma (τ - n + 1) / Real.Gamma (-τ - n)

/-- README 2.2. **Complementary weights.** For `-1 < τ < 0` the weights are positive and even
in `n`; at `τ = -1/2` they are all `1`. -/
theorem complementaryWeight_pos (τ : ℝ) (hτ : τ ∈ Ioo (-1) 0) (n : ℤ) :
    0 < complementaryWeight τ n ∧ complementaryWeight τ (-n) = complementaryWeight τ n ∧
      complementaryWeight (-1 / 2) n = 1 := by
  sorry

/-- README 2.2. **Agreement with the compact eigenforms of NoncompactQuantumSymmetry M5.** With
`ν = -(2τ + 1)`, `w(j) / w(0) = ∏_{k=1}^{j} (2k - 1 - ν) / (2k - 1 + ν)`. -/
theorem complementaryWeight_ratio (τ : ℝ) (hτ : τ ∈ Ioo (-1) 0) (j : ℕ) :
    let ν := -(2 * τ + 1)
    complementaryWeight τ j / complementaryWeight τ 0 =
      ∏ k ∈ Finset.Icc 1 j, (2 * (k : ℝ) - 1 - ν) / (2 * (k : ℝ) - 1 + ν) := by
  sorry

/-- README 2.3. The weighted Bergman probability measure `((k-1)/π) (1 - |z|²)^{k-2} dA` on
the unit disc. -/
def bergmanMeasure (k : ℕ) : Measure ℂ :=
  (volume.restrict (Metric.ball (0 : ℂ) 1)).withDensity
    fun z => ENNReal.ofReal (((k : ℝ) - 1) / π * (1 - ‖z‖ ^ 2) ^ (k - 2))

/-- README 2.3. The right action `z ↦ (a z + conj b) / (b z + conj a)` on the disc. -/
def diskAct (g : SU11) (z : ℂ) : ℂ :=
  (entryA g * z + conj (entryB g)) / (entryB g * z + conj (entryA g))

/-- README 2.3. The holomorphic discrete series action `(b z + conj a)^{-k} h(z · g)`. -/
def discreteAction (k : ℕ) (g : SU11) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  (entryB g * z + conj (entryA g)) ^ (-(k : ℤ)) * h (diskAct g z)

/-- README 2.3. **Holomorphic discrete series.** For `k ≥ 2` the action maps the disc to itself,
is a right action on the disc, preserves holomorphy and preserves the weighted Bergman norm. -/
theorem discreteAction_isometry (k : ℕ) (hk : 2 ≤ k) (g g' : SU11) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1)) :
    MapsTo (diskAct g) (Metric.ball 0 1) (Metric.ball 0 1) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1,
      discreteAction k (g * g') h z = discreteAction k g (discreteAction k g' h) z) ∧
    DifferentiableOn ℂ (discreteAction k g h) (Metric.ball 0 1) ∧
    ∫⁻ z, ‖discreteAction k g h z‖ₑ ^ 2 ∂bergmanMeasure k = ∫⁻ z, ‖h z‖ₑ ^ 2 ∂bergmanMeasure k := by
  sorry

/-- README 2.3. **Bergman norms and kernel.** `‖zʲ‖² = C(k-1+j, j)⁻¹` and the reproducing
kernel is `(1 - z conj w)^{-k}`. -/
theorem bergman_monomial_kernel (k : ℕ) (hk : 2 ≤ k) (j : ℕ) (z w : ℂ) (hz : ‖z‖ < 1)
    (hw : ‖w‖ < 1) :
    ∫⁻ x, ‖x ^ j‖ₑ ^ 2 ∂bergmanMeasure k = ((Nat.choose (k - 1 + j) j : ℝ≥0∞))⁻¹ ∧
    HasSum (fun i : ℕ => (Nat.choose (k - 1 + i) i : ℂ) * (z * conj w) ^ i)
      ((1 - z * conj w) ^ (-(k : ℤ))) := by
  sorry

/-- README 2.3. The antiholomorphic discrete series action `conj((b z + conj a)^{-k}) h(z · g)`. -/
def antiDiscreteAction (k : ℕ) (g : SU11) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  conj ((entryB g * z + conj (entryA g)) ^ (-(k : ℤ))) * h (diskAct g z)

/-- README 2.3. **Antiholomorphic discrete series.** It is the complex conjugate of the
holomorphic action; for `k ≥ 2` it is a right action on the disc, preserves antiholomorphy and
preserves the weighted Bergman norm. -/
theorem antiDiscreteAction_spec (k : ℕ) (hk : 2 ≤ k) (g g' : SU11) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ (fun z => conj (h z)) (Metric.ball 0 1)) :
    antiDiscreteAction k g h = (fun z => conj (discreteAction k g (fun w => conj (h w)) z)) ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1,
      antiDiscreteAction k (g * g') h z = antiDiscreteAction k g (antiDiscreteAction k g' h) z) ∧
    DifferentiableOn ℂ (fun z => conj (antiDiscreteAction k g h z)) (Metric.ball 0 1) ∧
    ∫⁻ z, ‖antiDiscreteAction k g h z‖ₑ ^ 2 ∂bergmanMeasure k =
      ∫⁻ z, ‖h z‖ₑ ^ 2 ∂bergmanMeasure k := by
  sorry

/-- README 2.3. **Weights of the discrete series.** `T(k_α) zʲ = e^{i(k/2 + j)α} zʲ` in the
holomorphic model and `T(k_α) conj(z)ʲ = e^{-i(k/2 + j)α} conj(z)ʲ` in the antiholomorphic one. -/
theorem discreteAction_rot (k j : ℕ) (α : ℝ) :
    discreteAction k (rot α) (fun z => z ^ j) =
      (fun z => Complex.exp (((k : ℂ) / 2 + j) * α * Complex.I) * z ^ j) ∧
    antiDiscreteAction k (rot α) (fun z => conj z ^ j) =
      (fun z => Complex.exp (-(((k : ℂ) / 2 + j) * α * Complex.I)) * conj z ^ j) := by
  sorry

/-- README 2.4. The `ax + b` group `{x ↦ a x + b, a > 0}`. -/
@[ext]
structure AxB where
  /-- The dilation `a > 0`. -/
  a : ℝ
  /-- The translation `b`. -/
  b : ℝ
  /-- The dilation is strictly positive. -/
  a_pos : 0 < a

namespace AxB

instance : Mul AxB := ⟨fun g h => ⟨g.a * h.a, g.a * h.b + g.b, mul_pos g.a_pos h.a_pos⟩⟩

instance : One AxB := ⟨⟨1, 0, one_pos⟩⟩

instance : Inv AxB := ⟨fun g => ⟨g.a⁻¹, -(g.a⁻¹ * g.b), inv_pos.2 g.a_pos⟩⟩

/-- The positive dilation of a product in `AxB`. -/
@[simp] theorem mul_a (g h : AxB) : (g * h).a = g.a * h.a := rfl
/-- The translation of a product in `AxB`. -/
@[simp] theorem mul_b (g h : AxB) : (g * h).b = g.a * h.b + g.b := rfl
/-- The positive dilation of the identity in `AxB`. -/
@[simp] theorem one_a : (1 : AxB).a = 1 := rfl
/-- The translation of the identity in `AxB`. -/
@[simp] theorem one_b : (1 : AxB).b = 0 := rfl
/-- The positive dilation of the inverse in `AxB`. -/
@[simp] theorem inv_a (g : AxB) : g⁻¹.a = g.a⁻¹ := rfl
/-- The translation of the inverse in `AxB`. -/
@[simp] theorem inv_b (g : AxB) : g⁻¹.b = -(g.a⁻¹ * g.b) := rfl

instance : Group AxB where
  mul_assoc g h k := by ext <;> simp <;> ring
  one_mul g := by ext <;> simp
  mul_one g := by ext <;> simp
  inv_mul_cancel g := by ext <;> simp [g.a_pos.ne']

/-- README 2.4. The `ax + b` group acts on the half-line by `g • x = x / a`, so that
`g⁻¹ • x = a x`. -/
instance : MulAction AxB ℝ where
  smul g x := x / g.a
  one_smul x := div_one x
  mul_smul g h x := by
    show x / (g.a * h.a) = x / h.a / g.a
    rw [div_div, mul_comm]

end AxB

/-- README 2.4. The invariant measure `dx / x` on the half-line. -/
def halfLineMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun x => ENNReal.ofReal x⁻¹

/-- README 2.4. The multiplier `e^{i λ b x}` of the `ax + b` group on the half-line. -/
def axbCocycle (lam : ℝ) (g : AxB) (x : ℝ) : ℂ := Complex.exp ((lam * g.b * x : ℝ) * Complex.I)

/-- README 2.4. The representation `(T_λ(a, b) f)(x) = e^{i λ b x} f(a x)` on `L²(ℝ₊, dx/x)`. -/
def axbRep (lam : ℝ) : ContRepresentation ℂ AxB (Lp ℂ 2 halfLineMeasure) :=
  multiplierRep halfLineMeasure (axbCocycle lam)

/-- README 2.4. **Representations of the `ax + b` group.** `T_λ` realizes the formula and is
unitary for every real `λ`; for `λ ≠ 0` it is irreducible; `T_λ ≅ T_λ'` exactly when `λ` and
`λ'` have the same sign. -/
theorem axbRep_spec (lam lam' : ℝ) (hlam : lam ≠ 0) (hlam' : lam' ≠ 0) :
    (∀ g f, (axbRep lam g f : ℝ → ℂ) =ᵐ[halfLineMeasure] multiplierAction (axbCocycle lam) g f) ∧
    (axbRep lam).IsUnitary ∧
    (∀ W : Submodule ℂ (Lp ℂ 2 halfLineMeasure), IsClosed (W : Set (Lp ℂ 2 halfLineMeasure)) →
      (∀ g, ∀ v ∈ W, axbRep lam g v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
    ((∃ U : Lp ℂ 2 halfLineMeasure ≃ₗᵢ[ℂ] Lp ℂ 2 halfLineMeasure,
        ∀ g v, U (axbRep lam g v) = axbRep lam' g (U v)) ↔ 0 < lam * lam') := by
  sorry

/-- README 2.5. Tau Ceti's Heisenberg group acts on the line through `g • x = x - g.x`. -/
instance : MulAction (TauCeti.HeisenbergGroup ℝ) ℝ where
  smul g x := x - g.x
  one_smul x := sub_zero x
  mul_smul g h x := by
    show x - (g.x + h.x) = x - h.x - g.x
    ring

/-- README 2.5. The Schrödinger multiplier `e^{i(z + y x)}`. -/
def schrodingerCocycle (g : TauCeti.HeisenbergGroup ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((g.z + g.y * x : ℝ) * Complex.I)

/-- README 2.5. The Schrödinger representation `(U(g) f)(x) = e^{i(z + y x)} f(x + g.x)` on
`L²(ℝ)`. -/
def schrodinger : ContRepresentation ℂ (TauCeti.HeisenbergGroup ℝ) (Lp ℂ 2 (volume : Measure ℝ)) :=
  multiplierRep volume schrodingerCocycle

/-- README 2.5. **Schrödinger representation.** It realizes the formula and is unitary. -/
theorem schrodinger_spec :
    (∀ g f, (schrodinger g f : ℝ → ℂ) =ᵐ[volume] multiplierAction schrodingerCocycle g f) ∧
    schrodinger.IsUnitary := by
  sorry

open scoped FourierTransform in
/-- README 2.5. **Fourier dictionary.** For integrable `f` and `𝓕 f(ξ) = ∫ e^{-2πivξ} f(v) dv`,
`𝓕(U(g) f)(ξ) = e^{i(2πxξ + z - xy)} 𝓕 f(ξ - y/(2π))`. -/
theorem fourier_schrodinger (g : TauCeti.HeisenbergGroup ℝ) (f : ℝ → ℂ) (hf : Integrable f)
    (ξ : ℝ) :
    𝓕 (multiplierAction schrodingerCocycle g f) ξ =
      Complex.exp ((2 * π * g.x * ξ + g.z - g.x * g.y : ℝ) * Complex.I) *
        𝓕 f (ξ - g.y / (2 * π)) := by
  sorry

/-- README 2.6. The sphere model of the motion group: `(a, k)` acts by
`e^{i R ⟨a, ξ⟩} f(k⁻¹ ξ)`. -/
def motionAction {n : ℕ} (R : ℝ) (g : MotionGroup n) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  Complex.exp ((R * ⟪g.a, ξ⟫_ℝ : ℝ) * Complex.I) * f (rotE g.k⁻¹ ξ)

/-- README 2.6. **Sphere model: representation law.** -/
theorem motionAction_mul {n : ℕ} (R : ℝ) (g h : MotionGroup n)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    motionAction R (g * h) f = motionAction R g (motionAction R h f) ∧ motionAction R 1 f = f := by
  sorry

/-- README 2.6. **Sphere model: unitarity.** For real `R` the action preserves the `L²` norm for
the surface measure on the unit sphere. -/
theorem lintegral_motionAction {n : ℕ} (R : ℝ) (g : MotionGroup n)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (hf : Measurable f) :
    ∫⁻ ξ, ‖motionAction R g f ξ‖ₑ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere =
      ∫⁻ ξ, ‖f ξ‖ₑ ^ 2 ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  sorry

/-! ## Layer 3: matrix elements -/

section MatrixElements

variable {G H ι : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [DecidableEq ι]

/-- README 3.1. The matrix element `D_{mn}(g) = ⟪e_m, U(g) e_n⟫` of a representation in a Hilbert
basis, Edmonds's `⟨m|D(g)|n⟩`; Roadmap 1's `SU(2)` matrix element is an instance. -/
def matrixElement (U : ContRepresentation ℂ G H) (e : HilbertBasis ι ℂ H) (m n : ι) (g : G) : ℂ :=
  ⟪e m, U g (e n)⟫_ℂ

/-- README 3.1. **Bridge to Tau Ceti's matrix coefficient.** When `U` is norm continuous,
`D_{mn}(g)` is the conjugate of `matrixCoeff U hU (e n) (e m) g`. -/
theorem matrixElement_eq_conj_matrixCoeff [TopologicalSpace G] (U : ContRepresentation ℂ G H)
    (hU : Continuous U) (e : HilbertBasis ι ℂ H) (m n : ι) (g : G) :
    matrixElement U e m n g = conj (U.matrixCoeff hU (e n) (e m) g) := by
  sorry

/-- README 3.2. **Addition theorem.** `D_{mn}(gh) = Σₖ D_{mk}(g) D_{kn}(h)`, absolutely
convergent, and `D_{mn}(1) = δ_{mn}`. -/
theorem hasSum_matrixElement_mul (U : ContRepresentation ℂ G H) (e : HilbertBasis ι ℂ H)
    (m n : ι) (g h : G) :
    HasSum (fun k => matrixElement U e m k g * matrixElement U e k n h)
        (matrixElement U e m n (g * h)) ∧
      Summable (fun k => ‖matrixElement U e m k g * matrixElement U e k n h‖) ∧
      matrixElement U e m n 1 = if m = n then 1 else 0 := by
  sorry

/-- README 3.2. **Unitarity relations.** A representation is unitary exactly when the columns of
its matrix are orthonormal; then the rows are orthonormal and `D_{mn}(g⁻¹) = conj D_{nm}(g)`. -/
theorem isUnitary_iff_hasSum_matrixElement (U : ContRepresentation ℂ G H) (e : HilbertBasis ι ℂ H) :
    (U.IsUnitary ↔ ∀ g m n, HasSum (fun k => conj (matrixElement U e k m g) *
        matrixElement U e k n g) (if m = n then 1 else 0)) ∧
    (U.IsUnitary → ∀ g m n,
      HasSum (fun k => matrixElement U e m k g * conj (matrixElement U e n k g))
        (if m = n then 1 else 0) ∧
      matrixElement U e m n g⁻¹ = conj (matrixElement U e n m g)) := by
  sorry

/-- README 3.3. The weight space `{v | U(κ u) v = u^j v}` of a circle subgroup `κ`. -/
def weightSpace (U : ContRepresentation ℂ G H) (κ : Circle →* G) (j : ℤ) : Submodule ℂ H where
  carrier := {v | ∀ u : Circle, U (κ u) v = ((u : ℂ) ^ j) • v}
  add_mem' := by
    intro v w hv hw u
    simp only [map_add, hv u, hw u, smul_add]
  zero_mem' := by
    intro u
    simp
  smul_mem' := by
    intro c v hv u
    simp only [map_smul, hv u]
    exact smul_comm _ _ _

/-- README 3.3. **Weight decomposition.** For a unitary representation whose restriction to the
circle subgroup has continuous orbits, `H` is the Hilbert sum of the weight spaces; a matrix
element between weight vectors of weights `j_m`, `j_n` transforms by
`D_{mn}(κ u₁ g κ u₂) = u₁^{j_m} u₂^{j_n} D_{mn}(g)`. -/
theorem isHilbertSum_weightSpace (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
    (κ : Circle →* G) (hκ : ∀ v, Continuous fun u => U (κ u) v) (e : HilbertBasis ι ℂ H)
    (m n : ι) (jm jn : ℤ) (hm : e m ∈ weightSpace U κ jm) (hn : e n ∈ weightSpace U κ jn)
    (u₁ u₂ : Circle) (g : G) :
    IsHilbertSum ℂ (fun j : ℤ => weightSpace U κ j) (fun j => (weightSpace U κ j).subtypeₗᵢ) ∧
      matrixElement U e m n (κ u₁ * g * κ u₂) =
        (u₁ : ℂ) ^ jm * (u₂ : ℂ) ^ jn * matrixElement U e m n g := by
  sorry

end MatrixElements

/-! ## Layer 4: infinitesimal operators -/

/-- README 4.1. The derivative at `0` of the orbit of `v` along a curve `γ` through `1`. -/
def infinitesimal {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ContRepresentation ℂ G H) (γ : ℝ → G) (v : H) : H :=
  deriv (fun s => U (γ s) v) 0

/-- README 4.1. **Ladder operators.** On `e_m = e^{inθ}`, `m = n - ε`, the infinitesimal
operators of the principal series exist, `J₊ = -A₁ + iA₂` raises `m` with coefficient `m - τ`,
`J₋ = -A₁ - iA₂` lowers it with coefficient `-(m + τ)`, and `J₃ = -iA₃` acts by `m`. -/
theorem principalSeries_ladder (τ : ℂ) (e : Fin 2) (n : ℤ) :
    let U := principalSeries τ e
    let m : ℂ := (n : ℂ) - (e : ℂ) / 2
    let v : ℤ → Lp ℂ 2 (haarAddCircle (T := 2 * π)) := fun j => fourierLp 2 j
    HasDerivAt (fun s => U (boost s) (v n)) (infinitesimal U boost (v n)) 0 ∧
    HasDerivAt (fun s => U (boostY s) (v n)) (infinitesimal U boostY (v n)) 0 ∧
    HasDerivAt (fun s => U (rot s) (v n)) (infinitesimal U rot (v n)) 0 ∧
    -infinitesimal U boost (v n) + Complex.I • infinitesimal U boostY (v n) =
      (m - τ) • v (n + 1) ∧
    -infinitesimal U boost (v n) - Complex.I • infinitesimal U boostY (v n) =
      (-(m + τ)) • v (n - 1) ∧
    -(Complex.I • infinitesimal U rot (v n)) = m • v n := by
  sorry

/-- README 4.2. **Casimir eigenvalue.** `A₁² + A₂² - A₃²` acts on `e^{inθ}` by `τ(τ + 1)`. -/
theorem principalSeries_casimir (τ : ℂ) (e : Fin 2) (n : ℤ) :
    let U := principalSeries τ e
    let v : Lp ℂ 2 (haarAddCircle (T := 2 * π)) := fourierLp 2 n
    infinitesimal U boost (infinitesimal U boost v) +
        infinitesimal U boostY (infinitesimal U boostY v) -
        infinitesimal U rot (infinitesimal U rot v) = (τ * (τ + 1)) • v := by
  sorry

/-- README 3.3. **Euler factorization of matrix elements.** With `e_m = e^{inθ}`, `m = n - ε`,
`D_{m'm}(g(α, t, γ)) = e^{im'α} D_{m'm}(b_t) e^{imγ}`, Roadmap 1's `e^{im'α} d_{m'm}(β) e^{imγ}`
with `b_t` in place of `b_β`. -/
theorem principalSeries_matrixElement_euler (τ : ℂ) (e : Fin 2) (n' n : ℤ) (α t γ : ℝ) :
    let D := matrixElement (principalSeries τ e) (fourierBasis (T := 2 * π)) n' n
    D (eulerSU11 α t γ) =
      Complex.exp (((n' : ℂ) - (e : ℂ) / 2) * α * Complex.I) * D (boost t) *
        Complex.exp (((n : ℂ) - (e : ℂ) / 2) * γ * Complex.I) := by
  sorry

/-- README 4.3. **Template ODE.** The matrix element `P(t) = D_{m'm}(b_t) = ⟪e_{m'}, T(b_t) e_m⟫`,
`e_m = e^{inθ}`, `m = n - ε`, is smooth and satisfies
`P'' + coth t P' - (m'² + m² - 2m'm cosh t) / sinh² t · P = τ(τ + 1) P` for `t > 0`. -/
theorem principalSeries_matrixElement_ode (τ : ℂ) (e : Fin 2) (n' n : ℤ) :
    let P : ℝ → ℂ := fun t =>
      matrixElement (principalSeries τ e) (fourierBasis (T := 2 * π)) n' n (boost t)
    let m' : ℂ := (n' : ℂ) - (e : ℂ) / 2
    let m : ℂ := (n : ℂ) - (e : ℂ) / 2
    ContDiff ℝ ∞ P ∧ ∀ t : ℝ, 0 < t →
      deriv (deriv P) t + ((Real.cosh t / Real.sinh t : ℝ) : ℂ) * deriv P t -
          (m' ^ 2 + m ^ 2 - 2 * m' * m * (Real.cosh t : ℂ)) / ((Real.sinh t : ℂ) ^ 2) * P t =
        τ * (τ + 1) * P t := by
  sorry

/-! ## Layer 5: Gel'fand pairs and spherical functions -/

section Gelfand

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

/-- README 5.1. `f` is bi-invariant under `K`: `f(k₁ x k₂) = f(x)`. -/
def IsBiInvariant (K : Subgroup G) (f : G → ℂ) : Prop :=
  ∀ k₁ ∈ K, ∀ k₂ ∈ K, ∀ x, f (k₁ * x * k₂) = f x

/-- README 5.1. The convolution `(f * h)(x) = ∫ f(y) h(y⁻¹ x) dμ(y)`. -/
def conv (μ : Measure G) (f h : G → ℂ) (x : G) : ℂ := ∫ y, f y * h (y⁻¹ * x) ∂μ

/-- README 5.1. `(G, K)` is a Gel'fand pair for the Haar measure `μ`: convolution of continuous
compactly supported bi-`K`-invariant functions is commutative. -/
def IsGelfandPair (μ : Measure G) (K : Subgroup G) : Prop :=
  ∀ f h : G → ℂ, Continuous f → HasCompactSupport f → IsBiInvariant K f →
    Continuous h → HasCompactSupport h → IsBiInvariant K h → conv μ f h = conv μ h f

/-- README 5.1. **Gel'fand's criterion.** On a unimodular locally compact group with compact
`K`, a continuous involutive anti-automorphism `σ` with `σ x ∈ K x K` gives a Gel'fand pair. -/
theorem isGelfandPair_of_antiAut [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (σ : G → G) (hσc : Continuous σ)
    (hσmul : ∀ x y, σ (x * y) = σ y * σ x) (hσσ : ∀ x, σ (σ x) = x)
    (hσK : ∀ x, ∃ k₁ ∈ K, ∃ k₂ ∈ K, σ x = k₁ * x * k₂) :
    IsGelfandPair μ K := by
  sorry

/-- README 5.1. **Symmetric pairs.** A continuous involutive automorphism `θ` fixing `K`, with
`G = K P` for `P = {p | θ p = p⁻¹}`, gives a Gel'fand pair. -/
theorem isGelfandPair_of_involution [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (θ : G →* G) (hθc : Continuous θ) (hθθ : ∀ x, θ (θ x) = x)
    (hθK : ∀ k ∈ K, θ k = k) (hKP : ∀ x, ∃ k ∈ K, ∃ p, θ p = p⁻¹ ∧ x = k * p) :
    IsGelfandPair μ K := by
  sorry

/-- README 5.2. `φ` is a spherical function for `(G, K)` and the measure `ν` on `K`: continuous,
bi-`K`-invariant, `φ(1) = 1`, with `∫_K φ(x k y) dν(k) = φ(x) φ(y)`. Boundedness is not
required. -/
def IsSphericalFunction (K : Subgroup G) (ν : Measure K) (φ : G → ℂ) : Prop :=
  Continuous φ ∧ IsBiInvariant K φ ∧ φ 1 = 1 ∧ ∀ x y, ∫ k : K, φ (x * k * y) ∂ν = φ x * φ y

/-- README 5.2. **The functional equation suffices.** For compact `K` with an invariant
probability measure, a continuous `φ` is spherical exactly when it is not identically zero and
satisfies the functional equation. -/
theorem isSphericalFunction_iff [IsTopologicalGroup G] [BorelSpace G] {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    [ν.IsMulRightInvariant] {φ : G → ℂ} (hφ : Continuous φ) :
    IsSphericalFunction K ν φ ↔
      (∃ x, φ x ≠ 0) ∧ ∀ x y, ∫ k : K, φ (x * k * y) ∂ν = φ x * φ y := by
  sorry

/-- README 5.2. The spherical transform `f ↦ ∫ f(x) φ(x⁻¹) dμ(x)`. -/
def sphericalTransform (μ : Measure G) (φ : G → ℂ) (f : G → ℂ) : ℂ := ∫ x, f x * φ x⁻¹ ∂μ

/-- README 5.2. **Multiplicativity of the spherical transform** on continuous compactly supported
bi-invariant functions. -/
theorem sphericalTransform_conv [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G} (hK : IsCompact (K : Set G))
    (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
    {φ : G → ℂ} (hφ : IsSphericalFunction K ν φ) (f h : G → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (hfK : IsBiInvariant K f) (hhc : Continuous h)
    (hhs : HasCompactSupport h) (hhK : IsBiInvariant K h) :
    sphericalTransform μ φ (conv μ f h) = sphericalTransform μ φ f * sphericalTransform μ φ h := by
  sorry

/-- README 5.2. **Bounded spherical functions are the characters of `L¹(K\\G/K)`.** A bounded
spherical function gives a nonzero multiplicative functional on the integrable bi-invariant
functions; conversely every nonzero, linear, `L¹`-bounded multiplicative functional on them is
the spherical transform of a unique bounded spherical function. -/
theorem bounded_sphericalFunction_iff_character [IsTopologicalGroup G] [LocallyCompactSpace G]
    [BorelSpace G] [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    [ν.IsMulRightInvariant] :
    (∀ φ : G → ℂ, IsSphericalFunction K ν φ → (∃ C, ∀ x, ‖φ x‖ ≤ C) →
      (∀ f h, Integrable f μ → IsBiInvariant K f → Integrable h μ → IsBiInvariant K h →
        sphericalTransform μ φ (conv μ f h) =
          sphericalTransform μ φ f * sphericalTransform μ φ h) ∧
      ∃ f, Integrable f μ ∧ IsBiInvariant K f ∧ sphericalTransform μ φ f ≠ 0) ∧
    ∀ χ : (G → ℂ) → ℂ,
      (∀ f h, Integrable f μ → Integrable h μ → χ (f + h) = χ f + χ h) →
      (∀ (c : ℂ) f, Integrable f μ → χ (c • f) = c * χ f) →
      (∀ f h, f =ᵐ[μ] h → χ f = χ h) →
      (∃ C, ∀ f, Integrable f μ → IsBiInvariant K f → ‖χ f‖ ≤ C * ∫ x, ‖f x‖ ∂μ) →
      (∀ f h, Integrable f μ → IsBiInvariant K f → Integrable h μ → IsBiInvariant K h →
        χ (conv μ f h) = χ f * χ h) →
      (∃ f, Integrable f μ ∧ IsBiInvariant K f ∧ χ f ≠ 0) →
      ∃! φ : G → ℂ, IsSphericalFunction K ν φ ∧ (∃ C, ∀ x, ‖φ x‖ ≤ C) ∧
        ∀ f, Integrable f μ → IsBiInvariant K f → χ f = sphericalTransform μ φ f := by
  sorry

/-- README 5.3. The subspace of `K`-fixed vectors. -/
def fixedSubmodule {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ContRepresentation ℂ G H) (K : Subgroup G) : Submodule ℂ H where
  carrier := {v | ∀ k ∈ K, U k v = v}
  add_mem' := by
    intro v w hv hw k hk
    simp only [map_add, hv k hk, hw k hk]
  zero_mem' := by
    intro k _
    simp
  smul_mem' := by
    intro c v hv k hk
    simp only [map_smul, hv k hk]

/-- README 5.3. **Spherical functions from representations.** If the `K`-fixed vectors of a
strongly continuous unitary representation are the line through a unit vector `v`, then
`g ↦ ⟪v, U(g) v⟫` is a positive-definite spherical function. -/
theorem isSphericalFunction_inner [IsTopologicalGroup G] [BorelSpace G] {H : Type*}
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
    (hc : ∀ w, Continuous fun g => U g w) {K : Subgroup G} (hK : IsCompact (K : Set G))
    (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
    (v : H) (hv : ‖v‖ = 1) (hfix : fixedSubmodule U K = Submodule.span ℂ {v}) :
    IsSphericalFunction K ν (fun g => ⟪v, U g v⟫_ℂ) ∧
      (Matrix.of fun g h : G => ⟪v, U (g⁻¹ * h) v⟫_ℂ).PosSemidef := by
  sorry

/-- README 5.3. **Multiplicity one.** In an irreducible strongly continuous unitary
representation of a separable group with a Gel'fand pair `(G, K)`, the `K`-fixed vectors form a
space of dimension at most one. -/
theorem rank_fixedSubmodule_le_one [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
    [SecondCountableTopology G] (μ : Measure G) [μ.IsHaarMeasure] (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (hG : IsGelfandPair μ K) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (U : ContRepresentation ℂ G H) (hU : U.IsUnitary)
    (hc : ∀ w, Continuous fun g => U g w)
    (hirr : ∀ W : Submodule ℂ H, IsClosed (W : Set H) → (∀ g, ∀ w ∈ W, U g w ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    Module.rank ℂ (fixedSubmodule U K) ≤ 1 := by
  sorry

end Gelfand

/-- README 5.3. **Positive-definite spherical functions come from representations.** A
positive-definite spherical function is `g ↦ ⟪v, U(g) v⟫` for a strongly continuous unitary
representation `U` and a `K`-fixed unit vector `v`. -/
theorem exists_isUnitary_of_sphericalFunction {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {K : Subgroup G}
    (hK : IsCompact (K : Set G)) (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]
    [ν.IsMulRightInvariant] {φ : G → ℂ} (hφ : IsSphericalFunction K ν φ)
    (hpos : (Matrix.of fun g h : G => φ (g⁻¹ * h)).PosSemidef) :
    ∃ (V : Type u) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V) (_ : CompleteSpace V)
      (U : ContRepresentation ℂ G V) (v : V), U.IsUnitary ∧ (∀ w, Continuous fun g => U g w) ∧
        ‖v‖ = 1 ∧ v ∈ fixedSubmodule U K ∧ ∀ g, φ g = ⟪v, U g v⟫_ℂ := by
  sorry

/-- README 5.4. **`(SU(1,1), K)` is a Gel'fand pair**, by Gel'fand's criterion with the transpose
`g(α, t, γ)ᵀ = g(γ, t, α)`. -/
theorem isGelfandPair_su11 : IsGelfandPair su11Haar su11K := by
  sorry

/-- README 5.4. **Radial equation on `SU(1,1)`.** For a spherical function of `(SU(1,1), K)`,
`F(t) = φ(b_t)` is smooth and satisfies `F'' + coth t F' = c F` for `t > 0` and some `c`. -/
theorem sphericalFunction_su11_ode (ν : Measure su11K) [IsProbabilityMeasure ν]
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] {φ : SU11 → ℂ}
    (hφ : IsSphericalFunction su11K ν φ) :
    ∃ c : ℂ, ContDiff ℝ ∞ (fun t => φ (boost t)) ∧ ∀ t : ℝ, 0 < t →
      deriv (deriv fun s => φ (boost s)) t +
          ((Real.cosh t / Real.sinh t : ℝ) : ℂ) * deriv (fun s => φ (boost s)) t =
        c * φ (boost t) := by
  sorry

end SFVK.FunctionSpaceModels

/-! ## Supplier declarations named in the README -/

#check @Matrix.SpecialLinearGroup
#check @Matrix.specialOrthogonalGroup
#check @MeasureTheory.Measure.toSphere
#check @MeasureTheory.Measure.IsHaarMeasure
#check @MeasureTheory.Measure.modularCharacter
#check @MeasureTheory.Measure.rnDeriv
#check @MeasureTheory.Measure.Regular
#check @HilbertBasis.hasSum_inner_mul_inner
#check @Complex.besselJ
#check @ContRepresentation.IsUnitary
#check @ContRepresentation.matrixCoeff
#check @ContRepresentation.toStronglyContinuousGroup
#check @ContRepresentation.IsUnitary.posSemidef_inner_map_inv_mul
#check @TauCeti.posSemidef_inv_mul_iff_exists_isUnitary
#check @MeasureTheory.Measure.leftRegular
#check @MeasureTheory.Measure.isUnitary_leftRegular
#check @MeasureTheory.Measure.continuous_leftRegular_apply
#check @TauCeti.HeisenbergGroup.equivProd
#check @Matrix.toEuclideanLin
#check @Real.fourier_real_eq_integral_exp_smul
