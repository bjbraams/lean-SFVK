# Roadmap: function-space models of noncompact groups

**Summary.** This roadmap builds the concrete representation theory of the noncompact groups that
occur in the group-theoretic approach to special functions: `SU(1,1)`, the `ax + b` group, the
Heisenberg group, the oscillator group and the Euclidean motion groups. It realizes their
representations on spaces of functions on homogeneous spaces (the circle, the disc, the half-line,
the line, the sphere) by multiplier formulas `(T(g) f)(x) = α(g, x) f(g⁻¹ • x)`, and develops the
general tools that turn such a model into special-function identities: matrix elements in a
Hilbert basis with their addition theorem and unitarity relations, weight decompositions under a
circle subgroup, infinitesimal operators on explicit vectors with the Casimir eigenvalue and the
second-order equation of matrix elements, and Gel'fand pairs with compact `K`, spherical functions
and the spherical transform. Its organization follows the structure of the subject rather than
any one text: groups and invariant measures, then `G`-spaces and multipliers, then the models,
then the analysis of a model (matrix elements, infinitesimal operators), then harmonic analysis on
`K\G/K`. The content is drawn from Vilenkin–Klimyk (*Representation of Lie Groups and Special
Functions*, Vol. 1, Chs. 1, 2, 4–6), Klimyk–Vilenkin (*Representations of Lie Groups and Special
Functions*, EMS 59, Part II Ch. 1), Wawrzyńczyk (*Group Representations and Special Functions*,
Chs. 1, 2, 5), Dieudonné (*Special Functions and Linear Representations of Lie Groups*, §§8–9) and
Miller (*Lie Theory and Special Functions*, §§1-3, 3-6, 5-18), with the Euler-angle and
matrix-element conventions of Edmonds (*Angular Momentum in Quantum Mechanics*, §4.1); each
headline cites its sources; see [References](#references).

Mathlib has Haar measure, the modular character, Radon–Nikodym derivatives and `withDensity`,
`Lp` spaces, Fourier series on `AddCircle` with `fourierBasis`, Hilbert bases and Hilbert sums,
`Matrix.SpecialLinearGroup` with its topology, the Gamma function and the surface measure
`MeasureTheory.Measure.toSphere`. Tau Ceti has continuous representations on topological vector
spaces with unitarity (`ContRepresentation.IsUnitary`), norm-continuous matrix coefficients
(`ContRepresentation.matrixCoeff`), the left regular representation on `Lᵖ` with its unitarity and
strong continuity (`MeasureTheory.Measure.leftRegular`), positive-definite coefficients and the GNS
characterization (`TauCeti.posSemidef_inv_mul_iff_exists_isUnitary`), one-parameter groups
(`ContRepresentation.toStronglyContinuousGroup`) and the Heisenberg group `TauCeti.HeisenbergGroup`.
Neither has the motion groups `ℝⁿ ⋊ SO(n)` as topological groups, multiplier representations, any
model of a noncompact group on a function space, matrix elements of a strongly continuous
representation, Gel'fand pairs or spherical functions.

The roadmap covers:
- `SU(1,1)` with Euler angles, the Cayley transform, Haar measure and the Lie algebra; the `ax + b`,
  Heisenberg and oscillator groups in coordinates, and the motion groups `ℝⁿ ⋊ SO(n)` and
  `ISO(1,1)` as locally compact groups, with Haar measures and modular functions (Layer 0);
- quasi-invariant measures with their Radon–Nikodym cocycle, multiplier cocycles, the unitarity
  criterion, strong continuity, the quasi-regular and left regular representations, and
  cohomologous multipliers (Layer 1);
- the principal series of `SU(1,1)` on the circle with its unitarity range and Hermitian adjoint,
  the weights of the complementary series, the holomorphic and antiholomorphic discrete series on
  weighted Bergman spaces with their reproducing kernels, each with its dictionary to the
  normalized induced models of NoncompactQuantumSymmetry M4, the representations of the `ax + b`
  group on the half-line, the Schrödinger representation of the Heisenberg group with its Fourier
  dictionary, and the sphere models of the motion groups (Layer 2);
- matrix elements in a Hilbert basis, the addition theorem, the unitarity relations and weight
  decompositions under a circle subgroup (Layer 3);
- infinitesimal operators of the principal series on the trigonometric basis, the Casimir
  eigenvalue and the second-order equation of the matrix elements (Layer 4);
- Gel'fand pairs, Gel'fand's criterion and its symmetric-pair form, spherical functions, the
  spherical transform, spherical functions of representations, multiplicity one, and the pair
  `(SU(1,1), K)` with its radial equation (Layer 5).

## Scope and ownership

The roadmap is complete when Tau Ceti proves all of the following.

0. **Groups in coordinates** (0.1–0.3).
1. **`G`-spaces and multiplier representations** (1.1–1.4).
2. **Function-space models** (2.1–2.6).
3. **Matrix elements in infinite dimension** (3.1–3.3).
4. **Infinitesimal operators of the circle models** (4.1–4.3).
5. **Gel'fand pairs and spherical functions** (5.1–5.4).

The numbers are those of the layers below, and `k.n` names subsection `n` of Layer `k`.
`Coordinates.lean` and `Suggested.lean` state the headlines that carry a Lean name, each with
every conclusion the README attaches to it. Other headlines are
targets of the same standing, stated in prose. The `**Checks.**` and `### Examples` of each layer
are statements to prove; they test the conventions on explicit values.

**Boundary with the RepresentationTheory family.** The family index
([RepresentationTheory](../RepresentationTheory/README.md)) stops the analytic theory at compact
groups: it has no infinite-dimensional unitary representations of noncompact groups, no Plancherel
theory and no tempered spectrum, and it keeps the structure theory of noncompact reductive groups
(Cartan, Iwasawa and KAK decompositions in its LieGroups roadmap). This roadmap sits outside that
family and owns exactly the following analytic material for noncompact groups: explicit models on
function spaces given by multiplier formulas, the analysis of a given model through its matrix
elements, weights and infinitesimal operators, and harmonic analysis on `K\G/K` up to the
spherical transform. It owns no classification, no decomposition of a representation into
irreducibles and no Plancherel formula.

**Boundary with SmoothBanachRepresentations.**
[SmoothBanachRepresentations](../RepresentationTheory/SmoothBanachRepresentations/README.md) (its
Layers 0–4), extending
[AutomorphicFormsOnReductiveGroups §2.7](../AutomorphicFormsOnReductiveGroups/README.md), owns
the one-parameter generators, the Gårding space, the smooth vectors and the derived Lie and
enveloping actions of a strongly continuous Banach representation, with the convention
`dπ(X) v = d/dt π(exp tX) v` at `t = 0`.
[NoncompactQuantumSymmetry M0](../NoncompactQuantumSymmetry/README.md) owns the Hilbert-adjoint
statements on that domain (skew-symmetry of real generators, Nelson's theorem, analytic vectors).
This roadmap consumes them and computes, for the principal series of `SU(1,1)`, the derivatives of
explicit orbits `s ↦ T(ω(s)) e_m` of trigonometric basis vectors; the derivative it uses is the
same one, at the same point, and agrees with the derived action of those roadmaps on smooth
vectors (4.1).

**Boundary with NoncompactQuantumSymmetry.** One object has one owner: what
[NoncompactQuantumSymmetry](../NoncompactQuantumSymmetry/README.md) owns is consumed from it with
its hypotheses and is not restated here; this roadmap gives only its own concrete model and a
dictionary, an agreement theorem identifying the model with that roadmap's object and the
parameter map. That roadmap owns:
- the measurable theory of quasi-invariant measures on transitive spaces `G/H`, Borel sections,
  normalized induction and the imprimitivity theorem (its M1); this roadmap owns quasi-invariant
  measures given by a density for an arbitrary measurable action (1.1) and the multiplier
  representations they carry (1.2–1.4), which on a transitive space are induced representations
  in its M1 model;
- the regular Mackey machine for semidirect products (its M2), which classifies the irreducible
  unitary representations of the `ax + b` and motion groups, and, in its M2 shear-coordinate
  block, the induced models `π_b` of the Heisenberg group with their unitarity, strong
  continuity, central character, irreducibility and classification;
- the unitary dual of `SL(2,ℝ) ≅ SU(1,1)` for the fixed conjugacy by `C₀` (its M4 and M4.SL2R):
  normalized parabolic induction, the principal and complementary series with their invariant
  forms and Hilbert completions, the discrete series `D_n^±` for `n ≥ 2`, their limits `D_1^±`,
  irreducibility, equivalences, endpoint composition, exhaustion, the compact weights and the
  Casimir values `q_B`; the compact eigenvalues of the complementary forms (its M5); the
  Fourier–Laplace and upper half-plane models of `D_l^±` (its M6.C); and the Plancherel theorem
  of `SL(2,ℝ)` (its M4.P);
- the null little group `Δ` with `E(2) = Δ/{±1}` and its type I property (its M4.TypeI), and the
  Euclidean adapters `ℝ² ⋊ Spin(2)` and `ℝ³ ⋊ SU(2)` with their nonzero-radius irreducibles and
  restriction calculations (its M6).

This roadmap owns the motion groups `M(n)` and `ISO(1,1)` as topological groups (0.3), which that
roadmap uses only as the quotients of its covers; the circle, disc, half-line, line and sphere
models in the coordinates of Vilenkin–Klimyk and Miller; the facts that are visible on those
models (representation law, `L²` boundedness, unitarity range, Hermitian adjoint, reproducing
kernels, weights, infinitesimal operators); the `ax + b` models, which that roadmap does not treat
separately; Gel'fand pairs and spherical functions (Layer 5), which it does not treat; and the
dictionaries: `sl2rToSU11_spec`, `principalAction_compactPicture`, `complementaryWeight_ratio`
and `discreteAction_rot` (2.1–2.3), the Casimir dictionary (4.2), `fourier_schrodinger` (2.5) and
the identification of the sphere models of `M(2)` and `M(3)` with its Euclidean adapters (2.6).

**Other boundaries.**
- [OperatorAlgebraDynamics](../OperatorAlgebraDynamics/README.md) D4.LCAWeyl proves
  that an irreducible Weyl pair for a locally compact abelian group is the Schrödinger pair with
  multiplicity one; 2.5 takes the irreducibility of the Schrödinger representation from
  NoncompactQuantumSymmetry M2 instead, through the Fourier dictionary. The
  Stone–von Neumann theorem for the real Heisenberg group in its Hilbert multiplicity form is owned
  by the roadmap MetaplecticAutomorphicForms (its §1.2) and is not a target here.
- [RepresentationTheory/LieGroups](../RepresentationTheory/LieGroups/README.md) Layer 9 owns the
  KAK decomposition of a real reductive group; the Euler angles of 0.1 are its instance for
  `SU(1,1)` and are proved here directly in coordinates. That roadmap leaves spherical and
  Harish-Chandra harmonic analysis downstream, and
  [RealSemisimpleLieGroups](../RealSemisimpleLieGroups/README.md) excludes spherical functions
  on `G/K`; Layer 5 owns spherical functions for unimodular locally compact `G` and compact `K`
  in general.
  [SmoothRepresentationsOfLocalGroups](../SmoothRepresentationsOfLocalGroups/README.md) treats
  spherical Hecke algebras of `p`-adic groups; Layer 5 states nothing specific to totally
  disconnected groups.
- [RepresentationTheory/CompactGroups](../RepresentationTheory/CompactGroups/README.md) Layer 5
  supplies Haar measure, Peter–Weyl and representative-function density for compact `K`; the
  density of `K`-finite vectors in a Banach representation is its named gap
  `gap:banach-gfinite-density`, consumed by AutomorphicFormsOnReductiveGroups §2.1 and here (3.3).
- The identification of specific matrix elements with special functions (Legendre and Jacobi
  functions for `SU(1,1)`, Bessel functions for the motion groups, Laguerre and Hermite functions
  for the Heisenberg and oscillator groups), the decomposition of specific quasi-regular
  representations and the resulting integral transforms are owned by the sibling roadmaps of the
  same project (Euclidean motion groups and Bessel functions; affine, triangular and Heisenberg
  groups; `SU(1,1)` and `SL(2,ℝ)`). Checks below compare with those functions numerically and do
  not make the identification a target.
- The `SU(2)` and `SO(3)` instances of 3.1–3.2 and 5.1–5.2, including the Gel'fand pair
  `(SO(3), SO(2))`, are owned by the sibling roadmap on matrix elements of `SU(2)` and `SO(3)`
  (its Layers 2, 3 and 6). That roadmap's `SU(2)` matrix element is the instance of
  `matrixElement` (3.1) for its unitary model of `Sym^d ℂ²` and the standard basis.

**Inputs.** Cases of the targets that Mathlib or Tau Ceti already proves are inputs, not targets:
- the left regular representation on `L²(G)`, its unitarity and strong continuity:
  `MeasureTheory.Measure.leftRegular`, `MeasureTheory.Measure.isUnitary_leftRegular`,
  `MeasureTheory.Measure.continuous_leftRegular_apply`; 1.3 identifies it with a multiplier
  representation;
- positive definiteness of `g ↦ ⟪ξ, π g ξ⟫` for unitary `π`:
  `ContRepresentation.IsUnitary.posSemidef_inner_map_inv_mul`, consumed in 5.3;
- Parseval's identity in a Hilbert basis, `HilbertBasis.hasSum_inner_mul_inner`, consumed in 3.2.

## Conventions

- **Actions.** Groups act on the left. A source's right action `z ↦ z · g` is kept as a right
  action on points (`circleAct`, `diskAct`), and the operator `f ↦ (z ↦ m(g, z) f(z · g))` is then a
  representation `T(gh) = T(g) T(h)`. In the multiplier framework of 1.2 this is the left action
  `g • z = z · g⁻¹`.
- **Multipliers.** `(T(g) f)(x) = α(g, x) f(g⁻¹ • x)` with `α(1, x) = 1` and
  `α(gh, x) = α(g, x) α(h, g⁻¹ • x)` (`IsMultiplierCocycle`). This is Vilenkin–Klimyk §2.1.6
  (4), p. 80, and Wawrzyńczyk (2.2.7)–(2.2.11), pp. 107–108; Miller's right-action form
  `ν(x, g₁g₂) = ν(x, g₁) ν(xg₁, g₂)` (§1-3, pp. 16–17) is the same identity read through
  `g ↦ g⁻¹`.
- **Radon–Nikodym densities.** `Measure.map (g • ·) μ = μ.withDensity (ρ g)`, with
  `ρ : G → X → ℝ≥0∞`. Then `ρ(gh, x) = ρ(g, x) ρ(h, g⁻¹ • x)` almost everywhere, the identity of
  Wawrzyńczyk Proposition 1.7.2 (p. 86) and of NoncompactQuantumSymmetry M1, and a multiplier
  representation is unitary exactly when `|α(g, x)|² = ρ(g, x)` almost everywhere.
- **Inner products** are conjugate-linear in the first argument, as in Mathlib and Tau Ceti.
- **Matrix elements.** `matrixElement π e m' m g = ⟪e m', π g (e m)⟫`, written `D_{m'm}(g)`, the
  convention of Edmonds (4.1.10), p. 55, and of the sibling `SU(2)` roadmap, whose matrix element
  is the instance of `matrixElement` for its unitary model of `Sym^d ℂ²` and its standard basis.
  In the Vilenkin–Klimyk notation it is `t_{m'm}(g)` (§2.1.2 (2)–(4), pp. 71–72). Tau Ceti's
  `ContRepresentation.matrixCoeff π hπ v w g` is `⟪π g v, w⟫` and needs `π` continuous in
  operator norm, which fails for the models here (the left regular representation of a
  nondiscrete group is not norm continuous); `matrixElement` is therefore a plain function, and
  for norm-continuous `π` it is `conj (matrixCoeff π hπ (e m) (e m') g)`
  (`matrixElement_eq_conj_matrixCoeff`).
- **`SU(1,1)`** is the subgroup `su11` of `SL(2, ℂ)` of matrices `[[a, b], [conj b, conj a]]`,
  `|a|² − |b|² = 1`, with the subspace topology; `entryA g = a`, `entryB g = b`.
- **Euler angles** follow the sibling `SU(2)` roadmap, which uses Edmonds's convention
  (`eulerD α β γ = k_α b_β k_γ`, Edmonds (4.1.9), p. 55, at spin `1/2`), with the same letters and
  order: `g(α, t, γ) = k_α b_t k_γ` (`eulerSU11`), `k_α = diag(e^{iα/2}, e^{−iα/2})` (`rot`, the
  matrix of that roadmap's torus factor) and the real symmetric boost
  `b_t = [[cosh(t/2), sinh(t/2)], [sinh(t/2), cosh(t/2)]]` (`boost`). The boost letter is `t`
  because `τ` is the principal-series parameter. Ranges `0 ≤ α < 2π`, `t ≥ 0`, `−2π ≤ γ < 2π`.
  `K = su11K` is the diagonal subgroup `{k_α}`.
- **Relation to the `SU(2)` angles** (`eulerSU11_continuation`). The `SU(2)` middle factor
  `b_β = [[cos(β/2), sin(β/2)], [−sin(β/2), cos(β/2)]]` at `β = it` is `boostY t`, which lies in
  `SU(1,1)`, and `b_t = k_{−π/2} b_{it} k_{π/2}`; hence `k_α b_{it} k_γ = g(α + π/2, t, γ − π/2)`.
  Under `β = it` the `SU(2)` equation of the matrix elements with eigenvalue `j(j + 1)` becomes the
  equation of 4.3 with `τ(τ + 1)`; the constant phase `e^{i(m'−m)π/2}` of the shift does not change
  it.
- **Vilenkin–Klimyk.** Their `g(φ, t, ψ) = g_φ a_t g_ψ` (§6.1.1 (10)–(12), p. 271) is
  `g(φ, t, ψ)` here, with the same matrices. Their basis `e^{−ikθ}` with weight label `k + ε` is
  `e_m` with `m = −(k + ε)`, so their `t^χ_{kl}` in weight labels is `D_{−k,−l}`, as in the sibling
  roadmap's conversion `t^{VK}_{mn} = D_{−m,−n}`. Locators of Vilenkin–Klimyk below are
  transported by this dictionary.
- **The circle** is `AddCircle (2 * π)` with the Haar probability measure `haarAddCircle` and the
  point `e^{iθ} = fourier 1 θ`. For the principal series with parity `e = 2ε` the basis is
  `e_m = e^{inθ} = fourierLp 2 n` with `m = n − ε ∈ ℤ − ε`, so that `T(k_α) e_m = e^{imα} e_m`,
  the weight convention of the sibling `SU(2)` roadmap.
- **Principal series parameters.** `χ = (τ, ε)` with `τ ∈ ℂ` and `ε ∈ {0, 1/2}`; `ε` is indexed by
  `e = 2ε : Fin 2`, as the sibling `SU(2)` roadmap indexes spin `l` by `d = 2l : ℕ`. The multiplier
  is `|u|^{2τ} (u/|u|)^{2ε}` with `u = b e^{iθ} + conj a`, the mixed power of Vilenkin–Klimyk
  §6.4.1 (1)–(5), pp. 298–299, and Klimyk–Vilenkin §2.2 (23), p. 163, which writes it as
  `(b e^{iθ} + conj a)^{τ+ε} (conj b e^{−iθ} + a)^{τ−ε}`.
- **Comparison with NoncompactQuantumSymmetry M4.** Its fixed conjugacy
  `C₀ = ((1 + i)/2)[[1, i], [1, −i]]` maps `SL(2,ℝ)` onto `SU(1,1)` and its rotation `k_t` to our
  `k_{2t}` (`sl2rToSU11_spec`), so its compact weight `n` (`π(k_t) e_n = e^{int} e_n`) is our `2m`.
  Under `C₀` its generators are `H_K = 2J₃`, `E_+ = −J₊`, `E_− = J₋`, so its
  `q_B = ½(E_−E_+ + E_+E_−) − H_K²/4` is minus our Casimir `A₁² + A₂² − A₃²`. Its parabolic
  parameter is `ν = −(2τ + 1)` (`principalAction_compactPicture`; `ν` and `−ν` give equivalent
  representations there), its parity label is `e`, and `q_B = (1 − ν²)/4 = −τ(τ + 1)`. The
  unitary principal series `Re τ = −1/2` is its `ν ∈ iℝ`; the complementary series
  `−1 < τ < 0`, `e = 0`, is its `0 < |ν| < 1` with even parity; the holomorphic and
  antiholomorphic discrete series of weight `k ≥ 2` are its `D_k^+` and `D_k^−`.
- **Infinitesimal operators.** `A_j = d/ds T(ω_j(s))` at `s = 0` for `ω₁ = boost`, `ω₂ = boostY`,
  `ω₃ = rot`, with tangents `b₁ = ½[[0, 1], [1, 0]]`, `b₂ = ½[[0, i], [−i, 0]]`,
  `b₃ = ½ diag(i, −i)` and brackets `[b₁, b₂] = −b₃`, `[b₂, b₃] = b₁`, `[b₃, b₁] = b₂`
  (Vilenkin–Klimyk §6.1.2 (1)–(6), p. 272). With Edmonds's `T(k_α) = exp(iαJ₃)` the weight
  operator is `J₃ = −iA₃`, the ladder operators are `J_± = −A₁ ± iA₂`, and the Casimir operator is
  `A₁² + A₂² − A₃² = ½(J₊J₋ + J₋J₊) + J₃²` (corrected form, erratum E06.4.03). Vilenkin–Klimyk's
  `H_±, H₃` are `J_∓, −J₃`.
- **Haar measures.** On a noncompact group the normalization is fixed in coordinates: on `SU(1,1)`
  `(8π²)⁻¹ sinh t dα dt dγ` over the Euler ranges, Vilenkin–Klimyk's normalization (§6.1.4 (2),
  p. 275), fixed by `su11Haar {t ≤ T} = cosh T − 1` (the total mass is infinite). Remark: the
  `SU(2)` density `(16π²)⁻¹ sin β` of the sibling roadmap is Vilenkin–Klimyk's (1) on the same
  page, and its formal continuation `β = it` has modulus `(16π²)⁻¹ sinh t`, half of ours; a Haar
  measure of a noncompact group is fixed only up to a scalar, and the factor `2` is
  Vilenkin–Klimyk's choice, kept here; on the
  `ax + b` group `a⁻² da db` (left) and `a⁻¹ da db` (right); on the Heisenberg group Lebesgue
  measure in `(x, y, z)`. On a compact `K` the Haar measure is a probability measure.
- **Gel'fand pairs** are taken with `C_c` bi-invariant functions, in the definition of Dieudonné
  §8, p. 25 (`C_c(K\G/K)` commutative); Wawrzyńczyk (p. 221) uses `L¹(K\G/K)`, which is its
  closure. Spherical functions are continuous, bi-`K`-invariant, `φ(1) = 1` and satisfy
  `∫_K φ(xky) dk = φ(x) φ(y)`, without Dieudonné's boundedness requirement (§8, p. 28); by
  `isSphericalFunction_iff` this is Wawrzyńczyk's definition in §5.1 (continuous, not identically
  zero, the functional equation). The bounded ones are Dieudonné's and are the characters of
  `L¹(K\G/K)` (5.2).
- **Errata.** Statements follow the corrected forms of the project's ERRATA files: E01.1.11
  (oscillator group), E02.1.01 (continuity of a representation is strong continuity), E06.1.03 and
  E06.4.03 (Casimir of `su(1,1)`), E06.4.04 (analytic model of the discrete series), W84-E02.8.02
  (Schrödinger representation), W84-E05.1.01 (convolution with a spherical function), E01.2.11
  (bi-invariant functions form a subalgebra, not an ideal).

## Exact supplier contracts

### From Tau Ceti

- `ContRepresentation.IsUnitary` (`TauCeti/RepresentationTheory/Continuous/Unitary/Basic.lean`):
  `∀ g v w, ⟪π g v, π g w⟫ = ⟪v, w⟫`. The unitarity predicate throughout.
- `ContRepresentation.matrixCoeff`
  (`TauCeti/RepresentationTheory/Continuous/MatrixCoefficient.lean`):
  the coefficient `g ↦ ⟪π g v, w⟫` as an element of `C(G, 𝕜)` for norm-continuous `π`. 3.1
  relates `matrixElement` to it.
- `MeasureTheory.Measure.leftRegular`, `MeasureTheory.Measure.isUnitary_leftRegular`,
  `MeasureTheory.Measure.continuous_leftRegular_apply`
  (`TauCeti/RepresentationTheory/Continuous/LeftRegular/Basic.lean`): left translation
  `f ↦ f(g⁻¹ ·)` on `Lᵖ(G, μ)` for left-invariant `μ`, unitary for `p = 2`, with continuous
  orbits for `p < ∞` and locally finite `μ`. Used in 1.3.
- `ContRepresentation.IsUnitary.posSemidef_inner_map_inv_mul` and
  `TauCeti.posSemidef_inv_mul_iff_exists_isUnitary`
  (`TauCeti/RepresentationTheory/Continuous/Unitary/PositiveDefinite.lean`): coefficients
  `⟪ξ, π g ξ⟫` of unitary representations are exactly the positive-definite functions. Used in
  5.3.
- `ContRepresentation.toStronglyContinuousGroup`
  (`TauCeti/RepresentationTheory/Continuous/OneParameter.lean`): a representation of `ℝ` with
  continuous orbits as a strongly continuous group. Used in 4.1 for the one-parameter subgroups.
- `TauCeti.HeisenbergGroup` and `TauCeti.HeisenbergGroup.equivProd`
  (`TauCeti/GroupTheory/SpecificGroups/Heisenberg.lean`): the group of triples with
  `(x, y, z)(x', y', z') = (x + x', y + y', z + z' + x y')`. Used in 0.2 and 2.5.

### From Mathlib

- `haarAddCircle`, `fourier`, `fourierLp`, `fourierBasis`: the circle, its Haar probability
  measure and the trigonometric Hilbert basis. Used in 2.1, 3.3, Layer 4.
- `Real.fourier_real_eq_integral_exp_smul`: the Fourier transform `𝓕` on `ℝ` with the kernel
  `e^{−2πivξ}`. Used in 2.5.
- `Matrix.toEuclideanLin`: a matrix acting on `EuclideanSpace`. Used in 0.3.
- `HilbertBasis.hasSum_inner_mul_inner`, `IsHilbertSum`: Parseval and Hilbert sums. Used in 3.2,
  3.3.
- `MeasureTheory.Measure.IsHaarMeasure`, `MeasureTheory.Measure.modularCharacter`, `withDensity`,
  `Measure.map`: Haar measure and the modular function. Used in Layer 0, 1.1, Layer 5.
- `MeasureTheory.Measure.toSphere`: the surface measure on the unit sphere. Used in 2.6.
- `Matrix.SpecialLinearGroup` with its topology and `IsTopologicalGroup` instance. Used in 0.1.
- `Real.Gamma`, `Complex.besselJ`: in 2.2 and in the Checks of 2.6.

### From other roadmaps

- [SmoothBanachRepresentations](../RepresentationTheory/SmoothBanachRepresentations/README.md)
  0.2 (one-parameter generators) and 3.1 (the real Lie and enveloping action on smooth vectors);
  [AutomorphicFormsOnReductiveGroups §2.7](../AutomorphicFormsOnReductiveGroups/README.md) for the
  smooth carrier. Consumed in 4.1–4.2 for the statement that the explicit derivatives are the
  derived action on the smooth vectors `e_m`.
- [NoncompactQuantumSymmetry](../NoncompactQuantumSymmetry/README.md), consumed with its
  hypotheses: M0 (skew-symmetry of `dπ(X)` for unitary `π`) in 4.1; M2 (the regular Mackey
  classification) in 2.4 and 2.6, and its shear-coordinate Heisenberg models `π_b` (irreducibility
  and classification) in 2.5; M4 and M4.SL2R (the fixed conjugacy `C₀`, normalized induction, the
  `SL(2,ℝ)` dual with its invariant forms, completions, irreducibility, equivalences, endpoint
  composition, compact weights and `q_B`) in 2.1–2.3 and 4.2; M5 (the compact eigenvalues of the
  complementary forms) in 2.2; M6.C (the half-plane models of `D_l^±`) in 2.3; M4.TypeI (`Δ` and
  `E(2) = Δ/{±1}`) and M6 (the Euclidean adapters) in 2.6.
- [RepresentationTheory/CompactGroups](../RepresentationTheory/CompactGroups/README.md) Layer 5
  and its gap `gap:banach-gfinite-density`, with AutomorphicFormsOnReductiveGroups §2.1 for its
  abbreviation of `K`-finiteness. Consumed in 3.3.
- [RepresentationTheory/LieGroups](../RepresentationTheory/LieGroups/README.md) Layer 9 (the KAK
  decomposition), of which 0.1 is the `SU(1,1)` instance; and its Lie functor, for the general
  form of 5.4.

The two Lean modules import no other roadmap and use the Tau Ceti declarations above directly.
The build command is `lake build SFVKRoadmaps`.

## How to read the build

Layer 0 fixes the groups and their invariant measures in coordinates, so that every later formula
can be checked by hand. Layer 1 is the general machinery of multiplier representations on a
measure space with a quasi-invariant measure; its unitarity criterion and its strong-continuity
theorem are used for every model of Layer 2. Layer 2 builds the models. The `SU(1,1)` models on the
circle are not defined through the general machinery, because the circle action is a right action
written on angles; 2.1 proves their representation law, unitarity range and Hermitian adjoint
directly, and the general theorems apply through `g • z = z · g⁻¹`. Layer 3 is general: it holds
for any representation on a Hilbert space with a Hilbert basis, and its weight decomposition is
what makes the matrix elements of Layer 4 functions of one variable. Layer 4 computes the
infinitesimal operators of the principal series on the trigonometric basis and derives the
second-order equation of its matrix elements; it is the template that the special-function
roadmaps instantiate. Layer 5 is harmonic analysis on `K\G/K` and needs only Layers 0 and 3; its
`SU(1,1)` example uses the radial part of the Casimir equation of Layer 4.

The harder material is 1.3 (strong continuity, which needs density of compactly supported
continuous functions), 2.2 (invariance of the complementary form), 4.3 (the template equation)
and 5.3 (multiplicity one, which needs Schur's lemma for a commutative `*`-algebra of operators).

## Layer 0: groups in coordinates

### 0.1 `SU(1,1)`

Sources: Vilenkin–Klimyk §6.1.1 (10)–(12), p. 271 (Euler angles), §6.1.2 (1)–(6), p. 272 (Lie
algebra), §6.1.3 (4), p. 274 (Cayley transform), §6.1.4 (2), p. 275 (Haar measure); Miller §5-18
(5.156)–(5.158), pp. 226–227 (coordinates); Dieudonné §8, p. 27 (the real form `SL(2, ℝ)`).

`su11` is a subgroup of `Matrix.SpecialLinearGroup (Fin 2) ℂ` with the subspace topology, `rot`,
`boost` and `boostY` are its one-parameter subgroups, and
`eulerSU11 α t γ = rot α * boost t * rot γ`. Prove:
- **Euler factorization** (`eulerSU11_coe`): the matrix of `g(α, t, γ)` is
  `[[a, b], [conj b, conj a]]` with `a = cosh(t/2) e^{i(α+γ)/2}` and `b = sinh(t/2) e^{i(α−γ)/2}`;
- **Euler angles** (`eulerSU11_surjective_unique`): every `g` is `g(α, t, γ)` with
  `0 ≤ α < 2π`, `t ≥ 0`, `−2π ≤ γ < 2π`, and the angles are unique when `t > 0`;
- **Conversion to the `SU(2)` angles** (`eulerSU11_continuation`): the `SU(2)` middle factor `b_β`
  at `β = it` is `boostY t`, and `k_α b_{it} k_γ = g(α + π/2, t, γ − π/2)`;
- **Cayley transform** (`mem_su11_iff_cayley`): `g ∈ SU(1,1)` exactly when
  `g = C h C⁻¹` for some `h ∈ SL(2, ℝ)`, with `C = [[1, −i], [1, i]]` (`cayleyMatrix`);
- **Haar measure of `SU(1,1)`** (`su11Haar_isHaarMeasure`): the image `su11Haar` of
  `(8π²)⁻¹ sinh t dα dt dγ` on `eulerDomain` is a Haar measure and is right invariant;
- **Lie algebra of `SU(1,1)`** (`su11_lieBasis`): the brackets of `b₁, b₂, b₃`, the
  one-parameter laws `boost (s + t) = boost s * boost t` (and for `boostY`, `rot`), and the
  tangents `b₁, b₂, b₃` at `0`;
- the Euler angles are the KAK decomposition of RepresentationTheory/LieGroups Layer 9 for
  `SU(1,1)` with `K = su11K` and `A = {boost t}`, and the Cayley transform carries `SO(2)` onto
  `su11K` and the diagonal subgroup of `SL(2, ℝ)` onto `{boostY t}`.

The proof of uniqueness reads `cosh(t/2) = |a|`, `(α + γ)/2 = arg a` and `(α − γ)/2 = arg b`
modulo `2π`; the lattice of periods of `(α, γ)` is generated by `(2π, 2π)` and `(2π, −2π)` and
has the stated ranges as a fundamental domain. Invariance of `su11Haar` is the computation of the
Jacobian of left and right translation in Euler angles; uniqueness of Haar measure then gives the
normalization-independent statement.

**Checks.**
- `entryA (rot α) = e^{iα/2}` and `entryB (rot α) = 0`, so `rot α ∈ su11K`.
- `entryA (boost t) = cosh(t/2)` and `entryB (boost t) = sinh(t/2)`; `boost t ∉ su11K` for
  `t ≠ 0`.
- `rot (2π)` is `−1`, `rot (4π)` is `1`: the `γ`-range has length `4π`, and with
  `0 ≤ γ < 2π` (Edmonds's range for rotations) half of `SU(1,1)` is missed.
- `g(α, t, γ)ᵀ = g(γ, t, α)` (used in 5.4).
- `b_t = k_{−π/2} b_{it} k_{π/2}` and `k_α b_{it} k_γ = g(α + π/2, t, γ − π/2)` at
  `(α, t, γ) = (0.7, 1.3, −2.1)` to `10⁻²⁵`; `b_{it}` at `t = 1.3` is
  `[[1.21879 33029, 0.69674 75261 i], [−0.69674 75261 i, 1.21879 33029]]`.
- Negative control: `k_α b_{it} k_γ ≠ g(α, t, γ)`; without the shift by `π/2` the entries `(1, 2)`
  and `(2, 1)` differ by the factors `i` and `−i`.
- For `h = [[2, 3], [1, 2]] ∈ SL(2, ℝ)`, `C h C⁻¹ = [[2 + i, −2i], [2i, 2 − i]]`, with
  `|2 + i|² − |2i|² = 1`.
- Negative control: the reverse conjugation `C⁻¹ h C = [[4, i], [i, 0]]` is not in `SU(1,1)`.
- `su11Haar {g(α, t, γ) : t ≤ T} = cosh T − 1`; at `T = 1` this is `0.54308 06348`.
- Negative control: the density `sin t` of the `SU(2)` formula is negative for `π < t < 2π`, so
  it defines no measure on the Euler domain.
- `[b₁, b₂] = −b₃`; the sign `+b₃` of `su(2)` fails.
- Negative control (erratum E06.1.03): `−b₁² + b₂² + b₃²` does not commute with `b₁`, while
  `b₁² + b₂² − b₃²` is central in the enveloping algebra.

*Needs:* Mathlib `Matrix.SpecialLinearGroup`, `MeasureTheory.Measure.IsHaarMeasure`;
RepresentationTheory/LieGroups Layer 9 for the comparison bullet.

### 0.2 Solvable and nilpotent groups in coordinates

Sources: Vilenkin–Klimyk §1.2.6 (1)–(3), pp. 62–63 (left and right Haar measures, modular
function), p. 66, Example 5 (triangular groups; erratum E01.2.08), §1.1.8, p. 50, Example 2
(Heisenberg group), §5.1.1 (5.1.1.1), p. 207 (the triangular group of order three);
Klimyk–Vilenkin §1.6 (14), (15), p. 160 (triangular and oscillator groups; erratum E01.1.11),
§2.8, p. 166 (the `ax + b` group); Wawrzyńczyk §2.8, Example 2, pp. 132–133 (Heisenberg group).

The `ax + b` group is `AxB`, pairs `(a, b)` with `a > 0` and `(a, b)(a', b') = (aa', ab' + b)`.
Prove:
- **Haar measures of the `ax + b` group** (`axb_haar`): `a⁻² da db` is left invariant,
  `a⁻¹ da db` is right invariant, and `a⁻² da db` is not right invariant;
- **Haar measure of the Heisenberg group** (`heisenberg_haar`): Lebesgue measure in the
  coordinates of `TauCeti.HeisenbergGroup.equivProd` is left and right invariant;
- **Oscillator group law** (`oscillatorMatrix_mul`): the matrices `s(w, α, δ)` multiply by
  `(w₁ + e^{−iα₁} w₂, α₁ + α₂, δ₁ + δ₂ − Im(e^{−iα₁} conj w₁ w₂)/4)`;
- `AxB`, `TauCeti.HeisenbergGroup ℝ` and the oscillator group are locally compact topological
  groups in their coordinate topologies, and the modular function of `AxB` is `(a, b) ↦ a`, in
  the convention `Measure.map (· * g) μ_L = Δ(g) μ_L`, agreeing with
  `MeasureTheory.Measure.modularCharacter`;
- the oscillator group has the bi-invariant Haar measure `r dr dϑ dα dδ` for `w = 2r e^{iϑ}`, and
  the triangular group `g(a, b, d, τ) = [[1, a, b], [0, e^τ, d], [0, 0, 1]]` of Vilenkin–Klimyk
  §5.1.1 has the bi-invariant Haar measure `e^{−τ} da db dd dτ`.

**Checks.**
- The left measure `a⁻² da db` of `[1, 2] × [0, 1]` is `1/2`, and of its right translate by
  `(2, 0)`, the box `[2, 4] × [0, 1]`, it is `1/4`; so `Measure.map (· * (2, 0)) μ_L = 2 μ_L`.
- Negative control: the right measure `a⁻¹ da db` is not left invariant: left translation by
  `(2, 0)` multiplies it by `2`.
- The Heisenberg commutator `⁅(1, 0, 0), (0, 1, 0)⁆ = (0, 0, 1)`, which is central.
- In the corrected oscillator form, `s(1, 0, 0)² = s(2, 0, 0)`.
- Negative control (erratum E01.1.11): with the printed entry `iδ − |w|²/2` the product
  `s(1, 0, 0)²` has `(2, 3)` entry `−1`, so `w = 2`, but `(1, 3)` entry `−5/4`, whose real part
  should be `−|w|²/2 = −2`: the printed set is not closed under multiplication.
- The triangular group is unimodular: left and right Haar densities in `(a, b, d, τ)` are both
  `e^{−τ}`.

*Needs:* Mathlib `withDensity`, `MeasureTheory.Measure.modularCharacter`; Tau Ceti
`TauCeti.HeisenbergGroup`.

### 0.3 Motion groups

Sources: Vilenkin–Klimyk §4.1.1 (1)–(8), pp. 165–166 (`ISO(2)`); Klimyk–Vilenkin §1.5 (12)–(13),
p. 159 (Cartan motion groups), §2.9 (33)–(35), pp. 166–167 (`ISO(1,1)`); Dieudonné §8, (III),
pp. 26–27; Wawrzyńczyk §5.3, Example 1(b), p. 225.

`MotionGroup n` is `M(n) = ℝⁿ ⋊ SO(n)`: pairs `(a, k)` of a vector of `EuclideanSpace ℝ (Fin n)`
and a matrix of `SOn n` (Mathlib's `Matrix.specialOrthogonalGroup`) acting by `rotE`, with
`(a, k)(a', k') = (a + k a', k k')` and the topology of `ℝⁿ × SO(n)`; it is the matrix group
`[[k, a], [0, 1]]`, and `ISO2` is `M(2)`. `ISO11` is `ISO(1,1) = ℝ² ⋊ SO₀(1,1)`: pairs `(a, s)`
with `(a, s)(a', s') = (a + Λ_s a', s + s')` for the boost `lorentzBoost s`. The group laws are
proved in `Coordinates.lean`. Mathlib, Tau Ceti and the roadmaps on main have these groups at most
algebraically (Tau Ceti's affine isometry group as a semidirect product, without topology). Prove:
- **`M(n)` is a topological group** and **`M(n)` is locally compact** (instances of
  `Coordinates.lean`), and the same for `ISO(1,1)`;
- **Haar measure of `M(n)`; unimodularity** (`motionHaar_isHaarMeasure`): for the Haar probability
  measure `ν` of `SO(n)`, `motionHaar n ν = da dk` is a Haar measure of `M(n)` and is right
  invariant;
- **Haar measure of `ISO(1,1)`; unimodularity** (`iso11Haar_isHaarMeasure`): Lebesgue measure
  `da₁ da₂ ds` is a Haar measure and is right invariant;
- **Polar decomposition of `M(n)`, `n ≥ 2`** (`motionGroup_polar`): every `g` is
  `(0, k₁)(r e₁, 1)(0, k₂)` with `r = |g.a|`, and `r ≥ 0` is determined by `g`; on `M(2)` this is
  the polar form `g(r, φ; α)` with its product law (Vilenkin–Klimyk §4.1.1 (2)–(4), p. 165);
- the Lie algebra basis `b₁ = E₁₃`, `b₂ = E₂₃`, `b₃ = E₂₁ − E₁₂` of `iso(2)` and its brackets
  `[b₁, b₂] = 0`, `[b₂, b₃] = b₁`, `[b₃, b₁] = b₂` (Vilenkin–Klimyk §4.1.1 (6)–(8), p. 166).

**Checks.**
- For `M(2)` the left and right Haar densities in `(a₁, a₂, θ)` are both `1`; so are those of
  `ISO(1,1)` in `(a₁, a₂, s)`.
- The polar product of `g(r₁, 0; 0)` and `g(r₂, φ₂; 0)` has `r² = r₁² + r₂² + 2 r₁ r₂ cos φ₂`.
- `Λ_s` preserves `x² − y²` but not `x² + y²`: `Λ_1 (1, 0) = (cosh 1, sinh 1)` has
  `cosh² 1 − sinh² 1 = 1` and `cosh² 1 + sinh² 1 = cosh 2 = 3.76219 56911`.
- Negative control: `M(1) = ℝ`, so the rotation group is trivial and the motion group is
  abelian; `(−1, 1)` has no polar decomposition with `r ≥ 0`, and the Gel'fand-pair property of
  5.4 holds there for the trivial reason, not through 5.1.

*Needs:* Mathlib `Matrix.specialOrthogonalGroup`, `Matrix.toEuclideanLin`,
`MeasureTheory.Measure.IsHaarMeasure`.

### Examples

- The `ax + b` group is not unimodular; its modular function is `(a, b) ↦ a`.
- `SU(1,1)`, `M(2)`, `ISO(1,1)`, the Heisenberg, oscillator and triangular groups are unimodular,
  with the Haar measures above.

### Dependencies

Mathlib (Haar measure, `withDensity`, special linear groups); Tau Ceti (`TauCeti.HeisenbergGroup`);
RepresentationTheory/LieGroups Layer 9.

## Layer 1: `G`-spaces and multiplier representations

### 1.1 Quasi-invariant measures and the Radon–Nikodym cocycle

Sources: Wawrzyńczyk §1.7 (1.7.1)–(1.7.3), Propositions 1.7.1–1.7.2, pp. 85–86; Vilenkin–Klimyk
§1.2.6, p. 62 (relatively invariant measures), p. 64 (measures on `G/H`; errata E01.2.06,
E01.2.07).

For a group `G` acting measurably on `(X, μ)`, `IsQuasiInvariantWith μ ρ` says that
`Measure.map (g • ·) μ = μ.withDensity (ρ g)` for every `g`. Prove:
- **Radon–Nikodym cocycle** (`IsQuasiInvariantWith.cocycle`): for σ-finite `μ` and measurable
  densities, `ρ(gh, x) = ρ(g, x) ρ(h, g⁻¹ • x)` for `μ`-almost every `x`;
- `ρ(1, ·) = 1` almost everywhere, `ρ(g, ·) > 0` almost everywhere, and `μ` and its translates
  are mutually absolutely continuous;
- for compact `K ≤ G` with `G` locally compact, the image of a Haar measure of `G` on `G/K` is a
  `G`-invariant Radon measure, and any two `G`-invariant Radon measures on `G/K` are proportional;
- the examples fixed for later use: the circle under `SU(1,1)` acting by `g • z = z · g⁻¹`, with
  `ρ(g, z) = |b z + conj a|⁻²` (2.1); the disc under `SU(1,1)` with the invariant measure
  `(1 − |z|²)⁻² dA` and `ρ = 1`; the half-line under `AxB` with `ρ = 1` for `dx/x` (2.4); the line
  under the Heisenberg group with `ρ = 1` (2.5); the upper half-plane under `SL(2, ℝ)` acting by
  Möbius maps, with `ρ(g, z) = |a − c z|⁻⁴` for Lebesgue measure.

**Checks.**
- For `G` acting on itself by left multiplication and a left Haar measure, `ρ = 1`.
- For `ℝ` acting on itself by translation and `μ = eˣ dx`, `ρ(g, x) = e^{−g}`, constant in `x`;
  the cocycle identity is `e^{−(g+h)} = e^{−g} e^{−h}`.
- For the circle, `∫ |b e^{iθ} + conj a|⁻² dθ/2π = 1` (Poisson integral) for every `g`.
- On the upper half-plane with `g = [[2, 3], [1, 2]]` and `z = 0.4 + 1.3i`,
  `ρ(g, z) = |2 − z|⁻⁴ = 0.05536 33218`.
- Negative control: `|c z + d|⁻⁴ = 0.01801 72064` at the same point, the Jacobian of `g` instead of
  `g⁻¹`, is not the density.

*Needs:* Mathlib `withDensity`, `MeasureTheory.Measure.rnDeriv`, quotient measures.

### 1.2 Multiplier cocycles and the representation law

Sources: Vilenkin–Klimyk §2.1.6 (4), p. 80, Example 5; Wawrzyńczyk §2.2 (2.2.7)–(2.2.11),
pp. 107–108; Miller §1-3, pp. 16–17 (local multiplier representations).

Prove:
- **Representation law** (`multiplierAction_law_iff`): `multiplierAction α` satisfies
  `T(1) = id` and `T(gh) = T(g) T(h)` on all functions `X → ℂ` exactly when `α` is a multiplier
  cocycle (`IsMultiplierCocycle`); the forward direction takes `f ≡ 1`;
- the same formula defines representations on the spaces of continuous, smooth (for smooth
  actions and multipliers) and polynomial functions it preserves, and on `C(X)` with the sup norm
  for compact `X` and continuous `α`, where it is continuous in the strong operator topology.

**Checks.**
- `α ≡ 1` is a cocycle and gives the shift representation `f ↦ f(g⁻¹ • ·)`.
- For a character `χ` of `G`, `α(g, x) = χ(g)` is a cocycle.
- Negative control: `α ≡ 0` satisfies the product identity but not `α(1, x) = 1`, and gives
  `T = 0`, which is not a representation.

*Needs:* nothing beyond the group action.

### 1.3 Unitarity, strong continuity and the quasi-regular representation

Sources: Wawrzyńczyk §2.2 (2.2.12)–(2.2.13), Proposition 2.2.4, pp. 108–109; Vilenkin–Klimyk
§2.1.6, Examples 1–2, pp. 77–78 (regular and quasi-regular representations); erratum E02.1.01.

`multiplierRep μ α` is the continuous representation on `L²(X, μ)` that agrees almost everywhere
with `multiplierAction α`, when one exists. Prove:
- **Unitarity criterion** (`exists_isUnitary_multiplierAction_iff`): for a measurable cocycle
  and quasi-invariant σ-finite `μ`, a unitary representation realizing the formula exists exactly
  when `|α(g, x)|² = ρ(g, x)` almost everywhere;
- **The multiplier representation** (`multiplierRep_spec`): under that condition
  `multiplierRep μ α` realizes the formula and is unitary;
- **Strong continuity** (`continuous_multiplierRep_apply`): for a continuous action of a locally
  compact group on a locally compact Hausdorff space with a regular measure and a jointly
  continuous unitary multiplier, every orbit `g ↦ T(g) f` is continuous;
- **Quasi-regular representation** (`isMultiplierCocycle_sqrt`): for a pointwise Radon–Nikodym
  cocycle `ρ`, `√ρ` is a multiplier cocycle with `|√ρ|² = ρ`, so
  `(π(g) f)(x) = ρ(g, x)^{1/2} f(g⁻¹ • x)` is unitary;
- **Left regular representation** (`multiplierRep_one_eq_leftRegular`): for `G` acting on itself
  with a left-invariant measure, `multiplierRep μ 1` is `MeasureTheory.Measure.leftRegular`.

The unitarity criterion is the change of variables `x = g • y`. Strong continuity: by unitarity
it suffices to test on the dense subspace of continuous compactly supported `f`; on such `f`,
`T(g) f` is supported in `V · supp f` for `g` in a compact neighbourhood `V`, and dominated
convergence applies to the jointly continuous integrand.

**Checks.**
- For the circle model of 2.1 the condition reads `|u|^{4 Re τ} = |u|⁻²` with
  `u = b e^{iθ} + conj a`, since `|u|⁻²` is the Jacobian of `θ ↦ θ · g`; that is, `Re τ = −1/2`.
- For `μ = dx/x` on `(0, ∞)` and `AxB`, `ρ = 1`, so every multiplier of modulus `1` is unitary.
- Negative control: `α(g, x) = ρ(g, x)` (no square root) satisfies the cocycle identity but not
  the unitarity condition unless `ρ = 1`.

*Needs:* Mathlib `Lp`, `MeasureTheory.Measure.Regular`, density of continuous compactly
supported functions in `L²`; Tau Ceti `MeasureTheory.Measure.leftRegular`.

### 1.4 Cohomologous multipliers

Sources: Wawrzyńczyk §2.2, pp. 107–108; Vilenkin–Klimyk §2.2.5 (1), p. 87 (equivalent
representations).

`coboundaryTwist β α g x = β(x) α(g, x) / β(g⁻¹ • x)`. Prove:
- **Cohomologous multipliers** (`multiplierAction_coboundaryTwist`): multiplication by a
  nowhere-vanishing `β` intertwines `multiplierAction α` with
  `multiplierAction (coboundaryTwist β α)`, the twist of a cocycle is a cocycle, and the twist has
  the modulus of `α` when `|β| = 1`;
- for measurable `β` with `|β| = 1`, multiplication by `β` is a unitary equivalence between
  `multiplierRep μ α` and `multiplierRep μ (coboundaryTwist β α)`.

**Checks.**
- `coboundaryTwist 1 α = α`.
- For `G = ℝ` acting on `ℝ` by translation, `α = 1` and `β(x) = e^{ix}`, the twist is
  `e^{ig}`: the shift representation is equivalent to its tensor product with the character
  `g ↦ e^{ig}`.
- Negative control: for `|β| ≠ 1`, e.g. `β(x) = eˣ`, the twisted multiplier `e^{g}` is not unitary
  on `L²(ℝ, dx)`; multiplication by `β` is then not bounded.

*Needs:* 1.2–1.3.

### Examples

- The left regular representation of `AxB` with left Haar measure is the multiplier
  representation with `α = 1`; with right Haar measure it is the multiplier representation with
  `α(g, x) = Δ(g)^{1/2}`.

### Dependencies

Layer 0; Mathlib `Lp`, `withDensity`; Tau Ceti `MeasureTheory.Measure.leftRegular`;
NoncompactQuantumSymmetry M1 for the comparison on transitive spaces.

## Layer 2: function-space models

### 2.1 The principal series of `SU(1,1)` on the circle

Sources: Vilenkin–Klimyk §6.4.1 (1)–(5), pp. 298–299, §6.4.5 (1)–(3), pp. 306–307 (Hermitian
adjoint), §6.4.6 (1)–(4), pp. 307–308 (unitarity), §2.1.6, Example 5, p. 80; Klimyk–Vilenkin
§2.2 (23), p. 163; Miller §5-18 (5.159)–(5.167), pp. 227–232; Wawrzyńczyk §2.2, Examples 2–3,
pp. 109–111.

`circleAct g` is the right action `e^{iθ} ↦ (a e^{iθ} + conj b)/(b e^{iθ} + conj a)` on angles,
`principalAction τ e g f θ = principalMultiplier τ e g θ · f(circleAct g θ)`, and
`principalSeries τ e` is the continuous representation on `L²(haarAddCircle)` realizing it.
Prove:
- **The circle as an `SU(1,1)`-space** (`circleAct_mul_map`): `circleAct` is a right action, and
  `Measure.map (circleAct g) haarAddCircle` has density `|a − b e^{iθ}|⁻²`;
- **Principal series: representation law** (`principalAction_mul`);
- **Principal series on `L²`** (`principalSeries_spec`): for every `τ ∈ ℂ` and `e` the formula
  defines a representation on `L²` with continuous orbits;
- **Unitarity of the principal series** (`principalSeries_isUnitary_iff`): unitary exactly when
  `Re τ = −1/2`;
- **Hermitian adjoint** (`inner_principalSeries`):
  `⟪T_{(τ,ε)}(g) f, h⟫ = ⟪f, T_{(−conj τ − 1, ε)}(g⁻¹) h⟫`;
- **Weights** (`principalSeries_rot`): `T(k_α) e_m = e^{imα} e_m` for `e_m = e^{inθ}`, `m = n − ε`,
  `k_{2π} = −1` and `T(−1) = (−1)^{2ε}`;
- **The fixed conjugacy `SL(2, ℝ) ≅ SU(1,1)`** (`sl2rToSU11_spec`): `sl2rToSU11` is a bijective
  homomorphism, conjugation by NoncompactQuantumSymmetry M4's `C₀`, and maps `k_t` to `k_{2t}`;
- **Agreement with normalized parabolic induction** (`principalAction_compactPicture`): with
  `(W F)(k_t) = e^{iet} F(π − 2t)` (`compactTransport`), `W` carries
  `principalAction τ e (sl2rToSU11 h)` to `f ↦ r(h⁻¹k_t)^{−(1+ν)} f(θ(h⁻¹k_t))`,
  `ν = −(2τ + 1)`, where `h⁻¹k_t` has first column `r (cos θ, sin θ)`, and `W F` has parity `e`;
- `W` is unitary from `L²(𝕋)` onto the functions of parity `e` in `L²(SO(2))`, so
  `principalSeries τ e` is unitarily equivalent to M4's normalized induced representation
  `I_(e, ν)` in its compact picture, with `ν = −(2τ + 1)`. Consumed from M4 through this
  dictionary, with its hypotheses: for `Re τ = −1/2` the irreducibility (except at `τ = −1/2`,
  `e = 1`) and the equivalence `T_{(τ,ε)} ≅ T_{(−τ−1,ε)}` (its `ν ↔ −ν`), and the splitting of
  `principalSeries (−1/2) 1` into `D_1^+ ⊕ D_1^−` on the subspaces spanned by the `e_m` with
  `m ≥ 1/2` and with `m ≤ −1/2`.

The `L²` operator exists for every `τ` because the multiplier is bounded and the Jacobian of
`circleAct g` is bounded above and below. Unitarity at `Re τ = −1/2` is 1.3; the converse tests
`f = 1`. The adjoint formula is the change of variables `θ ↦ circleAct g θ` with the density of
the first bullet.

**Checks.**
- For `g = g(0.3, 0.9, 1.1)` and `f = e^{2iθ} + 3e^{−iθ} + 1` (`‖f‖² = 11`):
  `‖T_{(−1/2 + 0.37i, 1/2)}(g) f‖² = 11` and `‖T_{(0.1 + 0.37i, 1/2)}(g) f‖² = 12.01988 80665`.
- Negative control: at `τ = 0`, `e = 0`, `‖T(g) 1‖² = 1` for every `g`, yet
  `‖T(g) f‖² = 11.49378 19663 ≠ 11`: preserving the norm of constants does not make the
  representation unitary.
- At `τ = 0.23 + 0.4i`, `α = 0.7`: `T(k_α) e_m / e_m = e^{imα}` at `m = 3` (`ε = 0`,
  `−0.50485 + 0.86321 i`) and at `m = 5/2` (`ε = 1/2`, `−0.17825 + 0.98399 i`); for `ε = 1/2`,
  `T(k_{2π}) = −1`.
- Negative control: the Vilenkin–Klimyk labels `e^{−ikθ}` have `T(k_α) e^{−ikθ} = e^{−i(k+ε)α}`;
  reading `k` as `m` reverses the sign of every weight.
- Negative control: the adjoint parameter is `−conj τ − 1`, not `−τ − 1`; at `τ = 0.27 + 0.61i`,
  `e = 0`, the `g` and `f` above and `h = 2e^{iθ} − e^{−3iθ} + i/2` the two give
  `⟪f, T(g⁻¹) h⟫ = −1.19620 − 0.38632 i` and `−1.99828 − 0.47504 i`, and only the first equals
  `⟪T(g) f, h⟫`.
- `T_{(τ, ε)}(k_α)` is a rotation of the circle by `α` up to the factor `e^{−iεα}`.
- For `h = [[2, 3], [1, 2]]`, `sl2rToSU11 h` has `a = 2 − i`, `b = 2i`.
- For that `h`, `F = e^{2iθ} + 3e^{−iθ} + 1`, `t = 0.81` and `τ = −1/2 + 0.37i`, both sides of
  `principalAction_compactPicture` are `−0.31332 53614 + 2.79503 57546 i` at `e = 0` and
  `−1.70516 84444 − 2.23669 35927 i` at `e = 1` (`r = 1.09837 03109`,
  `θ = 2.37859 25937`).
- Negative control: with `ν = 2τ + 1` in place of `−(2τ + 1)` the right side at `e = 0` is
  `0.07657 65538 + 2.81150 02548 i`; `ν` and `−ν` give equivalent representations, but only
  `−(2τ + 1)` makes `W` itself the intertwiner.

*Needs:* 1.1–1.3; Mathlib `haarAddCircle`, `fourierLp`; NoncompactQuantumSymmetry M4 (the fixed
conjugacy, the compact picture and the consumed facts).

### 2.2 The complementary series

Sources: Vilenkin–Klimyk §6.4.6 (5)–(11), pp. 308–309; Miller §5-18 (5.168)–(5.170),
pp. 232–234.

For `−1 < τ < 0` and `ε = 0`, `complementaryWeight τ n = Γ(τ − n + 1)/Γ(−τ − n)`, the weight of
Vilenkin–Klimyk's invariant form `Σₙ w(n) conj(f̂ n) ĥ n`. The invariant form of the
complementary series, its positivity, its Hilbert completion and the unitary representation on
it are NoncompactQuantumSymmetry M4's, and their compact eigenvalues are its M5's; this
subsection owns the weights and the dictionary. Prove:
- **Complementary weights** (`complementaryWeight_pos`): the weights are positive and even in `n`
  for `−1 < τ < 0`, and all equal `1` at `τ = −1/2`;
- **Agreement with the compact eigenforms of NoncompactQuantumSymmetry M5**
  (`complementaryWeight_ratio`): with `ν = −(2τ + 1)`,
  `w(j)/w(0) = ∏_{k=1}^{j} (2k − 1 − ν)/(2k − 1 + ν)`, its eigenvalue `a_{±2j}` on the vectors of
  compact weight `±2j`;
- through `W` of 2.1, `w(0)⁻¹ Σₙ w(n) conj(f̂ n) ĥ n` is M4's complementary form at
  `ν = −(2τ + 1)`, normalized at the constant vector, so the completion of the smooth functions in
  it carries M4's complementary series; its invariance, completion and irreducibility are consumed
  from M4.

The ratio is the recursion `w(n + 1)/w(n) = (n + 1 + τ)/(n − τ)` of the Gamma function, and
`2k − 1 − ν = 2(k + τ)`, `2k − 1 + ν = 2(k − 1 − τ)`. `w(n)` grows like `|n|^{2τ+1}`.

**Checks.**
- `w(−0.2, 0) = 0.25359 82026` and `w(−0.2, ±1) = 1.01439 28104`.
- `w(−0.9, 0) = 8.90253 80657` and `w(−0.9, ±1) = 0.98917 08962`.
- Negative control: `w(0.3, 0) = −0.20741 88997 < 0`, so the form is indefinite outside
  `−1 < τ < 0`.
- At `τ = −0.3` (`ν = −0.4`): `w(1)/w(0) = 7/3 = a_2(−0.4)` and
  `w(5)/w(0) = 4.38970 63503`; at `τ = −0.8` (`ν = 0.6`): `w(2)/w(0) = 1/6`.
- Negative control: the product at `ν = 2τ + 1` is the reciprocal, `3/7` at `τ = −0.3`, `j = 1`.

*Needs:* 2.1; Mathlib `Real.Gamma`; NoncompactQuantumSymmetry M4 and M5.

### 2.3 The holomorphic discrete series

Sources: Miller §5-18 (5.171)–(5.176), pp. 234–236 (Bargmann space); Vilenkin–Klimyk §6.4.6,
pp. 309–310 (analytic model; errata E06.4.04, E06.4.05); Klimyk–Vilenkin §2.2 (21)–(22),
pp. 162–163.

For `k ≥ 2`, `bergmanMeasure k = ((k − 1)/π) (1 − |z|²)^{k−2} dA` on the unit disc,
`discreteAction k g h z = (b z + conj a)^{−k} h(z · g)` and
`antiDiscreteAction k g h z = conj((b z + conj a)^{−k}) h(z · g)`. Prove:
- **Holomorphic discrete series** (`discreteAction_isometry`): `diskAct g` maps the disc to
  itself, the action is a representation on functions on the disc, preserves holomorphy and
  preserves the weighted Bergman norm;
- **Antiholomorphic discrete series** (`antiDiscreteAction_spec`): `antiDiscreteAction k g h` is
  `conj ∘ discreteAction k g (conj ∘ h)`, and for `k ≥ 2` and antiholomorphic `h` the action is a
  representation on functions on the disc, preserves antiholomorphy and preserves the weighted
  Bergman norm;
- **Bergman norms and kernel** (`bergman_monomial_kernel`): `‖zʲ‖² = C(k − 1 + j, j)⁻¹` and the
  reproducing kernel is `Σⱼ C(k − 1 + j, j) (z conj w)ʲ = (1 − z conj w)^{−k}`;
- **Weights of the discrete series** (`discreteAction_rot`): `T(k_α) zʲ = e^{i(k/2 + j)α} zʲ` and
  `T(k_α) conj(z)ʲ = e^{−i(k/2 + j)α} conj(z)ʲ`;
- the holomorphic functions of finite norm form a Hilbert space `A²_k` with orthonormal basis
  `C(k − 1 + j, j)^{1/2} zʲ`, the action is a strongly continuous unitary representation on it,
  and so is the conjugate action on `conj(A²_k)`. Their weights `m = ±(k/2 + j)` are M4's compact
  weights `±(k + 2j)`, those of `D_k^±`. Through `sl2rToSU11` and the lowest-weight vector `1`,
  `A²_k` is M4's `D_k^+` and `conj(A²_k)` its `D_k^−`; their irreducibility and the comparison
  with M6.C's half-plane models are consumed from NoncompactQuantumSymmetry.

**Checks.**
- `bergmanMeasure k` is a probability measure (`j = 0`).
- `‖z‖² = 1/2` for `k = 2`; `‖z³‖² = 1/10` for `k = 3`; `‖z‖² = 1/5` for `k = 5`.
- For `g = g(0.3, 0.8, 1.2)` and `h = 1 + 2z − z³`, `k = 3`: `‖T(g) h‖² = ‖h‖² = 2.43333 33333`.
- Negative control: the exponent `+k` in place of `−k` gives `‖·‖² = 12.92483 64196` for the same
  data.
- At `z = 0.3 + 0.2i`, `w = −0.1 + 0.5i`, `k = 3`: the kernel is `1.01356 85446 − 0.61087 26358 i`.
- At `k = 3`, `j = 2`, `α = 0.7`: `T(k_α) conj(z)² = e^{−2.45i} conj(z)²`, with
  `e^{−2.45i} = −0.77023 12540 − 0.63776 47021 i`.
- Negative control: conjugating `h` without conjugating the multiplier gives the weight
  `k/2 − j`, here `e^{−0.35i} = 0.93937 27128 − 0.34289 78075 i`; these weights are unbounded in
  both directions, so that formula is not `D_k^−`.

*Needs:* 1.2; Mathlib `DifferentiableOn`, `Metric.ball`, `lintegral`; NoncompactQuantumSymmetry M4
and M6.C.

### 2.4 The `ax + b` group on the half-line

Sources: Klimyk–Vilenkin §2.8 (30)–(32), p. 166 (erratum E01.2.04); Vilenkin–Klimyk §1.2.6,
p. 66, Example 5.

`AxB` acts on `ℝ` by `g • x = x / a`, preserving `halfLineMeasure = dx/x` on `(0, ∞)`, and
`axbRep λ` is the multiplier representation with `axbCocycle λ g x = e^{iλbx}`, so
`(T_λ(a, b) f)(x) = e^{iλbx} f(ax)`. Prove:
- **Representations of the `ax + b` group** (`axbRep_spec`): for real `λ, λ' ≠ 0`, `T_λ` realizes
  the formula, is unitary and is irreducible, and `T_λ ≅ T_λ'` exactly when `λ λ' > 0`;
- `T_λ` is strongly continuous for the coordinate topology of `AxB`;
- every irreducible strongly continuous unitary representation of `AxB` is equivalent to `T_1`,
  to `T_{−1}`, or to a character `(a, b) ↦ a^{is}` (consumed from NoncompactQuantumSymmetry M2,
  applied to `ℝ ⋊ ℝ_{>0}` with the two open orbits `(0, ∞)` and `(−∞, 0)` of the dual action).

Irreducibility: an invariant closed subspace is invariant under multiplication by all
`e^{iλbx}`, hence (the span being dense in `L^∞`) is `L²(E)` for a measurable `E`, which dilation
invariance forces to be null or conull. The dilation `f ↦ f(c ·)`, `c > 0`, intertwines `T_λ` and
`T_{λc}`.

**Checks.**
- `T_1(a, b) T_1(a', b') = T_1(aa', ab' + b)` at `x = 0.9`, `f(x) = x e^{−x}`.
- Negative control: with the composed order `(a', b')(a, b)` the law fails: for
  `(a, b) = (1.7, 0.6)`, `(a', b') = (0.8, −1.3)` the two sides differ by `0.25055` in modulus.
- Negative control: `T_0` is the dilation representation of `ℝ_{>0}` on `L²(dx/x)`, which is
  reducible (the Mellin transform diagonalizes it).

*Needs:* 1.2–1.3; NoncompactQuantumSymmetry M2 for the classification bullet.

### 2.5 The Schrödinger representation

Sources: Wawrzyńczyk §2.8, Example 2 and Proposition 2.8.3, pp. 132–133 (erratum W84-E02.8.02);
Vilenkin–Klimyk §1.1.8, Example 2, p. 50.

The Heisenberg group acts on `ℝ` by `g • x = x − g.x`, and `schrodinger` is the multiplier
representation with `schrodingerCocycle g x = e^{i(z + y x)}`, so
`(U(g) f)(x) = e^{i(z + yx)} f(x + g.x)`. Prove:
- **Schrödinger representation** (`schrodinger_spec`): it realizes the formula and is unitary;
- **Fourier dictionary** (`fourier_schrodinger`): for integrable `f` and Mathlib's
  `𝓕 f(ξ) = ∫ e^{−2πivξ} f(v) dv`, `𝓕(U(g) f)(ξ) = e^{i(2πxξ + z − xy)} 𝓕 f(ξ − y/(2π))`;
- with `p = 2πξ`, `f ↦ 𝓕 f(p/(2π))` is `√(2π)` times a unitary map intertwining `U` with
  NoncompactQuantumSymmetry M2's `π_1`, which in the native coordinates of
  `TauCeti.HeisenbergGroup` is `π_1(x, y, z) φ(p) = e^{i(px + z − xy)} φ(p − y)`. Its strong
  continuity, its central character `z ↦ e^{iz}`, its irreducibility and the classification of
  the irreducibles with that central character are consumed from M2 through this dictionary;
- its space of smooth vectors (in the sense of SmoothBanachRepresentations Layer 2) is the
  Schwartz space;
- it is OperatorAlgebraDynamics D1.CentralTwists' twisted shift for `G = ℝ`.

**Checks.**
- `U(p) V(q) U(p)⁻¹ V(q)⁻¹ = e^{ipq}` for `U(p) = U(g(p, 0, 0))`, `V(q) = U(g(0, q, 0))`.
- The differentials are `d/dx`, `ix` and `i` on the Schwartz space.
- Negative control (erratum W84-E02.8.02): the printed `e^{iz} e^{−iyx} f(x + g.x)` has
  `U(g) U(g') U(gg')⁻¹ = e^{−2i g.x g'.y}`, not `1`.
- For `g = (0.7, −1.1, 0.4)`, `f(v) = e^{−v²/2}(1 + v)` and `ξ = 0.23`, both sides of
  `fourier_schrodinger` are `0.14854 68692 + 0.22397 31637 i`.
- Negative control: the shift `ξ + y/(2π)` in place of `ξ − y/(2π)` gives
  `−0.68675 87947 + 2.40215 71458 i` at the same data.

*Needs:* 1.2–1.3; Mathlib `Real.fourier_real_eq_integral_exp_smul`; NoncompactQuantumSymmetry M2;
SmoothBanachRepresentations Layer 2.

### 2.6 Sphere models of the motion groups

Sources: Vilenkin–Klimyk §4.1.2 (1)–(9), pp. 166–167; Klimyk–Vilenkin §2.7 (27)–(29),
pp. 165–166; Miller §3-7 (3.48)–(3.51), p. 70, §3-8 (3.52)–(3.54), pp. 71–72.

For `R > 0` and `g = (a, k)` in `MotionGroup n`, `(T_R(g) f)(ξ) = e^{iR⟨a, ξ⟩} f(k⁻¹ ξ)` on
`L²(S^{n−1})` (`motionAction`). Prove:
- **Sphere model: representation law** (`motionAction_mul`): `T_R(gh) = T_R(g) T_R(h)` and
  `T_R(1) = 1` on functions;
- **Sphere model: unitarity** (`lintegral_motionAction`) for the surface measure;
- **Irreducibility of the sphere models**: for `n ≥ 2` and `R > 0`, `T_R` is a strongly continuous
  irreducible unitary representation of `M(n)`, and `T_R ≅ T_R'` only for `R = R'`. For `n ≥ 4`
  this is a target here: an invariant closed subspace is invariant under multiplication by the
  functions `ξ ↦ e^{iR⟨a, ξ⟩}`, whose span is dense in `C(S^{n−1})` by Stone–Weierstrass, and so
  is `L²(E)` for a rotation-invariant `E`, which transitivity of `SO(n)` makes null or conull;
- for `n = 2, 3`, `M(2) = (ℝ² ⋊ Spin(2))/{±1}`, which is NoncompactQuantumSymmetry's
  `E(2) = Δ/{±1}`, and `M(3) = (ℝ³ ⋊ SU(2))/{±1}`; `T_R` is the pullback of its Euclidean
  adapters' nonzero-radius irreducibles `T_(R, 0)` and `S_(R, 0)` (radius `R`, trivial on `−1`),
  whose irreducibility and inequivalence are consumed from its M6 and M2;
- the matrix elements of `T_R` on `M(2)` in the basis `e^{inθ}` are
  `i^{m−n} J_{m−n}(R r) e^{…}` (the identification is owned by the sibling roadmap on Euclidean
  motion groups and Bessel functions).

**Checks.**
- On `M(2)`, with the normalized measure `dθ/2π` on the circle (Mathlib's surface measure is
  `2π` times it), `⟪e^{2iθ}, T_R(r e₁, 1) e^{−iθ}⟫` at `R = 1.7`, `r = 0.8` is
  `−0.04662 03227 i = i³ J₃(1.36)`.
- These matrix elements satisfy the Bessel equation with Casimir eigenvalue `−R²`.
- Negative control: for `n = 1`, `S⁰ = {±1}`, the rotation group is trivial and `T_R` splits into
  the two characters `a ↦ e^{±iRa}`: irreducibility needs `n ≥ 2`.

*Needs:* 0.3, 1.2; Mathlib `MeasureTheory.Measure.toSphere`, `Complex.besselJ`;
NoncompactQuantumSymmetry M2, M4.TypeI and M6.

### Examples

- The unitarity range of the `SU(1,1)` multiplier representations on the circle is the line
  `Re τ = −1/2`; the complementary interval `−1 < τ < 0` for `ε = 0` is unitary only in
  NoncompactQuantumSymmetry M4's complementary form (2.2).
- `principalSeries (−1/2) 0` contains the constant function as its unique `K`-fixed line.

### Dependencies

Layers 0–1; NoncompactQuantumSymmetry M2, M4, M4.TypeI, M5, M6 and M6.C.

## Layer 3: matrix elements in infinite dimension

### 3.1 Matrix elements

Sources: Vilenkin–Klimyk §2.1.2 (2)–(4), pp. 71–72; Wawrzyńczyk §2.6 (2.6.1), pp. 124–126;
Miller §3-6, pp. 67–68.

`matrixElement π e m' m g = ⟪e m', π g (e m)⟫ = D_{m'm}(g)` for a representation `π` on a Hilbert
space with Hilbert basis `e`. The sibling `SU(2)` roadmap's matrix element is its instance for the
unitary model of `Sym^d ℂ²` and the standard basis. Prove:
- **Bridge to Tau Ceti's matrix coefficient** (`matrixElement_eq_conj_matrixCoeff`): for
  norm-continuous `π`, `matrixElement π e m' m g = conj (matrixCoeff π hπ (e m) (e m') g)`;
- for a strongly continuous `π`, each `matrixElement π e m' m` is continuous.

**Checks.**
- For the trivial representation `matrixElement π e m n g = δ_mn`.
- For `principalSeries τ e` and `fourierBasis`, `matrixElement n n (rot α) = e^{imα}`, `m = n − ε`.
- Negative control: the coefficient `⟪π g (e m'), e m⟫`, the argument order of `matrixCoeff`, is
  `conj D_{mm'}(g)`; on the diagonal above it is `e^{−imα}`.

*Needs:* Tau Ceti `ContRepresentation.matrixCoeff`.

### 3.2 Addition theorem and unitarity relations

Sources: Vilenkin–Klimyk §2.1.2 (3)–(4), p. 72, Examples 1–4; Wawrzyńczyk §2.6 (2.6.2),
Propositions 2.6.1–2.6.2, pp. 126–128; Miller §5-18 (5.172)–(5.173), p. 234.

Prove:
- **Addition theorem** (`hasSum_matrixElement_mul`): `D_{m'm}(gh) = Σₖ D_{m'k}(g) D_{km}(h)` with
  absolute convergence, and `D_{m'm}(1) = δ_{m'm}`, for every representation on a Hilbert space;
- **Unitarity relations** (`isUnitary_iff_hasSum_matrixElement`): `π` is unitary exactly when
  `Σₖ conj D_{km'}(g) D_{km}(g) = δ_{m'm}` for all `g`; then also
  `Σₖ D_{m'k}(g) conj D_{mk}(g) = δ_{m'm}` and `D_{m'm}(g⁻¹) = conj D_{mm'}(g)`;
- change of basis: for Hilbert bases `e`, `e'` with `e' m = Σⱼ c_{jm} e j`, the matrix elements in
  `e'` are `D'_{m'm} = Σ conj c_{jm'} D_{jk} c_{km}` with absolute convergence.

The addition theorem is Parseval (`HilbertBasis.hasSum_inner_mul_inner`) applied to
`⟪π(g)* e_{m'}, π(h) e_m⟫`; absolute convergence is Cauchy–Schwarz in `ℓ²`.

**Checks.**
- For `ℤ` acting on `ℓ²(ℤ)` by shifts, `D_{m'm}(k) = δ_{m', m+k}` and the addition theorem is
  `δ_{m', m+k+l} = Σ_j δ_{m', j+k} δ_{j, m+l}`.
- For the unitary principal series and the trigonometric basis, `Σₖ |D_{k0}(g)|² = 1`.
- Negative control: for `principalSeries 0.1 0`, which is not unitary, the column sum
  `Σₖ |D_{k0}(g)|²` is `‖T(g) 1‖² = 1.05851 38265` for `g = boost 1`.

*Needs:* 3.1; Mathlib `HilbertBasis.hasSum_inner_mul_inner`.

### 3.3 Weights under a circle subgroup

Sources: Vilenkin–Klimyk §6.5.1 (1)–(4), p. 311, §6.5.2 (1)–(5), pp. 312–313; Wawrzyńczyk §5.1
(5.1.4)–(5.1.5), p. 209; NoncompactQuantumSymmetry M4 (compact weights).

For `κ : Circle →* G`, `weightSpace π κ j = {v | ∀ u, π(κ u) v = uʲ v}`. Prove:
- **Weight decomposition** (`isHilbertSum_weightSpace`): for unitary `π` with continuous orbits on
  the circle, `H` is the Hilbert sum of the weight spaces, and matrix elements between weight
  vectors of weights `j'`, `j` satisfy `D_{m'm}(κ u₁ g κ u₂) = u₁^{j'} u₂^{j} D_{m'm}(g)`;
- the `κ`-finite vectors (finite sums of weight vectors) are dense, and for a strongly continuous
  Banach representation of `G` they are dense in the smooth vectors (CompactGroups'
  `gap:banach-gfinite-density`);
- for `SU(1,1)` with `κ(u) = diag(u, conj u)`, so that `κ(e^{iα/2}) = k_α`, the vector `e_m` has
  weight `2m` in `principalSeries τ e`, the sibling `SU(2)` roadmap's weight of `e_m`;
- **Euler factorization of matrix elements** (`principalSeries_matrixElement_euler`):
  `D_{m'm}(g(α, t, γ)) = e^{im'α} D_{m'm}(b_t) e^{imγ}`, the form `e^{im'α} d_{m'm}(β) e^{imγ}` of
  Edmonds (4.1.12), p. 55, with `b_t` in place of `b_β` (Vilenkin–Klimyk §6.5.2 (1), p. 312, in the
  labels of Conventions).

**Checks.**
- For the regular representation of the circle on `L²(haarAddCircle)`, `weightSpace j` is the line
  of `fourierLp 2 j`.
- Negative control: in `principalSeries τ 1` every `m` lies in `ℤ + 1/2`, so every weight `2m` is
  odd, no vector is fixed by `κ`, and the `K`-fixed space is `0`.
- `D_{m'm}(k_α) = δ_{m'm} e^{imα}` in the trigonometric basis.
- The factorization holds to `10⁻²⁶` at `τ = 0.23 + 0.4i`, `(α, t, γ) = (0.7, 1.3, −2.1)`,
  `(m', m) = (2, −1)` for `ε = 0` and `(3/2, −3/2)` for `ε = 1/2`.
- Negative control: the Vilenkin–Klimyk form `e^{−i(m'α + mγ)} D_{m'm}(b_t)` with the same `m', m`
  fails at these data: the two differ by the factor `e^{2i(m'α + mγ)} = e^{7i}` for `ε = 0`.

*Needs:* 3.1–3.2; Mathlib `IsHilbertSum`; CompactGroups Layer 5.

### Examples

- `D₀₀(b_t)` of `principalSeries (−1/2 + 0.8i) 0` at `t = 0.9` is `0.83316 90033`, the value of
  the Legendre function `P_τ(cosh 0.9)`.

### Dependencies

Layer 2 for the `SU(1,1)` bullets; Mathlib Hilbert bases; Tau Ceti `ContRepresentation.matrixCoeff`.

## Layer 4: infinitesimal operators of the circle models

### 4.1 Ladder operators

Sources: Vilenkin–Klimyk §6.4.1 (6)–(15), pp. 299–300, §2.1.5 (1)–(2), pp. 75–76; Miller §3-6
(3.44)–(3.47), pp. 68–69, Lemma 3.1; Wawrzyńczyk §2.8, Theorems 2.8.1–2.8.2, pp. 131–132.

`infinitesimal π γ v = d/ds π(γ s) v` at `s = 0`. Prove:
- **Ladder operators** (`principalSeries_ladder`): on `e_m = e^{inθ}`, `m = n − ε`, the orbits
  along `boost`, `boostY` and `rot` are differentiable in `L²` at `0`, and
  `J₊ e_m = (m − τ) e_{m+1}`, `J₋ e_m = −(m + τ) e_{m−1}`, `J₃ e_m = m e_m`;
- the trigonometric polynomials are a core of smooth vectors on which `A₁, A₂, A₃` are the
  derived action of SmoothBanachRepresentations 3.1 for `b₁, b₂, b₃`, and for `Re τ = −1/2` they
  are skew-symmetric (NoncompactQuantumSymmetry M0); as differential operators,
  `A₃ = d/dθ − iε` and `A₁, A₂` are first-order operators with multiplier terms linear in `τ`.

**Checks.**
- At `τ = 0.23 + 0.4i` and `n = 3`: for `ε = 0` (`m = 3`) the coefficients of `J₊, J₋, J₃` are
  `2.77 − 0.4i`, `−3.23 − 0.4i`, `3`; for `ε = 1/2` (`m = 5/2`) they are `2.27 − 0.4i`,
  `−2.73 − 0.4i`, `5/2`.
- For `τ = −1/2 + iρ`, `J₊` and `−J₋` are adjoint on trigonometric polynomials:
  `conj(m − τ) = m + 1 + τ`.
- Negative control: `J₊` defined with `−iA₂` in place of `+iA₂` is `J₋`, which lowers `m`.

*Needs:* 2.1; SmoothBanachRepresentations 0.2, 3.1; NoncompactQuantumSymmetry M0.

### 4.2 Casimir eigenvalue

Sources: Vilenkin–Klimyk §6.4.4, pp. 305–306 (erratum E06.4.03), §2.1.5, p. 77; Miller §5-18,
pp. 227–232.

Prove:
- **Casimir eigenvalue** (`principalSeries_casimir`): `A₁² + A₂² − A₃²` acts on every `e_m` by
  `τ(τ + 1)`;
- under `C₀`, NoncompactQuantumSymmetry M4.SL2R's `H_K`, `E_+`, `E_−` are `2J₃`, `−J₊`, `J₋`, so
  its `q_B` is `−(A₁² + A₂² − A₃²)`; the Casimir values on the unitary irreducibles are consumed
  from M4 through this dictionary;
- `½(J₊J₋ + J₋J₊) + J₃² = A₁² + A₂² − A₃²` on trigonometric polynomials, and
  `½(J₊J₋ + J₋J₊) e_m = (τ(τ + 1) − m²) e_m`.

**Checks.**
- At `τ = 0.23 + 0.4i` the eigenvalue is `0.1229 + 0.584i` for both values of `ε`.
- At `τ = −1/2 + 0.8i` it is `−0.89 = −1/4 − 0.8²`; NoncompactQuantumSymmetry M4's
  `q_B = (1 − ν²)/4` at `ν = −(2τ + 1)` is `0.89 = −τ(τ + 1)`.
- For the discrete series of weight `k` (`τ = −k/2`), `−τ(τ + 1) = k(2 − k)/4`, M4.P's
  `q_B = l(2 − l)/4` at `l = k`: `0`, `−3/4`, `−2` for `k = 2, 3, 4`.
- Negative control: the `su(2)` sign pattern `A₁² + A₂² + A₃²` gives `τ(τ + 1) − 2m²` on `e_m`,
  which depends on `m`.

*Needs:* 4.1.

### 4.3 The second-order equation of matrix elements

Sources: Vilenkin–Klimyk §6.7.5 (4)–(8), p. 342, §2.1.5 (3)–(5), p. 77; Wawrzyńczyk §5.4,
Theorem 5.4.2, p. 227.

Prove:
- **Template ODE** (`principalSeries_matrixElement_ode`): `P(t) = D_{m'm}(b_t)` is smooth and
  `P″ + coth t P′ − (m′² + m² − 2m′m cosh t)/sinh² t · P = τ(τ + 1) P` for `t > 0`;
- the same argument for any representation of `SU(1,1)` with a scalar Casimir `c` on a weight
  basis of smooth vectors gives the equation with `c` in place of `τ(τ + 1)`, and for `M(2)` it
  gives `P″ + P′/r − (m′ − m)²/r² · P = −R² P` for the matrix elements of 2.6.

The proof writes the Casimir in Euler angles as a second-order operator on `C^∞(SU(1,1))`, applies
it to `g ↦ D_{m'm}(g)`, and uses the Euler factorization of 3.3 to replace `∂_α`, `∂_γ` by `im′`,
`im`. Under `β = it` and the shift of Conventions it is the equation of the `SU(2)` matrix elements
`d_{m'm}(β)` of the sibling `SU(2)` roadmap, with `j(j + 1)` in place of `τ(τ + 1)`.

**Checks.**
- Residuals below `10⁻²⁴` at `t = 0.9` for `(τ, ε, m′, m) = (−1/2 + 0.8i, 0, 0, 0)`,
  `(−1/2 + 0.8i, 0, −2, 1)`, `(0.3 + 0.2i, 1/2, −3/2, −7/2)`, `(−0.3, 0, 2, −1)`.
- For `m′ = m = 0` the equation is Legendre's in `x = cosh t`, solved by `P_τ(cosh t)`.
- Negative control: with `−coth t` in place of `+coth t` the residual of `D₀₀(b_t)` is `0.95678`.
- For `M(2)` at `R = 1.7`, `m′ − m = 3`, `r = 0.8` the residual of the Bessel equation is below
  `10⁻²⁴`.

*Needs:* 3.3, 4.1–4.2.

### Examples

- `D₀₀(b_t) = P_τ(cosh t)` for the principal series at `τ = −1/2 + 0.8i`, `t = 0.9`:
  `0.83316 90033` from both sides.

### Dependencies

Layers 2–3; SmoothBanachRepresentations 0.2, 3.1; NoncompactQuantumSymmetry M0.

## Layer 5: Gel'fand pairs and spherical functions

### 5.1 Bi-invariant convolution and Gel'fand's criterion

Sources: Dieudonné §8, pp. 25–27 (definition, Gelfand's theorem, cases (I)–(III); erratum
D80-E08.0.04); Wawrzyńczyk §5.3, pp. 221–226 (definition, symmetric pairs, Theorem 5.3.3,
Example 1), Problem 8, pp. 230–231; Vilenkin–Klimyk §1.2.7, p. 67 (erratum E01.2.11).

`IsBiInvariant K f`, `conv μ f h x = ∫ f(y) h(y⁻¹ x) dμ(y)` and `IsGelfandPair μ K` (convolution of
continuous compactly supported bi-`K`-invariant functions commutes). Prove:
- **Gel'fand's criterion** (`isGelfandPair_of_antiAut`): on a unimodular locally compact group
  with compact `K`, a continuous involutive anti-automorphism `σ` with `σ x ∈ K x K` for every
  `x` gives a Gel'fand pair;
- **Symmetric pairs** (`isGelfandPair_of_involution`): on a unimodular locally compact group with
  compact `K`, a continuous involutive automorphism `θ` fixing `K` pointwise with `G = K P`,
  `P = {p | θ p = p⁻¹}`, gives a Gel'fand pair;
- the continuous compactly supported bi-`K`-invariant functions form a subalgebra of `C_c(G)`
  (not an ideal), and for a Gel'fand pair `G` is unimodular.

The criterion: `f ∘ σ = f` for bi-invariant `f`, `σ` preserves Haar measure (it multiplies it by
`c` with `c² = 1`), and `(f * h) ∘ σ = (h ∘ σ) * (f ∘ σ)`. The symmetric-pair form takes
`σ(x) = θ(x⁻¹)`: for `x = kp`, `σ(x) = k⁻¹ x k⁻¹`.

**Checks.**
- For abelian `G` and `K = {1}`, every `(G, K)` is a Gel'fand pair (`σ = id`).
- For the motion group `M(n)`, `θ(a, k) = (−a, k)` is a continuous involutive automorphism with
  `G = K · ℝⁿ` (Dieudonné case (III), Wawrzyńczyk Example 1(b)).
- Negative control: `(SU(1,1), {1})` is not a Gel'fand pair: `C_c(SU(1,1))` is not commutative.
- Inversion also satisfies the criterion for `(SU(1,1), K)`:
  `g(α, t, γ)⁻¹ = k_{−γ} b_{−t} k_{−α}` and `b_{−t} = k_π b_t k_π⁻¹`.

*Needs:* Mathlib Haar measure; Layer 0.

### 5.2 Spherical functions and the spherical transform

Sources: Wawrzyńczyk §5.1, Theorem 5.1.1, (5.1.2)–(5.1.5), pp. 208–209, Lemma 5.1.3, p. 210,
Proposition 5.1.4, pp. 211–212, Theorem 5.1.7, p. 218 (erratum W84-E05.1.01); Dieudonné §8 (107),
p. 28, §9 (108)–(109), p. 30.

`IsSphericalFunction K ν φ`: `φ` is continuous, bi-`K`-invariant, `φ(1) = 1` and
`∫_K φ(x k y) dν(k) = φ(x) φ(y)`; boundedness is not required.
`sphericalTransform μ φ f = ∫ f(x) φ(x⁻¹) dμ(x)`. Prove:
- **The functional equation suffices** (`isSphericalFunction_iff`): for a bi-invariant Haar
  probability measure `ν` on compact `K`, a continuous `φ` is spherical exactly when it is not
  identically zero and satisfies the functional equation;
- **Multiplicativity of the spherical transform** (`sphericalTransform_conv`) on continuous
  compactly supported bi-invariant functions;
- **Bounded spherical functions are the characters of `L¹(K\G/K)`**
  (`bounded_sphericalFunction_iff_character`): on a second-countable locally compact group with
  compact `K`, a bounded spherical function gives, by its spherical transform, a nonzero
  multiplicative functional on the integrable bi-invariant functions; conversely every nonzero,
  linear, `L¹`-bounded multiplicative functional on them, depending only on the class of `f`, is
  the spherical transform of a unique bounded spherical function;
- for a Gel'fand pair and bounded continuous bi-invariant `φ ≠ 0`, `φ` is spherical exactly when
  `φ(1) = 1` and `f * φ = λ_f φ` with `λ_f = ∫ f(u) φ(u⁻¹) du` for all bi-invariant `f`.

Bi-invariance and `φ(1) = 1` follow from the functional equation: if `φ(x₀) ≠ 0`, then
`φ(x₀) φ(k y) = ∫ φ(x₀ k' k y) dk' = φ(x₀) φ(y)` by invariance of `ν`, similarly on the right,
and `φ(x) φ(1) = ∫ φ(x k) dk = φ(x)`.

**Checks.**
- For `G = ℝ`, `K = {0}`: `x ↦ e^{sx}` is spherical for every `s ∈ ℂ`, and the spherical
  transform is `f ↦ ∫ f(x) e^{−sx} dx`; it is bounded only for `s ∈ iℝ`.
- Negative control: `x ↦ 2eˣ` is not spherical: `φ(0) = 2` and `φ(x + y) ≠ φ(x) φ(y)`.
- For `(SU(1,1), K)` and every `τ ∈ ℂ`, `φ_τ(g) = ⟪1, T_{(τ,0)}(g) 1⟫` is spherical and
  `φ_τ(b_t) = P_τ(cosh t)`; at `x = b_{0.6}`, `y = b_{1.3}` both sides of the functional equation
  are `2.33645 02682` for `τ = 1`, `1.40991 65308` for `τ = 1/2` and `0.90165 45857` for
  `τ = −0.3`.
- Negative control (unbounded spherical function): `φ_1(b_t) = cosh t`, with
  `φ_1(b_5) = 74.20994 85248`, is spherical but unbounded, and its spherical transform is not
  defined on all of `L¹(K\G/K)`; dropping boundedness from the character theorem would admit it.
  `φ_τ` is bounded exactly for `−1 ≤ Re τ ≤ 0`; at `τ = −0.3`, `φ(b_5) = 0.41425 42793`.

*Needs:* 5.1; Mathlib Bochner integration.

### 5.3 Spherical functions of representations; multiplicity one

Sources: Wawrzyńczyk §5.2, Theorem 5.2.1, pp. 218–220, §5.3, Theorem 5.3.1, pp. 222–223;
Dieudonné §9 (110), p. 30.

`fixedSubmodule π K` is the space of `K`-fixed vectors. Prove:
- **Spherical functions from representations** (`isSphericalFunction_inner`): if the `K`-fixed
  vectors of a strongly continuous unitary representation are the line through a unit vector `v`,
  then `g ↦ ⟪v, π(g) v⟫` is a positive-definite spherical function;
- **Multiplicity one** (`rank_fixedSubmodule_le_one`): for a Gel'fand pair and an irreducible
  strongly continuous unitary representation of a second-countable `G`, the `K`-fixed space has
  dimension at most one;
- **Positive-definite spherical functions come from representations**
  (`exists_isUnitary_of_sphericalFunction`): a positive-definite spherical function is
  `⟪v, π(g) v⟫` for a strongly continuous unitary `π` and a `K`-fixed unit vector `v` (the GNS
  construction of `TauCeti.posSemidef_inv_mul_iff_exists_isUnitary`, with `v` fixed because `φ`
  is bi-invariant);
- for a Gel'fand pair, the closed span of `π(G) v` is irreducible and determined by `φ` up to
  equivalence.

**Checks.**
- For `principalSeries (−1/2 + iρ) 0` the `K`-fixed space is the constant functions.
- Negative control: for `principalSeries τ 1` it is `0` (3.3), so no spherical function arises.
- For the trivial representation, `fixedSubmodule` is everything and `φ ≡ 1`.

*Needs:* 5.1–5.2; Tau Ceti `ContRepresentation.IsUnitary.posSemidef_inner_map_inv_mul`,
`TauCeti.posSemidef_inv_mul_iff_exists_isUnitary`.

### 5.4 `(SU(1,1), K)` and the radial equation

Sources: Wawrzyńczyk §5.1, Example 3, pp. 215–216, Problem 8(b), p. 231, §5.4, Theorem 5.4.2,
p. 227; Vilenkin–Klimyk §6.5.10 (1)–(2), pp. 325–326; Dieudonné §8, (II), pp. 26–27.

Prove:
- **`(SU(1,1), K)` is a Gel'fand pair** (`isGelfandPair_su11`), by 5.1 with `σ(g) = gᵀ`;
- **Radial equation on `SU(1,1)`** (`sphericalFunction_su11_ode`): `F(t) = φ(b_t)` is smooth and
  `F″ + coth t F′ = c F` for `t > 0`;
- for a connected Lie group `G` and compact `K`, spherical functions are analytic joint
  eigenfunctions of the `G`-invariant differential operators on `G/K` (Wawrzyńczyk Theorem 5.4.2),
  with the operators built from the Lie functor of RepresentationTheory/LieGroups; on `M(2)` the
  radial equation is `F″ + F′/r = c F`, and `(M(n), SO(n))` is a Gel'fand pair by the symmetric
  pair form of 5.1;
- `(SO(3), SO(2))` with inversion satisfies 5.1; it is the sibling `SU(2)` roadmap's example
  (its Layer 6, as `(SU(2), T)`), recovered here as an instance.

**Checks.**
- `g(α, t, γ)ᵀ = g(γ, t, α) = (k_γ k_α⁻¹) g(α, t, γ) (k_γ⁻¹ k_α)`, which lies in `K g K`.
- For `φ(b_t) = P_τ(cosh t)` the constant is `c = τ(τ + 1)`.
- `F(t) = cosh t = P₁(cosh t)` satisfies the equation with `c = 2 = τ(τ + 1)` at `τ = 1`.
- Negative control: the smooth bi-invariant `F(t) = cosh² t` gives `F″ + coth t F′ = 6 cosh² t − 2`,
  not a multiple of `F`: not every bi-invariant function satisfies the radial equation.

*Needs:* 0.1, 4.3, 5.1–5.2.

### Examples

- `(SU(1,1), K)`, `(M(n), SO(n))` and `(SO(3), SO(2))` are Gel'fand pairs; `(SU(1,1), {1})` is not.

### Dependencies

Layers 0, 3, 4; Mathlib Haar measure; Tau Ceti positive definiteness; RepresentationTheory/LieGroups
for the general form of 5.4.

## Downstream consumers

- The sibling roadmaps of the same project on Euclidean motion groups and Bessel functions, on
  affine, triangular and Heisenberg groups, on `SU(1,1)` and `SL(2, ℝ)`, and on rank-one symmetric
  spaces, which identify the matrix elements and spherical functions of Layers 2–5 with Bessel,
  Laguerre, Whittaker, Legendre and Jacobi functions.

## Beyond this roadmap (a roadmap for a roadmap; do not implement)

The following material lies outside this roadmap. It is recorded only to fix the boundary.
Contributors should not attempt it under this roadmap.

- **Plancherel theory**: the decomposition of `L²(G)` and of `L²(G/K)` into irreducibles, the
  Plancherel–Godement theorem (Dieudonné §9, pp. 30–33), the Harish-Chandra `c`-function and the
  inversion of the spherical transform (Wawrzyńczyk Chapter 16); for `SL(2,ℝ)` the Plancherel
  theorem is NoncompactQuantumSymmetry M4.P's.
- **Classification of unitary duals** beyond the consumed results: Mackey theory in general and
  higher-rank groups (Vilenkin–Klimyk Chs. 15–16).
- **Higher-rank spherical functions** and the Heckman–Opdam hypergeometric functions
  (Heckman–Schlichtkrull Part I).
- **The universal covering group of `SU(1,1)`** and its principal series (Vilenkin–Klimyk §6.1.5,
  §6.4.7).
- **Miller's local multiplier representations of Lie algebras** and Weisner's method (Miller
  Chs. 1–2), which the special-function roadmaps use for generating functions.

## Prior formalization

None of this material is formalized in Mathlib or Tau Ceti. The project repository `lean-SFVK`
that hosts this roadmap has no code for it.

## Provenance against the source synopses

This table maps the subsections to the project's synopsis entries of the sources. It is a
secondary index; the layers above are the specification.

| Here | Synopsis entries |
|---|---|
| 0.1 | VK06.1.03, VK06.1.04, VK06.1.06, VK06.1.07, VK06.1.09, VK06.1.12; M68.05.18.01 |
| 0.2 | VK01.2.15, VK01.2.16, VK01.2.21, VK01.1.26, VK05.1.01; KV01.1.17, KV01.1.18 |
| 0.3 | VK04.1.01–VK04.1.04, VK04.2.03, VK04.2.06; KV01.1.15, KV01.1.16; D80.08.0.05 |
| 1.1 | W84.01.7.01, W84.01.7.02; VK01.2.15, VK01.2.18 |
| 1.2 | VK02.1.27; W84.02.2.03; M68.01.3.05 |
| 1.3 | W84.02.2.04; VK02.1.22, VK02.1.23 |
| 1.4 | W84.02.2.03; VK02.2.22 |
| 2.1 | VK06.4.01, VK06.4.08, VK06.4.09; KV01.2.06; M68.05.18.02, M68.05.18.03; W84.02.2.05 |
| 2.2 | VK06.4.10; M68.05.18.04 |
| 2.3 | M68.05.18.05, M68.05.18.06; VK06.4.11; KV01.2.05 |
| 2.4 | KV01.2.13; VK01.2.21 |
| 2.5 | W84.02.8.03; VK01.1.26 |
| 2.6 | VK04.1.05–VK04.1.08; KV01.2.11, KV01.2.12, KV01.2.14; M68.03.7.01, M68.03.8.01 |
| 3.1 | VK02.1.12; W84.02.6.01; M68.03.6.01 |
| 3.2 | VK02.1.12, VK02.1.13; W84.02.6.02; VK06.6.01 |
| 3.3 | VK06.5.01, VK06.5.04; W84.05.1.03 |
| 4.1 | VK06.4.02; VK02.1.18, VK02.1.19; M68.03.6.02, M68.03.6.03 |
| 4.2 | VK06.4.07; VK02.1.21 |
| 4.3 | VK06.7.19; VK02.1.20; W84.05.4.02 |
| 5.1 | D80.08.0.02–D80.08.0.05; W84.05.3.01, W84.05.3.04, W84.05.3.05, W84.05.4.05 |
| 5.2 | W84.05.1.02–W84.05.1.06, W84.05.1.12; D80.08.0.07, D80.09.0.01 |
| 5.3 | W84.05.2.01, W84.05.3.02; D80.09.0.02 |
| 5.4 | W84.05.1.10, W84.05.4.02; VK06.5.23 |

## References

- J. Dieudonné, *Special Functions and Linear Representations of Lie Groups*, CBMS Regional
  Conference Series in Mathematics 42, AMS, 1980, §§8–9.
- A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press, 1957
  (reprinted 1996), §4.1, pp. 53–57 (the Euler-angle and matrix-element conventions).
- G. Heckman and H. Schlichtkrull, *Harmonic Analysis and Special Functions on Symmetric Spaces*,
  Perspectives in Mathematics 16, Academic Press, 1994, Part I (cited in Beyond).
- A. U. Klimyk and N. Ya. Vilenkin, *Representations of Lie Groups and Special Functions*, in
  A. A. Kirillov (ed.), *Representation Theory and Noncommutative Harmonic Analysis II*,
  Encyclopaedia of Mathematical Sciences 59, Springer, 1995, Part II, Chapter 1, §§1–2.
- W. Miller, Jr., *Lie Theory and Special Functions*, Mathematics in Science and Engineering 43,
  Academic Press, 1968, §§1-3, 3-6–3-8, 5-18.
- N. Ja. Vilenkin and A. U. Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 1,
  Mathematics and Its Applications (Soviet Series) 72, Kluwer, 1991, Chs. 1, 2, 4, 5, 6.
- A. Wawrzyńczyk, *Group Representations and Special Functions*, Mathematics and Its Applications
  (East European Series), Reidel / PWN, 1984, Chs. 1, 2, 5.
