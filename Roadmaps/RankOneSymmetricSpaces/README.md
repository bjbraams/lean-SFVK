# Special functions on rank-one symmetric spaces: Jacobi functions and real hyperbolic space

**Summary.** This roadmap builds the harmonic analysis of the rank-one Riemannian symmetric spaces
through its special function, the Jacobi function `φ_λ^{(α,β)}`, and carries it out in full on
the real hyperbolic space `ℍⁿ = SO₀(n, 1)/SO(n)`. On the analytic side it develops the Jacobi
function and the Jacobi operator, the Harish-Chandra series `Φ_λ` and the `c`-function with the
connection formula and the asymptotics, the bounds and positivity of `φ_λ`, Koornwinder's
Laplace-type representation and product formula, and the Jacobi transform with its Paley–Wiener
estimate, its inversion formula, its Plancherel formula and its unitary extension. On the
geometric side it builds the hyperboloid model of `ℍⁿ` with the Lorentz group, the invariant
volume in polar and horospherical coordinates, the Laplace–Beltrami operator through the ambient
wave operator, the boundary sphere with the plane waves and the Poisson kernel, the Gel'fand pair
`(SO₀(n, 1), SO(n))`, its spherical functions as Jacobi functions with `(α, β) = (n/2 − 1, −1/2)`,
the spherical transform with its inversion and Plancherel constants, the Abel transform, and the
Helgason–Fourier transform with its inversion and Plancherel theorems. The spherical principal
series of `SO₀(n, 1)` on `L²(S^{n−1})` is the representation-theoretic counterpart: its
`K`-fixed matrix coefficient is `φ_λ`.

The roadmap is a synthesis of several sources and follows none of them in its organization: it is
ordered by proof dependency, from the one-variable special function, through its transform, to
the geometry of `ℍⁿ` and the harmonic analysis on it. Its sources are Wawrzyńczyk (*Group
Representations and Special Functions*, Chs. 11 and 18), Koornwinder's survey of Jacobi functions
as presented by Klimyk–Vilenkin (*Representations of Lie Groups and Special Functions*, in
Kirillov (ed.), Encyclopaedia of Mathematical Sciences 59, Part II Ch. 5 §2), Vilenkin–Klimyk
(*Representation of Lie Groups and Special Functions*, Vol. 2, Chs. 9 and 11), Heckman–Schlichtkrull
(*Harmonic Analysis and Special Functions on Symmetric Spaces*, the rank-one parts) and the NIST
Digital Library of Mathematical Functions §15.9(ii); each subsection cites several of them by
locator; see [References](#references).

Mathlib has the Gauss hypergeometric series on the unit disc, the Gamma function, `Real.arcosh`,
`Matrix.SpecialLinearGroup` with its topology, Haar measure, the surface measure
`MeasureTheory.Measure.toSphere`, averages `MeasureTheory.average`, `Lp` spaces, the Fourier
transform and iterated derivatives. Neither Mathlib nor Tau Ceti has Jacobi functions, the
Harish-Chandra `c`-function, the Jacobi transform, the hyperboloid model of real hyperbolic space
with its Lorentz group, the Laplace–Beltrami operator of `ℍⁿ`, the spherical functions of a
noncompact symmetric space, the Abel transform or the Helgason–Fourier transform.

The roadmap covers:
- the Jacobi function and operator, special cases, the polynomial case, the Harish-Chandra
  series, the `c`-function, the connection formula and the asymptotics, the bounds,
  Koornwinder's Laplace-type representation and product formula (Layer 0);
- the Jacobi transform: evenness, holomorphy, the Paley–Wiener estimate, the transform of the
  Jacobi operator, inversion, Plancherel, the unitary extension, the discrete terms outside the
  range `|β| ≤ α + 1`, and the Paley–Wiener theorem (Layer 1);
- the hyperboloid model of `ℍⁿ`: the Lorentz form, the group `SO₀(n, 1)` and its subgroup `K`,
  transitivity and the distance, the invariant volume in polar and horospherical coordinates, the
  Laplace–Beltrami operator with its invariance and radial part, the boundary sphere with plane
  waves and Poisson integrals, and the Gel'fand pair (Layer 2);
- the spherical functions of `ℍⁿ`: Harish-Chandra's integral, the eigenvalue equation, the
  classification, boundedness and positive definiteness, the cases `n = 2, 3`, and the spherical
  principal series (Layer 3);
- harmonic analysis on `ℍⁿ`: the spherical transform as a Jacobi transform with inversion and
  Plancherel, the Abel transform, and the Helgason–Fourier transform with inversion, Plancherel
  and the transform of the Laplacian (Layer 4).

## Scope and ownership

The roadmap is complete when Tau Ceti proves all of the following.

0. **Jacobi functions** (0.1–0.4).
1. **The Jacobi transform** (1.1–1.3).
2. **Real hyperbolic space** (2.1–2.5).
3. **Spherical functions on `ℍⁿ`** (3.1–3.4).
4. **Harmonic analysis on `ℍⁿ`** (4.1–4.4).

The numbers are those of the layers below, and `k.n` names subsection `n` of Layer `k`.
`Suggested.lean` states the headlines that carry a Lean name, each with every conclusion the
README attaches to it; it is not an exhaustive acceptance test, and the other headlines and the
plain bullets of each subsection are targets of the same standing, stated in prose. The
`**Checks.**` and `### Examples` of each layer are statements to prove; they test the conventions
on explicit values.

**Boundary with SpecialFunctionsGroupModels.** That roadmap owns Gel'fand pairs, Gel'fand's
criterion, spherical functions with their functional equation and the spherical transform of a
general pair `(G, K)` with compact `K` (its §§5.1–5.2), and multiplier representations on
`G`-spaces (its Layer 1). This roadmap consumes those definitions, proves that
`(SO₀(n, 1), SO(n))` is a Gel'fand pair by its criterion, and owns the Harish-Chandra
`c`-function and the inversion of the spherical transform in rank one, which that roadmap places
beyond its scope.

**Boundary with SpecialFunctionsSU11MatrixElements.** That roadmap owns the matrix elements
`𝔓^τ_{mn}` of `SU(1, 1)`, the Legendre and conical functions as `𝔓^τ_{00}` (its §1.3), their
product formula (its §3.2) and the Mehler–Fock transforms of order `0` and `m` (its §§5.2–5.3).
This roadmap owns the Jacobi function for general `(α, β)`, the `c`-function, the general Jacobi
transform, the Abel transform and Koornwinder's product formula for general `(α, β)`. It states
the Mehler–Fock transform as the instance `(α, β) = (0, 0)` of the Jacobi transform by citing
SpecialFunctionsSU11MatrixElements §5.2, and the spherical functions of `ℍ²` as conical
functions by citing its §1.3; it does not reprove them.

**Boundary with [RealSemisimpleLieGroups](../RealSemisimpleLieGroups/README.md) and
[LieGroupsPartII](../LieGroupsPartII/README.md).** Those roadmaps own the structure theory of
`G/K` for a general real reductive group: Cartan involutions, restricted roots, the Iwasawa and
`KAK` decompositions, parabolic subgroups and the Riemannian symmetric space with its metric
(RealSemisimpleLieGroups §5.2 identifies `SO₀(n, 1)/SO(n)` with the upper sheet of the
hyperboloid). They exclude spherical functions and harmonic analysis on `G/K`. This roadmap
builds `ℍⁿ` concretely in coordinates, with the decompositions it needs proved by matrix
computation, and records the comparison with their general objects as a Check.

**Boundary with [NoncompactQuantumSymmetry](../NoncompactQuantumSymmetry/README.md).** Its M4 and
M4.Lorentz own the principal and complementary series of `SL(2, ℝ)` and `SL(2, ℂ)` with their
classification and irreducibility. This roadmap consumes them for `n = 2, 3` through the local
isomorphisms `SO₀(2, 1) ≅ PSL(2, ℝ)` and `SO₀(3, 1) ≅ PSL(2, ℂ)`, and owns the spherical
principal series of `SO₀(n, 1)` for general `n`.

**Boundary with [AutomorphicSpectralTheory](../AutomorphicSpectralTheory/README.md) and
[AnalyticNumberTheoryPartII](../AnalyticNumberTheoryPartII/README.md).** AutomorphicSpectralTheory
§§0.35–0.37 own the Legendre function `Q_{s−1}` and point-pair invariants on the upper half-plane
for the Selberg trace formula; AnalyticNumberTheoryPartII §6.12 uses local inverse-Abel adapters
for the heat kernel of `ℍ²`. Neither depends on this roadmap; the Abel transform of 4.2 for
`n = 2` is the general object of which their adapters are instances, and the comparison is
recorded as a Check of 4.2, not as a dependency.

**Boundary with [SpecialFunctionsHypergeometric](../SpecialFunctionsHypergeometric/README.md)
and [LaguerreJacobi](../LaguerreJacobi/README.md).** The first owns `F(a, b; c; z)` with its
continuation, transformations and connection formulas and leaves the Jacobi function and
transform (DLMF 15.9.11–15.9.14) to a sequel; this roadmap is that sequel. The second owns the
Jacobi polynomials `P_k^{(α,β)}` (its §3.2), consumed in 0.1.

## Conventions

- **Jacobi function.** `φ_λ^{(α,β)}(t) = F((ρ + iλ)/2, (ρ − iλ)/2; α + 1; −sinh² t)` with
  `ρ = α + β + 1`, for complex `α, β, λ` and real `t` (`jacobiFunction`; DLMF 15.9.11;
  Klimyk–Vilenkin Part II Ch. 5 §2.4 (12), p. 233). `F` is the principal branch of
  SpecialFunctionsHypergeometric (its Layer 1), so `F = Γ(c) 𝐅` and the value is junk (`0`) at
  `α + 1 ∈ {0, −1, −2, …}`; theorems exclude those parameters. Vilenkin–Klimyk Vol. 2 write
  `𝔓_μ^{(α,β)}(cosh 2t)` for `φ_λ(t)` with `μ = (iλ − ρ)/2`.
- **Jacobi operator.** `L = d²/dt² + ((2α + 1) coth t + (2β + 1) tanh t) d/dt`, with
  `L φ_λ = −(λ² + ρ²) φ_λ` (`jacobiOperator`).
- **`c`-function.** `c(λ) = 2^{ρ−iλ} Γ(α + 1) Γ(iλ) / (Γ((iλ + ρ)/2) Γ((iλ + α − β + 1)/2))`,
  normalized by `c(−iρ) = 1` (`cFunction`). Klimyk–Vilenkin's `𝐜(λ)` (p. 233) is
  `2√π c(λ)/Γ(α + 1)`; this roadmap uses Koornwinder's `c`, which makes the Plancherel density
  `(2π)⁻¹ |c(λ)|⁻²` independent of `α`.
- **Jacobi transform.** `f̃(λ) = ∫₀^∞ f(t) φ_λ(t) Δ(t) dt` with
  `Δ(t) = (2 sinh t)^{2α+1} (2 cosh t)^{2β+1}` (`jacobiTransform`, `jacobiWeight`; DLMF 15.9.12),
  for real `α > −1` and `β`.
- **Real hyperbolic space.** `ℍⁿ` (`n ≥ 2`) is the upper sheet of `[x, x] = 1` in
  `Fin (n + 1) → ℝ`, `[x, y] = x₀ y₀ − x₁ y₁ − ⋯ − xₙ yₙ`, with index `0` the time coordinate
  (`lorentz`, `hyperboloid`), as in Wawrzyńczyk §11.1 and Vilenkin–Klimyk Vol. 2 §9.1 up to the
  position of the time coordinate (Vilenkin–Klimyk put it last). The base point is `o = e₀`
  (`basePoint`), and `d(x, y) = arcosh [x, y]` (`hyperbolicDist`), so the radius of `x` is
  `t = arcosh x₀`. The metric is the one induced by `−[·, ·]`, of curvature `−1`.
- **Groups.** `G = SO₀(n, 1)` is the subgroup of `SL(n + 1, ℝ)` that preserves `[·, ·]` and maps
  `ℍⁿ` onto itself (`lorentzGroup`); `K ≅ SO(n)` is the stabilizer of `o` (`rotationSubgroup`).
  `orbitMap g = g o`.
- **Volume.** `dm = dx₁ ⋯ dxₙ / x₀` on `ℍⁿ`, through the chart `y ↦ (√(1 + |y|²), y)`
  (`hyperboloidChart`, `hyperbolicMeasure`). In polar coordinates
  `dm = sinh^{n−1} t dt dω` with `dω` the surface measure of `S^{n−1}`, of total mass
  `ω_{n−1} = 2π^{n/2}/Γ(n/2)` (`sphereArea`).
- **Laplacian.** `Δ` is the Laplace–Beltrami operator, negative semidefinite, computed by the
  ambient wave operator `∂₁² + ⋯ + ∂ₙ² − ∂₀²` on the extension of `f` homogeneous of degree `0`
  (`hyperbolicLaplacian`; Wawrzyńczyk §11.5, (11.5.1)–(11.5.3), pp. 411–412). Its radial part is
  `F'' + (n − 1) coth t F'`.
- **Spherical functions.** `φ_λ(x) = φ_λ^{(n/2−1, −1/2)}(arcosh x₀)` (`sphericalFunction`), with
  `ρ = (n − 1)/2` and `Δ φ_λ = −(λ² + ρ²) φ_λ`. The boundary point over `b ∈ S^{n−1}` is
  `b̃ = (1, b)` (`boundaryVector`); `dσ` is the normalized rotation-invariant measure on
  `S^{n−1}`, used through averages over `sphereMeasure`.
- **Transforms on `ℍⁿ`.** `Sf(λ) = ∫ f φ_λ dm` (`sphericalTransform`) and
  `f̂(λ, b) = ∫ f(x) [x, b̃]^{iλ−ρ} dm(x)` (`helgasonFourier`), as in Wawrzyńczyk §18.7,
  (18.7.12), p. 640, read on `ℍⁿ`. The constant of both inversion formulas is
  `C_n = 2^{n−1} / (2π ω_{n−1})` (`plancherelConstant`), with `C_3 = 1/(2π²)`.
- **Abel transform.** On `ℍ^{m+1}`, `𝒜F(s) = e^{−ms/2} ∫_{ℝ^m} F(arcosh(cosh s + |v|² e^{−s}/2)) dv`
  (`abelTransform`), the horocycle integral of the radial function `F ∘ d(o, ·)` weighted by
  `e^{−ρs}`.
- Complex powers are principal; every base raised to a complex power in this roadmap is positive
  (`[x, b̃] > 0` on `ℍⁿ`, `2 cosh t > 0`, `|cosh t + r e^{iψ} sinh t| > 0`).

## Exact supplier contracts

### From Mathlib

- `Real.arcosh`, `Complex.Gamma`, `Matrix.SpecialLinearGroup` with its topology,
  `MeasureTheory.Measure.toSphere`, `MeasureTheory.average`, `MeasureTheory.Lp`,
  `MeasureTheory.Measure.IsHaarMeasure`, `iteratedDeriv`, `ascPochhammer`.

### From other roadmaps

- SpecialFunctionsHypergeometric Layer 1 (`F` on the cut plane), its elementary cases (§4.1),
  connection formulas (§5.4) and quadratic transformations (§7.1); `Suggested.lean` carries
  verbatim local copies
  `eulerIntegral`, `IsEulerContinuation`, `regularizedGaussHypergeometric` and
  `gaussHypergeometric`.
- LaguerreJacobi §3.2, the Jacobi polynomial, local copy `jacobi`.
- SpecialFunctionsGroupModels §§5.1–5.2 (`IsBiInvariant`, `conv`, `IsGelfandPair`,
  `IsSphericalFunction`, verbatim local copies; the criterion of §5.1 and the spherical
  functions of representations of §5.3) and Layer 1 (multiplier representations, consumed in
  3.4).
- SpecialFunctionsSU11MatrixElements §1.3 (conical functions), §2.1 (`|𝔓| ≤ 1` on the principal
  and complementary series) and §5.2 (the Mehler–Fock transform), consumed in Checks of 0.2, 1.2
  and 3.3.
- NoncompactQuantumSymmetry M4 and M4.Lorentz (irreducibility of the principal series of
  `SL(2, ℝ)` and `SL(2, ℂ)`), consumed in 3.4.
- RealSemisimpleLieGroups §5.2 (the symmetric space `G/K`), consumed in a Check of 2.1.

## How to read the build

Layers 0 and 1 are one-variable analysis and depend only on the hypergeometric function. Layer 2
is the geometry of `ℍⁿ` and depends on nothing in Layers 0–1. Layer 3 joins them: the spherical
functions of Layer 2's Gel'fand pair are the Jacobi functions of Layer 0. Layer 4 transfers the
inversion and Plancherel theorems of Layer 1 to `ℍⁿ` through 3.1 and the polar coordinates of
2.2, and extends them to non-radial functions through the plane waves of 2.4.

## Layer 0: Jacobi functions

### 0.1 Definition, equation and polynomial case

Sources: DLMF 15.9.11; Klimyk–Vilenkin Part II Ch. 5 §2.4, (12), p. 233; Vilenkin–Klimyk Vol. 2
§11.4.1, pp. 332–333 (the functions `𝔓_μ^{(α,β)}` from `U(n − 1, 1)`); Wawrzyńczyk §18.5,
(18.5.1)–(18.5.2), pp. 627–628 (the rank-one radial equation).

`jacobiFunction α β λ t` and `jacobiOperator α β u t` as in Conventions. Prove:
- **Value at the origin** (`jacobiFunction_zero`): `φ_λ(0) = 1` for `α + 1 ∉ {0, −1, …}`;
- **Evenness** (`jacobiFunction_neg`, `jacobiFunction_even`): `φ_{−λ} = φ_λ` and
  `φ_λ(−t) = φ_λ(t)`;
- **Holomorphy** (`differentiable_jacobiFunction`): `φ_λ(t)` is entire in `λ`;
- **The Jacobi equation** (`jacobiOperator_jacobiFunction`): `L φ_λ = −(λ² + ρ²) φ_λ` on
  `t > 0`;
- **Uniqueness** (`eq_jacobiFunction_of_jacobiOperator`): for `Re α ≥ 0`, a solution on
  `(0, ∞)` that is continuous on `[0, ∞)` with value `1` at `0` is `φ_λ`;
- **The trivial spherical function** (`jacobiFunction_I_mul_rho`): `φ_{±iρ} ≡ 1`;
- **The polynomial case** (`jacobiFunction_eq_jacobi`):
  `φ_{i(2k+ρ)}(t) = k!/(α + 1)_k · P_k^{(α,β)}(cosh 2t)`.

Proof route: the hypergeometric equation in `z = −sinh² t` becomes the Jacobi equation; the
second solution at `t = 0` behaves like `t^{−2α}` (like `log t` at `α = 0`), which is not
continuous at `0` when `Re α ≥ 0`, `α ≠ 0`, or `α = 0`. At `λ = i(2k + ρ)` the first parameter
is `−k` and `F` terminates; LaguerreJacobi §3.2 gives
`P_k^{(α,β)}(x) = (α + 1)_k/k! · F(−k, k + ρ; α + 1; (1 − x)/2)` and
`(1 − cosh 2t)/2 = −sinh² t`.

**Checks.**
- `φ_{0.5}^{(1,0)}(1) = 0.60870 20756`.
- At `(α, β) = (1, 1/2)`, `k = 1`, `t = 0.7`:
  `φ_{i(2+ρ)}(t) = 1 + (ρ + 1)/(α + 1) · sinh² t = 2.00703 61572`.
- `L` applied to the constant `1` is `0`, and `φ_{iρ} ≡ 1` has eigenvalue `−((iρ)² + ρ²) = 0`.
- Negative control (uniqueness needs `Re α ≥ 0`): for `α = −1/4` the second solution at `0`
  behaves like `t^{1/2}`, so `φ_λ` plus that solution is continuous on `[0, ∞)` with value `1`
  at `0`, solves the equation, and differs from `φ_λ`.

*Needs:* SpecialFunctionsHypergeometric Layer 1; LaguerreJacobi §3.2.

### 0.2 Special cases and the quadratic transformation

Sources: DLMF 15.9.11 with 15.4.11 and 15.4.15; Klimyk–Vilenkin Part II Ch. 5 §2.3, p. 232
(the Mehler–Fock case) and §2.4, p. 233 (the remark on rank-one spaces); Wawrzyńczyk §11.3,
(11.3.1), pp. 401–402.

Prove:
- **Fourier case** (`jacobiFunction_cos`): `φ_λ^{(−1/2,−1/2)}(t) = cos λt`;
- **The case of `ℍ³`** (`jacobiFunction_sin`): `φ_λ^{(1/2,−1/2)}(t) = sin λt/(λ sinh t)`;
- **Quadratic transformation** (`jacobiFunction_quadratic`):
  `φ_λ^{(α,−1/2)}(t) = φ_{2λ}^{(α,α)}(t/2)`;
- `φ_λ^{(1/2,1/2)}(t) = 2 sin λt/(λ sinh 2t)`;
- **Conical case**: `φ_λ^{(0,−1/2)}(t) = P_{−1/2+iλ}(cosh t)` and
  `φ_λ^{(0,0)}(t) = P_{−1/2+iλ/2}(cosh 2t)`, the conical functions of
  SpecialFunctionsSU11MatrixElements §1.3.

Proof route: `F(a, −a; 1/2; −sinh² t) = cosh 2at` and
`F(a, 1 − a; 3/2; −sinh² t) = sinh((2a − 1)t)/((2a − 1) sinh t)` (DLMF 15.4.11 and 15.4.15 at
`z = sinh t`, SpecialFunctionsHypergeometric §4.1); the quadratic transformation is
SpecialFunctionsHypergeometric §7.1 read at `z = −sinh² t`.

**Checks.**
- `φ_2^{(−1/2,−1/2)}(1) = cos 2 = −0.41614 68365`.
- `φ_1^{(1/2,−1/2)}(1) = sin 1/sinh 1 = 0.71602 29154`.
- Negative control (the second parameter of `ℍ³`): `φ_1^{(1/2,0)}(1) = 0.59651 55509`, not
  `sin 1/sinh 1`.

*Needs:* 0.1; SpecialFunctionsHypergeometric §§4.1 and 7.1.

### 0.3 The Harish-Chandra series, the `c`-function and the connection formula

Sources: DLMF 15.9.13–15.9.14; Klimyk–Vilenkin Part II Ch. 5 §2.4, (13)–(14), p. 233;
Vilenkin–Klimyk Vol. 2 §9.4.10, (1)–(5), pp. 92–93; Wawrzyńczyk §18.5, (18.5.1)–(18.5.2),
pp. 627–628.

`harishChandraSeries α β λ t` is
`Φ_λ(t) = (2 cosh t)^{iλ−ρ} F((ρ − iλ)/2, (α − β + 1 − iλ)/2; 1 − iλ; cosh⁻² t)` for `t > 0`, and
`cFunction α β λ` as in Conventions. Prove:
- **`Φ_λ` solves the Jacobi equation** (`jacobiOperator_harishChandraSeries`) on `t > 0` for
  `iλ ∉ {1, 2, …}`;
- **Leading behaviour** (`tendsto_harishChandraSeries`): `Φ_λ(t) e^{(ρ−iλ)t} → 1`;
- **The connection formula** (`jacobiFunction_eq_cFunction`):
  `φ_λ = c(λ) Φ_λ + c(−λ) Φ_{−λ}` on `t > 0` for `iλ ∉ ℤ`;
- **Normalization** (`cFunction_neg_I_mul_rho`): `c(−iρ) = 1`;
- **Asymptotics** (`tendsto_jacobiFunction_mul_exp`): for `Im λ < 0`,
  `φ_λ(t) e^{(ρ−iλ)t} → c(λ)`;
- **Growth of the Plancherel density** (`norm_cFunction_inv_sq_le`): for real `α > −1`,
  `|c(λ)|⁻² ≤ C (1 + |λ|)^{2α+1}` on the real line;
- `c(λ)` has no zeros on `ℝ \ {0}`, and for real `α, β` and real `λ`, `c(−λ) = conj c(λ)`.

Proof route: the connection formula is SpecialFunctionsHypergeometric §5.4 (the connection
between `z = 0` and `z = ∞`) read at `z = −sinh² t`, with the duplication formula of `Γ`; the
growth bound is Stirling's formula for the four Gamma factors.

**Checks.**
- At `(α, β) = (1, 1/2)`, `c(−iρ) = 1`; Klimyk–Vilenkin's `𝐜 = 2√π c/Γ(α + 1)` gives
  `𝐜(−iρ) = 2√π = 3.54490 77018` there (negative control for the normalization).
- `c^{(1/2,−1/2)}(λ) = 1/(iλ)`, so `|c(λ)|⁻² = λ²` for `ℍ³`.
- `|c^{(0,−1/2)}(λ)|⁻² = πλ tanh πλ`, at `λ = 1` equal to `3.12988 10356`, the Mehler–Fock
  density of SpecialFunctionsSU11MatrixElements §5.2 in the variable of `ℍ²`.
- `c^{(−1/2,−1/2)} ≡ 1/2`, and `cos λt = (e^{iλt} + e^{−iλt})/2` is the connection formula with
  `Φ_λ(t) = e^{(iλ)t}`.

*Needs:* 0.1; SpecialFunctionsHypergeometric §5.4; Mathlib Stirling.

### 0.4 Bounds, Laplace-type representation and product formula

Sources: Vilenkin–Klimyk Vol. 2 §11.4.6, (4)–(10), pp. 348–350 (Koornwinder's product formula
and the Laplace-type representation); §11.4.1, (6)–(7), p. 333; Klimyk–Vilenkin Part II Ch. 5
§2.4, p. 234; Heckman–Schlichtkrull Part II, Lecture 8, Example 8.1, (8.3)–(8.4), pp. 171–172.

Prove:
- **The energy bound** (`norm_jacobiFunction_le_one`): for real `λ`, real `α ≥ −1/2` and
  `α + β + 1 ≥ 0`, `|φ_λ(t)| ≤ 1`;
- **Koornwinder's Laplace-type representation** (`jacobiFunction_laplace`), for real
  `α > β > −1/2`:
  `φ_λ(t) = C ∫₀^π ∫₀¹ |cosh t + r e^{iψ} sinh t|^{iλ−ρ} w(r, ψ) dr dψ` with
  `w(r, ψ) = r^{2β+1} (1 − r²)^{α−β−1} sin^{2β} ψ`,
  `C = 2Γ(α + 1)/(√π Γ(α − β) Γ(β + 1/2))`;
- **Bound by the imaginary part** (`norm_jacobiFunction_le`), for real `α ≥ β ≥ −1/2`:
  `|φ_λ(t)| ≤ φ_{i Im λ}(t)`;
- **Bounded Jacobi functions** (`bddAbove_jacobiFunction_iff`), for real `α ≥ β ≥ −1/2`:
  `φ_λ` is bounded on `[0, ∞)` exactly when `|Im λ| ≤ ρ`;
- **Koornwinder's product formula** (`jacobiFunction_mul_jacobiFunction`), for real
  `α > β > −1/2`: `φ_λ(t₁) φ_λ(t₂)` is the same double integral of
  `φ_λ(arcosh |cosh t₁ cosh t₂ + r e^{iψ} sinh t₁ sinh t₂|)`;
- the kernel form of the product formula with the kernel `K(t₁, t₂, t) ≥ 0` supported in
  `|t₁ − t₂| ≤ t ≤ t₁ + t₂` (Vilenkin–Klimyk Vol. 2 §11.4.6, (7)–(10)).

Proof route for the energy bound: with `u = φ_λ` real for real `α, β, λ` and
`E = u² + u'²/(λ² + ρ²)`, the Jacobi equation gives
`E' = −2((2α + 1) coth t + (2β + 1) tanh t) u'²/(λ² + ρ²)`; the coefficient is `≥ 0` for
`t > 0` under the hypotheses, since `(2α + 1) coth t + (2β + 1) tanh t ≥ 2ρ tanh t`, so `E`
decreases from `E(0) = 1`. The Laplace representation is proved for integers
`α > β ≥ 0` from the disc integral of §11.4.1 and extended by Carlson's theorem; the bound by
the imaginary part and the product formula follow from it, and boundedness from the bound with
the asymptotics of 0.3.

**Checks.**
- At `(α, β) = (1.3, 0.2)`, `λ = 0.7 − 0.4i`, `t = 0.9`, both sides of the Laplace
  representation are `0.58004 53793 + 0.02910 68436i`.
- `φ_λ^{(−1/2,−1/2)} = cos λt` satisfies the energy bound for real `λ`, with equality
  `E ≡ 1`.
- Negative control (the hypotheses of the energy bound): at `(α, β) = (−1/4, −3/2)`,
  `ρ = −3/4 < 0`, `λ = 0.3`, `t = 3`, `|φ_λ(t)| = 5.47284 88029`.
- Negative control (the strip): at `(α, β) = (1.3, 0.2)`, `λ = 0.5 − 2.8i`, so
  `|Im λ| = ρ + 0.3`, `|φ_λ(20)| = 331.25`.

*Needs:* 0.1, 0.3; Mathlib Carlson-type uniqueness (or a direct proof for real
`α > β > −1/2`).

### Examples

- `φ^{(−1/2,−1/2)}`, `φ^{(1/2,−1/2)}` and `φ^{(0,−1/2)}` are the spherical functions of `ℝ`,
  `ℍ³` and `ℍ²`.

### Dependencies

SpecialFunctionsHypergeometric Layer 1, §§4.1, 5.4 and 7.1; LaguerreJacobi §3.2; Mathlib Gamma
function.

## Layer 1: the Jacobi transform

### 1.1 Definition and elementary properties

Sources: DLMF 15.9.12; Klimyk–Vilenkin Part II Ch. 5 §2.4, (15), p. 233;
Heckman–Schlichtkrull Part I §5.4, (5.4.2), p. 83.

`jacobiWeight α β t`, `jacobiTransform α β f λ` and the measure `jacobiMeasure α β` (`Δ dt` on
`(0, ∞)`). Prove:
- **Evenness** (`jacobiTransform_neg`);
- **Holomorphy** (`differentiable_jacobiTransform`) for continuous compactly supported `f` and
  `α > −1`;
- **The Paley–Wiener estimate** (`norm_jacobiTransform_le`): for real `α ≥ β ≥ −1/2` and `f`
  continuous with support in `[−R, R]`, `|f̃(λ)| ≤ C e^{R |Im λ|}`;
- **The transform diagonalizes `L`** (`jacobiTransform_jacobiOperator`): for smooth even
  compactly supported `f`, `(L f)~ = −(λ² + ρ²) f̃`.

Proof route: `L` is symmetric for `Δ dt`, since `(Δ u')' = Δ L u`; the boundary terms vanish at
`0` because `f'(0) = 0` and `Δ(t) = O(t^{2α+1})`. The estimate is 0.4's bound by the imaginary
part with `φ_{i Im λ}(t) ≤ φ_0(t) e^{|Im λ| t}` (Laplace representation).

**Checks.**
- `jacobiWeight (−1/2) (−1/2) ≡ 1`, so the transform is the Fourier cosine transform; for
  `f(t) = e^{−t²}`, `f̃(1.5) = (√π/2) e^{−9/16} = 0.50495 68809`.
- `jacobiWeight (1/2) (−1/2) t = 4 sinh² t` and `jacobiWeight 0 (−1/2) t = 2 sinh t`.
- Negative control (the factors `2`): with the weight `sinh^{2α+1} t cosh^{2β+1} t` the
  Plancherel density of 1.2 becomes `2^{2ρ} (2π)⁻¹ |c|⁻²`, at `(1/2, −1/2)` equal to `2λ²/π`
  rather than `λ²/(2π)`.

*Needs:* 0.1, 0.4; Mathlib integration by parts.

### 1.2 Inversion, Plancherel and the unitary extension

Sources: Klimyk–Vilenkin Part II Ch. 5 §2.4, (15)–(16), p. 233; DLMF 15.9.12–15.9.13;
Wawrzyńczyk Theorem 18.6.1, p. 631; Heckman–Schlichtkrull Part II, Lecture 8, Example 8.3,
(8.23)–(8.24), pp. 181–182.

`jacobiPlancherelMeasure α β` is `(2π)⁻¹ |c(λ)|⁻² dλ` on `(0, ∞)`. Prove, for real `α > −1` and
`|β| ≤ α + 1`:
- **Inversion** (`jacobiTransform_inversion`): for smooth even compactly supported `f`,
  `f(t) = (2π)⁻¹ ∫₀^∞ f̃(λ) φ_λ(t) |c(λ)|⁻² dλ`;
- **Plancherel** (`jacobiTransform_plancherel`):
  `∫₀^∞ |f|² Δ dt = (2π)⁻¹ ∫₀^∞ |f̃|² |c|⁻² dλ`;
- **The unitary Jacobi transform** (`exists_jacobiTransform_linearIsometryEquiv`):
  `L²((0, ∞), Δ dt) ≅ L²((0, ∞), (2π)⁻¹ |c|⁻² dλ)`, extending the transform.

Proof route (Koornwinder): shift the contour of the Fourier-type integral of `f̃(λ) c(−λ)⁻¹ Φ_λ`
using the connection formula, the Paley–Wiener estimate and the absence of poles of `c(−λ)⁻¹`
in `Im λ ≤ 0` when `|β| ≤ α + 1`; surjectivity of the unitary extension from the completeness
of `{φ_λ}` (the Paley–Wiener theorem 1.3 gives a dense range).

**Checks.**
- `(α, β) = (−1/2, −1/2)`: `(2π)⁻¹ |c|⁻² = 2/π`, the Fourier cosine inversion
  `f(t) = (2/π) ∫₀^∞ f̃(λ) cos λt dλ`.
- `(α, β) = (0, 0)`: with `t = s/2` and `λ = 2τ`, the inversion is the Mehler–Fock inversion of
  SpecialFunctionsSU11MatrixElements §5.2 with density `τ tanh πτ`.
- `(α, β) = (1/2, −1/2)`: `(2π)⁻¹ |c|⁻² = λ²/(2π)`.
- Negative control (the range of `β`): at `(α, β) = (0, 3/2)`, outside `|β| ≤ α + 1`, the
  function `φ_{iμ}` with `μ = β − α − 1 = 1/2` lies in `L²(Δ dt)` and is orthogonal to every
  `φ_λ`, `λ ∈ ℝ`, so the continuous Plancherel formula fails there.

*Needs:* 0.3, 1.1; Mathlib `MeasureTheory.Lp` and `LinearIsometryEquiv`.

### 1.3 Discrete terms and the Paley–Wiener theorem

Sources: Klimyk–Vilenkin Part II Ch. 5 §2.4, p. 233 (the remark on poles); Heckman–Schlichtkrull
Part II, Lecture 8, Example 8.3, pp. 181–182; Wawrzyńczyk Theorem 18.8.1, p. 645.

Prove:
- **Discrete terms**: for real `α > −1` and `|β| > α + 1`, the inversion formula holds with the
  finitely many terms `d(λ_j) f̃(λ_j) φ_{λ_j}` at the poles `λ_j = i(|β| − α − 1 − 2j)` of
  `c(−λ)⁻¹` in `0 < Im λ`, with the residues of DLMF 15.9.13 as `d(λ_j)`;
- **The Paley–Wiener theorem**: for `α ≥ β ≥ −1/2`, the Jacobi transform maps the smooth even
  functions supported in `[−R, R]` onto the even entire functions `g` with
  `|g(λ)| ≤ C_N (1 + |λ|)^{−N} e^{R |Im λ|}` for every `N`.

Proof route: the poles cross the contour of 1.2; the Paley–Wiener theorem through the Abel
transform of 4.2 (Heckman–Schlichtkrull Part I §5.4, Theorem 5.4.2, p. 83), read for general
`(α, β)` by Koornwinder's Abel transform.

**Checks.**
- At `(α, β) = (0, 3/2)` there is one discrete term, at `λ₀ = i/2`.
- For `α ≥ β ≥ −1/2` there are no discrete terms (`|β| ≤ α + 1`).
- Negative control: `e^{−t²}` is not of compact support and its transform
  `(√π/2) e^{−λ²/4}` in the Fourier case grows like `e^{(Im λ)²/4}`, faster than any
  `e^{R |Im λ|}`.

*Needs:* 1.2; 4.2.

### Examples

- The Fourier cosine transform, the Mehler–Fock transform and the radial Fourier transform on
  `ℍ³` are the Jacobi transforms at `(−1/2, −1/2)`, `(0, 0)` and `(1/2, −1/2)`.

### Dependencies

Layer 0; Mathlib `Lp`, Fourier analysis; SpecialFunctionsSU11MatrixElements §5.2 for a Check.

## Layer 2: real hyperbolic space

### 2.1 The hyperboloid, the Lorentz group and the distance

Sources: Wawrzyńczyk §11.1, pp. 389–392, and §18.1, Example 1, pp. 611–613 (the Lobachevsky
space); Vilenkin–Klimyk Vol. 2 §9.1.9, p. 23; Heckman–Schlichtkrull Part II, Lecture 8,
Example 8.1, (8.3), p. 171.

`lorentz`, `hyperboloid`, `basePoint`, `hyperbolicDist`, `lorentzGroup`, `rotationSubgroup`,
`orbitMap` as in Conventions. Prove:
- **Transitivity** (`exists_orbitMap_eq`): every `x ∈ ℍⁿ` is `g o`;
- **Distance** (`hyperbolicDist_basePoint`): `d(o, x) = arcosh x₀` and `d(gx, gy) = d(x, y)`;
- `K` is compact and isomorphic to `SO(n)`, acting on `(x₁, …, xₙ)`;
- **Cartan decomposition in coordinates**: every `g ∈ G` is `k₁ a_t k₂` with
  `k₁, k₂ ∈ K`, `t = d(o, g o) ≥ 0` and `a_t` the boost in the `(x₀, x₁)`-plane; `d` is a metric
  and `(ℍⁿ, d)` is the Riemannian distance of the induced metric.

Proof route: `a_t o = (cosh t, sinh t, 0, …)`; rotate `(x₁, …, xₙ)` into the `x₁`-axis by `K`.

**Checks.**
- `[o, o] = 1`, and `(−1, 0, …, 0)` satisfies `[x, x] = 1` but is not in `ℍⁿ` (negative control
  for the sheet).
- `d(o, (cosh 1, sinh 1, 0)) = 1`, while the Euclidean distance is `1.29461 74807` (negative
  control).
- `diag(−1, −1, 1)` has determinant `1` and preserves `[·, ·]` but maps `ℍ²` to the lower
  sheet, so it is not in `lorentzGroup 2` (negative control for the condition on the sheet).
- The boost `a_t` is in `lorentzGroup n` and the rotations of `(x₁, …, xₙ)` are in `K`.
- `SO₀(n, 1)/SO(n)` with this action is RealSemisimpleLieGroups §5.2's symmetric space of
  `SO₀(n, 1)`.

*Needs:* Mathlib `Matrix.SpecialLinearGroup`, `Real.arcosh`.

### 2.2 The invariant volume

Sources: Wawrzyńczyk §11.1, (11.1.6), p. 392; Vilenkin–Klimyk Vol. 2 §9.1.9, p. 23;
Heckman–Schlichtkrull Part I §5.4, (5.4.3), p. 83 (horospherical coordinates).

`hyperboloidChart`, `hyperbolicMeasure`, `sphereArea`. Prove:
- **Invariance** (`map_hyperbolicMeasure`) under `G`;
- **Polar coordinates** (`lintegral_hyperbolicMeasure_radial`): for `n ≥ 1`,
  `∫ F(d(o, x)) dm = ω_{n−1} ∫₀^∞ F(t) sinh^{n−1} t dt`, and the full form
  `dm = sinh^{n−1} t dt dω`;
- **Horospherical coordinates** (`lintegral_hyperbolicMeasure_horospherical`): on `ℍ^{m+1}`,
  `x(s, v) = (cosh s + |v|² e^{−s}/2, e^{−s} v, −sinh s − |v|² e^{−s}/2)` and
  `dm = e^{−ms} dv ds`;
- `m` is the Riemannian volume of the induced metric, and the Haar measure of `G` pushes to a
  multiple of `m` under `g ↦ g o`.

Proof route: invariance under `K` is invariance of the chart under rotations; invariance under
the boosts is a change of variables in the chart, and `G = K A K`. Polar coordinates: `y = sinh t ω`
in the chart.

**Checks.**
- `ω₁ = 2π`, `ω₂ = 4π`, `ω₃ = 2π² = 19.73920 88022`.
- The hyperbolic disc of radius `1` in `ℍ²` has area `2π(cosh 1 − 1) = 3.41227 62653`; the chart
  measure `dy` without the factor `1/x₀` gives `π sinh² 1 = 4.33884 68454` (negative control).
- The ball of radius `1` in `ℍ³` has volume `π(sinh 2 − 2) = 5.11093 27057`.
- `x(s, v)` lies on `ℍ^{m+1}`: `x₀² − e^{−2s}|v|² − x_{m+1}² = 1`.

*Needs:* 2.1; Mathlib change of variables, `MeasureTheory.Measure.toSphere`.

### 2.3 The Laplace–Beltrami operator

Sources: Wawrzyńczyk §11.5, (11.5.1)–(11.5.8), Theorem 11.5.1, pp. 411–412; Vilenkin–Klimyk
Vol. 2 §9.3.2, (5)–(7), pp. 47–48; Heckman–Schlichtkrull Part II, Lecture 8, Example 8.1, (8.4),
pp. 171–172.

`hyperbolicLaplacian n f x` as in Conventions. Prove:
- **Invariance** (`hyperbolicLaplacian_comp`): `Δ(f ∘ g) = (Δf) ∘ g` on `ℍⁿ`;
- **Radial part** (`hyperbolicLaplacian_radial`):
  `Δ(F ∘ d(o, ·))(x) = F''(t) + (n − 1) coth t F'(t)` at `t = d(o, x) > 0`;
- `Δ` is the Laplace–Beltrami operator of the induced metric, symmetric and negative
  semidefinite on `C_c^∞(ℍⁿ)` for `m`, and generates the algebra of `G`-invariant differential
  operators on `ℍⁿ`.

Proof route: `g` commutes with the homogeneous extension and with the wave operator. The radial
part: the homogeneous extension of `F(arcosh x₀)` is `F(arcosh(y₀/√[y, y]))`; differentiate.

**Checks.**
- `Δ x₀ = n x₀` on `ℍⁿ` (`x₀ = cosh t`: `cosh t + (n − 1) coth t sinh t`).
- Negative control (the homogeneous extension): the wave operator applied to `x₀` itself gives
  `0`, not `n x₀`.
- The radial part at `(α, β) = (n/2 − 1, −1/2)` is the Jacobi operator `L`:
  `(2α + 1) coth t + (2β + 1) tanh t = (n − 1) coth t`.

*Needs:* 2.1; Mathlib iterated derivatives.

### 2.4 The boundary sphere, plane waves and the Poisson kernel

Sources: Wawrzyńczyk Theorem 11.5.1, (11.5.6), p. 412; §18.1, Proposition 18.1.6,
(18.1.12)–(18.1.15) and Lemma 18.1.7, pp. 610–611; the harmonic functions of (18.1.16), p. 613.

`boundaryVector n b = (1, b)` for `b ∈ S^{n−1}`, `sphereMeasure n`. Prove:
- **Plane waves** (`hyperbolicLaplacian_planeWave`):
  `Δ[x, b̃]^{−μ} = μ(μ − n + 1)[x, b̃]^{−μ}`;
- **Poisson integrals are harmonic** (`hyperbolicLaplacian_poisson`): for continuous `F` on
  `S^{n−1}`, `Δ ∫ [x, b̃]^{1−n} F(b) dσ(b) = 0`;
- `G` acts on `S^{n−1}` by `g · b = (g b̃)'/(g b̃)₀`, with Jacobian `(g⁻¹ b̃)₀^{1−n}` for `dσ`,
  and `[g x, b̃] = [x, g⁻¹ b̃]` relates the plane waves at `g · b` and `b`;
- `[x, b̃] > 0` on `ℍⁿ`, and `∫ [x, b̃]^{1−n} dσ(b) = 1`.

Proof route: `[y, b̃]` is linear and `[b̃, b̃] = 0`, so the wave operator of
`([y, b̃]/√[y, y])^{−μ}` is a two-line computation; the Poisson kernel is the plane wave at
`μ = n − 1`.

**Checks.**
- At `μ = iλ + ρ`, `μ(μ − n + 1) = −(λ² + ρ²)`.
- `[b̃, b̃] = 0` and `[o, b̃] = 1`.
- For `n = 2` and the boost `a_{0.8}`, the Jacobian identity
  `∫ F(g⁻¹ · b) [g o, b̃]^{−1} dσ(b) = ∫ F dσ` holds for `F(θ) = cos² θ + 0.3 sin θ`
  (both sides `1/2`), while without the Jacobian the two sides are `0.57218` and `1/2`
  (negative control).

*Needs:* 2.3; Mathlib `MeasureTheory.Measure.toSphere`, `MeasureTheory.average`.

### 2.5 The Gel'fand pair

Sources: SpecialFunctionsGroupModels §5.1 (Gel'fand's criterion and its symmetric-pair form);
Wawrzyńczyk §18.3, Corollary 18.3.3, p. 622.

Prove:
- **`(SO₀(n, 1), SO(n))` is a Gel'fand pair** (`isGelfandPair_lorentzGroup`), by the involution
  `g ↦ J (gᵀ)⁻¹ J`, `J = diag(1, −1, …, −1)`, which fixes `K` and inverts the boosts;
- `G` is unimodular, and `G = K P` with `P = {p | θ p = p⁻¹}` the symmetric positive elements.

**Checks.**
- `θ(a_t) = a_{−t}` and `θ(k) = k` for `k ∈ K`.
- `θ` is an automorphism: `θ(gh) = θ(g) θ(h)`, and `θ² = id`.
- Negative control: `(SO₀(n, 1), {1})` is not a Gel'fand pair.

*Needs:* 2.1, 2.2; SpecialFunctionsGroupModels §5.1.

### Examples

- `ℍ²` with `SO₀(2, 1) ≅ PSL(2, ℝ)` and `ℍ³` with `SO₀(3, 1) ≅ PSL(2, ℂ)`.

### Dependencies

Mathlib matrices, measure theory and derivatives; SpecialFunctionsGroupModels §5.1;
RealSemisimpleLieGroups §5.2 for a Check.

## Layer 3: spherical functions on `ℍⁿ`

### 3.1 Harish-Chandra's integral and the eigenvalue equation

Sources: Wawrzyńczyk §18.1, Example 1, pp. 611–613, and §11.3, (11.3.1), p. 401;
Vilenkin–Klimyk Vol. 2 §9.3.2, (5)–(7), pp. 47–48; Heckman–Schlichtkrull Part II, Lecture 8,
Example 8.1, pp. 171–172.

`sphericalFunction n λ x`. Prove, for `n ≥ 2`:
- **Harish-Chandra's integral** (`sphericalFunction_eq_average`):
  `φ_λ(x) = ∫ [x, b̃]^{−(iλ+ρ)} dσ(b)`;
- **Eigenfunction** (`hyperbolicLaplacian_sphericalFunction`): `Δφ_λ = −(λ² + ρ²) φ_λ`;
- `φ_λ` is the unique `K`-invariant eigenfunction of `Δ` with that eigenvalue and value `1` at
  `o`.

Proof route: the integral is `K`-invariant and an eigenfunction by 2.4; its radial part solves
the Jacobi equation at `(n/2 − 1, −1/2)` (2.3), is continuous at `0` with value `1`, and
`α = n/2 − 1 ≥ 0`, so 0.1's uniqueness identifies it.

**Checks.**
- `n = 3`: `φ_λ(x) = sin λt/(λ sinh t)` (0.2).
- `φ_{±iρ} ≡ 1`, and `∫ [x, b̃]^{0} dσ = 1` at `λ = iρ`.
- Negative control (the second Jacobi parameter): `(α, β) = (n/2 − 1, 0)` gives, for `n = 3`,
  `φ_1(1) = 0.59651 55509 ≠ sin 1/sinh 1`.

*Needs:* 0.1, 0.2, 2.3, 2.4.

### 3.2 Spherical functions of the Gel'fand pair

Sources: Wawrzyńczyk Theorem 18.3.5, p. 622, Corollaries 18.3.3–18.3.4, p. 622;
SpecialFunctionsGroupModels §5.2.

Prove, for `n ≥ 2` and the normalized Haar measure `ν` of `K`:
- **`φ_λ ∘ orbitMap` is spherical** (`isSphericalFunction_sphericalFunction`) in the sense of
  SpecialFunctionsGroupModels §5.2;
- **Classification** (`isSphericalFunction_iff`): every spherical function is
  `φ_λ ∘ orbitMap` for some `λ ∈ ℂ`, and `φ_λ = φ_μ` exactly when `μ = ±λ`.

Proof route: the functional equation from Harish-Chandra's integral and the Jacobian of 2.4;
conversely a spherical function is a `K`-invariant eigenfunction of `Δ` (SpecialFunctionsGroupModels
§5.2 and the mean-value property), so 3.1's uniqueness applies.

**Checks.**
- `φ_λ ∘ orbitMap` is bi-`K`-invariant because `d(o, k₁ g k₂ o) = d(o, g o)`.
- The eigenvalue `−(λ² + ρ²)` takes each value at exactly `±λ`.
- Negative control: `2 φ_λ` satisfies the eigenvalue equation but not `φ(1) = 1` and not the
  functional equation.

*Needs:* 3.1; SpecialFunctionsGroupModels §5.2.

### 3.3 Boundedness and positive definiteness

Sources: Wawrzyńczyk §18.5, Theorems 18.5.4–18.5.5, p. 631; Vilenkin–Klimyk Vol. 2 §9.2.8,
pp. 39–40; Heckman–Schlichtkrull Part II, Lecture 8, Example 8.1, p. 172.

Prove:
- `φ_λ` is bounded on `ℍⁿ` exactly when `|Im λ| ≤ ρ` (0.4 at `α = n/2 − 1 ≥ β = −1/2`);
- `φ_λ` is positive definite on `G` exactly when `λ ∈ ℝ` or `λ ∈ i[−ρ, ρ]`;
- `|φ_λ| ≤ 1` for `λ ∈ ℝ ∪ i[−ρ, ρ]`.

**Checks.**
- `n = 2`: `φ_λ(x) = P_{−1/2+iλ}(x₀)`, and the bound `|φ_λ| ≤ 1` for `λ ∈ ℝ` is
  SpecialFunctionsSU11MatrixElements §2.1's `|𝔓| ≤ 1`.
- `φ_{iρ} = 1` is positive definite, the coefficient of the trivial representation.
- Negative control: for `λ = i(ρ + 1)` the function `φ_λ` is unbounded, so it is not positive
  definite.

*Needs:* 0.4, 3.2, 3.4; Tau Ceti positive-definite functions.

### 3.4 The spherical principal series

Sources: Wawrzyńczyk §11.7, Theorem 11.7.1, p. 419 (`n = 3`); Theorem 18.5.4, p. 631;
Vilenkin–Klimyk Vol. 2 §9.2.6, p. 35, and §9.2.8, pp. 39–40.

The spherical principal series `π_λ` of `G` on `L²(S^{n−1}, dσ)`:
`(π_λ(g) F)(b) = (g⁻¹ b̃)₀^{−(iλ+ρ)} F(g⁻¹ · b)`, a multiplier representation of
SpecialFunctionsGroupModels Layer 1. Prove:
- `π_λ` is a continuous representation, unitary exactly when `λ ∈ ℝ`;
- its `K`-fixed vector `1` has coefficient `⟪1, π_λ(g) 1⟫ = φ_λ(g o)`;
- `π_λ` is irreducible for `λ ∈ ℝ \ {0}` (for `n = 2, 3` through NoncompactQuantumSymmetry M4 and
  M4.Lorentz), and `π_λ ≅ π_{−λ}` by the Knapp–Stein intertwiner;
- the complementary series: for `λ ∈ i(−ρ, ρ) \ {0}`, `π_λ` is unitarizable by an invariant
  inner product whose kernel is a power of `|b − b'|` (Vilenkin–Klimyk Vol. 2 §9.2.8).

**Checks.**
- The multiplier at `g = a_t`, `b = (1, 0, …)` is `e^{(iλ+ρ)t}`.
- `n = 2`: under `SO₀(2, 1) ≅ PSL(2, ℝ) ≅ SU(1, 1)/{±1}`, `π_λ` is equivalent to the principal
  series of SpecialFunctionsGroupModels §2.1 at `τ = −1/2 + iλ`.
- Negative control: the multiplier `(g⁻¹ b̃)₀^{−iλ}` without `ρ` does not give a unitary
  representation for real `λ`.

*Needs:* 2.4, 3.1; SpecialFunctionsGroupModels Layer 1, §2.1, §5.3; NoncompactQuantumSymmetry
M4, M4.Lorentz.

### Examples

- For `n = 3`, the spherical functions `sin λt/(λ sinh t)` of `SL(2, ℂ)/SU(2)` (Wawrzyńczyk
  (11.3.1)).

### Dependencies

Layers 0 and 2; SpecialFunctionsGroupModels Layer 1 and §§5.1–5.3; NoncompactQuantumSymmetry M4.

## Layer 4: harmonic analysis on `ℍⁿ`

### 4.1 The spherical transform

Sources: Wawrzyńczyk §11.3, Theorem 11.3.1, (11.3.5)–(11.3.6), p. 402 (`n = 3`); Theorem 18.6.1,
p. 631; Vilenkin–Klimyk Vol. 2 §10.1.2, pp. 160–161.

`sphericalTransform n f λ`, `plancherelConstant n`. Prove, for `n ≥ 2`:
- **The spherical transform is a Jacobi transform** (`sphericalTransform_radial`): for radial
  `f = F ∘ d(o, ·)`, `Sf(λ) = ω_{n−1} 2^{1−n} F̃(λ)` at `(α, β) = (n/2 − 1, −1/2)`;
- **Inversion and Plancherel** (`sphericalTransform_inversion`): for `F` smooth, even and of
  compact support, `F(t) = C_n ∫₀^∞ Sf(λ) φ_λ(t) |c(λ)|⁻² dλ` and
  `∫ |f|² dm = C_n ∫₀^∞ |Sf(λ)|² |c(λ)|⁻² dλ`;
- `S(f * h) = Sf · Sh` for radial `f, h` (SpecialFunctionsGroupModels §5.2), and `S` extends to a
  unitary map of the radial part of `L²(ℍⁿ)`.

Proof route: polar coordinates (2.2), `Δ(t) = 2^{n−1} sinh^{n−1} t` at
`(n/2 − 1, −1/2)`, and 1.2.

**Checks.**
- `C₂ = C₃ = 1/(2π²) = 0.05066 05918` and `C₄ = 2/π³ = 0.06450 30689`.
- For `n = 3`, `C₃ |c(λ)|⁻² = λ²/(2π²)`, Wawrzyńczyk's density in (11.3.6).
- Negative control: the constant `(2π)⁻¹` of 1.2 in place of `C₃` multiplies the right side of
  the Plancherel formula on `ℍ³` by `2π²/(2π) = π`.

*Needs:* 1.2, 2.2, 3.1.

### 4.2 The Abel transform

Sources: Heckman–Schlichtkrull Part I §5.4, (5.4.2)–(5.4.5), Theorem 5.4.2, Proposition 5.4.3,
pp. 83–84; Wawrzyńczyk §18.7, (18.7.12), p. 640.

`abelTransform m F s` on `ℍ^{m+1}`. Prove:
- **Evenness** (`abelTransform_neg`);
- **Spherical transform = Fourier ∘ Abel** (`sphericalTransform_eq_integral_abelTransform`):
  `S(F ∘ d(o, ·))(λ) = ∫ 𝒜F(s) e^{iλs} ds`;
- **`ℍ³`** (`abelTransform_two`): `𝒜F(s) = 2π ∫_{cosh s}^∞ F(arcosh u) du`;
- **Support**: `F` supported in `[0, R]` gives `𝒜F` supported in `[−R, R]`, and `𝒜` is a
  bijection of smooth even compactly supported functions (Heckman–Schlichtkrull Proposition
  5.4.3), with explicit inverse for odd `n` by `(d/d cosh s)^{(n−1)/2}`.

Proof route: in the horospherical coordinates of 2.2, `[x(s, v), b̃] = e^{−s}` for
`b̃ = (1, 0, …, 0, −1)`, so `f̂(λ, b)` of 4.3 at this `b` is `∫ 𝒜F(s) e^{−iλs} ds` for radial
`f`, and it equals `Sf(λ)` (4.3); evenness follows from the evenness of `S` (0.1) and the
injectivity of the Fourier transform.

**Checks.**
- `[x(s, v), (1, 0, …, 0, −1)] = e^{−s}` on the horospherical chart.
- `F(t) = e^{−cosh t}` on `ℍ³`: `𝒜F(s) = 2π e^{−cosh s}`, so
  `S(F ∘ d)(λ) = 4π K_{iλ}(1)` with the modified Bessel function `K_ν`.
- Negative control: without the factor `e^{−ms/2}`, `𝒜F` is not even.
- `n = 2`: `𝒜F(s) = √2 ∫_{|s|}^∞ F(t) sinh t (cosh t − cosh s)^{−1/2} dt`, the form against
  which the local adapters of AnalyticNumberTheoryPartII §6.12 are compared.

*Needs:* 2.2, 3.1, 4.1; Mathlib Fourier transform.

### 4.3 The Helgason–Fourier transform

Sources: Wawrzyńczyk §18.7, (18.7.12)–(18.7.13), p. 640; Theorem 18.8.1, p. 645;
Heckman–Schlichtkrull Part II, Lecture 8, Example 8.1, pp. 171–172.

`helgasonFourier n f λ b`. Prove, for `n ≥ 2` and `f` smooth of compact support:
- **Inversion and Plancherel** (`helgasonFourier_inversion`):
  `f(x) = C_n ∫₀^∞ ∫ f̂(λ, b) [x, b̃]^{−iλ−ρ} dσ(b) |c(λ)|⁻² dλ` on `ℍⁿ` and
  `∫ |f|² dm = C_n ∫₀^∞ ∫ |f̂(λ, b)|² dσ(b) |c(λ)|⁻² dλ`;
- **The transform diagonalizes `Δ`** (`helgasonFourier_hyperbolicLaplacian`):
  `(Δf)^(λ, b) = −(λ² + ρ²) f̂(λ, b)`;
- **Equivariance**: `(f ∘ g⁻¹)^(λ, b) = (g⁻¹ b̃)₀^{iλ−ρ} f̂(λ, g⁻¹ · b)`, that is
  `(f ∘ g⁻¹)^(λ, ·) = π_{−λ}(g) f̂(λ, ·)` with the representation of 3.4;
- the unitary extension `L²(ℍⁿ, m) ≅ L²((0, ∞) × S^{n−1}, C_n |c|⁻² dλ dσ)`, onto the subspace of
  the symmetry `f̂(−λ, ·) = A_λ f̂(λ, ·)` with the intertwiner of 3.4;
- **The Paley–Wiener theorem** (Wawrzyńczyk Theorem 18.8.1).

Proof route: for radial `f`, `f̂(λ, b) = Sf(λ)` by 3.1, and the inversion is 4.1; in general,
average `f ∘ g` over `K` (the radialization) at each point and use 3.1 again.

**Checks.**
- For radial `f`, `f̂(λ, b) = Sf(λ)` for every `b`.
- `f̂(−iρ, b) = ∫ f dm` (the exponent is `0`).
- Negative control: dropping `|c(λ)|⁻²` from the inversion fails already for radial `f` on
  `ℍ³`, where it is `λ²`.

*Needs:* 2.4, 3.1, 3.4, 4.1.

### 4.4 The hyperbolic plane and three-space

Sources: Wawrzyńczyk §11.3–§11.4, (11.3.5)–(11.3.6), (11.4.1), p. 402; Klimyk–Vilenkin Part II
Ch. 5 §2.3, p. 232.

Prove:
- `n = 2`: the spherical transform is the Mehler–Fock transform of
  SpecialFunctionsSU11MatrixElements §5.2 with density `πλ tanh πλ`, and the Helgason–Fourier
  transform on the disc model `SU(1, 1)/K` agrees with 4.3 under `ℍ² ≅ 𝔻`;
- `n = 3`: `S(F ∘ d)(λ) = (4π/λ) ∫₀^∞ F(t) sinh t sin λt dt`, with inversion
  `F(t) = (1/(2π²)) ∫₀^∞ Sf(λ) (sin λt/(λ sinh t)) λ² dλ`.

**Checks.**
- `n = 3`, `F(t) = e^{−t²}`: both `∫ |f|² dm = 4π ∫₀^∞ e^{−2t²} sinh² t dt` and
  `(1/(2π²)) ∫₀^∞ |Sf|² λ² dλ` equal `2.55427 67443`.
- `n = 2`: `C₂ |c^{(0,−1/2)}(λ)|⁻² = πλ tanh πλ/(2π²)`.
- Negative control: using `φ^{(0,0)}` for `ℍ²` without halving `t` gives the conical function
  of `cosh 2t`, not of `cosh t`.

*Needs:* 4.1, 4.3; SpecialFunctionsSU11MatrixElements §5.2.

### Examples

- Radial Gaussians on `ℍ³` and the heat kernel of `ℍ³`, `(4πs)^{−3/2} (t/sinh t) e^{−s−t²/(4s)}`.

### Dependencies

Layers 1–3; Mathlib Fourier transform.

## Downstream consumers

- Roadmaps on harmonic analysis of complex and quaternionic hyperbolic spaces and on the Selberg
  trace formula in dimension `n ≥ 3`, which the same project plans as sequels.

## Beyond this roadmap (a roadmap for a roadmap; do not implement)

The following material lies outside this roadmap. It is recorded only to fix the boundary.
Contributors should not attempt it under this roadmap.

- **Complex, quaternionic and octonionic hyperbolic spaces** as geometric objects: their
  groups `SU(n, 1)`, `Sp(n, 1)`, `F₄₍₋₂₀₎`, Laplacians and Helgason–Fourier transforms. Their
  spherical functions are Jacobi functions with `(α, β) = (n − 1, 0)`, `(2n − 1, 1)` and
  `(7, 3)` (Vilenkin–Klimyk Vol. 2 §11.4.1), so Layers 0–1 cover their radial analysis.
- **Pseudo-Riemannian hyperboloids** `X_{p,q}` and their discrete series
  (Heckman–Schlichtkrull Part II).
- **Higher-rank spherical functions**, Harish-Chandra's `c`-function in general and the
  Gindikin–Karpelevich formula.
- **Jacobi functions of the second kind** and the Jacobi transform on non-even functions.
- **Heat kernels and wave equations** on `ℍⁿ` for general `n`.

## Prior formalization

[lean-SFVK](https://github.com/bjbraams/lean-SFVK) (Apache-2.0) is the same author's project on
special functions and group representations. Its `SFVK/RankOne/` modules define, without
`sorry`, the Jacobi function, the Jacobi operator, the Harish-Chandra series, the `c`-function,
the Jacobi weight and transform, the Lorentz form, the hyperboloid, the Lorentz group and its
rotation subgroup, the hyperbolic volume and Laplacian, and the spherical, Abel and
Helgason–Fourier transforms, with the conventions used here, and state the theorems of the layers
with conversion lemmas to lean-DLMF's Jacobi function (written there as `Γ(α + 1) 𝐅`). Its
modules are `SFVK/RankOne/Basic/Jacobi.lean` and `SFVK/RankOne/Basic/Hyperbolic.lean` (the
definitions) and `SFVK/RankOne/Jacobi.lean`, `SFVK/RankOne/JacobiTransform.lean`,
`SFVK/RankOne/Hyperbolic.lean` and `SFVK/RankOne/Spherical.lean` (the theorems).

This roadmap specifies the mathematics intrinsically; lean-SFVK supplies prior proofs and
implementation references, and reused code carries attribution under the repository's porting
guidance.

## References

- G. Heckman and H. Schlichtkrull, *Harmonic Analysis and Special Functions on Symmetric Spaces*,
  Perspectives in Mathematics 16, Academic Press, 1994: Part I §5.4, pp. 83–84; Part II,
  Lecture 8, Examples 8.1 and 8.3, pp. 171–172 and 181–182.
- A. U. Klimyk and N. Ja. Vilenkin, *Representations of Lie Groups and Special Functions*, in
  A. A. Kirillov (ed.), *Representation Theory and Noncommutative Harmonic Analysis II*,
  Encyclopaedia of Mathematical Sciences 59, Springer, 1995, Part II Ch. 5 §§2.3–2.4,
  pp. 232–234.
- NIST Digital Library of Mathematical Functions, §15.9(ii), https://dlmf.nist.gov/15.9.ii.
- N. Ja. Vilenkin and A. U. Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2,
  Kluwer, 1993: §9.1.9, p. 23; §§9.2.6–9.2.8, pp. 35–40; §9.3.2, pp. 47–48; §9.4.10,
  pp. 92–93; §10.1.2, pp. 160–161; §§11.4.1 and 11.4.6, pp. 332–333 and 348–350.
- A. Wawrzyńczyk, *Group Representations and Special Functions*, Reidel and PWN, 1984: Ch. 11,
  §§11.1–11.7, pp. 389–423; Ch. 18, §§18.1–18.8, pp. 610–645.
