# Special functions from `SU(1,1)`: matrix elements, addition theorems and the Mehler–Fock transform

**Summary.** This roadmap identifies the matrix elements of the representations of `SU(1,1)`
(equivalently `SL(2, ℝ)`) with the classical functions of hypergeometric type and derives their
identities from the group law. Its central object is Vilenkin and Klimyk's function
`𝔓^τ_{mn}(cosh t)`, the matrix element of the principal series `T_{(τ,ε)}` between weight vectors
`e_m`, `e_n` on the boost `b_t`. The roadmap proves that it is a Gauss hypergeometric function, a
Legendre function `P_τ` at `m = n = 0`, an associated Legendre function in its first column and a
Jacobi polynomial in the integral and discrete cases, and it derives from the representation the
symmetries in the indices and the degree, the unitarity relations of the principal, complementary
and discrete series, the addition and multiplication theorems, the generating functions and the
convolution in the degree, the first-order and three-term recurrences, the matrix elements on the
other one-parameter subgroups, and the Mehler–Fock transform with its Parseval identity and
inversion, of order `0` and of every integer order. The roadmap is a synthesis of several sources
and follows none of them in its organization: it is ordered by the structure of the subject and
by proof dependency, from the function and its closed forms, through the unitary series and the
group-law identities, to recurrences and transforms. Its sources are Vilenkin–Klimyk
(*Representation of Lie Groups and Special Functions*, Vol. 1, Chapters 6 and 7), Wawrzyńczyk
(*Group Representations and Special Functions*, Chapter 10), Dieudonné (*Special Functions and
Linear Representations of Lie Groups*, §§13–14) and Miller (*Lie Theory and Special Functions*,
§5-18); most subsections cite several of them by locator; see [References](#references).

Mathlib has complex powers with the principal branch, interval and Bochner integrals, the
power-series Gauss function `ordinaryHypergeometric` on the unit disc, the Pochhammer polynomials
`ascPochhammer`, the Gamma function, `Real.arcosh` and `Real.arsinh`, Fourier series on `AddCircle`
with `fourierBasis`, `Lp` spaces and Hilbert bases. Tau Ceti has continuous representations
(`ContRepresentation`) with unitarity. Neither has any matrix element of a noncompact group as an
explicit function, the functions `𝔓^τ_{mn}`, or the Mehler–Fock transform.

The roadmap covers:
- the function `𝔓^τ_{mn}(cosh t)` as a circle integral, its identification with the matrix
  elements of the principal series, its holomorphy and parity, its hypergeometric forms, its
  Legendre and associated Legendre specializations, its symmetries in `m`, `n` and `τ`, and its
  vanishing and finite forms at integral and half-integral degree (Layer 1);
- the unitarity relations and bounds of the principal and complementary series, and the matrix
  elements of the discrete series in the Bergman model with their Jacobi-polynomial form and
  generating function (Layer 2);
- the addition theorem, the multiplication formulas and the product formula with the triangle
  kernel, the generating function with its row sums, the convolution in the degree and the shift
  of the degree by `1/2` (Layer 3);
- the derivatives in `t`, the ladder relations and the three-term recurrences (Layer 4);
- the matrix elements on the second hyperbolic and the parabolic subgroups, and the Mehler–Fock
  transform of order `0` and of integer order `m` (Layer 5).

## Scope and ownership

The roadmap is complete when Tau Ceti proves all of the following.

1. **The function `𝔓^τ_{mn}` and the principal series** (1.1): the identification of the matrix
   elements of `principalSeries τ e` on `g(α, t, γ)` with `e^{i(m'α + mγ)} 𝔓^τ_{m'm}(cosh t)`,
   the value at `t = 0`, holomorphy in `τ`, smoothness and parity in `t`.
2. **Closed forms** (1.2–1.3): the hypergeometric forms in `tanh²(t/2)` and `−sinh²(t/2)`, the
   Jacobi-function form, Laplace's integral for `𝔓^τ_{00}`, and the associated Legendre form of
   `𝔓^τ_{m0}`.
3. **Symmetries and the integral case** (1.4–1.5): the index symmetries, the reflection
   `τ ↦ −τ − 1`, conjugation, the vanishing at integral and half-integral degree and the relation
   to the `SU(2)` matrix elements.
4. **Unitary series** (2.1–2.2): the unitarity relations and the bounds `|·| ≤ 1` of the
   principal and complementary series, the boundedness range of `P_τ(cosh t)`, and the discrete
   series matrix elements in the Bergman model.
5. **Group-law identities** (3.1–3.3): the addition theorem, the multiplication and product
   formulas, generating functions, row sums, the convolution in the degree and the degree shift.
6. **Recurrences** (4.1–4.2): derivatives in `t`, ladder relations and three-term recurrences.
7. **Other subgroups and transforms** (5.1–5.3): the matrix elements on `SU11.boostY` and on the
   parabolic subgroup, and the Mehler–Fock transforms of order `0` and of integer order `m`.

This roadmap consumes, and does not prove:
- from SpecialFunctionsGroupModels (a roadmap of the same project; prose references by section
  number): the group `SU(1,1)` with its Euler angles (§0.1), the principal series
  `principalSeries τ e` on the circle with its weights (§2.1), the complementary weights (§2.2),
  the holomorphic and antiholomorphic discrete series on the weighted Bergman spaces (§2.3), the
  matrix elements with the addition theorem and the inverse (§§3.1–3.2), the Euler factorization
  of matrix elements (§3.3), the ladder operators (§4.1), the second-order equation of the matrix
  elements (§4.3), and the spherical functions and spherical transform of `(SU(1,1), K)` (§§5.2,
  5.4);
- from [NoncompactQuantumSymmetry](../NoncompactQuantumSymmetry/README.md): the irreducibility,
  equivalences, exhaustion and Plancherel theorem of the unitary dual of `SL(2, ℝ)` (M4, M4.P),
  through the dictionary of SpecialFunctionsGroupModels §2.1;
- from [SpecialFunctionsHypergeometric](../SpecialFunctionsHypergeometric/README.md): the Gauss
  function `𝐅` on the cut plane (its Layer 1) and Pfaff's transformation (its 5.1);
- from SpecialFunctionsLegendre (a roadmap of the Tau Ceti special-function series; prose
  references): `P^μ_ν` on `(1, ∞)` (its 1.1), Laplace's integral (its 8.2), the behaviour at
  infinity (its 4.5) and the addition theorem for general degree (its 10.2);
- from [LaguerreJacobi](../LaguerreJacobi/README.md): the Jacobi polynomials (its Layer 3);
- from SpecialFunctionsSU2MatrixElements (a roadmap of the same project): the `SU(2)` matrix
  elements `d^j_{m'm}(β)` (its §2.3) and the convention of Vilenkin and Klimyk (its §2.7).

**Boundaries.**
- SpecialFunctionsGroupModels owns the models and the general theory of matrix elements; this
  roadmap owns the explicit functions they produce on `SU(1,1)`. The second-order equation of the
  matrix elements is that roadmap's §4.3; this roadmap rewrites it in `z = cosh t` only as a
  consequence (4.2).
- NoncompactQuantumSymmetry owns the representation theory of `SL(2, ℝ)`: irreducibility,
  equivalence, the classification and the Plancherel theorem. This roadmap owns the explicit
  Mehler–Fock transform on `SU(1,1)/K`, whose unitarity it deduces from M4.P.
- SpecialFunctionsLegendre owns the functions `P^μ_ν`, `Q^μ_ν` and their analytic theory,
  including the addition theorem for general degree and Laplace's integral; its Beyond excludes
  the Mehler–Fock transformation, which this roadmap owns. This roadmap states its results through
  `𝔓^τ_{mn}` and records the agreement with `P^μ_ν` in prose.
- RankOneSymmetricSpaces (a sequel of the same project) owns the Jacobi functions
  `φ^{(α,β)}_λ` in general, the Harish-Chandra `c`-function, the Jacobi transform, the Abel
  transform and the Fourier transform on the hyperbolic spaces; it reads the Mehler–Fock transform
  of 5.2 as the instance `α = β = 0` of the Jacobi transform, through
  `φ^{(0,0)}_λ(t) = P_{−1/2+iλ/2}(cosh 2t) = 𝔓^{−1/2+iλ/2}_{00}(cosh 2t)`.

## Conventions

- **Groups, angles and matrix elements** are those of SpecialFunctionsGroupModels (§0.1, §3.1):
  `SU(1,1)` is the group `SU11` of matrices `[[a, b], [conj b, conj a]]` with `|a|² − |b|² = 1`;
  `g(α, t, γ) = k_α b_t k_γ` (`SU11.euler`) with `k_α = diag(e^{iα/2}, e^{−iα/2})`
  (`SU11.rotation`) and `b_t = [[cosh(t/2), sinh(t/2)], [sinh(t/2), cosh(t/2)]]` (`SU11.boost`);
  `D_{m'm}(g) = ⟪e_{m'}, U(g) e_m⟫` (`matrixElement`), conjugate-linear in the first slot.
- **The principal series** `T_{(τ,ε)} = principalSeries τ e` with `e = 2ε ∈ {0, 1}` acts on
  `L²` of the circle; its weight vectors are `e_m = e^{inθ}` with `m = n − ε`
  (`T(k_α) e_m = e^{imα} e_m`). Indices `m`, `n` of `𝔓^τ_{mn}` are these weights: real numbers
  with `m − n ∈ ℤ`, integers for `ε = 0` and half-integers for `ε = 1/2`.
- **The function `𝔓^τ_{mn}(cosh t)`** is `SU11.boostMatrixElement τ m n t`, a function of `t ∈ ℝ`
  rather than of `cosh t`, defined for every `τ ∈ ℂ` and real `m`, `n` by
  `(2π)⁻¹ ∫₀^{2π} A(θ)^{τ+n} A(−θ)^{τ−n} e^{i(m−n)θ} dθ`, where
  `A(θ) = cosh(t/2) + sinh(t/2) e^{iθ}`, with principal powers. Both bases have real part at least
  `cosh(t/2) − |sinh(t/2)| > 0`, so the powers are continuous and the definition has no junk
  values. This is Vilenkin–Klimyk's §6.5.4 (1), p. 314, Dieudonné's §14 (173)–(174), pp. 49–50,
  and Wawrzyńczyk's (10.2.14), p. 357; for `t ≥ 0` it is their `𝔓^τ_{mn}(cosh t)`. The
  identities are stated for all real `t` where they hold for all real `t`; parity (1.1) converts
  `t < 0` to `t > 0`.
- **Labels.** Vilenkin and Klimyk label the basis by `e^{−ikθ}` and write
  `t_{mn}(g(φ, t, ψ)) = e^{−i(mφ+nψ)} 𝔓_{mn}(cosh t)` (§6.5.2 (5), p. 313). In the labels here
  (weights of `e^{inθ}`) the same function appears with the phase `e^{+i(m'α+mγ)}`
  (SpecialFunctionsGroupModels §3.3); the functions `𝔓^τ_{mn}` themselves agree, because the
  relabelling `k ↦ −k` and the reflection `θ ↦ −θ` of the integral cancel (1.1).
- **Gamma factors.** Identities of the sources with quotients of Gamma functions are stated in a
  form without junk values: with `Complex.Gamma` replaced by its reciprocal `(Complex.Gamma x)⁻¹`,
  which is entire and equals Mathlib's value `(Complex.Gamma x)⁻¹ = 0` at the poles, or with the
  Pochhammer polynomial `(x)_k = ascPochhammer ℂ k` evaluated at `x` in place of
  `Γ(x + k)/Γ(x)`.
- **Hypergeometric functions.** `F(a, b; c; x)` for `|x| < 1` is Mathlib's
  `ordinaryHypergeometric`; on the cut plane it is SpecialFunctionsHypergeometric's `𝐅` times
  `Γ(c)`. The `tanh²(t/2)` forms only need the disc.
- **Transforms** are written in the variable `t > 0` with the measure `sinh t dt`, the image of
  `dx` on `(1, ∞)` under `x = cosh t`, and with the spectral parameter `ρ > 0`,
  `τ = −1/2 + iρ`, and the measure `ρ tanh(πρ) dρ`.
- Square brackets `[z^j] f` denote the coefficient of `z^j` in the Taylor series of `f` at `0`.

## Exact supplier contracts

### From Mathlib

- `cpow` with `Complex.cpow_add` and the principal branch; `intervalIntegral`, `integral`,
  `lintegral`, `MeasureTheory.Measure.withDensity`, `Lp`, `LinearIsometryEquiv`.
- `ordinaryHypergeometric` (`Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.lean`),
  `ascPochhammer`, `Complex.Gamma`, `Real.arcosh`, `Real.arsinh`, `Real.arctan`.
- `fourierBasis`, `haarAddCircle`, `HilbertBasis`, `HasSum`, `HasDerivAt`, `ContDiff`,
  `Differentiable`.

### From Tau Ceti

- `ContRepresentation` (`TauCeti/RepresentationTheory/Continuous/MatrixCoefficient.lean`), the
  carrier of `principalSeries`.

### From other roadmaps

- SpecialFunctionsGroupModels §§0.1, 2.1–2.3, 3.1–3.3, 4.1, 4.3, 5.2, 5.4, as listed under Scope
  and ownership. `Suggested.lean` copies the definitions it needs verbatim (`su11`, `SU11`,
  `SU11.entryA`, `SU11.entryB`, `SU11.ofPair`, `SU11.rotation`, `SU11.boost`, `SU11.boostY`,
  `SU11.euler`, `SU11.circleDenominator`, `SU11.circleAct`, `SU11.principalMultiplier`,
  `SU11.principalAction`, `SU11.IsPrincipalSeriesRealization`, `SU11.principalSeries`,
  `complementaryWeight`, `bergmanMeasure`, `SU11.diskAct`, `SU11.discreteAction`,
  `matrixElement`).
- [NoncompactQuantumSymmetry](../NoncompactQuantumSymmetry/README.md) M4 and M4.P, in 2.1 and
  5.2–5.3.
- [SpecialFunctionsHypergeometric](../SpecialFunctionsHypergeometric/README.md) Layer 1 and 5.1,
  in 1.2.
- SpecialFunctionsLegendre 1.1, 4.5, 8.2 and 10.2, in 1.3, 2.1 and 3.1.
- [LaguerreJacobi](../LaguerreJacobi/README.md) Layer 3, in 1.5 and 2.2.
- SpecialFunctionsSU2MatrixElements §§2.3, 2.7, in 1.5.

`Suggested.lean` imports no other roadmap.

## How to read the build

Layer 1 is the analysis of one explicit integral. The identification with the principal series
(1.1) is a change of variables on the circle; everything else in Layer 1 is classical analysis of
the integral: the binomial series gives the hypergeometric forms, the substitution `φ ↦ π − φ`
gives Laplace's integral, and the substitutions `θ ↦ −θ`, `θ ↦ θ + π` give the index symmetries
and parity. The symmetries that change `τ` or transpose the indices come from the Hermitian
adjoint and the intertwiners of SpecialFunctionsGroupModels §2.1, or from the hypergeometric form
and Euler's transformation.

Layers 2 and 3 apply the representation: unitarity gives the bounds, and the addition theorem of
SpecialFunctionsGroupModels §3.2 on the Euler angles of a product gives the addition and
multiplication theorems. The generating function is the Fourier series of the integrand, so the
row sums and the convolution in the degree are statements about products of Fourier series.
Layer 4 differentiates the addition theorem at the identity, which turns the ladder operators of
SpecialFunctionsGroupModels §4.1 into recurrences. Layer 5 is the hardest: the Mehler–Fock
transform needs the Plancherel theorem of NoncompactQuantumSymmetry M4.P restricted to
`K`-finite vectors, and its order-`m` form needs the matrix elements `𝔓^τ_{m0}` as kernels.

## Layer 1: the functions `𝔓^τ_{mn}`

### 1.1 Definition and the principal series

Sources: Vilenkin–Klimyk §6.5.1 (1)–(4), p. 311, §6.5.2 (1)–(5), pp. 312–313, §6.5.4 (1),
p. 314; Dieudonné §14 (170)–(174), pp. 49–50; Wawrzyńczyk (10.2.13)–(10.2.15), p. 357; Miller
§5-18 (5.159), (5.164), pp. 227–231.

Prove:
- **Principal-series matrix elements** (`SU11.principalSeries_matrixElement_euler_eq`): for every
  `τ ∈ ℂ`, `e`, integers `n'`, `n` and real `α`, `t`, `γ`, with `m' = n' − e/2`, `m = n − e/2`,
  `D_{m'm}(g(α, t, γ)) = e^{i(m'α + mγ)} 𝔓^τ_{m'm}(cosh t)`, where `D` is
  `matrixElement (principalSeries τ e) fourierBasis` at the indices `n'`, `n`; at `α = γ = 0` this
  is `D_{m'm}(b_t) = 𝔓^τ_{m'm}(cosh t)`;
- **Value at the identity** (`SU11.boostMatrixElement_zero`): `𝔓^τ_{mn}(1) = δ_{mn}` for
  `m − n ∈ ℤ`;
- **Holomorphy in the degree** (`SU11.differentiable_boostMatrixElement_degree`): `τ ↦ 𝔓^τ_{mn}(cosh t)`
  is entire;
- **Real analyticity in `t`** (`SU11.contDiff_boostMatrixElement_radius`): `t ↦ 𝔓^τ_{mn}(cosh t)` is real analytic
  on `ℝ`;
- **Parity** (`SU11.boostMatrixElement_neg`): `𝔓^τ_{mn}(cosh(−t)) = (−1)^{m−n} 𝔓^τ_{mn}(cosh t)`
  for `m − n ∈ ℤ`, where the left side is the value at `−t`;
- `𝔓^τ_{mn}(cosh t)` is the `(m − n)`th Fourier coefficient of the integrand in the sense of 3.3,
  so the functions with fixed `τ`, `n`, `t` determine the integrand.

The matrix element is `(2π)⁻¹ ∫ e^{−in'θ} |u|^{2τ} (u/|u|)^e e^{in θ'} dθ` with
`u = sinh(t/2) e^{iθ} + cosh(t/2)` and `e^{iθ'} = (cosh(t/2) e^{iθ} + sinh(t/2))/u`. On the circle
`|u|² = u ū`, `cosh(t/2) e^{iθ} + sinh(t/2) = e^{iθ} ū`, and the principal powers of `u` and `ū`
multiply (their arguments lie in `(−π/2, π/2)`), so the integrand is
`(cosh(t/2) + sinh(t/2) e^{iθ})^{τ−m} (cosh(t/2) + sinh(t/2) e^{−iθ})^{τ+m} e^{i(m−m')θ}`; the
substitution `θ ↦ −θ` gives the definition. The Euler phase is SpecialFunctionsGroupModels §3.3.
Holomorphy is differentiation under the integral; parity is the substitution `θ ↦ θ + π`, since
`sinh(−t/2) e^{iθ} = sinh(t/2) e^{i(θ+π)}`.

**Checks.**
- `𝔓^τ_{2,−1}(cosh 1.3) = −0.01150 64149 − 0.01597 50333 i` at `τ = 0.23 + 0.4i`, and the
  circle-model matrix element `D_{2,−1}(b_{1.3})` of `principalSeries τ 0` agrees to `10⁻³⁰`; so
  do `(n', n) = (0, 0), (1, 3), (−2, 2)` for both `e`.
- The factorization holds to `10⁻³⁰` at `(α, t, γ) = (0.7, 1.3, −2.1)`, `(n', n) = (2, −1)`, for
  `e = 0` and `e = 1`.
- Negative control: at these data `m'α + mγ = 3.5`, and the Vilenkin–Klimyk phase
  `e^{−i(m'α + mγ)} = −0.93646 + 0.35078 i` differs from `e^{i(m'α + mγ)} = −0.93646 − 0.35078 i`;
  with it the factorization fails.
- At `τ = 1`: `𝔓^1_{00}(cosh t) = cosh t`, `𝔓^1_{10}(cosh t) = sinh t / 2`,
  `𝔓^1_{01}(cosh t) = sinh t`.
- At `τ = 1/2`: `𝔓^{1/2}_{1/2,1/2}(cosh t) = cosh(t/2)` and
  `𝔓^{1/2}_{−1/2,1/2}(cosh t) = sinh(t/2)`.
- Negative control for parity: `𝔓^τ_{2,−1}(cosh(−1.3)) = +0.01150 64149 + 0.01597 50333 i`, the
  negative of the value at `t = 1.3`: the function of `t` is not even when `m − n` is odd.

*Needs:* SpecialFunctionsGroupModels §§0.1, 2.1, 3.1, 3.3; Mathlib `fourierBasis`, `cpow`.

### 1.2 Hypergeometric forms

Sources: Vilenkin–Klimyk §6.5.3 (1)–(3), p. 313, (1′), p. 314, §6.5.1 (5)–(7), pp. 311–312;
Miller §5-18 (5.159), p. 228.

Prove, for `m − n = k ∈ ℕ`:
- **The `tanh²` form** (`SU11.boostMatrixElement_eq_hypergeometric`):
  `𝔓^τ_{mn}(cosh t) = (τ − m + 1)_k / k! · cosh^{2τ}(t/2) tanh^k(t/2) F(t)`, where
  `F(t) = F(−τ − n, −τ + m; k + 1; tanh²(t/2))`, and for `m − n = −k` the same with `(m, n)`
  replaced by `(−m, −n)` (1.4);
- **The `−sinh²` form**: `𝔓^τ_{mn}(cosh t) = (τ − m + 1)_k / k! · sinh^k(t/2) cosh^{−(m+n)}(t/2) G`,
  where `G = F(−τ − n, τ − n + 1; k + 1; −sinh²(t/2))` is the continued function of
  SpecialFunctionsHypergeometric; by Pfaff's transformation (its 5.1) from the `tanh²` form;
- **The Jacobi-function form**: with `λ = i(2τ + 1)`, the last `F` is the Jacobi function
  `φ^{(k, −(m+n))}_λ(t/2) = F((ρ + iλ)/2, (ρ − iλ)/2; k + 1; −sinh²(t/2))`,
  `ρ = k − (m + n) + 1`, in the normalization of RankOneSymmetricSpaces.

The binomial series of both factors of the integrand, integrated term by term, give a double sum
whose diagonal is the hypergeometric series in `tanh²(t/2)` after Euler's transformation; the
Pochhammer factor replaces Vilenkin–Klimyk's `Γ(τ − n + 1)/Γ(τ − m + 1)` and is the polynomial
`(τ − m + 1) ⋯ (τ − n)`, so the statement has no junk at the poles.

**Checks.**
- At `τ = 0.23 + 0.4i`, `t = 1.3` the `tanh²` form agrees with the integral to `10⁻³⁰` for
  `(m, n) = (2, −1), (0, 0), (5/2, 1/2), (3, 3)`, and so does the `−sinh²` form.
- At `k = 0`, `m = n = 0`: `𝔓^τ_{00}(cosh t) = cosh^{2τ}(t/2) F(−τ, −τ; 1; tanh²(t/2))`.
- Negative control: the factor `Γ(τ + m + 1)/Γ(τ + n + 1)` in place of `(τ − m + 1)_k` gives at
  `(m, n) = (2, −1)` the value `−0.00166 47647 + 0.05137 79018 i`, which is `𝔓^τ_{−1,2}`, the
  transposed element (1.4), not `𝔓^τ_{2,−1}`.

*Needs:* 1.1; Mathlib `ordinaryHypergeometric`, `ascPochhammer`; SpecialFunctionsHypergeometric
Layer 1 and 5.1.

### 1.3 Legendre and conical functions

Sources: Vilenkin–Klimyk §6.5.7 (1)–(4), pp. 322–323, §6.5.10 (1)–(2), pp. 325–326;
Dieudonné §13 (150), p. 44, §14 (175), p. 50; Wawrzyńczyk §10.2, p. 357 (the Legendre function
`𝔓_ζ = 𝔓^ζ_{00}`).

Prove:
- **Laplace's integral** (`SU11.boostMatrixElement_zero_zero`):
  `𝔓^τ_{00}(cosh t) = π⁻¹ ∫₀^π (cosh t + sinh t cos φ)^τ dφ` for real `t`, so `𝔓^τ_{00}` is the
  Legendre function `P_τ(cosh t)` by SpecialFunctionsLegendre 8.2, and at `τ = −1/2 + iρ` the
  conical function `P_{−1/2+iρ}(cosh t)`;
- **Associated Legendre functions**: for an integer `m`,
  `𝔓^τ_{m0}(cosh t) = Γ(τ + 1)/Γ(τ − m + 1) · P^{−m}_τ(cosh t)` for `τ` off the poles, with
  SpecialFunctionsLegendre's `P^μ_ν` (its 1.1); for `m ≥ 0` the factor is `(τ − m + 1)_m`;
- **Zonal and associated spherical functions**: `g ↦ 𝔓^τ_{00}(cosh t)` is the spherical function
  of `principalSeries τ 0` for `(SU(1,1), K)` in the sense of SpecialFunctionsGroupModels §5.2, and
  `g(α, t, γ) ↦ e^{imα} 𝔓^τ_{m0}(cosh t)` are its associated spherical functions.

Laplace's integral is the definition with `m = n = 0`: the product of the two conjugate factors is
`(cosh t + sinh t cos θ)^τ`, and the symmetry `θ ↦ 2π − θ` halves the range.

**Checks.**
- `𝔓^{−1/2+0.8i}_{00}(cosh 0.9) = 0.83316 90033`, the value of SpecialFunctionsGroupModels §3.3's
  example and of `P_{−1/2+0.8i}(cosh 0.9)`.
- At `τ = 0.23 + 0.4i`, `t = 1.3`, `m = 1, 2, −1`: the quotient `𝔓^τ_{m0}/P^{−m}_τ` is
  `0.23 + 0.4i`, `−0.3371 − 0.216i`, `0.73525 01644 − 0.23910 57445 i`, the values of
  `Γ(τ + 1)/Γ(τ − m + 1)`.
- Negative control: with `P^{m}_τ` in place of `P^{−m}_τ` the quotient at `m = 1` is
  `0.73525 01644 − 0.23910 57445 i`, not `Γ(τ + 1)/Γ(τ) = 0.23 + 0.4i`.
- `𝔓^0_{00} = 1`, `𝔓^1_{00}(cosh t) = cosh t = P_1(cosh t)`.

*Needs:* 1.1; SpecialFunctionsLegendre 1.1 and 8.2; SpecialFunctionsGroupModels §5.2.

### 1.4 Symmetries

Sources: Vilenkin–Klimyk §6.5.5 (1)–(9), pp. 318–320; Miller §5-18 (5.161)–(5.163),
pp. 229–230 (the matrix of `g⁻¹`).

Prove, for `m − n ∈ ℤ`:
- **Sign reversal** (`SU11.boostMatrixElement_neg_neg`): `𝔓^τ_{−m,−n} = 𝔓^τ_{mn}`;
- **Transposition** (`SU11.boostMatrixElement_swap`):
  `𝔓^τ_{mn} / (Γ(τ + n + 1) Γ(τ − n + 1)) = 𝔓^τ_{nm} / (Γ(τ + m + 1) Γ(τ − m + 1))`, with
  reciprocal Gamma functions;
- **Reflection of the degree** (`SU11.boostMatrixElement_reflect`):
  `𝔓^{−τ−1}_{mn} / (Γ(τ − m + 1) Γ(τ + m + 1)) = (−1)^{m−n} 𝔓^τ_{mn} / (Γ(τ − n + 1) Γ(τ + n + 1))`;
- **Conjugation** (`SU11.conj_boostMatrixElement`): `conj 𝔓^τ_{mn} = 𝔓^{conj τ}_{mn}`; so
  `𝔓^τ_{mn}` is real for real `τ`, and `𝔓^{−1/2+iρ}_{mm}` and `𝔓^{−1/2+iρ}_{00}` are real.

Sign reversal is `θ ↦ −θ` and conjugation is conjugating the integrand followed by `θ ↦ −θ`.
Transposition follows from the hypergeometric form of 1.2 and Euler's transformation, or from the
inverse `D(g⁻¹)` of SpecialFunctionsGroupModels §3.2 and the Hermitian adjoint of §2.1, for `τ` off
the poles, and then everywhere by holomorphy (1.1). Reflection is the intertwiner `Q` of
Vilenkin–Klimyk §6.5.5 (3) between `T_{(τ,ε)}` and `T_{(−τ−1,ε)}` (equivalence consumed from
NoncompactQuantumSymmetry M4 on the unitary line) evaluated on `b_t`, extended by holomorphy.

**Checks.**
- At `τ = 0.23 + 0.4i`, `t = 1.3`: `𝔓^τ_{2,−1} = −0.01150 64149 − 0.01597 50333 i` and
  `𝔓^τ_{−1,2} = −0.00166 47647 + 0.05137 79018 i`; the transposition holds to `10⁻³⁰`.
- Negative control: the Gamma quotient in the opposite orientation,
  `Γ(τ + m + 1)Γ(τ − m + 1)/(Γ(τ + n + 1)Γ(τ − n + 1)) · 𝔓^τ_{nm}`, is
  `0.08533 09700 − 0.10360 31521 i`, not `𝔓^τ_{mn}`.
- `𝔓^{−τ−1}_{2,−1}(cosh 1.3) = 0.00166 47647 − 0.05137 79018 i`, and the reflection holds to
  `10⁻²⁵`; negative control: without the sign `(−1)^{m−n}` the right side is the negative.
- At `τ = 1`, `(m, n) = (1, 0)`: `𝔓^1_{10} / (Γ(2)Γ(2)) = sinh t / 2 = 𝔓^1_{01} / (Γ(3)Γ(1))`.

*Needs:* 1.1–1.2; SpecialFunctionsGroupModels §§2.1, 3.2; NoncompactQuantumSymmetry M4.

### 1.5 Integral and half-integral degree

Sources: Vilenkin–Klimyk §6.5.6 (1)–(4), pp. 320–321, §6.5.3 (4), p. 314.

Let `ℓ ≥ 0` with `2ℓ ∈ ℕ` and `m − ℓ`, `n − ℓ ∈ ℤ`. Prove:
- **Vanishing** (`SU11.boostMatrixElement_eq_zero_of_lt`): `𝔓^ℓ_{mn}(cosh t) = 0` when
  `|n| ≤ ℓ < |m|`;
- the span of the `e_m` with `|m| ≤ ℓ` is invariant under `principalSeries ℓ e` (`e = 2ℓ mod 2`),
  the representation on it is the `SU(2)`-type representation of dimension `2ℓ + 1`, and for
  `|m|, |m'| ≤ ℓ`,
  `𝔓^ℓ_{m'm}(cosh t) = i^{m−m'} ((ℓ+m)!(ℓ−m)!/((ℓ+m')!(ℓ−m')!))^{1/2} d^ℓ_{m'm}(it)`, where
  `d^ℓ_{m'm}(it)` is SpecialFunctionsSU2MatrixElements' finite sum for `d^ℓ_{m'm}(β)` (its §2.3)
  with `cos(β/2)`, `sin(β/2)` replaced by `cosh(t/2)`, `i sinh(t/2)`;
- for `|m|, |m'| ≤ ℓ` the function is `sinh^{|m'−m|}(t/2) cosh^{|m'+m|}(t/2)` times a Jacobi
  polynomial of degree `ℓ − max(|m|, |m'|)` in `cosh t` (LaguerreJacobi Layer 3).

The invariance is a degree count: for `|n| ≤ ℓ` the multiplier `|u|^{2ℓ}` times `e^{inθ'}` is a
trigonometric polynomial of degrees `−ℓ … ℓ` (`|u|² = u ū`), so its coefficients outside vanish.
The `SU(2)` formula is the analytic continuation `β = it` of SpecialFunctionsGroupModels'
Conventions (`k_α b_{it} k_γ = g(α + π/2, t, γ − π/2)`) applied to the polynomial representation.

**Checks.**
- At `τ = 0`: `𝔓^0_{10}(cosh t) = 0` while `𝔓^0_{01}(cosh t) = tanh(t/2)`: the vanishing needs
  `|n| ≤ ℓ < |m|`, not `|m| ≤ ℓ < |n|` (negative control for the orientation).
- At `ℓ = 1`, `t = 0.9`: `𝔓^1_{2,1} = 𝔓^1_{2,0} = 𝔓^1_{2,−1} = 0` to `10⁻³⁰`, while
  `𝔓^1_{1,2} = 0.09135 94`.
- At `ℓ = 1`, `t = 0.9`: the quotients `𝔓^ℓ_{m'm}/d^ℓ_{m'm}(it)` are `1`, `−1` at
  `(m', m) = (1, 1), (1, −1)`, and `√2 i`, `−i/√2` at `(0, 1)`, `(1, 0)`; at `ℓ = 3/2`,
  `(−1/2, −3/2)` gives `−√3 i`.

*Needs:* 1.1–1.2; SpecialFunctionsSU2MatrixElements §2.3; LaguerreJacobi Layer 3;
SpecialFunctionsGroupModels Conventions.

## Layer 2: the unitary series

### 2.1 Principal and complementary series

Sources: Vilenkin–Klimyk §6.5.1 (8), p. 312; Miller §5-18 (5.161), p. 229, (5.168)–(5.170),
pp. 232–233; Dieudonné §13 (151), p. 44, §14 (175), p. 50.

Prove:
- **Unitarity relations of the principal series** (`SU11.hasSum_norm_sq_boostMatrixElement`): for
  `Re τ = −1/2` and every `n`, `Σ_{k∈ℤ} |𝔓^τ_{n+k,n}(cosh t)|² = 1` and
  `Σ_{k∈ℤ} |𝔓^τ_{n,n+k}(cosh t)|² = 1`;
- **Bound** (`SU11.norm_boostMatrixElement_le_one`): `|𝔓^τ_{mn}(cosh t)| ≤ 1` for `Re τ = −1/2`,
  in particular `|P_{−1/2+iρ}(cosh t)| ≤ 1`;
- **Complementary series** (`SU11.hasSum_complementarySeries_weighted_norm_sq`): for real `−1 < τ < 0`, `ε = 0` and
  integers `m`, `n`, with `w = complementaryWeight τ`,
  `Σ_{k∈ℤ} w(k)/w(n) · |𝔓^τ_{kn}(cosh t)|² = 1` and `(w(m)/w(n))^{1/2} |𝔓^τ_{mn}(cosh t)| ≤ 1`;
  these are the matrix elements of NoncompactQuantumSymmetry M4's complementary series in the
  orthonormal basis `e_n / w(n)^{1/2}` of SpecialFunctionsGroupModels §2.2;
- **Boundedness range**: `t ↦ P_τ(cosh t)` is bounded on `[0, ∞)` exactly when
  `−1 ≤ Re τ ≤ 0`.

The principal series is unitary on `Re τ = −1/2` (SpecialFunctionsGroupModels §2.1); the sums are
Parseval for the unit vectors `T(b_t) e_n` and `T(b_t)* e_n`, and the bound is Cauchy–Schwarz. The
complementary relations are the same argument in the completion of NoncompactQuantumSymmetry M4,
whose orthonormal basis is `e_n/w(n)^{1/2}`. The boundedness range uses the asymptotics of `P_τ` at
infinity (SpecialFunctionsLegendre 4.5) and the reflection of 1.4.

**Checks.**
- At `τ = −1/2 + 0.8i`, `t = 0.9`, both sums are `1` to `10⁻²⁵` for `n = 0, 2` (`ε = 0`) and
  `n = −1/2, 3/2` (`ε = 1/2`), and `max |𝔓^τ_{mn}| = 0.83317` over `|m|, |n| ≤ 3`, at
  `m = n = 0`.
- Negative control: at `τ = 0.1`, `t = 1`, `Σ_k |𝔓^τ_{k0}|² = 1.05851 38265`.
- Complementary series at `τ = −0.3`, `t = 0.9`: the weighted sum is `1` to `10⁻²⁵` for
  `n = 0, 1, −2`; negative control: the unweighted sum is `0.95351 90712`.
- `P_1(cosh t) = cosh t` is unbounded (`Re τ = 1`), `P_0 = 1` and `P_{−1/2}(cosh t)` are bounded.

*Needs:* 1.1, 1.3–1.4; SpecialFunctionsGroupModels §§2.1–2.2, 3.2; NoncompactQuantumSymmetry M4;
SpecialFunctionsLegendre 4.5.

### 2.2 The discrete series in the Bergman model

Sources: Vilenkin–Klimyk §6.5.6 (5)–(10), pp. 321–322, §6.7.1 (11)–(12′), p. 333; Miller §5-18
(5.171)–(5.176), pp. 234–236.

For `k ≥ 2` let `C_j = C(k − 1 + j, j)` and `φ_j = C_j^{1/2} z^j`, the orthonormal basis of
SpecialFunctionsGroupModels §2.3; the weight of `φ_j` is `k/2 + j`.
`SU11.discreteMatrixElement k j' j g = ⟪φ_{j'}, discreteAction k g φ_j⟫` in `L²(bergmanMeasure k)`.
Prove:
- **Discrete-series matrix elements** (`SU11.discreteMatrixElement_euler`): with `m' = k/2 + j'`,
  `m = k/2 + j`,
  `D_{j'j}(g(α, t, γ)) = e^{i(m'α + mγ)} (C_j/C_{j'})^{1/2} 𝔓^{−k/2}_{m'm}(cosh t)`, where
  `D_{j'j}(g) = discreteMatrixElement k j' j g`;
- **Generating function** (`SU11.discreteMatrixElement_boost_coeff`):
  `(C_{j'}/C_j)^{1/2} D_{j'j}(b_t) = [z^{j'}] B(z)`, where
  `B(z) = (cosh(t/2) z + sinh(t/2))^j (sinh(t/2) z + cosh(t/2))^{−k−j}`;
- **Unitarity** (`SU11.hasSum_norm_sq_discreteMatrixElement`): `Σ_{j'} |D_{j'j}(g)|² = 1`;
- **Jacobi polynomials**: for `j' ≥ j`, the `tanh²` form of 1.2 terminates and
  `F(−j, k + j'; j' − j + 1; x) = j!/(j' − j + 1)_j · P^{(j'−j, k−1)}_j(1 − 2x)` at
  `x = tanh²(t/2)`, with LaguerreJacobi's Jacobi polynomial; for `j' < j` use the transposition of
  1.4;
- the antiholomorphic series has the conjugate matrix elements `conj D_{j'j}(g)`, the matrix
  elements of `D_k^−` (Miller (5.178), p. 237).

The coefficient form is the definition: `discreteAction k (b_t) z^j = B(z)`, and
`⟪z^{j'}, z^i⟫ = δ C_{j'}⁻¹`. The integral of 1.1 at `τ = −k/2`, `n = k/2 + j` is the same Taylor
coefficient by the residue theorem on the circle (Cauchy's formula for the coefficient), which gives
the identification.

**Checks.**
- At `k = 2`, `t = 0.9`: `D_{2,1}(b_t) = −0.54707 15360`, `𝔓^{−1}_{3,2} = −0.67002 30580`, and
  the quotient is `(C_1/C_2)^{1/2} = (2/3)^{1/2}`; at `k = 3`, `(j', j) = (1, 3)`, the quotient is
  `(10/3)^{1/2} = 1.82574 18584`.
- `D_{00}(b_t) = cosh^{−k}(t/2)`: `0.82200 12294` at `k = 2`, `t = 0.9`.
- `Σ_{j'} |D_{j'1}(b_{0.9})|² = 1` to `10⁻²⁵` for `k = 2, 3`.
- Negative control: without the factor `(C_j/C_{j'})^{1/2}` the quotient at `k = 2`, `(2, 1)` is
  `1 ≠ (2/3)^{1/2}`.
- The Jacobi form holds to `10⁻³⁰` at `(k, j', j) = (2, 2, 1), (2, 4, 2), (3, 3, 0)`.

*Needs:* 1.1–1.2, 1.4; SpecialFunctionsGroupModels §2.3; LaguerreJacobi Layer 3.

## Layer 3: identities from the group law

### 3.1 The addition theorem

Sources: Vilenkin–Klimyk §6.6.1 (1)–(2), pp. 326–327, §6.6.2 (1), (4), p. 327; Miller §5-18
(5.160), p. 229, (5.172), p. 235.

Prove:
- **The Euler angles of a product** (`SU11.cosh_of_boost_mul_euler`): if
  `boost t₁ * euler φ t₂ 0 = euler α t γ`, then
  `cosh t = cosh t₁ cosh t₂ + sinh t₁ sinh t₂ cos φ`;
- **Addition theorem** (`SU11.hasSum_boostMatrixElement_addition`): for every `τ`, with the
  Euler angles above and `m'`, `m` in `ε + ℤ`,
  `Σ_{k ∈ ε+ℤ} 𝔓^τ_{m'k}(cosh t₁) e^{ikφ} 𝔓^τ_{km}(cosh t₂) = e^{i(m'α + mγ)} 𝔓^τ_{m'm}(cosh t)`,
  with absolute convergence;
- **Legendre addition**: at `m' = m = 0`,
  `P_τ(cosh t₁ cosh t₂ + sinh t₁ sinh t₂ cos φ) = Σ_k e^{ikφ} 𝔓^τ_{0k}(cosh t₁) 𝔓^τ_{k0}(cosh t₂)`;
  at `φ = 0`, `Σ_k 𝔓^τ_{0k}(cosh t₁) 𝔓^τ_{k0}(cosh t₂) = P_τ(cosh(t₁ + t₂))`; through 1.3 this is
  SpecialFunctionsLegendre 10.2's addition theorem for `P^μ_ν`;
- **Inverse**: at `φ = 0`, `t₂ = −t₁`: `Σ_k 𝔓^τ_{m'k}(cosh t) 𝔓^τ_{km}(cosh(−t)) = δ_{m'm}`.

The addition theorem is SpecialFunctionsGroupModels §3.2 for `principalSeries τ e` on
`g = b_{t₁}`, `h = k_φ b_{t₂}`, with 1.1 for all three matrix elements. The first bullet is the
computation `|a|² = cosh²(t/2)` for the product.

**Checks.**
- At `t₁ = 0.8`, `t₂ = 1.1`, `φ = 0.7`: `cosh t = 3.13878 81544`; negative control: the sign `−`
  in front of `sinh t₁ sinh t₂ cos φ` gives `1.32428 18905`.
- At these data and `τ = 0.23 + 0.4i` the addition theorem holds to `10⁻²⁹` for
  `(m', m) = (2, −1), (0, 0), (3/2, −1/2)`, with `α = arg a + arg b`, `γ = arg a − arg b`.
- Negative control: with `e^{−ikφ}` in place of `e^{ikφ}` the sum at `(2, −1)` is
  `−0.03727 27216 − 0.02620 76979 i`, while the right side is `−0.00777 14849 − 0.04489 65837 i`.

*Needs:* 1.1; SpecialFunctionsGroupModels §§0.1, 3.2; SpecialFunctionsLegendre 10.2.

### 3.2 Multiplication formulas

Sources: Vilenkin–Klimyk §6.6.3 (1)–(8), pp. 327–329; Dieudonné §13 (151), p. 44.

Prove:
- **Fourier-coefficient form** (`SU11.boostMatrixElement_mul_boostMatrixElement`): for every
  integer `k`, with `x(φ) = cosh t₁ cosh t₂ + sinh t₁ sinh t₂ cos φ`,
  `𝔓^τ_{0k}(cosh t₁) 𝔓^τ_{k0}(cosh t₂) = (2π)⁻¹ ∫₀^{2π} e^{−ikφ} 𝔓^τ_{00}(x(φ)) dφ`, where
  `𝔓^τ_{00}(x)` means `𝔓^τ_{00}(cosh(arcosh x))`;
- **Mean value on the hyperboloid**: at `k = 0`,
  `P_τ(cosh t₁) P_τ(cosh t₂) = (2π)⁻¹ ∫₀^{2π} P_τ(x(φ)) dφ`, the mean of `P_τ` over the circle of
  radius `t₂` about the point at distance `t₁` from the origin;
- **Product formula with the triangle kernel** (`SU11.boostMatrixElement_product_kernel`): for
  `t₁, t₂ > 0`,
  `P_τ(cosh t₁) P_τ(cosh t₂) = π⁻¹ ∫_{|t₁−t₂|}^{t₁+t₂} P_τ(cosh s) sinh s Δ(s)^{−1/2} ds`, where
  `Δ(s) = (cosh(t₁ + t₂) − cosh s)(cosh s − cosh(t₁ − t₂))`;
- the general multiplication formula: `𝔓^τ_{m'k}(cosh t₁) 𝔓^τ_{km}(cosh t₂)` is the `k`th Fourier
  coefficient in `φ` of the right side of the addition theorem.

The first bullet is the addition theorem of 3.1 at `m' = m = 0`, where the phase is `1`,
integrated against `e^{−ikφ}`. The kernel form is the substitution `cosh s = x(φ)` on `[0, π]`,
with `sinh t₁ sinh t₂ sin φ = ((cosh(t₁ + t₂) − cosh s)(cosh s − cosh(t₁ − t₂)))^{1/2}`.

**Checks.**
- At `τ = 0.23 + 0.4i`, `t₁ = 0.8`, `t₂ = 1.1`: the Fourier form holds to `10⁻³⁰` for
  `k = 0, 1, 2`, and `P_τ(cosh t₁) P_τ(cosh t₂) = 1.03022 70795 + 0.26882 77410 i`.
- The kernel form gives the same value to `10⁻¹⁷` (quadrature with endpoint singularities).
- Negative control: the normalization `(2π)⁻¹` in the kernel form gives half the value,
  `0.51511 35398 + 0.13441 38705 i`.
- At `τ = 0` the kernel form says `π⁻¹ ∫ sinh s Δ(s)^{−1/2} ds = 1`: the kernel is a
  probability density.

*Needs:* 1.3, 3.1; Mathlib `Real.arcosh`.

### 3.3 Generating functions and the degree

Sources: Vilenkin–Klimyk §6.7.1 (6)–(9), (13)–(13′), pp. 332–334, §6.7.3 (2)–(5),
pp. 336–337 (the `SU(2)` analogues of the degree shift); Dieudonné §14 (171)–(172), p. 49 (the
expansion of `T_l(s) e^{−inθ}`).

Prove, for real `n` and `t`:
- **Generating function** (`SU11.hasSum_boostMatrixElement_fourier`): for every `θ`,
  `Σ_{k∈ℤ} 𝔓^τ_{n+k,n}(cosh t) e^{−ikθ} = A(θ)^{τ+n} A(−θ)^{τ−n}`, absolutely, with `A` of
  Conventions;
- **Row sums** (`SU11.hasSum_boostMatrixElement_row`): `Σ_{k∈ℤ} 𝔓^τ_{n+k,n}(cosh t) = e^{τt}` and
  `Σ_{k∈ℤ} (−1)^k 𝔓^τ_{n+k,n}(cosh t) = e^{−τt}`;
- **Convolution in the degree** (`SU11.hasSum_boostMatrixElement_degree`):
  `𝔓^{τ₁+τ₂}_{m, n₁+n₂}(cosh t) = Σ_{k∈ℤ} 𝔓^{τ₁}_{n₁+k, n₁}(cosh t) 𝔓^{τ₂}_{m−n₁−k, n₂}(cosh t)`
  for `m − n₁ − n₂ ∈ ℤ`;
- **Shift of the degree by `1/2`** (`SU11.boostMatrixElement_degree_shift`):
  `𝔓^{τ+1/2}_{m, n+1/2} = cosh(t/2) 𝔓^τ_{m−1/2, n} + sinh(t/2) 𝔓^τ_{m+1/2, n}`;
- at `n = 0`, `θ = π/2`: `Σ_k (−i)^k 𝔓^τ_{k0}(cosh t) = cosh^τ t`, since
  `|cosh(t/2) + i sinh(t/2)|² = cosh t`.

The integrand of 1.1 is smooth and `2π`-periodic in `θ`, so its Fourier series converges
absolutely, and 1.1 says its coefficients are the `𝔓^τ_{n+k,n}`; the row sums are `θ = 0, π`. The
convolution is the product of two such Fourier series, with `cpow_add` for the bases of positive
real part. The shift is the convolution with `τ₂ = 1/2`, `n₂ = 1/2`, where the only nonzero
coefficients are `𝔓^{1/2}_{1/2,1/2} = cosh(t/2)` and `𝔓^{1/2}_{−1/2,1/2} = sinh(t/2)`.

**Checks.**
- At `τ = 0.23 + 0.4i`, `t = 1.3`: `e^{τt} = 1.17026 25152 + 0.67004 76476 i`, and both row sums
  hold to `10⁻¹⁴` for `n = 0, 1/2, 2`.
- The convolution holds to `10⁻²⁸` at `τ₁ = 0.23 + 0.4i`, `τ₂ = −0.6 + 0.1i` for
  `(m, n₁, n₂) = (1, 0, 0), (2, 1/2, −3/2), (0, 1, 2)`.
- The shift holds to `10⁻³⁰` for `(m, n) = (1, 0), (1/2, 1/2), (−2, 1)`.
- At `θ = π/2`, `n = 0`: both sides are `1.12610 47073 + 0.31335 53931 i`.
- Negative control: the sum over the second index, `Σ_k 𝔓^τ_{0,k}(cosh 1.3)`, is
  `4.29404 03470 + 2.45860 36000 i`, not `e^{τt}`: the row sums run over the first index.

*Needs:* 1.1; Mathlib Fourier series on `AddCircle`.

## Layer 4: recurrences

### 4.1 Derivatives and ladder relations

Sources: Vilenkin–Klimyk §6.7.2 (8)–(13), p. 336, and its `SU(2)` analogues (3)–(7),
pp. 335–336; Dieudonné §14 (173), p. 49 (the generator of the boost on `e^{−inθ}`).

Prove, for `m − n ∈ ℤ`:
- **Derivatives** (`SU11.hasDerivAt_boostMatrixElement`): `d/dt 𝔓^τ_{mn}(cosh t)` equals
  `½(τ − m + 1) 𝔓^τ_{m−1,n} + ½(τ + m + 1) 𝔓^τ_{m+1,n}` and
  `½(τ + n) 𝔓^τ_{m,n−1} + ½(τ − n) 𝔓^τ_{m,n+1}`;
- **Ladder relations** (`SU11.boostMatrixElement_ladder`): for `t ≠ 0`,
  `d/dt 𝔓^τ_{mn} + (n cosh t − m)/sinh t · 𝔓^τ_{mn} = (τ + n) 𝔓^τ_{m,n−1}` and
  `d/dt 𝔓^τ_{mn} − (n cosh t − m)/sinh t · 𝔓^τ_{mn} = (τ − n) 𝔓^τ_{m,n+1}`;
- at `n = 0` and through 1.3 these are the ladder relations of `P^{−m}_τ` in `z = cosh t`
  (Vilenkin–Klimyk §6.7.2 (12)–(13)), the relations SpecialFunctionsLegendre 1.4 proves for
  `P^μ_ν`.

The derivatives are the addition theorem of SpecialFunctionsGroupModels §3.2 for `b_{t+s} = b_s b_t`
and `b_t b_s`, differentiated at `s = 0`, with the generator of `s ↦ b_s` on the weight basis read
off from 1.2 at `t = 0`: `A e_n = ½(τ − n) e_{n+1} + ½(τ + n) e_{n−1}`. The ladder relations combine
the second derivative formula with the generator of the rotations (SpecialFunctionsGroupModels
§4.1).

**Checks.**
- Both derivative formulas hold to `10⁻³⁰` at `τ = 0.23 + 0.4i`, `t = 1.3` for
  `(m, n) = (2, −1), (0, 0), (3/2, 1/2)`.
- At `(m, n) = (2, −1)` the ladder quotients `(d/dt 𝔓 ± (n cosh t − m)/sinh t · 𝔓)/𝔓^τ_{m,n∓1}`
  are `−0.77 + 0.4i = τ + n` and `1.23 + 0.4i = τ − n`.
- Negative control: the quotient of the `+` combination by `𝔓^τ_{m,n+1}` instead is
  `−0.09251 + 0.00201 i`, not a polynomial in `τ`.
- At `τ = 0`, `m = n = 0`: `d/dt 𝔓^0_{00} = 0 = ½ 𝔓^0_{−1,0} + ½ 𝔓^0_{1,0}` by 1.5.

*Needs:* 1.1–1.2, 1.5; SpecialFunctionsGroupModels §§3.2, 4.1; SpecialFunctionsLegendre 1.4.

### 4.2 Three-term recurrences and the equation in `z = cosh t`

Sources: Vilenkin–Klimyk §6.7.2 (5), (9), pp. 335–336; Miller §5-18, pp. 227–228 (the
hypergeometric form from which the recurrences also follow).

Prove, for `t ≠ 0` and `m − n ∈ ℤ`:
- **Recurrences** (`SU11.boostMatrixElement_recurrence`):
  `2(n cosh t − m)/sinh t · 𝔓^τ_{mn} = (τ + n) 𝔓^τ_{m,n−1} − (τ − n) 𝔓^τ_{m,n+1}` and
  `2(m cosh t − n)/sinh t · 𝔓^τ_{mn} = (τ − m + 1) 𝔓^τ_{m−1,n} − (τ + m + 1) 𝔓^τ_{m+1,n}`;
- **The equation in `z`**: `w(z) = 𝔓^τ_{mn}(z)` for `z = cosh t > 1` satisfies
  `(z² − 1) w″ + 2z w′ − (m² + n² − 2mnz)/(z² − 1) · w = τ(τ + 1) w`, SpecialFunctionsGroupModels
  §4.3's equation after the change of variable.

The first recurrence is the difference of the two ladder relations of 4.1; the second is the
first applied to the transposition of 1.4. The equation is §4.3 of SpecialFunctionsGroupModels
with `d/dt = sinh t d/dz`.

**Checks.**
- Both recurrences hold to `10⁻²⁹` at `τ = 0.23 + 0.4i`, `t = 1.3` for
  `(m, n) = (2, −1), (3/2, 1/2), (0, 2)`.
- Negative control: the second recurrence with the right side negated misses by `0.229` at
  `(2, −1)`.
- At `m = n = 0` the equation is Legendre's, `(z² − 1) w″ + 2z w′ = τ(τ + 1) w`, solved by
  `P_τ(z)` (1.3).

*Needs:* 1.4, 4.1; SpecialFunctionsGroupModels §4.3.

## Layer 5: other subgroups and transforms

### 5.1 The other one-parameter subgroups

Sources: Vilenkin–Klimyk §7.7.1, p. 435; Miller §5-18 (5.156)–(5.158), pp. 226–227 (the Euler
coordinates of an element of `SU(1,1)` read from `a`, `b`).

`SU11.parabolic s = [[1 + is/2, s/2], [s/2, 1 − is/2]]`, the image of the unipotent subgroup
`[[1, s], [0, 1]]` of `SL(2, ℝ)` up to conjugation. Prove:
- **The second hyperbolic subgroup** (`SU11.principalSeries_matrixElement_boostY`):
  `D_{m'm}(boostY t) = i^{m'−m} 𝔓^τ_{m'm}(cosh t)`;
- **The parabolic subgroup** (`SU11.principalSeries_matrixElement_parabolic`): for real `s`,
  `D_{m'm}(parabolic s) = e^{i(m'+m) arctan(s/2)} 𝔓^τ_{m'm}(cosh(2 arsinh(s/2)))`, where
  `cosh(2 arsinh(s/2)) = 1 + s²/2`;
- **The parabolic subgroup in Euler angles** (`SU11.parabolic_add_and_eq_euler`): `parabolic` is a
  homomorphism from `ℝ`, and `parabolic s = euler β (2 arsinh(s/2)) β` with `β = arctan(s/2)`.

`boostY t = k_{π/2} b_t k_{−π/2}` (SpecialFunctionsGroupModels Conventions); the parabolic element
has `a = 1 + is/2 = e^{iβ} cosh(t/2)` and `b = s/2 = sinh(t/2)` with `t = 2 arsinh(s/2)`, so it is
`euler β t β`; then 1.1.

**Checks.**
- At `τ = 0.23 + 0.4i`, `t = 1.3`: both identities hold to `10⁻³⁰` in the circle model for
  `(n', n) = (2, −1)` (`e = 0`) and `(1, 0)` (`e = 1`), the parabolic one at `s = 0.8` and
  `s = −1.7`.
- At `s = 0.8`, `(n', n) = (2, −1)`, `e = 0`: `D = −0.00133 70826 − 0.00458 54908 i`.
- Negative control: Vilenkin–Klimyk's phase `[(1 + is/2)/(1 − is/2)]^{−(m+n)/2}` belongs to the
  labels `e^{−ikθ}`; read in the labels here it gives the conjugate phase.

*Needs:* 1.1; SpecialFunctionsGroupModels §§0.1, 3.3, Conventions.

### 5.2 The Mehler–Fock transform

Sources: Vilenkin–Klimyk §7.8.4 (15)–(17), pp. 485–486; Wawrzyńczyk (10.5.11)–(10.5.12),
p. 373, whose inversion constant `1/(2π²)` differs from the constant `1` fixed here by the
Parseval check.

With `μ = sinh t dt` on `(0, ∞)` and `ν = ρ tanh(πρ) dρ` on `(0, ∞)`,
`SU11.mehlerFock f ρ = ∫₀^∞ f(t) 𝔓^{−1/2+iρ}_{00}(cosh t) sinh t dt`. Prove:
- **Parseval** (`SU11.lintegral_mehlerFock`): for continuous `f` with compact support in
  `(0, ∞)`, `∫ |f|² dμ = ∫ |mehlerFock f|² dν` (as `ℝ≥0∞`-valued integrals);
- **Inversion** (`SU11.mehlerFock_inversion`): for smooth `f` with compact support in `(0, ∞)`
  and `t > 0`, `f(t) = ∫₀^∞ mehlerFock f ρ · 𝔓^{−1/2+iρ}_{00}(cosh t) ρ tanh(πρ) dρ`;
- **Unitarity** (`SU11.exists_mehlerFock_unitary`): there is a unitary
  `L²(μ) ≃ L²(ν)` that agrees with `mehlerFock` on the functions of the first bullet;
- through `x = cosh t` this is the Mehler–Fock transform `c(ρ) = ∫₁^∞ F(x) P_{−1/2+iρ}(x) dx` on
  `L²((1, ∞), dx)`, and up to the constant factor between `sinh t dt` and the image of the Haar
  measure it is SpecialFunctionsGroupModels §5.2's spherical transform of `(SU(1,1), K)` at the
  spherical functions `𝔓^{−1/2+iρ}_{00}`.

The proof restricts NoncompactQuantumSymmetry M4.P's Plancherel theorem for `SL(2, ℝ)` to the
bi-`K`-invariant functions, where only the spherical principal series contributes, and identifies
the spherical functions with `𝔓^{−1/2+iρ}_{00}` (1.3) and the Plancherel density with
`ρ tanh(πρ)` through the dictionary `ν = −(2τ + 1) = −2iρ` of SpecialFunctionsGroupModels §2.1.
Inversion on smooth compactly supported functions follows from Parseval by polarization and the
continuity of `ρ ↦ 𝔓^{−1/2+iρ}_{00}(cosh t)`.

**Checks.**
- For `f(t) = e^{−cosh t}`: `mehlerFock f ρ = (2/π)^{1/2} K_{iρ}(1)`, `0.30642 19939` at
  `ρ = 0.5` and `0.10680 53193` at `ρ = 1.7` (`K` the Macdonald function).
- Negative control: `(2/π)^{1/2} K_{1/2+iρ}(1)` (the Laplace transform of `P_ν` read with
  `ν + 1/2 = 1/2 + iρ` instead of `iρ`) is complex at these `ρ`, while `mehlerFock f ρ` is real.
- Parseval for `F(x) = (x − 1) e^{−x}`: `∫₁^∞ |F|² dx = 0.03383 38208` and
  `∫₀^∞ |c(ρ)|² ρ tanh(πρ) dρ = 0.03383 38208`; negative control: the density `ρ dρ` without
  `tanh(πρ)` gives `0.03715 31`.

*Needs:* 1.1, 1.3, 1.4, 2.1; NoncompactQuantumSymmetry M4.P; SpecialFunctionsGroupModels §§2.1,
5.2.

### 5.3 The Mehler–Fock transform of order `m`

Sources: Vilenkin–Klimyk §7.8.4 (3)–(11), pp. 483–485; Miller §5-18 (5.159), pp. 227–228 (the
matrix elements `A_{l0}` that are the kernels).

For an integer `m`,
`SU11.mehlerFockOrder m f ρ = ∫₀^∞ f(t) conj 𝔓^{−1/2+iρ}_{m0}(cosh t) sinh t dt`. Prove:
- **Parseval** (`SU11.lintegral_mehlerFockOrder`): for continuous `f` with compact support in
  `(0, ∞)`, `∫ |f|² dμ = ∫ |mehlerFockOrder m f|² dν`;
- **Inversion** (`SU11.mehlerFockOrder_inversion`): for smooth `f` with compact support in `(0, ∞)`
  and `t > 0`, `f(t) = ∫₀^∞ mehlerFockOrder m f ρ · 𝔓^{−1/2+iρ}_{m0}(cosh t) ρ tanh(πρ) dρ`;
- through 1.3 the kernel is `Γ(1/2 + iρ)/Γ(1/2 + iρ − m) · P^{−m}_{−1/2+iρ}(cosh t)`, so this is
  the generalized Mehler–Fock transform of order `−m` with the density
  `|Γ(1/2 + iρ)/Γ(1/2 + iρ − m)|² ρ tanh(πρ)`.

The functions `e^{imα} f(t)` on `SU(1,1)/K` are the `K`-type `m` of `L²(SU(1,1)/K)`; the
Plancherel theorem of NoncompactQuantumSymmetry M4.P on that `K`-type has only the spherical
principal series, whose matrix elements on the `K`-type are `e^{imα} 𝔓^{−1/2+iρ}_{m0}(cosh t)` by
1.1, so the transform is unitary with the same density as for `m = 0`; no discrete series occurs
because `L²(SU(1,1)/K)` has none.

**Checks.**
- At `m = 0` the transform is `mehlerFock` (the kernel is real by 1.4).
- `|𝔓^{−1/2+iρ}_{10}|² = (1/4 + ρ²) |P^{−1}_{−1/2+iρ}|²`.
- Parseval for `F(x) = (x − 1) e^{−x}` at `m = 1, 2`: both sides are `0.03383 382`, the value of
  `∫₁^∞ |F|² dx` for every `m`.
- Negative control: for the `K`-types `(m, n)` with `mn > 0` of `L²(SU(1,1))` the same formula
  misses the discrete-series terms of Vilenkin–Klimyk §7.8.4 (8) (Beyond).

*Needs:* 1.1, 1.3, 5.2; NoncompactQuantumSymmetry M4.P.

## Examples

- `𝔓^{−1/2+0.8i}_{00}(cosh 0.9) = 0.83316 90033 = P_{−1/2+0.8i}(cosh 0.9)`.
- `𝔓^{0.23+0.4i}_{2,−1}(cosh 1.3) = −0.01150 64149 − 0.01597 50333 i`.
- `Σ_k 𝔓^τ_{k0}(cosh t) = e^{τt}`.

## Beyond this roadmap (a roadmap for a roadmap; do not implement)

The following material lies outside this roadmap. It is recorded only to fix the boundary.
Contributors should not attempt it under this roadmap.

- **The kernels in mixed and continuous bases** (Vilenkin–Klimyk §§7.1–7.7): the Mellin and
  Fourier realizations on the line, the kernels `K^{ij}` and the Whittaker, Bessel and
  hypergeometric functions they produce, and the Kontorovich–Lebedev transform (§7.8.4 (18)–(20)).
- **The transforms on `L²(SU(1,1))` of `K`-types `(k, m)` with `km > 0`** and of half-integral
  type, with their discrete-series terms (Vilenkin–Klimyk §7.8.4 (3)–(14)), and the orthogonality
  of the Jacobi polynomials with integer parameters of §7.8.4 (14).
- **The Jacobi transform** for general `(α, β)`, the `c`-function, the Abel transform and the
  Fourier transform on hyperbolic spaces: RankOneSymmetricSpaces.
- **The universal covering group** of `SU(1,1)` and its matrix elements (Vilenkin–Klimyk §6.4.7).
- **Asymptotics** of `𝔓^τ_{mn}(cosh t)` for large `t` or large indices beyond the boundedness
  range of 2.1.

## Prior formalization

[lean-SFVK](https://github.com/bjbraams/lean-SFVK) (Apache-2.0) is the same author's project on
special functions and group representations. Its `SFVK/SU11/` modules prove the `SU(1,1)`
coordinates, the circle model and the matrix elements of SpecialFunctionsGroupModels with the
names used here. Its modules `SFVK/SU11/Basic/BoostMatrixElements.lean` (the definitions of this
roadmap) and `SFVK/SU11/MatrixElements.lean`, `SFVK/SU11/Transforms.lean` (statements of the
targets) are the same author's prior work on this roadmap; they are references, not
specifications.

## References

- J. Dieudonné, *Special Functions and Linear Representations of Lie Groups*, CBMS Regional
  Conference Series in Mathematics 42, AMS, 1980, §§13–14.
- W. Miller, Jr., *Lie Theory and Special Functions*, Mathematics in Science and Engineering 43,
  Academic Press, 1968, §5-18.
- N. Ja. Vilenkin and A. U. Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 1,
  Mathematics and Its Applications (Soviet Series) 72, Kluwer, 1991, Chs. 6–7.
- A. Wawrzyńczyk, *Group Representations and Special Functions*, Mathematics and Its Applications
  (East European Series), Reidel / PWN, 1984, Ch. 10.
