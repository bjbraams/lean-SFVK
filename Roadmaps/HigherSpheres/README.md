# Special functions on spheres: `SO(n)`, `U(n)`, Gegenbauer and disk polynomials

**Summary.** This roadmap develops the harmonic analysis of the real sphere `S^{n-1} ⊂ ℝⁿ` under
`SO(n)` and of the complex sphere `S^{2n-1} ⊂ ℂⁿ` under `U(n)`, and the special functions that it
produces: Gegenbauer polynomials as the zonal spherical functions of `(SO(n), SO(n - 1))` and
disk polynomials as those of `(U(n), U(n - 1))`. It proves the closed dimension of the spaces of
spherical harmonics, the uniqueness of the zonal harmonic, the addition theorem and reproducing
kernel, the Funk–Hecke formula, the Laplace integral, the product formula and the Gegenbauer
addition theorem, the classification of the spherical functions of both pairs, the branching of
harmonics from `ℝ^{m+1}` to `ℝᵐ` with explicit Gegenbauer factors, the harmonics of bidegree
`(p, q)` on `ℂⁿ` with their dimension and branching, the orthogonality of disk polynomials, and the
expansion of the zonal polynomials of `SO(2n)` in disk polynomials. The roadmap is a synthesis of
several sources and follows none of them in its organization: it is ordered by proof dependency,
from the sphere and its measure, through harmonic polynomials and zonal polynomials, to the
integral identities and spherical functions, and then repeats the pattern for the complex sphere.
Its sources are Vilenkin–Klimyk (*Representation of Lie Groups and Special Functions*, Vol. 2,
Chapters 9–11), Klimyk–Vilenkin (*Representations of Lie Groups and Special Functions*, in
Encyclopaedia of Mathematical Sciences 59), Wawrzyńczyk (*Group Representations and Special
Functions*, Chapter 9) and Dieudonné (*Special Functions and Linear Representations of Lie
Groups*, §7); each subsection cites several of them by locator; see [References](#references).

Mathlib has the surface measure on the unit sphere (`toSphere`), the orthogonal and unitary
matrix groups (`Matrix.specialOrthogonalGroup`, `Matrix.unitaryGroup`), multivariate polynomials
with partial derivatives and weighted homogeneous components, the Chebyshev polynomials
(`Chebyshev.T`) and the Gamma function. Tau Ceti has the Laplacian on polynomials, the harmonic
homogeneous polynomials `MvPolynomial.harmonicSubmodule` with the Fischer decomposition and their
dimension, the restriction to the sphere `MvPolynomial.sphereEval` with its injectivity on
harmonic polynomials, compactness and the topological-group structure of the unitary groups, and
the Haar probability measure `TauCeti.haarProb` of a compact group. Neither has zonal polynomials,
Gegenbauer polynomials as functions on a sphere, the addition theorem, the Funk–Hecke formula,
harmonics of bidegree `(p, q)`, disk polynomials or the Gel'fand pairs of this roadmap.

The roadmap covers:
- the sphere, the stabilizer `K_η` of a unit vector, transitivity and the double cosets, the
  normalized sphere measure with its invariance, its image of the Haar measure and its polar-angle
  density, and the Gel'fand pair `(SO(n), K_η)` (Layer 1);
- the closed dimension of the spherical harmonics, their inequivalence for distinct degrees and
  the uniqueness of the `K_η`-invariant harmonic (Layer 2);
- the normalized zonal polynomial `ω_{n,l}` with its Gegenbauer, Chebyshev and Legendre forms, the
  value at one, generating function and derivative of the Gegenbauer polynomial, the differential
  equation, the zonal harmonic and the Laplace integral (Layer 3);
- the addition theorem and reproducing property, the bound `|ω| ≤ 1`, orthogonality, the
  Funk–Hecke formula, the zonal spherical functions with their classification and product
  formula, and the Gegenbauer addition theorem (Layer 4);
- the branching of harmonics from `ℝ^{m+1}` to `ℝᵐ`, with its dimension count, its norm constant
  and the Gel'fand–Tsetlin basis it generates (Layer 5);
- `U(n)` and the complex sphere: the disc density, the Gel'fand pair `(U(n), K_η)`, harmonics of
  bidegree `(p, q)` with their dimension, decomposition and branching, disk polynomials with their
  Jacobi form, orthogonality and bound, the `U(n)`-zonal harmonic, the spherical functions with
  their classification, the addition theorem, and the expansion of the `SO(2n)` zonal polynomials
  in disk polynomials (Layer 6).

## Scope and ownership

The roadmap is complete when Tau Ceti proves all of the following.

1. **The sphere and the rotation group** (1.1–1.3).
2. **Spherical harmonics** (2.1–2.3).
3. **Zonal polynomials and Gegenbauer polynomials** (3.1–3.4).
4. **Addition theorem, Funk–Hecke, spherical functions** (4.1–4.5).
5. **Branching** (5.1–5.2).
6. **The complex sphere and `U(n)`** (6.1–6.6).

The numbers are those of the layers below, and `k.n` names subsection `n` of Layer `k`.
`Suggested.lean` states the headlines that carry a Lean name, each with every conclusion the
README attaches to it; it is not an exhaustive acceptance test, and the other headlines and the
plain bullets of each subsection are targets of the same standing, stated in prose. The
`**Checks.**` of each subsection are statements to prove; they test the conventions on explicit
values.

**Boundary with Tau Ceti and RiemannianGeometry R8.** Tau Ceti owns the harmonic polynomials:
the Laplacian, the Fischer decomposition, the dimension of `H_l` as a difference of binomial
coefficients, the restriction to the sphere and its injectivity, and the action of the orthogonal
group by `(g · p)(x) = p(g⁻¹ x)` (in `TauCeti/RingTheory/MvPolynomial/Harmonic/Orthogonal.lean`).
[RiemannianGeometry R8](../RiemannianGeometry/README.md) owns the uniqueness of the iterated
Fischer decomposition and the eigenvalue `l(l + n - 2)` of the restricted harmonics (R8.1), the
identification of the eigenspaces of the Laplace–Beltrami operator with the restricted harmonics,
their orthogonality and the completeness of their sum in `L²(S^{n-1})` (R8.2), and the
irreducibility of `H_l` under `SO(n)` for `n ≥ 3` with highest weight `l ε₁` (R8.3). This roadmap
consumes them and owns the special functions: the closed dimension formula, the zonal harmonic and
its uniqueness, the zonal polynomials, and every integral identity in which they occur.

**Boundary with LaguerreJacobi.** [LaguerreJacobi §6.2](../LaguerreJacobi/README.md) owns the
Gegenbauer polynomial `C_l^{(λ)}` by the explicit sum of DLMF 18.5.10, its leading coefficient,
its relation to Jacobi polynomials, its orthogonality for `-1/2 < λ`, `λ ≠ 0`, and its Hilbert
basis; its §3.2 owns the Jacobi polynomials. It excludes the family at `λ = 0` (where its
`C_l^{(0)}` vanishes for `l ≥ 1`), and it does not state the value at one, the generating
function, the derivative or the differential equation. This roadmap owns those four facts (3.2)
and works with the normalized zonal polynomial `ω_{n,l}`, which has no degeneracy at `n = 2`. The
orthogonality of 4.2 is stated for `ω_{n,l}`, with its constant in terms of `dim H_l`, and
agrees with that of LaguerreJacobi on their common range (4.2 Checks).

**Boundary with RepresentationTheory.**
[ClassicalGroups](../RepresentationTheory/ClassicalGroups/README.md)
owns the abstract branching rule `SO(n) ↓ SO(n - 1)` (its Layer 6.2) and the Gel'fand–Tsetlin
patterns of GLₙ (its Layer 6); this roadmap owns the explicit harmonic polynomials that realize
the branching (5.1) and the basis they generate (5.2).
[CompactGroups](../RepresentationTheory/CompactGroups/README.md) owns Peter–Weyl and Schur
orthogonality for compact groups, consumed in 4.4 and 6.5.

**Boundary with the roadmaps of the same project.** SpecialFunctionsGroupModels owns Gel'fand
pairs, spherical functions and the spherical transform for a general locally compact group (its
§§5.1–5.3) and the sphere models of the motion groups (its §2.6); this roadmap instantiates the
first for `(SO(n), K_η)` and `(U(n), K_η)` and copies its definitions verbatim. The roadmap
SpecialFunctionsSU2MatrixElements owns the sphere `S²` with the spherical harmonics `Y_l^m`, their
addition theorem (its §6.3) and the Gel'fand pair `(SU(2), T)` (its §6.4); the case `n = 3` here
agrees with it (4.1 Checks). The roadmap on Euclidean motion groups and Bessel functions of the
same project owns the plane-wave expansion, the Bochner (Hankel-transform) theorem for
`f(r) Y(ξ)`, and the spherical functions of `(M(n), SO(n))`, which apply the Funk–Hecke formula of
4.3 to `t ↦ e^{irt}`.

**Not owned here.** Spherical harmonics on hyperboloids and the groups `SO₀(n - 1, 1)` and
`U(n - 1, 1)`, Gegenbauer functions of noncomplex or nonintegral degree, and harmonic analysis on
Stiefel and Grassmann manifolds (see Beyond).

## Conventions

- **Dimensions.** `n` is the dimension of the ambient space: `S^{n-1} ⊂ ℝⁿ` with `SO(n)`, and
  `S^{2n-1} ⊂ ℂⁿ` with `U(n)`. This is the convention of Vilenkin–Klimyk Chapters 9–11 and of
  Wawrzyńczyk Chapter 9. Dieudonné (§7) and Klimyk–Vilenkin (Part II, Chapter 2, §2.4) write
  `Sⁿ ⊂ ℝ^{n+1}` with `SO(n + 1)`, so their `n` is `n - 1` here.
- **Base point.** A unit vector `η` replaces the sources' north pole `e_n`, and
  `K_η = stab η` is its stabilizer. Every statement holds for every unit `η`.
- **Actions.** Groups act on the left: `g • x = g x` (`Matrix.toEuclideanLin`), and on functions
  by `(g · f)(x) = f(g⁻¹ x)`, as in Tau Ceti.
- **Inner products** are conjugate-linear in the first argument, as in Mathlib:
  `⟪y, x⟫ = ∑ conj(yᵢ) xᵢ`. The complex variable of a disk polynomial is `w = ⟪η, ξ⟫`, which is
  holomorphic in `ξ`.
- **Measures.** `sphereMeasure n` and `complexSphereMeasure n` are probability measures (the
  surface measure divided by its total mass), and the Haar measure of a compact group has mass `1`.
  With these, every reproducing constant is a dimension: `∑ Yᵢ(x) Yᵢ(y) = dim H_l ω_{n,l}(⟪x, y⟫)`.
  Vilenkin–Klimyk §9.1.9 and §10.2.1 use the same normalization; the unnormalized constants carry
  the factor `|S^{n-1}| = 2π^{n/2}/Γ(n/2)`.
- **Zonal polynomials.** `ω_{n,l}(t) = ₂F₁(-l, l + n - 2; (n - 1)/2; (1 - t)/2)`, normalized by
  `ω_{n,l}(1) = 1`. For `n ≥ 3` and `λ = (n - 2)/2` it is `C_l^{(λ)}(t)/C_l^{(λ)}(1)`, the
  normalized Gegenbauer polynomial of Vilenkin–Klimyk §9.3.2 (4) and of Wawrzyńczyk (9.2.11). The
  index `λ` is DLMF's; Vilenkin–Klimyk and Wawrzyńczyk write `p`.
- **Disk polynomials.** `R^α_{p,q}(w) = w^{p-q} ₂F₁(-q, p + α + 1; α + 1; 1 - |w|²)` for `p ≥ q`
  and `R^α_{q,p} = conj R^α_{p,q}`, with `R^α_{p,q}(1) = 1`. The `U(n)` case is `α = n - 2`.
- **Spherical functions** follow SpecialFunctionsGroupModels §5.2: continuous, bi-invariant,
  `φ(1) = 1` and `∫_K φ(x k y) dk = φ(x) φ(y)`, without a boundedness requirement. The spherical
  function of a class-one representation with fixed unit vector `v` is `g ↦ ⟪v, T(g) v⟫`; on
  `(U(n), K_η)` this is `R^{n-2}_{p,q}(⟪g η, η⟫)`, which is the conjugate argument of
  `⟪η, g η⟫` (6.5 Checks).

## Exact supplier contracts

### From Tau Ceti

- `MvPolynomial.normSq`, `MvPolynomial.harmonicSubmodule`
  (`TauCeti/RingTheory/MvPolynomial/Harmonic.lean`): `|x|²` and the harmonic homogeneous
  polynomials of degree `l`, with the Fischer decomposition and the dimension theorem.
- `MvPolynomial.sphereEval` (`TauCeti/Analysis/MvPolynomial/Sphere.lean`): restriction of a real
  polynomial to the unit sphere, injective on harmonic homogeneous polynomials.
- The topological-group instances and compactness of `Matrix.specialOrthogonalGroup` and
  `Matrix.unitaryGroup` (`TauCeti/Topology/Algebra/UnitaryGroup.lean`).
- `TauCeti.haarProb` (`TauCeti/RepresentationTheory/Compact/Haar.lean`): the Haar probability
  measure of a compact group, left and right invariant.

### From Mathlib

- `toSphere`, the surface measure on the unit sphere of a finite-dimensional inner product space.
  Used in 1.2 and 6.1.
- `Matrix.specialOrthogonalGroup`, `Matrix.unitaryGroup`, `Matrix.toEuclideanLin`,
  `MulAction.stabilizer`. Used in 1.1 and 6.1.
- `MvPolynomial.pderiv`, `MvPolynomial.weightedHomogeneousSubmodule`, `ascPochhammer`. Used in
  Layers 3 and 6.
- `Chebyshev.T` and the Gamma function. Used in 3.1, 3.4 and 4.4.

### From other roadmaps

- [RiemannianGeometry](../RiemannianGeometry/README.md) R8.1–R8.3, as described under Scope and
  ownership. Consumed in 2.2, 4.1 and 4.4.
- [LaguerreJacobi](../LaguerreJacobi/README.md) §3.2 (Jacobi polynomials) and §6.2 (Gegenbauer
  polynomials and their orthogonality), with its hypotheses. Consumed in 3.1, 4.2 and 6.3.
- [ClassicalGroups](../RepresentationTheory/ClassicalGroups/README.md) Layer 6.2 (the branching
  `SO(n) ↓ SO(n - 1)`), and its highest-weight classification of the representations of `U(n)`.
  Consumed in 5.1 and 6.2.
- [CompactGroups](../RepresentationTheory/CompactGroups/README.md): Peter–Weyl and Schur
  orthogonality. Consumed in 4.4 and 6.5.
- SpecialFunctionsGroupModels, a roadmap of the same project: §§5.1–5.3 (Gel'fand pairs,
  spherical functions of representations, multiplicity one) and §0.3 (`SO(n)` and its action).
  The roadmap SpecialFunctionsSU2MatrixElements of the same project: §§6.3–6.4, for the Checks of
  the case `n = 3`.

`Suggested.lean` imports no other roadmap; it carries local verbatim copies of the Gegenbauer and
Jacobi polynomials of LaguerreJacobi (`gegenbauer`, `jacobi`) and of the Gel'fand-pair
definitions of SpecialFunctionsGroupModels (`IsBiInvariant`, `conv`, `IsGelfandPair`,
`IsSphericalFunction`, `SOn`).

## How to read the build

Layer 1 fixes the sphere, its measure and the base point; its polar-angle density turns every
integral of a function of `⟪η, x⟫` into an integral over `[-1, 1]`, which is how the orthogonality
and Funk–Hecke statements become one-variable identities. Layer 2 is the bridge to Tau Ceti and R8:
the harmonic spaces, their dimension, and the uniqueness of the `K_η`-invariant harmonic, which is
the heart of every later identification. Layer 3 builds the zonal polynomial as an explicit
terminating sum and the zonal harmonic as its homogenization, and proves the one-variable facts.
Layer 4 combines them: the addition theorem follows from uniqueness (Layer 2) and invariance of the
measure (Layer 1), and Funk–Hecke, orthogonality, the bound, the spherical functions and the
product formula follow from the addition theorem. The Gegenbauer addition theorem of 4.5 needs the
branching of Layer 5 for its proof. Layer 6 repeats the pattern for `U(n)`, with harmonics of
bidegree `(p, q)` in place of degree `l`; its last subsection connects the two halves.

The harder material is the uniqueness of the invariant harmonic (2.3 and 6.4), the
classifications (4.4 and 6.5), which need Peter–Weyl, and the branching decomposition with its
norm constant (5.1).

## Layer 1: the sphere and the rotation group

### 1.1 The sphere, the stabilizer and the double cosets

Sources: Vilenkin–Klimyk §9.1.9 (1)–(6), p. 22 (the sphere as `SO(n)/SO(n - 1)`, spherical
coordinates); Wawrzyńczyk §9.5, p. 337 (the `K`-orbits on the sphere); Dieudonné §7, p. 22.

`SO(n)` acts on `ℝⁿ` (`smul_def`), `Sphere n` is the unit sphere, and `stab η` is the stabilizer
`K_η` of `η`. Prove:
- **Transitivity** (`exists_smul_eq`): for `n ≥ 2`, every unit vector is `g η` for some
  `g ∈ SO(n)`;
- `K_η` is closed, hence compact, and for a unit vector `η` it is conjugate to the copy of
  `SO(n - 1)` fixing the last coordinate;
- **Double cosets** (`mem_doubleCoset_iff`): for `n ≥ 3` and unit `η`, `h ∈ K_η g K_η` exactly when
  `⟪η, g η⟫ = ⟪η, h η⟫`.

Route: Gram–Schmidt completes `η` and `ξ` to positively oriented orthonormal bases. For the double
cosets, `K_η` acts transitively on each sphere `{x : ⟪η, x⟫ = t, |x| = 1}` when `n ≥ 3`, so
`g η` and `h η` are related by some `k₁ ∈ K_η`, and `(k₁ g)⁻¹ h ∈ K_η`.

**Checks.**
- For `n = 3`, `η = e₃` and `g` the rotation by `θ` about `e₁`, `⟪η, g η⟫ = cos θ`.
- Negative control: for `n = 2`, `K_η` is trivial, the rotations by `0.5` and `-0.5` have the same
  `⟪η, g η⟫ = cos 0.5` and lie in different double cosets; the hypothesis `n ≥ 3` is needed.
- Negative control: for `n = 1`, `SO(1)` is trivial and does not map `1` to `-1`; transitivity
  needs `n ≥ 2`.
- `stab η` contains `1` and every `g` with `g η = η` (`MulAction.stabilizer`); for `η = 0` it is
  all of `SO(n)`.

### 1.2 The normalized sphere measure

Sources: Vilenkin–Klimyk §9.1.9 (1)–(6), p. 22 (invariant measure and its expression
`dξ = Γ(n/2)/(√π Γ((n - 1)/2)) sin^{n-2} θ dη dθ`); Wawrzyńczyk §9.5, (9.5.1), p. 337;
Klimyk–Vilenkin Part II, Chapter 2, §2.4, (24), p. 179.

`sphereMeasure n` is Mathlib's surface measure `toSphere` divided by its total mass, and
`polarConstant n` is `c_n = Γ(n/2)/(√π Γ((n - 1)/2))`. Prove:
- **Invariance** (`integral_smul_sphereMeasure`): `∫ f(g x) dσ(x) = ∫ f dσ` for `g ∈ SO(n)`;
- **Haar to sphere** (`integral_haarProb_smul`): for `n ≥ 2` and unit `η`, the image of
  `TauCeti.haarProb (SOn n)` under `g ↦ g η` is `sphereMeasure n`;
- **Polar-angle density** (`integral_inner_sphereMeasure`): for `n ≥ 2`, unit `η` and continuous
  `f`, `∫ f(⟪η, x⟫) dσ(x) = c_n ∫_{-1}^{1} f(t) (1 - t²)^{(n-3)/2} dt`;
- the normalized measure is the unique `SO(n)`-invariant Borel probability measure on the sphere
  for `n ≥ 2`.

Route: invariance from `toSphere` of the rotation-invariant Lebesgue measure; Haar to sphere from
uniqueness of invariant measures on the homogeneous space, or from Tau Ceti's column map of the
orthogonal group; the density by integrating out the `K_η`-orbits in the spherical coordinates of
Vilenkin–Klimyk §9.1.9 (6).

**Checks.**
- `c_2 = 1/π`, `c_3 = 1/2`, `c_4 = 2/π`, `c_5 = 3/4`.
- The density has total mass one: `c_n ∫_{-1}^{1} (1 - t²)^{(n-3)/2} dt = 1` for `n = 2, …, 6`.
- `∫ ⟪η, x⟫⁴ dσ = 3/(n(n + 2))`: `1/5` for `n = 3`, `3/35` for `n = 5`.
- For `n = 3` the density is the constant `1/2` on `[-1, 1]` (Archimedes).
- Negative control: for `n = 1`, `SO(1)` is trivial, the image of its Haar measure is the point
  mass at `η` and not the uniform measure on `{±1}`; the hypothesis `n ≥ 2` is needed.

### 1.3 The Gel'fand pair `(SO(n), K_η)`

Sources: Wawrzyńczyk §9.5, p. 337; Dieudonné §7, pp. 22–23; Vilenkin–Klimyk §9.2.6, pp. 35–36.

Prove:
- **Gel'fand pair** (`isGelfandPair_SOn`): convolution of continuous bi-`K_η`-invariant functions
  on `SO(n)` commutes, for every `n` and every `η`.

Route: for `n ≥ 3` and unit `η`, `g⁻¹ ∈ K_η g K_η` by 1.1, since `⟪η, g⁻¹ η⟫ = ⟪g η, η⟫`, and
Gel'fand's criterion of SpecialFunctionsGroupModels §5.1 applies with `σ(g) = g⁻¹`. For `n ≤ 2`
the group `SO(n)` is abelian. For `η` not a unit vector, `K_η` is `K_{η/|η|}` or `SO(n)`.

**Checks.**
- For `n = 2`, `K_η` is trivial and the pair is Gel'fand because `SO(2)` is abelian, although
  `g⁻¹ ∉ K_η g K_η` for the rotation by `0.5`.
- For `n = 3`, `(SO(3), SO(2))` is the image of SpecialFunctionsSU2MatrixElements §6.4.
- Negative control: `(SO(3), {1})` is not a Gel'fand pair: `SO(3)` is not abelian.

## Layer 2: spherical harmonics

### 2.1 Dimension

Sources: Vilenkin–Klimyk §9.2.3 (4)–(5), p. 30 (with erratum E09.2.01 of the project's errata
file for the printed dimension of the homogeneous polynomials); Wawrzyńczyk §9.4, p. 335 (the
dimension of `H^l_n`); Dieudonné §7, (99), p. 23.

Prove:
- **Closed dimension formula** (`finrank_harmonicSubmodule_mul`): for `n ≥ 3`,
  `dim H_l(ℝⁿ) = (2l + n - 2)(l + n - 3)!/((n - 2)! l!)`, stated multiplied out in `ℕ`.

Route: Tau Ceti's dimension theorem `C(n + l - 1, l) - C(n + l - 3, l - 2)` and a factorial
identity.

**Checks.**
- `n = 3`: `dim H_l = 2l + 1`, so `1, 3, 5, 7, 9`.
- `n = 4`: `(l + 1)²`; `n = 5`: `1, 5, 14, 30, 55`; `n = 6`: `1, 6, 20, 50, 105`.
- `n = 2`: `dim H_0 = 1` and `dim H_l = 2` for `l ≥ 1`, which the formula gives for `l ≥ 1`.
- Negative control: at `n = 2`, `l = 0` the multiplied-out formula reads `1 · (0! · 0!) = 0 · 0!`,
  which is false; the hypothesis `n ≥ 3` excludes it.

### 2.2 Spherical harmonics as representations

Sources: Vilenkin–Klimyk §9.2.6 (2′), p. 35 (the decomposition of `L²(S^{n-1})` and the
quasi-regular representation); Wawrzyńczyk Theorem 9.4.1, p. 335; Dieudonné §7, (100)–(102),
pp. 23–24.

The restriction of Tau Ceti's orthogonal-group action to `SO(n)` acts on `H_l`, and by 1.2 its
restriction to the sphere is unitary for the `L²(sphereMeasure n)` inner product. Prove:
- **Inequivalence**: for `n ≥ 3` the representations on `H_l` for distinct `l` are pairwise
  inequivalent;
- `L²(S^{n-1})` is the orthogonal Hilbert sum of the restrictions of the `H_l` (R8.2), and every
  irreducible subrepresentation of the quasi-regular representation is one of them.

Route: `H_l` is irreducible (R8.3); for `l ≠ l'` the `K_η`-invariant vectors (2.3) are the zonal
harmonics, whose spherical functions `ω_{n,l}` and `ω_{n,l'}` differ (3.1), so the
representations differ. Alternatively the eigenvalues `l(l + n - 2)` of R8.1 differ.

**Checks.**
- For `n = 3` the representation on `H_1` is the defining representation of `SO(3)` and that on
  `H_2` is the five-dimensional representation on traceless symmetric matrices.
- Negative control: for `n = 2` and `l ≥ 1`, `H_l` is the sum of the characters `e^{± ilθ}` and
  is not irreducible; the statements are for `n ≥ 3`.
- For `n = 3`, `H_1` and `H_2` are inequivalent although both are irreducible: their dimensions
  `3` and `5` differ, and so do their spherical functions `t` and `(3t² - 1)/2`.

### 2.3 Class one: the invariant harmonic

Sources: Vilenkin–Klimyk §10.2.1, Lemma, p. 173 (with erratum E10.2.01 of the project's errata
file: the denominator is `C_l^{(n-2)/2}(1)`); Vilenkin–Klimyk §9.2.6, pp. 35–36 (the
representations of class one); Dieudonné §7, p. 23 (uniqueness of the zonal function);
Wawrzyńczyk (9.2.9)–(9.2.11), p. 330.

Prove:
- **Uniqueness of the zonal harmonic** (`eq_smul_zonalHarmonic`): for `n ≥ 3` and unit `η`, a
  harmonic homogeneous polynomial of degree `l` that is invariant under `K_η` equals
  `p(η) Z_{l,η}`, with `Z_{l,η}` the zonal harmonic of 3.3;
- the irreducible representations of `SO(n)` with a nonzero `K_η`-fixed vector are exactly the
  `H_l` (`n ≥ 3`), and that vector is unique up to a scalar.

Route: a `K_η`-invariant polynomial is a polynomial in `⟪η, x⟫` and `|x|²` (the `K_η`-orbits
are the spheres of 1.1); harmonicity of `∑ a_j ⟪η, x⟫^j |x|^{l-j}` gives the two-term recurrence of
the coefficients of `ω_{n,l}`, which leaves one free constant. The classification uses the
Peter–Weyl theorem: a class-one representation occurs in `L²(SO(n)/K_η) = L²(S^{n-1})`.

**Checks.**
- For `n = 3`, `l = 2`, `η = e₃`, the invariant harmonics are the multiples of
  `(3x₃² - |x|²)/2`, with value `1` at `η`.
- `Z_{1,η}(x) = ⟪η, x⟫` for every `n ≥ 2`.
- Negative control: for `n = 2`, `K_η` is trivial, every element of `H_l` is invariant, and
  `dim H_l = 2` for `l ≥ 1`; uniqueness needs `n ≥ 3`.
- Negative control: the misprinted denominator `C_l^{(n-1)/2}(1)` of Vilenkin–Klimyk p. 173 gives
  the value `C_2^{(1/2)}(1)/C_2^{(1)}(1) = 1/3` at `η` for `n = 3`, `l = 2`, not `1`.

## Layer 3: zonal polynomials and Gegenbauer polynomials

### 3.1 The zonal polynomial

Sources: Vilenkin–Klimyk §9.3.2 (2)–(4), p. 47 (the zonal spherical function as a
hypergeometric function and as a normalized Gegenbauer polynomial); Wawrzyńczyk (9.2.11),
p. 330; Klimyk–Vilenkin Part II, Chapter 2, §2.4, (25), p. 180; Dieudonné §7, (103), p. 24.

`zonalPolynomial n l` is the terminating sum
`∑_{k ≤ l} (-l)_k (l + n - 2)_k / (((n - 1)/2)_k k!) ((1 - t)/2)^k` (`zonalPolynomial_def`).
For `n ≤ 1` the lower parameter `(n - 1)/2` is not positive, a denominator may vanish and the
value is junk; every theorem except the value at one assumes `n ≥ 2`. Prove:
- **Value at one** (`zonalPolynomial_eval_one`): `ω_{n,l}(1) = 1`;
- **Parity** (`zonalPolynomial_comp_neg`): `ω_{n,l}(-t) = (-1)^l ω_{n,l}(t)` for `n ≥ 2`;
- **Degree** (`natDegree_zonalPolynomial`): `ω_{n,l}` has degree exactly `l` for `n ≥ 2`;
- **Gegenbauer form** (`gegenbauer_eq_zonalPolynomial`): for `n ≥ 3` and `λ = (n - 2)/2`,
  `C_l^{(λ)} = ((n - 2)_l / l!) ω_{n,l}`;
- **Chebyshev** (`zonalPolynomial_two`): `ω_{2,l} = T_l`;
- **Legendre** (`zonalPolynomial_three`): `ω_{3,l} = P_l = P_l^{(0,0)}`;
- for `n = 4`, `(l + 1) ω_{4,l} = U_l`, the Chebyshev polynomial of the second kind.

Route: the Gegenbauer form by comparison with DLMF 18.5.10 through Pfaff's transformation, or by
the Jacobi relation of LaguerreJacobi §6.2 and the hypergeometric form of the Jacobi polynomials;
the parity from the symmetry `t ↦ -t` of the differential equation of 3.2; the special cases by
the same differential equation and the value at one.

**Checks.**
- `ω_{n,0} = 1` and `ω_{n,1}(t) = t` for every `n ≥ 2`.
- `ω_{n,2}(t) = (n t² - 1)/(n - 1)`: at `t = 0.3` it is `-0.82` for `n = 2`, `-0.365` for
  `n = 3` and `-0.092` for `n = 6`.
- `ω_{3,2}(t) = (3t² - 1)/2` and `ω_{5,2}(t) = (5t² - 1)/4`.
- `ω_{2,3}(0.3) = T_3(0.3) = -0.792`.
- `ω_{n,l}(-1) = (-1)^l`.
- Negative control: `ω_{4,2}(t) = (4t² - 1)/3`, while the unnormalized `C_2^{(1)}(t) = 4t² - 1`;
  with the lower parameter `(n - 2)/2` in place of `(n - 1)/2` the value at `t = 0.3`, `n = 4`
  would be `-0.575` instead of `-0.21333`.

### 3.2 One-variable identities

Sources: Vilenkin–Klimyk §9.3.7 (1)–(2), pp. 59–60 (generating function); Vilenkin–Klimyk §9.3.2
(4), p. 47 (the value `C_l^{(p)}(1)`); Dieudonné §7, (103), p. 24 (the Gegenbauer polynomials
and their differential equation).

Prove:
- **Value at one** (`gegenbauer_eval_one`): `C_l^{(λ)}(1) = (2λ)_l/l!` for every real `λ`;
- **Generating function** (`hasSum_gegenbauer`): for `|t| ≤ 1` and `|z| < 1`,
  `∑_l C_l^{(λ)}(t) zˡ = (1 - 2tz + z²)^{-λ}`;
- **Derivative** (`derivative_gegenbauer`): `d/dt C_{l+1}^{(λ)} = 2λ C_l^{(λ+1)}`;
- **Derivative of the zonal polynomial** (`derivative_zonalPolynomial`): for `n ≥ 2`,
  `ω_{n,l+1}' = ((l + 1)(l + n - 1)/(n - 1)) ω_{n+2,l}`;
- **Differential equation** (`zonalPolynomial_ode`): for `n ≥ 2`,
  `(1 - t²) ω'' - (n - 1) t ω' + l(l + n - 2) ω = 0`.

Route: the generating function by the binomial series in `2tz - z²` and the explicit sum; the
derivative by differentiating the explicit sum term by term; the differential equation from the
hypergeometric equation in `(1 - t)/2`. Vilenkin–Klimyk's route to the generating function is
group theoretic: `|x - h|^{2-n}` is harmonic in `x` and invariant under `K_η` for `h = |h| η`, so
its Taylor coefficients in `|h|` are zonal harmonics.

**Checks.**
- At `λ = 3/2`, `t = 0.4`, `z = 0.3` both sides of the generating function are `1.27606 15166`.
- At `λ = 0` the generating function gives `C_0^{(0)} = 1` and `C_l^{(0)} = 0` for `l ≥ 1`, in
  agreement with LaguerreJacobi §6.2.
- `ω_{5,4}' = 7 ω_{7,3}` (the case `n = 5`, `l = 3`).
- The residual of the differential equation for `ω_{n,3}` at `t = 0.35` vanishes for `n = 2, 3, 5`.
- Negative control: with `(n - 2) t ω'` in place of `(n - 1) t ω'`, the residual for `ω_{5,3}` at
  `t = 0.35` is `0.525`, not `0`.

### 3.3 The zonal harmonic

Sources: Vilenkin–Klimyk §9.2.3 (3), p. 30 (the harmonic projection) and §10.2.1, p. 173;
Wawrzyńczyk (9.2.9)–(9.2.11), p. 330; Dieudonné §7, p. 23.

`linearForm η` is the polynomial `x ↦ ⟪η, x⟫` (`eval_linearForm`), and `zonalHarmonic n l η` is
`∑_j c_j ⟪η, x⟫^j |x|^{l-j}` over `j ≡ l (mod 2)`, where `c_j` are the coefficients of
`ω_{n,l}`. Prove:
- **The zonal harmonic is harmonic** (`zonalHarmonic_mem_harmonicSubmodule`): for `n ≥ 2` and a
  unit vector `η`, `Z_{l,η} ∈ H_l`;
- **Values on the sphere** (`eval_zonalHarmonic`): for `n ≥ 2` and `|x| = 1`,
  `Z_{l,η}(x) = ω_{n,l}(⟪η, x⟫)`;
- **Invariance** (`eval_smul_zonalHarmonic`): `Z_{l,η}(k x) = Z_{l,η}(x)` for `k ∈ K_η`.

Route: the Laplacian of `⟪η, x⟫^j |x|^{2i}` with `|η| = 1` is
`j(j - 1)|x|^{2i} ⟪η, x⟫^{j-2} + 2i(2i + n - 2 + 2j) ⟪η, x⟫^j |x|^{2i-2}`, and the coefficient
recurrence is that of the differential equation of 3.2.

**Checks.**
- For `n = 3`, `l = 2`: `Z = (3⟪η, x⟫² - |x|²)/2`, of Laplacian `0`, with `Z(η) = 1`.
- For `n = 4`, `l = 2`: `Z = (4⟪η, x⟫² - |x|²)/3`.
- The zonal harmonics of degrees `2, 3, 4` in dimensions `2, 3, 4, 5`, for
  `η = (1/3, 2/3, 2/3, 0, …)` (and `(3/5, 4/5)` for `n = 2`), have Laplacian `0` and value `1` at
  `η`.
- Negative control: `η` must be a unit vector: for `n = 3`, `l = 2` the Laplacian of
  `(3⟪η, x⟫² - |x|²)/2` is `3(|η|² - 1)`.
- Negative control: `P_2` homogenized in `ℝ⁴`, `(3x₄² - |x|²)/2`, has Laplacian `-1`; the
  dimension in `ω_{n,l}` must be that of the ambient space.

### 3.4 The Laplace integral

Sources: Vilenkin–Klimyk §9.3.2 (2), p. 47; Klimyk–Vilenkin Part II, Chapter 2, §2.4, (24),
p. 179 (the integral over the sphere and its hypergeometric value).

Prove:
- **Laplace integral** (`zonalPolynomial_laplace`): for `n ≥ 3`,
  `ω_{n,l}(cos φ) = c'ₙ ∫_0^π (cos φ + i sin φ cos θ)^l sin^{n-3} θ dθ` with
  `c'ₙ = Γ((n - 1)/2)/(√π Γ((n - 2)/2))`.

Route: the function `x ↦ (⟪η, x⟫ + i⟪ζ, x⟫)^l` with `ζ ⊥ η` a unit vector is harmonic; average it
over `K_η` and apply 2.3 and the density of 1.2 on the sphere `S^{n-2}` of `ζ`.

**Checks.**
- `c'₃ = 1/π`, `c'₄ = 1/2`, `c'₅ = 2/π`.
- At `φ = 0.9`, `n = 3`, `l = 2` both sides are `0.07959 84290` (Laplace's first integral for
  `P_2`); at `n = 5`, `l = 3` both are `-0.04587 59550`.
- Vilenkin–Klimyk print `cos θ - i sin θ cos ψ`; the substitution `ψ ↦ π - ψ` gives the sign
  used here.
- Negative control: for `n = 2` the constant `c'₂` has `Γ(0)` in the denominator; the formula
  needs `n ≥ 3`.

## Layer 4: addition theorem, Funk–Hecke, spherical functions

### 4.1 Addition theorem and reproducing kernel

Sources: Vilenkin–Klimyk §10.2.1 (2)–(3), pp. 174–175 (the convolution theorem and the addition
theorem with normalized measure); Vilenkin–Klimyk §9.3.1 (1)–(5), pp. 44–46; Wawrzyńczyk
Theorem 9.4.1, p. 335; Dieudonné §7, (101), p. 23.

Prove:
- **Addition theorem** (`addition_theorem`): for `n ≥ 2` and an `L²(sphereMeasure n)`-orthonormal
  basis `Y` of `H_l`, `∑ᵢ Yᵢ(x) Yᵢ(y) = dim H_l · ω_{n,l}(⟪x, y⟫)` on the sphere;
- **Reproducing property** (`integral_sphereEval_mul_zonalPolynomial`): for `n ≥ 2` and
  `p ∈ H_l`, `∫ p(x) ω_{n,l}(⟪x, y⟫) dσ(x) = p(y)/dim H_l`;
- **Bound** (`abs_zonalPolynomial_le_one`): `|ω_{n,l}(t)| ≤ 1` for `|t| ≤ 1` and `n ≥ 2`;
- `dim H_l · ω_{n,l}(⟪·, y⟫)` restricted to the sphere is the kernel of the orthogonal projection of
  `L²(S^{n-1})` onto `H_l`.

Route: `K(x, y) = ∑ Yᵢ(x) Yᵢ(y)` does not depend on the basis, is invariant under the diagonal
action of `SO(n)` (1.2), so `K(·, y) ∈ H_l` is `K_y`-invariant and is `K(y, y) Z_{l,y}` by 2.3
(for `n = 2` directly from `cos`, `sin`); integrating `K(y, y)` over `y` gives `dim H_l`. The bound
is Cauchy–Schwarz on `K`.

**Checks.**
- `n = 3`: `∑_m Y_l^m(x) conj Y_l^m(y) = (2l + 1)/(4π) P_l(⟪x, y⟫)` in the measure of total mass
  `4π`, the addition theorem of SpecialFunctionsSU2MatrixElements §6.3; with mass `1` the factor is
  `2l + 1`.
- `n = 2`: `Y = √2 cos lθ, √2 sin lθ` gives `2 cos l(θ - θ') = 2 T_l(cos(θ - θ'))`.
- `l = 0`: `Y = 1` and `ω = 1`.
- Negative control: in the unnormalized surface measure of `S²` the constant is `(2l + 1)/(4π)`,
  not `2l + 1`; the normalization of 1.2 is what makes the constant a dimension.

### 4.2 Orthogonality

Sources: Vilenkin–Klimyk §9.3.8 (1)–(3), pp. 62–63; Wawrzyńczyk (9.4.10), p. 335;
Klimyk–Vilenkin Part II, Chapter 3, §1.10, (29), p. 192.

Prove:
- **Orthogonality** (`integral_zonalPolynomial_mul`): for `n ≥ 2`,
  `c_n ∫_{-1}^{1} ω_{n,l} ω_{n,l'} (1 - t²)^{(n-3)/2} dt = δ_{ll'}/dim H_l`;
- for `n ≥ 3` this is the orthogonality of LaguerreJacobi §6.2 at `λ = (n - 2)/2`, with
  `h_l = π 2^{1-2λ} Γ(l + 2λ)/((l + λ) l! Γ(λ)²)` (DLMF 18.3, Table 18.3.1) and the ratio of
  normalizations of 3.1.

Route: by 1.2, the integral is `∫ Z_{l,η} Z_{l',η} dσ`; for `l ≠ l'` the spaces `H_l`, `H_{l'}` are
orthogonal (R8.2); for `l = l'` it is `Z_{l,η}(η)/dim H_l` by the reproducing property of 4.1.

**Checks.**
- `n = 3`, `l = l' = 2`: `1/5`; `n = 4`, `l = l' = 3`: `1/16`; `n = 6`, `l = l' = 2`: `1/20`.
- `n = 2`, `l = l' = 3`: `(1/π) ∫ T_3² (1 - t²)^{-1/2} dt = 1/2`.
- `l = 2`, `l' = 4` and `l = 1`, `l' = 3`: `0` for `n = 3, …, 6`.
- Negative control: without the weight, `c_5 ∫ ω_{5,2}² dt = 0.25`, not `1/14`.

### 4.3 The Funk–Hecke formula

Sources: Vilenkin–Klimyk §10.2.1 (5)–(6), p. 175; Wawrzyńczyk (9.5.1), p. 337.

Prove:
- **Funk–Hecke** (`funk_hecke`): for `n ≥ 2`, continuous `f`, unit `η` and `p ∈ H_l`,
  `∫ f(⟪η, x⟫) p(x) dσ(x) = λ_l(f) p(η)` with
  `λ_l(f) = c_n ∫_{-1}^{1} f(t) ω_{n,l}(t) (1 - t²)^{(n-3)/2} dt`;
- the formula extends to `f` with `∫ |f(t)| (1 - t²)^{(n-3)/2} dt < ∞`.

Route: `f(⟪η, x⟫)` is `K_η`-invariant, so by 1.2 the integral does not change when `p` is
replaced by its average over `K_η`, which is `p(η) Z_{l,η}` by 2.3; the integral of
`f(⟪η, x⟫) Z_{l,η}(x)` is `λ_l(f)` by the density of 1.2 and 3.3.

**Checks.**
- `n = 3`, `l = 2`, `f = exp`: `λ_2 = (1/2) ∫ eᵗ P_2(t) dt = (e - 7/e)/2 = 0.07156 28701`.
- For `f = ω_{n,l'}`, `λ_l(f) = δ_{ll'}/dim H_l` (4.2).
- Monte Carlo for `f = exp`, `p = x₁x₂` and `p = Re(x₁ + i x₂)³`, `η = (0.6, 0.8, 0, …)`,
  `n = 2, 3, 4`, agrees with `λ_l(f) p(η)` within sampling error.
- Negative control: replacing `ω_{n,l}` by the unnormalized `C_l^{((n-2)/2)}` multiplies the
  right side by `C_l^{((n-2)/2)}(1)`, for example by `3` at `n = 4`, `l = 2`.

### 4.4 Zonal spherical functions

Sources: Vilenkin–Klimyk §9.3.2 (4), p. 47 and §9.4.5 (1), p. 76 (product formula);
Wawrzyńczyk (9.4.9), p. 335 and (9.5.2), p. 337 (with W84-E09.5.01 of the project's errata
file, which corrects the derivation and confirms the formula); Klimyk–Vilenkin Part II,
Chapter 2, §2.4, (25), p. 180; Dieudonné §7, p. 24.

`zonalSpherical n l η g = ω_{n,l}(⟪η, g η⟫)`. Prove:
- **Zonal spherical functions** (`isSphericalFunction_zonalSpherical`): for `n ≥ 3`, unit `η`
  and a left-invariant probability measure `ν` on `K_η`, `zonalSpherical n l η` is a spherical
  function of `(SO(n), K_η)`;
- **Classification** (`exists_eq_zonalSpherical`): for `n ≥ 3`, every spherical function of
  `(SO(n), K_η)` is `zonalSpherical n l η` for some `l`;
- **Product formula** (`zonalPolynomial_product`): for `n ≥ 3`,
  `ω(cos a) ω(cos b) = c'ₙ ∫_0^π ω(cos a cos b + sin a sin b cos ψ) sin^{n-3} ψ dψ`;
- `zonalSpherical n l η g = ⟪Z, g · Z⟫/⟪Z, Z⟫` for the zonal harmonic `Z = Z_{l,η}` in
  `L²(sphereMeasure n)`, and it is positive definite.

Route: the functional equation is SpecialFunctionsGroupModels §5.3 applied to `H_l` with fixed
vector `Z_{l,η}` (2.3); the classification uses multiplicity one (§5.3 there) and Peter–Weyl, with
2.3 for the class-one representations. The product formula is the functional equation at
`x = g_a`, `y = g_b` (rotations by `a`, `b` in a plane through `η`), with the integral over `K_η`
reduced to `ψ` by the density of 1.2 on `S^{n-2}`.

**Checks.**
- `n = 3`, `l = 3`, `a = 0.7`, `b = 1.9`: both sides of the product formula are
  `-0.01149 84607`; for `n = 4` they are `0.03324 20083`, for `n = 6` `0.03595 25879`.
- Wawrzyńczyk's form (9.5.2) with `C_l^{(p)}`, `p = 3/2`, `l = 3`: both sides `0.60290 52598`.
- `zonalSpherical n l η 1 = ω_{n,l}(1) = 1`.
- Negative control: for `n = 2`, `K_η` is trivial and `cos lθ = ω_{2,l}(cos θ)` is not
  multiplicative: `cos 1.2 = 0.36236` while `cos 0.5 cos 0.7 = 0.67121`; the spherical functions of
  `SO(2)` are the characters `e^{ilθ}`, so the hypothesis `n ≥ 3` is needed.

### 4.5 The Gegenbauer addition theorem

Sources: Vilenkin–Klimyk §9.4.3 (1)–(5), p. 71 (with erratum E09.4.01 of the project's errata
file for the three-angle relation (2)); Klimyk–Vilenkin Part II, Chapter 3, §1.3, (14), p. 186.

Prove:
- **Gegenbauer addition theorem** (`gegenbauer_addition`): for `λ > 1/2` the identity displayed
  below holds for all real `θ`, `φ`, `ψ`;
- the case `λ = (n - 2)/2` is the addition theorem of 4.1 for the matrix elements of
  `SO(n)` between the Gel'fand–Tsetlin vectors of 5.2 of the second level.

```text
C_l^(λ)(cos θ cos φ + sin θ sin φ cos ψ)
  = Γ(2λ - 1)/Γ(λ)² ∑_{m ≤ l} 2^(2m) Γ(λ + m)² (l - m)! (2λ + 2m - 1)/Γ(2λ + l + m)
      (sin θ sin φ)^m C_{l-m}^(λ+m)(cos θ) C_{l-m}^(λ+m)(cos φ) C_m^(λ-1/2)(cos ψ)
```

Route: expand `Z_{l,η}(g x)` in the branching basis of 5.1 for the chain
`SO(n) ⊃ SO(n - 1)`, with the norm constant of 5.1; the coefficients are associated spherical
functions `sin^m θ C_{l-m}^{(λ+m)}(cos θ)`, and the remaining zonal function of `SO(n - 1)` is
`C_m^{(λ-1/2)}`. The polynomial identity then extends from `λ = (n - 2)/2`, `n ≥ 4`, to real
`λ > 1/2` because both sides are rational in `λ` after division by `Γ(λ)²`.

**Checks.**
- At `l = 4`, `θ = 0.6`, `φ = 1.3`, `ψ = 2.2`: both sides `1.61944 86134` for `λ = 3/2`,
  `0.88298 12104` for `λ = 1`, `3.61090 91337` for `λ = 5/2`.
- `l = 0`: both sides are `1`, since `Γ(2λ - 1)(2λ - 1)/Γ(2λ) = 1`.
- Negative control: at `λ = 1/2` the factor `Γ(2λ - 1)` has a pole and `C_m^{(0)} = 0` for
  `m ≥ 1`; the Legendre case needs the limit form with `C_m^{(0)}` replaced by `(2/m) T_m`, and
  the hypothesis `λ > 1/2` excludes it.

## Layer 5: branching `SO(m + 1) ↓ SO(m)`

### 5.1 The branching harmonics

Sources: Vilenkin–Klimyk §9.3.1 (1)–(5), pp. 44–46 (the orthonormal basis of `L²(S^{n-1})`
built from Gegenbauer polynomials); Klimyk–Vilenkin Part II, Chapter 2, §2.4, (27), p. 180 (the
matrix elements `t_{m0}^l`); Wawrzyńczyk (9.2.9), p. 330.

`branchFactor m l k` is `|x|^{l-k} ω_{m+1+2k,l-k}(x_{m+1}/|x|)` on `ℝ^{m+1}`, and
`branchHarmonic m l k h = branchFactor m l k · h(x₁, …, x_m)` (`branchHarmonic_apply`). Prove:
- **Branching harmonics are harmonic** (`branchHarmonic_mem`): for `m ≥ 1`, `k ≤ l` and
  `h ∈ H_k(ℝᵐ)`, `branchHarmonic m l k h ∈ H_l(ℝ^{m+1})`;
- **Branching decomposition** (`harmonicSubmodule_eq_iSup_branchHarmonic`): for `m ≥ 1`,
  `H_l(ℝ^{m+1})` is the internal direct sum over `k ≤ l` of the images of `H_k(ℝᵐ)`;
- **Branching dimension** (`finrank_harmonicSubmodule_succ`): for `m ≥ 1`,
  `dim H_l(ℝ^{m+1}) = ∑_{k ≤ l} dim H_k(ℝᵐ)`;
- **Branching norm** (`integral_branchHarmonic_sq`): for `m ≥ 1`, `k ≤ l` and `h ∈ H_k(ℝᵐ)`,
  `‖branchHarmonic m l k h‖² = κ ‖h‖²` in the normalized `L²` norms, with
  `κ = c_{m+1}/(c_{m+1+2k} dim H_{l-k}(ℝ^{m+1+2k}))`;
- the images are the `SO(m)`-isotypic components of `H_l(ℝ^{m+1})`, the abstract branching rule of
  ClassicalGroups Layer 6.2, and are pairwise orthogonal.

Route: with `x = (x', s)`, `r = |x|`, and `h` harmonic of degree `k`, the Laplacian of
`F(s, r) h(x')` reduces to the equation of 3.2 for `ω_{m+1+2k,l-k}` (the shift `2k` is the degree
of `h`); the dimension count closes the decomposition. The norm is the integral over the sphere in
the coordinates `x = (sin θ y, cos θ)`, `y ∈ S^{m-1}`, which by 1.2 and 4.2 gives `κ`.

**Checks.**
- The branching harmonics for `m + 1 = 3, 4`, `l = 2, 3`, `k = 0, 1, 2` with `h = 1, x₁, x₁x₂`
  have Laplacian `0`.
- Dimension count: `dim H_l(ℝ^{m+1}) = ∑_{k ≤ l} dim H_k(ℝᵐ)` for `m = 2, …, 6`, `l ≤ 7`;
  for `m = 1` it reads `2 = 1 + 1` for `l ≥ 1`.
- `κ` for `m = 2`, `l = 2`, `k = 1`: `c_3/(c_5 · 5) = 2/15`; Monte Carlo of the left side for
  `h = x₁` gives `0.0666` against `(2/15)(1/2) = 0.0667`.
- Negative control: for `m + 1 = 3`, `l = 3`, `k = 1` the factor `ω_{3,2}` of the ambient
  dimension in place of `ω_{5,2}` gives `branchFactor · x₁` the Laplacian `-2x₁`; the shift by
  `2k` is needed.

### 5.2 The Gel'fand–Tsetlin basis and associated spherical functions

Sources: Vilenkin–Klimyk §9.3.1 (1)–(5), pp. 44–46; Klimyk–Vilenkin Part II, Chapter 2, §2.4,
(27), p. 180.

Prove:
- **Gel'fand–Tsetlin basis**: iterating 5.1 along `ℝⁿ ⊃ ℝ^{n-1} ⊃ … ⊃ ℝ²` gives, for every
  chain `l = l_{n-1} ≥ l_{n-2} ≥ … ≥ l_1 ≥ 0` and sign `±` of the last step, an element of `H_l`
  that is a product of factors `sin^{l_{j-1}} θ_j ω_{j+2l_{j-1}, l_j - l_{j-1}}(cos θ_j)` in the
  spherical coordinates of Vilenkin–Klimyk §9.1.9 (6); after division by the square root of the
  product of the constants `κ` of 5.1 these form an orthonormal basis of `H_l` in
  `L²(sphereMeasure n)`;
- **Associated spherical functions**: for `h ∈ H_k(ℝ^{n-1})` the function
  `g ↦ ⟪branchHarmonic (n - 1) l k h, g · Z_{l,e_n}⟫` depends on `g` through `g e_n` and is
  proportional to `sin^k θ C_{l-k}^{(k+(n-2)/2)}(cos θ) h(ξ')` at `g e_n = (sin θ ξ', cos θ)`.

Route: 5.1 by induction on the dimension, with orthogonality of the images of distinct `k`; the
associated functions by the reproducing property of 4.1 applied to `branchHarmonic`.

**Checks.**
- For `n = 3` the basis is `sin^{|m|} θ ω_{3+2|m|, l-|m|}(cos θ) (cos mφ or sin mφ)`, which is
  `Y_l^m` up to normalization and the Condon–Shortley sign.
- The number of chains with `l_{n-1} = l` is `dim H_l(ℝⁿ)` (5.1, iterated).
- Negative control: omitting the factor `sin^{l_{j-1}} θ_j` destroys harmonicity: for `n = 3`,
  `l = 1`, `m = 1`, `cos φ` alone is not the restriction of a harmonic polynomial of degree `1`.

## Layer 6: the complex sphere and `U(n)`

### 6.1 `U(n)` and the complex sphere

Sources: Vilenkin–Klimyk §11.2.2 (1)–(15), pp. 295–297 (the representations `T^{nℓℓ′}` and
the subgroup `U(n - 1)`); Klimyk–Vilenkin Part II, Chapter 2, §2.8, p. 182.

`U(n)` acts on `ℂⁿ` (`smul_def_unitary`), `ComplexSphere n` is the unit sphere `S^{2n-1}`,
`stabU η` is the stabilizer and `complexSphereMeasure n` the normalized surface measure. Prove:
- **Transitivity** (`exists_smul_eq_unitary`): for `n ≥ 1`, `U(n)` acts transitively on the unit
  sphere;
- **Disc density** (`integral_inner_complexSphereMeasure`): for `n ≥ 2` and unit `η`,
  `∫ f(⟪η, ξ⟫) dσ(ξ) = ((n - 1)/π) ∫_{|w|<1} f(w) (1 - |w|²)^{n-2} dA(w)`;
- **Gel'fand pair** (`isGelfandPair_Un`): `(U(n), K_η)` is a Gel'fand pair for every `n`, `η`;
- the double coset `K_η g K_η` is determined by `⟪η, g η⟫` for `n ≥ 2`.

Route: transitivity by unitary Gram–Schmidt; the density from the real density of 1.2 in
dimension `2n` after integrating over the circle of phases; the Gel'fand pair by Gel'fand's
criterion with `σ(g) = gᵀ` for `η = e_n`, which preserves `⟪η, g η⟫` and hence, by the last
bullet, each double coset; a general unit `η` is conjugate to `e_n`, and `U(1)` is abelian.

**Checks.**
- `E|⟪η, ξ⟫|⁴ = 2/(n(n + 1))`: `1/3`, `1/6`, `1/10` for `n = 2, 3, 4`, by the density and by
  Monte Carlo.
- The density has mass one: `((n - 1)/π) ∫_{|w|<1} (1 - |w|²)^{n-2} dA = 1`.
- Negative control: for `n = 1` the image of the sphere is the unit circle, which has measure zero
  in the disc; the density needs `n ≥ 2`.
- `stabU η` for unit `η` is conjugate to the `U(n - 1)` fixing the last coordinate.

### 6.2 Harmonics of bidegree `(p, q)`

Sources: Vilenkin–Klimyk §11.2.1 (18)–(20), p. 295 (dimension and eigenvalue) and §11.2.2
(1)–(15), pp. 295–297 (irreducibility, the `U(n - 1)`-fixed vector and branching);
Klimyk–Vilenkin Part II, Chapter 2, §2.8, p. 182 (highest weights `(p, 0, …, 0, -q)` and the
restriction to `U(n - 1)`).

Polynomials in `z, z̄` are `MvPolynomial (Fin n ⊕ Fin n) ℂ`, the variable `Sum.inl j` standing for
`zⱼ` and `Sum.inr j` for `z̄ⱼ`; `bidegreeWeight` assigns `(1, 0)` and `(0, 1)`, `complexLaplacian`
is `∑ⱼ ∂²/∂zⱼ∂z̄ⱼ`, `bidegreeHarmonic n p q` is the space `H^{p,q}` of harmonic polynomials of
bidegree `(p, q)`, and `evalC z f` evaluates at `(z, z̄)`. Prove:
- **Dimension** (`finrank_bidegreeHarmonic_mul`): for `n ≥ 2`,
  `dim H^{p,q} = (p + n - 2)!(q + n - 2)!(p + q + n - 1)/((n - 1)!(n - 2)! p! q!)`, multiplied
  out in `ℕ`;
- **Real and complex harmonics** (`finrank_harmonicSubmodule_eq_sum_bidegree`):
  `dim H_m(ℝ^{2n}) = ∑_{p+q=m} dim H^{p,q}(ℂⁿ)`;
- **Branching dimension** (`finrank_bidegreeHarmonic_succ`): for `n ≥ 1`,
  `dim H^{p,q}(ℂ^{n+1}) = ∑_{a ≤ p, b ≤ q} dim H^{a,b}(ℂⁿ)`;
- **Decomposition**: the complexification of `H_m(ℝ^{2n})`, written in `z, z̄`, is the direct sum
  of the `H^{p,q}` with `p + q = m`;
- **Irreducibility and inequivalence**: `U(n)` acts irreducibly on `H^{p,q}` by
  `(g · f)(z) = f(g⁻¹ z)`, with highest weight `(p, 0, …, 0, -q)`, and the `H^{p,q}` are
  pairwise inequivalent for `n ≥ 2`;
- the restriction of `H^{p,q}(ℂ^{n+1})` to `U(n)` is the sum of the `H^{a,b}(ℂⁿ)` with `a ≤ p`,
  `b ≤ q`, each once.

Route: the complex Fischer decomposition (multiplication by `|z|²` is injective and adjoint to the
complex Laplacian), giving `dim H^{p,q} = dim P^{p,q} - dim P^{p-1,q-1}`; irreducibility from the
uniqueness of the `K_η`-fixed vector (6.4) and the highest-weight theory of ClassicalGroups.

**Checks.**
- `n = 2`: `dim H^{p,q} = p + q + 1`; `n = 3`: `dim H^{1,1} = 8` (the adjoint representation of
  `SU(3)`), `dim H^{2,1} = 15`.
- `dim H^{p,q} = C(n + p - 1, p) C(n + q - 1, q) - C(n + p - 2, p - 1) C(n + q - 2, q - 1)` for
  `n = 2, …, 5`, `p, q ≤ 4`.
- `∑_{p+q=m} dim H^{p,q}(ℂⁿ) = dim H_m(ℝ^{2n})` for `n = 2, …, 5`, `m ≤ 6`.
- Negative control: `|z|² = ∑ zⱼ z̄ⱼ` has bidegree `(1, 1)` and `complexLaplacian` value `n`, not
  `0`; it is not in `H^{1,1}`.
- Negative control: for `n = 1`, `H^{p,q}(ℂ)` is `0` for `p, q ≥ 1` (`∂_z ∂_{z̄} z^p z̄^q ≠ 0`),
  whereas the dimension formula at `n = 1` is meaningless; the hypothesis `n ≥ 2` is needed there.

### 6.3 Disk polynomials

Sources: Vilenkin–Klimyk §11.3.2 (4)–(6), p. 309 (the zonal functions of `U(n)` as `₂F₁` and Jacobi
polynomials) and §11.4.5, p. 345 (the disk polynomials `R^α_{mn}`; the printed case `m < n` has
`z` where `z̄` is meant, and the coefficient of (28) is erratum E11.4.10 of the project's errata
file); Klimyk–Vilenkin Part II, Chapter 2, §2.8, (34), p. 182.

`diskPolynomial α p q w` is the sum over `i ≤ min(p, q)` of
`(-1)ⁱ C(p, i) C(q, i) i!/(α + 1)ᵢ · (1 - |w|²)ⁱ w^{p-i} w̄^{q-i}` (`diskPolynomial_def`), a
form symmetric in `p` and `q`. For `α ∈ {-1, -2, …}` a denominator vanishes and the value is
junk; the theorems assume `-1 < α` or `α = n - 2`, `n ≥ 2`. Prove:
- **Value at one** (`diskPolynomial_one`): `R^α_{p,q}(1) = 1`;
- **Symmetry** (`diskPolynomial_swap`): `R^α_{q,p} = conj R^α_{p,q}`;
- **Jacobi form** (`diskPolynomial_eq_jacobi`): for `-1 < α` and `q ≤ p`,
  `R^α_{p,q}(w) = (q!/(α + 1)_q) P_q^{(α, p-q)}(2|w|² - 1) w^{p-q}`;
- **Orthogonality on the disc** (`integral_diskPolynomial_mul`): for `-1 < α`,
  `((α + 1)/π) ∫_{|w|<1} R^α_{p,q} conj R^α_{p',q'} (1 - |w|²)^α dA = δ h` with
  `h = (α + 1)/(p + q + α + 1) · p! q!/((α + 1)_p (α + 1)_q)`;
- **Bound** (`norm_diskPolynomial_le_one`): `|R^{n-2}_{p,q}(w)| ≤ 1` for `|w| ≤ 1`, `n ≥ 2`;
- the `R^α_{p,q}` form a complete orthogonal system in `L²` of the disc with weight
  `(1 - |w|²)^α`, `α > -1`.

Route: the Jacobi form by expanding `P_q^{(α,β)}` in powers of `(x - 1)/2 = |w|² - 1`; the
orthogonality from the orthogonality of `e^{i(p-q)θ}` in the angle and of Jacobi polynomials in
`2r² - 1` (LaguerreJacobi §4 through §3.2); the bound from 6.5 (a normalized positive-definite
function is bounded by its value at `1`); completeness from the Stone–Weierstrass theorem, since
the `R^α_{p,q}` with `p + q ≤ N` span the polynomials of degree `≤ N` in `w, w̄`.

**Checks.**
- `R^α_{p,0}(w) = w^p`; `R^0_{1,1}(w) = 2|w|² - 1`; `R^α_{1,1}(w) = ((α + 2)|w|² - 1)/(α + 1)`,
  so `R^1_{1,1}(0.5) = -1/8`.
- `R^0_{2,1}(w) = w(3|w|² - 2)`, so `R^0_{2,1}(0.5) = -0.625`.
- Orthogonality constants: `h = 1/3, 1/4, 1/5` for `α = 0` and `(p, q) = (1, 1), (2, 1), (3, 1)`;
  `h = 4/21` for `α = 1/2`, `(1, 1)`; `h = 4/5` for `α = -1/2`, `(1, 1)`; cross terms `0`.
- Negative control (the misprint of Vilenkin–Klimyk p. 345): with `z` in place of `z̄` for
  `p < q`, `R_{0,1}(i)` would be `i`; the correct value is `conj i = -i`.
- Negative control: at `α = -1` the coefficient of `i = 1` divides by `(0)₁ = 0`.

### 6.4 The `U(n)`-zonal harmonic

Sources: Vilenkin–Klimyk §11.2.2 (11)–(13), p. 297 (uniqueness of the `U(n - 1)`-fixed vector) and
§11.3.2 (4)–(6), p. 309.

`diskHarmonic n p q η` is `∑ᵢ cᵢ (|z|² - w w̄)ⁱ w^{p-i} w̄^{q-i}` with `w = ⟪η, z⟫` and the
coefficients `cᵢ` of `R^{n-2}_{p,q}`. Prove:
- **The `U(n)`-zonal harmonic lies in `H^{p,q}`** (`diskHarmonic_mem`): for `n ≥ 2` and a unit
  vector `η`;
- **Values on the sphere** (`evalC_diskHarmonic`): for `n ≥ 2` and `|ξ| = 1`, its value is
  `R^{n-2}_{p,q}(⟪η, ξ⟫)`;
- **Class one** (`eq_smul_diskHarmonic`): for `n ≥ 2` and unit `η`, a `K_η`-invariant element of
  `H^{p,q}` is `f(η) · diskHarmonic n p q η`.

Route: as in 2.3 and 3.3, with the `K_η`-invariants generated by `w`, `w̄` and `|z|²`, and the
coefficient recurrence of the hypergeometric equation in `1 - |w|²`.

**Checks.**
- `diskHarmonic n p q η` has complex Laplacian `0` for `n = 2, 3`, `η = (3/5, 4i/5, 0, …)` and
  `(p, q) = (2, 1), (2, 2), (1, 3)`, and at a random unit `ξ` its value equals
  `R^{n-2}_{p,q}(⟪η, ξ⟫)`.
- `diskHarmonic n 1 0 η = ⟪η, z⟫` and `diskHarmonic n 1 1 η = (n|w|² - |z|²)/(n - 1)`, which is
  `2|w|² - |z|²` at `n = 2`.
- Negative control: with `α = n - 1` in place of `n - 2`, the polynomial for `n = 3`,
  `(p, q) = (1, 1)`, `η = e₃` is proportional to `4|z₃|² - |z|²`, of complex Laplacian `1`, while
  `3|z₃|² - |z|²` has Laplacian `0`.

### 6.5 Spherical functions of `(U(n), K_η)`

Sources: Vilenkin–Klimyk §11.3.2 (4)–(6), p. 309; Klimyk–Vilenkin Part II, Chapter 2, §2.8,
(34), p. 182; Vilenkin–Klimyk §11.2.2 (11)–(15), p. 297.

`diskSpherical n p q η g = R^{n-2}_{p,q}(⟪g η, η⟫)`. Prove:
- **Disk polynomials are spherical functions** (`isSphericalFunction_diskSpherical`): for
  `n ≥ 2`, unit `η` and a left-invariant probability measure `ν` on `K_η`;
- **Classification** (`exists_eq_diskSpherical`): for `n ≥ 2`, every spherical function of
  `(U(n), K_η)` is `diskSpherical n p q η` for some `p, q`;
- **Addition theorem for `H^{p,q}`** (`disk_addition_theorem`): for `n ≥ 2` and an
  `L²(complexSphereMeasure n)`-orthonormal basis `Y` of `H^{p,q}`,
  `∑ᵢ Yᵢ(x) conj Yᵢ(y) = dim H^{p,q} · R^{n-2}_{p,q}(⟪y, x⟫)`;
- `diskSpherical n p q η g = ⟪Z, g · Z⟫/⟪Z, Z⟫` for `Z = diskHarmonic n p q η`.

Route: as in 4.1 and 4.4. The kernel `∑ Yᵢ(x) conj Yᵢ(y)` is holomorphic of degree `p` in `x`,
so it is a function of `⟪y, x⟫ = ∑ conj(yᵢ) xᵢ`; the matrix coefficient is
`⟪Z, g · Z⟫ = ∫ conj Z(ξ) Z(g⁻¹ξ) dσ`, which by the reproducing property is
`R(⟪g η, η⟫)/dim H^{p,q}`.

**Checks.**
- `n = 2`, `(p, q) = (1, 0)`: `Y = √2 z₁, √2 z₂`, and `∑ Yᵢ(x) conj Yᵢ(y) = 2⟪y, x⟫`, which
  is `dim H^{1,0} R_{1,0}(⟪y, x⟫)`.
- `diskSpherical n p q η 1 = R(1) = 1`.
- Monte Carlo of the functional equation on `(U(3), U(2))`, `(p, q) = (2, 1)`: the average over
  `K_η` of `φ(g k h)` is `-0.01130 - 0.00650i` against `φ(g) φ(h) = -0.01127 - 0.00652i`.
- Negative control: without the average over `K_η`, `φ(g h) = -0.20852 + 0.09975i` for the same
  `g`, `h`; `φ` is not multiplicative.
- The argument `⟪η, g η⟫` in place of `⟪g η, η⟫` gives `diskSpherical n q p η`, which is also
  spherical; the convention fixes which of the two is attached to `H^{p,q}`.

### 6.6 Zonal polynomials of `SO(2n)` and disk polynomials

Sources: Vilenkin–Klimyk §11.3.2 (4)–(6), p. 309 and §9.3.2 (4), p. 47; adaptation (restriction
of the zonal harmonic of `SO(2n)` to `U(n)`).

Prove:
- **Zonal polynomials of `SO(2n)` as sums of disk polynomials**
  (`zonalPolynomial_eq_sum_diskPolynomial`): for `n ≥ 2` and every `w ∈ ℂ`,
  `dim H_m(ℝ^{2n}) ω_{2n,m}(Re w) = ∑_{p+q=m} dim H^{p,q}(ℂⁿ) R^{n-2}_{p,q}(w)`.

Route: identify `ℝ^{2n}` with `ℂⁿ`, so `⟪x, y⟫_ℝ = Re ⟪x, y⟫_ℂ`; by 6.2 the space `H_m(ℝ^{2n})`
is the sum of the `H^{p,q}` with `p + q = m`, and summing the addition theorems of 6.5 over
`p + q = m` gives that of 4.1 for `SO(2n)` at `x, y` on the sphere; the identity in `w = ⟪y, x⟫`
on the disc extends to all of `ℂ` because both sides are polynomials in `w, w̄`.

**Checks.**
- `n = 2`, `m = 2`: `9 ω_{4,2}(0.35) = 3(R_{2,0} + R_{1,1} + R_{0,2})(0.35 - 0.52i)`, both sides
  `-1.53`.
- At `w = 1.3 + 0.9i`, outside the disc: both sides are `17.28` (`n = 2`, `m = 2`) and `136.76`
  (`n = 3`, `m = 3`).
- Negative control: for `n = 3`, `m = 2` the weights `6, 8, 6` of the `H^{p,q}` are not equal; at
  `w = 0.35 - 0.52i` the weighted sum over `20` gives `ω_{6,2}(0.35) = -0.053`, while the unweighted
  average of the `R^1_{p,2-p}(w)` is `-0.06882`.

## Downstream consumers

- The roadmap on Euclidean motion groups and Bessel functions of the same project, for the
  Funk–Hecke formula (4.3) applied to plane waves and the Gegenbauer polynomials in the matrix
  elements of `M(n)`.
- The roadmap on rank-one symmetric spaces of the same project, for the compact duals `S^{n-1}`
  and `S^{2n-1}` and their spherical functions (4.4, 6.5).

## Beyond this roadmap (a roadmap for a roadmap; do not implement)

The following material lies outside this roadmap. It is recorded only to fix the boundary.
Contributors should not attempt it under this roadmap.

- **Koornwinder's addition formula for disk polynomials** (Vilenkin–Klimyk §11.4.5 (28), p. 345,
  with erratum E11.4.10 of the project's errata file) and the product formula of disk
  polynomials; they need the branching of `U(n) ↓ U(n - 1)` in full, not only its dimension.
- **Spherical harmonics on hyperboloids** and the representations of `SO₀(n - 1, 1)` and
  `U(n - 1, 1)` of class one (Vilenkin–Klimyk §§9.2.9–9.2.10 and Chapter 10); Gegenbauer and
  Jacobi functions of complex degree.
- **Quaternionic spheres** `Sp(n)/Sp(n - 1)` and the remaining compact rank-one spaces.
- **Stiefel and Grassmann manifolds** and the zonal polynomials of several variables.
- **Gel'fand–Tsetlin bases of `U(n)`** beyond the class-one representations and the full
  Gel'fand–Tsetlin formulas (ClassicalGroups Layer 6).

## Prior formalization

[lean-SFVK](https://github.com/bjbraams/lean-SFVK) (Apache-2.0) is the same author's project on
special functions and group representations. Its modules `SFVK/Spheres/Basic/Sphere.lean`,
`SFVK/Spheres/Basic/Zonal.lean` and `SFVK/Spheres/Basic/Disk.lean` (collected by
`SFVK/Spheres/Basic.lean`) define, without `sorry`, the objects of this roadmap (with its own names
for the matrix groups, their actions and the stabilizers) and prove their elementary special values;
its modules `SFVK/Spheres/SphereMeasure.lean`, `SFVK/Spheres/Zonal.lean`,
`SFVK/Spheres/Addition.lean`, `SFVK/Spheres/Branching.lean` and `SFVK/Spheres/Unitary.lean`
(collected by `SFVK/Spheres.lean`) state the theorems of Layers 1, 2–3, 4, 5 and 6 under
Mathlib-style names, and relate `zonalPolynomial` and `diskPolynomial` to the Gegenbauer, Legendre
and Jacobi polynomials of lean-DLMF, which also proves the Gegenbauer addition theorem of 4.5. This
roadmap specifies the mathematics intrinsically; lean-SFVK supplies implementation references, and
reused code carries attribution under the repository's porting guidance.

## References

- J. Dieudonné, *Special Functions and Linear Representations of Lie Groups*, CBMS Regional
  Conference Series in Mathematics 42, AMS, 1980, §7.
- A. U. Klimyk and N. Ya. Vilenkin, *Representations of Lie Groups and Special Functions*, in
  A. A. Kirillov (ed.), *Representation Theory and Noncommutative Harmonic Analysis II*,
  Encyclopaedia of Mathematical Sciences 59, Springer, 1995, Part II, Chapter 2, §§2.4, 2.8 and
  Chapter 3, §§1.3, 1.10.
- N. Ja. Vilenkin and A. U. Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2,
  Mathematics and Its Applications (Soviet Series) 74, Kluwer, 1993, Chapters 9–11.
- A. Wawrzyńczyk, *Group Representations and Special Functions*, Mathematics and Its Applications
  (East European Series), Reidel / PWN, 1984, Chapter 9.
- NIST Digital Library of Mathematical Functions, §§18.3, 18.5 (Gegenbauer and Jacobi
  normalizations), cited through LaguerreJacobi.
