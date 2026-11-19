# Roadmap plans: special functions and group representations

This file plans a family of Tau Ceti roadmaps that develop the theory linking group
representations to special functions, following Vilenkin and Klimyk and the other references
synopsized in this project. The roadmaps are to be written under the rules of the Tau Ceti roadmap
repository ([CONTRIBUTING](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/CONTRIBUTING.md)
and the README checklist "Writing a roadmap"): every milestone rests on Mathlib, Tau Ceti, earlier
material in the same roadmap, or a cited roadmap; nothing is optional; conventions are pinned; the
markdown is definitive and `Suggested.lean` gives suggested forms.

The focus is on special functions. General representation theory is developed only as far as the
special-function results need it.

## 1. Position in the Tau Ceti landscape

**Suppliers of the special functions (Track A).** The functions themselves are specified by
special-function roadmaps. On Tau Ceti main (checked 2026-11-19): the Gauss hypergeometric
function (SpecialFunctionsHypergeometric), the generalized hypergeometric and Appell functions,
parabolic cylinder functions, Airy functions, the exponential, error and incomplete Gamma
functions, Bessel functions (SpecialFunctionsBessel), the general theory of orthogonal polynomials
(SpecialFunctionsOrthogonalPolynomialsGeneral) and the Laguerre and Jacobi polynomials
(LaguerreJacobi). In review: Gamma (DLMF 5), confluent hypergeometric and Whittaker functions
(DLMF 13) and Legendre functions (DLMF 14). A roadmap for 3j, 6j and 9j symbols (DLMF 34) is
planned. No roadmap supplies the Krawtchouk polynomials; Roadmap 1 owns them. The roadmaps below
consume these functions with DLMF normalizations and do not define them. lean-DLMF is a cited
source for the suppliers, not the ground of these roadmaps.

**Representation theory.** Tau Ceti's representation-theory family covers finite and compact
groups (Peter–Weyl, characters, the SU(2) engine), Lie groups and the Lie correspondence (with the
Cartan, Iwasawa and KAK decompositions), highest weights and the classical groups. It explicitly
excludes infinite-dimensional unitary representations of noncompact groups and Plancherel theory,
and welcomes roadmaps for that material separately. The family planned here consumes the compact
and Lie-group material and supplies the concrete noncompact models that the special functions
need, without attempting a general unitary theory of noncompact groups.

**Noncompact material already on main.** Two roadmaps on Tau Ceti main own part of the
noncompact theory, and the family consumes whatever they own rather than restating it (one owner
per result; a concrete model of ours enters through an agreement theorem with the parameter map):
- NoncompactQuantumSymmetry: derived representations and Stone generators (M0), the Mackey
  machine for regular semidirect products (M2, which covers the classification for the ax+b group
  and the motion groups), and for SL(2,ℝ) ≅ SU(1,1) the principal, complementary and discrete
  series with their irreducibility, equivalences and exhaustion and the Plancherel theorem (M4,
  M4.P).
- RepresentationTheory/SmoothBanachRepresentations: smooth vectors and the derived Lie-algebra
  action (with AutomorphicFormsOnReductiveGroups §2.7). The RepresentationTheory family index on
  main does not list this roadmap, although it sits in the family directory.

**Proposed family.** An index roadmap "Special functions and group representations", with
arXiv topic `math.CA` (the main results are special-function identities), whose sub-roadmaps are
listed in §4–§6.

## 2. What Mathlib and Tau Ceti already contain

Baseline: Mathlib `1b1ccf4b` (2026-11-02) and Tau Ceti `396c3bd9` (2026-11-12), the revisions
pinned in `lakefile.toml`. Tau Ceti changes quickly; recheck against its current main before a
roadmap is written.

### 2.1 Present

**Groups.**

- GL(n), SL(n), U(n), SU(n), O(n), SO(n) as matrix groups. Mathlib `LinearAlgebra/UnitaryGroup`, `Matrix.SpecialLinearGroup`, `Matrix.GeneralLinearGroup`.
- Compactness and topological-group structure of unitary groups. Tau Ceti `Topology/Algebra/UnitaryGroup`.
- SU(2) → SO(3) double cover; conjugacy classes of SU(2); simplicity of SO(3). Tau Ceti `RepresentationTheory/SU2/{Adjoint,ConjugacyClasses,NormalSubgroup}`.
- Heisenberg group over a ring (algebraic), `HeisenbergGroup`. Tau Ceti `GroupTheory/SpecificGroups/Heisenberg`.
- Affine isometries as translations ⋊ linear isometries (algebraic). Tau Ceti `Analysis/Normed/Affine/Isometry/SemidirectProduct`.
- SL(2,ℝ) acting on the upper half-plane. Mathlib `Analysis/Complex/UpperHalfPlane/MoebiusAction`.
- Matrix exponential lines in SO, SU, SL, Sp; smooth Iwasawa decomposition of GL(n). Tau Ceti `Geometry/Lie/Exponential/Matrix/*`, `Geometry/Lie/Iwasawa`.

**Representations.**

- Algebraic representations; `ContRepresentation`. Mathlib `RepresentationTheory/Basic`, `RepresentationTheory/Continuous/Basic`.
- Strongly continuous and unitary representations, Hilbert sums, Schur's lemma, intertwiners, tensor products, restriction, coinduction on C(G,V). Tau Ceti `RepresentationTheory/Continuous/**`.
- One-parameter unitary groups and their Stone generator. Tau Ceti `RepresentationTheory/Continuous/Unitary/OneParameter`.
- `toStronglyContinuousGroup`; `Measure.leftRegular` with its unitarity and strong continuity; `posSemidef_inv_mul_iff_exists_isUnitary` and `IsUnitary.posSemidef_inner_map_inv_mul` (positive definiteness of matrix coefficients). Tau Ceti `RepresentationTheory/Continuous/**`.
- Left regular representation on Lᵖ(G,E) for a left-invariant measure; regular representations of compact groups on L². Tau Ceti `Continuous/LeftRegular/Basic`, `Compact/RegularRepresentation`.
- Representations on functions on a G-set (algebraic). Tau Ceti `RepresentationTheory/FunLeft`.

**Matrix coefficients.**

- g ↦ ⟪π g v, w⟫, sesquilinearity, the product identity; L² classes for compact G. Tau Ceti `Continuous/MatrixCoefficient`, `Compact/MatrixCoefficient`.

**Compact groups.**

- Haar averaging, unitarizability, Schur orthogonality, Peter–Weyl, characters, Frobenius–Schur, the circle group. Tau Ceti `RepresentationTheory/Compact/**`.

**SU(2).**

- Sym^d ℂ² with weight basis; irreducibility, inequivalence, exhaustion; characters; Weyl group; Weyl integration and character orthonormality; 𝔰𝔲(2) in the basis −iσₐ/2; differential of Sym^d; holomorphic extension to SL₂(ℂ), GL₂(ℂ). Tau Ceti `RepresentationTheory/SU2/**`.

**Lie algebras.**

- sl, so, sp, skew-adjoint algebras; Lie algebra of a Lie group (left-invariant derivations); sl₂-triples. Mathlib `Algebra/Lie/{Classical,SkewAdjoint,Sl2}`, `Geometry/Manifold/GroupLieAlgebra`.
- Lie functor; fundamental vector fields; differentials of rational GL(n) representations; Casimir operators (algebraic). Tau Ceti `Geometry/Lie/{Functor,FundamentalVectorField}`, `ClassicalGroups/Differential`, `Algebra/Lie/HighestWeight/*`.
- Highest weights, branching, Weyl dimension formulas, Gel'fand–Tsetlin bases of GL(n) modules. Tau Ceti `RepresentationTheory/ClassicalGroups/**`.

**Measures.**

- Sphere surface measure `toSphere`; quotient measures for discrete subgroups. Mathlib `MeasureTheory/Constructions/HaarToSphere`, `MeasureTheory/Measure/Haar/Quotient`.
- Uniform law on the sphere; O(n+1) fibred over Sⁿ with its measure. Tau Ceti `Probability/Distributions/Uniform/Sphere`, `Geometry/Euclidean/Volume/OrthogonalGroup`.

### 2.2 Absent

1. Coordinates: Euler angles on SU(2), SO(3) and SU(1,1), and Haar measure in these coordinates.
   The Weyl integration formula covers class functions only.
2. Groups: SU(1,1) and SO(2,1); the ax+b group; Vilenkin–Klimyk's group of third-order triangular
   matrices; the oscillator group; topological, Haar and Lie structure on ISO(2), ISO(1,1), M(n)
   and the Heisenberg group. No group type for M(n), ISO(2) or ISO(1,1) exists in Mathlib or Tau
   Ceti (Tau Ceti's affine-isometry semidirect product is algebraic only); Roadmap 2 owns them as
   topological groups.
3. Representations on L²(X, μ) of a G-space X: the quasi-regular representation for invariant and
   quasi-invariant μ; multiplier representations from a cocycle; concrete induced models of
   noncompact groups (ISO(2) on L²(S¹), principal series of SU(1,1), Schrödinger model of the
   Heisenberg group).
4. Matrix elements with respect to an orthonormal basis in the Vilenkin–Klimyk convention, the
   addition theorem as a convergent series in infinite dimension, and the unitarity relations.
5. The derived Lie-algebra action on an invariant dense core, infinitesimal operators as
   differential operators, the Casimir operator as a differential operator, and the template
   theorems "matrix elements satisfy the Casimir equation" and "raising and lowering operators give
   recurrences".
6. K-finite vectors and the isotypic decomposition under a circle subgroup for unitary
   representations of noncompact groups.
7. Gel'fand pairs and zonal spherical functions: the bi-K-invariant convolution algebra,
   Gel'fand's criterion, the functional equation, positive definiteness, eigenfunctions of
   invariant differential operators, the spherical transform.
8. Spherical harmonics.

## 3. Conventions for the whole family

- Groups act on the left; a representation is a homomorphism into the operators (Mathlib's
  `Representation`, `ContRepresentation`). A right action x ↦ xg of a source is converted by
  g ↦ g⁻¹.
- Inner products are conjugate-linear in the first argument (Mathlib). The matrix element is
  D_{m'm}(g) = ⟪e_{m'}, T(g) e_m⟫. Tau Ceti's matrix coefficient g ↦ ⟪π g v, w⟫
  (`ContRepresentation.matrixCoeff`) requires continuity of π in the operator-norm topology, which
  fails for every infinite-dimensional model of a nondiscrete group (already for the left regular
  representation). Roadmap 2 therefore defines the matrix element directly for a strongly
  continuous unitary representation and a Hilbert basis, with a bridge theorem: where π is norm
  continuous, the matrix element is the complex conjugate of Tau Ceti's coefficient at
  (v, w) = (e_m, e_{m'}). Roadmap 1's SU(2) matrix element is its instance.
- Haar measure on a compact group has total mass 1. On a noncompact group the normalization is
  fixed in each roadmap and stated in coordinates.
- Euler angles follow Edmonds, *Angular Momentum in Quantum Mechanics* (author's decision,
  2026-11-19). On SU(2), g = k_α b_β k_γ with k_α = diag(e^{iα/2}, e^{−iα/2}) and the real middle
  factor b_β = [[cos β/2, sin β/2], [−sin β/2, cos β/2]] (Edmonds's exp(iαJ_z) exp(iβJ_y)
  exp(iγJ_z) at spin 1/2); weights satisfy T(k_α) e_m = e^{imα} e_m, and
  D^j_{m'm}(k_α b_β k_γ) = e^{im'α} d^j_{m'm}(β) e^{imγ} exactly as Edmonds prints it, with d^j
  real. On SU(1,1) the middle factor is the boost b_t = [[cosh t/2, sinh t/2],
  [sinh t/2, cosh t/2]] (letter t, since τ is the principal-series parameter), with the same
  letters, order and weight sign. Haar measure: (16π²)⁻¹ sin β dα dβ dγ on SU(2) (total mass 1)
  and Vilenkin–Klimyk's (8π²)⁻¹ sinh t dα dt dγ on SU(1,1), which differs by a factor 2 from the
  formal continuation of the SU(2) density. Vilenkin–Klimyk's Euler-angle convention (middle
  factor a rotation about the x-axis, which brings a factor i^{m−n}) enters each roadmap through
  one stated conversion theorem; for SU(2), u^{VK}(φ, θ, ψ) = k_{φ+π/2} b_θ k_{ψ−π/2} and
  t^{VK}_{mn} = D_{−m,−n}. The general KAK decomposition belongs to the Lie-groups roadmap; Euler
  angles are stated as its instance where that roadmap provides it.
- Special functions carry DLMF normalizations, as supplied by Track A. Where a source uses another
  normalization the conversion is a stated theorem. Edmonds's spherical harmonics Y_lm equal DLMF's
  Y_l^m (14.30.1); his associated Legendre functions lack the Condon–Shortley factor (−1)^m of
  DLMF's Ferrers functions.
- Spherical functions of a Gel'fand pair are defined without a boundedness requirement
  (continuous, φ(e) = 1, the functional equation), as in Wawrzyńczyk, Helgason and Faraut; the
  bounded ones are characterized as the characters of the bi-K-invariant L¹ algebra, and the
  positive-definite ones as those of unitary representations with a K-fixed vector.
- Statements follow the corrected forms in this project's ERRATA files, not the printed ones.

## 4. Roadmap 1: matrix elements of SU(2) and SO(3), Jacobi and Legendre functions

**Scope.** The matrix elements of the irreducible representations of SU(2) and SO(3), their
expression through Jacobi polynomials, Legendre polynomials and associated Legendre functions, the
identities that follow from the group structure, and harmonic analysis on SU(2) and S². It
includes the pieces of the general infrastructure that this case needs (coordinates, matrix
elements in an orthonormal basis, the Lie-algebra action on the polynomial model, the Gel'fand
pair (SO(3), SO(2))).

**Excluded, with owner.** Tensor products and Clebsch–Gordan coefficients (Roadmap 3); SU(1,1)
and Jacobi functions of non-integral degree (Roadmap 7); SO(n) for n > 3 (Roadmap 5); the general
infrastructure for noncompact groups (Roadmap 2).

**Inputs.** Tau Ceti's SU(2) development (Sym^d models, weight basis, irreducibility and
exhaustion, characters, Weyl integration, 𝔰𝔲(2) and the differential of Sym^d) and compact-group
development (Haar measure, Schur orthogonality, Peter–Weyl); Mathlib's Chebyshev polynomials and
Lie algebras; LaguerreJacobi and SpecialFunctionsOrthogonalPolynomialsGeneral (Jacobi polynomials
with their orthogonality, recurrences, Rodrigues formulas and generating functions as supplier
facts; Legendre polynomials through Mathlib; no supplier for the Krawtchouk polynomials, which this
roadmap owns),
the DLMF 14 roadmap (associated Legendre functions on (−1, 1)) and the DLMF 15 roadmap (the Gauss
function, for the hypergeometric forms).

**Sources.** Edmonds Chs. 1–4 (the convention: §1.3, §§4.1–4.2); VK06 §§6.1–6.3, 6.6–6.10 (in
VK's convention, through the conversion theorem); KV02 §§1–2; KV03; Wawrzyńczyk Chapter 8
(§§8.1–8.6); Dieudonné §2 and §7; Miller 1968 §§2-3–2-4; Miller 2010 Chapter 2.

### Layer 1.0: coordinates and the unitary models

- Euler angles on SU(2) and SO(3) in Edmonds's convention (§3): existence and uniqueness of
  (α, β, γ) on the open dense set 0 < β < π with the ranges 0 ≤ α < 2π, −2π ≤ γ < 2π (for SO(3),
  0 ≤ γ < 2π); the exceptional sets β ∈ {0, π}; compatibility with the double cover.
- Haar measure in Euler angles: for integrable f,
  ∫_{SU(2)} f = (16π²)⁻¹ ∫ f(α, β, γ) sin β dα dβ dγ over the fixed ranges (and the SO(3)
  analogue with its normalization), proved from uniqueness of Haar measure. The class-function
  case agrees with Tau Ceti's Weyl integration formula.
- The invariant inner product on Sym^{2l} ℂ², and the orthonormal basis of normalized monomials
  z₁^{l+m} z₂^{l−m}/√((l+m)!(l−m)!), m = −l, …, l. Tau Ceti's model `symPowerModel` is not
  unitary for 2l ≥ 2; the unitary model is its transport by e_i ↦ √(i!(2l−i)!) e_i, and its basis
  is Tau Ceti's weight basis up to positive scalars, in the same order (m = i − l).
- The representation of SO(3) for integral l, through the double cover.

### Layer 1.1: matrix elements and their closed forms

- D^l_{m'm}(g) in the convention of §3, and its factorization in Euler angles,
  D^l_{m'm}(α, β, γ) = e^{im'α} d^l_{m'm}(β) e^{imγ}, valid for all real angles. (In
  Vilenkin–Klimyk's convention the corresponding formula is
  t^l_mn(φ, θ, ψ) = i^{m−n} e^{−i(mφ + nψ)} P^l_mn(cos θ); the factor i^{m−n} is needed already at
  l = 1/2, and it comes from their x-axis middle factor.)
- Edmonds's finite-sum formula for d^l_{m'm} (4.1.15), and its expression through Jacobi
  polynomials P_k^{(a,b)} with k = l − max(|m'|, |m|), a = |m' − m|, b = |m' + m|, with a real
  sign and no power of i.
- Special cases: P^l_00 = P_l (Legendre polynomials); P^l_m0 and associated Legendre functions
  P_l^m; the Gegenbauer form where it applies.
- Symmetries: t^l_mn(g⁻¹) = conj t^l_nm(g); the index symmetries P^l_mn = P^l_nm = P^l_{−m,−n}
  up to the stated signs; values at θ = 0 and θ = π.
- Hypergeometric forms of P^l_mn through the Gauss function at the arguments used in VK06.

### Layer 1.2: identities from the group law

- Addition theorem: t^l_mn(g₁g₂) = Σ_k t^l_mk(g₁) t^l_kn(g₂), and in Euler angles the addition
  theorems for P^l_mn, Jacobi and Legendre polynomials (VK06 §6.6); the Legendre addition
  theorem P_l(cos θ₁ cos θ₂ − sin θ₁ sin θ₂ cos φ) = Σ_m … as a special case.
- Unitarity relations Σ_k conj t^l_km(g) t^l_kn(g) = δ_mn and their Jacobi-polynomial forms.
- Product (multiplication) formulas from integration over the torus (VK06 §6.6, Wawrzyńczyk §8.3).
- Orthogonality of P^l_mn in L²([0, π], sin θ dθ) for fixed (m, n), derived from Schur
  orthogonality and the Euler-angle Haar formula; the resulting proof of Jacobi orthogonality for
  the integral parameters (α, β) that occur, checked against the DLMF 18 supplier.
- Peter–Weyl in coordinates: the functions √(2l+1) t^l_mn are a Hilbert basis of L²(SU(2)); the
  Fourier expansion of functions on SU(2) and its Plancherel identity (VK06 §6.10).

### Layer 1.3: the Lie-algebra action and its consequences

- The action of 𝔰𝔲(2) and of its complexification on the polynomial model as first-order
  differential operators; raising and lowering operators J₊, J₋, J₃ and their action on e_m^l.
- The infinitesimal operators of the right and left regular representations on C^∞(SU(2)) in
  Euler angles, and the Casimir operator (the Laplacian of SU(2)) as an explicit second-order
  differential operator in (α, β, γ) on the chart 0 < β < π, stated in Lean: it is the Casimir of
  both regular representations, each D^l_{m'm} is an eigenfunction with eigenvalue −l(l + 1), and
  on functions independent of γ it is the Laplace–Beltrami operator of S².
- Consequences: the differential equation of P^l_mn (the Jacobi equation in the stated
  variables), the recurrence relations of VK06 §6.7 and Wawrzyńczyk §8.4, obtained from raising
  and lowering operators.
- Generating functions of VK06 §6.7, from the polynomial model.

### Layer 1.4: the sphere S² and spherical harmonics

- SO(3) acting on S² with the rotation-invariant probability measure; S² ≅ SO(3)/SO(2).
- The quasi-regular representation of SO(3) on L²(S²); the spherical harmonics Y_l^m as the
  functions √(2l+1) conj t^l_{m0} (or the convention fixed in the roadmap) composed with the
  orbit map; their orthonormality and completeness; the decomposition L²(S²) = ⊕_l H_l with H_l
  irreducible of dimension 2l + 1.
- The Gel'fand pair (SO(3), SO(2)): the bi-SO(2)-invariant integrable functions form a commutative
  convolution algebra; the zonal spherical functions are the Legendre polynomials P_l(cos θ); the
  functional equation; the addition theorem for spherical harmonics
  Σ_m Y_l^m(x) conj Y_l^m(y) = (2l + 1)(4π)⁻¹ P_l(x · y) in the surface-measure normalization.
- The Laplace–Beltrami operator on S² as the Casimir operator, with eigenvalue −l(l + 1) on H_l.

### Layer 1.5: characters and functions of the column index

- Characters as Chebyshev polynomials of the second kind, χ_l(θ) = U_{2l}(cos(θ/2)), linking Tau
  Ceti's torus character formula to Mathlib's Chebyshev polynomials (VK06 §6.9), and the
  character expansions of class functions.
- Matrix elements as functions of the column index: the Krawtchouk polynomials (owned here, for
  lack of a supplier) and their orthogonality from the unitarity relations (VK06 §6.8).

### Acceptance examples

- l = 1/2 and l = 1: the explicit 2 × 2 and 3 × 3 matrices t^l(φ, θ, ψ).
- D^1_00 = d^1_00(β) = cos β; d^l_00(β) = P_l(cos β) for l ≤ 3 by direct expansion; the j = 1/2
  and j = 1 matrices agree with Edmonds's printed ones.
- The Legendre addition theorem at l = 1 is the spherical law of cosines.
- The Euler-angle Haar formula integrates the constant 1 to 1, and |t^1_00|² to 1/3.

## 5. Roadmap 2: function-space models of noncompact groups

**Scope.** The general infrastructure for concrete representations of the noncompact groups that
occur in the special-function theory: the groups with their topology, Haar measure and
coordinates; representations on L² of G-spaces; matrix elements in orthonormal bases in infinite
dimension; infinitesimal operators on an invariant core; K-finite vectors; Gel'fand pairs with
compact K. It contains the general forms of the items that Roadmap 1 builds for SU(2) and SO(3).

**Excluded, with owner.** The identification of specific matrix elements with special functions
(Roadmaps 4, 6, 7, 8); the decomposition of specific quasi-regular representations and the
corresponding integral transforms (the same roadmaps); the Mackey machine for regular semidirect
products, the classification of the irreducible representations of SL(2,ℝ) ≅ SU(1,1) and its
Plancherel theorem (NoncompactQuantumSymmetry M2, M4, M4.P, consumed); derived representations,
smooth vectors and the agreement of derived operators with Stone generators
(NoncompactQuantumSymmetry M0, SmoothBanachRepresentations, AutomorphicFormsOnReductiveGroups
§2.7, consumed); general Mackey
theory, the imprimitivity theorem, abstract Plancherel theory and Harish-Chandra theory (not in
this family).

**Inputs.** Tau Ceti's continuous and unitary representations (strong continuity, Hilbert sums,
Stone generator, coinduction), compact-group development (for K), Lie-group development
(exponential map, fundamental vector fields, the Lie functor); Mathlib's Haar measure, quotient
measures, Radon–Nikodym derivatives, Lᵖ spaces and Fourier analysis on the circle.

**Sources.** VK01, VK02 §§2.1–2.3; KV01 §§1–2; Wawrzyńczyk Chapters 1–3 and 5; Dieudonné §§4–5 and
§8; Miller 1968 §§1-1–1-4, 3-6–3-7.

### Layer 2.0: the groups

- SU(1,1), with its isomorphism to SL(2,ℝ) by the Cayley transform; ISO(2) = ℝ² ⋊ SO(2);
  ISO(1,1); M(n) = ℝⁿ ⋊ SO(n) (owned here as topological groups: no group type exists in Mathlib
  or Tau Ceti); the ax+b group; the Heisenberg group over ℝ; the oscillator group; the group of
  third-order real triangular matrices of VK05.
- For each: topological-group structure, local compactness, a coordinate system, Haar measure in
  coordinates, the modular function (unimodularity where it holds), and the Lie algebra in a
  stated basis.
- Coordinate decompositions used later: the polar decomposition of ISO(2) and M(n); the Euler-type
  decomposition of SU(1,1) in the convention of §3 (middle factor a boost b_t), cited as an
  instance of the KAK decomposition of the Lie-groups roadmap.

### Layer 2.1: G-spaces and quasi-invariant measures

- A measurable G-action on X with a quasi-invariant σ-finite measure μ; the Radon–Nikodym cocycle
  ρ(g, x) = d(g⁻¹·μ)/dμ (x) and its cocycle identity.
- Invariant measures on G/K for compact K by pushforward of Haar measure; uniqueness up to scalar.
- Examples fixed for later use: ℝ² and S¹ under ISO(2); the unit circle and the unit disc under
  SU(1,1) (quasi-invariant, with ρ explicit); the upper half-plane under SL(2,ℝ); ℝ under ax+b.

### Layer 2.2: quasi-regular and multiplier representations

- The quasi-regular representation (π(g)f)(x) = ρ(g, x)^{1/2} f(g⁻¹x) on L²(X, μ): a
  representation, unitary, strongly continuous.
- Multiplier representations (T(g)f)(x) = α(g, x) f(g⁻¹x) for a measurable cocycle α; the cocycle
  condition is equivalent to the representation property; unitarity criterion |α(g, x)|² =
  ρ(g, x); equivalence of representations whose cocycles differ by a coboundary.
- Representations on spaces of smooth or polynomial functions by the same formulas, with the
  continuity properties stated for each space.

### Layer 2.3: concrete induced models

- The representations of ISO(2) and M(n) on L²(S^{n−1}) indexed by R > 0, as multiplier
  representations; their unitarity and strong continuity; irreducibility for ISO(2).
- The principal-series and complementary-series representations of SU(1,1) on functions on the
  circle as multiplier representations, with the parameter ranges for unitarity; the discrete
  series on holomorphic function spaces on the disc, with their reproducing kernels.
- The irreducible unitary representations of the ax+b group on L²(ℝ₊).
- The Schrödinger representation of the Heisenberg group on L²(ℝ), unitary and irreducible.
- What NoncompactQuantumSymmetry owns is consumed, and this roadmap adds only its concrete models
  with agreement theorems (the item-by-item table is in Roadmap 2's notes):
  - principal series: irreducibility, the equivalence τ ↔ −τ − 1 and the splitting at the
    reducible point are M4's; the circle model is M4's compact picture under the identification of
    SL(2,ℝ) with SU(1,1), with parameter ν = −(2τ + 1);
  - complementary series: the invariant form and the completion are M4's; this roadmap keeps the
    positivity of its weights and their match with M5's eigenvalues;
  - holomorphic and antiholomorphic discrete series: the disc models are this roadmap's, matched
    with M4's D_k^± (NQS weight n is 2m here); irreducibility and the half-plane models (M6.C) are
    consumed;
  - Casimir values and K-types: a stated dictionary (NQS's Casimir is minus ours);
  - Plancherel (M4.P): consumed, not restated;
  - Schrödinger representation: irreducibility from M2, with the Fourier transform intertwining
    the line model and M2's model;
  - sphere models of M(2), M(3): pulled back from NQS's Euclidean adapters (M6, M4.TypeI), with
    irreducibility consumed; for n ≥ 4 irreducibility is this roadmap's.
  The ax+b models and Gel'fand pairs have no counterpart in NoncompactQuantumSymmetry and are
  owned here. The classification for the ax+b group is NoncompactQuantumSymmetry M2's; the
  irreducibility of the half-line models is proved directly.

### Layer 2.4: matrix elements in infinite dimension

- Matrix elements t_mn(g) for a unitary representation and an orthonormal basis (e_m), in the
  convention of §3, as an interface over Tau Ceti's matrix coefficient.
- The addition theorem t_mn(g₁g₂) = Σ_k t_mk(g₁) t_kn(g₂) with absolute convergence, from the
  Parseval identity; the unitarity relations; behaviour under change of orthonormal basis.
- Weight bases: for a circle subgroup K, the K-isotypic decomposition of a unitary
  representation as a Hilbert sum, K-finite vectors and their density, and the form of matrix
  elements between weight vectors (t_mn(k₁ g k₂) = e^{−imφ₁} t_mn(g) e^{−inφ₂}).

### Layer 2.5: infinitesimal operators

- The derived operator dπ(A) on smooth vectors, its agreement with the Stone generator and the
  Lie-algebra homomorphism property are consumed (NoncompactQuantumSymmetry M0,
  SmoothBanachRepresentations, AutomorphicFormsOnReductiveGroups §2.7); this roadmap restricts them
  to explicit cores (trigonometric polynomials, C_c^∞ functions) of its models.
- For the representations of Layers 2.2–2.3: dπ(A) as a differential operator, computed from the
  fundamental vector fields of the action and the derivative of the cocycle.
- The Casimir element acting on D; its value on irreducible models where it is scalar.
- Template theorems: if T is irreducible with scalar Casimir c, the matrix elements between weight
  vectors satisfy the second-order ordinary differential equation obtained from the Casimir in the
  coordinates of Layer 2.0; raising and lowering operators give three-term relations between
  matrix elements of adjacent weights.

### Layer 2.6: Gel'fand pairs with compact K

- For a locally compact unimodular G and compact K: the convolution algebra of bi-K-invariant
  integrable functions; Gel'fand's criterion (an involutive anti-automorphism fixing every double
  coset implies commutativity).
- Spherical functions: definition through the functional equation ∫_K φ(x k y) dk = φ(x) φ(y),
  without a boundedness requirement (§3); the bounded ones are exactly the characters of the
  bi-K-invariant L¹ algebra (an unbounded spherical function of (SU(1,1), K) shows the
  distinction); for a unitary
  representation with a K-fixed unit vector v, the spherical function g ↦ ⟪v, π(g) v⟫ and its
  positive definiteness.
- Spherical functions as joint eigenfunctions of the G-invariant differential operators on G/K
  (for G a Lie group), stated for the operators constructed in Layer 2.5.
- The spherical transform of bi-K-invariant functions and its multiplicativity on convolution.

### Acceptance examples

- The ax+b group is not unimodular; its modular function in the coordinates of Layer 2.0.
- ISO(2) and SU(1,1) are unimodular, with Haar measures written in coordinates.
- The unitarity range of the SU(1,1) multiplier representations on the circle.
- (ISO(2), SO(2)) satisfies Gel'fand's criterion; so does (SO(3), SO(2)), recovering Roadmap 1.4.

## 6. The further roadmaps

These are indicated approximately; each will be written in the form of §§4–5 once its inputs are
in place.

**Roadmap 3. Clebsch–Gordan and Racah theory for SU(2).** Tensor products of the representations
of Roadmap 1; Clebsch–Gordan coefficients, 3j and 6j symbols, their orthogonality and symmetries;
Hahn and Racah polynomials and other discrete orthogonal polynomials through the coupling
coefficients. Inputs: Roadmap 1, the DLMF 34 roadmap, DLMF 18 (discrete polynomials). Sources:
VK08, KV06, Wawrzyńczyk §8.7.

**Roadmap 4. Euclidean motion groups and Bessel functions.** The ISO(2) representations of
Roadmap 2 with matrix elements i^{n−m} J_{m−n}(R r) e^{…}; the Jacobi–Anger expansion; the Graf
and Gegenbauer addition theorems; Neumann series; ISO(1,1) with Macdonald and Hankel functions;
plane-wave expansions in ℝⁿ; the Hankel transform from the decomposition of the quasi-regular
representation; the contraction SO(3) → ISO(2) and the limit of Legendre functions to Bessel
functions (Mehler–Heine). Inputs: Roadmaps 1–2, DLMF 10. Sources: VK04, KV05, Miller 1968 §§3-1–3-10,
Wawrzyńczyk Chapter 7, Dieudonné §16, Miller 1977 Chapter 1.

**Roadmap 5. Spheres in higher dimension: SO(n) and U(n).** Gegenbauer polynomials as zonal
spherical functions of (SO(n), SO(n−1)); spherical harmonics on S^{n−1}, their dimension and the
decomposition of L²(S^{n−1}); the addition theorem and the Funk–Hecke formula; disk polynomials
for (U(n), U(n−1)); Gel'fand–Tsetlin bases where Tau Ceti's classical-group development supplies
them. Inputs: Roadmaps 1–2, DLMF 18, Tau Ceti's classical groups. Sources: VK09–VK11, Wawrzyńczyk
Chapter 9.

**Roadmap 6. Affine, triangular and Heisenberg groups.** The ax+b group with the Gamma and Beta
functions and the Mellin transform; the triangular group of VK05 with confluent hypergeometric and
Whittaker functions; the Heisenberg and oscillator groups in the Schrödinger and Bargmann–Fock
models with Hermite and Laguerre functions, their addition and product formulas; Miller's
generating-function method for the oscillator algebra. Inputs: Roadmap 2, Tau Ceti's Hermite
basis, DLMF 5, 13, 18. Sources: VK03, VK05, VK12, Miller 1968 Chapter 4, Wawrzyńczyk Chapter 12.

**Roadmap 7. SU(1,1) and SL(2,ℝ).** Matrix elements of the principal, complementary and discrete
series as Jacobi functions, Legendre functions P^μ_ν and Gauss functions; addition theorems and
generating functions; mixed bases (VK07); the Mehler–Fock transform from the decomposition of the
quasi-regular representation on the disc. Irreducibility, equivalences, exhaustion and the
Plancherel theorem of the series are NoncompactQuantumSymmetry M4's and are consumed, not
re-proved; this roadmap must be scoped around the matrix elements and transforms.
Inputs: Roadmaps 1–2, NoncompactQuantumSymmetry M4, DLMF 14, 15. Sources: VK06 §§6.4–6.5, VK07,
Wawrzyńczyk Chapter 10, Dieudonné §14, Miller 1968 Chapter 5.

**Roadmap 8. Rank-one symmetric spaces.** Spherical functions on real hyperbolic spaces as Jacobi
functions; the rank-one Harish-Chandra c-function; the spherical (Jacobi) transform with its
inversion and Plancherel formulas in rank one; harmonic analysis on the hyperbolic plane and
three-space. Inputs: Roadmaps 2 and 7, the Lie-groups roadmap. Sources: Wawrzyńczyk Chapters 11 and
18, KV05, rank-one parts of Heckman–Schlichtkrull.

**Roadmap-for-a-roadmap (not to be implemented from this file).** Higher-rank spherical functions
and Heckman–Opdam hypergeometric functions (Heckman–Schlichtkrull Part I); special functions of
matrix argument (VK17); Gel'fand–Tsetlin bases in general (VK18); quantum groups and
q-orthogonal polynomials (VK14); modular forms, theta functions and affine Lie algebras (VK19);
discrete groups and functions of discrete argument (VK13); semisimple groups in general
(VK15–VK16).

**Miller's Lie-algebraic method** (local multiplier representations of Lie algebras, Weisner's
method, Miller 1968, Miller 1977) enters Roadmaps 1, 4, 6 and 7 as layers on generating functions
and recurrences rather than as a separate roadmap.

**References outside the focus.** Olver 1986, 1995 and 1999, Bluman–Kumei, Bluman–Cheviakov–Anco
and most of Xu 2017 concern symmetry methods for differential equations and classical invariant
theory. They are not sources for this family, except where separation of variables produces
special functions (Miller 1977) and Xu's path hypergeometric functions (Xu 2017 Chapter 15).

## 7. Order and coordination

- Roadmap 1 depends only on Tau Ceti's compact-group and SU(2) development and on Track A; it is
  the first to be written. Roadmap 2 is independent of Roadmap 1 and can be written in parallel.
- Roadmap 3 needs Roadmap 1; Roadmaps 4–6 need Roadmap 2 (and Roadmap 4 also Roadmap 1); Roadmap 7
  needs Roadmaps 1–2; Roadmap 8 needs Roadmap 7.
- Coordination points: the matrix-element convention of §3 with Tau Ceti's compact-group roadmap;
  the coordinate decompositions with the Lie-groups roadmap (Layer 9, KAK); spherical harmonics
  and the Laplacian with the PDE roadmap; the boundary statement of the representation-theory
  family (no general unitary theory of noncompact groups) with the Tau Ceti maintainers.
- Each roadmap is prototyped in `SFVK/` in this project, with `Suggested.lean` extracted from it,
  and cites the synopsis entries of this project only in a provenance section.
