# Special functions from group models: Euclidean motion groups and Bessel functions

**Summary.** This roadmap derives the theory of Bessel functions of integer order, and of the
Bessel functions that occur as zonal functions in higher dimension, from the representations of
the Euclidean and pseudo-Euclidean motion groups. The circle models `T_R` of the plane motion group
`M(2) = ℝ² ⋊ SO(2)` have the matrix elements `i^{n−m} e^{i(n−m)φ} e^{−inα} J_{n−m}(R r)`; the group
law then gives the addition theorem and the multiplication formula, the infinitesimal operators
give the recurrences and Bessel's equation, Miller's complexification `T₃` gives the generating
functions and Weisner's identity, the hyperbola model of `ISO(1,1)` gives the Macdonald kernel,
the decomposition of the quasi-regular representation of `M(2)` gives the Hankel transform with
its inversion and Plancherel formulas, the Gel'fand pair `(M(n), SO(n))` gives the zonal Bessel
functions `Γ(n/2) (2/z)^{n/2−1} J_{n/2−1}(z)` with their classification, and the contraction of
`SO(3)` and `SO(n + 1)` to the motion groups gives the limits of Wigner's `d`-functions and of
Gegenbauer polynomials to Bessel functions. The roadmap is a synthesis of several sources and
follows none of them in its organization: it is ordered by proof dependency, from the group in
coordinates, through the circle models and their matrix elements, to the identities that need
only the group law, the complexified group, the pseudo-Euclidean group, harmonic analysis on the
plane and on `ℝⁿ`, and the contractions. Its sources are Vilenkin–Klimyk (*Representation of Lie
Groups and Special Functions*, Vols. 1 and 2), Miller (*Lie Theory and Special Functions*),
Dieudonné (*Special Functions and Linear Representations of Lie Groups*) and, for the Euler-angle
conventions of the contraction, Edmonds (*Angular Momentum in Quantum Mechanics*), with the
Digital Library of Mathematical Functions for the identifications; each subsection cites several
of them by locator; see [References](#references).

Mathlib has `Complex.besselJ` with its power series, its parity in the argument for integer
order and `Complex.besselJ_neg_int`, the Fourier transform `𝓕` on inner product spaces, Fourier
series on `AddCircle` with `fourierBasis`, the surface measure `MeasureTheory.Measure.toSphere`,
the Laplacian `Δ`, `Matrix.specialOrthogonalGroup` and the complex Gamma function. Tau Ceti has
continuous representations with unitarity (`ContRepresentation.IsUnitary`). Neither has the
motion groups, any of their representations, Bessel's integral, the addition theorems, the Hankel
transform, the zonal functions of `ℝⁿ` or the contraction limits.

The roadmap covers:
- the plane motion group in polar coordinates (Layer 0);
- the circle models `T_R`, `R ∈ ℂ`, with their `L²` realization, unitarity range, irreducibility,
  matrix elements and infinitesimal operators (Layer 1);
- the addition theorem in polar form and the multiplication formula with its radial form
  (Layer 2);
- Miller's group `T₃` with its multiplier representation, matrix elements, addition theorem,
  Bessel form and Weisner's generating function (Layer 3);
- the hyperbola model of `ISO(1,1)` with its Laplace realization and Macdonald kernel (Layer 4);
- the quasi-regular representation of `M(n)` under the Fourier transform, cylindrical waves, the
  Hankel transform with inversion, Plancherel and Laguerre eigenfunctions, and the Fourier
  transform of radial functions on `ℝⁿ` (Layer 5);
- the Gel'fand pair `(M(n), SO(n))`: zonal Bessel functions, their classification, boundedness
  and radial equation, and the plane-wave expansion in `ℝ³` (Layer 6);
- the contraction limits `d^l_{pq}(x/l) → J_{p−q}(x)` and the zonal Gegenbauer limit (Layer 7).

## Scope and ownership

The roadmap is complete when Tau Ceti proves all of the following.

0. **The plane motion group in polar coordinates** (0.1).
1. **The circle models of `M(2)`** (1.1–1.3).
2. **Identities from the group law** (2.1–2.2).
3. **Miller's complex group `T₃`** (3.1–3.3).
4. **The pseudo-Euclidean motion group `ISO(1,1)`** (4.1–4.2).
5. **The quasi-regular representation and the Hankel transform** (5.1–5.3).
6. **The Gel'fand pair `(M(n), SO(n))`** (6.1–6.3).
7. **Contraction to the motion groups** (7.1–7.2).

The numbers are those of the layers below, and `k.n` names subsection `n` of Layer `k`.
`Suggested.lean` states the headlines that carry a Lean name, each with every conclusion the
README attaches to it; it is not an exhaustive acceptance test, and the other headlines and the
plain bullets of each subsection are targets of the same standing, stated in prose. The
`**Checks.**` and `### Examples` of each layer are statements to prove; they test the conventions
on explicit values.

**Boundaries.**
- SpecialFunctionsGroupModels, a roadmap of the same project, owns the groups `M(n)` and
  `ISO(1,1)` with their topology and Haar measures (its §0.3), the sphere models of `M(n)` for
  real `R > 0` with their representation law and unitarity (§2.6), matrix elements with the
  addition theorem and unitarity relations for any representation on a Hilbert space (§§3.1–3.2),
  the second-order equation of matrix elements (§4.3) and Gel'fand pairs, spherical functions
  and the spherical transform for compact `K` (§§5.1–5.2). This roadmap owns their instances on
  `M(2)` with complex `R`, the identification of the matrix elements with Bessel functions, and
  the spherical functions of `(M(n), SO(n))`.
- SpecialFunctionsSU2MatrixElements, a roadmap of the same project, owns Wigner's `d`-functions in
  Edmonds's convention (its §2.3), their Jacobi and Legendre forms (§§2.4, 2.6) and the spherical
  harmonics `Y_l^m` with their addition theorem (§§6.1, 6.3). Layer 7 and 6.3 consume them.
- [SpecialFunctionsBessel](../SpecialFunctionsBessel/README.md) owns the analytic theory of the
  cylinder functions for complex order: the generating function and the Jacobi–Anger expansions (its
  4.1), the multiplication theorem and the addition theorems of Neumann and Graf (4.2), Gegenbauer's
  addition theorem and the Gegenbauer plane-wave expansion 10.23.9 (4.3), the integral
  representations including the `cosh` integral of `K_ν` (5.1), the integrals of three Bessel
  functions (11.3) and the plane-wave expansion 10.60.7 (11.5). This roadmap owns the
  group-theoretic forms of these identities for integer order (2.1–2.2), states the agreement and
  does not restate the analytic versions. That roadmap's Beyond leaves the Hankel transform and the
  Fourier transform of radial functions in `ℝⁿ` with no planned roadmap, and assigns the
  Mehler–Heine limits to the orthogonal-polynomial and Legendre roadmaps, none of which owns them;
  this roadmap owns the Hankel transform for real order `ν > −1` (5.2), the radial Fourier transform
  (5.3), and the two contraction limits of Layer 7, which are the integer-parameter cases of DLMF
  18.11.5. The general Mehler–Heine formula for Jacobi polynomials stays with the
  orthogonal-polynomial roadmaps.
- [NoncompactQuantumSymmetry](../NoncompactQuantumSymmetry/README.md) owns the regular Mackey
  machine (its M2), which classifies the irreducible unitary representations of `M(2)` and
  `ISO(1,1)` and gives the irreducibility of the hyperbola models; 4.1 consumes it. This roadmap
  proves the irreducibility of the circle models directly (1.1), for complex `R` as well.
- The plane-wave expansion in `ℝⁿ` for `n ≥ 4` in terms of spherical harmonics of `S^{n−1}`
  belongs to the sibling roadmap on spheres in higher dimension of the same project; its zonal
  form is DLMF 10.23.9 of SpecialFunctionsBessel 4.3, consumed in 6.3. This roadmap owns the
  case `n = 3` with the spherical harmonics of SpecialFunctionsSU2MatrixElements.
- [LaguerreJacobi](../LaguerreJacobi/README.md) owns the Laguerre polynomials and the completeness
  of the Laguerre functions; 5.2 consumes them.

## Conventions

- **Groups.** `M(n)` is SpecialFunctionsGroupModels' `MotionGroup n`: pairs `(a, k)` with
  `(a, k)(a', k') = (a + k a', k k')`. On `M(2)`, `k_α` is the rotation by `α` (`rotation`), and
  `g(r, φ; α) = (r e(φ), k_α)` (`polar`) with `e(φ) = (cos φ, sin φ)` (`planePoint`), the
  coordinates of Vilenkin–Klimyk §4.1.1. A plane vector is also read as the complex number
  `a₁ + i a₂` (`toComplex`). The circle is `𝕋 = ℝ/2πℤ` with Mathlib's Haar probability measure
  `haarAddCircle`, i.e. `dψ/2π`, and `unitVec ψ = e(ψ)`; the angle of a rotation is `rotAngle`.
- **Circle models.** `(T_R(g) f)(ψ) = e^{iR⟨a, e(ψ)⟩} f(ψ − α)` for `g = (a, k_α)` and complex
  `R` (`circleAction`). This is SpecialFunctionsGroupModels' sphere model at `n = 2` and real
  `R`, Vilenkin–Klimyk's `T_{iR}` (their `T_R` of §4.1.2 (2), p. 166, has the real exponent
  `e^{Rr cos(ψ−φ)}`, unitary for imaginary `R`; on p. 195 their `L̂_R` is our `T_R` as well),
  and Miller's representation `(ρ)` of §3-8, (3.56), p. 73, with
  `ρ = R`. Unitary means `R` real.
- **Matrix elements** follow SpecialFunctionsGroupModels §3.1:
  `D_{mn}(g) = ⟪e_m, T(g) e_n⟫` (`matrixElement`), conjugate-linear in the first slot, in the
  basis `e_n(ψ) = e^{inψ}` (`fourierBasis`). Then `T(k_α) e_n = e^{−inα} e_n`: the weight of
  `e_n` under the rotation subgroup is `−n`, and
  `D_{mn}(g(r, φ; α)) = i^{n−m} e^{i(n−m)φ} e^{−inα} J_{n−m}(R r)`. This is Vilenkin–Klimyk
  §4.1.3 (3), p. 168, and Miller (3.57), p. 73, with Miller's `U_{nm}` read as our `D_{nm}`.
- **Bessel functions** are Mathlib's `Complex.besselJ ν z = (z/2)^ν ₀F₁(ν + 1; −z²/4)`; for
  integer order it is entire in `z`. `J_{−n} = (−1)ⁿ Jₙ`.
- **Fourier transform** is Mathlib's, `𝓕f(ξ) = ∫ e^{−2πi⟨x, ξ⟩} f(x) dx`. Vilenkin–Klimyk's
  transform of §4.4.1 (2), p. 193, has `e^{+i⟨x, y⟩}`; the dictionary is `y = −2πξ`, so the
  representation on the circle `|ξ| = ρ` is `T_{−2πρ}`, equivalent to `T_{2πρ}` by 1.1.
- **Hankel transform** `(H_ν φ)(R) = ∫₀^∞ φ(r) J_ν(R r) r dr` (`hankelTransform`), the
  Fourier–Bessel transform of Vilenkin–Klimyk §4.4.2 (3), p. 196.
- **Zonal Bessel functions** `Ω_n(λ, r) = Γ(n/2) Σ_k (−λ²r²/4)^k / (k! Γ(k + n/2))`
  (`besselZonal`), entire in `λ` and `r`; for `λ r ≠ 0` it is
  `Γ(n/2) (2/(λr))^{n/2−1} J_{n/2−1}(λ r)`, and `Ω_2 = J₀`, `Ω_3(λ, r) = sin(λr)/(λr)`,
  `Ω_1(λ, r) = cos(λr)`. Vilenkin–Klimyk Vol. 2 §9.3.2 (8)–(10), p. 48, write it for
  `ISO(n − 1)` with `p = (n − 2)/2`; here the dimension of the translation space is `n`.
- **`ISO(1,1)`** is SpecialFunctionsGroupModels' `ISO11`: pairs `(a, s)` with the boost
  `lorentzBoost s`. The hyperbola model is
  `(T_R(g) Φ)(θ) = e^{−R(a₁ cosh θ − a₂ sinh θ)} Φ(θ − s)` (`hyperbolaAction`), Vilenkin–Klimyk
  §4.2.3 (1)–(3), pp. 173–174, on the branch `x = (cosh θ, sinh θ)`; unitary for imaginary `R`.
- **Miller's group `T₃`** is `ℂ³` with `(b, c, τ)(b', c', τ') = (b + e^τ b', c + e^{−τ} c', τ + τ')`
  (`T3`), the group of Miller (3.4), p. 53, in his coordinates; its multiplier representation is
  `(A(g) f)(z) = exp(ω b z + ω c / z + m₀ τ) f(e^τ z)` (`millerAction`), Miller (3.6), p. 54.
- **Wigner's `d`** is SpecialFunctionsSU2MatrixElements' `wignerSmallD d i k β` with `d = 2l`,
  `i = l + m'`, `k = l + m` (Edmonds (4.1.15)); `d^l_{00}(β) = P_l(cos β)`.

## Exact supplier contracts

### From Tau Ceti

- `ContRepresentation.IsUnitary` (`TauCeti/RepresentationTheory/Continuous/Unitary/Basic.lean`):
  the unitarity predicate, in 1.1 and 4.1.
- `ContRepresentation` and `ContRepresentation.trivial`: the representations of 1.1 and 4.1 and
  the fallback of their realization by choice.

### From Mathlib

- `Complex.besselJ`, `Complex.besselJ_neg_int`: Bessel functions throughout.
- `haarAddCircle`, `fourier`, `fourierLp`, `fourierBasis`: the circle, its normalized measure and
  the trigonometric Hilbert basis, in Layer 1.
- The Fourier transform `𝓕` on `EuclideanSpace ℝ (Fin n)`: in Layer 5.
- `MeasureTheory.Measure.toSphere`: the surface measure, in 6.1.
- The Laplacian `Δ` of `Mathlib/Analysis/InnerProductSpace/Laplacian.lean`: in 5.1.
- `Complex.Gamma`, `Matrix.specialOrthogonalGroup`, `Matrix.toEuclideanLin`, `Complex.arg`.

### From other roadmaps

- SpecialFunctionsGroupModels (same project): §0.3 (the motion groups `M(n)` and `ISO(1,1)`, the
  topological-group instances, Haar measures and the polar decomposition), §2.6 (the sphere
  model), §§3.1–3.2 (matrix elements, the addition theorem, the inverse and the unitarity
  relations), §4.3 (the second-order equation of matrix elements), §§5.1–5.2 (bi-invariant
  functions, spherical functions, the spherical transform and the character theorem).
- SpecialFunctionsSU2MatrixElements (same project): §2.3 (Wigner's `d`), §2.4 (Jacobi
  polynomials and the Jacobi form of `d`), §2.6 (the Legendre form), §6.1 (the spherical
  harmonics), §6.3 (their addition theorem).
- [SpecialFunctionsBessel](../SpecialFunctionsBessel/README.md): 1.5 (recurrences and ladder
  operators), 4.1–4.3, 5.1 (the `cosh` integral of `K_ν`, DLMF 10.32.9), 11.2 (Weber's
  exponential integrals, for the Checks of 5.2), 11.3 and 11.5, consumed as stated in the
  layers.
- [LaguerreJacobi](../LaguerreJacobi/README.md): the Laguerre polynomials (its Layer 1) and the
  completeness of the Laguerre functions in `L²((0, ∞), x^α e^{−x} dx)`, in 5.2; the Gegenbauer
  polynomial, in 7.2.
- [NoncompactQuantumSymmetry](../NoncompactQuantumSymmetry/README.md) M2, in 1.1 (the
  classification remark) and 4.1.

`Suggested.lean` imports no other roadmap; it carries verbatim local copies of the definitions it
needs, each marked with its owner.

## How to read the build

Layer 0 fixes coordinates on `M(2)`. Layer 1 builds `T_R` and computes its matrix elements; the
one analytic input is Bessel's integral `(1/2π) ∫ e^{iz cos ψ} e^{inψ} dψ = iⁿ Jₙ(z)` (1.2),
which is the Jacobi–Anger expansion read as a Fourier series. Layer 2 needs only Layer 1 and the
addition theorem of SpecialFunctionsGroupModels §3.2. Layer 3 is independent of Layers 1–2: it
works with Laurent series in `z`, not with a Hilbert space. Layer 4 is parallel to Layer 1 for
`ISO(1,1)`. Layer 5 uses Layer 1 to identify the pieces of the quasi-regular representation and
Bessel's integral again for the Hankel transform. Layer 6 uses Layer 5 only for the spherical
transform and otherwise needs the sphere integral of 6.1. Layer 7 needs only the closed forms of
Wigner's `d` and of the Gegenbauer polynomials.

The harder material is the irreducibility of `T_R` for complex `R` (1.1), Hankel inversion and
Plancherel for real order (5.2), the classification of spherical functions (6.2) and the
contraction limits with the uniformity they need (Layer 7).

## Layer 0: the plane motion group in polar coordinates

### 0.1 Rotations and polar coordinates

Sources: Vilenkin–Klimyk §4.1.1 (1)–(5), p. 165; Miller §3-5 (3.39)–(3.40), p. 65.

`rotation α` is the matrix `[[cos α, −sin α], [sin α, cos α]]` of `SO(2)`; `rotAngle k` is the
argument of `k₀₀ + i k₁₀` in `ℝ/2πℤ`; `polar r φ α = (r e(φ), k_α)`. Prove:
- **Rotations form a circle group** (`rotation_add`): `k_{α+β} = k_α k_β`;
- **Every rotation of the plane is some `k_α`** (`exists_rotation_eq`), with `rotAngle k_α = α`
  modulo `2π`;
- **`rotAngle` is a homomorphism** (`rotAngle_mul`) to `ℝ/2πℤ`;
- **`k_α` is multiplication by `e^{iα}`** (`toComplex_rotE_rotation`) in the complex coordinate;
- **Polar product law** (`polar_mul`): `g(r₁, φ₁; α₁) g(r₂, φ₂; α₂) = g(r, φ; α₁ + α₂)` with
  `r e^{iφ} = r₁ e^{iφ₁} + r₂ e^{i(φ₂ + α₁)}`;
- **Polar form of `M(2)`** (`exists_polar`): every `g` is `g(|a|, φ; α)`.

These are the `n = 2` coordinates of the polar decomposition of SpecialFunctionsGroupModels §0.3,
with the complex form of Vilenkin–Klimyk §4.1.1 (5), p. 165 (`M(2)` as the matrices
`[[e^{iα}, z], [0, 1]]`).

**Checks.**
- `rotation (π/2)` sends `e₁` to `e₂`, and `toComplex e₂ = i = e^{iπ/2} · 1`.
- `g(1, 0; 0) g(1, π/2; 0)` has `r e^{iφ} = 1 + i`, so `r = √2`, `φ = π/4`, and rotation part
  `k₀`.
- `g(1, 0; π/2) g(1, 0; 0)` has `r e^{iφ} = 1 + i` but `g(1, 0; 0) g(1, 0; π/2)` has
  `r e^{iφ} = 2`; both have rotation part `k_{π/2}`.
- Negative control: the angle sum without the rotation of the second translation,
  `r₁ e^{iφ₁} + r₂ e^{iφ₂}`, gives `2` instead of `1 + i` for the first product of the previous
  Check; it is the law of the direct product `ℝ² × SO(2)`.

*Needs:* SpecialFunctionsGroupModels §0.3; Mathlib `Matrix.specialOrthogonalGroup`.

### Dependencies

SpecialFunctionsGroupModels §0.3.

## Layer 1: the circle models of `M(2)`

### 1.1 The models `T_R`, `R ∈ ℂ`

Sources: Vilenkin–Klimyk §4.1.2 (1)–(3), p. 166, and the irreducibility argument on p. 167;
Miller §3-8 (3.55)–(3.56), p. 73, and §3-7 (3.50)–(3.51), p. 71 (the unitary representations
`(ρ)`); Dieudonné §16, p. 57.

`circleAction R g f ψ = e^{iR⟨a, e(ψ)⟩} f(ψ − rotAngle k)` for `g = (a, k)`. `circleRep R` is the
representation on `L²(𝕋)` that agrees almost everywhere with it and has continuous orbit maps,
chosen when one exists (`IsCircleRealization`), as in SpecialFunctionsGroupModels §1.3. Prove:
- **Representation law of the circle model** (`circleAction_mul`): `T_R(gh) = T_R(g) T_R(h)` and
  `T_R(1) = 1` on functions;
- **Agreement with the sphere model** (`circleAction_eq_motionAction`): for real `R`, `T_R` is
  SpecialFunctionsGroupModels' `motionAction R` on the unit circle;
- **Size of the multiplier** (`norm_circleAction`): `|e^{iR⟨a, e(ψ)⟩}| = e^{−Im R ⟨a, e(ψ)⟩}`, so
  `‖T_R(g)‖ ≤ e^{|Im R| |a|}`;
- **`L²` realization** (`exists_circleRealization`) for every complex `R`;
- **Unitarity range** (`isUnitary_circleRep_iff`): `T_R` is unitary exactly when `R` is real;
- **`T_{−R}` and `T_R` are equivalent** (`circleAction_neg`) through the half-turn
  `f ↦ f(· + π)`;
- **Irreducibility of `T_R`, `R ≠ 0`** (`circleRep_irreducible`): a closed invariant subspace is
  `0` or `L²(𝕋)`;
- `T_R ≅ T_{R'}` (by a bounded operator with bounded inverse intertwining them) exactly when
  `R'² = R²`; for real `R, R' > 0` and unitary equivalence, this with the irreducibility gives
  SpecialFunctionsGroupModels §2.6's inequivalence at `n = 2`.

Irreducibility: a closed subspace invariant under the rotations is the closed span of the `e_n`
it contains (its projection commutes with the rotations, hence with each Fourier projection); by
the ladder relations of 1.3 applied to the difference quotients of `T_R((t e(β), 1))`, which stay
in the subspace, it contains `e_{n±1}` with `e_n` when `R ≠ 0`. The equivalence class is fixed by
the Casimir value `−R²` of 1.3.

**Checks.**
- For `R = 0`, `T_0(g) e_n = e^{−inα} e_n`: `T_0` is the sum of the characters `(a, k_α) ↦ e^{−inα}`
  and is reducible; irreducibility needs `R ≠ 0`.
- `|T_R(r e₁, 1) 1|(0) = e^{−r Im R}`, which is `e^{−0.8} = 0.44932 89641` at `R = i`, `r = 0.8`,
  and the model is not unitary there.
- `T_{−R}` and `T_R` have the same Casimir value `−R²`; at `R = 1.7`, `D^{−R}_{2,−1}` and
  `D^R_{2,−1}` at `(0.8 e₁, 1)` are `+0.04662 03227 i` and `−0.04662 03227 i`, related by
  `(−1)^{m−n} = −1` (1.2).
- Negative control: without the rotation in the argument, `f ↦ e^{iR⟨a, e(ψ)⟩} f(ψ)` is not a
  representation: the product law of 0.1 needs `f(ψ − α)` to turn `e^{iR⟨a', e(ψ − α)⟩}` into
  `e^{iR⟨k_α a', e(ψ)⟩}`.

*Needs:* 0.1; SpecialFunctionsGroupModels §§1.3, 2.6; NoncompactQuantumSymmetry M2 for the remark
that the `T_R`, `R > 0`, and the characters exhaust the irreducible unitary representations of
`M(2)` (Vilenkin–Klimyk p. 167), which is not a target here.

### 1.2 Matrix elements

Sources: Vilenkin–Klimyk §4.1.3 (1)–(5), pp. 167–168 (the symbol `r^R_{mn}` in (4) is `t^R_{mn}`);
Miller §3-8 (3.57),
p. 73; Vilenkin–Klimyk §4.1.5 (1), p. 170 (Bessel's integral as a Fourier coefficient).

Prove:
- **Bessel's integral on the circle** (`integral_exp_inner_fourier`):
  `∫_𝕋 e^{iR⟨r e(φ), e(ψ)⟩} e^{inψ} dψ/2π = iⁿ e^{inφ} Jₙ(R r)` for complex `R`; route: the
  Jacobi–Anger expansion of SpecialFunctionsBessel 4.1 at `t = i e^{i(ψ−φ)}`, integrated term by
  term;
- **Matrix elements of `T_R`** (`matrixElement_circleRep_polar`):
  `D_{mn}(g(r, φ; α)) = i^{n−m} e^{i(n−m)φ} e^{−inα} J_{n−m}(R r)`;
- **Weights** (`circleRep_rotation_fourierLp`): `T_R(k_α) e_n = e^{−inα} e_n`;
- **Sign change of `R`** (`matrixElement_circleRep_neg`): `D^{−R}_{mn} = (−1)^{m−n} D^R_{mn}`;
- for real `R`, the unitarity relations of SpecialFunctionsGroupModels §3.2 at `g = (r e₁, 1)` are
  `Σ_k J_{k−m}(x) J_{k−n}(x) = δ_{mn}`, Vilenkin–Klimyk §4.1.4 (6), p. 169, which is DLMF
  10.23.3–10.23.5 of SpecialFunctionsBessel 4.2 for integer order; state the agreement.

**Checks.**
- At `R = 1.7`, `D_{2,−1}(g(0.8, 0.4; 1.1)) = −0.00465 42661 − 0.04638 74153 i` from the integral
  and from the closed form.
- At `R = 0.6 + 0.9i` the same element is `0.00453 57033 + 0.01297 66161 i` from both sides.
- At `g = (0.8 e₁, 1)`, `D_{2,−1} = i³ J₃(1.36) = −0.04662 03227 i`, SpecialFunctionsGroupModels
  §2.6's Check.
- `Σ_k J_{3−k}(2.3) J_{1−k}(2.3) = 0` and `Σ_k J_{2−k}(2.3)² = 1`.
- Negative control: Bessel's integral with `e^{−inψ}` in place of `e^{inψ}` at `R = 0.9 + 0.4i`,
  `r = 1.1`, `φ = 0.3`, `n = 3` is `0.00744 58507 − 0.02409 75058 i`, not
  `i³ J₃(R r) e^{3iφ} = 0.02177 55860 + 0.01272 61278 i`; and the closed form with `e^{+inα}` in
  place of `e^{−inα}` gives `−0.03476 50176 + 0.03106 20031 i` in the first Check.

*Needs:* 1.1; SpecialFunctionsBessel 4.1; SpecialFunctionsGroupModels §§3.1–3.2.

### 1.3 Infinitesimal operators

Sources: Vilenkin–Klimyk §4.1.2 (4)–(9), p. 167; Miller §3-7 (3.50)–(3.51), p. 71;
Vilenkin–Klimyk §4.1.4, p. 170 (the recurrences as infinitesimal addition theorems).

With `B_β = d/dt T_R((t e(β), 1))|₀`, multiplication by `iR cos(ψ − β)`, and `B₃ = −d/dψ`, the
operators `H± = B_{0} ± i B_{π/2}` act by `H± e_n = iR e_{n±1}`. Prove:
- **Ladder operators** (`hasDerivAt_circleAction_fourier`):
  `d/dt T_R((t e(β), 1)) e_n |₀ = (iR/2)(e^{−iβ} e_{n+1} + e^{iβ} e_{n−1})` pointwise;
- **Casimir value `−R²`** (`circleAction_casimir`): `B₀² + B_{π/2}² = −R²` on every function;
- **Lie derivative of matrix elements** (`hasDerivAt_matrixElement_mul_translation`):
  `d/dt D_{mn}(g (t e₁, 1))|₀ = (iR/2)(D_{m,n+1}(g) + D_{m,n−1}(g))`;
- with the closed form of 1.2, the last identity at `g = (r e₁, 1)` and the analogous one for
  `(t e₂, 1)` are the recurrences `J_{k−1} − J_{k+1} = 2J'_k` and `J_{k−1} + J_{k+1} = (2k/x) J_k`
  of SpecialFunctionsBessel 1.5, and the Casimir equation is Bessel's equation for `J_{n−m}(R r)`,
  the `M(2)` case of SpecialFunctionsGroupModels §4.3; state the agreement.

**Checks.**
- At `R = 1.2 + 0.3i`, `β = 0.7`, `n = 2`, `ψ = 0.4` both sides of the ladder identity are
  `−1.02205 65417 + 0.59311 22752 i`.
- At the same point `B₀² e₂ + B_{π/2}² e₂ = −R² e₂ = −0.42405 76722 − 1.47005 95534 i`.
- At `R = 1.7`, `(m, n) = (1, −2)`, `g = g(0.8, 0.4; 1.1)` the Lie derivative is
  `0.04278 48273 − 0.16131 61715 i` from both sides.
- Negative control: Vilenkin–Klimyk's `H± e_n = R e_{n±1}` (no factor `i`) is the same identity
  for their `T_R = T_{iR}` here; read in our convention it gives the Casimir value `+R²`.

*Needs:* 1.1–1.2; SpecialFunctionsBessel 1.5; SpecialFunctionsGroupModels §4.3.

### Examples

- `D_{00}(g) = J₀(R|a|)`: the zonal matrix element of `T_R` is the spherical function of 6.2 at
  `n = 2`; at `R = 1.7`, `|a| = 0.8` it is `J₀(1.36) = 0.58838 50403`.

### Dependencies

Layer 0; SpecialFunctionsGroupModels §§1.3, 2.6, 3.1–3.2, 4.3; SpecialFunctionsBessel 1.5, 4.1–4.2;
NoncompactQuantumSymmetry M2.

## Layer 2: identities from the group law

### 2.1 The addition theorem in polar form

Sources: Vilenkin–Klimyk §4.1.4 (1)–(6), pp. 168–169; Miller (3.32), p. 63 (Graf's theorem from
`T₃`); DLMF 10.23.7.

Prove:
- **Addition theorem in polar form** (`hasSum_besselJ_polar_addition`): if
  `r e^{iφ} = r₁ + r₂ e^{iφ₂}`, then for complex `R` and integers `m, n`,
  `e^{i(n−m)φ} J_{n−m}(R r) = Σ_k J_{k−m}(R r₁) J_{n−k}(R r₂) e^{i(n−k)φ₂}`;
- the special cases `Σ_k (−1)^k e^{ikφ₂} J_k(r₁) J_k(r₂) = J₀(r)`,
  `Σ_k J_{n−k}(x) J_k(y) = J_n(x + y)`, `Σ_k (−1)^k J_{n−k}(x) J_k(y) = J_n(x − y)` and
  `Σ_k J_{n+k}(x) J_k(x) = δ_{n0}` (Vilenkin–Klimyk §4.1.4 (3)–(6), p. 169);
- the first bullet is Graf's addition theorem 10.23.7 of SpecialFunctionsBessel 4.2 at integer
  order; state the agreement.

Route: SpecialFunctionsGroupModels §3.2's addition theorem for `T_R` at
`g₁ = (r₁ e₁, 1)`, `g₂ = g(r₂, φ₂; 0)`, whose product is `g(r, φ; 0)` by 0.1, with the closed
form of 1.2; the powers of `i` cancel.

**Checks.**
- At `R = 0.7 + 0.2i`, `(m, n) = (1, 3)`, `r₁ = 1.3`, `r₂ = 0.7`, `φ₂ = 0.9` both sides are
  `0.08967 74027 + 0.17150 10358 i`.
- At `φ₂ = 0` the theorem is `J_{n−m}(R(r₁ + r₂)) = Σ_k J_{k−m}(R r₁) J_{n−k}(R r₂)`, Neumann's
  addition theorem.
- Negative control: with `e^{−i(n−k)φ₂}` in place of `e^{i(n−k)φ₂}` the sum in the first Check is
  `0.19176 22112 − 0.02611 31424 i`.

*Needs:* 0.1, 1.2; SpecialFunctionsGroupModels §3.2.

### 2.2 The multiplication formula and its radial form

Sources: Vilenkin–Klimyk §4.1.4 (7)–(9), pp. 169–170; DLMF 10.23.7 (the geometry of Graf's
theorem).

Prove:
- **Multiplication formula** (`integral_besselJ_circleMean`): with `w = r₁ + r₂ e^{iφ₂}`,
  `∫₀^{2π} (w/|w|)ⁿ e^{−imφ₂} Jₙ(R|w|) dφ₂ = 2π J_{n−m}(R r₁) J_m(R r₂)`;
- **Radial form of the multiplication formula** (`besselJ_mul_besselJ_eq_integral`): for
  `r₁, r₂ > 0`, `r₁ ≠ r₂`,
  `J_{n−m}(r₁) J_m(r₂) = (2/π) ∫_{|r₁−r₂|}^{r₁+r₂} cos(nφ − mφ₂) r Jₙ(r) Δ^{−1/2} dr`, with
  `Δ = 4r₁²r₂² − (r² − r₁² − r₂²)²` (four times the squared area of the triangle with sides
  `r₁, r₂, r`), `φ₂ = arccos((r² − r₁² − r₂²)/(2r₁r₂))` and `φ = arg(r₁ + r₂ e^{iφ₂})`.

Route: the multiplication formula is the orthogonality of `e^{ikφ₂}` applied to 2.1; the radial
form substitutes `r = |w|` on the two halves `φ₂ ∈ (0, π)` and `(π, 2π)`, whose contributions are
complex conjugates. The printed (8) has `e^{i(nφ − mφ₂)}` in place of the cosine; its left side
is real.

**Checks.**
- The circle mean at `R = 1`, `(m, n) = (1, 2)`, `r₁ = 1.3`, `r₂ = 0.7` is
  `J₁(1.3) J₁(0.7) = 0.17174 34254`; at `(m, n) = (1, 3)` it is `J₂(1.3) J₁(0.7) = 0.06021 50045`.
- At `R = 0.5 + 0.4i`, `(m, n) = (1, 3)` both sides are `−0.00693 81873 + 0.01776 29627 i`.
- The radial form at `m = n = 0` gives `J₀(1.3) J₀(0.7) = 0.54642 03250`, and at `(m, n) = (1, 3)`
  gives `0.06021 50045`.
- Negative control: the printed exponential form gives `0.06021 50045 − 0.00361 89355 i` at
  `(m, n) = (1, 3)`, not real.

*Needs:* 2.1.

### Dependencies

Layer 1; SpecialFunctionsGroupModels §3.2; SpecialFunctionsBessel 4.2.

## Layer 3: Miller's complex group `T₃`

### 3.1 The multiplier representation and its matrix elements

Sources: Miller §3-1 (3.3)–(3.11), pp. 52–55, and (3.12), p. 56.

`T3` is `ℂ³` with the law of Conventions; it is a group (`Suggested.lean` proves the group laws).
`millerAction ω m₀ g f z = exp(ω b z + ω c / z + m₀ τ) f(e^τ z)`, and
`millerMatrix ω m₀ l k g` is Miller's (3.11),
`e^{(k+m₀)τ} Σ_s (ωb)^{s+(l−k)⁺} (ωc)^{s+(k−l)⁺} / ((s + (l−k)⁺)! (s + (k−l)⁺)!)`. Prove:
- **Representation law of Miller's model** (`millerAction_mul`): `A(gh) = A(g) A(h)` and
  `A(1) = 1` (Miller (3.7));
- **Generating function of the matrix elements** (`hasSum_millerMatrix`):
  `exp(ω b z + ω c / z + (k + m₀) τ) = Σ_l A_{lk}(g) z^{l−k}` for `z ≠ 0` (Miller (3.9)): the
  matrix of `A(g)` on the Laurent monomials `f_k(z) = z^k`;
- **Addition theorem for the matrix elements** (`hasSum_millerMatrix_mul`):
  `A_{lk}(gh) = Σ_j A_{lj}(g) A_{jk}(h)` (Miller (3.10));
- written out with Miller's `₀F₁` form (3.12) at `τ = 0`, the addition theorem is the `₀F₁`
  addition formula (3.16), pp. 56–57, and its special cases on p. 57.

**Checks.**
- At `(ω, m₀) = (−1, 0.3)`, `g = (0.3 + 0.2i, −0.5 + 0.1i, 0.2 + 0.4i)`, `A_{2,−1}(g)` is
  `−0.00067 84434 − 0.00647 24196 i` from the series and from the Laurent coefficient.
- With `h = (−0.4 + 0.3i, 0.2 + 0.6i, −0.3 + 0.1i)`, both sides of the addition theorem for
  `(l, k) = (1, −2)` are `−0.01673 21668 + 0.00648 04404 i`.
- `A_{lk}(1) = δ_{lk}`.
- Negative control: the law `(b + b', c + c', τ + τ')` of the abelian group `ℂ³` breaks the
  representation law as soon as `τ ≠ 0`: `A(g) A(h)` has `b + e^τ b'` in the exponent.

*Needs:* Mathlib power series and `HasSum` over `ℤ`.

### 3.2 The Bessel form

Sources: Miller (3.13)–(3.15), p. 56, and (3.32), p. 63.

Prove:
- **Bessel form of the matrix elements** (`millerMatrix_eq_besselJ`): for `b = r v/2`,
  `c = −r/(2v)`, `v ≠ 0`, `A_{lk}(b, c, τ) = e^{(m₀+k)τ} (−v)^{l−k} J_{l−k}(−ω r)`;
- at `τ = 0`, `v = −1`, `ω = −1`, `k = 0` the generating function of 3.1 is
  `exp((r/2)(z − z⁻¹)) = Σ_l J_l(r) z^l` (Miller (3.15)), SpecialFunctionsBessel 4.1's
  generating function; and the addition theorem of 3.1 in these coordinates is Graf's theorem
  (Miller (3.32)); state both agreements.

**Checks.**
- At `ω = 2 + 0.5i`, `r = 1.1 + 0.3i`, `v = 0.7 − 0.5i`, `τ = 0.2 + 0.4i`, `m₀ = 0`:
  `A_{3,1} = 0.48510 79951 − 0.11578 56057 i` and `A_{1,3} = −1.35258 79958 + 0.12873 54117 i`,
  from both sides.
- `A_{lk}` with `b = c = 0` is `δ_{lk} e^{(m₀+k)τ}`, and `J_{l−k}(0) = δ_{lk}`.
- Negative control: with `J_{l−k}(ω r)` in place of `J_{l−k}(−ω r)` the value at `(l, k) = (2, 1)`
  is `−0.85141 20393 + 0.32540 91509 i` instead of `0.85141 20393 − 0.32540 91509 i`.

*Needs:* 3.1; Mathlib `Complex.besselJ`.

### 3.3 Weisner's generating function

Sources: Miller §3-4 (3.33)–(3.38), pp. 63–65.

With `E_m(y) = Σ_k (−y/4)^k / (2^m k! Γ(m + k + 1))` (`besselJEntire`), the entire function with
`E_m(u²) = u^{−m} J_m(u)`, prove:
- **Weisner's generating function** (`hasSum_besselJ_weisner`): for complex `m`, `t ≠ 0` and
  `|x t| < 2`, `Σ_n Jₙ(x) tⁿ / Γ(m − n + 1) = (2 + x t)^m E_m(x² + 2x/t)`, with `1/Γ` zero at the
  poles.

Route (Miller): `h(x, t) = (2 + xt)^m E_m(x² + 2x/t)` is `T(g) [J_m(x) t^m]` for the element
`b = τ = 0`, `c = −1` of `T₃` acting by the two-variable realization of §3-3; the Casimir equation
makes each Laurent coefficient a solution of Bessel's equation bounded at `0`, hence `cₙ Jₙ`, and
the second eigen-equation gives `c_{n+1} = (m − n) cₙ`, `c₀ = 1/Γ(m + 1)`.

**Checks.**
- At `m = 0.7`, `x = 0.9`, `t = 0.6` both sides are `0.69013 27265`.
- At `m = 0` only `n ≤ 0` survive, and the identity is
  `Σ_{n ≥ 0} J_{−n}(x) t^{−n}/n! = J₀(√(x² + 2x/t))`, the case `ν = 0` of the multiplication
  theorem 10.23.1 of SpecialFunctionsBessel 4.2; at `x = 0.9`, `t = 0.6` both sides are
  `0.25168 55588`.
- Negative control: the theorem is not a case of the generating function of 3.1, whose
  coefficients carry no `1/Γ(m − n + 1)`; at `m = 0.7` the term `n = 1` has weight
  `1/Γ(0.7) = 0.77038 31839`, not `1`.

*Needs:* 3.1–3.2; SpecialFunctionsBessel 1.1 (uniqueness of the solution bounded at `0`).

### Dependencies

Mathlib; SpecialFunctionsBessel 1.1, 4.1–4.2.

## Layer 4: the pseudo-Euclidean motion group `ISO(1,1)`

### 4.1 The hyperbola model

Sources: Vilenkin–Klimyk §§4.2.1–4.2.3 (1)–(6), pp. 171–175.

`hyperbolaAction R g Φ θ = e^{−R(a₁ cosh θ − a₂ sinh θ)} Φ(θ − s)` for `g = (a, s)`;
`hyperbolaRep R` is its realization on `L²(ℝ)` by choice (`IsHyperbolaRealization`). Prove:
- **Representation law of the hyperbola model** (`hyperbolaAction_mul`);
- **`L²` realization exactly on the imaginary axis, and unitarity there**
  (`exists_hyperbolaRealization_iff`): a realization with continuous orbit maps exists exactly
  when `Re R = 0`, and then `hyperbolaRep R` is unitary;
- for `R ∈ iℝ \ {0}` the model is irreducible, by NoncompactQuantumSymmetry M2: it is induced from
  the character `a ↦ e^{−R[x₀, a]}` of `ℝ²` at a point `x₀` of the hyperbola, whose orbit under
  `SO₀(1,1)` is one branch and whose stabilizer is trivial;
- for `R = 0` the model is the regular representation of `SO₀(1,1) ≅ ℝ` and is reducible.

The law uses that `Λ_s` preserves `[x, y] = x₁y₁ − x₂y₂`: `[Λ_{−s} x, a'] = [x, Λ_s a']`. The
printed equivalence `T_R ≅ T_{−R}` (Vilenkin–Klimyk p. 175) maps one branch of the hyperbola to
the other; on one branch `T_{iρ}` and `T_{−iρ}` are inequivalent, since the joint spectrum of
the translations lies on opposite branches of `y₁² − y₂² = ρ²`.

**Checks.**
- `[Λ_s x, Λ_s y] = [x, y]`: at `s = 1`, `x = (1, 0)` the form is `cosh² 1 − sinh² 1 = 1`.
- At `R = i`, `|T_R(g) Φ| = |Φ(· − s)|` pointwise.
- At `R = 1`, `g = ((−1, 0), 0)` the multiplier `e^{cosh θ}` is unbounded, so `T_1(g)` does not
  map `L²(ℝ)` into itself: no realization.
- Negative control: the Euclidean form `x₁y₁ + x₂y₂` in place of `[x, y]` breaks the law, since
  `Λ_s` does not preserve it.

*Needs:* SpecialFunctionsGroupModels §§0.3, 1.3; NoncompactQuantumSymmetry M2.

### 4.2 The Laplace realization and the Macdonald kernel

Sources: Vilenkin–Klimyk §4.2.4 (1)–(8), pp. 175–176; DLMF 10.32.9.

`fourierLaplace Φ λ = ∫ Φ(θ) e^{λθ} dθ`, entire for continuous `Φ` with compact support, with
the inversion `Φ(θ) = (1/2πi) ∫_{a−i∞}^{a+i∞} F(μ) e^{−μθ} dμ` (Vilenkin–Klimyk §4.2.4 (2)).
Prove:
- **Boosts act diagonally** (`fourierLaplace_hyperbolaAction_boost`):
  `F_{(0,s)}(λ) = e^{λs} F(λ)`;
- **Translations act by the Macdonald kernel** (`fourierLaplace_hyperbolaAction_translation`):
  for `Re R > 0`, `r > 0`, real `a` and smooth `Φ` with compact support,
  `F_{((r,0),0)}(λ) = (1/2π) ∫ (∫ e^{−Rr cosh θ + (λ − a − it)θ} dθ) F(a + it) dt`;
- the inner integral is `2 K_{λ−a−it}(R r)` by the `cosh` integral of SpecialFunctionsBessel 5.1
  (DLMF 10.32.9), so the kernel is Vilenkin–Klimyk's `(1/πi) K_{λ−μ}(R r) dμ`;
- for `g = (0, ψ)((r, 0), 0)(0, s − ψ)`, an element of the semigroup `|a₂| < a₁`
  (Vilenkin–Klimyk §4.2.2 (5), p. 172), the operator has the kernel
  `e^{λψ} (1/πi) K_{λ−μ}(R r) e^{μ(s−ψ)}` (§4.2.4 (7)–(8), p. 176).

**Checks.**
- For `Φ(θ) = e^{−(θ−0.5)²}` and `λ = 0.4 + 0.7i`, both sides of the boost identity are
  `1.75888 31600 + 0.93816 74289 i`.
- For `Φ(θ) = e^{−θ²}`, `F(μ) = √π e^{μ²/4}`, `R = 0.8`, `r = 1.3`, `a = 0.2`, `λ = 0.4 + 0.7i`,
  both sides of the translation identity are `0.47429 63035 + 0.04156 61041 i`.
- At `μ = 0.1 + 0.3i` the inner integral is `2 K_{λ−μ}(1.04) = 0.77349 63299 + 0.06617 00352 i`.
- Negative control: for `g = ((0, r), 0)` the kernel integral `∫ e^{±R r sinh θ + (λ−μ)θ} dθ`
  diverges when `Re R ≠ 0` (Vilenkin–Klimyk p. 176): only the semigroup `|a₂| < a₁` has an
  integral kernel of this form.

*Needs:* 4.1; SpecialFunctionsBessel 5.1.

### Dependencies

SpecialFunctionsGroupModels §§0.3, 1.3; NoncompactQuantumSymmetry M2; SpecialFunctionsBessel 5.1.

## Layer 5: the quasi-regular representation and the Hankel transform

### 5.1 The Fourier picture of `L(g) f = f ∘ g⁻¹`

Sources: Vilenkin–Klimyk §4.4.1 (1)–(7), pp. 193–195;
Vilenkin–Klimyk Vol. 2 §9.1.8 (1)–(4), p. 19 (the Laplacian commutes with `ISO(n)`).

`motionApply g x = a + k x` is the action of `M(n)` on `ℝⁿ`. Prove:
- **Fourier transform of a translate-rotate** (`fourier_comp_motionApply`): for integrable `f`,
  `𝓕(f ∘ g⁻¹)(ξ) = e^{−2πi⟨a, ξ⟩} 𝓕f(k⁻¹ξ)`;
- **On the circle `|ξ| = ρ` the quasi-regular representation is `T_{−2πρ}`**
  (`fourier_comp_motionApply_circle`): `ρ e(ψ) ↦ 𝓕(f ∘ g⁻¹)(ρ e(ψ))` is
  `T_{−2πρ}(g)` applied to `ψ ↦ 𝓕f(ρ e(ψ))`;
- the map `f ↦ (ρ ↦ 𝓕f(ρ e(·)))` is unitary from `L²(ℝ²)` onto `L²((0, ∞), 2πρ dρ; L²(𝕋))` and
  intertwines `L` with the field `ρ ↦ T_{−2πρ}`: the decomposition `L ≅ ∫^⊕ T_{2πρ} 2πρ dρ` of
  Vilenkin–Klimyk §4.4.1 (7), p. 195, where `T_R` stands for our `T_R`, their `T_{iR}`;
- **Cylindrical waves** (`laplacian_cylindricalWave`): `u(x) = Jₙ(R|x|)(x/|x|)ⁿ`, with `x` read as
  a complex number, satisfies `Δu = −R²u` on `x ≠ 0`, for complex `R`.

**Checks.**
- At `g = 1` the first identity is trivial; at `g = (a, 1)` it is the translation rule of `𝓕`.
- For `R = 1.7`, `n = 2`, `x = (0.6, −0.4)`, `Δu(x) = −R² u(x) = −0.18385 12093 + 0.44124 29024 i`.
- Negative control: with Vilenkin–Klimyk's kernel `e^{+i⟨x, y⟩}` the circle representation is
  `T_{+|y|}`; the plane-wave computation printed on p. 195, with `e^{+i⟨x, y⟩}` in the inverse
  transform, is off by the factor `(−1)ⁿ R`.

*Needs:* 1.1; Mathlib `𝓕`, `Δ`.

### 5.2 The Hankel transform

Sources: Vilenkin–Klimyk §4.4.2 (1)–(7), pp. 196–197; Vilenkin–Klimyk Vol. 2 §10.2.6 (1)–(7),
pp. 186–187, and (13)–(17), p. 188.

`hankelTransform ν φ R = ∫₀^∞ φ(r) J_ν(Rr) r dr`. Prove:
- **Fourier transform of an angular mode** (`fourier_angularMode`): for `∫₀^∞ |φ(r)| r dr < ∞`,
  `ρ > 0`, `𝓕(φ(|x|) (x/|x|)ⁿ)(ρ e(ψ)) = 2π (−i)ⁿ e^{inψ} (Hₙφ)(2πρ)`;
- **Hankel inversion** (`hankelTransform_hankelTransform`): for real `ν > −1` and smooth `φ` with
  compact support in `(0, ∞)`, `H_ν H_ν φ = φ` on `(0, ∞)`;
- **Plancherel for the Hankel transform** (`lintegral_hankelTransform`) for the same `φ`:
  `∫₀^∞ |H_ν φ|² R dR = ∫₀^∞ |φ|² r dr`;
- `H_ν` extends to a unitary involution of `L²((0, ∞), r dr)`;
- **Laguerre functions are eigenfunctions** (`hankelTransform_laguerre`): for `ν > −1`, `λ > 0`,
  `H_ν(x^ν e^{−x²/2} L_k^ν(x²))(λ) = (−1)^k λ^ν e^{−λ²/2} L_k^ν(λ²)`.

Route. For integer `ν = n` the group route: by the first bullet and Fourier inversion and Plancherel
on `ℝ²`, `Hₙ` is the radial part of `𝓕` on the `n`-th angular mode (Vilenkin–Klimyk §4.4.2 (3)–(5)).
For real `ν > −1` the Laguerre route: the eigenfunction bullet follows from Weber's integral
`∫ e^{−x²/2} x^{2j+ν} J_ν(λx) x dx = 2^j j! λ^ν e^{−λ²/2} L_j^ν(λ²/2)` (Vol. 2 (14), p. 188;
SpecialFunctionsBessel 11.2) and a finite Laguerre identity (Vol. 2 (15)); the functions
`x^ν e^{−x²/2} L_k^ν(x²)` are complete and orthogonal in `L²((0, ∞), x dx)` (LaguerreJacobi, after
`x² = y`), so `H_ν` is the unitary operator with eigenvalues `(−1)^k` on this basis; it remains to
identify that operator with the integral on smooth `φ`. Vilenkin–Klimyk derive
`ν ∈ ½ℤ_{≥0}` from the groups and assert "any `ν`" (Vol. 2 p. 186).

**Checks.**
- `H₀(e^{−r²/2})(1.3) = e^{−0.845} = 0.42955 73582`.
- `H₂(r² e^{−r²/2})(1.3) = 1.69 e^{−0.845} = 0.72595 19354`.
- At `ν = 0.3`, `k = 2`, `λ = 1.3` both sides of the eigenfunction identity are
  `−0.44798 00523`; at `k = 0` they are `0.46473 37023`.
- For `n = 2`, `φ(r) = r² e^{−r²}`, `ρ = 0.35`, `ψ = 0.6` both sides of the angular-mode identity
  are `−0.41081 82347 − 1.05668 67890 i`.
- At `k = 1` the eigenvalue is `−1`: both sides are `0.18124 61439`.
- Negative control: the eigenvalue `+1` at `k = 1` would give `−0.18124 61439`.

*Needs:* 5.1; SpecialFunctionsBessel 11.2; LaguerreJacobi.

### 5.3 The Fourier transform of radial functions on `ℝⁿ`

Sources: Vilenkin–Klimyk Vol. 2 §10.2.6 (1)–(2), p. 186; Dieudonné §16, p. 57.

Prove:
- **Fourier transform of a radial function on `ℝⁿ`** (`fourier_radial`): for `n ≥ 1`,
  `f(x) = φ(|x|)` with `∫₀^∞ |φ(r)| r^{n−1} dr < ∞` and `ξ ≠ 0`,
  `𝓕f(ξ) = 2π |ξ|^{1−n/2} ∫₀^∞ φ(r) J_{n/2−1}(2π|ξ| r) r^{n/2} dr`.

Route: integrate over spheres in polar coordinates and use 6.1,
`∫_{S^{n−1}} e^{−2πi r⟨ξ, ω⟩} dσ = |S^{n−1}| Ω_n(2π|ξ|, r)`.

**Checks.**
- `e^{−π|x|²}` is its own transform: at `n = 3`, `|ξ| = 0.7` the right side is
  `e^{−0.49π} = 0.21451 39731`.
- At `n = 1` the formula is `2 ∫₀^∞ φ(r) cos(2π|ξ| r) dr`, since `J_{−1/2}(z) = √(2/(πz)) cos z`.
- At `n = 2` it is the angular-mode identity of 5.2 at `n = 0`.
- Negative control: the order `n/2` in place of `n/2 − 1` gives a function vanishing at `ξ → 0`
  for every `φ`, while `𝓕f(0) = ∫ f ≠ 0` for `f = e^{−π|x|²}`.

*Needs:* 6.1; Mathlib polar coordinates.

### Examples

- The three-Bessel integral
  `∫₀^∞ J_{n−m}(R r₁) J_m(R r₂) Jₙ(R r) R dR = (2/π) cos(nφ − mφ₂)/√Δ` for
  `|r₁ − r₂| < r < r₁ + r₂`, `0` outside (Vilenkin–Klimyk §4.4.2, p. 198, with the cosine where
  the printed text has the exponential), from 2.2 by Hankel inversion; at `m = 0` it is DLMF
  10.22.74 of SpecialFunctionsBessel 11.3.

### Dependencies

Layers 1, 6.1; SpecialFunctionsBessel 11.2–11.3; LaguerreJacobi; Mathlib `𝓕`.

## Layer 6: the Gel'fand pair `(M(n), SO(n))`

### 6.1 Zonal Bessel functions

Sources: Vilenkin–Klimyk Vol. 2 §9.3.2 (8)–(10), p. 48, and §9.3.3 (3), pp. 48–49; Dieudonné §16
(193), p. 57; DLMF 10.9.4.

`besselZonal n λ r = Γ(n/2) Σ_k (−λ²r²/4)^k / (k! Γ(k + n/2))`;
`motionSphericalFunction n λ (a, k) = Ω_n(λ, |a|)`. Prove:
- **Bessel form of the zonal function** (`besselZonal_eq_besselJ`): for `λ` in the slit plane and
  `r > 0`, `Ω_n(λ, r) = Γ(n/2)(2/(λr))^{n/2−1} J_{n/2−1}(λr)`;
- **Integral over the sphere** (`besselZonal_eq_integral_sphere`): `Ω_n(λ, |a|)` is the mean of
  `e^{iλ⟨a, ξ⟩}` over the unit sphere `S^{n−1}`;
- **Radial equation** (`besselZonal_ode`): `Ω_n(λ, ·)` is smooth and
  `Ω″ + ((n − 1)/r) Ω′ = −λ² Ω` for `r > 0`.

**Checks.**
- `Ω₂(λ, r) = J₀(λr)` and `Ω₃(λ, r) = sin(λr)/(λr)`: at `λ = 1.4`, `r = 0.9`, `Ω₃ = 0.75562 72552`.
- `Ω₄(1.4, 0.9) = 2 J₁(1.26)/1.26 = 0.81425 17801` from the series and from the Bessel form.
- `Ω_n(λ, 0) = 1` for every `n ≥ 1` and `λ`.
- Negative control: `Ω_n(5i, 1)` at `n = 2` is `I₀(5) = 27.23987 18236`, larger than `1`: the
  sphere mean of `e^{iλ⟨a,ξ⟩}` is bounded by `1` only for real `λ`.

*Needs:* Mathlib `Complex.besselJ`, `Complex.Gamma`, `MeasureTheory.Measure.toSphere`.

### 6.2 Spherical functions

Sources: Dieudonné §16, (188)–(193), pp. 55–57; Vilenkin–Klimyk Vol. 2 §9.3.2 (8)–(10), p. 48.

`rotationSubgroup n` is `K = {(0, k)}`. Prove:
- **The spherical functions of `(M(n), SO(n))`** (`isSphericalFunction_motion_iff`): for `n ≥ 2`
  and the Haar probability measure of `K`, the spherical functions in the sense of
  SpecialFunctionsGroupModels §5.2 are exactly the `φ_λ`, `λ ∈ ℂ`;
- **The parameter is determined up to sign** (`motionSphericalFunction_inj`):
  `φ_λ = φ_μ` exactly when `λ² = μ²`;
- **Bounded spherical functions** (`bounded_besselZonal_iff`): `Ω_n(λ, ·)` is bounded on
  `[0, ∞)` exactly for real `λ`, and then by `1`;
- the bounded spherical functions are the positive-definite ones, and the spherical transform of
  a radial `f(a) = φ(|a|)` is `|S^{n−1}| ∫₀^∞ φ(r) Ω_n(λ, r) r^{n−1} dr`, the radial Fourier
  transform of 5.3 at `λ = 2π|ξ|`;
- **The zonal matrix element of `T_R` is the spherical function**
  (`matrixElement_circleRep_zero_zero`) at `n = 2`: `D_{00}(g) = Ω₂(R, |a|)`.

Route: `φ_λ` is spherical by 6.1, since `∫_K e^{iλ⟨a + k b, ξ⟩} dk` averaged over `ξ` factors; a
spherical function is bi-`K`-invariant, so it is `F(|a|)`, and it is an eigenfunction of the
Laplacian (the Casimir), so `F` solves the radial equation of 6.1 and is regular at `0`; the
solution space regular at `0` with `F(0) = 1` is `{Ω_n(λ, ·)}` for `−λ²` the eigenvalue
(Dieudonné p. 57 for `n = 2`; "in the same way" for `n ≥ 3`).

**Checks.**
- At `n = 3`, `λ = 1.4`, `|a| = 0.8`, `|b| = 1.9`, the functional equation reads
  `(1/2) ∫₀^π Ω₃(λ, √(a² + b² + 2ab cos θ)) sin θ dθ = Ω₃(λ, a) Ω₃(λ, b) = 0.13994 31600`.
- At `n = 4` with the weight `(2/π) sin² θ` both sides are `0.29031 44269`.
- Negative control: at `n = 1`, `K` is trivial and `Ω₁(λ, a) = cos(λa)` is the sphere mean but not
  spherical: `cos(1.3) = 0.26749 88286 ≠ cos(0.5) cos(0.8) = 0.61141 76589`; the theorem needs
  `n ≥ 2`.

*Needs:* 6.1, 1.2; SpecialFunctionsGroupModels §§5.1–5.2.

### 6.3 The plane-wave expansion in `ℝ³`

Sources: Vilenkin–Klimyk Vol. 2 §9.3.3 (3), pp. 48–49; DLMF 10.60.7 and 14.30.9.

Prove:
- **Plane-wave expansion in `ℝ³`** (`hasSum_planeWave_sphericalHarmonic`): for `κ, r > 0`,
  `e^{i⟨κ k̂, r x̂⟩} = 4π Σ_l i^l j_l(κr) Σ_m Y_l^m(k̂) conj Y_l^m(x̂)` with
  `j_l(z) = √(π/(2z)) J_{l+1/2}(z)` and SpecialFunctionsSU2MatrixElements' `Y_l^m`;
- for general `n ≥ 2` the zonal form
  `e^{iz cos α} = Γ(ν)(z/2)^{−ν} Σ_k (ν + k) i^k J_{ν+k}(z) C_k^ν(cos α)`, `ν = n/2 − 1`, is
  DLMF 10.23.9 of SpecialFunctionsBessel 4.3; at `n = 3` it is the plane-wave expansion 10.60.7
  of its 11.5, and the first bullet follows from it by the addition theorem of spherical harmonics
  (SpecialFunctionsSU2MatrixElements §6.3).

**Checks.**
- At `k = (0.9, 0.4, 1.2)`, `x = (−0.3, 0.7, 0.5)` both sides are `0.81964 80178 + 0.57286 74601 i`
  (30 terms).
- At `x̂ = k̂` the inner sum is `(2l + 1)/(4π)`, and the expansion is
  `e^{iz} = Σ (2l + 1) i^l j_l(z)`.
- Negative control: without the factor `i^l` the sum is real, `0.98765 73120` at the first
  Check.

*Needs:* SpecialFunctionsSU2MatrixElements §§6.1, 6.3; SpecialFunctionsBessel 4.3, 11.5.

### Dependencies

Layers 1, 5; SpecialFunctionsGroupModels §§5.1–5.2; SpecialFunctionsSU2MatrixElements §§6.1,
6.3; SpecialFunctionsBessel 4.3, 11.5.

## Layer 7: contraction to the motion groups

### 7.1 Wigner's `d`-functions

Sources: Vilenkin–Klimyk Vol. 2 §9.3.4, p. 51 (the contraction of `SO(n)` to `ISO(n − 1)`);
Edmonds (4.1.15), p. 57, and (4.1.23), through SpecialFunctionsSU2MatrixElements §§2.3–2.4;
DLMF 18.11.5.

Prove:
- **Contraction of Wigner's `d`-functions** (`tendsto_wignerSmallD_besselJ`): for fixed integers
  `p, q` and real `x`, `d^l_{pq}(x/l) → J_{p−q}(x)` as `l → ∞`;
- at `p = q = 0` this is the Mehler–Heine limit `P_l(cos(x/l)) → J₀(x)` through
  SpecialFunctionsSU2MatrixElements §2.6.

Route: the Jacobi form of `d^l_{pq}` of SpecialFunctionsSU2MatrixElements §2.4 (Edmonds
(4.1.23)), with Mehler–Heine for Jacobi polynomials of fixed integer parameters (DLMF 18.11.5),
proved from the finite sum by dominated convergence; the sign for `p < q` is that of
`J_{p−q} = (−1)^{p−q} J_{q−p}`.

**Checks.**
- At `x = 1.7`, `d^{800}_{0,0}(1.7/800) = 0.39737 10368` and `J₀(1.7) = 0.39798 48594`.
- `d^{800}_{1,0}(1.7/800) = 0.57782 69529`, `J₁(1.7) = 0.57776 52315`;
  `d^{800}_{0,1}(1.7/800) = −0.57782 69529`.
- `d^{800}_{2,−1}(1.7/800) = 0.08528 95484`, `J₃(1.7) = 0.08514 99269`.
- Negative control: `J_{q−p}` in place of `J_{p−q}` has the wrong sign at `(p, q) = (1, 0)`.

*Needs:* SpecialFunctionsSU2MatrixElements §§2.3–2.4, 2.6.

### 7.2 Gegenbauer polynomials

Sources: Vilenkin–Klimyk Vol. 2 §9.3.4 (3)–(4), p. 51, with §9.3.3 (1), (3), pp. 48–49.

Prove:
- **Contraction of zonal functions** (`tendsto_gegenbauerC_besselJ`): for `Re p > 0`, `r > 0`,
  `(l!/Γ(2p + l)) C_l^p(cos(r/l)) → √π J_{p−1/2}(r) / ((2r)^{p−1/2} Γ(p))`;
- equivalently `C_l^p(cos(r/l))/C_l^p(1) → Ω_{2p+1}(1, r)`, by `C_l^p(1) = Γ(2p + l)/(l! Γ(2p))`
  and Legendre's duplication formula; at `p = (n − 1)/2` this is the contraction of the
  normalized zonal spherical functions of `SO(n + 1)` to those of `(M(n), SO(n))` (6.2).

**Checks.**
- At `p = 1.5`, `r = 2.2` the left side is `0.24098 12503`, `0.25123 09552`, `0.25251 29826` at
  `l = 50, 400, 3000`, and the limit is `0.25271 04772 = Ω₄(1, 2.2)/Γ(3)`.
- At `p = ½`, `C_l^{1/2} = P_l` and the limit is `J₀(r)`, 7.1 at `p = q = 0`.
- Negative control: without the factor `l!/Γ(2p + l)` the left side grows like `l^{2p−1}`.

*Needs:* LaguerreJacobi (Gegenbauer polynomials); SpecialFunctionsBessel 4.3.

### Dependencies

SpecialFunctionsSU2MatrixElements §§2.3–2.4, 2.6; LaguerreJacobi; Layer 6.

## Downstream consumers

- The sibling roadmaps of the same project on spheres in higher dimension (the plane-wave
  expansion in `ℝⁿ` with spherical harmonics of `S^{n−1}`) and on rank-one symmetric spaces (the
  flat limit of the Jacobi functions).

## Beyond this roadmap (a roadmap for a roadmap; do not implement)

The following material lies outside this roadmap. It is recorded only to fix the boundary.
Contributors should not attempt it under this roadmap.

- **The other kernels of `ISO(1,1)`**: the translations `((0, ±r), 0)` and `((±1, ±1), 0)`, whose
  operators in the Laplace realization are Gamma-function kernels and, for `Re R = 0`, Hankel-
  function kernels (Vilenkin–Klimyk §4.2.4, from p. 176 on), and the resulting addition theorems
  for `K_ν` and `H_ν`.
- **The quasi-regular representation of `ISO(1,1)`** and its sector transforms (Vilenkin–Klimyk
  §4.4.3 ff., from p. 198).
- **Kontorovich–Lebedev and Mellin forms** of these transforms, and the Neumann/Struve and
  Meijer transforms of Vilenkin–Klimyk Vol. 2 §10.2.6 (8)–(12), p. 187.
- **The representations of `ISO(n)` for `n ≥ 3`** on `L²(S^{n−1})` with their matrix elements
  (Vilenkin–Klimyk Vol. 2 §9.2.4 and Ch. 10), which need the spherical harmonics of the sibling
  roadmap on spheres.
- **Contraction of representations** (operator convergence of `T^l(g(x/l))` to `T_R(g)`) beyond
  the matrix-element limits of Layer 7, and the contraction of `SO₀(n, 1)` (Vilenkin–Klimyk Vol. 2
  §9.3.4 (4), p. 51).

## Prior formalization

[lean-SFVK](https://github.com/bjbraams/lean-SFVK) (Apache-2.0) is the same author's project on
special functions and group representations. Its modules `SFVK/MotionGroups/Basic/Group.lean`,
`SFVK/MotionGroups/Basic/CircleModel.lean`, `SFVK/MotionGroups/Basic/Miller.lean`,
`SFVK/MotionGroups/Basic/Hyperbola.lean`, `SFVK/MotionGroups/Basic/Zonal.lean` and the theorem
modules `SFVK/MotionGroups/Polar.lean`, `SFVK/MotionGroups/CircleModel.lean`,
`SFVK/MotionGroups/MatrixElements.lean`, `SFVK/MotionGroups/Addition.lean`,
`SFVK/MotionGroups/Miller.lean`, `SFVK/MotionGroups/Hyperbola.lean`,
`SFVK/MotionGroups/Hankel.lean`, `SFVK/MotionGroups/Spherical.lean` and
`SFVK/MotionGroups/Contraction.lean` state the definitions and targets of this roadmap, mostly
with the names used here, with each conjunction split into one lemma per fact and with
lean-DLMF's Gegenbauer, Laguerre, spherical Bessel and spherical harmonic functions in place of
the local copies; the definitions there carry no `sorry`, and most theorems are open. This roadmap
specifies the mathematics intrinsically; lean-SFVK supplies implementation references, and reused
code carries attribution under the repository's porting guidance.

## References

- J. Dieudonné, *Special Functions and Linear Representations of Lie Groups*, CBMS Regional
  Conference Series in Mathematics 42, AMS, 1980, §16.
- A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press, 1957
  (reprinted 1996), §4.1 (the Euler-angle conventions of Wigner's `d`).
- W. Miller, Jr., *Lie Theory and Special Functions*, Mathematics in Science and Engineering 43,
  Academic Press, 1968, Ch. 3, §§3-1–3-8.
- N. Ja. Vilenkin and A. U. Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 1,
  Mathematics and Its Applications (Soviet Series) 72, Kluwer, 1991, Ch. 4.
- N. Ja. Vilenkin and A. U. Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2,
  Mathematics and Its Applications (Soviet Series) 74, Kluwer, 1993, §§9.1.8, 9.3, 10.2.6.
- NIST Digital Library of Mathematical Functions, https://dlmf.nist.gov, §§10.9, 10.23, 10.32,
  10.60, 14.30, 18.11.
