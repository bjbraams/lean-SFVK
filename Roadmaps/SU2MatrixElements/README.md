# Roadmap: matrix elements of SU(2) and SO(3), Jacobi and Legendre functions

## Summary

The irreducible unitary representations of SU(2) are the symmetric powers `Sym^d ℂ²`, `d ≥ 0`.
In a weight basis and in Euler angles their matrix elements are Wigner's functions
`D^j_{m'm}(α, β, γ) = e^{im'α} d^j_{m'm}(β) e^{imγ}` of spin `j = d/2`. The reduced functions
`d^j_{m'm}` are Jacobi polynomials with integral parameters, times powers of `sin(β/2)` and
`cos(β/2)`. Legendre polynomials, Ferrers functions, spherical harmonics, the Chebyshev polynomials
of the second kind and the Krawtchouk polynomials are special cases or reorganizations of them.

This roadmap builds the matrix elements on top of Tau Ceti's SU(2) and compact-group development,
in the convention of Edmonds [E]. It derives the classical identities from the group structure:
- the addition and product formulas from the homomorphism property;
- orthogonality from Schur;
- the differential equation and recurrences from the Lie-algebra action;
- the Krawtchouk orthogonality from unitarity;
- harmonic analysis on `S²` from the double cover `SU(2) → SO(3)`.

The development is organized by the structure of the subject: coordinates and the unitary model;
the matrix elements and their closed forms; what follows from the group law; what follows from the
Lie algebra; characters and the column index; the homogeneous space `S² = SO(3)/SO(2)`.

It draws on:
- Edmonds [E, §1.3, Ch. 2, §§4.1–4.2, 4.6], whose convention it adopts;
- Vilenkin and Klimyk [VK, §§6.1–6.3, 6.6–6.10], through one stated conversion theorem;
- the survey of Klimyk and Vilenkin [KV, §2.2];
- Wawrzyńczyk [W, Ch. 8], Dieudonné [D, §2] and Miller [M68, §5-16].

## Scope and ownership

The roadmap is complete when Tau Ceti proves every statement of `Suggested.lean` and the prose
targets of the layers below.

Inputs:
- Tau Ceti's SU(2) development: the models `Sym^d`, the weight basis, irreducibility and
  exhaustion, characters, Weyl integration, and the double cover `SU(2) → SO(3)`.
- Its compact-group development: normalized Haar measure, Schur orthogonality, Peter–Weyl.
- Mathlib's Chebyshev polynomials, shifted Legendre polynomials and Gauss series.
- The Jacobi polynomials of the LaguerreJacobi roadmap (§3.2), on main.

Owned here:

- Euler angles on SU(2) and SO(3), and the Haar measures in Euler angles;
- the invariant inner product on `Sym^d ℂ²`, the unitary model and the matrix elements `D^j`;
- the functions `d^j_{m'm}` with their closed forms, symmetries and special values;
- the conversion from the convention of Vilenkin and Klimyk;
- the addition, product and orthogonality theorems, and Plancherel in coordinates;
- the infinitesimal operators, the Casimir and Laplacian in Euler angles, the differential
  equation, recurrences and generating function;
- characters as Chebyshev polynomials;
- matrix elements as Krawtchouk polynomials, with a local Krawtchouk polynomial;
- spherical harmonics on `S²` as matrix elements, with their orthonormality, completeness, rotation
  law and addition theorem;
- the Gel'fand pair (SU(2), T), which is (SO(3), SO(2)) lifted to the double cover.

Not owned:

- the general matrix element of a unitary representation in a Hilbert basis: the planned
  function-space-models roadmap of lean-SFVK (Roadmap 2 of its plan) owns it as
  SFVK.FunctionSpaceModels.matrixElement, and `matrixElement` here is its instance for SU(2), the
  unitary model and the standard basis;
- tensor products and Clebsch–Gordan coefficients (planned Roadmap 3);
- SU(1,1) and Jacobi functions of non-integral degree (planned Roadmap 7);
- SO(n) for `n > 3` (planned Roadmap 5);
- the Jacobi, Legendre and Gegenbauer polynomials as such (LaguerreJacobi, §§3, 6);
- the Ferrers functions of general order and degree (the DLMF 14 roadmap SpecialFunctionsLegendre,
  in review);
- the Gauss function on the cut plane (SpecialFunctionsHypergeometric, on main).

Boundary in one sentence: everything that needs the group SU(2) or SO(3) is here; everything that
is a fact about one polynomial family alone is the supplier's.

## Conventions

The convention is that of Edmonds [E], chosen so that every displayed formula of [E, §§4.1–4.2]
holds verbatim for a genuine left representation of SU(2).

- `SU2` is Tau Ceti's `Matrix.specialUnitaryGroup (Fin 2) ℂ`.
- Spin `j = d/2` with `d : ℕ`. The basis index is `i : Fin (d + 1)` with magnetic quantum number
  `m = i - d/2` (`edWeight`). Edmonds's order `m = j, j - 1, …, -j` is `i = d, d - 1, …, 0`.
  The index `i` is that of Tau Ceti's `TauCeti.SU2.weightBasis`, whose `i`-th vector is
  `z₁^i z₂^{d-i}`. Its Tau Ceti weight `2i - d` is `2m`, so no reindexing against Tau Ceti is
  needed.
- The action is `T(g) f(z₁, z₂) = f(g₀₀z₁ + g₁₀z₂, g₀₁z₁ + g₁₁z₂)`, which is Tau Ceti's `Sym^d`
  under `e₀ ↦ z₁`, `e₁ ↦ z₂`.
- The invariant norm of `z₁^i z₂^{d-i}` is `√(i!(d-i)!)` (`monomialNorm`). The orthonormal basis
  is `u(j, m) = z₁^{j+m} z₂^{j-m} / √((j+m)!(j-m)!)`, Edmonds's spinor realization
  [E, §4.1, p. 56]. At `j = 1/2`, `u(1/2, 1/2)` is the first standard basis vector of `ℂ²`.
- The matrix element is `D^j_{m'm}(g) = ⟪e_{m'}, T^j(g) e_m⟫` [E, (4.1.10), p. 55]. Tau Ceti's
  matrix coefficient `g ↦ ⟪π g v, w⟫` is the only primitive: `matrixElement d i k g` is the
  conjugate of `ContRepresentation.matrixCoeff` at `v = e_k`, `w = e_i`, with `m' = i - d/2` and
  `m = k - d/2`. Mathlib's inner product is conjugate-linear in the first argument.
- Euler angles. Edmonds writes the operator of `(α, β, γ)` as
  `exp(iαJ_z) exp(iβJ_y) exp(iγJ_z)` [E, (4.1.9), p. 55], with `ħ = 1`.
- The group element of `(α, β, γ)` is the spin-one-half value of that operator:
  `eulerD α β γ = g_α b_β g_γ`. Here `g_α = diag(e^{iα/2}, e^{-iα/2})`, which is
  `TauCeti.SU2.torusExp (α/2)`, and `b_β = [[cos(β/2), sin(β/2)], [-sin(β/2), cos(β/2)]]`
  (`bBeta`) is Edmonds's `exp(iβJ_y)` [E, (4.1.13), p. 56].
- With these choices `D^j_{m'm}(eulerD α β γ) = e^{im'α} d^j_{m'm}(β) e^{imγ}`
  [E, (4.1.12), p. 55], for all real `α, β, γ`. The real function `d^j_{m'm}` is Edmonds's
  finite sum [E, (4.1.15), p. 57] (`smallD`). Since `matrixElement` comes from
  `TauCeti.SU2.symPowerModel` by transport, `T(gh) = T(g) T(h)`.
- These formulas were verified symbolically (sympy) at `j = 1/2` and `j = 1` against the printed
  matrices [E, (4.1.13), p. 56; p. 57]. The homomorphism property was verified for generic
  `2 × 2` matrices.
- Edmonds's angles range over `0 ≤ α < 2π`, `0 ≤ β < π`, `0 ≤ γ < 2π` for rotations
  [E, §1.3, p. 7]. On SU(2) one angle needs a range of length `4π`, since
  `eulerD α β (γ + 2π) = -eulerD α β γ`. The SU(2) box is therefore `0 ≤ α < 2π`, `0 < β < π`,
  `-2π ≤ γ < 2π` (`eulerBox`).
- Rotations. Tau Ceti's double cover `TauCeti.SU2.toSO3` (the action on Pauli coordinates) sends
  `g_α` to `R_z(-α)` and `b_β` to `R_y(-β)`. Hence
  `toSO3 (eulerD α β γ) = R_z(-α) R_y(-β) R_z(-γ)`.
- Edmonds describes `D(αβγ)` as the operator of the rotation of the coordinate frame
  [E, §4.1, p. 53]. In fixed axes that frame rotation is `R_z(α) R_y(β) R_z(γ)` [E, §1.3, p. 8].
  The rotation of `eulerD α β γ` under `TauCeti.SU2.toSO3` is the inverse of the frame rotation
  with `α` and `γ` exchanged, `(R_z(γ) R_y(β) R_z(α))⁻¹`. This roadmap attaches the group element
  `eulerD α β γ` to `(α, β, γ)`, so that Edmonds's formulas hold verbatim. It does not use the
  frame-rotation reading.
- `d^j` is defined for every real `β`, with no square roots, so no statement needs a range of `β`
  except where `sin β` or `sin(β/2)` is divided by.
- Spherical harmonics: Edmonds's `Y_{lm}` [E, (2.5.5), p. 21; (2.5.29), p. 24] equals DLMF's
  `Y_l^m` (14.30.1). Edmonds's associated Legendre function [E, (2.5.10), p. 22; (2.5.17),
  p. 23] has no Condon–Shortley factor: `P_l^m(Edmonds) = (-1)^m P_l^m(DLMF)`. Edmonds puts the
  `(-1)^m` into `Y_{lm}`, and DLMF puts it into the Ferrers function. This was checked numerically
  for `l ≤ 3`. `sphericalHarmonic` is DLMF's `Y_l^m` as a polynomial on `ℝ³`.
- The surface measure on `S²` is `MeasureTheory.Measure.toSphere` of Lebesgue measure, of total
  mass `4π`.
- Vilenkin–Klimyk. Their basis `ψ_n = z₁^{l-n} z₂^{l+n}/√·` is `e_i` with `n_VK = d/2 - i = -m`.
  Their Euler element is `u(φ, θ, ψ) = g_φ a_θ g_ψ` with
  `a_θ = [[cos(θ/2), i sin(θ/2)], [i sin(θ/2), cos(θ/2)]]`.
- Hence `t^{VK}_{mn} = D_{-m,-n}` and `u(φ, θ, ψ) = eulerD (φ + π/2) θ (ψ - π/2)`, and VK's real
  function is `P^l_{mn}(cos θ) = d^l_{mn}(θ)` (`vk_conversion`). Locators of VK below refer to
  VK's convention and are transported by this theorem.

## Exact supplier contracts

### From Tau Ceti (pin 396c3bd)

- `TauCeti.SU2.symPowerModel` is the continuous model of `Sym^d` on
  `EuclideanSpace ℂ (Fin (d+1))` in the weight basis, with:
  - `TauCeti.SU2.continuous_symPowerModel`;
  - `TauCeti.SU2.isIrreducible_symPowerModel`;
  - `TauCeti.SU2.existsUnique_nonempty_equiv_symPower` (every continuous irreducible
    representation is some `Sym^d`, uniquely).

  The model is not unitary for `d ≥ 2`; the unitary model of Layer 1 is its transport by `scale`.
- `TauCeti.SU2.torusExp` and `TauCeti.SU2.torus`.
- `TauCeti.SU2.toSO3` with `TauCeti.SU2.coe_toSO3_torusHom`, `TauCeti.SU2.toSO3_surjective` and
  `TauCeti.SU2.ker_toSO3`.
- `TauCeti.SU2.character_symPower_eq_chebyshevU_eval` (the character of `Sym^d` is
  `U_d(tr g / 2)`) and `TauCeti.SU2.weyl_integration_formula`.
- `TauCeti.haarProb`.
- `ContRepresentation.matrixCoeff`, `ContRepresentation.IsUnitary` and
  `ContRepresentation.schur_orthogonality`.
- `TauCeti.IrrepModel`, `TauCeti.IsIrrepSkeleton`, and `TauCeti.peterWeylBasis` with
  `TauCeti.coe_peterWeylBasis`.
- `ContinuousLinearEquiv.congr` and `ContinuousLinearEquiv.continuous_congr`: transport of a
  representation along a continuous linear equivalence.
- Layer 4 consumes in prose the differential of `Sym^d` and the identification of the Lie algebra
  of SU(2) with that of SO(3), from Tau Ceti's SU2 Differential and StandardBasis modules.

### From Mathlib (pin 1b1ccf4)

- `Polynomial.shiftedLegendre`, so that `P_l(z)` is its value at `(1 - z)/2` (`legendrePoly`).
- `Polynomial.Chebyshev.U`, `ordinaryHypergeometric` and `ascPochhammer`.
- `MeasureTheory.Measure.toSphere` and `Laplacian.laplacian`.

### From the LaguerreJacobi roadmap (on main)

- §3.2: the Jacobi polynomial over a `ℚ`-algebra, by the explicit DLMF 18.5.8 sum. Its
  normalization `P_n^{(a,b)}(1) = C(n+a, n)` is Edmonds's (4.1.17) [E, p. 58]. `Suggested.lean`
  carries a verbatim local copy, `jacobi`, whose docstring names the owner.
- Layers 2 and 3 consume §3.3 (reflection, derivative), §3.4 (Rodrigues) and §4.3
  (orthogonality, with the norm sequence of Edmonds's (4.1.22)).
- §6 supplies the Legendre and Gegenbauer specializations.

### Planned or in review (prose only)

- SpecialFunctionsLegendre (DLMF 14, in review) owns the Ferrers functions `P_l^m` on `(-1, 1)`.
  Layer 2 states the integral-order case through derivatives of `P_l`, and that roadmap's
  definition must match it.
- No DLMF 18 Hahn-class roadmap (Krawtchouk, Meixner) exists. `krawtchouk` is owned here until one
  does.

## How to read the build

Each layer lists its targets as bold headlines with their Lean names, a proof route, a `*Needs:*`
line and Checks. A headline restated from a source carries a locator; corollaries carry a route.
Layers 1 and 2 are the foundation. Given Layer 2, Layers 3–6 are independent of each other, except
that Layer 6 uses the addition theorem of Layer 3.

## Layer 1: coordinates and the unitary model

Sources:
- [E, §1.3, pp. 6–8; (4.1.8)–(4.1.13), pp. 55–56];
- [VK, §6.1.1, p. 269; §6.1.4, p. 275, (1); §6.2.3, pp. 278–280], in VK's convention;
- [W, (8.3.4), p. 291];
- [D, §2 (22)–(28), pp. 6–7].

- **The Euler matrix** (`coe_eulerD`). The entries of `eulerD α β γ` are
  `cos(β/2) e^{±i(α+γ)/2}` on the diagonal, and `sin(β/2) e^{i(α-γ)/2}` and
  `-sin(β/2) e^{-i(α-γ)/2}` off it. Route: multiply out.
- **Euler angles cover SU(2), and are a bijection on the generic set**
  (`exists_eulerD_eq_and_bijOn`).
  - Every `g` is `eulerD α β γ` with `β ∈ [0, π]`.
  - On `eulerBox` the map is a bijection onto `{g₀₀ g₀₁ ≠ 0}`.
  - This is [E, §1.3, p. 7, footnote 5] for SO(3), and [VK, §6.1.1, p. 269, (2)–(3)] in VK's
    convention.
  - Route: `|g₀₀| = cos(β/2)` determines `β`. `arg g₀₀` and `arg g₀₁` determine `(α ± γ)/2`
    modulo `2π`. The `γ`-range of length `4π` separates `g` from `-g`.
- **Euler angles on SO(3)** (`toSO3_eulerD`).
  - `R(eulerD α β γ) = R_z(-α) R_y(-β) R_z(-γ)`.
  - Every rotation has this form with `γ ∈ [0, 2π)`.
  - Route: `TauCeti.SU2.coe_toSO3_torusHom` for the outer factors, a direct Pauli computation for
    `b_β`, then `TauCeti.SU2.toSO3_surjective`.
- **Haar measure in Euler angles** (`haarProb_eq_map_eulerMeasure`).
  - The normalized Haar measure is the image of `eulerMeasure = (16π²)⁻¹ sin β dα dβ dγ` on the
    box, and every Haar-integrable function integrates accordingly.
  - Sources: [VK, §6.1.4, p. 275, (1)]; [W, (8.3.4), p. 291]. Edmonds's (4.6.1) [E, p. 62]
    integrates over `γ ∈ [0, 2π]` with `(8π²)⁻¹`, which is the SO(3) form.
  - Route: the image measure is a probability measure, because `∫ sin β` over the box is `16π²`.
    It is left invariant: left multiplication acts on the first row `(g₀₀, g₀₁) ∈ S³ ⊂ ℂ²` by a
    unitary map preserving the surface measure, and the Euler angles are spherical coordinates on
    `S³`. Conclude by uniqueness of Haar measure.
  - As a consistency check, not part of the statement: on class functions it agrees with
    `TauCeti.SU2.weyl_integration_formula`.
- **Haar measure of SO(3)** (`map_toSO3_haarProb`). Route: the image of a Haar probability measure
  under a continuous surjective homomorphism of compact groups is the Haar probability measure.
- **The invariant inner product** (`isUnitary_unitaryModel`).
  - The transport `unitaryModel d` of `TauCeti.SU2.symPowerModel` by `scale` is unitary and
    irreducible.
  - Sources: [E, §4.1, p. 56]; [VK, §6.2.3, pp. 278–279]; [D, §2 (22)–(23), p. 6].
  - Route: unitarity on the generators `g_α` (diagonal) and `b_β`, or by the explicit sum of
    Layer 2 and `matrixElement_mul_inv`.
  - Irreducibility follows by `ContinuousLinearEquiv.congr` from
    `TauCeti.SU2.isIrreducible_symPowerModel`.
- **The unitary dual of SU(2)** (`isIrrepSkeleton_irrepModel`). The `irrepModel d` form a skeleton
  of the continuous unitary irreducible representations. Route:
  `TauCeti.SU2.existsUnique_nonempty_equiv_symPower`, then the standard fact that two equivalent
  unitary irreducible representations are unitarily equivalent (Schur).
- **The representation of SO(3)** (second conjunct of `matrixElement_torusExp_pi_mul`). For even
  `d` the unitary model factors through `TauCeti.SU2.toSO3`. This is because
  `-1 = torusExp π` acts by `(-1)^d`, and `TauCeti.SU2.ker_toSO3` is the centre.

*Needs:* Tau Ceti's SU(2) and Haar development; nothing from other roadmaps.

**Checks.**

- `ofPair 1 0 = 1`.
- `ofPair α β` has determinant `|α|² + |β|² = 1`.
- Negative control: `[[α, β], [conj β, conj α]]` (sign of the lower-left entry dropped) has
  determinant `|α|² - |β|²`, which is not `1` when `β ≠ 0`; it is not in SU(2).
- `bBeta 0 = 1`.
- `bBeta β * bBeta β' = bBeta (β + β')`.
- `bBeta π = [[0, 1], [-1, 0]]`, Edmonds's `exp(iπJ_y)` at spin one half.
- Negative control: `bBeta (2π) = -1`, not `1`.
- `eulerD α 0 0 = torusExp (α/2)`.
- `eulerD 0 β 0 = bBeta β`.
- `(eulerD α β γ)⁻¹ = eulerD (-γ) (-β) (-α)`.
- Negative control: `eulerD (2π) 0 0 = -1`, not `1`; this is why `γ` ranges over an interval of
  length `4π`.
- `∫ sin β` over `eulerBox` is `2π · 2 · 4π = 16π²`.
- The volume of `eulerBox` is `8π³`.
- Negative control: with Edmonds's SO(3) range `γ ∈ [0, 2π)` the same density has mass `1/2`,
  because the half box covers only one of `±g`.
- `rotZ a * rotZ b = rotZ (a + b)`.
- `rotZ (π/2)` sends `e₁` to `e₂` (counterclockwise).
- Negative control: `toSO3 (torusExp (α/2)) = rotZ (-α)`, not `rotZ α`
  (`TauCeti.SU2.coe_toSO3_torusHom`).
- `rotY (π/2)` sends `e₃` to `e₁`.
- `rotY a * rotY b = rotY (a + b)`.
- Negative control: `toSO3 (bBeta β) = rotY (-β)`, not `rotY β`; they differ at `β = 1.1` by
  `1.78` in the maximum entry.
- `eulerMeasure` has total mass `1`.
- Its density is nonnegative, since `sin β > 0` on `(0, π)`.
- Negative control: without the density `sin β` the mass is `8π³/16π² = π/2`.
- `edWeight 1 1 = 1/2`.
- `edWeight 2 1 = 0`.
- `edWeight d i + edWeight d (d - i) = 0`.
- Negative control: `vkWeight d i = -edWeight d i`; using VK's weight in `matrixElement_eulerD`
  conjugates the phases `e^{im'α}`.
- `monomialNorm 1 i = 1` for both `i`.
- `monomialNorm 2 0 = √2`.
- Negative control: for `d = 2` the standard basis of `TauCeti.SU2.symPowerModel` is not
  orthonormal for the invariant product. For `aTheta 0.7`, the matrix `M` of
  `symPowerModel 2 (aTheta 0.7)` has `‖M*M - 1‖ = 0.68`.
- `scale 0` and `scale 1` are the identity.
- `scale 2` multiplies `e₀` and `e₂` by `√2` and fixes `e₁`.
- `scale d` is diagonal with positive entries, so it commutes with the torus action.
- Negative control: transport by the inverse scaling is not unitary for `d = 2`. For
  `aTheta 0.7` the transported matrix `M` has `‖M*M - 1‖ = 1.66`.
- `unitaryModel 0` is the trivial representation.
- `unitaryModel 1 g` is the matrix of `g` in Edmonds's order `m = 1/2, -1/2` (`matrixElement_one`).
- Negative control: `unitaryModel 2` is unitary while `TauCeti.SU2.symPowerModel 2` is not.
- `(irrepModel d).dim = d + 1`.
- `irrepModel 0` is the trivial one-dimensional model.
- `irrepModel 1` and `irrepModel 2` are inequivalent: their characters at `-1` are `-2` and `3`.
- Negative control: a model built on `TauCeti.SU2.symPowerModel 2` directly fails the
  unitarity field.

## Layer 2: matrix elements and their closed forms

Sources:
- [E, (4.1.10)–(4.1.27), pp. 55–59; (4.2.1)–(4.2.7), pp. 59–60; (2.5.5)–(2.5.30), pp. 21–24];
- in VK's convention, [VK, §6.3.1, p. 280, (3); §6.3.3, pp. 284–285; §6.3.6, pp. 287–288;
  §6.3.7, p. 289];
- [KV, p. 178, (19), (19a), (20), (21)];
- [D, §2 (32)–(37), p. 7] and [M68, §5-16, p. 219].

- **The matrix element** (`matrixElement`, `unitaryModel_single`).
  `T(g) e_m = Σ_{m'} D_{m'm}(g) e_{m'}` [E, (4.1.5), p. 54].
- **The explicit polynomial formula** (`matrixElement_eq_entrySum`).
  - `D` is a polynomial in the four entries of `g`, with the coefficients of `entrySum`.
  - It is the binomial expansion of the action on monomials, which is Edmonds's spinor
    computation [E, p. 56] and [VK, §6.3.1, p. 280, (3)] in VK's indices.
  - Route: expand `(g₀₀z₁ + g₁₀z₂)^k (g₀₁z₁ + g₁₁z₂)^{d-k}` and normalize.
- **Spin one half is the defining representation** (`matrixElement_one`) [E, (4.1.13), p. 56].
- **The group law** (`matrixElement_mul_inv`).
  - `D(gh) = D(g) D(h)` as matrices.
  - `D_{m'm}(g⁻¹) = conj D_{mm'}(g)`.
  - Both unitarity relations hold.
  - Sources: [E, §4.2, p. 60]; [M68, §5-16, p. 219].
  - Route: homomorphism and unitarity of `unitaryModel`.
- **The centre and the passage to SO(3)** (`matrixElement_torusExp_pi_mul`); compare
  [E, (4.2.1), p. 59] on `D(π)D(π) ≠ D(0)` for half-integral `j`.
- **Matrix elements in Euler angles** (`matrixElement_eulerD`).
  `D^j_{m'm}(eulerD α β γ) = e^{im'α} d^j_{m'm}(β) e^{imγ}` for all real angles [E, (4.1.12),
  p. 55; (4.1.15), p. 57]. Route: factor, use the diagonal action of `g_α` and `g_γ`, and compare
  `entrySum` at `b_β` with the sum (4.1.15).
- **The Jacobi form** (`smallD_eq_jacobi`).
  - `d^j_{m'm}(β) = ± √(κ!(d-κ)!/((κ+a)!(κ+b)!)) sin(β/2)^a cos(β/2)^b P_κ^{(a,b)}(cos β)`.
  - Here `a = |m' - m|`, `b = |m' + m|`, `κ = j - max(|m'|, |m|)`, and the sign is
    `(-1)^{max(m - m', 0)}`.
  - Edmonds states it for `m' - m ≥ 0`, `m' + m ≥ 0` [E, (4.1.23), p. 58]. The absolute-value
    form holds for all indices by the symmetries below; there is no factor `i^{m'-m}`.
  - Also [KV, p. 178, (19a)] and [D, §2 (33)–(35), p. 7], each in its own convention.
- **The hypergeometric form** (`smallD_eq_hypergeometric`), from the Jacobi form and DLMF 18.5.7,
  `P_κ^{(a,b)}(cos β) = (a+1)_κ/κ! F(-κ, κ+a+b+1; a+1; sin²(β/2))` [VK, §6.3.4, p. 286].
- **Symmetries** (`smallD_symm`).
  - `d_{m'm} = (-1)^{m'-m} d_{mm'} = (-1)^{m'-m} d_{-m',-m}`;
  - `d_{m'm}(-β) = d_{mm'}(β)`;
  - `d_{m'm}(π + β) = (-1)^{j-m'} d_{-m',m}(β)`.
  - Sources: [E, (4.2.2)–(4.2.6), pp. 59–60]; in VK's convention, [VK, §6.3.6, p. 288],
    corrected per E06.3.01 and E06.7.04.
- **Values at `0` and `π`** (`smallD_zero_pi`). `d_{m'm}(0) = δ_{m'm}` and
  `d_{m'm}(π) = (-1)^{j+m} δ_{m',-m}` [E, (4.2.1), p. 59].
- **Legendre polynomials are the zonal matrix elements** (`smallD_two_mul_self`).
  `D^l_{00}(αβγ) = P_l(cos β)` [E, (4.1.26), p. 59; KV, p. 178, (21); D, §2 (36), p. 7].
- **Associated Legendre functions** (`smallD_eq_ferrers`).
  - For `0 ≤ n ≤ l`, `d^l_{n0}(β) = √((l-n)!/(l+n)!) sin^n β P_l^{(n)}(cos β)` for all `β`. This
    is Edmonds's `√((l-n)!/(l+n)!) P_l^n(cos β)` [E, (4.1.24), p. 59] with his Ferrers function
    [E, (2.5.10), p. 22].
  - In DLMF's normalization, with the Condon–Shortley factor, it is
    `(-1)^n √((l-n)!/(l+n)!) P_l^n(cos β)` for `0 ≤ β ≤ π`.
  - In VK's convention, see [VK, §6.3.7, p. 289], corrected per E06.3.02 and E06.3.10.
- **The conversion from Vilenkin–Klimyk** (`vk_conversion`).
  - `u(φ, θ, ψ) = eulerD (φ + π/2) θ (ψ - π/2)`.
  - VK's Euler formula `t^{VK}_{mn}(u) = i^{m-n} e^{-i(mφ+nψ)} P^l_{mn}(cos θ)` [VK, §6.3.3,
    p. 285, (4)–(5); KV, p. 178, (19), after E02.2.04 and E02.2.05] holds with
    `t^{VK}_{mn} = D_{-m,-n}` and `P^l_{mn}(cos θ) = d^l_{mn}(θ)`, for all real angles.
  - Route: `a_θ = g_{π/2} b_θ g_{-π/2}` and `matrixElement_eulerD`. The phases
    `e^{∓iπ/4 · 2m}` give `i^{m-n}`, and `(-1)^{m-n} d_{-m,-n} = d_{mn}`.
- **The Gegenbauer form.** For `m = 0` the Jacobi parameters are `a = b = |m'|`, and `d^l_{m'0}`
  is a multiple of `sin^{|m'|} β C_{l-|m'|}^{(|m'|+1/2)}(cos β)`. Route: LaguerreJacobi §6.

*Needs:* Layer 1; LaguerreJacobi §3.2–3.4.

**Checks.**

- `matrixElement 0 0 0 g = 1`.
- `matrixElement 1 i k g = g (rev i) (rev k)`; for instance `D^{1/2}_{1/2,1/2}(g) = g₀₀`.
- `D^1_{00}(eulerD α β γ) = cos β` (`d = 2`, `i = k = 1`).
- Negative control: `D^{1/2}_{1/2,1/2}(torusExp t) = e^{it}`; the unconjugated matrix coefficient
  gives `e^{-it}`.
- `entrySum 1 0 0 A = A 1 1`.
- `entrySum 2 1 1 A = A₀₀A₁₁ + A₀₁A₁₀`, which on SU(2) is `|g₀₀|² - |g₀₁|² = cos β`.
- Negative control: `A₀₀A₁₁ - A₀₁A₁₀ = det A = 1` is the wrong sign combination for `D^1_{00}`.
- `smallD 1` in Edmonds's order is `[[cos(β/2), sin(β/2)], [-sin(β/2), cos(β/2)]]`
  [E, (4.1.13), p. 56].
- `smallD 2` in Edmonds's order has rows `[(1+cos β)/2, sin β/√2, (1-cos β)/2]`,
  `[-sin β/√2, cos β, sin β/√2]` and `[(1-cos β)/2, -sin β/√2, (1+cos β)/2]` [E, p. 57].
- `smallD 2 1 1 β = cos β`, and `smallD d i k (β + 4π) = smallD d i k β`.
- Negative control: read in Tau Ceti's order `i = 0, 1, 2` without the reversal to Edmonds's
  order, `smallD 2` differs from Edmonds's printed matrix by `1.11` in the maximum entry at
  `β = 0.9`.
- `legendrePoly 2 = (3X² - 1)/2`.
- `(legendrePoly l).eval 1 = 1`.
- Negative control: `shiftedLegendre l` at `(1 + z)/2` is `(-1)^l P_l(z)`; at `l = 1` it gives
  `-z`.
- `aTheta 0 = 1`, and `aTheta θ = torusExp (π/4) * bBeta θ * torusExp (-π/4)`.
- `eulerU 0 0 0 = 1`, and `eulerU φ θ ψ = eulerD (φ + π/2) θ (ψ - π/2)`.
- `vkWeight 1 0 = 1/2`.
- Negative control: VK's Euler formula without the factor `i^{m-n}` fails by `1.73` in the
  maximum entry for `d ≤ 5`; with it the error is below `10⁻²⁹`.

## Layer 3: identities from the group law

Sources:
- [E, (4.6.1), p. 62];
- in VK's convention, [VK, §6.6.1, p. 326; §6.6.2, p. 327; §6.6.3, p. 327; §6.10.1, pp. 364–365;
  §6.10.2, p. 366];
- [D, §2, p. 7], [M68, §5-16, p. 219] and [W, (8.3.4)–(8.3.6), p. 291].

- **The angle of a product** (`cos_of_eulerD_mul`).
  - If `b_{β₁} g_{α₂} b_{β₂} = eulerD α β γ`, then
    `cos β = cos β₁ cos β₂ - sin β₁ sin β₂ cos α₂`.
  - Source: [D, §2, p. 7], whose `a_θ` gives the same sign.
  - Route: `cos β = 2|g₀₀|² - 1`.
- **The addition theorem for `d^j`** (`smallD_addition`).
  `e^{i(m'α + mγ)} d_{m'm}(β) = Σ_μ e^{iμα₂} d_{m'μ}(β₁) d_{μm}(β₂)`. This is VK's [VK, §6.6.1,
  p. 326], corrected per E06.6.01, transported by `vk_conversion`. Route: `matrixElement_mul_inv`
  and `matrixElement_eulerD`.
- **The Legendre addition theorem** (`legendre_addition`).
  `P_l(cos β₁ cos β₂ - sin β₁ sin β₂ cos α) = Σ_m (-1)^m cos(mα) d^l_{m0}(β₁) d^l_{m0}(β₂)` for all
  real angles [VK, §6.6.2, p. 327]. Route: `m' = m = 0` in the addition theorem and
  `d_{0m} = (-1)^m d_{m0}`.
- **The product formula and the functional equation** (`legendre_product`).
  `P_l(cos θ₁) P_l(cos θ₂) = π⁻¹ ∫_0^π P_l(cos θ₁ cos θ₂ - sin θ₁ sin θ₂ cos φ) dφ`
  [VK, §6.6.3, p. 327], and
  `(2π)⁻¹ ∫_0^{2π} D^l_{00}(g · torusExp t · h) dt = D^l_{00}(g) D^l_{00}(h)`.
  Route: average the addition theorem over the torus; only `μ = 0` survives.
- **Schur orthogonality in coordinates** (`integral_matrixElement_mul_conj`).
  `∫ D^j_{m'm} conj D^{j'}_{n'n} = δ δ δ / (2j+1)` [E, (4.6.1), p. 62; VK, §6.10.1, pp. 364–365].
  Route: `ContRepresentation.schur_orthogonality` with `isIrrepSkeleton_irrepModel`.
- **Orthogonality of `d^j_{m'm}` for fixed `(m', m)`** (`integral_smallD_mul_smallD`).
  `∫_0^π d^j_{m'm} d^{j'}_{m'm} sin β dβ = 2/(2j+1) δ_{jj'}`. Route: the previous headline with
  `haarProb_eq_map_eulerMeasure`; the `α` and `γ` integrals give `8π²`.
- **Jacobi orthogonality for integral parameters.** Substituting the Jacobi form gives
  `∫_{-1}^1 P_κ^{(a,b)} P_{κ'}^{(a,b)} (1-z)^a (1+z)^b dz` for integers `a, b ≥ 0`. This must
  agree with [E, (4.1.22), p. 58] and LaguerreJacobi §4.3, which makes it a consistency check on
  the constants.
- **Plancherel on SU(2)** (`hasSum_plancherel`) [VK, §6.10.2, p. 366]. Route:
  `TauCeti.peterWeylBasis` for the skeleton `irrepModel` and `TauCeti.coe_peterWeylBasis`.

*Needs:* Layers 1–2.

**Checks.**

The definitions of this layer are those of Layers 1 and 2; its acceptance examples are listed
below. Numerical spot checks:
- The addition theorem holds for `d ≤ 4` at `β₁ = 0.7`, `β₂ = 2.9`, `α₂ = 0.45`, with error
  below `10⁻²⁹`.
- The Legendre addition theorem holds also at `β₁ = -1.2`, `β₂ = 4.0`.
- `∫ |D^1_{00}|² = 1/3` and `∫ |D^{1/2}_{1/2,-1/2}|² = 1/2`.

## Layer 4: the Lie-algebra action

Sources:
- [E, (4.1.6)–(4.1.9), pp. 54–55; p. 20; (2.5.9), p. 22];
- in VK's convention, [VK, §6.2.2, p. 277; §6.7.1, p. 331; §6.7.2, pp. 334–335; §6.7.5, p. 341;
  §6.10.3, p. 370];
- [W, (8.4.9)–(8.4.12), p. 297] and [M68, §5-16, p. 219].

- **The infinitesimal operators** (`hasDerivAt_matrixElement`).
  - Along `aTheta t = exp(itJ_x)`, `bBeta t = exp(itJ_y)` and `torusExp (t/2) = exp(itJ_z)`, the
    right derivatives of `D(g)` are `D(g) · iJ_k`.
  - The three matrices `i J_k` are `lieMatrix₁`, `lieMatrix₂` and `lieMatrix₃`, in Edmonds's basis
    [E, (4.1.9), p. 55].
  - Route: differentiate `entrySum`.
- **Commutation relations and the Casimir** (`lieMatrix_comm_casimir`).
  `[iJ_x, iJ_y] = -iJ_z` cyclically, and `(iJ_x)² + (iJ_y)² + (iJ_z)² = -j(j+1)`.
- **The raising and lowering operators.** `-i(lieMatrix₁ + i lieMatrix₂) = J_x + iJ_y` sends `e_m`
  to `√((j-m)(j+m+1)) e_{m+1}`, the action of Edmonds's `J₊` [E, p. 20]. Route: read off the
  matrices.
- **The differential equation** (`smallD_ode`).
  `d'' + cot β d' - (m'² + m² - 2m'm cos β)/sin² β d = -j(j+1) d` on `(0, π)`. Route: the Casimir
  applied to `D(eulerD α β γ)`. For `m = 0` it is Legendre's associated equation in `cos β`
  [E, (2.5.9), p. 22]. In VK's convention, see [VK, §6.7.5, p. 341]; also
  [W, (8.4.12), p. 297].
- **The first-order recurrence** (`hasDerivAt_smallD`). Route: the first headline at `g = b_β`.
  In VK's convention, see [VK, §6.7.2, pp. 334–335], corrected per E06.7.04; also
  [W, (8.4.10)–(8.4.11), p. 297].
- **The generating function** (`generating_function`), Edmonds's spinor identity
  [E, (4.1.14), p. 57] at `x₋ = 1`, `x₊ = w`.
- **The Casimir in Euler angles** (`casimir_eulerD`).
  - `rightField Y f g` and `leftField Y f g` are the derivatives of `f` at `t = 0` along
    `g * Y t` and `Y t * g`.
  - `rightCasimir` and `leftCasimir` sum the squares of these fields over the three
    one-parameter subgroups `aTheta`, `bBeta` and `torusExp (t/2)`. They are the Casimirs of the
    right and left regular representations, in the normalization of `lieMatrix_comm_casimir`.
  - `eulerLaplacian` is the operator
    `∂²_β + cot β ∂_β + sin⁻²β (∂²_α - 2 cos β ∂_α ∂_γ + ∂²_γ)` on functions of `(α, β, γ)`.
  - Claim: on the chart `0 < β < π`, for `f` whose pullback by `eulerD` is `C²` there, both
    Casimirs of `f` at `eulerD α β γ` equal `eulerLaplacian` of the pullback. Since the Casimir is
    central, the two agree.
  - In VK's convention, see [VK, §6.10.3, p. 370].
  - Route: write the three fields in Euler angles by solving `g Y = Σ c_i ∂_i g` (right) and
    `Y g = Σ c_i ∂_i g` (left), then square and add. This was checked symbolically (sympy) on a
    generic function `F(α, β, γ)`, for both sides.
- **Matrix elements are Casimir eigenfunctions** (`eulerLaplacian_matrixElement`).
  - `D^j_{m'm}` is an eigenfunction of `rightCasimir` and `leftCasimir` on all of SU(2), and of
    `eulerLaplacian` on the chart, with eigenvalue `-j(j+1)`.
  - Route: the right Casimir follows from `hasDerivAt_matrixElement` and the Casimir conjunct of
    `lieMatrix_comm_casimir`. The left Casimir follows by `matrixElement_mul_inv`. The coordinate
    form follows from `casimir_eulerD`, or directly from `smallD_ode`.
- **The Laplacian of SU(2) and that of `S²`** (`eulerLaplacian_sphere`, stated in Layer 6).
  - On functions independent of `γ`, `eulerLaplacian` is `sphereLaplacian` in the polar
    coordinates `(θ, φ) = (β, α)`.
  - `Y_l^m(spherePoint θ φ)` is an eigenfunction of `sphereLaplacian` with eigenvalue `-l(l+1)`
    [E, p. 22].
  - With (4.1.25) this exhibits the column `D^l_{m0}(α, β, γ) = (-1)^m √(4π/(2l+1)) Y_l^m(β, α)`
    as the lift to SU(2) of a Laplace–Beltrami eigenfunction.
  - Route: the `γ`-derivatives of a `γ`-independent function vanish. The eigenvalue follows from
    `smallD_ode` at `m = 0` and the first conjunct of `sphericalHarmonic_matrixElement`.

*Needs:* Layer 2; Tau Ceti's SU2 Differential module for the identification with `d Sym^d`.

**Checks.**

- `lieMatrix₁ 1` is `(i/2)[[0, 1], [1, 0]]`.
- `lieMatrix₁ d` is skew-Hermitian.
- Negative control: `lieMatrix₁ d` is the numerical derivative of `D(aTheta h)` at `h = 0` for
  `d ≤ 4`, with error below `10⁻²⁹`. The version without the factor `i` is Hermitian and fails.
- `lieMatrix₂ 1 = [[0, -1/2], [1/2, 0]]`. In Edmonds's order this is `[[0, 1/2], [-1/2, 0]]`,
  the derivative of `bBeta` at `0`.
- `lieMatrix₂ d` is real and skew-symmetric.
- Negative control: swapping the two off-diagonal signs gives `[iJ_x, iJ_y] = +iJ_z`, which
  contradicts the derivative check.
- `lieMatrix₃ 1 = diag(-i/2, i/2)`, which is `diag(i m)` for `m = -1/2, 1/2`.
- `lieMatrix₃ d` has trace `0`.
- Negative control: with VK's weight the diagonal would be `diag(i/2, -i/2)`, the derivative of
  `D(torusExp (-t/2))`.
- `rightField (fun t ↦ torusExp (t/2)) f` applied to `D^j_{m'm}` multiplies it by `i m`.
- `rightField bBeta` applied to `g ↦ g₀₀` gives `g₀₁ · (-1/2)`; this is the `(0, 0)` entry of
  `g · [[0, 1/2], [-1/2, 0]]`.
- Negative control: on `g ↦ g₀₀` the field `leftField bBeta` gives `g₁₀/2`, not
  `rightField bBeta`'s `-g₀₁/2`; at `g = eulerD 0.3 1.1 0.5` these are different numbers.
- `leftField Y f g` is `rightField Y f g` when `f` is a class function.
- `leftField (fun t ↦ torusExp (t/2))` applied to `D^j_{m'm}` multiplies it by `i m'`.
- Negative control: `leftField` is the derivative along `Y t * g`. The differential of the left
  regular representation is along `Y (-t) * g`, which has the opposite sign; the sign cancels in
  `leftCasimir`.
- `rightCasimir` of a constant is `0`.
- `rightCasimir` of each entry of `D^{1/2}` is `-3/4` times that entry, checked symbolically.
- Negative control: `rightCasimir` built from `torusExp t` (without the `1/2`) in place of
  `torusExp (t/2)` gives `-1/4 - 1/4 - 1 = -3/2` instead of `-3/4` on every entry of `D^{1/2}`,
  because `torusExp t` is `exp(2itJ_z)`.
- `leftCasimir` equals `rightCasimir` on every `D^j_{m'm}`, with eigenvalue `-j(j+1)`.
- `leftCasimir` of a constant is `0`.
- Negative control: `leftCasimir` without the torus term gives `-1/2` instead of `-3/4` on every
  entry of `D^{1/2}`.
- `eulerLaplacian` sends each of the nine entries `e^{im'α} d^1_{m'm}(β) e^{imγ}` of `D^1` to
  `-2` times itself, checked symbolically.
- `eulerLaplacian` sends each entry of `eulerD α β γ` (that is, `D^{1/2}`) to `-3/4` times
  itself.
- Negative control: with `+2 cos β ∂_α ∂_γ` in place of `-2 cos β ∂_α ∂_γ` the entry
  `D^1_{11}` is no longer an eigenfunction. The residual is
  `-(1 + 2 cos β + cos 2β) e^{i(α+γ)}/sin² β`, which is `-1.66` at `β = 1.1`, `α = γ = 0`.
- `sphereLaplacian` sends `Y_l^m(spherePoint θ φ)` to `-l(l+1)` times itself for `l ≤ 2`,
  checked symbolically.
- `sphereLaplacian` of a function of `φ` alone is `sin⁻²θ` times its second derivative.
- Negative control: `sphereLaplacian` without the term `cot θ ∂_θ` sends `cos θ = √(4π/3) Y_1^0`
  to `-cos θ` instead of `-2 cos θ`.

## Layer 5: characters and the column index

Sources:
- in VK's convention, [VK, §6.8.1, pp. 346–348; §6.9.2, p. 358; §6.9.3, p. 360];
- [KV, p. 178, (22)] and [W, Ch. 8].

- **Characters are Chebyshev polynomials** (`sum_matrixElement_self`).
  - `χ_j = Σ_m D^j_{mm}` is Tau Ceti's character and equals `U_{2j}(tr g / 2)`.
  - In Euler angles it is `U_{2j}(cos(β/2) cos((α+γ)/2))` [VK, §6.9.3, p. 360, corrected per
    E06.9.04 and E06.9.05; KV, p. 178, (22)].
  - Route: `TauCeti.SU2.character_symPower_eq_chebyshevU_eval` and the trace of `coe_eulerD`.
- **Expansion of class functions in characters.**
  - A continuous class function is the `L²` limit of `Σ_j (∫ f conj χ_j) χ_j`.
  - Route: Plancherel restricted to class functions, or Tau Ceti's Weyl integration and the
    completeness of `U_{2j}` on `[0, π]` with weight `sin²`.
- **Matrix elements as Krawtchouk polynomials** (`smallD_eq_krawtchouk`) [VK, §6.8.1,
  pp. 346–347, corrected per E06.8.02]. Route: the sum (4.1.15) and the Krawtchouk sum.
- **Krawtchouk orthogonality from unitarity** (`krawtchouk_orthogonal`), for `0 < p < 1` [VK,
  §6.8.1, p. 348, corrected per E06.8.03]. Route: the column unitarity relation of
  `matrixElement_mul_inv` at `b_β`, with `p = sin²(β/2)`.

*Needs:* Layer 2.

**Checks.**

- `krawtchouk N 0 p x = 1`.
- `krawtchouk N 1 p x = 1 - x/(Np)`; at `N = 3`, `p = 0.3`, `x = 2` it is `-11/9`.
- `krawtchouk 1 1 (1/2) 1 = -1`.
- Negative control: at `p = 2` the formal identity still holds, but the weights
  `C(N,x) p^x (1-p)^{N-x}` change sign and the "norm" `(1-p)/p` is `-1/2`. The orthogonality is a
  statement about a measure only for `0 < p < 1`.

## Layer 6: the sphere and the Gel'fand pair

Sources:
- [E, (4.1.25), p. 59; (2.5.5)–(2.5.6), p. 21; (2.5.29)–(2.5.30), p. 24];
- in VK's convention, [VK, §6.3.11, p. 297; §6.10.3, p. 370];
- [D, §7, p. 21], [W, Ch. 8] and [KV, p. 178, (20)–(21)].

- **Spherical harmonics are matrix elements** (`sphericalHarmonic_matrixElement`).
  - `D^l_{m0}(αβγ) = (-1)^m √(4π/(2l+1)) Y_l^m(β, α)` and
    `D^l_{0m}(αβγ) = √(4π/(2l+1)) Y_l^m(β, γ)` [E, (4.1.25), p. 59]. This uses Edmonds's
    `Y_{lm}`, which equals DLMF's `Y_l^m`.
  - On the orbit, `Y_l^m(R(g) e₃) = √((2l+1)/(4π)) conj D^l_{m0}(g)`.
  - The rotation law is `Y_l^m(R(g)⁻¹ x) = Σ_{m'} D^l_{m'm}(g) Y_l^{m'}(x)`.
  - Route: `smallD_eq_ferrers` and `matrixElement_eulerD`. The orbit statement uses
    `R(eulerD α β γ) e₃ = spherePoint β (π - α)`.
- **Orthonormality and completeness on `S²`** (`sphericalHarmonic_orthonormal_complete`).
  - Route: orthonormality from Schur orthogonality pushed forward by `orbitPoint`.
  - Completeness from Plancherel on SU(2) applied to `f ∘ orbitPoint`. That function is right
    invariant under the torus, hence orthogonal to every column `m ≠ 0`.
- **The decomposition of `L²(S²)`.** `L²(S²) = ⊕_l H_l`, where `H_l` is spanned by the `Y_l^m`,
  is invariant by the rotation law, and is irreducible of dimension `2l + 1`. Route: the two
  previous headlines and `isUnitary_unitaryModel`.
- **The addition theorem for spherical harmonics** (`sum_sphericalHarmonic_mul_conj`).
  `Σ_m Y_l^m(x) conj Y_l^m(y) = (2l+1)/(4π) P_l(x · y)`. Route: `legendre_addition` in the form
  `D^l_{00}(g⁻¹h) = Σ_m conj D^l_{m0}(g) D^l_{m0}(h)`.
- **Solid harmonics are harmonic** (`laplacian_solidHarmonic`).
  - This is the Euclidean form of the Laplace–Beltrami eigen-equation
    `Δ_{S²} Y_l = -l(l+1) Y_l` [E, p. 22]; the intrinsic form is not stated.
  - Route: `‖x‖^l Y_l^m(x/‖x‖)` is a homogeneous polynomial; apply the Legendre differential
    equation.
- **Gel'fand's criterion and the commutative algebra** (`gelfand_pair`).
  - Every `g⁻¹` lies in `T g T`, so convolution of continuous bi-`T`-invariant functions is
    commutative.
  - Route: for `g = eulerD α β γ` take `k₁ = g_{-γ} D g_{-α}` and `k₂ = g_{-γ} D⁻¹ g_{-α}` with
    `D = diag(i, -i)`, since `D b_β D⁻¹ = b_{-β}`. Then apply Gel'fand's trick with the
    anti-automorphism `g ↦ g⁻¹`.
  - The zonal spherical functions are `D^l_{00} = P_l(cos β)`, and they satisfy the functional
    equation of `legendre_product`.

*Needs:* Layers 2–3; Mathlib's `MeasureTheory.Measure.toSphere` and `Laplacian.laplacian`.

**Checks.**

- `orbitPoint 1 = e₃`.
- `orbitPoint (eulerD α β γ) = spherePoint β (π - α)`. At `(0.7, 1.1, -2.3)` this is
  `(-0.6816, 0.5741, 0.4536)`.
- `orbitPoint (g * torusExp t) = orbitPoint g`.
- Negative control: `orbitPoint (eulerD α β γ)` is not `spherePoint β α`; at `(0.7, 1.1, -2.3)`
  that point is `(0.6816, -0.5741, 0.4536)`.
- `spherePoint 0 φ = e₃`.
- `spherePoint θ φ` has norm `1`.
- `spherePoint (π/2) 0 = e₁`.
- Negative control: `spherePoint θ φ` and `spherePoint (-θ) (φ + π)` are equal, so the polar angle
  must be restricted to `[0, π]` for a chart.
- `sphericalHarmonic 0 0 = 1/√(4π)`.
- `sphericalHarmonic 1 1 x = √(3/(4π)) x₃`.
- `sphericalHarmonic 1 2 x = -√(3/(8π)) (x₁ + i x₂)`.
- Negative control: without the Condon–Shortley phase, `Y_1^1 = +√(3/(8π)) (x₁ + i x₂)`, and the
  first conjunct of `sphericalHarmonic_matrixElement` fails by a sign.
- `conv 1 1 = 1`.
- `conv D^d_{ij} D^d_{kl} = δ_{jk} D^d_{il} / (d + 1)` (Schur).
- Negative control: `conv` is not commutative on all continuous functions. At `d = 1`,
  `conv D_{01} D_{11} = D_{01}/2` while `conv D_{11} D_{01} = 0`.

## Acceptance examples

- `j = 1/2`: in Edmonds's order `m = 1/2, -1/2`, the matrix of `D^{1/2}(eulerD α β γ)` is
  `eulerD α β γ` itself. In particular `d^{1/2} = [[cos(β/2), sin(β/2)], [-sin(β/2), cos(β/2)]]`
  [E, (4.1.13), p. 56].
- `j = 1`: in the order `m = 1, 0, -1`, the matrix of `d^1(β)` is Edmonds's printed matrix
  [E, p. 57], whose rows are `[(1+cos β)/2, sin β/√2, (1-cos β)/2]`,
  `[-sin β/√2, cos β, sin β/√2]` and `[(1-cos β)/2, -sin β/√2, (1+cos β)/2]`.
- `D^1(eulerD α β γ)` has entries `e^{im'α} d^1_{m'm}(β) e^{imγ}`, checked symbolically.
- `D^1_{00} = cos β`, and `D^l_{00} = P_l(cos β)` for `l ≤ 3` by direct expansion.
- The Legendre addition theorem at `l = 1` is the spherical law of cosines
  `cos β = cos β₁ cos β₂ - sin β₁ sin β₂ cos α` (with this sign convention).
- The Euler-angle Haar formula integrates `1` to `1` and `|D^1_{00}|²` to `1/3`.
- The characters at `-1` are `(-1)^d (d + 1)`: `1, -2, 3, -4` for `d = 0, …, 3`.
- `vk_conversion` at `l = 1/2` and `l = 1` reproduces VK's matrices with the factor `i^{m-n}`.

All numbers above were recomputed with mpmath and sympy.

## Downstream consumers

- The lean-SFVK plan's Roadmap 3 (tensor products, Clebsch–Gordan coefficients) consumes
  Layers 1–2, in Edmonds's convention, which is also his convention for the 3j symbols.
- Roadmap 4 consumes the `S²` layer.
- Roadmap 2 states its general matrix element so that `matrixElement` here is an instance, and
  aligns its SU(1,1) Euler angles with `eulerD`.

## Beyond this roadmap

Roadmap for a roadmap; do not implement.

- Matrix elements on `SL(2, ℂ)` and complex Euler angles [VK, §6.3.3, p. 284].
- Degree-shift recurrences, Christoffel–Darboux, and generating functions in the degree
  [VK, §6.7.3, p. 336; §6.7.8, p. 344].
- Integral representations and the Rodrigues formula for `d^j` [VK, §6.3.5, p. 287].
- The recursion in `j` [E, (4.4.1), p. 61], and Wigner's computation through `d^j(π/2)`
  [E, (4.5.1)–(4.5.3), pp. 61–62].
- Expansion of smooth functions on SU(2) with rapid decay of coefficients [VK, §6.10.4, p. 372].
- Krawtchouk difference equations, generating functions, and the Meixner analogue for SU(1,1)
  [VK, §6.8.2, p. 350].
- Tensor products, Clebsch–Gordan and Wigner coefficients, and products of `D` [E, §4.3, p. 60]
  (planned Roadmap 3).

## References

- [E] A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press, 1957
  (reprint 1996), §1.3, Chapter 2, Chapter 4.
- [VK] N. Ja. Vilenkin, A. U. Klimyk, *Representation of Lie Groups and Special Functions*,
  Vol. 1, Kluwer, 1991, Chapter 6.
- [KV] A. U. Klimyk, N. Ja. Vilenkin, *Representations of Lie groups and special functions*, in
  A. A. Kirillov (ed.), *Representation Theory and Noncommutative Harmonic Analysis II*,
  Encyclopaedia of Mathematical Sciences 59, Springer, 1995, §2.2.
- [W] A. Wawrzyńczyk, *Group Representations and Special Functions*, Reidel, 1984, Chapter 8.
- [D] J. Dieudonné, *Special Functions and Linear Representations of Lie Groups*, CBMS 42, AMS,
  1980, §§2, 7.
- [M68] W. Miller, Jr., *Lie Theory and Special Functions*, Academic Press, 1968, §5-16.
- DLMF, §§14.30, 18.5.

## Provenance

The project's SYNOPSIS files index the sources other than Edmonds. Edmonds has no SYNOPSIS file,
so his equation numbers are given directly. The table maps each headline to its sources.

| Headline | Edmonds | VK06 (VK convention) | Other |
| --- | --- | --- | --- |
| Euler matrix, covering, bijection | §1.3, (4.1.9), (4.1.13) | VK06.1.01 | KV02.2.06; Dieudonné §2 |
| Euler angles on SO(3) | §1.3 | VK06.1.08 | |
| Haar measure in Euler angles | (4.6.1) | VK06.1.11 | Wawrzyńczyk §8.3 |
| Invariant inner product, unitary model | §4.1 p. 56 | VK06.2.05 | Dieudonné §2 |
| Unitary dual | | VK06.2.04, VK06.9.09 | Wawrzyńczyk §8.2 |
| Explicit polynomial formula | p. 56 | VK06.3.02 | Dieudonné §2 |
| Group law, unitarity | §4.2 | VK06.3.13, VK06.6.01 | Miller1968 §5-16 |
| Euler-angle factorization | (4.1.12), (4.1.15) | VK06.3.09 | KV02.2.06; Wawrzyńczyk §8.3 |
| Jacobi form | (4.1.23) | VK06.3.16 | KV02.2.06; Dieudonné §2 |
| Hypergeometric form | | VK06.3.11 | |
| Symmetries, values at 0 and π | (4.2.1)–(4.2.6) | VK06.3.14, VK06.3.15 | Miller1968 §5-16 |
| Legendre, Ferrers | (4.1.24), (4.1.26), (2.5.10) | VK06.3.17, VK06.3.26 | KV02.2.07; Dieudonné §2 |
| Conversion from VK | | VK06.3.09 | KV02.2.06 |
| Angle of a product, addition theorem | | VK06.1.02, VK06.6.03 | Dieudonné §2 |
| Legendre addition theorem | | VK06.6.06 | |
| Product formula, functional equation | | VK06.6.12 | Wawrzyńczyk §8.3 |
| Schur and `d^j` orthogonality | (4.6.1) | VK06.10.01 | Wawrzyńczyk §8.3 |
| Plancherel | | VK06.10.03 | Wawrzyńczyk §8.6 |
| Infinitesimal operators, Casimir | (4.1.6)–(4.1.9) | VK06.2.03, VK06.10.07 | Wawrzyńczyk §8.4 |
| Differential equation | (2.5.9) | VK06.7.18 | Wawrzyńczyk §8.4 |
| First-order recurrence | | VK06.7.08 | Wawrzyńczyk §8.4 |
| Generating function | (4.1.14) | VK06.7.01 | |
| Casimir in Euler angles, Laplacian | p. 22 | VK06.10.08 | Wawrzyńczyk §8.4 |
| Characters | | VK06.9.04, VK06.9.05 | KV02.2.08; Wawrzyńczyk §8.5 |
| Krawtchouk form and orthogonality | | VK06.8.01, VK06.8.04 | |
| Spherical harmonics, `S²` | (4.1.25), (2.5.29) | VK06.3.28, VK06.10.08 | Wawrzyńczyk §8.6; Dieudonné §7 |
| Gel'fand pair | | | Dieudonné §§6–7 |

ERRATA entries applied, all in VK's and KV's convention through `vk_conversion`:
- VK: E06.3.01, E06.3.02, E06.3.10, E06.6.01, E06.7.04, E06.8.02, E06.8.03, E06.9.04, E06.9.05
  and E06.10.04;
- KV: E02.2.04 and E02.2.05.
