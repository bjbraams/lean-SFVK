# HigherSpheres: working notes

Draft of Roadmap 5 of `ROADMAP_PLANS.md` §6 (spheres in higher dimension, `SO(n)` and `U(n)`). Not
submitted. The numerical checks are the scratchpad scripts `check1.py` to `check4.py`
(sfvk/r38/HigherSpheres), with their outputs `check*.out`; they are not part of the roadmap.

## Decisions taken in the draft (to confirm with the author)

- **Normalized zonal polynomial instead of Gegenbauer.** The primary object is
  `zonalPolynomial n l = ₂F₁(-l, l + n - 2; (n - 1)/2; (1 - t)/2)`, normalized at `1`. It covers
  `n = 2` (Chebyshev `T_l`) without the `λ = 0` degeneracy of LaguerreJacobi's `gegenbauer 0 l = 0`
  and makes every constant a dimension. The Gegenbauer polynomial enters through
  `gegenbauer_eq_zonalPolynomial` (`n ≥ 3`). lean-DLMF's `ultrasphericalPolynomial` is related
  to it in the SFVK code.
- **Base point.** A unit vector `η` and its stabilizer `K_η = MulAction.stabilizer` instead of
  `e_n` and an embedded `SO(n - 1)`. The sources all use `e_n`; the statements hold for every
  unit `η`, which avoids an embedding `SO(n - 1) → SO(n)` in the statements.
- **Measures normalized to mass one** (`sphereMeasure`, `complexSphereMeasure`), consistent with
  ROADMAP_PLANS §3 (Haar mass `1`) and with Vilenkin–Klimyk §10.2.1. lean-DLMF's
  `sphericalHarmonicInner` uses the unnormalized `toSphere`; the SFVK code must convert.
- **Statements in polynomial form.** Harmonic spaces are Tau Ceti's `harmonicSubmodule`, evaluated
  on the sphere by `sphereEval`; class one is stated as "a `K_η`-invariant harmonic polynomial is
  `p(η) Z_{l,η}`", and the addition theorem for an `L²`-orthonormal family indexed by
  `Fin (finrank)`. No `L²` Hilbert-space structure on `H_l` is built here (R8.2 owns it).
- **`U(n)` harmonics** are `MvPolynomial (Fin n ⊕ Fin n) ℂ` with weights `(1,0)`, `(0,1)` and the
  complex Laplacian `∑ ∂_{zⱼ} ∂_{z̄ⱼ}`; values at `z` are taken at `(z, z̄)` (`evalC`).
- **Disk polynomial** by the finite sum symmetric in `p, q`
  (`∑ (-1)ⁱ C(p,i) C(q,i) i!/(α+1)ᵢ (1-|w|²)ⁱ w^{p-i} w̄^{q-i}`), checked against
  VK's `₂F₁`/Jacobi form; the general-`α` orthogonality is owned here (analytic, Jacobi route).
- **Spherical function of `(U(n), K_η)`** is `R^{n-2}_{p,q}(⟪g η, η⟫)`, the matrix coefficient
  `⟪Z, g·Z⟫/⟪Z,Z⟫` with Mathlib's inner product; `R(⟪η, g η⟫)` is the spherical function of
  `H^{q,p}`. Checked by Monte Carlo (`check2.py`).
- **Ownership of Gegenbauer facts with no owner on main**: value at one, generating function,
  derivative, differential equation, Laplace integral, product formula and Gegenbauer addition
  theorem are owned here (3.2, 3.4, 4.4, 4.5). An OrthogonalPolynomialsClassical roadmap (DLMF 18,
  in preparation by the same author, not on main) might later claim the first four; then 3.2
  becomes consumed. **Question for the author.**
- **Boundary with Roadmap 4** (motion groups and Bessel): the plane-wave expansion, Bochner's
  theorem (VK §10.2.4) and `(M(n), SO(n))` go there; this roadmap supplies Funk–Hecke.
  **Question for the author / the R4 agent**: confirm.
- **Boundary with Roadmap 8** (rank-one symmetric spaces): the compact duals `S^{n-1}`, `S^{2n-1}`
  are treated here; their noncompact duals (hyperboloids, VK §§9.2.9–9.2.10, Ch. 10) are left to
  Roadmap 8 or Beyond. **Question for the author.**
- **Gel'fand–Tsetlin basis** (5.2) is stated in prose only; the Lean statements stop at one
  branching step (5.1). ClassicalGroups Layer 6 owns GT patterns of GLₙ abstractly.

## Ownership survey (upstream main, checked 2026-11-20)

- Tau Ceti (pinned 396c3bd): `MvPolynomial.laplacian`, `normSq`, `harmonicSubmodule`,
  `finrank_harmonicSubmodule_add_two`, Fischer decomposition, `harmonicRep` (orthogonal group),
  `sphereEval`, `harmonicSphereRestriction(_injective)`, `TauCeti.haarProb`, compactness of the
  unitary groups, `orthogonalGroupMeasure` and its last-column pushforward. The roadmap lake's
  TauCeti (2fd255d) does not build `Harmonic/Orthogonal`, so `Suggested.lean` does not import it.
- RiemannianGeometry R8.1–R8.3: uniqueness of Fischer, eigenvalue, spectral completeness,
  orthogonality, irreducibility (`N ≥ 3`). Consumed.
- LaguerreJacobi §6.2: `Polynomial.gegenbauer`, leading coefficient, Jacobi relation,
  orthogonality (`-1/2 < λ`, `λ ≠ 0`), Hilbert basis; excludes `λ = 0`, continuation; no value at
  one, generating function, ODE. §3.2 Jacobi. Consumed (local verbatim copies).
- GeometryOfNumbersAndQuadraticArithmetic §4.3: `polynomialLaplacian`, Fischer — boundary only.
- ClassicalGroups Layer 6.2 (`SO_n ↓ SO_{n-1}`), Layer 6 (GT patterns of `GL_n`). Consumed.
- No owner on main for: zonal polynomials, spherical harmonics in the representation sense,
  addition theorem, Funk–Hecke, disk polynomials, bidegree harmonics. Owned here.
- Roadmaps 1–2 (SFVK, open PRs): consumed in prose by section number (R2 §§0.3, 2.6, 5.1–5.3;
  R1 §§6.3–6.4).

## Supplier status

- lean-DLMF: `OrthogonalPolynomials.ultrasphericalPolynomial` (with generating function,
  derivative, value at one), `SphericalHarmonics/*` (harmonic homogeneous polynomials, dimension,
  `spherical_addition`, `funk_hecke` for `n = 3`, ultraspherical addition for `λ > 1/2`; several
  sorry'd). Used in the SFVK code through conversion lemmas.

## Open questions

- Is the classification of spherical functions (4.4, 6.5) wanted as a Lean target, or is it enough
  to state that the zonal functions are spherical? It needs Peter–Weyl in full.
- Koornwinder's addition formula for disk polynomials is in Beyond; include it? (VK (28) p. 345 has
  a wrong coefficient, E11.4.10.)

## Errata used

- VK E09.2.01 (§9.2.3 p. 30, dimension of homogeneous polynomials), E10.2.01 (§10.2.1 p. 173,
  denominator `C^{(n-2)/2}(1)`), E09.4.01 (§9.4.3 p. 71 (2), three-angle relation), E11.4.10
  (§11.4.5 p. 345 (28)); and VK p. 345 prints `z` for `z̄` in the case `m < n` of `R^α_{mn}`
  (not in the errata file; proposed as a new item).
- Wawrzyńczyk W84-E09.5.01 (p. 337, derivation of (9.5.2); formula correct). W84-E09.3.01
  (p. 331, Gegenbauer equation eigenvalue) is relevant to 3.2 but p. 331 is not cited.

## Locators read in the source (printed pages)

- VK Vol 2: §9.1.9 p. 22; §9.2.3 p. 30; §9.2.6 pp. 35–36; §9.3.1 pp. 44–46; §9.3.2 p. 47; §9.3.7
  pp. 59–60; §9.3.8 pp. 62–63; §9.4.3 p. 71; §9.4.5 p. 76; §10.2.1 pp. 173–175; §11.2.1 p. 295;
  §11.2.2 pp. 295–297; §11.3.2 p. 309; §11.4.5 p. 345.
- Wawrzyńczyk: pp. 330, 335, 337 (page images; the extracted text is empty).
- Dieudonné §7 pp. 22–24, (96)–(103) ((103) looks garbled in the extraction).
- Klimyk–Vilenkin 1995, Part II: pp. 179–180 ((24), (25), (27)), p. 182 ((34)), p. 186 ((14)),
  p. 192 ((29)). PDF page = printed + 6.

## Not yet re-read

- Wawrzyńczyk §9.3 p. 331 (the Gegenbauer equation): not cited; a candidate source for 3.2.
- KV (27) p. 180 is cited only for the shape `sin^m θ C_{l-m}^{m+(n-1)/2}` of associated spherical
  functions (OCR garbled; constant not used).
