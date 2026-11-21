# RankOneSymmetricSpaces: working notes (not part of the roadmap)

Roadmap 8 of ROADMAP_PLANS.md §6, "rank-one symmetric spaces". Pins: the lake of
/ufs/braams/TauCetiRoadmap (Tau Ceti and Mathlib as pinned there). `Suggested.lean` compiles with
50 `sorry` theorems, `#check` output and no other diagnostics. Numerical checks: the `check_*.py`
scripts in the session scratchpad (`sfvk/r38/RankOneSymmetricSpaces/`); every number quoted in
the README was recomputed there (mpmath or scipy), and the identities behind the headlines
(Jacobi equation, connection formula, `c(−iρ) = 1`, special cases, quadratic transformation,
polynomial case, energy bound, Laplace representation, product formula, Harish-Chandra integral
for `n = 2, …, 5`, horospherical density, ambient Laplacian on plane waves and radial functions,
Abel transform for `n = 2, 3, 4`, Plancherel constants for `n = 3`) were checked numerically or
symbolically. Wawrzyńczyk's PDF is a scan; its pages were OCRed into `ocr/` there (printed page =
PDF page − 15).

## Ownership survey (Tau Ceti main)

- RealSemisimpleLieGroups owns `G/K` in general (its §5.2 identifies `SO₀(n, 1)/SO(n)` with the
  hyperboloid) and complex hyperbolic space (§5.7) as geometry; it excludes spherical functions
  and harmonic analysis on `X`.
- LieGroupsPartII Layer 9 owns `KAK` and Iwasawa in general; here they are done in coordinates.
- SpecialFunctionsGroupModels (Roadmap 2) owns Gel'fand pairs and spherical functions in general
  (§§5.1–5.3) and multiplier representations (Layer 1); its Beyond puts the `c`-function and the
  inversion of the spherical transform outside it, so they are owned here.
- SpecialFunctionsSU11MatrixElements (Roadmap 7) owns `𝔓^τ_{mn}`, conical functions (§1.3), the
  `𝔓_{00}` product formula (§3.2) and the Mehler–Fock transforms (§§5.2–5.3). Its sections file
  agrees that Roadmap 8 owns the general Jacobi function, `c`, the Jacobi transform, the Abel
  transform, the Helgason–Fourier transform and the general Koornwinder product formula.
- NoncompactQuantumSymmetry M4 / M4.Lorentz own the `SL(2, ℝ)`, `SL(2, ℂ)` principal and
  complementary series; consumed for `n = 2, 3` in 3.4.
- AutomorphicSpectralTheory §§0.35–0.37 (`Q_{s−1}`, point-pair invariants on `𝔥`) and
  AnalyticNumberTheoryPartII §6.12 (inverse-Abel adapters for the `ℍ²` heat kernel): boundary
  only, no dependency in either direction.
- SpecialFunctionsHypergeometric's Beyond leaves DLMF 15.9.11–15.9.14 (Jacobi function and
  transform) unowned; owned here.
- SpecialFunctionsLegendre (DLMF Ch. 14) is not on main; conical functions are consumed from
  Roadmap 7 instead.
- Roadmap 5 (HigherSpheres) takes the compact parts of VK Vol. 2 Chs. 9–11; the hyperboloid and
  noncompact parts (`SO₀(n−1, 1)`, `U(n−1, 1)`, `Sp(n−1, 1)`) fall to this roadmap, of which only
  `SO₀(n, 1)` is built geometrically.

## Decisions for the author

- **Koornwinder's `c`** (`c(−iρ) = 1`, Plancherel density `(2π)⁻¹|c|⁻²`) rather than
  Klimyk–Vilenkin's `𝐜 = 2√π c/Γ(α + 1)`. Recorded in Conventions with a negative-control Check.
- **`F = Γ(c) 𝐅` from SpecialFunctionsHypergeometric** in the definition of `jacobiFunction`;
  lean-DLMF's `jacobiFunction` is `Γ(α + 1) 𝐅(…)`, the same function; the Lean code has the
  conversion lemma.
- **Time coordinate first** (index `0`), whereas Vilenkin–Klimyk put it last. Chosen for
  `Fin.cons` and `Pi.single 0`.
- **`SO₀(n, 1)` as a subgroup of `SL(n + 1, ℝ)`** with the condition "maps `ℍⁿ` onto itself",
  which gives a `sorry`-free subgroup proof; the equivalence with the usual `g₀₀ > 0` is a
  target-level fact (2.1 Checks).
- **Laplacian through the ambient wave operator** (Wawrzyńczyk §11.5) rather than a Riemannian
  metric on a manifold structure; the comparison with the Laplace–Beltrami operator of the
  induced metric (and with Tau Ceti's UpperHalfSpace) is a prose target of 2.3.
- **Complex/quaternionic/octonionic hyperbolic spaces in Beyond** as geometry; their radial
  analysis is covered by Layers 0–1 for general `(α, β)`. The author may prefer to add a Layer
  for `SU(n, 1)/U(n)` (VK Vol. 2 §11.4).
- **`ν` for the functional equation** is any left-invariant probability measure on `K`
  (hypotheses), as in Roadmap 2's `IsSphericalFunction`.
- **Target count**: 50 named theorems in `Suggested.lean` plus about 20 prose bullets (Cartan
  decomposition, Riemannian comparison, the boundary action, positive definiteness, the principal
  series, discrete terms, Paley–Wiener theorems, the unitary Helgason–Fourier transform,
  `n = 2, 3` specializations).

## Open questions

- The energy bound `|φ_λ| ≤ 1` (0.4) is stated for real `α ≥ −1/2`, `ρ ≥ 0` by the author's own
  Lyapunov argument (`E = u² + u'²/(λ² + ρ²)`); it is not quoted from a source. Numerically
  confirmed on a grid; a negative control at `(−1/4, −3/2)` gives `5.47`.
- 1.2 states inversion for `α > −1`, `|β| ≤ α + 1` following Klimyk–Vilenkin p. 233; Koornwinder
  (1984a), the primary source, is unread. For complex parameters the range differs.
- 1.3's discrete-term residues `d(λ_j)` are named but not written out.
- 3.4's complementary-series inner product is described, not written out (VK §9.2.8 has it).
- The 4.2 Check comparing with AnalyticNumberTheoryPartII §6.12 adapters: their normalization was
  not re-read.

## Locators not yet re-read in the PDF

- Vilenkin–Klimyk Vol. 2: running heads confirmed for pp. 23, 35, 39, 47–48, 92, 348–349; the
  content of §§9.1.9, 9.2.6, 9.2.8, 9.3.2, 9.4.10, 10.1.2 and 11.4.1 was taken from the synopsis
  file of that volume, not re-read on the page.
- Heckman–Schlichtkrull: §5.4 (5.4.2)–(5.4.5), Theorem 5.4.2, Proposition 5.4.3 (pp. 83–84) and
  Example 8.1 (pp. 171–172) confirmed in the text layer; Example 8.3 (pp. 181–182) from the
  synopsis only.
- DLMF 15.4.11 and 15.4.15 confirmed against lean-DLMF's tagged statements
  (`DLMF.Hypergeometric.opposite_parameters_sqrt`, `complementary_parameters_odd_sqrt` in
  `DLMF/Hypergeometric/Elementary/AlgebraicValues.lean`): at `z = sinh t` they give `cosh 2at`
  and `sinh((2a − 1)t)/((2a − 1) sinh t)`; they are stated for `|z| < 1`, so `|sinh t| ≥ 1`
  needs analytic continuation (SpecialFunctionsHypergeometric §4.1). 15.9.11–15.9.14 read online.
