# SU2MatrixElements: working notes

Draft of Roadmap 1 of `ROADMAP_PLANS.md` §4. Not submitted. The numerical checks are in the
scratchpad scripts `num1.py` to `num9.py` and `sym10.py` (sfvk/su2); `num9.py` and `sym10.py`
check the Edmonds convention, `sym12.py` the Casimir. They are not part of the roadmap.

## Decisions

- **Convention: Edmonds (author's decision, 2026-11-19).** Edmonds's `D^j_{m'm}(αβγ)` and
  `d^j_{m'm}(β)` (*Angular Momentum in Quantum Mechanics*, §§4.1–4.2) are the primary objects.
  Vilenkin–Klimyk enters only through the conversion theorem `vk_conversion`; the VK ERRATA items
  are applied there, and the other VK locators are marked "in VK's convention".
- Index convention: `d = 2j : ℕ` and `i : Fin (d + 1)` with `m = i - d/2` (`edWeight`). This is
  the index of Tau Ceti's `weightBasis` (monomial `z₁^i z₂^{d-i}`, Tau Ceti weight `2i - d = 2m`),
  so no reindexing is needed against Tau Ceti. Edmonds prints his matrices in the order
  `m = j, …, -j`, which is `i = d, …, 0`.
- `smallD d i k β` is Edmonds's finite sum (4.1.15), with natural-number indices, zero out of
  range, and total in `β` (no square roots of `1 ± cos β`). Every Euler-angle statement therefore
  holds for all real angles. The VK-era function `Pmn` (Jacobi form in `z`, junk outside
  `[-1, 1]`) is dropped.
- The unitary model is owned here: Tau Ceti's `symPowerModel d` is not unitary for `d ≥ 2`.
  `unitaryModel d` is its transport by `e_i ↦ √(i!(d-i)!) e_i` through
  `ContinuousLinearEquiv.congr`; its basis is Edmonds's spinor basis
  `z₁^{j+m} z₂^{j-m}/√((j+m)!(j-m)!)`.
- `matrixElement d i k g` is the conjugate of `ContRepresentation.matrixCoeff` at `v = e_k`,
  `w = e_i`, i.e. `⟪e_{m'}, T(g) e_m⟫ = D^j_{m'm}(g)`, a genuine left representation.
- Jacobi form without `i^{m'-m}`: `a = |i - k|`, `b = |d - i - k|`,
  `κ = min(i, k, d-i, d-k)`, sign `(-1)^{max(k - i, 0)}`; Edmonds's (4.1.23) is the case
  `m' ≥ |m|`.
- Spherical harmonics: Edmonds's `Y_{lm}` equals DLMF's `Y_l^m`; Edmonds's `P_l^m` lacks the
  Condon–Shortley `(-1)^m` (checked for `l ≤ 3`). (4.1.25) holds verbatim; on the orbit,
  `Y_l^m(R(g) e₃) = √((2l+1)/(4π)) conj D^l_{m0}(g)` and `R(eulerD α β γ) e₃` has polar angle `β`,
  azimuth `π - α`.
- Jacobi polynomials: verbatim local copy of LaguerreJacobi §3.2. Legendre: Mathlib's
  `shiftedLegendre` at `(1 - z)/2`. Ferrers functions through derivatives of `P_l`.
- Gel'fand pair stated for (SU(2), T) with explicit convolution; Laplace–Beltrami replaced by
  harmonicity of solid harmonics.

## The convention to copy into Roadmap 2 (SU(1,1) Euler angles)

- Group element: `eulerD α β γ = torusExp (α/2) * bBeta β * torusExp (γ/2)`, that is
  `diag(e^{iα/2}, e^{-iα/2}) · [[cos(β/2), sin(β/2)], [-sin(β/2), cos(β/2)]] ·
  diag(e^{iγ/2}, e^{-iγ/2})`, Edmonds's `exp(iαJ_z) exp(iβJ_y) exp(iγJ_z)` at spin 1/2.
- Entries: `[[cos(β/2) e^{i(α+γ)/2}, sin(β/2) e^{i(α-γ)/2}],
  [-sin(β/2) e^{-i(α-γ)/2}, cos(β/2) e^{-i(α+γ)/2}]]`.
- Ranges: SU(2) box `0 ≤ α < 2π`, `0 < β < π`, `-2π ≤ γ < 2π` (Haar density
  `(16π²)⁻¹ sin β`); SO(3) (Edmonds §1.3, p. 7) `0 ≤ α < 2π`, `0 ≤ β < π`, `0 ≤ γ < 2π`
  (density `(8π²)⁻¹ sin β`, Edmonds (4.6.1)).
- Basis and index: `i : Fin (d + 1)`, `m = i - d/2`, basis vector `z₁^i z₂^{d-i}/√(i!(d-i)!)`;
  action `T(g) f(z₁, z₂) = f(g₀₀z₁ + g₁₀z₂, g₀₁z₁ + g₁₁z₂)`.
- Matrix element: `D_{m'm}(g) = ⟪e_{m'}, T(g) e_m⟫` and
  `D_{m'm}(eulerD α β γ) = e^{im'α} d_{m'm}(β) e^{imγ}`.
- Rotation: `toSO3 (eulerD α β γ) = R_z(-α) R_y(-β) R_z(-γ)` with Tau Ceti's `toSO3`.
- The SU(1,1) analogue would replace `bBeta β` by `[[cosh(τ/2), sinh(τ/2)], [sinh(τ/2),
  cosh(τ/2)]]` and keep the outer torus factors and the letters `α, γ`; this is a suggestion for
  Roadmap 2, not checked here.

## Open questions for the author

None open. Decided by the author on 2026-11-19:
- Krawtchouk polynomials stay owned here for now.
- The Laplacian of SU(2) in Euler angles is stated in Lean: `eulerLaplacian` on the chart
  `0 < β < π`, equal to the Casimirs `rightCasimir` and `leftCasimir` of both regular
  representations (`casimir_eulerD`), with eigenvalue `-j(j+1)` on `D^j_{m'm}`
  (`eulerLaplacian_matrixElement`), and reducing to `sphereLaplacian` for `γ`-independent
  functions (`eulerLaplacian_sphere`). Checked with sympy (`sym12.py`): both Casimirs equal the
  operator on a generic `F(α, β, γ)`, and the eigenvalues are `-3/4` on `D^{1/2}` and `-2` on the
  nine entries of `D^1`.

## Supplier status (checked against upstream main on 2026-11-19)

- On main: LaguerreJacobi (Jacobi §3, orthogonality §4, Legendre and Gegenbauer §6),
  SpecialFunctionsHypergeometric, SpecialFunctionsOrthogonalPolynomialsGeneral,
  RepresentationTheory/CompactGroups (all its layers already proved in Tau Ceti),
  RepresentationTheory/LieGroups (SU(2) as S³, Weyl integration by hand for SU(2)).
- In review, so prose only: SpecialFunctionsLegendre (DLMF 14, PR 2121), SpecialFunctionsGamma
  (PR 2191).
- Absent: any Krawtchouk or Hahn-class roadmap; a DLMF 34 (3j) roadmap; the lean-SFVK Roadmap 2
  (drafted in parallel), whose general matrix element this roadmap instantiates in prose only.
- Tau Ceti at 396c3bd: everything used is present. Modules built for this draft: Compact
  PeterWeyl, SU2 Exhaustion, SU2 Adjoint, SU2 Weyl Integration and Orthogonality, OrthogonalGroup.
  The SU2 Differential and StandardBasis modules are not built in the shared lake; the README
  cites them in prose only.

## ROADMAP_PLANS statements found wrong or outdated

- §4, Layer 1.1: `t^l_mn(φ, θ, ψ) = e^{-i(mφ + nψ)} P^l_mn(cos θ)` drops the factor `i^{m-n}`. In
  VK's conventions, which the plan adopts, the formula is
  `t^l_mn = i^{m-n} e^{-i(mφ + nψ)} P^l_mn(cos θ)` (VK §6.3.3, p. 285, (4)–(5); KV p. 178 after
  E02.2.04 and E02.2.05). Without `i^{m-n}` the identity fails already at `l = 1/2`.
- §4, Layer 1.0: "Its weight vectors are Tau Ceti's weight basis up to positive scalars" is right,
  but Tau Ceti's model is not unitary for `d ≥ 2`, so the unitary model with the invariant inner
  product must be owned by this roadmap (it is not in Tau Ceti).
- §4, Layer 1.2: the Legendre addition theorem in the plan's form,
  `P_l(cos θ₁ cos θ₂ - sin θ₁ sin θ₂ cos φ)`, is right for VK's `a_θ`; the more common form with
  `+` corresponds to `φ ↦ φ + π`. Kept as in the plan, with a note in the README.
- §4, Inputs: the plan names "the DLMF 18 roadmap" for Krawtchouk polynomials; LaguerreJacobi on
  main excludes them, so no supplier exists.
- §4, Euler-angle statements in VK's form need `θ ∈ [0, π]`: with the square roots of the Jacobi
  form in `z = cos θ` the Euler formula is false for `θ ∉ [0, π]` (checked at `θ = 3.9`). The
  Edmonds form with `smallD` in half-angles holds for all real angles.
- §4 generally: the plan uses VK's convention; the author chose Edmonds's on 2026-11-19, so the
  plan's formulas apply only after `vk_conversion`.

## Sources actually read for locators

- VK 1991, Chapter 6 (extracted text; printed page = PDF page - 23): §6.1.1 p. 269, §6.1.4
  p. 275, §6.3.1 p. 280, §6.3.2–6.3.3 pp. 284–285, §6.3.6 p. 287, and the section headings of
  §§6.1–6.10 with their pages.
- KV in EMS 59, §2.2, p. 178 (PDF 184).
- Dieudonné 1980, §2, pp. 6–7 (PDF 11–12), (22)–(37) and the angle-of-product formula; §7 from
  the contents, p. 21.
- Wawrzyńczyk 1984 (scanned; page images): (8.3.4)–(8.3.6) p. 291, (8.4.9)–(8.4.12) p. 297.
- Miller 1968, §5-16, p. 219 (PDF 225).
- Edmonds 1957/1996 (page images; printed page = PDF page - 6): §1.3 pp. 6–8; §2.5 pp. 19–24;
  §§4.1–4.2 pp. 53–60; §§4.3–4.6 pp. 60–62.
- Equation-level locators not read directly (for example VK's (n) numbers inside §§6.6–6.10)
  are cited at section level with the section's first page.
