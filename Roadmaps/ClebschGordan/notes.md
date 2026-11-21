# ClebschGordan: working notes

Draft of Roadmap 3 of `ROADMAP_PLANS.md` §6 (Clebsch–Gordan and Racah theory for SU(2)). Not
submitted. The numerical checks are in the scratchpad scripts `cg.py`, `num1.py` to `num7.py`,
`leancheck.py` and `checks.py` to `checks3.py` (sfvk/r38/ClebschGordan); `leancheck.py` mirrors
the Lean definitions of `Suggested.lean` with truncated natural subtraction and evaluates every
Lean-named statement on small arguments, in and out of range. They are not part of the roadmap.

## Ownership survey

- No DLMF Chapter 34 roadmap exists on Tau Ceti main. SpecialFunctionsGeneralizedHypergeometric
  lists the 3j, 6j and 9j symbols as terminating `₃F₂`/`₄F₃` series in its Beyond section, and
  says a Hahn/Racah/Wilson roadmap would consume its Layer 4 and §6.1. LaguerreJacobi excludes the
  rest of the Askey scheme. OrthogonalPolynomialsGeneral lists Hahn/Wilson classes among its
  downstream consumers (its §§10.1–10.2, difference operators). No roadmap defines the Hahn or
  Racah polynomials, so this roadmap owns them, together with the 3j and 6j symbols.
- LieHighestWeight §0.1 (on main) owns the concrete polynomial realization of `V(m) ⊗ V(n)` for
  `sl₂`/`GL₂` (the vectors `(x₁y₂ - y₁x₂)^r x₁^{m-r} x₂^{n-r}`, their Gram matrix, comparison with
  Tau Ceti's `isInternal_cgSummand`). Boundary: this roadmap uses only the group-level statement
  and the orthonormal coupled basis; recorded under Not owned.
- QuantumGroups §8.5 owns the `q`-Clebsch–Gordan coefficients. NoncompactQuantumSymmetry is not
  relevant.
- Tau Ceti supplies `ContRepresentation.tprod` (Continuous/TensorProduct) and the Lie-algebra CG
  rule `TauCeti.Sl2Std.isInternal_cgSummand` (Algebra/Lie/Sl2/ClebschGordan). The latter module is
  not built in the roadmap lake (its `.olean` is missing there), so `Suggested.lean` does not
  import it and the README names it in prose only.
- lean-DLMF has `DLMF.WignerSymbols` (`wigner3j`, `clebschGordan`, `wigner6j`, `wigner9j`, with
  rational spins), and Hahn/Racah modules under `DLMF.OrthogonalPolynomials`. The lean-SFVK code
  bridges to them; the roadmap does not depend on lean-DLMF.

## Decisions to put to the author

1. Own the 3j and 6j symbols here, in the absence of a DLMF Chapter 34 roadmap? The alternative is
   a separate DLMF 34 roadmap with this one consuming it. The draft owns them, with Edmonds's
   group-theoretic route, and keeps the 9j symbol in Beyond.
2. Own the Hahn and Racah polynomials here (the plan says "Hahn and Racah polynomials and other
   discrete orthogonal polynomials through the coupling coefficients")? The draft owns both, with
   orthogonality at all real parameters by the polynomial-identity argument. Dual Hahn, Meixner,
   Charlier and Wilson are left to an Askey-scheme roadmap.
3. Doubled-integer arguments (`d = 2j`, `i = j + m`) for all symbols, as in Roadmap 1, rather than
   rational spins as in lean-DLMF. The draft uses natural numbers throughout; signs like
   `(-1)^{j₁+j₂+j₃}` are natural-number powers with evenness hypotheses where needed.
4. `sixJ_eq_racahPolynomial` restates VK §8.5.4 after correction (the identification of the
   parameters was recomputed: `α = -2l₃ - 1`, `β = -2l₂ - 1`, `γ = -l₁ - l₂ - l₃ - l - 2`,
   `δ = l₁ + l₂ - l₃ - l`, checked on 3762 admissible cases to `2·10⁻¹³`). Whether to record the
   discrepancy with VK as an erratum in `ERRATA-VK08.md` is for the author.
5. The coupled vectors live in the algebraic tensor product `V ⊗[ℂ] W` on which Tau Ceti's
   `tprod` acts, not in `EuclideanSpace ℂ (Fin (d₁+1) × Fin (d₂+1))`.

## Open questions

- Whether Tau Ceti's TensorProduct module exports a named orthonormal basis of `V ⊗ W` from
  orthonormal bases of the factors; `span_coupledVector` and `inner_coupledVector` would use it.
- `sum_racahPolynomial_mul` assumes nonvanishing of every denominator Pochhammer symbol up to
  index `2N + 1`; a sharper hypothesis is possible.

## Locators

Read in the source (printed pages; Edmonds PDF = printed + 6, VK 1991 PDF = printed + 23,
KV EMS 59 offset 6, Wawrzyńczyk PDF = printed + 15):
- Edmonds: (3.1.5) p. 35 (page from the running heads of the extracted text); (3.4.1) p. 36,
  (3.4.2) p. 37; (3.5.1)–(3.5.17) pp. 37–42; (3.6.11) and the stretched formula p. 45 (page image
  read); (3.7.1)–(3.7.8) pp. 46–47; (3.7.12)–(3.7.13) p. 48; (3.7.14)–(3.7.16) p. 49; (3.7.17)
  p. 50; (4.3.1) p. 60, (4.3.2)–(4.3.3) p. 61; (4.6.1)–(4.6.2) p. 62, (4.6.3)–(4.6.6) p. 63;
  (6.1.1) p. 90, (6.1.2)–(6.1.4) p. 91, (6.1.5) p. 92 (page image read), (6.2.1) p. 92, (6.2.4)
  p. 94, (6.2.5)–(6.2.8) p. 95, (6.2.9)–(6.2.11) p. 96, (6.2.12)–(6.2.15) p. 97, (6.3.2)–(6.3.6)
  p. 98, (6.3.7) p. 99.
- Wawrzyńczyk: (8.7.2)–(8.7.3) p. 305, (8.7.4)–(8.7.8) p. 306.
- KV: §2.1 p. 241, (11)–(16) pp. 241–242; §2.2 (17) p. 243.
- VK: §8.1.2 pp. 500–501 and §8.1.3 pp. 501–503 at equation level; the other VK sections are cited
  at section level with the page of the table of contents.
- DLMF: 34.1.1, 34.2.1–34.2.6, 34.3.1–34.3.22, 34.4.1–34.4.3, 34.5.1–34.5.23; 18.19 (Table
  18.19.1), 18.20.5, 18.25.9–18.25.12, 18.26.3, 18.26.10.

Not yet re-read at equation level:
- VK §§8.2.2, 8.2.6, 8.2.7, 8.3.1, 8.4.1–8.4.4, 8.4.8, 8.5.1, 8.5.2, 8.5.4 (located through
  `SYNOPSIS-VK08.md`; the README cites them at section level only).
- Wawrzyńczyk Problems 25–28, pp. 320–321 (the spin-one-half table); the README derives the table
  from the stretched formula instead of citing it.
- Edmonds Table 2 (p. 125 ff.) for the explicit 3j values with a spin `≤ 2`.
