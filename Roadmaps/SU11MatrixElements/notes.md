# Roadmap 7 (SU11MatrixElements): working notes

Draft of 2026-11-20. Tau Ceti directory name `SpecialFunctionsSU11MatrixElements`, namespace
`TauCetiRoadmap.SpecialFunctionsSU11MatrixElements` (sub-namespace `SU11`), topic `math.CA`.
Numeric scripts: `$S/sfvk/r38/SU11MatrixElements/` (core.py, check_layer1.py, check_integer.py,
check_layer2.py, check_layer34.py, check_misc.py, check_values.py, check_negctl.py,
check_realn.py, check_mehler_fock.py, check_mehler_fock_m.py, check_vk10.py). Section numbering
for Roadmap 8 is in `$S/sfvk/r38/SU11MatrixElements/sections.md`.

Size: 37 Lean-named theorem targets (all stated in Suggested.lean) and 19 prose targets, 56 in
all; 7 owned definitions (`boostMatrixElement`, `discreteMatrixElement`, `parabolic`,
`sinhMeasure`, `plancherelMeasure`, `mehlerFock`, `mehlerFockOrder`).

## Ownership survey (Tau Ceti main at upstream/main, 2026-11-20)

| Material | Owner | Here |
|---|---|---|
| `SU(1,1)`, Euler angles, circle model, `principalSeries`, complementary weights, Bergman discrete series, `matrixElement`, addition theorem/inverse, Euler factorization, ladder, template ODE, spherical functions | SpecialFunctionsGroupModels (Roadmap 2, open PR) | consumed by section, local verbatim copies in Suggested.lean |
| Irreducibility, equivalences, exhaustion, Plancherel of `SL(2,ℝ)` | NoncompactQuantumSymmetry M4, M4.P (main) | consumed (reflection 1.4, complementary 2.1, Mehler–Fock 5.2–5.3) |
| `𝐅` on the cut plane, contiguous relations, Pfaff | SpecialFunctionsHypergeometric (main) | consumed (1.2 `−sinh²` form); the `tanh²` form uses Mathlib's `ordinaryHypergeometric` |
| `P^μ_ν`, Laplace integral (8.2), addition theorem general degree (10.2), behaviour at infinity (4.5), contiguous relations (1.4) | SpecialFunctionsLegendre (PR #2121, not on main) | consumed in prose; its Beyond excludes Mehler–Fock |
| Jacobi polynomials | LaguerreJacobi (main) | consumed (1.5, 2.2) |
| `d^j_{m'm}(β)` | SpecialFunctionsSU2MatrixElements (Roadmap 1, open PR) | consumed (1.5) |
| Jacobi functions, c-function, Jacobi/Abel transforms, Helgason FT | RankOneSymmetricSpaces (Roadmap 8) | not here; R8 reads Mehler–Fock as the (0,0) Jacobi transform from 5.2 |
| `Q_{s−1}` by Heine's integral | AutomorphicSpectralTheory §§0.35–0.38 | not used |
| Mehler–Fock (order 0 and order m) | this roadmap | 5.2–5.3 |
| Kontorovich–Lebedev, mixed-basis kernels (VK07 §§7.1–7.7) | nobody | Beyond |

## Decisions to put to the author

1. **Central object as a function of `t`.** `SU11.boostMatrixElement τ m n t` is VK's
   `𝔓^τ_{mn}(cosh t)` as a function of `t ∈ ℝ` (not of `x = cosh t`), defined for all real `m`,
   `n` by the circle integral. It is not even in `t` when `m − n` is odd (parity target). The
   name avoids "reduced matrix element" (Wigner–Eckart, Roadmap 3). Alternative names:
   `SU11.vkP`, `SU11.legendreP` (rejected: collides with Legendre roadmap vocabulary).
2. **Indices.** Analytic identities take `n : ℝ`, `k : ℤ`, `m = n + k` (verified numerically for
   non-half-integer `n`, e.g. `n = 0.3`). Statements that go through `principalSeries` take
   `e : Fin 2`, `n : ℤ`, weight `n − e/2`.
3. **Gamma quotients** are stated with reciprocal Gamma (entire, Mathlib's `Γ⁻¹ = 0` at poles is
   correct) or Pochhammer polynomials: no junk values, no off-pole hypotheses.
4. **Transforms in the variable `t`** with `sinh t dt`; the `x = cosh t`, `dx` form is prose.
5. **Order-`m` Mehler–Fock** only for the `K`-types `(m, 0)` (functions on the disc), which have
   no discrete-series terms; the general `(k, m)` transforms with `km > 0` are Beyond.
6. **No Legendre-roadmap names in Lean.** `P_τ` appears only through `𝔓^τ_{00}` (Laplace
   integral, 1.3) because SpecialFunctionsLegendre is not on main; when it lands, an agreement
   lemma `boostMatrixElement τ 0 0 t = Complex.associatedLegendreP τ 0 (cosh t)` can be added.

## Open questions

- Wawrzyńczyk (10.5.12), p. 373, prints the Mehler–Fock inversion with the constant `1/(2π²)`;
  with his `F̃(ν) = ∫ F(τ) 𝔓_{iν−1/2}(cosh τ) sinh τ dτ` (10.5.11) the constant is `1`
  (Parseval verified numerically to 10 digits, `check_mehler_fock.py`, and VK §7.8.4 (15)–(17)
  has `1`). Recorded in the README Sources line; worth an errata entry for the Wawrzyńczyk
  synopsis.
- VK §6.7.1 (10), p. 333, as read from the OCR (`Σ i^m 𝔓^τ_{m0}/Γ(τ+m+1) = cosh τt/Γ(τ+1)`)
  diverges numerically in our labels; the README states instead the verified `θ = π/2` case of
  the generating function, `Σ_k (−i)^k 𝔓^τ_{k0} = cosh^τ t`. The page image of p. 333 was not
  checked.
- The Mehler–Fock unitarity proof route (restriction of M4.P to bi-`K`-invariant functions)
  needs the normalization of M4.P's Plancherel measure; the README avoids stating the constant
  between `sinh t dt` and the image of Haar measure.
- 2.1 boundedness range `−1 ≤ Re τ ≤ 0` is not in Dieudonné (his synopsis marks the "iff" as
  supplementary); the proof route uses SpecialFunctionsLegendre 4.5.

## Locators

Read in the source text (VK1991.txt, page images, Dieudonne1980.txt, Miller1968.txt):
- VK §6.5.1–§6.5.7, §6.5.10, §6.6.1–§6.6.3, §6.7.1 (6)–(13′), §6.7.2 (3)–(13), §6.7.3 (1)–(5)
  (pp. 336–337), §7.7.1 p. 435 (page image), §7.8.4 (1)–(20) pp. 483–486.
- Wawrzyńczyk p. 357 ((10.2.13)–(10.2.15) and the Legendre function) and p. 373
  ((10.5.11)–(10.5.12)), from page images (PDF page = printed page + 15: p. 357 is PDF 372,
  p. 373 is PDF 388).
- Dieudonné §13 (150)–(151), p. 44, §14 (170)–(175), pp. 49–50: equation positions confirmed in
  the OCR (form-feed page minus 4); content per the synopsis, consistent with the OCR.
- Miller §5-18 (5.156)–(5.178), pp. 226–238: equation positions confirmed in the OCR; content
  per the synopsis.

Not re-read (not cited in the README): Wawrzyńczyk (10.3.10)–(10.3.13), (10.4.5)–(10.4.9),
Theorem 10.5.4 beyond p. 373; VK §6.4.3, §6.4.6, §6.7.5 (cited by Roadmap 2 only).

## Prior formalization (Part B)

New lean-SFVK files (never edits of existing ones), all building:
- `SFVK/SU11/Basic/MatrixElementsBasic.lean`: `boostMatrixElement`, `parabolic`, `sinhMeasure`,
  `plancherelMeasure`, `mehlerFock`, `mehlerFockOrder` with `_def` lemmas; proved
  `exp_neg_abs_le_re_boostBase` (bases off the branch cut), `entryA_parabolic`,
  `entryB_parabolic`, `parabolic_zero`, `parabolic_add`. No sorry.
- `SFVK/SU11/MatrixElements.lean`: Layers 1–4 and 5.1, 36 theorems, 35 sorry;
  `principalSeries_matrixElement_parabolic` is proved from `parabolic_eq_euler` and
  `principalSeries_matrixElement_euler_eq`. Conjunctions of the roadmap are split per AGENTS.md
  (`_row`/`_column`, `_left`/`_right`, `_lower`/`_raise`, `_row_alternating`). Two lean-DLMF
  bridges beyond Suggested.lean: `boostMatrixElement_zero_zero_eq_legendreP` and
  `boostMatrixElement_eq_associatedP` (`m ∈ ℕ`, `t > 0`; verified numerically against DLMF
  14.3.6, `check_assocP.py`; false for negative `m` at `τ = -1`, hence `m : ℕ`), and the `−sinh²`
  form with lean-DLMF's regularized `𝐅`.
- `SFVK/SU11/Transforms.lean`: 5.2–5.3, 5 theorems, all sorry.

Not in Part B: README 2.2 (the Bergman model `bergmanMeasure`, `diskAct`, `discreteAction` is
Roadmap 2's and is not yet in lean-SFVK) and `boostY` (Roadmap 2's; it is
`euler (π/2) t (−π/2)`, so the 5.1 `boostY` statement is a specialization of
`principalSeries_matrixElement_euler_eq`).
