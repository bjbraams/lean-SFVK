# AffineHeisenbergGroups: working notes (not part of the roadmap)

Roadmap 6 of ROADMAP_PLANS.md, "affine, triangular and Heisenberg groups". Tau Ceti name
`SpecialFunctionsAffineHeisenbergGroups`. `Suggested.lean` compiles in the TauCetiRoadmap lake
(Tau Ceti 2fd255d pin; the module `TauCeti.Analysis.SpecialFunctions.Hermite.Function.HilbertBasis`
had to be built there first) with 46 `sorry` declarations and no other diagnostics. Gates
(texcheck, spancheck, idcheck, leading punctuation, line length) pass. Numerical checks: the
`checks*.py` scripts in the session scratchpad (`sfvk/r38/AffineHeisenbergGroups/`); every number
quoted in the README was recomputed there with mpmath.

## Targets

46 targets with a Lean name, plus 6 prose targets of the same standing (Mellin–Plancherel in 1.1,
the `S₄` coordinate change in 0.2, the three bullets of 2.6, Miller's Theorem 4.3 in 4.1).

## Ownership survey

- **Owned here**: the triangular group and its subgroups and factorizations; the oscillator group
  as an abstract group (SpecialFunctionsGroupModels owns only the matrix and its law); `T_χ` and
  its Mellin kernels; the Hermite matrix elements of the Schrödinger representation and their
  addition/orthogonality/completeness; Fock space and Bargmann transform in the form used here;
  the oscillator Fock representations; Miller's `G(0, 1)` model; the Charlier polynomials (no
  roadmap on main defines them; LaguerreJacobi excludes the rest of the Askey scheme).
- **Consumed**: SpecialFunctionsGroupModels §§0.2, 1.1–1.3, 2.4, 2.5, 3.1–3.2 (open PR, not on
  main; cited by section number in prose); LaguerreJacobi Layers 1–2 (on main);
  SpecialFunctionsConfluent (in review) for `W`, `M`, their integral representations,
  recurrences and equation; NoncompactQuantumSymmetry M2 and MetaplecticAutomorphicForms 1.2 for
  irreducibility / Stone–von Neumann; Tau Ceti Hermite basis and Heisenberg group.
- **Not restated**: SpecialFunctionsParabolicCylinder's Hermite–`D_n` bridge;
  OperatorTheory's harmonic oscillator.

## Decisions for the author

1. **Oscillator angle unreduced.** `Oscillator.α : ℝ`, so `Oscillator` is the cover of the matrix
   group (kernel `{(0, 2πk, 0)}`), and `oscillatorFock λ` exists for every real `λ`. Miller's
   `S₄` reduces `α` mod `2π` and needs integer `λ`. Alternative: `α : AddCircle (2π)` and
   `λ : ℤ`.
2. **Heisenberg in the oscillator group** is forced by SpecialFunctionsGroupModels' law:
   `(x, y, z) ↦ (x + iy, 0, −(z − xy/2)/2)` (checked numerically).
3. **`triangularRep` equivalence classes** (`γ = γ'`, `ρ = ρ'`) are derived here (Schur through
   the irreducible Heisenberg restriction); the sources do not state them.
4. **Kernel realization hypotheses** (`signedMellin_triangularAction`): `Re σ = 0`, `f ∈ C²` with
   compact support away from `0`, `a ≠ 0`, `0 < Re λ < c < 1`. The `a ≠ 0` hypothesis is needed
   (at `a = 0` the kernel integral diverges at `x = 0`); the source's formal computation omits
   it and handles `ε(τ)`, `z(b)` directly.
5. **Fock space** is the closed span of the monomials; `fockSpace_spec` says it is the a.e.-entire
   functions. The Bargmann kernel is the standard one for `U` and entire functions; VK Vol. 2
   (11), p. 420, uses antianalytic functions and `R^λ`.
6. **Mellin–Plancherel** is a prose target (no Lean statement); it is the only place
   `L²(dx/x)` unitarity of the Mellin transform enters, and Roadmap 2 already owns the
   unitarity of `T_λ`.
7. **`millerMatrixElement`** is defined by Miller's finite sum (4.24), which has no junk at
   `c = 0`; the Laguerre form carries `c ≠ 0`.
8. **`hermiteMatrixElement` with `m < n`** uses `(−conj α)^{n−m} L_m^{(n−m)}` rather than the
   continued `L_n^{(m−n)}`; both agree by VK Vol. 2 §12.1.6 (8), p. 417.

## Open questions

- SpecialFunctionsConfluent: does it own the Mellin–Barnes integrals of `W_{κ,μ}`? README 2.6
  treats their group derivation as a prose target and the identification as consumed.
- The normalization `e^{2τ} = x/(x + t)` of the factorization `g_+(t) g_1(x)` is computed here; the
  printed formula (VK Vol. 1 §5.2.1 (2), p. 213) is not legible in the scan, but the printed
  derivatives (3), p. 214, agree with this normalization.
- Klimyk–Vilenkin (19), p. 207, prints `Γ(λ − μ − 1)`; the numerics confirm `Γ(λ − μ + 1)`
  (already ERRATA-KV E04.1.04).

## Locators not re-read in full

Read in the source for this draft: VK Vol. 1 pp. 127–135, 207–214, 217, 219–220; VK Vol. 2
pp. 410–421; KV pp. 204–207, 218, 239; Miller pp. 85–88, 113, 117–118, 121–125; Wawrzyńczyk
pp. 425–430 (page images); Dieudonné p. 58.

Formula images missing from the text extraction (equation numbers and surrounding text read,
formula checked only numerically or through the parallel KV formula): VK Vol. 1 §5.1.1 (2)–(3),
(6)–(7), (9)–(12), p. 207–208; §5.1.2 (1), p. 208; §5.1.4 (1)–(4), (6), (8)–(13), pp. 211–213;
§5.2.1 (1)–(2), p. 213; §5.2.4 (2), (4)–(6), pp. 219–220; VK Vol. 1 §3.4.5 (5), p. 135; Miller
(4.24)–(4.28), pp. 87–88, (4.96), p. 113, (4.120)–(4.124), pp. 121–123, (4.126)–(4.127),
pp. 124–125; KV (5)–(7), p. 239. These should be checked against the page images before
submission.
