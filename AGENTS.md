# Project instructions — lean-SFVK

Before working, read and follow [the shared Lean instructions](../lean-codes/AGENTS.common.md),
then apply the project-specific rules below. Resolve that path relative to this file.
Local rules take precedence over the shared defaults. If the shared file is unavailable,
report that fact rather than proceeding without it.

## Build settings

- Lake root: the directory containing this `AGENTS.md`, also called the main project
  directory.
- Build output: `.lake/build-SFVK`; preserve the matching `buildDir` in `lakefile.toml`.
- Ordinary build command: `lake build > /tmp/SFVK-build.log 2>&1`.

## Project

This project formalizes special functions following the group representation approach as
presented by Vilenkin and Klimyk among others. The PDF sources are in the References
subdirectory.

The first phase of the project is a prose mathematical inventory of definitions, theorems
and other statements that are appropriate for formalization.

The second phase of the project is Lean formalization. The Lean codes live under `SFVK/`.

## Bibliography

At first the project is bibliographical, not involving any Lean code. Several PDF files
are available in the References subdirectory. We treat them as two units.
The first unit is one reference, the Part II by Klimyk and Vilenkin on representation
theory and special functions in the book edited by Kirillov, Representation theory ..., II,
Springer (EMS 59). This Part II of that book has Chapters 1 through 6. The files
SYNOPSIS-KV01.md through SYNOPSIS-KV06.md contain mathematical synopses of the six chapters
in the form of Lean-actionable mathematical statements (definitions, theorems, lemmas, and
where appropriate also formulas that do not carry a heading). By Lean-actionable I mean
statements that can, in later work, be turned into Lean statements. But the style of the
SYNOPSIS*.md files is mathematical; these files are meant for readers that know the
mathematics but that may not be familiar with Lean. In general, the SYNOPSIS follows the
order of the reference, except that sometimes definitions may be placed earlier in the
SYNOPSIS than they occur in the reference. In the process of assembling the Synopses
errata or suspected errata may be found and these go into ERRATA-KV.md.
The second unit is the three-volume set of works by authors Vilenkin and Klimyk (that order),
years 1991 through 1993, Representations ... Vols 1 through 3. The chapters in those books
are numbered consecutively, chapters 1-19 ignoring the introduction (ch 0). Synopses of
those chapters are in files SYNOPSIS-VK01.md through SYNOPSIS-VK19.md and errata (or
suspected errata) are in ERRATA-VK.md.

## Dependencies and import layers (adopted 2026-11-19, following lean-DLMF)

- `SFVKMathlib/` (modules `SFVKMathlib.*`) holds general results that are not specific to
  Vilenkin and Klimyk or to special functions (matrix elements in a Hilbert basis, multiplier
  actions, quasi-invariant measures). `SFVKMathlib` may import Mathlib, TauCeti and lean-DLMF,
  never `SFVK`; `SFVK` modules may import `SFVKMathlib`. Register a new `SFVKMathlib` module in
  `SFVKMathlib.lean` together with a line in its module docstring.
- lean-DLMF is a Lake path dependency (package `LeanDLMF`, `../lean-DLMF`). Use its special
  functions (`DLMF.OrthogonalPolynomials.jacobiPolynomialP`, `DLMF.Legendre.ferrersPNat`, …) with
  their DLMF normalizations instead of local copies; state any other normalization through a
  conversion theorem. Never copy lean-DLMF code here and never edit lean-DLMF from this project.
- The Lean code lives under `SFVK/`, one directory per area (`SU2/`, `SU11/`, …). Each area has:
  - a foundational layer: descriptive files under `SFVK/<Area>/Basic/`, collected by the
    umbrella `SFVK/<Area>/Basic.lean`;
  - a theorem layer: the other files under `SFVK/<Area>/`;
  - an area umbrella `SFVK/<Area>.lean` importing both.
  `SFVK/Basic.lean` is the foundational entry point and imports every area's `Basic.lean`;
  `SFVK.lean` imports `SFVK.Basic` and every area umbrella; `Main.lean` imports `SFVK` and
  `SFVKMathlib`. Every new module must be reachable from its umbrella; register it in the same
  change that creates it.
- Content of the foundational layer: for each central object (group, coordinate system, model,
  matrix element, special function), the definition with a docstring stating its convention,
  domain and normalization, and its basic API: unfolding and `simp` lemmas, special values,
  symmetries, the group or representation law, continuity, and the bridge to the corresponding
  Mathlib, TauCeti or lean-DLMF object where one exists. Only fully proved results go into the
  foundational layer: no `sorry` and no dependence on admitted lemmas.
- A foundational module may import only Mathlib, TauCeti, `SFVKMathlib` and other foundational
  modules. It must not import a theorem-layer module (even in its own area) or a lean-DLMF
  module; a definition that needs lean-DLMF lives in the theorem layer.
- Definitions never depend on `sorry`. A definition whose existence is not yet proved is made
  total by a dependent `if` on the existence statement, with a trivial fallback value (for
  example `principalSeries`, which is the trivial representation unless a realization exists);
  the existence is then a theorem-layer target.
- There is no hierarchy between areas: imports in both directions between areas are allowed,
  and only the file graph must be acyclic. If a definition or lemma is needed below its current
  file, move it down unchanged rather than copying it.

Mathlib and TauCeti are allowed throughout the SFVK library, including when filling
existing admissions. Preserve complex branches, normalizations, exceptional parameters
and the meaning of totalized series and integrals when adopting upstream statements.

## Namespaces and names (adopted 2026-11-19, following lean-DLMF)

- Every declaration under `SFVK/` lives in `SFVK.<Area>` (`SFVK.SU2`, `SFVK.SU11`); nothing is
  declared directly in `SFVK` except the carrier of an area's group (`SFVK.su11` and the type
  `SFVK.SU11`, with its API in namespace `SFVK.SU11`, as TauCeti does for `TauCeti.SU2`). Never
  name a type after a Mathlib class (`Group`, `Module`, …), which shadows the class inside the
  namespace.
- Never declare a new name in a Mathlib or TauCeti namespace from `SFVK/`: a later upstream
  declaration of the same name breaks the build. The exception is a dot-notation lemma whose
  namespace is fixed by the head symbol of its conclusion.
- `SFVKMathlib/` uses the namespace of the API it extends and Mathlib-style names, as
  candidates for upstreaming (`ContRepresentation.matrixElement`,
  `MeasureTheory.Measure.IsQuasiInvariantWith`, `MulAction.multiplierAction`).
- Helper families go in a descriptive sub-namespace of the area, never behind an abbreviated
  name prefix and never in an `…Aux` namespace.
- Every declaration name is spelled out (`circleDenominator`, not `circleDenom`;
  `magneticWeight`, not `edWeight`; `wignerSmallD`, not `smallD`), with no source initials and
  no single variable letters (`eulerMiddle`, not `bBeta`). Lemma names follow Mathlib's
  conclusion-first style (`isUnitary_principalSeries_iff`, `continuous_matrixElement`). A suffix
  `_one` means "at the identity"; name a statement about spin one half `…_spinHalf`. Names never
  carry identifiers of development rounds or agents, neither in declarations nor in file names.
- One fact per lemma: split a conjunction of independent facts into separate lemmas
  (`exists_euler_eq` and `bijOn_euler`, `wignerSmallD_zero` and `wignerSmallD_pi`). A lemma that
  gives several entries of one object may be split into `@[simp]` lemmas per entry.
- Definitions in the foundational layer and in `SFVKMathlib` carry `@[expose]`, so that other
  modules can unfold them; give each also a `_def` or `_apply` lemma.
- Every file starts with the copyright header including `Authors: Bastiaan J Braams`.
- There is no source-tag attribute (lean-DLMF's `@[dlmf …]` tags are specific to that project).
  Source locators go in the module and declaration docstrings, as author, short title, and
  theorem, section or equation number with the printed page (for example Edmonds, *Angular
  Momentum in Quantum Mechanics*, (4.1.15), p. 57). Never cite a locator that has not been read
  in the source.

## Statements and style

- Drop a SFVK exclusion of poles or singular points when Lean's totalized statement still
  holds there.
- Changing the statement of a target theorem or the body of a definition needs the user's
  approval. Report a suspected-false statement with the evidence, and do not silently weaken
  or repair it.
- Lines are at most 100 characters. A Lean file (`*.lean`) must not exceed 1,500 lines, and
  should stay under a soft limit of 1,000 lines. Split a long Lean file along its SFVK
  subsections. Other files, such as the Markdown synopses, errata and reviews, have no line
  limit; this overrides the shared file-length default.
- Module and declaration docstrings follow Mathlib style: state the mathematics, the SFVK
  references and the hypotheses. They contain no history (no dates, development rounds,
  former names or "previously admitted" remarks); history belongs in `REVIEW.md`.

## SFVK statement acquisition

- Cover definitions and mathematical theorems in the selected SFVK scope, including
  results stated in prose. Exclude graphical results and application notes.
- Purely numerical results are out of scope: tabulated function values, decimal values of
  zeros, constants or expansion coefficients (for example γ ≈ 0.5772156649). Exact values
  and asymptotic expansions remain in scope. A crude numerical bound may be proved as an
  helper lemma when a proof needs it (for example `γ < 3/5`).
- When a result is already in Mathlib, record a comment and a precise pointer to
  the upstream declaration instead of reproving it locally. Preserve any domain
  or branch differences when distinguishing upstream coverage from missing results.
