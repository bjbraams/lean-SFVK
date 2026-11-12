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

## Dependencies and import layers

- `SFVKMathlib/` (modules `SFVKMathlib.*`) holds general results that are not specific to
  Vilenkin and Klimyk. `SFVKMathlib` may import Mathlib, TauCeti and lean-DLMF, but not
  `SFVK`; `SFVK` modules may import `SFVKMathlib`.

Mathlib and TauCeti are allowed throughout the SFVK library, including when filling
existing admissions. Preserve complex branches, normalizations, exceptional parameters
and the meaning of totalized series and integrals when adopting upstream statements.

## Statements and style

- Drop a SFVK exclusion of poles or singular points when Lean's totalized statement still
  holds there.
- Changing the statement of a tagged theorem or the body of a definition needs the user's
  approval. Report a suspected-false statement with the evidence, and do not silently weaken
  or repair it.
- Lines are at most 100 characters and files at most 1,500 lines; split a long file along
  its SFVK subsections.
- Module and declaration docstrings follow Mathlib style: state the mathematics, the SFVK
  references and the hypotheses. They contain no history (no dates, development rounds,
  former names or "previously admitted" remarks); history belongs in `REVIEW.md`.

## SFVK statement acquisition

- Cover definitions and mathematical theorems in the selected SFVK scope, including
  results stated in prose. Exclude graphical results and application notes.
- Purely numerical results are out of scope: tabulated function values, decimal values of
  zeros, constants or expansion coefficients (for example γ ≈ 0.5772156649). Exact values
  and asymptotic expansions remain in scope. A crude numerical bound may be proved as an
  untagged helper lemma when a proof needs it (for example `γ < 3/5`).
- When a result is already in Mathlib, record a comment and a precise pointer to
  the upstream declaration instead of reproving it locally. Preserve any domain
  or branch differences when distinguishing upstream coverage from missing results.
