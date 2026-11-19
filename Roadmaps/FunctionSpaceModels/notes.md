# FunctionSpaceModels: working notes (not part of the roadmap)

Roadmap 2 of ROADMAP_PLANS.md §5, "function-space models of noncompact groups". Pins: Tau Ceti
396c3bd, Mathlib 1b1ccf4 (the lake of ~/lean-SFVK). `Suggested.lean` compiles with 61 `sorry`
declarations and no other diagnostics. Numerical checks: the `check_*.py` scripts in the session
scratchpad (`sfvk/FunctionSpaceModels/`); every number quoted in the README was recomputed there.

## Decisions

- **Organization by subject.** Layers: groups in coordinates; `G`-spaces and multipliers; models;
  matrix elements; infinitesimal operators of the circle models; Gel'fand pairs. VK, KV,
  Wawrzyńczyk, Dieudonné and Miller are cited by locator in each subsection; SYNOPSIS IDs only in
  the closing provenance table.
- **`matrixElement` is a plain function**, `⟪e m, π g (e n)⟫`, with the bridge
  `matrixElement_eq_conj_matrixCoeff`. Tau Ceti's `ContRepresentation.matrixCoeff` takes
  `Continuous π` in the operator-norm topology, which fails for every infinite-dimensional model
  here (the left regular representation of a nondiscrete group is not norm continuous), so it
  cannot be the general definition.
- **Left-action multiplier convention** `(T(g) f)(x) = α(g, x) f(g⁻¹ • x)`; the `SU(1,1)` circle
  and disc models keep the VK right action on points (`circleAct`, `diskAct`) and are linked by
  `g • z = z · g⁻¹`.
- **`L²` representations by choice**: `multiplierRep`, `principalSeries` are the continuous
  representation agreeing a.e. with the formula when one exists, trivial otherwise; `_spec`
  theorems assert existence. This avoids stating an `Lp`-level construction in the prototype.
- **`ε` indexed by `e : Fin 2`** (`e = 2ε`), mirroring Roadmap 1's `d = 2j`.
- **Edmonds convention, aligned with Roadmap 1** (author's choice). Euler angles
  `g(α, t, γ) = k_α b_t k_γ`, `k_α = diag(e^{iα/2}, e^{−iα/2})`,
  `b_t = [[cosh t/2, sinh t/2], [sinh t/2, cosh t/2]]` (in `su11` for our form
  `[[a, b], [conj b, conj a]]`). The boost letter is `t`, not `τ`, because `τ` is VK's
  principal-series parameter throughout Layers 2–5. Verified relation (`eulerSU11_continuation`,
  `check_edmonds.py`): `bBeta(it) = boostY t` and `b_t = k_{−π/2} bBeta(it) k_{π/2}`, hence
  `eulerD α (it) γ = g(α + π/2, t, γ − π/2)`. VK's `g(φ, t, ψ) = g_φ a_t g_ψ` is literally
  `g(φ, t, ψ)` (same matrices); the conversion is in the basis: VK's `e^{−ikθ}` (weight label
  `k + ε`) is `e_m`, `m = −(k + ε)`, so `t^{VK} = D_{−·,−·}` as in Roadmap 1. Basis
  `e_m = e^{inθ}`, `m = n − ε`, with `T(k_α) e_m = e^{imα} e_m` (weight `2m` for
  `κ(u) = diag(u, conj u)`); `D_{m'm}(g(α, t, γ)) = e^{im'α} D_{m'm}(b_t) e^{imγ}`
  (`principalSeries_matrixElement_euler`); ladder operators `J_± = −A₁ ± iA₂`, `J₃ = −iA₃`
  with `J₊ e_m = (m − τ) e_{m+1}`, `J₋ e_m = −(m + τ) e_{m−1}`; the 4.3 equation in `(m', m)`.
  Discrete series: `zʲ` is `e_m`, `m = k/2 + j`. SU(1,1) matrix entries renamed `a, b` to free
  `α, β, γ` for angles.
- **Haar normalization kept at VK's `(8π²)⁻¹ sinh t dα dt dγ`** (VK §6.1.4 (2), p. 275, rechecked
  on the page image text: SU(2) gets `1/16π²` in (1), SU(1,1) `1/8π²` in (2)). Total mass is
  infinite; the normalization is fixed by `su11Haar {t ≤ T} = cosh T − 1`.
- **Spherical functions** are continuous, bi-`K`-invariant, `φ(1) = 1`, functional equation, no
  boundedness (`IsSphericalFunction`); `isSphericalFunction_iff` gives Wawrzyńczyk's form.
  `bounded_sphericalFunction_iff_character` (bounded ones = characters of integrable
  bi-invariant functions) and `exists_isUnitary_of_sphericalFunction` (positive-definite ones
  from unitary representations with a `K`-fixed unit vector) are stated. Check: `φ_τ(b_t) =
  P_τ(cosh t)` is spherical for all `τ` (functional equation verified numerically at
  `τ = 1, 1/2, −0.3`) and bounded iff `−1 ≤ Re τ ≤ 0`; `φ_1(b_t) = cosh t` is the unbounded
  example (`check_nqs3.py`).
- **Gel'fand pairs with `C_c` bi-invariant functions** (Dieudonné).

### Decided 2026-11-19 (author)

1. Boost letter `t`: approved.
2. Haar normalization `(8π²)⁻¹ sinh t` (VK): approved; the factor-2 relation to the formal
   continuation of Roadmap 1's `(16π²)⁻¹ sin β` is a remark in README Conventions.
3. NoncompactQuantumSymmetry: one owner. Whatever it owns is consumed by section with its
   hypotheses; this roadmap gives its concrete model plus a dictionary (agreement theorem with
   the parameter map). Outcome per object below.
4. Motion groups: this roadmap owns `M(n) = ℝⁿ ⋊ SO(n)`, `ISO(2)` and `ISO(1,1)` as
   topological groups. Rechecked 2026-11-19: Mathlib has only `Matrix.specialOrthogonalGroup`;
   Tau Ceti has `semidirectProductMulEquiv` (affine isometries as a semidirect product,
   `Analysis/Normed/Affine/Isometry/SemidirectProduct.lean`) and the algebraic `ℝⁿ ⋊ O(n)` of
   `Geometry/Manifold/Riemannian/Isometry/Euclidean.lean`, no topology on `SemidirectProduct`;
   roadmaps on main (LieGroups, LieGroupsPartII) mention `ℝⁿ ⋊ O(n)` only as a non-example; NQS
   uses `ℝ² ⋊ Spin(2)`, `ℝ³ ⋊ SU(2)`, `E(2) = Δ/{±1}` and `ℝ⁴ ⋊ SO(3)` without owning the
   topological groups as such. Stated: `MotionGroup` (structure with proved group law, induced
   topology), `IsTopologicalGroup` and `LocallyCompactSpace` instances (sorry), `motionHaar`,
   `motionHaar_isHaarMeasure` (Haar + right invariant), `motionGroup_polar`; `ISO11` likewise
   with `lorentzBoost`, `iso11Haar_isHaarMeasure`; `ISO2 = MotionGroup 2`.
5. Spherical functions without boundedness, with the bounded-character and positive-definite
   theorems and an unbounded Check: done as above.

### NoncompactQuantumSymmetry outcome per object (upstream/main README and Suggested.lean)

| Object | NQS owner | Here |
|---|---|---|
| `SL(2,ℝ) ≅ SU(1,1)` conjugacy `C₀` | M4 (spacelike stabilizer) | dictionary `sl2rToSU11_spec` (formula, hom, `k_t ↦ k_{2t}`) |
| Principal series | M4 dual (normalized induction, irreducibility, `ν ∼ −ν`, `D_1^±` endpoint) | circle model ours (law, `L²`, unitarity iff `Re τ = −1/2`, adjoint, weights); agreement `principalAction_compactPicture`, `ν = −(2τ + 1)` (identity transport `W`); irreducibility, equivalence, `D_1^±` consumed |
| Complementary series incl. completion | M4 (invariant forms, completion), M5 (compact eigenvalues `a_{2j}`) | weights `complementaryWeight_pos` ours; dictionary `complementaryWeight_ratio` (= M5's `a_{2j}(ν)`, `ν = −(2τ+1)`); `complementaryForm`/`complementaryForm_invariant` removed |
| Holomorphic discrete series | M4 `D_k^+` (irreducibility), M6.C half-plane models | Bergman model ours (law, isometry, kernel, weights `discreteAction_rot`); `A²_k ≅ D_k^+` prose agreement; irreducibility consumed |
| Antiholomorphic discrete series | M4 `D_k^−` | model `antiDiscreteAction` + `antiDiscreteAction_spec` ours (stated); weights `−(k + 2j)` in M4 units; irreducibility consumed |
| Casimir | M4.SL2R `q_B`, M4.P values | our eigenvalue `τ(τ+1)` on the model; dictionary `H_K = 2J₃`, `E_+ = −J₊`, `E_− = J₋`, `q_B = −Casimir` (verified `check_nqs.py`); values on unitary irreducibles consumed |
| K-types | M4 compact weights | dictionary: M4 weight `n` = our `2m`; lists consumed |
| Plancherel | M4.P | Beyond (consumed, not a target) |
| Heisenberg / Schrödinger | M2 shear block `π_b` (unitarity, continuity, central character, irreducibility, classification) | our line model (formula, unitarity); agreement `fourier_schrodinger`; irreducibility removed from `schrodinger_spec`, consumed from M2 (was OAD D4.LCAWeyl) |
| `ax + b` | none specific (M2 general) | ours (`axbRep_spec` incl. irreducibility); classification via M2 |
| Motion groups as groups | none | ours (0.3) |
| Sphere models | M6 Euclidean adapters `T_(κ,e)`, `S_(η,s)`; M4.TypeI `E(2)` | ours for the model; `n = 2, 3` dictionary to `T_(R,0)`, `S_(R,0)` with irreducibility consumed; `n ≥ 4` irreducibility ours |
| Gel'fand pairs, spherical functions | none (M0 only uses `(SL(2,ℝ), SO(2))` as a pair of groups) | ours (Layer 5) |

- **Boundary with SmoothBanachRepresentations / AFORG §2.7 / NQS M0.** The general derived action,
  smooth vectors and skew-adjointness are consumed; Layer 4 computes explicit orbit derivatives of
  `e^{−ikθ}` with the same convention `d/dt π(exp tX) v` at `0`.
- **Boundary with the RepresentationTheory index.** The index stops at compact groups on the
  unitary side (no infinite-dimensional unitary representations of noncompact groups, no
  Plancherel, no tempered spectrum). This roadmap is not in that family; it owns explicit models
  and their analysis, and harmonic analysis on `K\G/K` up to the spherical transform; it owns no
  classification, decomposition or Plancherel formula (Beyond).
- **Schrödinger irreducibility** is consumed from NQS M2's shear block through `fourier_schrodinger`;
  the real-Heisenberg Stone–von Neumann theorem in Hilbert-multiplicity form is
  MetaplecticAutomorphicForms §1.2 (not on main), named in prose only.

## Supplier status (upstream/main 19ee622, checked 2026-11-19)

| Supplier | Status | Consumed in |
|---|---|---|
| Tau Ceti `ContRepresentation.*`, `leftRegular`, PositiveDefinite, OneParameter, `HeisenbergGroup` | at pin | 0.2, 1.3, 2.5, 3.1, 4.1, 5.3 |
| Mathlib Haar, `modularCharacter`, `toSphere`, Fourier on `AddCircle`, `HilbertBasis`, `SpecialLinearGroup` | at pin | throughout |
| SmoothBanachRepresentations 0.2, 3.1 | on main | 4.1–4.2 |
| AutomorphicFormsOnReductiveGroups §2.1, §2.7 | on main | 3.3, 4.1 |
| NoncompactQuantumSymmetry M0, M1, M2, M4, M4.SL2R, M4.TypeI, M4.P, M5, M6, M6.C | on main | 1.1, 2.1–2.6, 4.1–4.2, Beyond |
| OperatorAlgebraDynamics D1.CentralTwists | on main | 2.5 (D4.LCAWeyl boundary only) |
| RepresentationTheory/LieGroups Layer 9 | on main | 0.1, 5.4 |
| RepresentationTheory/CompactGroups Layer 5, `gap:banach-gfinite-density` | on main (gap named there) | 3.3 |
| RealSemisimpleLieGroups, SmoothRepresentationsOfLocalGroups | on main (boundary only) | — |
| MetaplecticAutomorphicForms §1.2 | absent from main | prose only (2.5 boundary) |
| SpecialFunctionsLegendre (PR #2121) | in review | not consumed (Checks are numeric) |
| Roadmap 1 SU2MatrixElements | draft in this repo | conventions (Edmonds); boundary (3.1–3.2, 5.4) |

## ROADMAP_PLANS.md statements found wrong or outdated

1. §3 "no second matrix-coefficient definition": Tau Ceti's `matrixCoeff` needs norm
   continuity and cannot serve strongly continuous infinite-dimensional representations; a plain
   `matrixElement` with a bridge theorem is required (Roadmap 1's draft already points to it).
2. §5 Layer 2.3: "irreducibility of the SU(1,1) series belongs to Roadmap 7". NQS M4 on main
   already owns irreducibility, equivalences and exhaustion for `SL(2,ℝ) ≅ SU(1,1)`; Roadmap 7
   would overlap it.
3. §5 Layer 2.3: `ax + b` irreducibility/classification and "general Mackey theory excluded" —
   the classification is NQS M2 (regular Mackey machine), already on main; this roadmap proves
   irreducibility of `T_λ` directly and consumes the classification.
4. §5 Layer 2.5: derived operators, agreement with Stone generators and the Lie homomorphism are
   owned by SmoothBanachRepresentations, AFORG §2.7 and NQS M0, not by this roadmap.
5. The RepresentationTheory family index does not list SmoothBanachRepresentations, although
   that roadmap sits in the family directory.
6. §5 Layer 2.0 asks for `M(n)`/`ISO` group types "from Tau Ceti/Mathlib"; none exist at the pin,
   and this roadmap owns them (decision 4).
7. §2.1 list of Tau Ceti inputs is outdated: it omits `posSemidef_inv_mul_iff_exists_isUnitary`,
   `IsUnitary.posSemidef_inner_map_inv_mul`, `Measure.leftRegular` with unitarity and strong
   continuity, `toStronglyContinuousGroup` and `HeisenbergGroup`.
8. §3 Euler-angle convention "a_θ in the rotation subgroup": for `SU(1,1)` the middle factor is a
   boost `b_t`, with `γ`-range of length `4π`; and the plan's VK convention for SU(2) is superseded
   by the author's Edmonds convention (Roadmap 1), which this roadmap follows.

## Open questions for the author

- Confirm `matrixElement` (plain) rather than an extension of `matrixCoeff` to strongly continuous
  representations in Tau Ceti.
- NQS M5 writes the compact eigenvalues as `a_{2j}(s)`; the dictionary takes `s = ν = −(2τ + 1)`
  (the sign fixed by the identity transport `W`). If M5's `s` is M4's `−ν`, the ratio theorem
  flips to the reciprocal; worth a line in a review of NQS.
