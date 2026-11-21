# MotionGroupsBessel: working notes

Draft of Roadmap 4 of `ROADMAP_PLANS.md` §6 (Euclidean motion groups and Bessel functions). Not
submitted. The numerical checks are the scratchpad scripts `checks1.py`–`checks6.py` and
`checks5_macdonald.py`, `contraction.py` (sfvk/r38/MotionGroupsBessel); they are not part of the
roadmap.

## Ownership survey (Tau Ceti main, 2026-11-20)

- SpecialFunctionsBessel (on main) owns, for complex order: generating function and Jacobi–Anger
  (4.1), multiplication theorem, Neumann and Graf (4.2), Gegenbauer addition and
  `hasSum_cexp_gegenbauer` (4.3), Neumann series (4.4), Bessel/Poisson/Mehler–Sonine and the
  `cosh` form of `K_ν` (5.1), Weber integrals (11.2), three-Bessel integrals 10.22.74–75 (11.3),
  plane wave 10.60.7 `hasSum_planeWave` (11.5). Its Beyond: Hankel and Kontorovich–Lebedev
  transforms and the radial Fourier transform in ℝⁿ "deferred, with no planned roadmap"; the
  Mehler–Heine limits "belong to the orthogonal-polynomial and Legendre roadmaps".
- LaguerreJacobi, SpecialFunctionsOrthogonalPolynomialsGeneral (main) and SpecialFunctionsLegendre
  (in review, not on main) do not state the Mehler–Heine limits. Decision taken here: own the two
  group-derived integer-parameter limits (Wigner `d` and Gegenbauer); leave general Jacobi
  (DLMF 18.11.5 for complex α, β) to the orthogonal-polynomial roadmaps.
- NoncompactQuantumSymmetry M2 (regular Mackey machine) supplies the classification and the
  irreducibility of the hyperbola models of ISO(1,1); M4.TypeI/M6 are Roadmap 2's concern.
- Roadmap 2 (SpecialFunctionsGroupModels, open PR) owns M(n), ISO(1,1), the sphere models for real
  R > 0, matrix elements in general, §4.3's template ODE and Gel'fand pairs; its "Scope" says the
  Bessel identification is not its target. Roadmap 1 owns `wignerSmallD`, Jacobi form, Y_l^m.
- Roadmap 5 (higher spheres, parallel) should own the plane-wave expansion in ℝⁿ, n ≥ 4, with
  harmonics of S^{n−1}; here only n = 3 with Roadmap 1's Y_l^m. Coordination point.

## Decisions to put to the author

1. Convention `T_R` with `e^{iR⟨a,ξ⟩}` (VK's `T_{iR}`, Miller's `(ρ)`), consistent with Roadmap 2
   §2.6; complex `R` allowed for the representation law, realization and matrix elements.
2. The circle is `AddCircle (2π)` with `haarAddCircle` (dψ/2π) and `fourierBasis`, as in the SU11
   code; rotations are matrices of `SOn 2` with an angle `rotAngle` via `Complex.arg`.
3. Hankel transform owned for real `ν > −1` (not only the group-derived integer and half-integer
   orders), by the Laguerre-eigenfunction route of VK Vol. 2 §10.2.6.
4. Miller's T₃ (Layer 3) is included although it is a complex local group: its matrix elements are
   explicit power series and the addition theorem is a statement about Laurent coefficients.
5. ISO(1,1): only the hyperbola model, its L² realization and the Macdonald kernel; Gamma and
   Hankel kernels and the quasi-regular representation of ISO(1,1) are in Beyond.
6. Prior-formalization module names in the README must be kept in step with the code.

## Open questions

- `isSphericalFunction_motion_iff`: the classification route ("in the same way", Dieudonné p. 57)
  needs that a spherical function is an eigenfunction of the Laplacian, i.e. smoothness of
  spherical functions (continuous ⇒ smooth via convolution with a bi-invariant approximate
  identity). Roadmap 2 §5.2 does not provide this; route to be written out.
- `circleRep_irreducible` for non-real R: the argument with difference quotients needs that the
  closed invariant subspace is invariant under the derivative, which holds since the orbit of a
  trigonometric polynomial is differentiable in norm. Worth stating as a lemma.
- `hankelTransform_hankelTransform` for real ν > −1: the identification of the Laguerre-diagonal
  unitary with the integral operator on C_c^∞(0,∞) needs dominated convergence on the Abel-summed
  kernel (VK Vol. 2 (17)); alternatively a direct Weber–Schafheitlin route.
- Does Roadmap 5 also want the zonal functions of SO(n) (Gegenbauer) — then 7.2 should consume its
  normalization.

## ROADMAP_PLANS statements found wrong or adjusted

- "matrix elements i^{n−m} J_{m−n}(R r) e^{…}": with Roadmap 2's convention
  D_{mn} = ⟪e_m, T e_n⟫ the order is J_{n−m}; i^{n−m} J_{m−n} would be (−i)^{n−m}J_{n−m}.
- VK §4.2.3: T_R ≅ T_{−R} on one branch is false (erratum E04.2.02 in ERRATA-VK.md).

## Sources actually read (printed pages)

- VK Vol. 1 (offset 23): pp. 165–176 (§§4.1.1–4.2.4), pp. 193–198 (§§4.4.1–4.4.3 start).
- VK Vol. 2 (1993, offset 18): pp. 48, 51, 186, 188.
- Miller 1968 (offset 6): pp. 52–57, 62–65, 70–71, 73.
- Dieudonné 1980 (offset 5): p. 57 (pp. 55–56 read through the synopsis only).
- Edmonds (4.1.15), (4.1.23): through Roadmap 1, not re-read.

## Locators not yet re-read in the source

- Dieudonné §16 (188)–(192), pp. 55–56 (cited in 6.2 together with p. 57).
- Miller (3.12), (3.16): the formulas themselves are illegible in the extraction (p. 56–57); the
  surrounding text was read.
- VK Vol. 2 §9.1.8, p. 19, and §10.2.6 (13)–(15) on p. 187 (from the synopsis).
- Wawrzyńczyk Ch. 7 (scanned PDF, no text): not used.
- KV05 §1 and Miller 1977 Ch. 1: not used.

## lean-SFVK code (SFVK/MotionGroups)

Differences between Suggested.lean and the SFVK statements, for the author:
- Conjunctions are split (AGENTS one-fact rule): `circleAction_mul` / `circleAction_one`,
  `millerAction_mul` / `millerAction_one` (both proved, in Basic), `exists_rotation_eq` /
  `rotAngle_rotation`, `polar_mul` → `toComplex_polar_mul_a` / `polar_mul_k`,
  `exists_hyperbolaRealization_iff` / `isUnitary_hyperbolaRep`, `besselZonal_ode` /
  `contDiff_besselZonal`, `bounded_besselZonal_iff` / `norm_besselZonal_le_one`.
- lean-DLMF in place of local copies: `ultrasphericalPolynomial` (theorem renamed
  `tendsto_ultrasphericalPolynomial_besselJ`), `laguerrePolynomialL`, `sphericalJ`,
  `DLMF.Legendre.sphericalHarmonic l m θ φ` (plane wave stated with `cos γ` written out, sum over
  `m ∈ [-l, l]`); `SFVK.SU2.wignerSmallD` and `ContRepresentation.matrixElement` from lean-SFVK.
- Added: `rotation_zero`, `toComplex_planePoint`, `besselZonal_zero_right`, `besselJEntire_sq`
  (`E_m(u²) = u^{-m} J_m(u)` on the slit plane), `integral_exp_cosh_eq_besselK` (the Macdonald
  kernel, proved from `DLMF.Bessel.besselK_eq_half_integral`), `motionApply_mul`,
  `isCircleRealization_circleRep`, `isHyperbolaRealization_hyperbolaRep`.
