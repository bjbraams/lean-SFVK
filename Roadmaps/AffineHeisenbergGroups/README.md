# Special functions from affine, triangular and Heisenberg groups

**Summary.** This roadmap derives the Gamma and Beta functions, the Whittaker functions, and the
Hermite, Laguerre and Charlier polynomials as kernels and matrix elements of representations of four
solvable and nilpotent groups: the `ax + b` group, the group of real triangular `3 × 3` matrices,
the Heisenberg group and the oscillator group. The `ax + b` group, diagonalized by the Mellin
transform, gives the Gamma function as a kernel and its addition formula; the triangular group, in
the same Mellin realization, gives the Whittaker functions `W_{κ,μ}` and `M_{κ,μ}` as kernels of two
one-parameter subgroups; the Heisenberg group in the Schrödinger and Fock models gives the Laguerre
matrix elements of the Hermite basis, with their addition theorem, orthogonality, completeness and
the Charlier polynomials; the oscillator group adds a rotation to the Fock model; and Miller's
complex group `G(0, 1)`, which is the complexified triangular group, gives the Laguerre generating
function and addition theorem by expanding entire functions. The roadmap is a synthesis of several
sources and follows none of them in its organization: it is ordered by the groups, from their
coordinates, through the Mellin realization of the affine and triangular groups, to the Hermite and
Fock models of the Heisenberg and oscillator groups and the power-series model of `G(0, 1)`. Its
sources are Vilenkin–Klimyk (*Representation of Lie Groups and Special Functions*, Vol. 1 for the
affine and triangular groups and Vol. 2 for the Heisenberg group), Klimyk–Vilenkin (*Representations
of Lie Groups and Special Functions*, in Kirillov (ed.), Encyclopaedia of Mathematical Sciences 59),
Miller (*Lie Theory and Special Functions*, Chapter 4), Wawrzyńczyk (*Group Representations and
Special Functions*, Chapter 12) and Dieudonné (*Special Functions and Linear Representations of Lie
Groups*, §17); each subsection cites several of them by locator; see [References](#references).

Mathlib has the Gamma and Beta functions, the Mellin transform with its behaviour under dilation
(`mellin_comp_mul_left`), Fourier analysis on `ℝ`, Hilbert bases and `Lp` spaces. Tau Ceti has the
Heisenberg group `TauCeti.HeisenbergGroup`, the Hermite functions `TauCeti.hermiteFunction` as a
Hilbert basis of `L²(ℝ)` (`TauCeti.hermiteHilbertBasis`), and continuous representations with
unitarity. Neither has the triangular or oscillator groups, the Mellin realization of a group
representation, the Whittaker kernels, the matrix elements of the Schrödinger representation, the
Fock space, or the Charlier polynomials.

The roadmap covers:
- the triangular group with its one-parameter subgroups and factorizations, the oscillator group as
  a group with its matrix realization, and the embeddings of the Heisenberg group into both (Layer
  0);
- the `ax + b` group on the half-line in the Mellin realization: the dilation and infinitesimal
  operators, the Gamma kernel and the Mellin–Barnes addition formula of the Gamma function (Layer
  1);
- the representations `T_χ` of the triangular group on the line: cocycle, unitarity range,
  irreducibility and equivalence, restriction to the Schrödinger representation, infinitesimal
  operators, the signed Mellin realization with its matrix kernel, the power and Whittaker kernels
  of the one-parameter subgroups and the kernel composition law (Layer 2);
- the matrix elements of the Schrödinger representation in the Hermite basis as Laguerre functions,
  their addition theorem, orthogonality and completeness on `ℝ²`, the Charlier polynomials as matrix
  elements, and the Bargmann transform onto the Fock space (Layer 3);
- the representations of the oscillator group on the Fock space and their Laguerre matrix elements
  (Layer 4);
- Miller's representations of `G(0, 1)` on entire functions, their matrix elements, the Laguerre
  generating function and the Laguerre addition theorem (Layer 5).

## Scope and ownership

This roadmap owns the triangular group, the oscillator group as an abstract group with its
Heisenberg embedding, the representations `T_χ` and their Mellin kernels, the Hermite matrix
elements of the Schrödinger representation and their identities, the Fock space and Bargmann
transform as used here, the oscillator Fock representations, Miller's `G(0, 1)` model and the
Charlier polynomials (no other roadmap owns a Charlier definition; LaguerreJacobi excludes the rest
of the Askey scheme). It consumes:
- from SpecialFunctionsGroupModels (by section number): the `ax + b` group, its Haar measures and
  the oscillator matrix with its law (§0.2), the multiplier framework (§§1.1–1.3), the
  representations `T_λ` of the `ax + b` group on `L²(dx/x)` with their irreducibility and
  equivalence classes (§2.4), the Schrödinger representation with its Fourier dictionary (§2.5), and
  matrix elements with the addition theorem and unitarity relations (§§3.1–3.2);
- from LaguerreJacobi: the generalized Laguerre polynomials (its Layer 1), their orthogonality and
  Hilbert bases (its Layer 2);
- from SpecialFunctionsConfluent: Whittaker's `M_{κ,μ}` and `W_{κ,μ}` with their integral
  representations, recurrences and differential equation;
- from NoncompactQuantumSymmetry M2 and MetaplecticAutomorphicForms 1.2: the irreducibility of the
  Schrödinger representation and the Stone–von Neumann theorem;
- from Tau Ceti: the Hermite functions and their Hilbert basis, and the Heisenberg group.

SpecialFunctionsParabolicCylinder owns the bridge between Hermite functions and the parabolic
cylinder functions `D_n`, and OperatorTheory owns the harmonic oscillator as an unbounded operator;
neither is restated here.

## Conventions

- **Actions and multipliers** are those of SpecialFunctionsGroupModels §1.2: groups act on the left
  and `(T(g) f)(x) = α(g, x) f(g⁻¹ • x)` (`multiplierAction`), with the cocycle identity
  `IsMultiplierCocycle`. Representations on `L²` are `multiplierRep μ α`, the continuous
  representation agreeing almost everywhere with the formula when one exists.
- **Inner products** are conjugate-linear in the first argument, and
  `matrixElement U e m n g = ⟪e m, U g (e n)⟫`, as in SpecialFunctionsGroupModels §3.1.
- **`ax + b` group.** `AxB` with `(a, b)(a', b') = (aa', ab' + b)`, acting on `ℝ` by
  `g • x = x / a`. Vilenkin–Klimyk's `R_λ(a, b) f(x) = e^{λbx} f(ax)` with complex `λ` is
  `affineAction λ`; at `λ = iρ` it is the multiplier action of SpecialFunctionsGroupModels §2.4
  (`affineAction_mul_I`).
- **Triangular group.** `TriangularGroup` has coordinates `(a, b, d, τ)` and matrix
  `[[1, a, b], [0, e^τ, d], [0, 0, 1]]` (Vilenkin–Klimyk §5.1.1 (1), p. 207), so
  `(a, b, d, τ)(a', b', d', τ') = (a' + a e^{τ'}, b + b' + a d', d + e^τ d', τ + τ')`. It acts on
  `ℝ` by `g⁻¹ • x = e^τ x + a`. Klimyk–Vilenkin write the same matrix as `g(a, b, e^τ, d)`.
- **Heisenberg group.** Tau Ceti's `(x, y, z)(x', y', z') = (x + x', y + y', z + z' + x y')`, the
  matrix `[[1, x, z], [0, 1, y], [0, 0, 1]]`; it is the subgroup `τ = 0` of the triangular group
  through `(x, y, z) ↦ (a, b, d, τ) = (x, z, y, 0)`. The Schrödinger representation is
  SpecialFunctionsGroupModels §2.5's `(U(g) f)(u) = e^{i(z + yu)} f(u + x)`, with central character
  `e^{iz}`. Vilenkin–Klimyk Vol. 2 use `R^λ` with
  `(R^λ(a, b, c) f)(x) = e^{iλ(c + b·x − a·b/2)} f(x − a)` (§12.1.7 (14), p. 420); the
  matrix-element formulas of the sources are converted to `U` in 3.1.
- **Hermite basis** `h_n = TauCeti.hermiteFunction n`,
  `h_n(u) = He_n(u√2) e^{−u²/2} / (n! √π)^{1/2}`, the eigenbasis of `a† a` with `a = (u + d/du)/√2`,
  `a† h_n = (n + 1)^{1/2} h_{n+1}`.
- **Laguerre polynomials** `L_n^{(α)}` are LaguerreJacobi's explicit sum (DLMF 18.5.12), defined for
  every `α` in a `ℚ`-algebra, so `L_n^{(m − n)}` with `m < n` is the polynomial continuation, equal
  to `(m!/n!) (−x)^{n−m} L_m^{(n−m)}(x)` (Vilenkin–Klimyk Vol. 2 §12.1.6 (8), p. 417; Wawrzyńczyk
  adopts the same continuation in §12.1, p. 429).
- **Oscillator group.** `Oscillator` has coordinates `(w, α, δ) ∈ ℂ × ℝ × ℝ` with the law of
  SpecialFunctionsGroupModels §0.2,
  `(w₁, α₁, δ₁)(w₂, α₂, δ₂) = (w₁ + e^{−iα₁} w₂, α₁ + α₂, δ₁ + δ₂ − Im(e^{−iα₁} conj w₁ w₂)/4)`. The
  angle `α` is real, not taken modulo `2π`, so `Oscillator` covers the matrix group with kernel
  `{(0, 2πk, 0)}` (`Oscillator.toMatrix_eq_one_iff`), and the rotation weight `λ` of 4.1 is any real
  number; Miller's `S₄` (§4-11, p. 113) is the matrix group and needs integer `λ`.
- **Fock space.** `fockMeasure = π⁻¹ e^{−|ζ|²} dζ` on `ℂ`, the measure of Miller §4-13, p. 117, and
  of Wawrzyńczyk (12.1.6), p. 425, at `λ = 1`; `fockMonomial n = ζⁿ / √n!`.
- **Mellin transform** is Mathlib's `mellin f s = ∫_{(0,∞)} t^{s−1} f(t) dt`; the signed transforms
  of the triangular group are `F_±(λ) = mellin (x ↦ f(±x)) λ` (`signedMellin`).
- **Kernels.** A kernel `K(w, z; g)` acts on Mellin transforms by
  `F ↦ ∫_{c−i∞}^{c+i∞} K(w, z; g) F(z) dz`; written on the line `z = c + is` this is
  `i ∫ K(w, c + is; g) F(c + is) ds`. The factor `1/(2πi)` is part of the kernel, as in the sources.
- **Miller's `G(0, 1)`.** `MillerGroup` has complex coordinates `(a, b, c, τ)` and Miller's law
  (§4-2, p. 86, the computation after (4.20)); its real points form the triangular group through
  `(a, b, c, τ) ↦ (e^τ c, a, b, τ)` (`millerToTriangular`).

## Exact supplier contracts

### From Mathlib

- `mellin`, `mellin_comp_mul_left`, `mellin_comp_rpow`; `Complex.Gamma`, `Complex.betaIntegral`,
  `Complex.Gamma_mul_Gamma_eq_betaIntegral`.
- `MeasureTheory.Lp`, `HilbertBasis`, `Orthonormal`, `Submodule.topologicalClosure`.

### From Tau Ceti

- `TauCeti.HeisenbergGroup` with `TauCeti.HeisenbergGroup.equivProd`.
- `TauCeti.hermiteFunction`, `TauCeti.hermiteFunctionLp`, `TauCeti.hermiteHilbertBasis` and
  `TauCeti.coe_hermiteHilbertBasis` (`TauCeti/Analysis/SpecialFunctions/Hermite/Function/`).
- `ContRepresentation` with `ContRepresentation.IsUnitary`.

### From other roadmaps

- SpecialFunctionsGroupModels §0.2 (the `ax + b` group, the oscillator matrix and its law),
  §§1.1–1.3 (multipliers), §2.4 (the `ax + b` representations), §2.5 (the Schrödinger
  representation), §§3.1–3.2 (matrix elements, addition theorem, unitarity relations). The
  definitions are copied verbatim into `Suggested.lean`.
- LaguerreJacobi Layer 1 (the Laguerre polynomials, copied verbatim) and Layer 2 (orthogonality).
- SpecialFunctionsConfluent (Whittaker's `M_{κ,μ}`, `W_{κ,μ}`, copied verbatim, with their integral
  representations, recurrences and equation).
- NoncompactQuantumSymmetry M2 and MetaplecticAutomorphicForms 1.2 (irreducibility of the
  Schrödinger representation, Stone–von Neumann).

## How to read the build

Layer 0 is algebra in coordinates. Layer 1 needs only Mathlib's Mellin transform and Gamma function.
Layer 2 needs Layer 0, the multiplier framework and the Whittaker functions. Layer 3 needs the
Schrödinger representation, the Hermite basis and the Laguerre polynomials. Layer 4 needs Layers 0
and 3. Layer 5 needs Layer 0 and the Laguerre polynomials, and is independent of the analysis of
Layers 1–4.

## Layer 0: the groups in coordinates

### 0.1 The triangular group

Sources: Vilenkin–Klimyk Vol. 1 §5.1.1 (1)–(13), pp. 207–208; Klimyk–Vilenkin Chapter 4, §1.4, p.
206; Dieudonné §17, p. 58.

`TriangularGroup` is the group of the Conventions with the one-parameter subgroups
`g_+(t) = (t, 0, 0, 0)` (`translationElement`), `g_−(t) = (0, 0, t, 0)` (`modulationElement`), `z(t) = (0, t, 0, 0)`
(`centralElement`), `ε(t) = (0, 0, 0, t)` (`dilation`), and
`g_1(t) = [[1, t, t²/2], [0, 1, t], [0, 0, 1]] = (t, t²/2, t, 0)` (`equalTranslationModulation`),
`g_2(t) = [[1, −t, −t²/2], [0, 1, t], [0, 0, 1]] = (−t, −t²/2, t, 0)` (`oppositeTranslationModulation`). Prove:
- **Matrix realization** (`TriangularGroup.toMatrix_mul`): `toMatrix` is a multiplicative and
  injective map into `3 × 3` real matrices;
- **Centre** (`TriangularGroup.mem_center_iff`): the centre is `{z(t)}` (Vilenkin–Klimyk §5.1.1, p.
  207);
- **Factorizations** (`TriangularGroup.factorizations`): `g(0, b, d, τ) = ε(τ) g_−(d e^{−τ}) z(b)`
  (§5.1.1 (8), p. 208); `g_1(t) = g_−(t) g_+(t) z(t²/2)` (§5.2.4 (2), p. 219, which the source uses
  in (3)); and for `x > 0`, `x + t > 0`, `g_+(t) g_1(x) = ε(τ) g_1(r) ε(−τ) z(tx/2)` with
  `r = (x(x + t))^{1/2}`, `e^{2τ} = x/(x + t)` (§5.2.1 (1)–(3), pp. 213–214);
- **Heisenberg subgroup** (`heisenbergToTriangular_injective`): `(x, y, z) ↦ (x, z, y, 0)` is an
  injective homomorphism from Tau Ceti's Heisenberg group onto `{τ = 0}`.

The Lie algebra relations `[a_+, a_−] = c`, `[a_±, e] = a_±`, `c` central (§5.1.1 (5), p. 207)
appear here only through the infinitesimal operators of 2.3. The left Haar measure is consumed from
SpecialFunctionsGroupModels §0.2.

**Checks.**
- The group law agrees with the matrix product at `g = (0.7, −1.2, 0.4, 0.3)`,
  `h = (−0.5, 0.9, 1.1, −0.8)` to `10⁻³⁰`.
- Negative control: with the factors in the order `hg` the entries differ by up to `0.97`.
- `g⁻¹ = (−a e^{−τ}, a d e^{−τ} − b, −d e^{−τ}, −τ)`: `g g⁻¹ = 1` at the same `g`.
- The three factorizations hold at `t = 0.8`, `x = 1.3`, and at `(b, d, τ) = (−0.4, 0.6, 0.9)`,
  exactly in floating point.

*Needs:* nothing beyond Mathlib and Tau Ceti.

### 0.2 The oscillator group

Sources: Miller §4-11 (4.95)–(4.97), p. 113; Klimyk–Vilenkin Chapter 6, §1.4, p. 239;
SpecialFunctionsGroupModels §0.2.

`Oscillator` is the group of the Conventions and `Oscillator.toMatrix g` is
SpecialFunctionsGroupModels §0.2's `oscillatorMatrix w α δ`. Prove:
- **Matrix realization** (`Oscillator.toMatrix_mul`): `toMatrix` is multiplicative;
- **Kernel of the matrix realization** (`Oscillator.toMatrix_eq_one_iff`): `toMatrix g = 1` exactly
  when `w = 0`, `δ = 0` and `α ∈ 2πℤ`;
- **Heisenberg subgroup** (`heisenbergToOscillator_injective`):
  `(x, y, z) ↦ (x + iy, 0, −(z − xy/2)/2)` is an injective homomorphism.

Miller's `S₄` is the same group in other coordinates; the change of coordinates is a target of the
same standing, stated in prose: match Miller's matrix (4.95) with `oscillatorMatrix` and transport
the law (4.96).

**Checks.**
- `toMatrix` is multiplicative at `(0.4 − 0.9i, 0.7, 0.2)`, `(−1.1 + 0.3i, −1.9, 0.5)` to `10⁻²⁶`.
- The Heisenberg embedding is a homomorphism at `(0.3, −0.7, 1.1)`, `(−1.4, 0.6, 0.25)`.
- Negative control: `(0, 2π, 0)` is not the identity of `Oscillator` but has matrix `1`.

*Needs:* SpecialFunctionsGroupModels §0.2.

### Examples

- `g_1(t)` is the exponential of `t(a_+ + a_−)`, which is why the Whittaker kernels of 2.5 sit on
  the subgroup `g_1`.

### Dependencies

0.1 and 0.2 are independent.

## Layer 1: the `ax + b` group, the Mellin transform and the Gamma function

### 1.1 The representations `R_λ` and their Mellin realization

Sources: Vilenkin–Klimyk Vol. 1 §3.4.1 (1)–(5), pp. 128–129, and §3.4.2 (1), (11)–(12), pp. 129–131;
Klimyk–Vilenkin Chapter 4, §1.2, p. 204.

`affineAction λ g f x = e^{λbx} f(ax)` for `g = (a, b)` and complex `λ`. Prove:
- **Representation law** (`affineAction_mul`): `R_λ(gh) = R_λ(g) R_λ(h)` and `R_λ(1) = 1` on all
  functions;
- **Dictionary** (`affineAction_mul_I`): for real `ρ`, `affineAction (ρ i)` is the multiplier action
  of SpecialFunctionsGroupModels §2.4 with cocycle `e^{iρbx}`; its unitarity on `L²(dx/x)`,
  irreducibility for `ρ ≠ 0` and equivalence classes are consumed from there;
- **Dilations are diagonal** (`mellin_affineAction_dilation`): for `a > 0`,
  `mellin (R_λ(a, 0) f) w = a^{−w} mellin f w`;
- **Infinitesimal operators** (`mellin_infinitesimal`): `mellin (x f) w = mellin f (w + 1)` (the
  operator `B_λ = λx` of (12)), and for `f` smooth with compact support in `(0, ∞)`,
  `mellin (x f') w = −w mellin f w` (the operator `A_λ = x d/dx` of (11)).

The Mellin–Plancherel theorem is a target of the same standing, stated in prose:
`f ↦ (s ↦ (2π)^{−1/2} mellin f (is))` extends to a unitary map from `L²((0, ∞), dx/x)` onto `L²(ℝ)`
(substitute `x = e^u` and use Mathlib's Fourier–Plancherel theorem), and it carries `R_0(a, 0)` to
multiplication by `a^{−is}`, so `R_0` is a direct integral of the characters `a ↦ a^{−is}`.

**Checks.**
- `R_λ(a, b) R_λ(a', b') = R_λ(aa', ab' + b)` at `λ = 0.3 − 1.1i`, `x = 0.9`, `f(x) = x e^{−x}`,
  `(a, b) = (1.7, 0.6)`, `(a', b') = (0.8, −1.3)`: both sides are
  `−0.00538 34360 + 0.23297 06662 i`.
- Negative control: the order `(a', b')(a, b)` gives `0.19850 10475 + 0.20926 94395 i`.
- Negative control: `R_0` is reducible (Vilenkin–Klimyk §3.4.1, p. 129): it is the dilation
  representation, diagonal in the Mellin realization.
- `mellin (e^{−x}) w = Γ(w)`, and the shift rule gives `Γ(w + 1) = w Γ(w)`.

*Needs:* Mathlib `mellin_comp_mul_left`; SpecialFunctionsGroupModels §§0.2, 2.4.

### 1.2 The Gamma kernel

Sources: Vilenkin–Klimyk Vol. 1 §3.4.2 (10), p. 131, and §3.4.3 (1)–(3), pp. 131–132;
Klimyk–Vilenkin Chapter 4, §1.2 (1), p. 204.

`affineGammaKernel λ a b w z = Γ(w − z) a^{−w} (−λb/a)^{z−w} / (2πi)` with the principal power.
Prove:
- **Gamma kernel** (`mellin_affineAction_eq_integral`): for `a > 0`, `Re(−λb) > 0`, `f` smooth with
  compact support in `(0, ∞)` and real `c < Re w`,
  `mellin (R_λ(a, b) f) w = i ∫ affineGammaKernel λ a b w (c + is) · mellin f (c + is) ds`.

The source proves the formula for `λ < 0`, `b > 0` and extends it by analytic continuation in `−λb`
to the slit plane (§3.4.3, p. 132); the hypothesis `Re(−λb) > 0` is the half-plane where
`∫_0^∞ e^{λbx/a} x^{w−z−1} dx` converges absolutely. Proof route: insert Mellin inversion for `f`
(the contour may be moved to any `c` since `mellin f` is entire and rapidly decreasing on vertical
lines), exchange the integrals, and evaluate the inner integral with Mathlib's
`Complex.integral_cpow_mul_exp_neg_mul_Ioi` after continuation in the rate.

**Checks.**
- The Gamma functional equation follows from the kernel: comparing `B_λ R_λ(1, t)` computed from
  (12) and from `d/ds R_λ(1, s + t)` gives `Γ(w − z + 1) = (w − z) Γ(w − z)` (§3.4.4 (1)–(3), p.
  132).
- At `a = 1`, `λ = −1`, `b = 1`, `f(x) = e^{−x}`: the left side is
  `mellin (e^{−2x}) w = 2^{−w} Γ(w)`, and the right side is the special addition formula of 1.3.
- `a = 1.3`, `b = 0.7`, `λ = −0.8 + 0.5i`, `w = 1.9 + 0.3i`, `c = 0.6`, `f(x) = x e^{−x}`
  (`mellin f z = Γ(z + 1)`): both sides are
  `a Γ(w + 1)(a − λb)^{−w−1} = 0.28351 98619 + 0.19963 64628 i`.
- Negative control: with `(−λb/a)^{w−z}` in place of `(−λb/a)^{z−w}` the right side is
  `0.02032 28410 − 0.05380 24362 i` at the same data.

*Needs:* 1.1; Mathlib Mellin inversion (`mellinInv_mellin_eq`).

### 1.3 The addition formula of the Gamma function

Sources: Vilenkin–Klimyk Vol. 1 §3.4.5 (1)–(5), p. 135; Klimyk–Vilenkin Chapter 4, §3.1, p. 218.

Prove:
- **Addition formula for the Gamma function** (`Gamma_mul_div_add_one_cpow`): for `t > 0` and
  `0 < c < Re w`, `Γ(w) (t/(t + 1))^w = (1/2π) ∫ Γ(w − c − is) Γ(c + is) t^{c + is} ds`;
- **Dual form** (`mellin_div_add_one_cpow`): for `Re u < 0 < Re(w + u)`,
  `mellin (t ↦ (t/(t + 1))^w) u = Γ(w + u) Γ(−u) / Γ(w)`.

Route: the addition formula is the kernel identity of 1.2 for `g(1, b) g(1, 1) = g(1, b + 1)`
(§3.4.5 (1)–(2)); equivalently it is Mellin inversion of the dual form, which is the Beta integral
`∫_0^∞ t^{w+u−1} (1 + t)^{−w} dt = B(w + u, −u)` (Mathlib `Complex.betaIntegral` after
`t = s/(1 − s)`).

**Checks.**
- `w = 1.7 + 0.4i`, `t = 0.6`, `c = 0.8`: both sides of the addition formula are
  `0.15377 50787 − 0.04801 10634 i`.
- `t = 1` (the special case (4)): both sides are `2^{−w} Γ(w) = 0.25810 49091 − 0.04898 41714 i`.
- Dual form at `w = 1.7 + 0.4i`, `u = −0.4 + 0.3i`: `1.20298 04832 + 0.67258 52838 i`.
- Negative control: the hypothesis `c < Re w` is needed: at `c = 2.5` the integral is
  `−0.20204 35566 − 0.00704 58538 i`, not the left side.

*Needs:* 1.2; Mathlib `Complex.betaIntegral`, `mellinInv_mellin_eq`.

### Examples

- `t ↦ e^{−t}` and `t ↦ (1 + t)^{−w}` are the basic functions whose Mellin transforms are `Γ` and a
  Beta quotient; 1.2 and 1.3 are the group form of these two facts.

### Dependencies

1.1 → 1.2 → 1.3.

## Layer 2: the triangular group and the Whittaker functions

### 2.1 The representations `T_χ`

Sources: Vilenkin–Klimyk Vol. 1 §5.1.2 (1), pp. 208–209, and §5.1.3 (3), p. 210; Klimyk–Vilenkin
Chapter 4, §1.4, p. 205; Dieudonné §17, p. 58.

For `χ = (σ, ω) ∈ ℂ²`, `triangularCocycle σ ω g x = e^{ωτ + σ(dx + b)}` and
`(T_χ(g) f)(x) = e^{ωτ + σ(dx + b)} f(e^τ x + a)` (`triangularAction`). For real `γ`, `ρ`,
`triangularRep γ ρ` is the representation on `L²(ℝ)` at `σ = iγ`, `ω = 1/2 + iρ`. Prove:
- **Cocycle** (`isMultiplierCocycle_triangularCocycle`): `triangularCocycle σ ω` is a multiplier
  cocycle for every `σ`, `ω`, so `T_χ` is a representation on functions;
- **Unitarity range** (`lintegral_triangularAction_iff`): `T_χ(g)` preserves `∫ |f|²` for every `g`
  and measurable `f` exactly when `Re σ = 0` and `Re ω = 1/2` (§5.1.2, p. 209);
- **Unitary representations** (`triangularRep_spec`): `triangularRep γ ρ` realizes the formula and
  is unitary; for `γ ≠ 0` it is irreducible, and for `γ, γ' ≠ 0`,
  `triangularRep γ ρ ≅ triangularRep γ' ρ'` exactly when `γ = γ'` and `ρ = ρ'`;
- **Restriction to the Heisenberg group** (`triangularAction_heisenberg`): at `σ = i`, the action of
  `(x, z, y, 0)` is the Schrödinger action of `(x, y, z)` for every `ω`.

Irreducibility and equivalence: the restriction to the Heisenberg subgroup is the Schrödinger
representation with central character `e^{iγz}` (rescale `u ↦ γu` for `γ ≠ 1`), which is irreducible
(consumed from NoncompactQuantumSymmetry M2); an intertwiner of two `T_χ` with the same `γ`
therefore commutes with that irreducible restriction and is a scalar, and then
`ε(τ) ↦ e^{ωτ} f(e^τ ·)` forces `ω = ω'`; the central character forces `γ = γ'`. The source proves
operator irreducibility for `σ ≠ 0` (§5.1.2, p. 208) by the argument of §3.4.1, p. 128; the
equivalence statement is derived here.

**Checks.**
- The representation law at `σ = 1.3i`, `ω = 0.5 + 0.7i`, `x = 0.37`, `f(x) = e^{−x²}(1 + x + x³)`,
  with `g`, `h` of 0.1's Checks: the defect is `5 · 10⁻³²`; with `hg` in place of `gh` it is
  `1.217`.
- Unitarity at the same data: `∫ |T_χ(g) f|² − ∫ |f|² = 0`.
- Negative control: at `Re ω = 0.3` the norm ratio is `e^{(2 · 0.3 − 1)τ} = e^{−0.12} = 0.88692`,
  not `1`.
- Negative control: the coordinate order `(x, y, z, 0)` in place of `(x, z, y, 0)` gives the phase
  `e^{i(y + zu)}` in place of `e^{i(z + yu)}`.

*Needs:* 0.1; SpecialFunctionsGroupModels §§1.2–1.3, 2.5; NoncompactQuantumSymmetry M2.

### 2.2 Infinitesimal operators

Sources: Vilenkin–Klimyk Vol. 1 §5.1.2 (2)–(3), p. 209.

Prove:
- **Infinitesimal operators** (`hasDerivAt_triangularAction`): for `f` continuously differentiable,
  the derivatives at `t = 0` of `T_χ(g_+(t)) f (x)`, `T_χ(g_−(t)) f (x)`, `T_χ(z(t)) f (x)` and
  `T_χ(ε(t)) f (x)` are `f'(x)`, `σ x f(x)`, `σ f(x)` and `ω f(x) + x f'(x)`.

**Checks.**
- `[A_+, A_−] = σ = Z`, matching `[a_+, a_−] = c` (§5.1.1 (5), p. 207).
- `[A_+, E] = A_+` and `[A_−, E] = −A_−`, matching `[a_±, e] = ±a_±` for the matrices `a_+ = E₀₁`,
  `a_− = E₁₂`, `e = E₁₁`.
- Negative control: the action `f(e^{−τ} x + a)` in place of `f(e^τ x + a)` gives `E = ω − x d/dx`
  and `[A_+, E] = −A_+`, contradicting the matrices.
- At `x = 0` the operator `E` reduces to multiplication by `ω`.

*Needs:* 2.1.

### 2.3 The signed Mellin realization and its kernel

Sources: Vilenkin–Klimyk Vol. 1 §5.1.3 (1)–(10), pp. 209–211; Klimyk–Vilenkin Chapter 4, §1.4
(11)–(13), pp. 205–206.

`signedMellin f ε λ = mellin (x ↦ f(εx)) λ` for `ε = ±1`. `triangularKernel σ ω ε η λ μ g` is
`e^{ωτ + σb}/(2πi)` times `∫ x^{λ−1} e^{σdεx} |e^τ εx + a|^{−μ} dx` over the `x > 0` with
`η(e^τ εx + a) > 0`. Prove:
- **Diagonal and central elements** (`signedMellin_dilation_centre`): `T_χ(ε(τ))` acts on `F_±(λ)`
  by multiplication with `e^{(ω−λ)τ}` and `T_χ(z(b))` by `e^{σb}` (§5.1.3 (6), p. 210, and p. 211);
- **Infinitesimal operators** (`signedMellin_infinitesimal`): for `f` smooth with compact support in
  `ℝ \ {0}`, `signedMellin f' ε λ = −ε(λ − 1) signedMellin f ε (λ − 1)`, and for every `f`,
  `signedMellin (x f) ε λ = ε signedMellin f ε (λ + 1)` (§5.1.3 (7)–(8), p. 211);
- **Kernel realization** (`signedMellin_triangularAction`): for `Re σ = 0`, `f` smooth with compact
  support in `ℝ \ {0}`, `a ≠ 0` and `0 < Re λ < c < 1`, `signedMellin (T_χ(g) f) ε λ` equals
  `Σ_η i ∫ triangularKernel σ ω ε η λ (c + is) g · signedMellin f η (c + is) ds`
  (§5.1.3 (4)–(5), p. 210).

The source exchanges the integrals formally and records the common convergence domain
`0 < Re λ < Re μ < 1` for `Re σ = 0` (p. 210); the hypotheses above are that domain on the line
`Re μ = c`, and `a ≠ 0` keeps `|e^τ εx + a|^{−μ}` away from `x = 0`; at `a = 0` the source
computes the diagonal and central elements directly (p. 210), as in the first bullet.

**Checks.**
- Negative control: at `g = 1` (`a = 0`) the kernel integral is `∫_0^∞ x^{λ−1−μ} dx`, which
  diverges for every `λ`, `μ`; the hypothesis `a ≠ 0` is needed.
- Negative control: the sign `−ε` in the derivative rule:
  `signedMellin f' (−1) λ = (λ − 1) signedMellin f (−1) (λ − 1)` (source (7)), not `−(λ − 1)`.
- `K_{+−}(g_+(t)) = 0` for `t > 0`: the set `x > 0`, `x + t < 0` is empty.

*Needs:* 2.1; Mathlib `mellinInv_mellin_eq`.

### 2.4 Power kernels

Sources: Vilenkin–Klimyk Vol. 1 §5.1.4 (1)–(6), pp. 211–212; Klimyk–Vilenkin Chapter 4, §1.4
(14)–(17), p. 206.

Prove, for `t > 0`:
- **Kernels of `g_+(t)`** (`triangularKernel_translationElement`): `K_{++} = Γ(μ − λ) Γ(λ) t^{λ−μ} / (2πi Γ(μ))`
  for `Re μ > Re λ > 0`; `K_{−+} = Γ(λ) Γ(1 − μ) t^{λ−μ} / (2πi Γ(λ − μ + 1))` for `Re λ > 0`,
  `Re μ < 1`; `K_{−−} = Γ(1 − μ) Γ(μ − λ) t^{λ−μ} / (2πi Γ(1 − λ))` for `Re λ < Re μ < 1`;
  `K_{+−} = 0`;
- **Kernel of `g_−(t)`** (`triangularKernel_modulationElement`): for `Re(σt) < 0` and `Re λ > Re μ`,
  `K_{++} = Γ(λ − μ) (−σt)^{μ−λ} / (2πi)` and `K_{+−} = K_{−+} = 0`.

These are Beta and Gamma integrals: `∫_t^∞ y^{−μ}(y − t)^{λ−1} dy = B(λ, μ − λ) t^{λ−μ}`.

**Checks.**
- `λ = 0.7 + 0.2i`, `μ = 1.6 + 0.1i`, `t = 0.9`:
  `K_{++}(g_+(t)) · 2πi = 1.57979 16581 − 0.29414 61055 i` by quadrature and by the formula.
- `λ = 0.7 + 0.2i`, `μ = 0.3 − 0.4i`: `K_{−+}(g_+(t)) · 2πi = 1.25464 00163 − 1.11027 39560 i` both
  ways.
- Negative control: `Re μ > Re λ` is needed for `K_{++}`: at `μ = 0.3 − 0.4i` the integral diverges
  at infinity.

*Needs:* 2.3; Mathlib `Complex.betaIntegral`.

### 2.5 Whittaker kernels

Sources: Vilenkin–Klimyk Vol. 1 §5.1.4 (7)–(14), pp. 212–213; Klimyk–Vilenkin Chapter 4, §1.4
(18)–(21), p. 207; Dieudonné §17, p. 58.

Let `σ = −1` and `t > 0`. Prove:
- **Whittaker kernels of `g_1(t)`** (`triangularKernel_equalTranslationModulation`):
  `K_{++}(λ, μ; g_1(t)) = Γ(λ) W_{(1−λ−μ)/2, (λ−μ)/2}(t²) / (2πi t)` for `Re λ > 0`;
  `K_{−+}(λ, μ; g_1(t)) = Γ(λ) Γ(1 − μ) M_{(1−λ−μ)/2, (λ−μ)/2}(t²) / (2πi t Γ(λ − μ + 1))` for
  `Re λ > 0`, `Re μ < 1`; `K_{+−}(g_1(t)) = 0`;
- **Whittaker kernels of `g_2(t)`** (`triangularKernel_oppositeTranslationModulation`):
  `K_{++}(λ, μ; g_2(t)) = Γ(1 − μ) W_{(λ+μ−1)/2, (λ−μ)/2}(t²) / (2πi t)` for `Re μ < 1`;
  `K_{+−}(λ, μ; g_2(t)) = Γ(λ) Γ(1 − μ) M_{(λ+μ−1)/2, (λ−μ)/2}(t²) / (2πi t Γ(λ − μ + 1))` for
  `Re λ > 0`, `Re μ < 1`; `K_{−+}(g_2(t)) = 0`;
- **Reflection** (`triangularKernel_reflect`): replacing `(a, d)` by `(−a, −d)` exchanges the sign
  indices, `K_{εη}(g') = K_{−ε,−η}(g)`; in particular `t ↦ −t` in `g_1`, `g_2` exchanges them
  (§5.1.4 (14), p. 213).

Route: substitute `y − t = tx` and use the integral representations of `W` and `M` (DLMF 13.16.5 and
13.16.1, consumed from SpecialFunctionsConfluent), as the source does with its own integral
representations (§5.1.4, pp. 212–213).

**Checks.**
- `λ = 0.7 + 0.2i`, `μ = 0.3 − 0.4i`, `t = 0.9`:
  `2πi K_{++}(g_1(t)) = 0.73565 43260 − 0.08105 87023 i` by quadrature and from `W`.
- Same data: `2πi K_{−+}(g_1(t)) = 1.20369 93199 − 1.19369 99522 i` from `M` with `Γ(λ − μ + 1)`;
  negative control: Klimyk–Vilenkin (19) prints `Γ(λ − μ − 1)`, which gives
  `−0.86546 35862 + 0.57177 60529 i`.
- Same data: `2πi K_{++}(g_2(t)) = 0.59458 16449 − 0.24094 69890 i` and
  `2πi K_{+−}(g_2(t)) = 1.36831 77364 − 1.11645 63421 i`.
- Negative control: exchanging the index `(1 − λ − μ)/2` of `K_{++}(g_1)` for `(λ + μ − 1)/2` gives
  `0.73087 38824 − 0.14159 45493 i`.
- `K_{−−}(g_1(−t)) = K_{++}(g_1(t))` and `K_{+−}(g_1(−t)) = K_{−+}(g_1(t))` by quadrature.

*Needs:* 2.3; SpecialFunctionsConfluent (Whittaker functions and their integral representations).

### 2.6 Composition of kernels and functional relations

Sources: Vilenkin–Klimyk Vol. 1 §5.2.1 (1)–(4), pp. 213–214, §5.2.3 (1), p. 217, and §5.2.4 (1)–(6),
pp. 219–220.

The following are targets of the same standing, stated in prose:
- **Kernel composition**: `K(λ, μ; g h) = Σ_ν i ∫ K(λ, ν; g) K(ν, μ; h)` along a line in a common
  convergence domain (§5.2.4 (1)), which follows from 2.3 applied twice;
- **Mellin–Barnes integrals of `W_{κ,μ}`**: the composition law for `g_1(t) = g_−(t) g_+(t) z(t²/2)`
  with the kernels of 2.4 and 2.5 gives a Mellin–Barnes integral of `W_{κ,μ}(z)` as a contour
  integral of Gamma products (§5.2.4 (3)–(4), p. 219), and the factorization through `g_+` gives the
  other forms (§5.2.4 (5)–(6), p. 220);
- **Differential relations**: differentiating `T_χ(g_+(t) g_1(x))` at `t = 0` through the
  factorization of 0.1 gives first-order relations between `K(g_1(x))`, its `x`-derivative and the
  infinitesimal operators (§5.2.1 (4)–(5), p. 214); with 2.5 they become the contiguous relations of
  `W_{κ,μ}` and `M_{κ,μ}`, and combining them gives Whittaker's equation
  `y'' + (−1/4 + κ/x + (1/4 − μ²)/x²) y = 0` (§5.2.3 (1), p. 217). The identification with
  SpecialFunctionsConfluent's recurrences and equation is the target; their proofs are consumed.

**Checks.**
- The derivatives of `r`, `τ`, `b` at `t = 0` in the factorization of 0.1 are `1/2`, `−1/(2x)` and
  `x/2`, as printed in §5.2.1 (3), p. 214.
- Negative control: the orientation `e^{2τ} = (x + t)/x` would give `dτ/dt = +1/(2x)` at `t = 0`.

*Needs:* 2.3–2.5; SpecialFunctionsConfluent.

### Examples

- At `λ = 1`, `μ = 0`: `K_{++}(g_1(t)) = W_{0, 1/2}(t²)/(2πit)` and `W_{0,1/2}(z) = e^{−z/2}`, so
  `2πi t K_{++} = e^{−t²/2}`, which is `e^{t²/2} ∫_t^∞ e^{−ty} dy · t`.

### Dependencies

2.1 → 2.2; 2.1 → 2.3 → 2.4, 2.5 → 2.6.

## Layer 3: the Heisenberg group, Hermite and Laguerre functions

### 3.1 Matrix elements of the Schrödinger representation

Sources: Vilenkin–Klimyk Vol. 2 §12.1.6 (2)–(9), pp. 415–417; Wawrzyńczyk §12.1 (12.1.10)–
(12.1.13), pp. 428–429; Miller §4-15 (4.122)–(4.123), pp. 122–123.

With `α = (−x + iy)/√2` and `A = |α|² = (x² + y²)/2`, `hermiteMatrixElement m n x y z` is
`e^{i(z − xy/2)} e^{−A/2} (n!/m!)^{1/2} α^{m−n} L_n^{(m−n)}(A)` for `n ≤ m` and
`e^{i(z − xy/2)} e^{−A/2} (m!/n!)^{1/2} (−conj α)^{n−m} L_m^{(n−m)}(A)` for `m < n`. Prove:
- **Hermite matrix elements** (`matrixElement_schrodinger_hermite`):
  `matrixElement schrodinger (hermiteHilbertBasis ℂ) m n g = hermiteMatrixElement m n g.x g.y g.z`;
- **Unitarity bound** (`norm_laguerre_le`): for `n ≤ m` and `A ≥ 0`,
  `(n!/m!)^{1/2} A^{(m−n)/2} e^{−A/2} |L_n^{(m−n)}(A)| ≤ 1` (Miller §4-15, p. 125).

Route: `U(x, y, z) = e^{i(z − xy/2)} exp(α a† − conj α a)` on the Schwartz space (the Weyl form of
`e^{iyu} e^{x d/du}`), and the displaced-number-state formula. The source forms are converted:
Vilenkin–Klimyk's `r^λ_{mp}(n(a, b, 0))` (9) is for `R^λ` of the Conventions, Wawrzyńczyk's
(12.1.13) and Miller's (4.123) are in the Fock model of 3.4.

**Checks.**
- `(x, y, z) = (0.7, −1.1, 0.4)`: the formula and the quadrature
  `∫ h_m(u) e^{i(z + yu)} h_n(u + x) du` agree at `(m, n) = (0, 0), (2, 0), (3, 1), (1, 3), (2, 2)`;
  at `(0, 0)` both are `e^{i(z − xy/2)} e^{−(x² + y²)/4}`.
- Negative control: without the phase `e^{−ixy/2}` the `(0, 0)` element is off by `e^{ixy/2}`,
  `|1 − e^{ixy/2}| = 0.38`.
- Negative control: the bound without the factor `A^{(m−n)/2}` fails at `m = 2`, `n = 1`, `A = 0`:
  `L_1^{(1)}(0) = 2 > √2`.

*Needs:* SpecialFunctionsGroupModels §§2.5, 3.1; Tau Ceti `hermiteHilbertBasis`; LaguerreJacobi
Layer 1.

### 3.2 Addition theorem, orthogonality and completeness

Sources: Vilenkin–Klimyk Vol. 2 §12.1.6 (11)–(13), p. 417, pp. 417–418, and §12.1.8 (1)–(5), pp.
420–421; Wawrzyńczyk §12.2 (12.2.2)–(12.2.4), p. 430; Miller §4-15 Theorem 4.3 and (4.127), pp.
124–125.

Prove:
- **Addition theorem** (`hasSum_hermiteMatrixElement_mul`): for Heisenberg elements `g`, `h`,
  `Σ_k E_{mk}(g) E_{kn}(h) = E_{mn}(gh)` with `E = hermiteMatrixElement`;
- **Orthogonality** (`integral_hermiteMatrixElement`):
  `∫∫ E_{mn}(x, y, 0) conj E_{m'n'}(x, y, 0) dx dy = 2π δ_{mm'} δ_{nn'}`;
- **Completeness** (`hermiteMatrixElement_hilbertBasis`): the functions
  `(2π)^{−1/2} E_{mn}(x, y, 0)` form a Hilbert basis of `L²(ℝ²)`.

Route: the addition theorem is SpecialFunctionsGroupModels §3.2 with 3.1. Orthogonality reduces in
polar coordinates to LaguerreJacobi's orthogonality of `L_n^{(k)}` against `x^k e^{−x}`; it is the
square integrability of `U` modulo the centre. Completeness: expand in a Fourier series in the angle
and use the completeness of `{x^{k/2} e^{−x/2} L_n^{(k)}}` (LaguerreJacobi Layer 2).

**Checks.**
- Addition at `g = (0.7, −1.1, 0.4)`, `h = (−0.4, 0.3, −0.6)`, `(m, n) = (2, 1)`, summing `k < 40`:
  both sides agree to `10⁻¹⁸`.
- `∫∫ |E_{00}|² = ∫∫ e^{−(x² + y²)/2} dx dy = 2π`.
- Negative control: `∫∫ E_{10} conj E_{01} = 0` although both have `|E|² = A e^{−A}`.

*Needs:* 3.1; SpecialFunctionsGroupModels §3.2; LaguerreJacobi Layer 2.

### 3.3 Laguerre identities and the Charlier polynomials

Sources: Vilenkin–Klimyk Vol. 2 §12.1.6, p. 416 (the generating function), §12.1.8 (4)–(5), p. 421;
Klimyk–Vilenkin Chapter 6, §1.4 (5)–(7), p. 239.

The Charlier polynomial is `charlier a n = Σ_{j ≤ n} C(n, j) (−1/a)^j x(x − 1)⋯(x − j + 1)`, the
`₂F₀(−n, −x; ; −1/a)` of DLMF 18.20.8. Prove:
- **Charlier matrix elements** (`hermiteMatrixElement_charlier`): for `x > 0` and `a = x²/2`,
  `E_{kn}(x, 0, 0) = (−1)^k (k! n!)^{−1/2} a^{(k+n)/2} e^{−a/2} c_k(n; a)`;
- **Charlier and Laguerre** (`charlier_eq_laguerre`): for `a ≠ 0` and natural `x`,
  `c_n(x; a) = (−1)^n n! a^{−n} L_n^{(x−n)}(a)`;
- **Duality** (`charlier_symm`): `c_n(x; a) = c_x(n; a)` for natural `n`, `x`;
- **Orthogonality and completeness** (`charlier_orthogonality`): for `a > 0`,
  `(a^k e^{−a}/k!) Σ_x (a^x/x!) c_k(x; a) c_p(x; a) = δ_{kp}` and the functions
  `(a^{k+x} e^{−a}/(k! x!))^{1/2} c_k(x; a)` form a Hilbert basis of `ℓ²(ℕ)`.

Route: the matrix elements are 3.1 at `y = z = 0`; orthogonality and completeness are the unitarity
relations of SpecialFunctionsGroupModels §3.2 for the unitary matrix `(E_{kn}(x, 0, 0))` together
with duality.

**Checks.**
- `x = 1.3`: both sides of the matrix-element identity agree at `(k, n) = (0, 0), (2, 3), (3, 1)`.
- `a = 1.5`: the orthogonality sums are `1`, `0`, `0` at `(k, p) = (2, 2), (2, 3), (0, 1)`.
- Duality and the Laguerre form at `a = 1.5`, `n = 3`, `x = 5`:
  `c_3(5; a) = c_5(3; a) = (−1)³ 3! a^{−3} L_3^{(2)}(a)`.
- Negative control: Klimyk–Vilenkin (5) prints the exponent `(m + k)/2`; with the representation
  label `m` in place of `n` the identity fails unless `m = n`.

*Needs:* 3.1–3.2.

### 3.4 The Fock model and the Bargmann transform

Sources: Vilenkin–Klimyk Vol. 2 §12.1.7 (1)–(15), pp. 418–420; Wawrzyńczyk §12.1 (12.1.6)–(12.1.8)
and Lemma 12.1.1, pp. 425–427; Miller §4-13 (4.111)–(4.114), pp. 117–118.

`fockSpace` is the closure in `L²(fockMeasure)` of the span of the `fockMonomial n`, and
`bargmannKernel ζ u = π^{−1/4} exp(−ζ²/2 + √2 ζu − u²/2)`. Prove:
- **Fock space** (`fockSpace_spec`): the `fockMonomial n` are orthonormal, and `F ∈ fockSpace`
  exactly when `F` agrees almost everywhere with an entire function;
- **Bargmann transform** (`bargmann_spec`): there is a linear isometry `B` from `L²(ℝ)` onto
  `fockSpace` with `B h_n = fockMonomial n`, given for integrable square-integrable `f` by
  `(B f)(ζ) = ∫ bargmannKernel ζ u f(u) du`, and
  `B (U(x, y, z) f) (ζ) = e^{i(z − xy/2)} e^{−|w|²/4 − conj w ζ/√2} (B f)(ζ + w/√2)` with
  `w = x + iy`.

The source kernels are for antianalytic functions in Vilenkin–Klimyk (11), p. 420, and for `R^λ`
(15); the kernel here is the standard Bargmann kernel for `U` and entire functions.

**Checks.**
- `B h_2 (ζ) = ζ²/√2` at `ζ = 0.4 − 0.3i` by quadrature.
- The intertwining identity at `(x, y, z) = (0.7, −1.1, 0.4)`, `ζ = 0.4 − 0.3i`,
  `f(u) = e^{−u²/2}(1 + u + u²)`.
- Negative control: `ζ ↦ conj ζ` is in `L²(fockMeasure)` but not in `fockSpace`: it is orthogonal to
  every `fockMonomial n`.

*Needs:* 3.1; Tau Ceti `hermiteHilbertBasis`.

### Examples

- The coherent states: `U(g) h_0 = Σ_m E_{m0}(g) h_m`, and `B(U(g) h_0)` is a multiple of the
  exponential `ζ ↦ e^{αζ}`.

### Dependencies

3.1 → 3.2 → 3.3; 3.1 → 3.4.

## Layer 4: the oscillator group on the Fock space

### 4.1 The representations and their matrix elements

Sources: Miller §4-14 (4.119)–(4.121) and Theorem 4.2, pp. 121–122, §4-15 (4.122)–(4.123) and Lemma
4.5, pp. 122–123; Klimyk–Vilenkin Chapter 6, §1.4, p. 239.

`Oscillator` acts on `ℂ` by `g⁻¹ • ζ = e^{iα}(ζ + w/√2)`, and for real `λ` `oscillatorFock λ` is the
multiplier representation on `L²(fockMeasure)` with
`oscillatorCocycle λ g ζ = e^{iλα − 2iδ} e^{−|w|²/4 − conj w ζ/√2}`. Prove:
- **Oscillator representations** (`oscillatorFock_spec`): `oscillatorFock λ` realizes the formula,
  is unitary, leaves `fockSpace` invariant and is irreducible on it, and its restriction to the
  Heisenberg subgroup of 0.2 is `B U B⁻¹`;
- **Oscillator matrix elements** (`inner_fockMonomial_oscillatorFock`):
  `⟪fockMonomial m, oscillatorFock λ g (fockMonomial n)⟫` equals
  `e^{iλα − 2iδ + inα} hermiteMatrixElement m n (Re w) (Im w) (Re w Im w / 2)`.

Route: `oscillatorFock λ (w, α, δ) = e^{iλα − 2iδ} D(−conj w/√2) R(α)` with the rotation
`R(α) F(ζ) = F(e^{iα} ζ)`, which multiplies `fockMonomial n` by `e^{inα}`; irreducibility as in
Miller's Lemma 4.5, from the rotation weights and the nonvanishing of the matrix elements.

**Checks.**
- Representation law at `λ = 2.3`, `g = (0.4 − 0.9i, 0.7, 0.2)`, `h = (−1.1 + 0.3i, −1.9, 0.5)`,
  `ζ = 0.3 + 0.6i`, `F(ζ) = 1 + ζ + ζ³/3`: defect `10⁻²⁵`.
- Negative control: with `+Im(e^{−iα₁} conj w₁ w₂)/4` in the law the defect is `0.363`.
- Matrix elements by Cauchy coefficient extraction agree with the formula at
  `(m, n) = (0, 0), (2, 1), (1, 3)`.

*Needs:* 0.2, 3.1, 3.4; SpecialFunctionsGroupModels §§1.2–1.3.

The orthogonality relations of Miller's Theorem 4.3 (p. 124) for `S₄` reduce to 3.2 after the
`α`-integration, which gives `δ_{λλ'}` for integer weights; they are a target of the same standing,
stated in prose.

### Dependencies

4.1 needs 0.2 and Layer 3.

## Layer 5: Miller's group `G(0, 1)` and the Laguerre addition theorem

### 5.1 The representations on entire functions

Sources: Miller §4-2 (4.17)–(4.28), pp. 85–88; Wawrzyńczyk §12.2 (12.2.1), p. 429; Vilenkin–Klimyk
Vol. 2 §12.1.6, p. 416.

`millerAction μ ω g f z = e^{μ(bz + a) − ωτ} f(e^τ z + e^τ c)` for `g = (a, b, c, τ)` (Miller
(4.19)), and `millerMatrixElement μ ω l k g` is `e^{μa + (k−ω)τ}` times the finite sum
`Σ_{s ≤ min(k, l)} C(k, s) c^{k−s} (μb)^{l−s} / (l − s)!` (Miller (4.24)). Prove:
- **Representation law** (`millerAction_mul`): `B(gh) = B(g) B(h)` on all functions (4.20);
- **Real points** (`millerAction_eq_triangularAction`): on real coordinates `millerToTriangular`
  turns Miller's law into the triangular law, and
  `millerAction μ ω g = triangularAction μ (−ω) (millerToTriangular g)` on functions on `ℝ`, so
  Miller's representation is `T_{(μ, −ω)}` continued to entire functions;
- **Matrix elements** (`hasSum_millerAction_monomial`): `B(g) z^k = Σ_l B_{lk}(g) z^l` for all
  `z ∈ ℂ` ((4.21)–(4.22));
- **Laguerre form** (`millerMatrixElement_eq_laguerre`): for `c ≠ 0`,
  `B_{lk}(g) = e^{μa + (k−ω)τ} c^{k−l} L_l^{(k−l)}(−μbc)` (4.26);
- **Addition theorem** (`hasSum_millerMatrixElement_mul`): `Σ_j B_{lj}(g) B_{jk}(h) = B_{lk}(gh)`
  ((4.23), and with the Laguerre form, (4.28));
- **Generating function** (`hasSum_laguerre_generating`):
  `e^{−xz}(1 + z)^m = Σ_n L_n^{(m−n)}(x) z^n` for all complex `x`, `z` ((4.27); Wawrzyńczyk
  (12.2.1)).

**Checks.**
- The representation law at `μ = 0.7 + 0.2i`, `ω = −0.3 + 0.5i`,
  `g = (0.2 + 0.1i, −0.6 + 0.3i, 0.9 − 0.2i, 0.3 + 0.4i)`,
  `h = (−0.5 + 0.2i, 0.4 + 0.1i, −0.3 + 0.6i, −0.2 + 0.1i)`, `f(z) = z² + 3z − 1`, `z = 0.3 + 0.6i`:
  defect `2 · 10⁻²⁵`.
- The finite sum and the Laguerre form agree at `(l, k) = (1, 3), (3, 1), (0, 0), (4, 2)`; the case
  `l > k` uses the continued `L_l^{(k−l)}`.
- Addition at `(l, k) = (2, 1)` with `j < 60`: `−0.59547 31557 − 0.06605 50294 i` both sides.
- Generating function at `x = 0.8`, `z = 0.3`, `m = 3`, with `n < 60`.
- Negative control: at `c = 0` and `l > k` the factor `c^{k−l}` is the junk value `0` of Lean's
  `zpow`, while `B_{10}((0, 1, 0, 0)) = μ`; hence the hypothesis `c ≠ 0`.

*Needs:* 0.1, 2.1; LaguerreJacobi Layer 1.

### Dependencies

5.1 needs 0.1 and 2.1 only for the real-points bullet.

## Boundaries

- The irreducible unitary representations of the `ax + b` and Heisenberg groups, their
  classification and the Stone–von Neumann theorem are consumed, not proved.
- Analytic properties of `W_{κ,μ}`, `M_{κ,μ}` beyond the kernel identities are those of
  SpecialFunctionsConfluent; Laguerre orthogonality and bases are LaguerreJacobi's.
- The representations of the triangular group are treated only through `T_χ` on the line; the
  one-dimensional representations and those trivial on the centre are not.

## Downstream consumers

- Roadmaps on `SL(2, ℝ)` and on the Euclidean motion groups that use the Mellin realization of this
  roadmap's Layer 2 and the Laguerre matrix elements of Layer 3, which the same project plans as
  sequels.

## Beyond this roadmap (a roadmap for a roadmap; do not implement)

The following material lies outside this roadmap. It is recorded only to fix the boundary.
Contributors should not attempt it under this roadmap.

- **Higher-dimensional Heisenberg groups** `N_n` and the tensor-product matrix elements
  (Vilenkin–Klimyk Vol. 2 §§12.1.1–12.1.5); the case `n = 1` is the one treated here.
- **Weisner's method and Miller's other models** of `𝒢(0, 1)` (Miller §§4-3–4-10), the
  representations `R(ω, m₀, μ)` with Laguerre functions (Miller §4-1), and the Lie-derivative
  recursions (Miller (4.41)–(4.44)).
- **The Hermite–Laguerre relations** of Vilenkin–Klimyk Vol. 2 §12.1.9 and the Laguerre product
  formulas obtained by integrating the addition theorem (Miller §4-15, p. 125).
- **Kirillov's orbit method** for nilpotent groups (Dieudonné §17, p. 58).

## Prior formalization

[lean-SFVK](https://github.com/bjbraams/lean-SFVK) (Apache-2.0) is the same author's project on
special functions and group representations. Its modules `SFVK/AffineHeisenberg/Basic/Groups.lean`
(the four groups of Layers 0 and 5 with the Heisenberg embeddings) and
`SFVK/AffineHeisenberg/Basic/Models.lean` (the pointwise models, multipliers, kernels, Fock space
and the `L²` representations chosen by uniqueness) contain the definitions of this roadmap,
fully proved. The theorem-layer modules `Groups`, `Affine`, `Triangular`, `Heisenberg`,
`Oscillator` and `Miller` under `SFVK/AffineHeisenberg/` state the targets of Layers 0–5 with the
same names; there the representation laws of 1.1 and 5.1, the dictionary to the `ax + b` model of
SpecialFunctionsGroupModels §2.4, the dilation rule of 1.1, the cocycle and the Heisenberg
restriction of 2.1 and the two Heisenberg embeddings of Layer 0 are proved, and the rest is
stated. The multiplier machinery it builds on is `SFVKMathlib/MeasureTheory/Group/Multiplier.lean`.
This roadmap specifies the mathematics intrinsically; lean-SFVK supplies prior proofs and
implementation references, and reused code carries attribution under the repository's porting
guidance.

## References

- J. Dieudonné, *Special Functions and Linear Representations of Lie Groups*, CBMS Regional
  Conference Series in Mathematics 42, AMS, 1980, §17.
- A. U. Klimyk and N. Ya. Vilenkin, *Representations of Lie Groups and Special Functions*, in A. A.
  Kirillov (ed.), *Representation Theory and Noncommutative Harmonic Analysis II*, Encyclopaedia of
  Mathematical Sciences 59, Springer, 1995, Part II, Chapters 4 and 6.
- W. Miller, Jr., *Lie Theory and Special Functions*, Mathematics in Science and Engineering 43,
  Academic Press, 1968, Chapter 4.
- N. Ja. Vilenkin and A. U. Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 1,
  Mathematics and Its Applications (Soviet Series) 72, Kluwer, 1991, §§3.4, 5.1–5.2.
- N. Ja. Vilenkin and A. U. Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2,
  Mathematics and Its Applications (Soviet Series) 74, Kluwer, 1993, §12.1.
- A. Wawrzyńczyk, *Group Representations and Special Functions*, Mathematics and Its Applications
  (East European Series), Reidel / PWN, 1984, Chapter 12.
