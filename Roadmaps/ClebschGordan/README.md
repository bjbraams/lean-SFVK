# Roadmap: Clebsch–Gordan and Racah theory for SU(2), Hahn and Racah polynomials

## Summary

The tensor product of the irreducible unitary representations of spins `j₁` and `j₂` of SU(2)
decomposes without multiplicity into the representations of spins
`j = |j₁ - j₂|, |j₁ - j₂| + 1, …, j₁ + j₂`. The entries of the unitary change of basis from the
product basis to the coupled basis are the Clebsch–Gordan coefficients
`(j₁ m₁ j₂ m₂ | j₁ j₂ j m)`, fixed by the Condon–Shortley phase. Their symmetric rescaling is
Wigner's 3-j symbol. Coupling three spins in two orders gives a second unitary matrix, whose
entries are the 6-j symbols of Racah and Wigner. The classical identities of these symbols
(orthogonality, symmetries, the Racah and Biedenharn–Elliott sum rules, the integral of three
matrix elements and the Gaunt and Legendre product formulas) all follow from the representation
theory. Read as functions of one magnetic or one intermediate spin, the coefficients are the Hahn
and the Racah polynomials, the top two discrete families of the Askey scheme, and their
orthogonality is the unitarity of the coupling matrices.

This roadmap builds the coupling theory on the unitary model and the matrix elements of the
roadmap SpecialFunctionsSU2MatrixElements and on Tau Ceti's tensor product of continuous
representations, and derives:
- the coupled basis, its uniqueness and the Clebsch–Gordan series from the decomposition of the
  tensor product;
- orthogonality from the unitarity of the change of basis;
- the recursions from the raising and lowering operators;
- the product and triple-integral formulas from the homomorphism property and Schur
  orthogonality;
- the 6-j symbol from the recoupling of three spins, and its sum rules from the associativity of
  the coupling;
- the orthogonality of the Hahn and the Racah polynomials, first at integral parameters from the
  coupling theory and then at all parameters by polynomial identity.

The development is organized by the structure of the subject, in proof-dependency order: the
coupling of two spins; products of matrix elements; the 3-j symbol; the Hahn polynomials; the
coupling of three spins and the 6-j symbol; the Racah polynomials.

The roadmap is a synthesis of several sources, none of which it follows section by section:
- Edmonds [E, Chapters 3, 4 and 6], whose convention it adopts, for the coefficients, the 3-j and
  6-j symbols, Racah's formulas, the symmetries, the sum rules and the product formulas;
- Vilenkin and Klimyk [VK, Chapter 8] and their survey [KV, §2], for the Clebsch–Gordan
  coefficients as matrix elements of the tensor product and their expression through Hahn and
  Racah polynomials;
- Wawrzyńczyk [W, §8.7], for the Clebsch–Gordan series of characters and of matrix elements;
- the DLMF [DLMF, Chapter 34 and §§18.19–18.26], for the closed forms, the hypergeometric forms
  and the normalizations of the Hahn and Racah polynomials.

## Scope and ownership

The roadmap is complete when Tau Ceti proves every statement of `Suggested.lean` and the prose
targets of the layers below.

Inputs:
- SpecialFunctionsSU2MatrixElements: the unitary model of spin `d/2` and its weights (§1.4), the
  matrix elements, their group law and unitarity (§§2.1–2.2), the matrix elements in Euler
  angles (§2.3), the Legendre polynomials as `jacobi 0 0 l` (§2.6), Schur orthogonality in
  coordinates (§3.3), the infinitesimal operators (§4.1), the characters (§5.1) and the spherical
  harmonics (§6.1).
- Tau Ceti: the tensor product of continuous representations, its unitarity and the inner product
  on simple tensors; the SU(2) models, their irreducibility and exhaustion; the Haar probability
  measure; the Lie-algebra Clebsch–Gordan rule for `sl₂`.
- Mathlib: `ascPochhammer`, finite sums, the inner product on the algebraic tensor product of
  finite-dimensional inner product spaces.
- SpecialFunctionsGeneralizedHypergeometric: the terminating `₃F₂` and `₄F₃` series (§1.1) and
  the Pfaff–Saalschütz and Whipple–Sheppard transformations (§§4.3, 4.5), for the hypergeometric
  forms of §§3.5, 4.1 and 5.5.

Owned here:
- admissible triples, the Clebsch–Gordan coefficients by Racah's closed formula, the coupled
  vectors in the tensor product of two unitary models, and their characterization;
- the decomposition of `Sym^{d₁} ⊗ Sym^{d₂}` as a unitary equivalence, the Clebsch–Gordan series
  of matrix elements and of characters;
- the 3-j symbol, the triangle coefficient, the 6-j symbol by Racah's formula, the recoupling
  coefficient, and Racah's `W`;
- the integral of three matrix elements, the linearization and triple-integral formulas for
  Legendre polynomials, Gaunt's integral and the product of two spherical harmonics;
- the Hahn polynomials `Q_n(x; α, β, N)` (DLMF 18.20.5) and the Racah polynomials
  `R_n(λ(y); α, β, γ, δ)` (DLMF 18.26.3), with their orthogonality, their expression through the
  coupling coefficients and the Racah-to-Hahn limit.

Not owned:
- the unitary model and the matrix elements (SpecialFunctionsSU2MatrixElements, Layers 1–2);
- the Jacobi and Legendre polynomials (LaguerreJacobi, §§3.2 and 6.1);
- the concrete polynomial realization of `V(m) ⊗ V(n)` for `sl₂` and `GL₂`, with the Gram matrix of
  its highest-weight vectors (LieHighestWeight, §0.1); this roadmap uses only the group-level
  statement and the orthonormal coupled basis;
- the quantum `q`-Clebsch–Gordan coefficients of `U_q(sl₂)` (QuantumGroups, §8.5);
- the terminating hypergeometric series and their summation and transformation formulas
  (SpecialFunctionsGeneralizedHypergeometric);
- the continuous families above the Racah polynomials (Wilson, continuous dual Hahn) and the
  remaining discrete families (Meixner, Charlier, dual Hahn as such), which are left to a roadmap
  on the Askey scheme.

Boundary in one sentence: every coefficient that arises from coupling irreducible representations
of SU(2), and the two polynomial families that these coefficients realize, are here; the
representations themselves and the hypergeometric machinery are the suppliers'.

## Conventions

The convention is that of Edmonds [E], which is the convention of SpecialFunctionsSU2MatrixElements
and of DLMF Chapter 34 [DLMF, §34.1].

- Spins and indices are natural numbers, doubled where needed: a spin `j = d/2` is given by
  `d : ℕ`, and a magnetic quantum number `m = i - d/2` by its index `i : ℕ`, valid for `i ≤ d`. The
  vector `e_i` of the unitary model of spin `d/2` has weight `m = i - d/2`, as in
  SpecialFunctionsSU2MatrixElements, §1.4. Edmonds's order `m = j, …, -j` is `i = d, …, 0`.
- The Clebsch–Gordan coefficient `clebschGordan d₁ d₂ d i₁ i₂ i` is Edmonds's
  `(j₁ m₁ j₂ m₂ | j₁ j₂ j m)` [E, (3.5.1), p. 37], with `j₁ = d₁/2`, `m₁ = i₁ - d₁/2`, and so on.
  It is defined by Racah's closed formula [E, (3.6.11), p. 45], is real, and is `0` outside the
  admissible range: unless `(j₁, j₂, j)` is an admissible triple, every index is in range and
  `m = m₁ + m₂`, which in indices is `2i + d₁ + d₂ = 2i₁ + 2i₂ + d`.
- An admissible triple (`IsTriad`) satisfies the three triangle inequalities and has
  `j₁ + j₂ + j` integral [E, (3.1.5), p. 35 and §3.5]; DLMF 34.2.1 writes it with the
  coefficients `Δ`.
- The phase convention is Condon–Shortley: `(j₁ j₁ j₂ (j - j₁) | j₁ j₂ j j) > 0`
  [E, (3.5.11), p. 40], together with the matrix of the raising and lowering operators of
  SpecialFunctionsSU2MatrixElements, §4.1, which has nonnegative entries. Racah's formula with
  this convention reproduces the coupled vectors of the unitary model with no further sign.
- The coupled vector of spin `j` and index `i` is
  `Σ_{i₁, i₂} (j₁ m₁ j₂ m₂ | j m) e_{i₁} ⊗ e_{i₂}` in the algebraic tensor product
  `EuclideanSpace ℂ (Fin (d₁+1)) ⊗[ℂ] EuclideanSpace ℂ (Fin (d₂+1))`, on which Tau Ceti's
  `ContRepresentation.tprod` acts.
- The 3-j symbol is
  `(j₁ j₂ j₃; m₁ m₂ m₃) = (-1)^{j₁ - j₂ - m₃} (2j₃ + 1)^{-1/2} (j₁ m₁ j₂ m₂ | j₁ j₂ j₃, -m₃)`
  [E, (3.7.3), p. 46], which is DLMF 34.1.1 solved for the 3-j symbol. In indices `-m₃` is
  `d₃ - i₃`, and `m₁ + m₂ + m₃ = 0` is `2(i₁ + i₂ + i₃) = d₁ + d₂ + d₃`. The exponent
  `j₁ - j₂ - m₃` is an integer on the support; the Lean form adds `2d₃` to keep it natural, which
  does not change the parity.
- The 6-j symbol `sixJ a b c d e f` is `{j₁ j₂ j₃; l₁ l₂ l₃}` with doubled spins
  `(a, b, c, d, e, f) = 2(j₁, j₂, j₃, l₁, l₂, l₃)`, by Racah's formula [E, (6.3.7), p. 99;
  DLMF 34.4.2], and is `0` unless the four triples `(j₁ j₂ j₃)`, `(j₁ l₂ l₃)`, `(l₁ j₂ l₃)`,
  `(l₁ l₂ j₃)` are admissible. The triangle coefficient is DLMF's `Δ` (34.2.5).
- Signs `(-1)^{j₁ + j₂ + j₃}` and the like are written with the natural number `(d₁ + d₂ + d₃)/2`
  where the sum of the doubled spins is even; wherever a statement could meet an odd sum, it either
  assumes evenness or the other side vanishes there.
- The Hahn polynomial is DLMF's `Q_n(x; α, β, N)` [DLMF 18.20.5], and the Racah polynomial is
  DLMF's `R_n(λ(y); α, β, γ, δ)` with `λ(y) = y(y + γ + δ + 1)` [DLMF 18.26.3], both as functions of
  the real variable `x` or `y`, written by the terminating sum with `ascPochhammer`. The Lean
  definitions are total: a vanishing denominator gives Lean's value `0` for that term, and every
  theorem that uses them assumes the denominators nonzero.
- Vilenkin and Klimyk write the Clebsch–Gordan coefficients as matrix elements of the tensor
  product in the basis `ψ_n = z₁^{l-n} z₂^{l+n}/√·` [VK, §8.1.2, pp. 500–501]; their coefficients
  agree with Edmonds's up to the reindexing `n = -m` of SpecialFunctionsSU2MatrixElements, §2.7,
  and the statements here are in Edmonds's form.

## Exact supplier contracts

### From Tau Ceti

- `ContRepresentation.tprod`, the tensor product of two continuous representations on the
  algebraic tensor product of finite-dimensional inner product spaces, with
  `ContRepresentation.matrixCoeff_tprod`: matrix coefficients of the tensor product are products
  of matrix coefficients. Tau Ceti's tensor product module also supplies continuity and the
  unitarity of the tensor product of unitary representations, and the inner product on simple
  tensors `⟪v ⊗ v', w ⊗ w'⟫ = ⟪v, w⟫ ⟪v', w'⟫`.
- `TauCeti.SU2.symPower` and its character; `TauCeti.SU2.symPowerModel` with irreducibility and
  exhaustion, through SpecialFunctionsSU2MatrixElements, §1.4.
- `TauCeti.haarProb` and Schur orthogonality, through SpecialFunctionsSU2MatrixElements, §3.3.
- The Lie-algebra Clebsch–Gordan rule for `sl₂` (Tau Ceti's Sl2 ClebschGordan module, after the
  pin of this repository's build of that module): `V(m) ⊗ V(n)` is the internal direct sum of
  copies of `V(m + n - 2k)`, `0 ≤ k ≤ min(m, n)`. §1.3 can use it, through the differential of
  `Sym^d`, as an alternative route to completeness.

### From Mathlib

- `ascPochhammer`, `Finset.sum`, `Nat.factorial`, `Real.sqrt`.
- `TensorProduct` and the inner product space structure on `V ⊗[ℂ] W`, as instantiated by Tau
  Ceti.
- `Filter.Tendsto` for §6.3.

### From SpecialFunctionsSU2MatrixElements

- §1.4: `unitaryModel`, the transport of `symPowerModel d` by `monomialScale`, and its basis `e_i`
  of weight `i - d/2`. `Suggested.lean` carries verbatim local copies of `monomialNorm`,
  `monomialScale`, `unitaryModel` and `matrixElement`, whose docstrings name the owner.
- §§2.1–2.3: the matrix element, `matrixElement d i k g = ⟪e_i, T(g) e_k⟫`, its group law,
  unitarity and the Euler-angle form `D^j_{m'm}(euler α β γ) = e^{im'α} d^j_{m'm}(β) e^{imγ}`.
- §2.6: Legendre polynomials as `jacobi 0 0 l`; `Suggested.lean` carries the LaguerreJacobi
  `jacobi` as a verbatim local copy.
- §3.3: Schur orthogonality in coordinates, `∫ D D̄ = δ/(2j + 1)`.
- §4.1: the raising and lowering matrices.
- §5.1: the characters `Σ_i D^j_{ii}` and their Chebyshev form.
- §6.1: the spherical harmonics `Y_l^m` as matrix elements, for §2.3.

### From SpecialFunctionsGeneralizedHypergeometric

- §1.1: the terminating generalized hypergeometric series; §4.3: Pfaff–Saalschütz; §4.5: the
  Whipple and Sheppard transformations of terminating `₄F₃` and `₃F₂` series.

## How to read the build

Each layer has numbered subsections. Each subsection lists its targets as bold headlines with
their Lean names, a source locator for a headline that restates a source result and a proof route
for a corollary, and Checks: at least three per definition, one fact per bullet, at least one a
negative control. Layer 1 is the foundation. Layers 2 and 3 depend on Layer 1; Layer 4 uses
§§1.2 and 1.4; Layer 5 uses Layers 1 and 3; Layer 6 uses Layer 5 and §4.1.

## Layer 1: the coupling of two spins

### 1.1 Admissible triples

Sources: [E, (3.1.5), p. 35; §3.5, pp. 37–38]; [DLMF 34.2.1]; [W, (8.7.2)–(8.7.3), p. 305].

- **Admissible triples** (`IsTriad`, `isTriad_comm`). `(j₁, j₂, j)` is admissible when
  `|j₁ - j₂| ≤ j ≤ j₁ + j₂` and `j₁ + j₂ + j ∈ ℤ`. The condition is symmetric in all three spins;
  the Lean statement records the symmetry in the first two, which the swap theorems use.
- **The dimension count** (`sum_isTriad_succ`). `Σ_j (2j + 1) = (2j₁ + 1)(2j₂ + 1)` over the
  admissible `j`. Route: the admissible `d` are `|d₁ - d₂|, |d₁ - d₂| + 2, …, d₁ + d₂`; sum the
  arithmetic progression. This is the dimension identity behind the Clebsch–Gordan series
  [W, (8.7.2), p. 305].

**Checks.**

- `IsTriad 1 1 0` and `IsTriad 1 1 2` hold: `½ ⊗ ½ = 0 ⊕ 1`.
- `IsTriad 1 1 1` fails: `j₁ + j₂ + j = 3/2` is not an integer.
- `IsTriad 2 4 8` fails: `4 > 1 + 2`.
- Negative control: dropping the parity condition admits `(½, ½, ½)`, and the dimension count at
  `d₁ = d₂ = 1` becomes `1 + 2 + 3 = 6 ≠ 4`.
- `sum_isTriad_succ 2 3`: `d ∈ {1, 3, 5}`, `2 + 4 + 6 = 12 = 3 · 4`.

### 1.2 The Clebsch–Gordan coefficients

Sources: [E, (3.6.11), p. 45; (3.5.1)–(3.5.4), pp. 37–38]; [VK, §8.2.2, p. 505];
[DLMF 34.1.1, 34.2.4].

- **The Clebsch–Gordan coefficient** (`clebschGordan`). Racah's formula [E, (3.6.11), p. 45]:
  with `L = j₁ + j₂ - j`, the coefficient `(j₁ m₁ j₂ m₂ | j m)` is
  `δ_{m, m₁ + m₂} √((2j+1) Δ² Π_r (j_r + m_r)!(j_r - m_r)!)` times the sum of
  `(-1)^z / (z! (L - z)! (j₁ - m₁ - z)! (j₂ + m₂ - z)! (j - j₂ + m₁ + z)! (j - j₁ - m₂ + z)!)`,
  over the `z` with all six arguments nonnegative, `Δ` the triangle coefficient of §5.1
  (DLMF 34.2.5) and `r` over the three spins.
- **Selection rules** (`clebschGordan_eq_zero_of_not_isTriad`, `clebschGordan_eq_zero_of_ne`).
  The coefficient vanishes for an inadmissible triple and unless `m = m₁ + m₂` [E, (3.5.4), p. 38].
  Route: the definition.
- **The 3-j form of Racah's formula.** `clebschGordan` agrees with DLMF 34.2.4 through the 3-j
  symbol of §3.1. Route: substitute `(3.7.3)` into `(3.6.11)`; the summation variables agree.

**Checks.**

- `clebschGordan 1 1 2 1 1 2 = 1`: `(½ ½ ½ ½ | 1 1) = 1`.
- `clebschGordan 1 1 0 1 0 0 = 1/√2` and `clebschGordan 1 1 0 0 1 0 = -1/√2`: the singlet
  `(e_↑ ⊗ e_↓ - e_↓ ⊗ e_↑)/√2`.
- `clebschGordan 1 1 2 1 0 1 = 1/√2`: the triplet `m = 0` vector is symmetric.
- `clebschGordan 2 2 2 2 1 2 = 1/√2` and `clebschGordan 2 2 2 1 1 1 = 0`:
  `(1 1 1 0 | 1 1) = 1/√2` and `(1 0 1 0 | 1 0) = 0`.
- Negative control: omitting the factor `2j + 1` under the square root gives
  `(½ ½ ½ ½ | 1 1) = 1/√3`, and the coupled vectors are no longer unit vectors.
- Negative control: `clebschGordan 1 1 2 1 1 1 = 0`, since `m₁ + m₂ = 1 ≠ 0 = m`; a definition
  without the projection condition returns a nonzero sum here.

### 1.3 The coupled basis

Sources: [E, (3.5.1)–(3.5.3), pp. 37–38; (3.4.1)–(3.4.2), pp. 36–37; (3.5.11), p. 40];
[VK, §8.1.2, pp. 500–501; §8.1.3, pp. 501–503]; [KV, §2.1, (11)–(13), pp. 241–242].

- **The coupled vector** (`coupledVector`). `w_{jm} = Σ (j₁ m₁ j₂ m₂ | j m) e_{m₁} ⊗ e_{m₂}`
  [E, (3.5.1), p. 37].
- **The intertwining property** (`tprod_coupledVector`). For admissible `(j₁, j₂, j)`,
  `(T^{j₁} ⊗ T^{j₂})(g) w_{jm} = Σ_{m'} D^j_{m'm}(g) w_{jm'}`. Route: both sides are polynomial in
  the entries of `g` by the entry formula of SpecialFunctionsSU2MatrixElements, §2.1; check on
  the torus `TauCeti.SU2.torusExp` and the middle Euler factor
  (SpecialFunctionsSU2MatrixElements, §1.1), or reduce to the Lie algebra through the recursions
  of §1.7, which say that the lowering operator acts on `w_{jm}` as on `e_m`.
- **Orthonormality** (`inner_coupledVector`) [E, (3.5.3), p. 38]. Route: the coupled vectors of
  different `j` span inequivalent subrepresentations, hence are orthogonal by Schur; for equal
  `j` orthonormality is §1.4.
- **Completeness** (`span_coupledVector`) [E, (3.5.2), p. 37]. Route: the dimension count of §1.1
  and orthonormality.
- **The decomposition of the tensor product.** `Sym^{d₁} ⊗ Sym^{d₂}` is unitarily equivalent to
  `⊕ Sym^d` over the admissible `d`, by the unitary map `e_{d,i} ↦ w_{d,i}`
  [VK, §8.1.3, pp. 501–503; KV, §2.1, (11), p. 241]. Route: the three previous targets. This
  restates, at the group level and with the unitary structure, the Lie-algebra rule of Tau Ceti.
- **The Condon–Shortley phase** (`clebschGordan_pos`). `(j₁ j₁ j₂ (j - j₁) | j j) > 0`
  [E, (3.5.11), p. 40]. Route: at `m₁ = j₁` only one `z` contributes to Racah's sum.
- **Uniqueness of the coupled basis** (`eq_coupledVector_of_tprod`). An orthonormal family that
  transforms as the standard basis of spin `j` and whose top vector has a positive component along
  `e_{j₁} ⊗ e_{j - j₁}` is the coupled basis: this is the content of the phase conventions
  [E, (3.4.1)–(3.4.2), pp. 36–37]. Route: by multiplicity one the map `e_m ↦ v_m` is a scalar
  multiple of `e_m ↦ w_{jm}`; the norm makes the scalar unimodular and the phase makes it `1`.

**Checks.**

- `coupledVector 1 1 0 0 = (e₁ ⊗ e₀ - e₀ ⊗ e₁)/√2` (in indices: `e₁` is spin up).
- `coupledVector d 0 d i = e_i ⊗ e₀`: coupling with spin zero is the identity.
- At `j₁ = j₂ = ½`, the swap `v ⊗ w ↦ w ⊗ v` fixes the triplet and negates the singlet, as
  `(-1)^{j₁ + j₂ - j}` of §1.5 predicts.
- Negative control: with Tau Ceti's non-unitary model `symPowerModel 2` in place of
  `unitaryModel 2`, the intertwining property fails at `d₁ = 2, d₂ = 0`: the two matrices are
  conjugate by `diag(√2, 1, √2)`, so their entries between `i = 1` and `i ∈ {0, 2}` differ by a
  factor `√2` or `1/√2`, and these entries have modulus `1/√2 ≠ 0` at `g = eulerMiddle (π/2)`.
- Negative control: the opposite phase convention `(j₁ (j - j₂) j₂ j₂ | j j) > 0` changes the sign
  of the singlet: `(½ ½ ½ -½ | 0 0) = +1/√2` in Edmonds's convention, `-1/√2` in the other.

### 1.4 Orthogonality

Sources: [E, (3.5.5)–(3.5.6), p. 38]; [VK, §8.2.6, p. 511]; [KV, §2.1, (14)–(15), p. 242].

- **Orthogonality in the coupled indices** (`sum_clebschGordan_mul_clebschGordan`)
  [E, (3.5.5), p. 38]. Route: the inner product of two coupled vectors in the product basis.
- **Orthogonality in the product indices** (`sum_clebschGordan_mul_clebschGordan_right`)
  [E, (3.5.6), p. 38]. Route: the change-of-basis matrix is square by §1.1 and real, so its
  orthogonal columns make orthogonal rows.

**Checks.**

- At `d₁ = d₂ = 1`, `i₁ = 1, i₂ = 0`: `(1/√2)² + (1/√2)² = 1` over `j = 0, 1`.
- At `d₁ = d₂ = 1`, the rows `(i₁, i₂) = (1, 0)` and `(0, 1)` give
  `(1/√2)(1/√2) + (1/√2)(-1/√2) = 0`.
- Negative control: the row sum needs every admissible `j`: at `d₁ = d₂ = 1`,
  `(i₁, i₂) = (1, 0)`, dropping `j = 0` leaves `1/2`.

### 1.5 Symmetries

Sources: [E, (3.5.14), p. 41; (3.5.15)–(3.5.17), p. 42]; [VK, §8.2.7, p. 513];
[KV, §2.1, (16), p. 242].

- **Exchange of the two spins** (`clebschGordan_swap`)
  `(j₁ m₁ j₂ m₂ | j m) = (-1)^{j₁ + j₂ - j} (j₂ m₂ j₁ m₁ | j m)` [E, (3.5.14), p. 41].
- **Reversal of the magnetic quantum numbers** (`clebschGordan_reflect`)
  `(j₁ m₁ j₂ m₂ | j m) = (-1)^{j₁ + j₂ - j} (j₁ -m₁ j₂ -m₂ | j -m)` [E, (3.5.17), p. 42].
- **Exchange of the second and the coupled spin** (`clebschGordan_rotate`)
  `(j₁ m₁ j₂ m₂ | j m) = (-1)^{j₁ - m₁} √((2j + 1)/(2j₂ + 1)) (j₁ m₁ j -m | j₂ -m₂)`
  [E, (3.5.15), p. 42]. With the swap this gives the remaining permutation [E, (3.5.16), p. 42].
- Route for all three: substitution in Racah's sum (`z ↦ L - z` and its relatives), or the
  invariance of the 3-j symbol of §3.1.

**Checks.**

- `clebschGordan_swap` at `(½, ½, 0)`: `1/√2 = (-1)^1 · (-1/√2)`.
- `clebschGordan_rotate` at `(1, 1, 0; 0, 0, 0)`: `-1/√3 = (-1)^1 √(1/3) · 1`.
- Negative control: without the sign, `clebschGordan_swap` fails at the singlet,
  `1/√2 ≠ -1/√2`.
- Negative control: the reversal sign is not `(-1)^{j₁ - m₁}`: at `(1, 1, 1; 1, 0 | 1)` the
  coefficient is `1/√2` and its reversal `-1/√2`, while `(-1)^{j₁ - m₁} = 1` there.

### 1.6 Special values

Sources: [E, (3.5.12)–(3.5.13), p. 40; p. 45].

- **Coupling with spin zero** (`clebschGordan_zero_right`) `(j m 0 0 | j m) = 1`
  [E, (3.5.12), p. 40].
- **Coupling to spin zero** (`clebschGordan_spin_zero`) `(j m j -m | 0 0) = (-1)^{j - m}/√(2j + 1)`
  [E, (3.5.13), p. 40].
- **The stretched coefficient** (`clebschGordan_stretched`): for `j = j₁ + j₂`,
  `(j₁ m₁ j₂ m₂ | j m)² = (2j₁)! (2j₂)! (j + m)! (j - m)! / ((2j)! Π_r (j_r + m_r)! (j_r - m_r)!)`,
  with positive sign [E, p. 45].
- **Spin one half** (`clebschGordan_spinHalf`):
  `(j₁ m₁ ½ ½ | j₁ + ½, m) = √((j₁ + m + ½)/(2j₁ + 1))`. Route: the stretched formula with
  `d₂ = 1`. The other three entries of the spin-one-half table follow from the reversal of §1.5 and
  the orthogonality of §1.4.

**Checks.**

- `clebschGordan_stretched 1 1 1 0 = 1/√2`.
- `clebschGordan_spinHalf` at `d = 2, i = 0`: `(1 -1 ½ ½ | 3/2 -½) = √(1/3)`.
- Negative control: `clebschGordan_spin_zero` without the sign fails at `d = 1, i = 0`:
  `clebschGordan 1 1 0 0 1 0 = -1/√2`.

### 1.7 Recursion relations

Sources: [E, (3.5.9)–(3.5.10), p. 39]; [VK, §8.3.1, p. 517].

- **The lowering recursion** (`clebschGordan_lowering`) [E, (3.5.9), p. 39], written with
  `m + 1` in place of `m` so that no index goes negative.
- **The raising recursion** (`clebschGordan_raising`) [E, (3.5.10), p. 39], shifted likewise.
- Route: apply `J_± = J_±^{(1)} + J_±^{(2)}` to `w_{jm}`, with the matrices of
  SpecialFunctionsSU2MatrixElements, §4.1, whose entries are `√((j ∓ m)(j ± m + 1))`.
- **Uniqueness by recursion.** The lowering recursion and the value at `m = j` determine all
  coefficients, which gives a second route to `tprod_coupledVector`.

**Checks.**

- `clebschGordan_lowering 1 1 2 0 0 0`: `√2 · (½ -½ ½ -½ | 1 -1) = √2 = 1 · (1/√2) + 1 · (1/√2)`.
- At the top index `i = d` both sides of the lowering recursion vanish, since `d - i = 0` and
  `clebschGordan` is `0` at index `d + 1`.
- Negative control: with the left factor `√((j + m + 1)(j - m))` replaced by `j - m`, the same
  instance (`j = 1`, `m = -1`) gives `2 ≠ √2`.

## Layer 2: products of matrix elements

### 2.1 The Clebsch–Gordan series

Sources: [E, (4.3.1), p. 60; (4.3.2)–(4.3.3), p. 61]; [W, (8.7.2), p. 305; (8.7.7)–(8.7.8),
p. 306]; [VK, §8.4.1, p. 529]; [KV, §2.1, (12), p. 242].

- **The product of two matrix elements** (`matrixElement_mul_matrixElement`)
  `D^{j₁}_{m₁'m₁} D^{j₂}_{m₂'m₂} = Σ (j₁ m₁' j₂ m₂' | j m') D^j_{m'm} (j₁ m₁ j₂ m₂ | j m)`,
  summed over `j, m', m` [E, (4.3.1), p. 60; W, (8.7.7), p. 306]. Route: take the matrix coefficient
  of `tprod` between simple tensors with `ContRepresentation.matrixCoeff_tprod`, and expand the
  simple tensors in the coupled basis by §1.4.
- **The inverse series.** `D^j_{m'm} = Σ (j₁ m₁' j₂ m₂' | j m') (j₁ m₁ j₂ m₂ | j m) D^{j₁}D^{j₂}`
  [E, (4.3.2), p. 61; W, (8.7.8), p. 306]. Route: orthogonality.
- **The Clebsch–Gordan series of characters** (`character_mul_character`) `χ_{j₁} χ_{j₂} = Σ_j χ_j`
  [W, (8.7.2), p. 305]. Route: the trace of the product formula, or the Chebyshev form of the
  characters (SpecialFunctionsSU2MatrixElements, §5.1).

**Checks.**

- At `j₁ = j₂ = ½` and all indices at the top, `matrixElement 1 1 1 g ^ 2` and
  `matrixElement 2 2 2 g` are both `g₀₀²`: the stretched case.
- Characters at `g = -1`: `(-2)(-2) = 4 = 1 + 3` for `j₁ = j₂ = ½`.
- Negative control: summing all `d ≤ d₁ + d₂` in the character identity, admissible or not, gives
  `χ₀ + χ_{1/2} + χ₁` at `j₁ = j₂ = ½`, of dimension `6 ≠ 4`.

### 2.2 Integrals of three matrix elements

Sources: [E, (4.6.1)–(4.6.2), p. 62]; [VK, §8.4.2, p. 532].

- **The integral of three matrix elements** (`integral_matrixElement_mul_mul`)
  `∫ D^{j₁}_{m₁'m₁} D^{j₂}_{m₂'m₂} D^{j₃}_{m₃'m₃} dg = (j₁ j₂ j₃; m₁' m₂' m₃')(j₁ j₂ j₃; m₁ m₂ m₃)`
  for the Haar probability measure [E, (4.6.2), p. 62], which Edmonds writes as an integral in
  Euler angles over the rotations; SpecialFunctionsSU2MatrixElements, §1.3, converts. Route:
  §2.1 on the first two factors, then Schur orthogonality (SpecialFunctionsSU2MatrixElements,
  §3.3) against `D^{j₃}` written as the conjugate of
  `D^{j₃}` with reversed indices.

**Checks.**

- At `j₁ = j₂ = j₃ = 0` both sides are `1`.
- At `(j₁, j₂, j₃) = (1, 1, 0)` and all indices at weight `0`: `∫ (D^1_{00})² = 1/3 = (-1/√3)²`.
- Negative control: with the third factor conjugated, `∫ D D D̄` is a product of two
  Clebsch–Gordan coefficients over `2j₃ + 1`; at `(½, ½, 1)` with all indices at the top it is
  `1/3`, while the 3-j product above is `0` by the projection rule.

### 2.3 Legendre polynomials and spherical harmonics

Sources: [E, (4.6.3)–(4.6.6), p. 63]; [DLMF 34.3.19–34.3.22]; [VK, §8.4.3, p. 533;
§8.4.4, p. 534].

- **Linearization of products of Legendre polynomials** (`jacobi_mul_jacobi`)
  `P_{l₁} P_{l₂} = Σ_l (2l + 1)(l₁ l₂ l; 0 0 0)² P_l` [DLMF 34.3.19]. Route: §2.1 at
  `m = m' = 0` with `D^l_{00}(euler 0 β 0) = P_l(cos β)` (SpecialFunctionsSU2MatrixElements,
  §2.6), and the 3-j symbol of §3.1 in place of the coefficients.
- **The integral of three Legendre polynomials** (`integral_jacobi_mul_mul`)
  `∫_{-1}^{1} P_{l₁} P_{l₂} P_{l₃} = 2 (l₁ l₂ l₃; 0 0 0)²` [E, (4.6.4), p. 63; DLMF 34.3.21].
  Route: the linearization and Legendre orthogonality.
- **The product of two spherical harmonics** [DLMF 34.3.20; E, (4.6.5), p. 63], and
  **Gaunt's integral**: `∫_{S²} Y_{l₁}^{m₁} Y_{l₂}^{m₂} Y_{l₃}^{m₃}` is
  `√((2l₁+1)(2l₂+1)(2l₃+1)/(4π)) (l₁ l₂ l₃; 0 0 0)(l₁ l₂ l₃; m₁ m₂ m₃)`
  [E, (4.6.3), p. 63; DLMF 34.3.22]. Route: §2.2 with the spherical harmonics
  as matrix elements (SpecialFunctionsSU2MatrixElements, §6.1).

**Checks.**

- `P₁² = (1/3) P₀ + (2/3) P₂`, the case `l₁ = l₂ = 1`.
- `∫_{-1}^{1} P₁ P₁ P₂ = 4/15`, which is `2 · (1 1 2; 0 0 0)² = 2 · 2/15`.
- Negative control: without the factor `2l + 1`, the coefficients of `P₁²` sum to `1/3 + 2/15`,
  not to `P₁(1)² = 1`.

## Layer 3: the 3-j symbol

### 3.1 Definition and symmetries

Sources: [E, (3.7.3)–(3.7.6), pp. 46–47]; [DLMF 34.1.1, 34.2.4, 34.3.8–34.3.12].

- **The 3-j symbol** (`threeJ`) [E, (3.7.3), p. 46; DLMF 34.1.1].
- **Even permutations** (`threeJ_cycle`) [E, (3.7.4), p. 46; DLMF 34.3.8]. Route: §1.5.
- **Odd permutations** (`threeJ_swap`) [E, (3.7.5), p. 47; DLMF 34.3.9]: the factor
  `(-1)^{j₁ + j₂ + j₃}`.
- **Reversal** (`threeJ_reflect`) [E, (3.7.6), p. 47; DLMF 34.3.10].
- **Regge symmetries.** The 3-j symbol is invariant under the 72-element group generated by the
  permutations, the reversal and the Regge symmetries [DLMF 34.3.11–34.3.12]. Route: Racah's form
  DLMF 34.2.4 and the substitution of its summation variable.
- **Racah's form** [DLMF 34.2.4]: `threeJ` is DLMF's single-sum formula with the triangle
  coefficient. Route: substitute into Racah's formula of §1.2.

**Checks.**

- `threeJ 1 1 0 1 0 0 = 1/√2`, DLMF 34.3.1 at `j = ½, m = ½`.
- `threeJ 2 2 2 1 1 1 = 0`: `(1 1 1; 0 0 0)` vanishes since `1 + 1 + 1` is odd.
- `threeJ 2 2 0 1 1 0 = -1/√3`.
- Negative control: the sign `(-1)^{j₁ - j₂ + m₃}` in place of `(-1)^{j₁ - j₂ - m₃}` differs by
  `(-1)^{2m₃}`: `(½ 1 ½; ½ -1 ½) = -1/√3` becomes `+1/√3`, and the cyclic symmetry fails for the
  wrong sign at `(0 ½ ½; 0 ½ -½)`.

### 3.2 Orthogonality

Sources: [E, (3.7.7)–(3.7.8), p. 47]; [DLMF 34.3.16–34.3.17].

- **Orthogonality in `(j₃, m₃)`** (`sum_threeJ_mul_threeJ`) [E, (3.7.7), p. 47; DLMF 34.3.16].
- **Orthogonality in `(m₁, m₂)`** (`sum_threeJ_mul_threeJ_right`) [E, (3.7.8), p. 47;
  DLMF 34.3.17].
- Route for both: §1.4 and the definition.

**Checks.**

- At `d₁ = d₂ = 1`, `j₃ = 0`: `1 · ((1/√2)² + (-1/√2)²) = 1`.
- The right-hand side of `sum_threeJ_mul_threeJ` is `0` for an inadmissible `j₃`, where every term
  vanishes.
- Negative control: without the factor `2j₃ + 1`, the sum at `j₃ = 1` is `1/3`.

### 3.3 Special values

Sources: [E, (3.7.14)–(3.7.16), p. 49; (3.7.17), p. 50]; [DLMF 34.3.1, 34.3.5].

- **Spin zero** (`threeJ_spin_zero`) [DLMF 34.3.1].
- **Vanishing magnetic numbers, odd sum** (`threeJ_zero_zero_zero_of_odd`) [E, (3.7.14), p. 49;
  DLMF 34.3.5]. Route: `threeJ_reflect` with all `m = 0`.
- **Vanishing magnetic numbers, even sum** (`threeJ_zero_zero_zero_of_even`)
  [E, (3.7.17), p. 50; DLMF 34.3.5].

**Checks.**

- `(1 1 2; 0 0 0) = √(2/15)`; `threeJ_zero_zero_zero_of_even` gives `g = 2`,
  `√(2! 2! 0!/5!) · 2!/(1! 1! 0!) = √(4/120) · 2`.
- `(2 2 2; 0 0 0) = -√(2/35)`.
- Negative control: dropping the factor `(-1)^g` gives `+√(2/35)` for `(2 2 2; 0 0 0)`.

### 3.4 Hypergeometric form and recursions

Sources: [DLMF 34.2.6, 34.3.13–34.3.14]; [E, (3.7.12)–(3.7.13), p. 48].

- **The `₃F₂` form** [DLMF 34.2.6]. The 3-j symbol is a terminating `₃F₂` at `1` times a ratio of
  factorials. Route: Racah's form 34.2.4, with the terminating series of
  SpecialFunctionsGeneralizedHypergeometric, §1.1. The denominator parameters are negative
  integers whose absolute values are at least the terminating index, so the series is defined at
  every admissible argument.
- **Recursions** [DLMF 34.3.13–34.3.14; E, (3.7.12)–(3.7.13), p. 48]. Route: §1.7 for the
  recursions in `m`; Edmonds derives the others from `threeJ_mul_sixJ` of §5.2 at special
  arguments.
- **The explicit values for `j₃ = 1`** [DLMF 34.3.2–34.3.3]. Route: Racah's formula.

**Checks.**

- 34.2.6 reproduces `(1 1 2; 0 0 0) = √(2/15)`.
- `(1 1 1; 1 -1 0) = 1/√6`.
- Negative control: continuing the `₃F₂` past its terminating index meets the zero denominator
  `(-N)_{N+1}`, so the terminating sum cannot be replaced by the full series.

## Layer 4: Hahn polynomials

### 4.1 Definition and the coupling coefficients

Sources: [DLMF 18.20.5, Table 18.19.1]; [VK, §8.5.1, p. 546]; [KV, §2.2, (17), p. 243].

- **The Hahn polynomial** (`hahn`) `Q_n(x; α, β, N) = ₃F₂(-n, n + α + β + 1, -x; α + 1, -N; 1)`
  [DLMF 18.20.5].
- **Clebsch–Gordan coefficients are Hahn polynomials** (`clebschGordan_eq_hahn`). With
  `j₁ = N/2`, `j₂ = (N + a + b)/2`, `j = n + (a + b)/2`, `m₁ = N/2 - x`, `m = (a - b)/2`, the
  coefficient is `(-1)^x N!/a!` times an explicit square root times `Q_n(x; a, b, N)`. This is
  [VK, §8.5.1, p. 546] and [KV, §2.2, (17), p. 243], restated in Edmonds's convention and
  normalization. Route: Racah's formula of §1.2 is a terminating `₃F₂` in `x`; transform it by
  SpecialFunctionsGeneralizedHypergeometric, §4.5 (Sheppard), or match Hahn's three-term
  recurrence against the recursions of §1.7.
- **The hypergeometric form of `clebschGordan`.** Every Clebsch–Gordan coefficient is a ratio of
  factorials times a terminating `₃F₂` at `1`, by 34.2.6 and the definition of §3.1.

**Checks.**

- `Q_0 = 1`.
- `Q_1(x; α, β, N) = 1 - (α + β + 2) x / ((α + 1) N)`.
- `Q_n(0; α, β, N) = 1`.
- Negative control: `clebschGordan_eq_hahn` at `N = 1, n = 0, x = 1, a = b = 0` gives
  `(-1)^1 · 1 · √(1 · 1 · 1/(1 · 2)) = -1/√2 = clebschGordan 1 1 0 0 1 0`; without `(-1)^x` it
  gives `+1/√2`.

### 4.2 Orthogonality and symmetry

Sources: [DLMF Table 18.19.1]; [VK, §8.5.1, p. 546; §8.5.2, p. 549].

- **Hahn orthogonality** (`sum_hahn_mul_hahn`) for `α, β > -1`, with the weight and norm of
  DLMF Table 18.19.1, multiplied through by `2n + α + β + 1` so that no division by it occurs.
  Route: at nonnegative integers `α = a`, `β = b` it is §1.4 through §4.1. Both sides, multiplied
  by `(α + 1)_n²`, are polynomials in `(α, β)` (the left side after clearing the factor
  `(α + 1)_n` in each `Q_n`); two polynomials in two variables that agree on `ℕ²` agree everywhere.
- **Dual orthogonality.** The orthogonality in `x` for fixed `n` is the other orthogonality of
  §1.4; it is the orthogonality of the dual Hahn polynomials [DLMF 18.25] and is stated here only
  through the Clebsch–Gordan coefficients.
- **The reflection** (`hahn_reflect`)
  `(α + 1)_n Q_n(x; α, β, N) = (-1)^n (β + 1)_n Q_n(N - x; β, α, N)`
  [VK, §8.5.1, p. 546]. Route: §1.5 through §4.1 at integral parameters, then polynomial
  identity; or the Sheppard transformation.

**Checks.**

- At `N = 1`, `α = β = 0`: `Q₁(x) = 1 - 2x`, weights `1, 1`, `Σ Q₁² = 2`, and the right-hand side
  of `sum_hahn_mul_hahn` divided by `2n + α + β + 1 = 3` is
  `(-1) · 3! · 1 · 1/(1 · (-1) · 1 · 3) = 2`.
- Orthogonality at `N = 2`, `α = 0.3`, `β = 1.7`, `n = 1`, `m = 2`: the weighted sum is `0` to
  `10⁻¹²`.
- Negative control: the weight `(α + 1)_x (β + 1)_{N-x}` without `1/(x!(N - x)!)` breaks
  orthogonality at `N = 2`, `α = 0.3`, `β = 1.7`, `n = 0`, `m = 1`: the sum is `1.89`.

## Layer 5: recoupling and the 6-j symbol

### 5.1 Definitions

Sources: [E, (6.1.1)–(6.1.4), pp. 90–91; (6.3.7), p. 99]; [DLMF 34.2.5, 34.4.2];
[VK, §8.4.8, p. 539].

- **The triangle coefficient** (`triangleCoefficient`) [DLMF 34.2.5].
- **The 6-j symbol** (`sixJ`) by Racah's formula [E, (6.3.7), p. 99; DLMF 34.4.2].
- **The recoupling coefficient** (`recouplingCoefficient`)
  `((j₁ j₂) j₁₂, j₃; J M | j₁, (j₂ j₃) j₂₃; J M)` [E, (6.1.4), p. 91], the inner product of the two
  coupled vectors of three spins, expanded in the product basis with four Clebsch–Gordan
  coefficients.

**Checks.**

- `triangleCoefficient 0 0 0 = 1`.
- `triangleCoefficient 2 2 2 = √(1/24)`: `Δ(1 1 1)² = 1! 1! 1!/4!`.
- `sixJ 1 1 0 1 1 0 = -1/2`: `{½ ½ 0; ½ ½ 0} = (-1)^{1}/2`.
- `sixJ 2 2 2 2 2 2 = 1/6`.
- `sixJ 1 1 2 1 1 0 = 1/2`.
- Negative control: `sixJ 1 1 1 1 1 1 = 0`, since `(½ ½ ½)` is not admissible; Racah's sum alone,
  read with truncated halves, does not see the parity condition.
- `recouplingCoefficient` at `j₁ = j₂ = j₃ = ½`, `j₁₂ = 0`, `j₂₃ = 0`, `J = ½`, `M = ½` is
  `-1/2`, and `(-1)^{2} √(1 · 1) {½ ½ 0; ½ ½ 0} = -1/2`.

### 5.2 The recoupling theorem

Sources: [E, (6.1.5), p. 92; (6.2.1), p. 92; (6.2.8), p. 95]; [DLMF 34.4.1, 34.5.23].

- **The recoupling theorem** (`recouplingCoefficient_eq_sixJ`) [E, (6.1.5), p. 92]: the recoupling
  coefficient is `(-1)^{j₁ + j₂ + j₃ + J} √((2j₁₂ + 1)(2j₂₃ + 1))` times the 6-j symbol, for every
  `M`. Route: independence of `M` from the intertwining property (both coupled vectors transform
  as `e_M`); the value from Racah's computation at `M = J` [E, §6.3, pp. 98–99], or the
  four-3-j formula below.
- **Four 3-j symbols** (`sixJ_eq_sum_threeJ`) [DLMF 34.4.1]. Route: insert the definition of
  `recouplingCoefficient` in the recoupling theorem and sum over `M` with the factor `1/(2J + 1)`.
- **A 3-j symbol times a 6-j symbol** (`threeJ_mul_sixJ`) [E, (6.2.8), p. 95; DLMF 34.5.23].
  Route: the recoupling theorem in the product basis, with orthogonality of §3.2.

**Checks.**

- The recoupling coefficient for `j₁ = j₂ = j₃ = ½`, `J = ½`, with `(j₁₂, j₂₃)` running over
  `(0, 0), (0, 1), (1, 0), (1, 1)`, is the orthogonal
  matrix `[[-½, √3/2], [√3/2, ½]]`, independent of `M`.
- `sixJ_eq_sum_threeJ` at `(0, 0, 0, 0, 0, 0)`: `1 = 1`.
- Negative control: the sign `(-1)^{Σ (l_r + m'_r)}` of DLMF 34.4.1 cannot be dropped: at
  `{0 0 0; ½ ½ ½} = -1/√2` the unsigned sum is `0`.

### 5.3 Symmetries

Sources: [E, (6.2.4), p. 94; (6.2.5), p. 95]; [DLMF 34.5.8–34.5.10].

- **Column permutations** (`sixJ_swap_columns`, `sixJ_cycle_columns`) [E, (6.2.4), p. 94;
  DLMF 34.5.8]. Route: Racah's formula is symmetric under the corresponding permutation of the four
  triangles.
- **Exchange of upper and lower entries in two columns** (`sixJ_swap_rows`) [E, (6.2.5), p. 95;
  DLMF 34.5.8].
- **Regge symmetries** [DLMF 34.5.9–34.5.10]. Route: Racah's formula.

**Checks.**

- `sixJ 2 1 1 2 1 1 = sixJ 1 2 1 1 2 1 = 1/6`, an instance of `sixJ_swap_columns`.
- `sixJ 1 1 0 1 1 2 = sixJ 1 1 2 1 1 0 = 1/2`.
- Negative control: exchanging upper and lower entries in one column only is not a symmetry:
  `sixJ 0 0 0 1 1 1 = -1/√2` and `sixJ 1 0 0 0 1 1 = 0`.

### 5.4 Sum rules and special values

Sources: [E, (6.2.9)–(6.2.11), p. 96; (6.2.12)–(6.2.15), p. 97; (6.3.2)–(6.3.3), p. 98];
[DLMF 34.5.1, 34.5.14–34.5.16].

- **Orthogonality** (`sum_sixJ_mul_sixJ`) [E, (6.2.9), p. 96; DLMF 34.5.14]. Route: the
  recoupling matrix is orthogonal.
- **The Racah sum rule** (`sum_sixJ_racah`) [E, (6.2.11), p. 96; DLMF 34.5.15]. Route: compare
  two recouplings of three spins.
- **The Biedenharn–Elliott identity** (`sixJ_mul_sixJ_biedenharnElliott`) [E, (6.2.12), p. 97;
  DLMF 34.5.16]. Route: the pentagon of recouplings of four spins.
- **A vanishing entry** (`sixJ_zero`) [E, (6.3.2), p. 98; DLMF 34.5.1].
- **Racah's `W`** `W(abcd; ef) = (-1)^{a+b+c+d} {a b e; d c f}` [E, (6.2.13), p. 97]: owned as a
  prose target, with no Lean name, since the 6-j symbol carries the same information.

**Checks.**

- `sum_sixJ_mul_sixJ` at `(a, b, d, e) = (1, 1, 1, 1)`, `f = f' = 0`: the terms `c = 0, 2` are
  `1 · (-½)² + 3 · (½)² = 1`.
- `sixJ_zero` at `(a, b, c) = (1, 1, 0)`: `sixJ 1 1 0 0 0 1 = -1/√2`.
- Negative control: the Racah sum rule without the factor `2j + 1` fails at
  `(a, b, c, d, e, f) = (0, 1, 0, 1, 1, 0)`: the sum is `-1/(2√2)`, the right-hand side `-1/√2`.

## Layer 6: Racah polynomials

### 6.1 Definition and the 6-j symbol

Sources: [DLMF 18.26.3, 18.25.11–18.25.12]; [VK, §8.5.4, p. 552].

- **The Racah polynomial** (`racahPolynomial`)
  `R_n(λ(y); α, β, γ, δ) = ₄F₃(-n, n + α + β + 1, -y, y + γ + δ + 1; α + 1, β + δ + 1, γ + 1; 1)`
  [DLMF 18.26.3], as a function of `y`.
- **6-j symbols are Racah polynomials** (`sixJ_eq_racahPolynomial`). For admissible arguments,
  `{l₁ l₂ l + l₃ - x; l₃ l l₂ + l₃ - n} = C_n W_x R_n(λ(x); α, β, γ, δ)` with
  `α = -2l₃ - 1`, `β = -2l₂ - 1`, `γ = -l₁ - l₂ - l₃ - l - 2`, `δ = l₁ + l₂ - l₃ - l` and explicit
  factorial factors `C_n`, `W_x`. This is the statement of [VK, §8.5.4, p. 552], corrected and
  restated in Edmonds's normalization (the correction is recorded in the Lean docstring). Route:
  Racah's formula of §5.1 is a terminating `₄F₃`; bring it to balanced form by Whipple's
  transformation (SpecialFunctionsGeneralizedHypergeometric, §4.5), or compare the three-term
  recurrence of `R_n` with the Racah sum rule.
- **The `₄F₃` form of the 6-j symbol** [DLMF 34.4.3]. Route: the same transformation.

**Checks.**

- `R_0 = 1`.
- `R_n(λ(0); α, β, γ, δ) = 1`.
- `R_1(λ(y)) = 1 + (α + β + 2) y (y + γ + δ + 1)/((α + 1)(β + δ + 1)(γ + 1))`.
- Negative control: with `y + γ + δ` in place of `y + γ + δ + 1`, `sixJ_eq_racahPolynomial` fails
  at `(e₁, e₂, e₃, e, x, n) = (2, 2, 2, 2, 1, 1)`: the 6-j symbol is `1/6`, the modified `R_1` is
  `0`.

### 6.2 Orthogonality

Sources: [DLMF 18.25.9, 18.25.11–18.25.12]; [VK, §8.5.4, p. 552].

- **Racah orthogonality** (`sum_racahPolynomial_mul`) [DLMF 18.25.9], in the case
  `α + 1 = -N` with the weight 18.25.11 and the norm 18.25.12. The hypothesis is the
  nonvanishing of every Pochhammer symbol in a denominator, which is the condition under which the
  identity makes sense; positivity of the weights is not needed. Route: at the integral parameters
  of §6.1 it is `sum_sixJ_mul_sixJ`; both sides are rational in `(β, γ, δ)`, and agreement on a
  Zariski-dense set of integral points gives the general identity.

**Checks.**

- `N = 0`: the sum has the single term `y = 0`, and both sides are `1`.
- `N = 2`, `(β, γ, δ) = (0.37, 1.21, 0.53)`, `n = 1`, `m = 2`: the sum is `0` to `10⁻¹²`.
- Negative control: the weight without the factor `(γ + δ + 1 + 2y)/(γ + δ + 1 + y)` fails
  orthogonality at `N = 1`.

### 6.3 Limit to the Hahn polynomials

Sources: [DLMF 18.26.10].

- **Hahn polynomials as limits of Racah polynomials** (`tendsto_racahPolynomial_hahn`)
  `lim_{δ → ∞} R_n(λ(x); α, β, -N - 1, δ) = Q_n(x; α, β, N)` [DLMF 18.26.10]. Route: termwise;
  the `k`-th term has `(x + γ + δ + 1)_k/(β + δ + 1)_k → 1`.
- **The group-theoretic reading.** As `l → ∞`, the 6-j symbol in the form of §6.1 tends to a
  Clebsch–Gordan coefficient in the form of §4.1 (Ponzano–Regge in the classical limit is in
  Beyond); stated here only through the polynomial limit.

**Checks.**

- `n = 0`: both sides are `1` for every `δ`.
- `n = 1`, `N = 3`, `α = 0.3`, `β = 1.2`, `x = 1`: at `δ = 10⁹` the two sides agree to `2·10⁻⁸`.
- Negative control: the limit `γ → ∞` with `δ` fixed does not give `Q_n`.

## Examples

- `½ ⊗ ½ = 0 ⊕ 1`: the singlet `(e_↑ ⊗ e_↓ - e_↓ ⊗ e_↑)/√2` and the triplet
  `e_↑ ⊗ e_↑, (e_↑ ⊗ e_↓ + e_↓ ⊗ e_↑)/√2, e_↓ ⊗ e_↓`.
- `1 ⊗ 1 = 0 ⊕ 1 ⊕ 2`, with `(1 0 1 0 | 1 0) = 0` and `(1 0 1 0 | 0 0) = -1/√3`.
- `P₁² = (1/3) P₀ + (2/3) P₂` and `P₁ P₂ = (2/5) P₁ + (3/5) P₃`.
- `{1 1 1; 1 1 1} = 1/6` and `{½ ½ 1; ½ ½ 0} = 1/2`.
- The recoupling matrix of three spins `½` to total `½` is `[[-½, √3/2], [√3/2, ½]]`.

All numbers above and in the Checks were recomputed in double precision with Python, from the
definitions of `Suggested.lean`, and every Lean-named statement was evaluated on all small
arguments (spins up to `2`, indices in and out of range).

## Downstream consumers

- A roadmap on tensor operators and the Wigner–Eckart theorem consumes Layers 1, 3 and 5.
- A roadmap on the Askey scheme consumes the Hahn and Racah polynomials of Layers 4 and 6, with
  their orthogonality.
- The SU(1,1) and oscillator analogues (Beyond) reuse the definitions of Layer 1 in the discrete
  series.

## Beyond this roadmap (a roadmap for a roadmap; do not implement)

- The 9-j symbol, its symmetries and its sum rules [E, Chapter 6; DLMF 34.6].
- Tensor operators and the Wigner–Eckart theorem [E, Chapter 5].
- Clebsch–Gordan coefficients of SU(1,1) and of the oscillator group [VK, §§8.6–8.7].
- Wilson polynomials and the continuous Hahn families; addition theorems and generating functions
  of the Hahn and Racah polynomials [VK, §8.5].
- Asymptotics of the 3-j and 6-j symbols (Ponzano–Regge) [DLMF 34.8].
- The `q`-analogues and the quantum 6-j symbols.

## References

- [E] A. R. Edmonds, *Angular Momentum in Quantum Mechanics*, Princeton University Press, 1957
  (reprint 1996), Chapters 3, 4 and 6.
- [VK] N. Ja. Vilenkin, A. U. Klimyk, *Representation of Lie Groups and Special Functions*,
  Vol. 1, Kluwer, 1991, Chapter 8.
- [KV] A. U. Klimyk, N. Ja. Vilenkin, *Representations of Lie groups and special functions*, in
  A. A. Kirillov (ed.), *Representation Theory and Noncommutative Harmonic Analysis II*,
  Encyclopaedia of Mathematical Sciences 59, Springer, 1995, §2.
- [W] A. Wawrzyńczyk, *Group Representations and Special Functions*, Reidel, 1984, §8.7.
- [DLMF] *NIST Digital Library of Mathematical Functions*, https://dlmf.nist.gov/, Chapter 34 and
  §§18.19, 18.20, 18.25, 18.26.

## Prior formalization

[lean-SFVK](https://github.com/bjbraams/lean-SFVK) (Apache-2.0), by the author of this roadmap,
states the targets of this roadmap against Tau Ceti, the SU(2) code of lean-SFVK and the lean-DLMF
Wigner symbols; its definitions carry no `sorry`, and most theorems are open. Its modules are a
cited source, not the specification. Definitions: `SFVK/ClebschGordan/Basic/Coefficients.lean`
(§§1.1, 1.2, 3.1, 5.1), `SFVK/ClebschGordan/Basic/Coupling.lean` (§1.3),
`SFVK/ClebschGordan/Basic/SixJ.lean` (§5.1) and `SFVK/ClebschGordan/Basic/Polynomials.lean`
(§§4.1, 6.1). Theorems: `SFVK/ClebschGordan/Coefficients.lean` (§§1.1, 1.4–1.7),
`SFVK/ClebschGordan/Coupling.lean` (§§1.3, 2.1–2.2), `SFVK/ClebschGordan/ThreeJ.lean`
(Layer 3, §2.3), `SFVK/ClebschGordan/SixJ.lean` (Layer 5) and
`SFVK/ClebschGordan/Polynomials.lean` (Layers 4 and 6), with conversion theorems to the lean-DLMF
3-j and 6-j symbols and the Hahn and Racah polynomials.
