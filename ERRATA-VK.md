# Errata and source checks — Vilenkin–Klimyk, Volumes 1–3

This record concerns *Representation of Lie Groups and Special Functions* by
N. Ja. Vilenkin and A. U. Klimyk: Volume 1 (1991), Volume 2 (1993), and
Volume 3 (1992), Chapters 1–19. It is independent of [ERRATA-KV](ERRATA-KV.md),
which concerns the different EMS 59 reference.

Locators below use printed page numbers. For the PDFs in References, add 23
for Volume 1, 18 for Volume 2, and 19 for Volume 3 to obtain the one-based PDF
page number. In particular, Volume 2 printed page 1 is PDF page 19.

“Confirmed” means that the assertion conflicts with its definitions, a displayed
calculation, or the counterexample recorded here. A suspected entry remains a
source question, not an adopted theorem. A proposed correction is mathematical
guidance for later statement acquisition; it is not a change to a tagged Lean
declaration. No claim is made that the remaining printed formulas are error free.

The chapter synopses use standard mathematical statements with explicit
conventions and identify consequential departures from the printed source.
Some source formula families are represented by exact finite recurrences,
coefficient extraction, or specified integral kernels. Those constructions fix
their normalization without reproducing long coefficient lists.

## Chapter 1

See [SYNOPSIS-VK01](SYNOPSIS-VK01.md).

### E01.01 — Confirmed missing hypothesis

Source: Volume 1, §1.0.6, p. 22.

A positive Hermitian metric alone is called Kähler. The associated two-form must
also be closed. The synopsis distinguishes Hermitian and Kähler structures.

### E01.02 — Confirmed typographical error

Source: Volume 1, §1.0.11, pp. 32–34.

The tensor-operator formula prints \(Ax\otimes Bx\) for an input \(x\otimes y\).
The second factor must be \(By\); the two input spaces need not coincide.

### E01.03 — Confirmed overgeneralization

Source: Volume 1, §1.1.6, p. 47.

The claim that invariant symmetric forms on arbitrary linear Lie algebras are
\(\lambda\mathrm{tr}(XY)+\mu\mathrm{tr}X\,\mathrm{tr}Y\) is false.
On the two-dimensional diagonal algebra, all symmetric bilinear forms are invariant,
a three-dimensional family, whereas the two displayed trace forms span at most
two dimensions. The assertion needs a specified full classical algebra.

### E01.04 — Confirmed false definitions

Source: Volume 1, §1.1.8, p. 50.

Vanishing Killing form does not characterize nilpotence. Over \(\mathbb C\), take
\([H,X]=X,[H,Y]=iY,[X,Y]=0\). The Killing form is zero because
\(1+i^2=0\), but \(\mathrm{ad}H\) is not nilpotent.
The proposed solvability condition \(\mathfrak g^\perp=[\mathfrak g,\mathfrak g]\)
also fails for every nonzero abelian algebra: its two sides are \(\mathfrak g\)
and \(0\). Use lower central and derived series, respectively.
These source definitions are not silently substituted for standard meanings.

### E01.05 — Confirmed dimension conflict

Source: Volume 1, §1.2.5, p. 61.

The declared \(p\times q\) ball coordinate is combined with the action
\((dZ+c)(Zb+a)^{-1}\), whose block sizes do not conform under the displayed
\(p,q\) ordering. Either transpose/reindex the coordinate or use the standard
conforming action \((aZ+b)(cZ+d)^{-1}\).

### E01.06 — Confirmed missing hypothesis

Source: Volume 1, §1.2.6, p. 63.

The criterion \(\Delta_H=\Delta_G|_H\) is said to hold automatically when \(G\)
is unimodular. It then holds exactly when \(H\) is unimodular.
A nonunimodular parabolic subgroup of a semisimple group gives a counterexample.

### E01.07 — Confirmed missing modular factor

Source: Volume 1, §1.2.7, pp. 66–67.

For a nonunimodular group, conjugation and inversion alone do not define the
star operation on its Haar \(L^1\) convolution algebra; the modular factor is needed.
The unweighted expression is valid in the unimodular case.

### E01.08 — Confirmed false ideal assertion

Source: Volume 1, §1.2.7, p. 67.

Bi-\(K\)-invariant functions form a convolution subalgebra, not generally a
two-sided ideal of all \(L^1(G)\). In a finite group, the normalized indicator
of a nonnormal subgroup \(K\) is bi-\(K\)-invariant, but translating it by a
suitable group element produces a function that is not. The compact averaging
range is a corner/Hecke algebra, not the claimed ambient ideal.

## Chapter 4

See [SYNOPSIS-VK04](SYNOPSIS-VK04.md).

### E04.01 — Confirmed index error

Source: Volume 1, §4.3.2, p. 181, formula (6).

The second identity prints
\((d/dz)(z^\nu Z_\nu)=z^\nu Z_{\nu+1}\).
It must have \(Z_{\nu-1}\) on the right. At \(\nu=0\), for \(Z=J\),
the printed formula says \(J_0'=J_1\), whereas \(J_0'=-J_1\).
The first identity in (6) has the correct raising index.

### E04.02 — Confirmed sign error

Source: Volume 1, §4.3.3, p. 181, first series.

The half-order J-series begins at \(n=1\) with sign \((-1)^n\).
It must be \((-1)^{n-1}\) for the following displayed sine formula.
The first nonzero Taylor coefficient is positive.

### E04.03 — Confirmed sign error

Source: Volume 1, §4.3.3, p. 181, formula (4).

The last member is \(+i\sqrt{2/(\pi z)}e^{iz}\).
With \(H^{(1)}=J+iN\), it is
\(-i\sqrt{2/(\pi z)}e^{iz}\).
The Rodrigues formula (9) on p. 182 already has the correct minus sign.

### E04.04 — Confirmed normalization error

Source: Volume 1, §4.3.3, p. 182, formulas (6), (11), (14).

These formulas use \(\sqrt{2/(\pi z)}\) for the Macdonald function.
The definition and integral in §3.5.6, p. 152, give
\(K_{1/2}(z)=\sqrt{\pi/(2z)}e^{-z}\).
Thus the half-integral K formulas on p. 182 need the common factor \(\pi/2\).
This is an internal inconsistency, not a freely chosen alternate normalization.

## Chapter 5

See [SYNOPSIS-VK05](SYNOPSIS-VK05.md).

### E05.01 — Confirmed bracket sign error

Source: Volume 1, §5.1.1, p. 207, formula (5).

The relation \([a_-,e]=a_-\) has the wrong sign.
The displayed matrices give \([a_-,e]=-a_-\).
Equivalently, \(A_-=\sigma x\) and \(E=\omega+x\partial_x\) satisfy
\([A_-,E]=-A_-\).

### E05.02 — Confirmed parameter-domain error

Source: Volume 1, §5.3.5, p. 227, definition of G2.

The exponential dilation parameter is restricted to \(\tau>0\).
This excludes the identity and inverses, so does not define the asserted group.
Use \(\tau\in\mathbb R\); the positive coordinate is \(e^\tau\).
Later inverse formulas in §5.4.5 themselves use \(-\tau\).

### E05.03 — Confirmed missing absolute values

Source: Volume 1, §5.4.5, pp. 244–246, direct-integral measure.

For \((\lambda,\mu)=(pu^2,pu)\), the Jacobian determinant is \(-pu^2\).
Lebesgue measure is therefore \(|p|u^2\,dp\,du\).
The printed signed \(p\,dp\) cannot be a positive direct-integral measure
on the stated whole real p-axis. The analogous \((r,s)\) substitution
requires \(|r|s^2\,dr\,ds\).

### E05.04 — Confirmed Gaussian-factor error

Source: Volume 1, §5.3.5, p. 230, formula (22).

In the higher derivative of \(e^{z^2/4}D_\lambda(z)\), the right side
has \(e^{-z^2/4}\). It must have \(e^{z^2/4}\).
The immediately preceding first-derivative identity has the plus sign.
Taking \(\lambda=1,n=1\) gives the direct check
\((d/dz)(e^{z^2/4}D_1(z))=1\).

### E05.05 — Confirmed irreducibility overstatement

Source: Volume 1, §5.3.6, pp. 232–233, circle realization.

The action on all \(L^2\) circle functions is claimed irreducible.
Its analytic exponential multipliers and rotations preserve the proper
closed Hardy subspace. The one-sided triangular coefficient matrices
(3)–(5) display this invariant subspace directly.
A suitable analytic subspace or subquotient, rather than the whole
bilateral Fourier space, is needed for an irreducibility claim.

## Chapter 8

See [SYNOPSIS-VK08](SYNOPSIS-VK08.md).

### E08.01 — Confirmed termination-condition error

Source: Volume 1, §8.5.4, p. 553, condition following formula (5).

The condition places all three lower-parameter negatives in
\(\{0,\ldots,n\}\). This can force a lower-factor zero before the degree-n
numerator terminates. A Racah system on \(\{0,\ldots,N\}\) instead requires
at least one of \(\alpha+1,\beta+\delta+1,\gamma+1\) to be \(-N\),
with \(n\le N\), no earlier lower zero, and any additional nondegeneracy
needed for exact degree n.

### E08.02 — Confirmed sign error

Source: Volume 1, §8.6.5, p. 569, final Charlier addition formula.

The prefactor \(a^n(-\rho_2)^{k+n}\) must be
\(a^n(-1)^n\rho_2^{k+n}\), retaining the other factors.
With \(a=1,\rho_1=2,\rho_2=3,n=k=1,x=2,y=1\), the printed left side
is \(2/5\) and the right side is \(-2/5\), using
\(c_j(x;b)={}_2F_0(-j,-x;-1/b)\) and the book's normalized Krawtchouk
polynomials. The proposed change removes the extra factor \((-1)^k\).

## Chapter 10

See [SYNOPSIS-VK10](SYNOPSIS-VK10.md).

### E10.01 — Confirmed index-range error

Source: Volume 2, §10.6.1, p. 248, definition of the Meijer G-function.

The bound is printed \(0\le n\le q\). The n numerator a-parameters
are drawn from the p a-parameters, so it must be \(0\le n\le p\).
The separate bound \(0\le m\le q\) is correct.

### E10.02 — Confirmed coordinate-density error

Source: Volume 2, §10.7.5, p. 273, invariant measure.

The measure is printed
\((x,x)^{-(n+2)/2}\,dw\,d\tau\,dx\,dr\)
in the coordinates of the preceding matrix and multiplication law.
Translation \(x\mapsto x+x_0\) already disproves its invariance.
The left Haar density in those coordinates is
\(e^{-(n+2)\tau}\,dw\,d\tau\,dx\,dr\):
the two translation blocks have dilation weights 1 and 2.
A radial-coordinate formula would require an explicit change of variables.

## Chapter 11

See [SYNOPSIS-VK11](SYNOPSIS-VK11.md).

### E11.01 — Confirmed global group error

Source: Volume 2, §11.1.1, p. 278.

The scalar-center quotient \(U(n)/U(1)\) is identified with \(SU(n)\).
For \(n>1\) it is \(PU(n)\cong SU(n)/\mu_n\). For example
\(U(2)/U(1)\cong SO(3)\), whereas \(SU(2)\) is simply connected.
The later transitive action of SU(n) on projective space remains valid,
with its finite kernel.

### E11.02 — Confirmed multiplicity error

Source: Volume 2, §11.7.4, p. 399, fixed-vector multiplicity.

The trivial Sp(n−1)-type is said to occur once in each class-one Sp(n)-type.
In the defining complex \(2n\)-dimensional representation its fixed space is
\(\mathbb C^2\), from the last quaternionic coordinate. More generally the
type labeled \((l,l')\) has fixed-space dimension \(l-l'+1\).
It is the Sp(n−1)×Sp(1) decomposition that separates the additional Sp(1)-type.
Scalar spherical coefficients require fixing that additional weight or
averaging over Sp(1).

## Chapter 12

See [SYNOPSIS-VK12](SYNOPSIS-VK12.md).

### E12.01 — Confirmed automorphism-group overstatement

Source: Volume 2, §12.2.2, p. 428; §12.3.1, p. 438.

Fixing the central generator does not force an automorphism to preserve
the chosen horizontal complement. The maps
\(v+tZ\mapsto v+(t+\ell(v))Z\), with arbitrary linear \(\ell\), are
additional center-fixing automorphisms. The group is
\(V^*\rtimes Sp(V)\) in these coordinates.
Sp(V) is the subgroup preserving the complement. Allowing central
rescaling enlarges it further to conformal symplectic automorphisms.

### E12.02 — Confirmed normality and topology errors

Source: Volume 2, §12.5.1, p. 458, integer Heisenberg lattice.

The integer lattice D is called invariant, and D\H a quotient group
homeomorphic to a cube. Conjugating an integer horizontal translation
by a real horizontal translation generally produces a noninteger central
coordinate, so D is not normal.
D\H is a compact nilmanifold with a cube as a fundamental set with boundary
identifications. It is not homeomorphic to the ordinary closed cube.

### E12.03 — Confirmed missing sign restriction

Source: Volume 2, §12.4.1, p. 452, Fock scalar product.

The Gaussian parameter is allowed to range over all real numbers in
the stated holomorphic Fock norm. That norm is positive and finite on
polynomials for \(\lambda>0\), not for negative \(\lambda\).
Negative central character is realized by the conjugate model with
positive Gaussian weight \(|\lambda|\). At zero the displayed
normalizing factor degenerates.

## Chapter 13

See [SYNOPSIS-VK13](SYNOPSIS-VK13.md).

### E13.01 — Suspected missing distinction

Source: Volume 2, §13.1.3, p. 487, polynomial derivative on subset functions.

The derivative D is applied after polynomials are described as functions
on the fixed-cardinality subset space. Differentiation does not descend
to that function quotient: \(\sum_i x_i-m\) vanishes there, while its
D-derivative is N. The harmonic-kernel construction is valid in the
formal squarefree graded spaces with their restriction maps.
The synopsis uses this distinction; the intended formal-space reading
may resolve the wording without a change to the polynomial identities.

### E13.02 — Confirmed reversed digit inequality

Source: Volume 2, §13.3.2, p. 544, p-adic neighborhoods.

The neighborhoods \(U_n(a)\) fix digits \(b_j=a_j\) for \(j>n\).
The approximants and valuation topology require fixing the low-order digits,
\(j\le n\), with n tending to positive infinity.
For example \(p^k\to0\) in the valuation topology, whereas fixing all
high-order digits gives the opposite behavior.

### E13.03 — Missing local-field restriction

Source: Volume 2, §§13.3.2,13.3.4, pp. 548, 557.

The four square classes and three quadratic extensions require odd
residue characteristic in this form. They do not hold for arbitrary
non-Archimedean local fields; \(\mathbb Q_2\) has eight square classes
and seven quadratic extensions. Any earlier convention restricting
the chapter to odd residue characteristic must be carried into these
statements. The synopses state it explicitly.

## Chapter 14

See [SYNOPSIS-VK14](SYNOPSIS-VK14.md).

### E14.01 — Confirmed factorial and exponent errors

Source: Volume 3, §14.1.1, p. 1, formula (3).

The numerator prints \((q;q)_r\) instead of \((q;q)_N\), and the
q-exponent is divided by 4 instead of 2.
The correct identity is
\[
 (q;q)_{N-r}
 =\frac{(-1)^r(q;q)_Nq^{r(r-2N-1)/2}}{(q^{-N};q)_r}.
\]
At \(r=0\), the printed right side is 1 but the left side is
\((q;q)_N\); this detects one error without any convention choice.

### E14.02 — Confirmed q-differentiation errors

Source: Volume 3, §14.1.8, p. 17, formulas (3)–(4).

The formulas mix multiplicative series parameters with exponents and
ordinary-looking derivative constants. At \(x=0\), the leading monomial
alone disproves the printed coefficients.
If \(A=q^\alpha\), \(C=q^\gamma\), and \(D_q\) is the divided
q-derivative in §14.1.5, the correct forms are
\[
 D_q\{x^\alpha{}_2\phi_1(A,B;C;q,x)\}
 =\frac{1-A}{1-q}x^{\alpha-1}
       {}_2\phi_1(Aq,B;C;q,x),
\]
\[
 D_q\{x^{\gamma-1}{}_2\phi_1(A,B;C;q,x)\}
 =\frac{1-C/q}{1-q}x^{\gamma-2}
       {}_2\phi_1(A,B;C/q;q,x).
\]
The printed second coefficient is \(2-c\), which is not a q-number.

## Chapter 15

See [SYNOPSIS-VK15](SYNOPSIS-VK15.md).

### E15.01 — Confirmed missing semisimplicity

Source: Volume 3, §15.1.2, p. 139, Cartan characterization.

A maximal commutative subalgebra containing regular elements need not
be Cartan. In \(\mathfrak{sl}_2(\mathbb C)\), the span of a nonzero
nilpotent E is maximal abelian and E has minimal centralizer dimension,
but its normalizer also contains H. Thus it is not a Cartan subalgebra.
Use a maximal toral subalgebra in the complex semisimple setting, or
the general nilpotent self-normalizing definition.
For real algebras, diagonalizability must be interpreted over the
complexification when discussing nonsplit Cartan subalgebras.

### E15.02 — Confirmed component ambiguity

Source: Volume 3, §15.2.1, p. 173, maximal compact subgroup.

For the full GL(n,R), a maximal compact subgroup is O(n), not SO(n).
SO(n) is correct for GL⁺(n,R), or for the determinant-one connected
setting. The reflection of one coordinate exhibits the missing component.
The cone stabilizer and integration constants must use the same choice.

## Chapter 16

See [SYNOPSIS-VK16](SYNOPSIS-VK16.md).

### E16.01 — Confirmed missing global hypotheses

Source: Volume 3, §16.2.5, p. 229, first sentence.

Not every nilpotent Lie group embeds in a complex unitriangular group.
The circle is nilpotent and has nontrivial finite-order elements,
whereas a characteristic-zero unitriangular group is torsion free.
The faithful unitriangular realization applies to the suitable simply
connected nilpotent setting. The subsequent orbit-method theorem
already states connectedness and simple connectedness.

## Chapter 17

See [SYNOPSIS-VK17](SYNOPSIS-VK17.md).

### E17.01 — Confirmed missing absolute values

Source: Volume 3, §17.4.1, p. 328, matrix norm.

The maximum eigenvalue of a Hermitian matrix is called its norm.
For \(-2I\) it is negative. Use \(\max_j|\lambda_j|\).
Without this correction, the condition “norm < 1” incorrectly includes
matrices outside the matrix Gauss series' convergence ball.

## Chapter 19

See [SYNOPSIS-VK19](SYNOPSIS-VK19.md).

### E19.01 — Confirmed overrestriction

Source: Volume 3, §19.1.6, pp. 459–460, multiplier systems.

For a nonintegral weight and a fixed branch of \((c\tau+d)^k\),
the multiplier must compensate the branch cocycle and is not generally
a group character. The theta and eta multipliers furnish the relevant
examples. One may instead work on a suitable covering group, where
the automorphy factor becomes a genuine action.

### E19.02 — Confirmed missing affine-type condition

Source: Volume 3, §19.4.7, pp. 519–520, affine classification.

Indecomposable, symmetrizable, and corank one do not imply affine type.
Let J be the 3×3 all-ones matrix and u the three-entry all-ones column.
The symmetric generalized Cartan matrix
\[
 A=\begin{pmatrix}3I-J&0&-u\\0&3I-J&-u\\-u^t&-u^t&2\end{pmatrix}
\]
is connected and has eigenvalues
\(0,3,3,3,3,1+\sqrt7,1-\sqrt7\).
It has corank one but is indefinite. Affine type additionally requires
positive semidefinite symmetrization, equivalently the appropriate
positive null-vector condition.

### E19.03 — Confirmed missing highest-weight restriction

Source: Volume 3, §19.5.3, p. 530, assertion 2.

The classification is stated for every irreducible integrable
representation, although only highest-weight representations are
classified here. The contragredient lowest-weight module of a
nontrivial positive-level integrable highest-weight module is
irreducible and integrable, with finite weight multiplicities and
negative level, and cannot be one of the listed dominant
highest-weight modules. Keep the highest-weight hypothesis.

### E19.04 — Confirmed cone confusion

Source: Volume 3, §19.5.4, p. 530, order on weights.

The character-support order uses a difference in P⁺, the dominant
weight cone. For highest-weight characters it must use Q⁺, the
nonnegative integral simple-root cone. A simple root itself need not
be dominant: in \(A_1^{(1)}\), \(\alpha_1(h_0)=-2\).
Thus replacing Q⁺ by P⁺ changes the permitted lower weights and the
completion in which the character product is formed.

## Conventions and checks that are not source errata

- Volume 1, §6.8.2, p. 351: the Meixner coefficient includes the factor
  \((-1)^s\). The omission recorded for the EMS 59 reference must not be
  transferred to this display.
- Volume 1, §5.3.5, p. 230, formula (24): its two translation series have
  different Gaussian prefactors, consistently with their opposite parameter
  shifts. They are not a common-prefactor identity.
- Volume 2, Chapter 13: \(q\) is often a finite-field cardinality greater than
  one, while the basic-series base is \(q^{-1}\). Chapter 14 also uses the
  symmetric q-number. A normalization difference alone is not an erratum.
- Volume 2, §12.6.6, p. 482: the displayed two-parameter polynomial
  orthogonality is bilinear with a complex weight. It contains no complex
  conjugation. It should not be read as positive Hilbert orthogonality.
- Volume 3, Chapter 17: the polynomial normalization is fixed by the expansion
  of \((\mathrm{Tr}X)^r\). Replacing it by a monic Jack normalization changes
  the hypergeometric coefficients.
- Volume 3, Chapter 19: the initial definition of modular forms permits
  meromorphic forms. This is a terminology difference from the holomorphic
  structure used by Mathlib, not an error.
- Chapters without an individual entry above have no confirmed discrepancy
  recorded in this pass. This record is not a substitute for checking a
  formula's branches and exceptional parameters before formalization.

## Remaining checks before formalization

1. Check continued Mellin–Barnes and sign-channel kernels against their
   defining integral on every connected branch domain, especially where a
   contour crossing creates a discrete residue.
2. Check the explicit noncompact Plancherel constants in the exact Haar
   normalization selected for formalization. The synopses' probability
   compact measures and the source's area measures need conversion factors.
3. For Chapters 17–18, compare the real, complex, and quaternionic determinant
   conventions and the square-root phases of normalized pattern coefficients.
4. For Chapter 19's type-dependent string and branching functions, retain the
   lattice \(M\), adjacent lattice \(M'\), rational initial q-power, and
   theta-characteristic convention when transcribing an individual identity.
