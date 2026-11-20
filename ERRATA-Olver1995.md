# Errata and source checks: Olver (1995), Equivalence, Invariants, and Symmetry

Reference: Peter J. Olver, *Equivalence, Invariants, and Symmetry*, Cambridge University Press,
Cambridge, 1995. Local copy:
[References/Olver1995EquivalenceInvariantsSymmetry-Cambridge.pdf](References/Olver1995EquivalenceInvariantsSymmetry-Cambridge.pdf).

Locators use printed page numbers. To get the one-based PDF page number, add 16 (throughout the
book). Line numbers, where given, count from the top of the page; negative line numbers count
from the bottom.

## Status vocabulary

- **Confirmed.** A contradiction is exhibited. It may be a direct calculation, a special case
  or counterexample, a numerical evaluation, a standard definition fixed in the source, or a
  conflict between two displays of the source.
- **Normalization check.** Two displays cannot both hold under one stated convention. An
  unstated change of basis, coordinate, branch or measure may explain the difference. The
  synopsis fixes one convention and states the conversion.
- **Open check.** A suspected problem that is not settled. The entry states the uncertainty
  and the conjectured correction. Formalization is expected to decide it.

Each erratum gives:

- the status;
- the location, as chapter, section (by its heading in the source and its number in the
  synopsis), printed page and equation or numbered item;
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries;
- where the same error is listed in one of the published corrections lists below, a Published
  line citing the item by its page and line, and saying how its correction differs from ours.

Synopsis entries cite errata by id. An erratum id \(\mathrm{O95\text-E}cc.s.nn\) is the
\(nn\)-th erratum located in section \(s\) of chapter \(cc\), with the sections numbered as in
the synopsis (the source's sections are unnumbered; \(s=0\) is chapter-introductory material).
An erratum in Table \(t\) at the end of the book has the id \(\mathrm{O95\text-ET}.t.nn\).

## Published errata lists

P. J. Olver gives two corrections lists for the book on his web pages:

- [Olver EIS 2nd printing], by P. J. Olver: *Corrections to second printing of Olver, P.J.,
  Equivalence, Invariants, and Symmetry, Cambridge University Press, Cambridge, 1995*, last
  modified January 4, 2021 (69 items). It applies to the supplied copy, whose copyright page
  reads "First published 1995, Reprinted 1996, This digitally printed version 2008", i.e. the
  second printing.
- [Olver EIS 1st printing], by P. J. Olver: *Corrections to first printing of Olver, P.J.,
  Equivalence, Invariants, and Symmetry, Cambridge University Press, Cambridge, 1995*, last
  modified January 4, 2021 (85 items). The second list repeats most of its items. The
  mathematical items that the second list omits were corrected in the second printing; this was
  confirmed on the supplied copy at pp. 61, 73, 85, 87, 108, 126, 142, 198, 368, 425 and 472.
  Two of those corrections carry statements recorded here: the claim that the normalizer is a
  normal subgroup (p. 55, [O95-E02.8.01]) and the quotient \(G_H/G\) (p. 190, [O95-E06.3.01]).

Both lists locate an item by printed page and line, with negative line numbers counted from the
bottom of the page. A Published line cites the item in this form. Some published corrections are
themselves incomplete or differ from ours; the Published line then says so, with the evidence in
the entry. Published corrections to statements that are correct as printed, and suggestions that
do not correct an error, are recorded in the chapter's notes (not errata), with the evidence.
Published corrections to statements that the synopsis does not cover are listed in the section
"Published corrections to material outside the synopses" at the end of this file. Items of the
lists that concern only wording, remarks on the literature, cross-references, figures, the index
or the bibliography are not recorded here.

## Scope

These are observations about this edition, not an official publisher list. No claim is made
that formulas without an erratum are free of errors. Formulas that a synopsis marks "as
printed" were transcribed from the page images without an independent check. Corrected
formulas in the synopsis are statements to be formalized. They are not Lean proofs. Garbling of
the text layer of the PDF is not recorded; every erratum was checked on the page image.

Each chapter section ends with a list of conventions and notation that are not errata, for
example a sign convention that differs from a modern reference, or a hypothesis that the source
states once globally and omits in a particular statement.

## Summary by chapter

- Chapter 1. Geometric Foundations: 40 entries, 4 errata (Confirmed 4).
- Chapter 2. Lie Groups: 59 entries, 8 errata (Confirmed 8).
- Chapter 3. Representation Theory: 48 entries, 10 errata (Confirmed 8, Normalization check 2).
- Chapter 4. Jets and Contact Transformations: 51 entries, 10 errata (Confirmed 10).
- Chapter 5. Differential Invariants: 35 entries, 9 errata (Confirmed 9).
- Chapter 6. Symmetries of Differential Equations: 51 entries, 15 errata (Confirmed 15).
- Chapter 7. Symmetries of Variational Problems: 29 entries, 4 errata (Confirmed 4).
- Chapter 8. Equivalence of Coframes: 21 entries, 2 errata (Confirmed 2).
- Chapter 9. Formulation of Equivalence Problems: 12 entries, 1 erratum (Confirmed 1).
- Chapter 10. Cartan's Equivalence Method: 22 entries, 22 errata (Confirmed 20, Normalization check 1, Open check 1).
- Chapter 11. Involution: 25 entries, 5 errata (Confirmed 5).
- Chapter 12. Prolongation of Equivalence Problems: 30 entries, 10 errata (Confirmed 10).
- Chapter 13. Differential Systems: 16 entries, 4 errata (Confirmed 4).
- Chapter 14. Frobenius' Theorem: 22 entries, 2 errata (Confirmed 2).
- Chapter 15. The Cartan–Kähler Existence Theorem: 16 entries, 1 erratum (Confirmed 1).
- Tables: 7 entries, 1 erratum (Confirmed 1).
- Total: 484 entries, 108 errata (Confirmed 104, Normalization check 3, Open check 1).

## Chapter 1. Geometric Foundations

### O95-E01.2.01. Nondegeneracy condition in the definition of functional dependence

Status: Confirmed.
Location: §1.2 (Functions), p. 12, Definition 1.9.
Printed: \(f_1,\dots,f_k\) are functionally dependent if near each \(x_0\) there is a smooth
\(H(z_1,\dots,z_k)\), "not identically zero on any subset of \(\mathbb R^k\)", with
\(H(f_1(x),\dots,f_k(x))=0\).
Correct: \(H\) not identically zero on any nonempty open subset of \(\mathbb R^k\).
Evidence: Read literally, "not identically zero on any subset" applied to the singletons
\(\{(f_1(x_0),\dots,f_k(x_0))\}\) says \(H(f(x_0))\ne0\), contradicting \(H(f(x))=0\); no family
would be dependent. The example on the same page (\(f_2=f_1/(1+f_1^2)\), with
\(H(z_1,z_2)=z_2(1+z_1^2)-z_1\), which vanishes on a curve) requires the open-set reading.
Target: [O95.01.2.05].

### O95-E01.3.01. Closedness condition for the linear curve on the torus

Status: Confirmed.
Location: §1.3 (Submanifolds), p. 15, Example 1.16.
Printed: the curve \(\phi(t)=(t,\kappa t)\bmod 2\pi\) on \(T^2\) is closed if \(\kappa/\pi\) is
rational, and dense if \(\kappa/\pi\) is irrational.
Correct: closed (a regular submanifold with parameter space \(S^1\)) iff \(\kappa\in\mathbb Q\);
dense iff \(\kappa\notin\mathbb Q\).
Evidence: \(\phi(t)=\phi(0)\) requires \(t=2\pi p\) and \(\kappa t=2\pi q\) with
\(p,q\in\mathbb Z\), \(p\ne0\), i.e. \(\kappa=q/p\). For \(\kappa=\pi\) (\(\kappa/\pi=1\)
rational) closure would need \(\pi p\in\mathbb Z\), impossible; by Kronecker's theorem that
curve is dense.
Target: [O95.01.3.03].

### O95-E01.5.01. Domain of the commuting-flows criterion in Theorem 1.28

Status: Confirmed.
Location: §1.5 (Lie Brackets), p. 22, Theorem 1.28.
Printed: \([\mathbf v,\mathbf w]=0\) iff \(\exp(t\mathbf v)\exp(s\mathbf w)x=\exp(s\mathbf w)
\exp(t\mathbf v)x\) "for all \(x\in M\) and all \(t,s\in\mathbb R\) where the equation is
defined".
Correct: for all \(x\) and all \((t,s)\) in a connected open set \(V\subset\mathbb R^2\)
containing \((0,0)\) on which both sides are defined, e.g. the connected component of \((0,0)\)
in the set where both sides are defined.
Evidence: Let \(M\) be the universal cover of \(\mathbb R^2\setminus\{0\}\) with the lifts of
\(\mathbf v=\partial_x\), \(\mathbf w=\partial_y\), so \([\mathbf v,\mathbf w]=0\), and let \(x\)
lie over \((-1,-1)\). Both sides are defined except on the rays \(\{s=1,\ t\ge1\}\) and
\(\{t=1,\ s\ge1\}\). At \(t=s=2\) both are defined, but the paths
\((-1,-1)\to(-1,1)\to(1,1)\) and \((-1,-1)\to(1,-1)\to(1,1)\) together encircle the origin once,
so the two sides lie on different sheets over \((1,1)\). The point \((2,2)\) lies in the
component \(\{t>1,\ s>1\}\), which does not contain \((0,0)\).
Published: [Olver EIS 2nd printing], p. 22, Theorem 1.28, line 3.
Target: [O95.01.5.02].

### O95-E01.7.01. Sign of the angle form

Status: Confirmed.
Location: §1.7 (Differential Forms), p. 29, Example 1.40.
Printed: \(\omega=(x^2+y^2)^{-1}[y\,dx-x\,dy]\); "locally \(\omega=d\theta\) is the differential of
the polar angle \(\theta=\tan^{-1}(y/x)\)".
Correct: \(\omega=-d\theta\) (equivalently \(d\theta=(x^2+y^2)^{-1}(x\,dy-y\,dx)\)).
Evidence: \(d\tan^{-1}(y/x)=\dfrac{1}{1+y^2/x^2}\Big(\dfrac{dy}{x}-\dfrac{y\,dx}{x^2}\Big)=
\dfrac{x\,dy-y\,dx}{x^2+y^2}\). At \((1,0)\), \(\omega=-dy\) while \(d\theta=dy\). The
conclusions (closed, not exact) are unaffected.
Target: [O95.01.7.09].

### Conventions and notation (not errata)

- p. 12: "covering map" means a surjective local diffeomorphism defined on all of \(M\); fibres
  need not have constant cardinality, unlike the standard notion ([O95.01.2.03]).
- p. 16: "The Implicit Function Theorem 1.10" refers to Theorem 1.7 (Theorem 1.10 is the theorem
  on regular families of functions).
- p. 17, Theorem 1.21: the dimension \(m-r\) refers to the rank \(r\) of the family near the
  variety, which the statement does not name ([O95.01.3.07]).
- p. 30, Definition 1.41 and p. 31, (1.29): the source's rank of a one-form is the length of the
  nonvanishing derived sequence; its rank of a two-form is half the matrix rank.
- p. 31: the stated sufficient condition \(x^{2j-1}\ne0\), \(j=1,\dots,s\), for the even Darboux
  form to have rank \(2s\) is not necessary; the exact condition is
  \((x^1,x^3,\dots,x^{2s-1})\ne0\) ([O95.01.8.02]).

## Chapter 2. Lie Groups

### O95-E02.1.01. The projective linear group in Example 2.13

Status: Confirmed.
Location: §2.1 (Transformation Groups), p. 39, Example 2.13.
Printed: "The quotient subgroup \(PSL(n,\mathbb R)=GL(n,\mathbb R)/\{\lambda\mathbb 1\}\) is called the
projective group. Note that if \(n\) is odd, we can identify \(PSL(n,\mathbb R)\simeq
SL(n,\mathbb R)\) … if \(n\) is even, … and hence \(PSL(n,\mathbb R)=SL(n,\mathbb R)/\{\pm\mathbb
1\}\)."
Correct: the projective group is \(PGL(n,\mathbb R)=GL(n,\mathbb R)/\{\lambda\mathbb 1\}\); for
\(n\) odd \(PGL(n,\mathbb R)\simeq SL(n,\mathbb R)\); for \(n\) even
\(PSL(n,\mathbb R)=SL(n,\mathbb R)/\{\pm\mathbb 1\}\) is the identity component of
\(PGL(n,\mathbb R)\), of index two.
Evidence: For \(n\) even the two printed descriptions of \(PSL(n,\mathbb R)\) differ:
\(\det(\lambda A)=\lambda^n\det A\), so the sign of the determinant is well defined on
\(GL(n,\mathbb R)/\{\lambda\mathbb 1\}\), and the class of \(\mathrm{diag}(-1,1,\dots,1)\) is not
the image of an element of \(SL(n,\mathbb R)\).
Published: [Olver EIS 2nd printing], p. 39, Example 2.13 (two items: the first two occurrences of
\(PSL(n,\mathbb R)\) become \(PGL(n,\mathbb R)\), and a sentence identifying \(PSL(n,\mathbb R)\)
with the identity component of \(PGL(n,\mathbb R)\) is appended).
Target: [O95.02.1.07].

### O95-E02.2.01. Closed orbits of the linear torus flow

Status: Confirmed.
Location: §2.2 (Invariant Subsets and Equations), p. 41, Example 2.20.
Printed: for \((\theta,\varphi)\mapsto(\theta+t,\varphi+\kappa t)\bmod2\pi\), the orbits are closed
and the action regular if \(\kappa/\pi\) is rational; if \(\kappa/\pi\) is irrational the orbits are
dense.
Correct: the orbits are closed and the action regular iff \(\kappa\in\mathbb Q\); dense iff
\(\kappa\notin\mathbb Q\).
Evidence: as in [O95-E01.3.01]: the orbit of \((0,0)\) returns to \((0,0)\) iff \(t=2\pi p\),
\(\kappa t=2\pi q\), \(p,q\in\mathbb Z\), \(p\ne0\), i.e. \(\kappa=q/p\). Example 2.33 on p. 45
treats the same flow with the condition "\(\kappa\) irrational", in conflict with this display.
Target: [O95.02.2.04].

### O95-E02.2.02. Orbit dimension does not characterize effectively free actions

Status: Confirmed.
Location: §2.2, p. 42, Proposition 2.22, second sentence.
Printed: "The group acts effectively freely if and only if its orbits have dimension
\(s=\dim G-\dim G_M\)."
Correct: the orbits all have dimension \(\dim G-\dim G_M\) iff \(G/G_M\) acts locally freely
(each \(G_x/G_M\) discrete). Effective freeness (\(G_x=G_M\) for all \(x\), p. 38) implies this,
but not conversely.
Evidence: \(G=SO(2)\) acting on \(M=\mathbb C^2\setminus\{0\}\) by
\((z,w)\mapsto(e^{i\theta}z,e^{2i\theta}w)\): \(G_M=\{1\}\), every orbit is one-dimensional
\(=\dim G-\dim G_M\), but \(G_{(0,1)}=\{\pm1\}\ne G_M\), so the action is not effectively free.
The first sentence of the proposition (locally free iff all orbits have dimension \(\dim G\)) is
the correct analogue.
Target: [O95.02.2.05].

### O95-E02.4.01. Cross-ratio of the canonical quadruple

Status: Confirmed.
Location: §2.4 (Invariant Functions), p. 47, Example 2.35.
Printed: the canonical form \((0,1,\infty,z)\) has cross-ratio \(1/(z-1)\).
Correct: with (2.7), \([0,1,\infty,z]=1/(1-z)\).
Evidence: \([p_1,p_2,p_3,p_4]=\frac{(p_1-p_2)(p_3-p_4)}{(p_1-p_3)(p_2-p_4)}\) with
\(p_3\to\infty\) gives \(\frac{(p_1-p_2)\cdot(-1)}{p_2-p_4}=\frac{-(0-1)}{1-z}=\frac1{1-z}\); e.g.
\([0,1,R,2]=(-1)(R-2)/((-R)(-1))\to-1=1/(1-2)\) as \(R\to\infty\). The second value on the same
page, \([s,-s,s^{-1},-s^{-1}]=-4/(s-s^{-1})^2\), is correct.
Target: [O95.02.4.05].

### O95-E02.6.01. Antisymmetry of the structure constants

Status: Confirmed.
Location: §2.6 (Structure Constants), p. 51, (2.14), first identity.
Printed: \(C^k_{ij}=-C^k_{ij}\).
Correct: \(C^k_{ij}=-C^k_{ji}\).
Evidence: the printed identity forces all \(C^k_{ij}=0\); antisymmetry of the bracket in (2.13)
gives \(C^k_{ij}=-C^k_{ji}\), and e.g. \(\mathfrak a(1)\) (Example 2.46) has \(C^2_{12}=-1\),
\(C^2_{21}=1\). The second identity of (2.14) (Jacobi) is correct.
Published: [Olver EIS 2nd printing], p. 51, (2.14).
Target: [O95.02.6.01].

### O95-E02.8.01. The normalizer is not a normal subgroup

Status: Confirmed.
Location: §2.8 (Subgroups and Subalgebras), p. 55, Exercise 2.59.
Printed: "the normalizer subgroup \(G_H=\{g\,|\,gHg^{-1}\subset H\}\) is a normal subgroup with Lie
algebra \(\mathfrak g_H=\{\mathbf v\in\mathfrak g\,|\,[\mathbf v,\mathbf w]\in\mathfrak h\) for all
\(\mathbf w\in\mathfrak h\}\)".
Correct: \(G_H\) is a subgroup of \(G\) in which \(H\) is normal (for connected \(H\) a closed Lie
subgroup when \(H\) is closed), with the stated Lie algebra; it need not be normal in \(G\).
Evidence: \(G=SO(3)\), \(H=SO(2)\) (rotations about the \(z\)-axis): \(G_H\) is the group of
rotations preserving the \(z\)-axis (\(\cong O(2)\)), which is not normal in \(SO(3)\), since a
rotation taking the \(z\)-axis to the \(x\)-axis conjugates it to the stabilizer of the \(x\)-axis.
(Also \(SO(3)\) is simple, so its only normal subgroups are trivial.)
Published: [Olver EIS 1st printing], p. 55, lines 4–5, changes "\(G_H=\{g\,|\,gHg^{-1}\subset H\}\) has Lie
algebra" to "\(G_H=\dots\) is a normal subgroup with Lie algebra"; the supplied printing carries
this change, and the inserted claim is the error recorded here. [Olver EIS 2nd printing] has no item for it.
Target: [O95.02.8.04].

### O95-E02.12.01. Inversion map of \(SE(2)\)

Status: Confirmed.
Location: §2.12 (Invariant Vector Fields), p. 68, (2.27) and the following display.
Printed: \(\iota(a,b,\theta)=(a\cos\theta+b\sin\theta,\,-a\sin\theta+b\cos\theta,\,-\theta)\), hence
\(\iota(x,y,z)=\big((x+yz)/\sqrt{1+z^2},\,(y-xz)/\sqrt{1+z^2},\,-z\big)\).
Correct: \(\iota(a,b,\theta)=(-a\cos\theta-b\sin\theta,\ a\sin\theta-b\cos\theta,\ -\theta)\) and
\(\iota(x,y,z)=\big(-(x+yz)/\sqrt{1+z^2},\,-(y-xz)/\sqrt{1+z^2},\,-z\big)\).
Evidence: \(g=(a,b,\theta)\) acts by \(x\mapsto R_\theta x+(a,b)^T\) (so that \(g\cdot0=(a,b,
\tan\theta)\) as stated). At \(\theta=0\) the printed formula gives \(\iota(a,b,0)=(a,b,0)\), but the
inverse of translation by \((a,b)\) is translation by \((-a,-b)\). The conclusion that \(d\iota\)
maps the generators (2.25) to the invariant fields (2.26) holds up to sign for either formula: a
direct computation gives \(d\iota(\mathbf v_1,\mathbf v_2,\mathbf v_3)=(-\mathbf w_1,\mathbf w_2,
-\mathbf w_3)\) for the corrected \(\iota\) (and \((\mathbf w_1,-\mathbf w_2,-\mathbf w_3)\) for
the printed one), consistent with \(d\iota(\mathbf v^R)=-\mathbf v^L\).
Target: [O95.02.12.03].

### O95-E02.13.01. Sign of the second invariant one-form for \(SE(2)\)

Status: Confirmed.
Location: §2.13 (Lie Derivatives and Invariant Differential Forms), p. 71, Example 2.94.
Printed: the invariant one-forms dual to (2.26) are \(\omega^1=(dx+z\,dy)/\sqrt{1+z^2}\),
\(\omega^2=(dy-z\,dx)/\sqrt{1+z^2}\), \(\omega^3=dz/(1+z^2)\).
Correct: the dual coframe has \(\omega^2=(z\,dx-dy)/\sqrt{1+z^2}\); the printed \(\omega^2\) is its
negative (still invariant, but not dual to \(\mathbf w_2\)).
Evidence: with \(\mathbf w_2=(z\partial_x-\partial_y)/\sqrt{1+z^2}\) from (2.26),
\(\langle(dy-z\,dx)/\sqrt{1+z^2};\mathbf w_2\rangle=(-1-z^2)/(1+z^2)=-1\).
Target: [O95.02.13.04].

### Conventions and notation (not errata)

- p. 48: "the" Lie algebra is the right-invariant one; its bracket is the negative of the matrix
  commutator on \(\mathfrak{gl}(n)\) (Example 2.42), and the generator map
  \(\mathfrak g_R\to\{\)vector fields\(\}\) is then a homomorphism (Theorem 2.62).
- p. 39, Example 2.15: the displayed hyperbolic rotations form the identity component of
  \(O(1,1)\), not all of \(O(1,1)\) (which has four components).
- p. 55: "three infinite families of classical complex Lie groups" counts \(SL\), \(SO\), \(Sp\)
  (four Cartan series \(A,B,C,D\)).
- p. 70, Example 2.92: the vector field is written \(\sum_{i=1}^p\xi^i\partial_{x^i}\) on
  \(\mathbb R^m\); read \(p=m\).
- p. 59, Theorem 2.70: the table's "Action" column lists representative group laws; the
  classification is of Lie algebras of vector fields up to local diffeomorphism.
- p. 36: [Olver EIS 2nd printing], p. 36 (line before Example 2.9), changes the local action "of \(GL(2)\) on the
  complex plane" to one of \(GL(2,\mathbb C)\). This makes the intended group explicit; the
  printed statement is also correct for \(GL(2,\mathbb R)\), which acts on \(\mathbb C\) by real
  linear fractional transformations.
- p. 65, Example 2.80: [Olver EIS 2nd printing], p. 65, line 8, changes "\(\mathbf v(HF)=0\) whenever \(H=0\)" to
  "\(\mathbf v(H)=0\)". The printed statement is also correct, since \(\mathbf v(F)=0\) gives
  \(\mathbf v(HF)=F\,\mathbf v(H)=-2xy(x^2+1)^{-1}HF\); the synopsis [O95.02.11.04] states the
  intended \(\mathbf v(H)\).

## Chapter 3. Representation Theory

### O95-E03.2.01. The \(\rho_{n,k}\) are not all irreducible representations of \(GL(2)\)

Status: Confirmed.
Location: §3.2 (Representations on Function Spaces), p. 80, paragraph after Theorem 3.10.
Printed: "the representations \(\rho_{n,k}\) provide a complete list of all irreducible
finite-dimensional representations of GL(2)".
Correct: the \(\rho_{n,k}\) (\(n\ge0\), \(k\in\mathbb Z\)) are all the irreducible holomorphic
(rational) finite-dimensional representations of \(GL(2,\mathbb C)\). Continuous irreducible
finite-dimensional representations of \(GL(2,\mathbb R)\) also include twists by
\(|\det A|^s\) (\(s\in\mathbb R\)) and by \(\mathrm{sign}\det A\).
Evidence: \(A\mapsto\mathrm{sign}\det A\) is a one-dimensional (hence irreducible) continuous
representation of \(GL(2,\mathbb R)\); a one-dimensional \(\rho_{n,k}\) has \(n=0\) and is
\(A\mapsto(\det A)^{-k}\), which differs from \(\mathrm{sign}\det A\) at \(A=2I\) for \(k\ne0\) and
at \(A=\mathrm{diag}(-1,1)\) for \(k=0\). Likewise \(A\mapsto|\det A|^{1/2}\). Exercise 3.23 (p. 89)
itself records the extra multiplier \(\mathrm{sign}\det A\) for \(GL(2,\mathbb R)\).
Target: [O95.03.2.06].

### O95-E03.4.01. Multiplication operator for the scalar matrices in \(\mu_{n,k}\)

Status: Confirmed.
Location: §3.4 (Infinitesimal Multipliers), pp. 86–87, Example 3.19.
Printed: the multiplier \(\mu_{n,k}\) has infinitesimal generators \(\partial_p\),
\(p\partial_p-\frac12n\), \(p^2\partial_p-np\), "and \(2k\), the latter denoting the multiplication
operator by the constant function \(2k\)"; these act locally effectively on the extended space
"when \(k\ne0\)".
Correct: the operator for the generator \(I\in\mathfrak{gl}(2)\) of the scalar subgroup is
multiplication by \(2k+n\), and the extended action is locally effective iff \(2k+n\ne0\).
Evidence: by (3.17), \(\exp(tI)=e^tI\) gives \(\mu_{n,k}(e^tI,p)=(e^{2t})^{-k}(e^t)^{-n}=
e^{-(2k+n)t}\), so \(h_I=-(2k+n)\) and \(\mathcal D_I=0-h_I=2k+n\). Consistency check: with the same
conventions \(\tfrac12(E_{11}-E_{22})\) gives \(h=\tfrac n2\) (the printed \(p\partial_p-\frac12n\))
and \(E_{11}\) gives \(p\partial_p+k\); then \(\mathcal D_{E_{22}}=\mathcal D_I-\mathcal D_{E_{11}}
=-p\partial_p+k+n\), which agrees with the direct computation for \(\mathrm{diag}(1,e^t)\)
(\(\bar p=e^{-t}p\), \(\mu=e^{-(k+n)t}\)). For example, for \(n=2\), \(k=-1\) the scalars act trivially on the
extended space although \(k\ne0\).
Target: [O95.03.4.04].

### O95-E03.5.01. Linear invariants correspond to relative invariants for the dual action

Status: Confirmed.
Location: §3.5 (Relative Invariants), p. 93, first full paragraph.
Printed: "a linear function \(J(x,u)=\sum_{\alpha=1}^nR_\alpha(x)u^\alpha\) is an invariant of the
extended group action (3.15) if and only if the vector-valued function
\(R(x)=(R_1(x),\dots,R_q(x))^T\) is a relative invariant of weight \(\mu\)".
Correct: \(J(x,v)=\sum_{\alpha=1}^qR_\alpha(x)v^\alpha\) is an invariant of the dual action
\((x,v)\mapsto(g\cdot x,\mu(g,x)^{-T}v)\) on \(E^*=M\times U^*\) iff \(R\) is a relative invariant
of weight \(\mu\).
Evidence: With (3.15), \((x,u)\mapsto(g\cdot x,\mu(g,x)u)\), and Definition 3.30,
\(R(g\cdot x)=\mu(g,x)R(x)\): \(R(g\cdot x)^T\mu(g,x)^{-T}v=R(x)^Tv\), whereas
\(R(g\cdot x)^T\mu(g,x)u=R(x)^T\mu^T\mu\,u\). Scalar example: \(G=\mathbb R\) acting on
\(\mathbb R\) by \(x\mapsto x+t\) with the multiplier \(\mu(t,x)=e^t\); \(R(x)=e^x\) is a relative
invariant, but under (3.15) \(J=e^xu\) becomes \(e^{x+t}e^tu=e^{2t}J\), while under the dual
action \(v\mapsto e^{-t}v\) the function \(e^xv\) is invariant. Example 14.6 (p. 425) uses the dual
action.
Published: [Olver EIS 2nd printing], p. 93, first full paragraph (replaced).
Target: [O95.03.5.04].

### O95-E03.6.01. Normalization of the coefficient vector fields (3.30)

Status: Normalization check.
Location: §3.6 (Classical Invariant Theory), p. 96, Theorem 3.40, (3.30), and pp. 96–97, the
quadratic example.
Printed: "Using the coefficients \(a_0,\dots,a_n\) as coordinates, cf. (3.3)", the generators are
\(\mathbf v_-=a_1\partial_{a_0}+2a_2\partial_{a_1}+\dots+na_n\partial_{a_{n-1}}\) and
\(\mathbf v_+=na_0\partial_{a_1}+(n-1)a_1\partial_{a_2}+\dots+a_{n-1}\partial_{a_n}\); for
\(Q=ax^2+2bxy+cy^2\) (3.5) they are \(\mathbf v_-=b\partial_a+2c\partial_b\),
\(\mathbf v_+=2a\partial_b+b\partial_c\), and "they are readily seen to annihilate the discriminant
\(\Delta=b^2-4ac\)".
Correct: in the binomial normalization (3.3) the generators are (up to an overall sign per field)
\(\mathbf v_-=\sum_{i}(n-i)a_{i+1}\partial_{a_i}\), \(\mathbf v_+=\sum_iia_{i-1}\partial_{a_i}\),
\(\mathbf v_0=\sum_i(2i-n)a_i\partial_{a_i}\); for (3.5): \(2b\partial_a+c\partial_b\),
\(-2a\partial_a+2c\partial_c\), \(a\partial_b+2b\partial_c\), which annihilate
\(\Delta=b^2-ac\) (the discriminant used on p. 95). The printed (3.30) is correct for the
unnormalized forms \(Q=\sum_ia_ix^iy^{n-i}\), for which \(Q=ax^2+bxy+cy^2\) has discriminant
\(b^2-4ac\).
Evidence: for \(x\mapsto x+ty\) (so \(\bar Q(\mathbf z)=Q(A^{-1}\mathbf z)\)) and
\(Q=ax^2+2bxy+cy^2\), \(\frac{d}{dt}(\bar a,\bar b,\bar c)|_{t=0}=(-2b,-c,0)\); for
\(Q=\sum a_ix^iy^{n-i}\) the same computation gives \(-(j+1)a_{j+1}\) in the \(a_j\) component,
i.e. the printed \(\mathbf v_-\). Applying the printed \(\mathbf v_-=b\partial_a+2c\partial_b\) to
\(b^2-ac\) gives \(3bc\ne0\), and to \(b^2-4ac\) gives \(0\). The determination of invariants is
unaffected once one normalization is used consistently; the synopsis states the binomial version.
Published: [Olver EIS 2nd printing], p. 96, (3.30), replaces the fields by
\(\mathbf v_-=\sum_i(n-i)a_{i+1}\partial_{a_i}\), \(\mathbf v_0=\sum_i(n-2i)a_i\partial_{a_i}\),
\(\mathbf v_+=\sum_iia_{i-1}\partial_{a_i}\), the binomial version given here (its
\(\mathbf v_0\) is the negative of ours). The list does not correct the quadratic example on
pp. 96–97, whose fields \(b\partial_a+2c\partial_b\), \(2a\partial_b+b\partial_c\) and the
discriminant \(b^2-4ac\) then disagree with the corrected (3.30).
Target: [O95.03.6.03].

### O95-E03.6.02. The field \(\mathbf v_0\) in the quadratic example

Status: Confirmed.
Location: §3.6, p. 96, last line.
Printed: for a quadratic polynomial (3.5), \(\mathbf v_0=-2a\partial_a+2b\partial_b\).
Correct: \(\mathbf v_0=-2a\partial_a+2c\partial_c\), as (3.30) gives for \(n=2\) (coefficients
\(-n,-(n-2),\dots,n\), i.e. \(-2,0,2\)).
Evidence: (3.30) with \(n=2\); the printed field does not annihilate either candidate
discriminant: \((-2a\partial_a+2b\partial_b)(b^2-ac)=2ac+4b^2\) and
\((-2a\partial_a+2b\partial_b)(b^2-4ac)=8ac+4b^2\), whereas \(-2a\partial_a+2c\partial_c\)
annihilates both.
Target: [O95.03.6.02], [O95.03.6.03].

### O95-E03.6.03. Vanishing Hessian: real scalar factor and degree one

Status: Confirmed.
Location: §3.6, p. 101, Theorem 3.49.
Printed: "A homogeneous function (polynomial) \(Q(x,y)\) of degree \(n\) has zero Hessian,
\(H[Q]\equiv0\), if and only if \(Q(x,y)=(ax+by)^n\) is the \(n\)-th power of a linear form."
Correct: for a nonzero polynomial of degree \(n\ge2\): over \(\mathbb C\), \(H\equiv0\) iff
\(Q=(ax+by)^n\); over \(\mathbb R\), iff \(Q=c(ax+by)^n\) with \(c\in\mathbb R\) (for odd \(n\) the
constant can be absorbed, for even \(n\) one needs \(c=\pm1\)). For homogeneous functions of degree
\(n\ne1\) the statement holds locally with \(c(ax+by)^n\) on a branch domain; for degree \(1\) every
homogeneous function has \(H\equiv0\).
Evidence: \(Q=-x^2\) is real, \(H=Q_{xx}Q_{yy}-Q_{xy}^2=(-2)\cdot0-0=0\), and \(-x^2\ne(ax+by)^2\)
for real \(a,b\). For functions: \(Q=x^2/y\) on \(y\ne0\) is homogeneous of degree \(1\) with
\(Q_{xx}=2/y\), \(Q_{xy}=-2x/y^2\), \(Q_{yy}=2x^2/y^3\), so
\(H=4x^2/y^4-4x^2/y^4=0\), but \(Q\) is not linear. In (3.46) the factor \(n(n-1)\) vanishes for
\(n=1\), so the ODE argument of the proof does not apply there.
Target: [O95.03.6.11].

### O95-E03.6.04. Index ranges in Stroh's covariants

Status: Confirmed.
Location: §3.6, p. 103, Theorem 3.51.
Printed: "\(Q\), \(R_r=(Q,Q)^{(2r)}\), \(0\le2r\le n\), and \((Q,R_r)^{(1)}\), \(0\le2r\le n-1\),
provide a complete set of \(n\) rationally independent covariants of \(Q\)."
Correct: \(1\le r\le n/2\) and \(1\le r\le(n-1)/2\), respectively (i.e. \(0<2r\)).
Evidence: with \(r=0\) included the list has \(1+(\lfloor n/2\rfloor+1)+(\lfloor(n-1)/2\rfloor+1)=
n+2\) members, not \(n\); moreover \(R_0=(Q,Q)^{(0)}=Q^2\) is a function of \(Q\), and
\((Q,R_0)^{(1)}=(Q,Q^2)^{(1)}=Q_x\cdot2QQ_y-Q_y\cdot2QQ_x=0\). With \(r\ge1\) the count is
\(1+\lfloor n/2\rfloor+\lfloor(n-1)/2\rfloor=n\).
Target: [O95.03.6.14].

### O95-E03.6.05. Normalizing factor of the quadratic invariant of the quartic

Status: Confirmed.
Location: §3.6, p. 104, Example 3.52.
Printed: \(i=\frac1{1372}(Q,Q)^{(4)}\).
Correct: \(i=\frac1{1152}(Q,Q)^{(4)}\) for \(i\) as in (3.35) and the transvectant (3.37).
Evidence: direct expansion for \(Q=a_0x^4+4a_1x^3y+6a_2x^2y^2+4a_3xy^3+a_4y^4\) gives
\((Q,Q)^{(4)}=1152\,(a_0a_4-4a_1a_3+3a_2^2)\); e.g. \(Q=x^4+y^4\): \(Q_{xxxx}=Q_{yyyy}=24\), all
mixed fourth derivatives vanish, so \((Q,Q)^{(4)}=2\cdot24\cdot24=1152\), while \(i=1\).
(\(1372=2^2\cdot7^3\) has no relation to the factorials of the quartic.)
Target: [O95.03.6.15].

### O95-E03.6.06. Normalizing factor of the cubic invariant of the quartic

Status: Confirmed.
Location: §3.6, p. 104, Example 3.52.
Printed: \(j=\frac1{96}(Q,H)^{(4)}\), with \(H=\frac12(Q,Q)^{(2)}\).
Correct: \(j=\frac1{248832}(Q,H)^{(4)}\), \(248832=2^{10}3^5\), for \(j\) as in (3.35).
Evidence: symbolic expansion of \((Q,H)^{(4)}\) for the general quartic (3.34) gives
\(248832\det\begin{pmatrix}a_0&a_1&a_2\\a_1&a_2&a_3\\a_2&a_3&a_4\end{pmatrix}\). Spot check:
\(Q=6x^2y^2\) (\(a_2=1\)): \(j=-1\), \(H=Q_{xx}Q_{yy}-Q_{xy}^2=144x^2y^2-576x^2y^2=-432x^2y^2\), and
\((Q,H)^{(4)}=6\binom42Q_{xxyy}H_{xxyy}=6\cdot24\cdot(-1728)=-248832\).
Target: [O95.03.6.15].

### O95-E03.6.07. Coefficients of the quartic syzygy

Status: Normalization check.
Location: §3.6, p. 104, Example 3.52, (3.47).
Printed: \(jQ^3=\frac1{72}iQ^2H-\frac1{2^73^6}H^3-\frac1{2^{12}3^4}T^2\), with
\(H=\frac12(Q,Q)^{(2)}\), \(T=(Q,H)^{(1)}\).
Correct: with these \(H\) and \(T\) and with \(i,j\) as in (3.35),
\(jQ^3=\frac1{144}iQ^2H-\frac1{2^{10}3^6}H^3-\frac1{2^{14}3^4}T^2\). The printed coefficients are
right if \(H\) is replaced by \(\frac14(Q,Q)^{(2)}\) and \(T\) by \((Q,\frac14(Q,Q)^{(2)})^{(1)}\).
Evidence: solving \(jQ^3=c_1iQ^2H+c_2H^3+c_3T^2\) identically in \(a_0,\dots,a_4,x,y\) gives the
unique solution \(c_1=1/144\), \(c_2=-1/746496\), \(c_3=-1/1327104\); under \(H\mapsto H/2\),
\(T\mapsto T/2\) these become \(1/72\), \(-1/93312=-1/(2^73^6)\), \(-1/331776=-1/(2^{12}3^4)\).
Spot check with \(Q=6x^2y^2\): \(i=3\), \(j=-1\), \(H=-432x^2y^2\), \(T=0\); the corrected identity
reads \(-216=\frac{3\cdot36\cdot(-432)}{144}+\frac{432^3}{746496}=-324+108\).
Target: [O95.03.6.15].

### Conventions and notation (not errata)

- p. 77: the right Lie algebra convention gives \(\mathfrak{gl}(V)\) the bracket \(BA-AB\); a Lie
  algebra representation then satisfies \(\rho([\mathbf v,\mathbf w])=\rho(\mathbf w)\rho(\mathbf
  v)-\rho(\mathbf v)\rho(\mathbf w)\).
- p. 82: the source's multipliers are cocycles of the action (Definition 3.12), not Mackey's
  multipliers of projective representations (footnote on p. 82).
- p. 89 and p. 95: weight conventions for the determinantal multiplier differ in sign: Exercise 3.26
  has generators \(x\partial_x-k\) (multiplier \((\det A)^k\)), while p. 95 writes
  \(\mu_k(A,\mathbf x)=(\det A)^{-k}\) in line with (3.7) and (3.12).
- p. 97: the cubic discriminant (3.33) is \(-\frac2{27}\) times the polynomial discriminant of
  \(Q(p,1)\); any constant multiple is a relative invariant.
- p. 103, Example 3.52: "a binary quartic, (3.1)" refers to (3.34).
- Theorem 3.40 (p. 96) characterizes relative invariants for the group generated by \(SL(2)\) and
  the scalar matrices (\(GL(2,\mathbb C)\), \(GL(2,\mathbb R)^+\)); for \(\det A<0\) a further sign
  check is required ([O95.03.6.03]).

## Chapter 4. Jets and Contact Transformations

### O95-E04.2.01. Orbit dimension in Theorem 4.6

Status: Confirmed.
Location: §4.2, p. 110, Theorem 4.6.
Printed: "acting semi-regularly and transversally on \(E\simeq X\times U\) with
\(r\)-dimensional orbits. Let \(I_1,\dots,I_{p-s},J_1,\dots,J_q\) be a complete set of
functionally independent invariants".
Correct: the orbits are \(s\)-dimensional.
Evidence: on the \((p+q)\)-dimensional space \(E\) a complete set of invariants for
\(s\)-dimensional orbits has \(p+q-s\) members (Theorem 2.38), matching the list
\(I_1,\dots,I_{p-s},J_1,\dots,J_q\); the next paragraph also speaks of orbits of the projected
action that "also have dimension \(s\)".
Published: [Olver EIS 2nd printing], p. 110, Theorem 4.6, line 2.
Target: [O95.04.2.02].

### O95-E04.3.01. The transformed jet in the definition of prolongation

Status: Confirmed.
Location: §4.3 (Jets and Prolongations), p. 113, line 7.
Printed: \(\bar z_0=(\bar x_0,\bar u_0^{(n)})=(x_0,\bar f(x_0))\).
Correct: \(\bar z_0=(\bar x_0,\bar u_0^{(n)})=(\bar x_0,\bar f^{(n)}(\bar x_0))\).
Evidence: \(\bar z_0\in J^n\) consists of the derivatives up to order \(n\) of \(\bar f=g\cdot f\) at
the image point \(\bar x_0\), as the preceding sentence says, with
\((\bar x_0,\bar f(\bar x_0))=g\cdot(x_0,f(x_0))\). For \(g:(x,u)\mapsto(x+1,u)\), \(f(x)=x\),
\(x_0=0\), \(n=1\): \(\bar f(x)=x-1\) and \(\bar z_0=(1,0,1)\), while \((x_0,\bar f(x_0))=(0,-1)\) and
\((x_0,\bar f^{(1)}(x_0))=(0,-1,1)\).
Published: [Olver EIS 2nd printing], p. 113, line 7, changes \(\bar f(x_0)\) to \(\bar f^{(n)}(x_0)\) but keeps the
base point \(x_0\); the evaluation point must be \(\bar x_0\).
Target: [O95.04.3.03].

### O95-E04.5.01. Cross-reference in Example 4.20

Status: Confirmed.
Location: §4.5, p. 120, Example 4.20, line after (4.35).
Printed: "The Lie algebra (4.14) clearly projects to the \((x,p)\)-plane".
Correct: "The Lie algebra (4.35)".
Evidence: (4.14) is the list of coefficients of the linear fractional map (4.13); the algebra
being projected is the first prolongation (4.35).
Published: [Olver EIS 2nd printing], p. 120, second line after (4.35).
Target: [O95.04.5.08].

### O95-E04.5.02. Truncation in the evolutionary form (4.31)–(4.32)

Status: Confirmed.
Location: §4.5, p. 119, (4.31)–(4.32).
Printed: \(\mathbf v_Q^{(n)}=\sum_{\alpha=1}^q\sum_{\#J\ge0}D_JQ^\alpha\,\partial_{u^\alpha_J}\) (4.31)
and \(\mathbf v^{(n)}=\mathbf v_Q^{(n)}+\sum_{i=1}^p\xi^iD_i\) (4.32).
Correct: \(\mathbf v_Q^{(n)}=\sum_\alpha\sum_{0\le\#J\le n}D_JQ^\alpha\,\partial_{u^\alpha_J}\) and
\(\mathbf v^{(n)}=\mathbf v_Q^{(n)}+\sum_i\xi^iD_i^{(n)}\), where \(D_i^{(n)}\) is the total
derivative (4.18) with the sum restricted to \(0\le\#J\le n\).
Evidence: \(\mathbf v^{(n)}\) is a vector field on \(J^n\) ((4.20)–(4.21)), with coefficients
\(\varphi^\alpha_J=D_JQ^\alpha+\sum_i\xi^iu^\alpha_{J,i}\) for \(\#J\le n\); the printed right side of
(4.32) has \(\partial_{u^\alpha_J}\)-components of every order and equals the infinite prolongation.
Published: [Olver EIS 2nd printing], p. 119, (4.31) and (4.32) (two items).
Target: [O95.04.5.06].

### O95-E04.6.01. Coefficients of a one-form on \(J^n\)

Status: Confirmed.
Location: §4.6 (Contact Forms), p. 124, first display, first line.
Printed: \(\omega=\sum_{i=1}^pQ(x,u^{(n)})\,dx^i+\sum_{\alpha=1}^q\sum_{\#J\le n}P^J_\alpha
(x,u^{(n)})\,du^\alpha_J\).
Correct: \(\omega=\sum_{i=1}^pQ_i(x,u^{(n)})\,dx^i+\dots\).
Evidence: A general one-form has independent coefficients of the \(dx^i\); the second line of the
display and (4.41) use \(Q_i\).
Published: [Olver EIS 2nd printing], p. 124, first displayed equation.
Target: [O95.04.6.05].

### O95-E04.7.01. Generating function of the Legendre transformation

Status: Confirmed.
Location: §4.7, p. 127, paragraph after Theorem 4.28.
Printed: "the function \(H=\bar u-u-\bar xx\) generates the Legendre transformation (4.47)".
Correct: \(H=\bar u-u+\bar xx\) generates (4.47). The printed \(H\) generates the variant
\(\bar x=-p\), \(\bar u=u-xp\), \(\bar p=x\).
Evidence: (4.51) with \(H=\bar u-u-S(\bar x,x)\) gives \(p=-S_x\), \(\bar p=S_{\bar x}\),
\(\bar u=u+S\) (as the source states). For \(S=\bar xx\) this is \(\bar x=-p\), \(\bar p=x\),
\(\bar u=u-xp\); for \(S=-\bar xx\) it is \(\bar x=p\), \(\bar p=-x\), \(\bar u=u-xp\), which is
(4.47).
Target: [O95.04.7.04].

### O95-E04.7.02. Letter in (4.52)

Status: Confirmed.
Location: §4.7, p. 128, Exercise 4.31, (4.52).
Printed: \(\sum_{i=1}^p\pi^\alpha_i(x,u^{(1)})D_j\xi^i=D_j\psi^\alpha\).
Correct: \(\sum_{i=1}^p\pi^\alpha_i(x,u^{(1)})D_j\chi^i=D_j\psi^\alpha\).
Evidence: the exercise defines the map by \(\bar x^i=\chi^i(x,u^{(1)})\); no \(\xi^i\) occurs in
it, and (4.53) correctly uses \(\chi^i\). The identity is the chain rule
\(D_j\bar u^\alpha=\sum_i\bar u^\alpha_iD_j\bar x^i\).
Target: [O95.04.7.07].

### O95-E04.8.01. Index range in (4.58)

Status: Confirmed.
Location: §4.8, p. 130, (4.58).
Printed: \(\partial Q^\alpha/\partial u^\beta_i+\xi^i\delta^\alpha_\beta=0\),
\(\alpha,\beta=1,\dots,q\), \(j=1,\dots,p\).
Correct: the free index is \(i=1,\dots,p\).
Evidence: \(\partial Q^\alpha/\partial u^\beta_i=\partial\varphi^\alpha/\partial u^\beta_i-
\sum_ju^\alpha_j\,\partial\xi^j/\partial u^\beta_i-\xi^i\delta^\alpha_\beta\), so (4.55) is
equivalent to (4.58) with index \(i\); \(j\) does not occur in the displayed equation.
Target: [O95.04.8.02].

### O95-E04.9.01. Coefficient of \(\partial_p\) in the first line of (4.67)

Status: Confirmed.
Location: §4.9, p. 135, (4.67), first line.
Printed: \(\mathbf v_+=2xu\partial_x+u^2\partial_u-2xp\,\partial_p\).
Correct: \(\mathbf v_+=2xu\partial_x+u^2\partial_u-2xp^2\,\partial_p\).
Evidence: by (4.29), \(\varphi^x=D_x(u^2)-pD_x(2xu)=2up-p(2u+2xp)=-2xp^2\). The second line of
(4.67) is computed the same way and is correct:
\(2up-p(2u+2xp+2x)=-2x(p^2+p)\). The base fields of both lines are the images of the Type 1.1
and Type 1.2 algebras under \((x,u)\mapsto(1/u,x)\) (checked symbolically).
Target: [O95.04.9.03].

### O95-E04.9.02. The function \(h\) in (4.68)

Status: Confirmed.
Location: §4.9, p. 135, paragraph after (4.68).
Printed: \(h(p)=\sqrt{\sqrt{p+1}+\sqrt p}\), so that \((p^2+p)h'(p)^2=h(p)^2\).
Correct: \(h(p)=(\sqrt{p+1}+\sqrt p)^2\) (up to a constant factor).
Evidence: the condition \((p^2+p)h'^2=h^2\) is the right one: with the corrected (4.67), the
\(\partial_{\bar p}\)-component of the push-forward of the second \(\mathbf v_+\) under (4.68)
differs from the first \(\mathbf v_+\) by \(2x\big(h^2-(p^2+p)h'^2\big)/h'\). Solving,
\(h'/h=1/\sqrt{p^2+p}\), \(\log h=2\log(\sqrt p+\sqrt{p+1})\). The printed \(h\) gives
\((p^2+p)h'^2=h^2/16\). With \(h=(\sqrt{p+1}+\sqrt p)^2\) all three fields of the second algebra
map to those of the first (checked symbolically).
Target: [O95.04.9.03].

### Conventions and notation (not errata)

- p. 112 onward: \(p\) denotes both the number of independent variables and, for \(p=q=1\), the
  derivative coordinate \(u_x\) (the source's footnote on p. 113).
- p. 116, Exercise 4.15: "\(F\) is constant" means locally constant on a disconnected domain.
- p. 120, Example 4.20: the intransitive algebra \(\partial_x,x\partial_x,x^2\partial_x\) is called
  Type 3.3, which Table 3 lists as \(\partial_u,u\partial_u,u^2\partial_u\) (the roles of \(x\) and
  \(u\) interchanged).
- p. 131: Lie's "characteristic function" is \(W=-Q\).
- pp. 128–129: Bäcklund's Theorem 4.32 is proved in the source only infinitesimally (for
  transformations connected to the identity through one-parameter groups); the full statement is
  cited ([15], [11]) and reproved in Chapters 11 and 15.
- p. 134: Lie's classification (Theorem 4.37) is complex; the source states that the real
  classification has not been done. Table 4 lists characteristics, not vector fields; the vector
  fields (4.66) are recovered from (4.61) up to sign (e.g. \(Q=u_x\) gives \(-\partial_x\)). The
  three algebras of Table 4 close under the bracket (checked symbolically).

## Chapter 5. Differential Invariants

### O95-E05.5.01. Signs of the generators (5.15)

Status: Confirmed.
Location: §5.5, p. 148, Example 5.18, (5.15).
Printed: \(\mathbf v_0=x\partial_x-\frac n2u\partial_u\), \(\mathbf v_+=x^2\partial_x-nxu\partial_u\).
Correct: \(\mathbf v_0=x\partial_x+\frac n2u\partial_u\), \(\mathbf v_+=x^2\partial_x+nxu\partial_u\).
Evidence: along \(\bar x=x/(1-tx)\) (\(\gamma=-t\), \(\delta=1\)) the action (5.14) gives
\(\bar u=(1-tx)^{-n}u\), with \(t\)-derivative \(nxu\) at \(t=0\); similarly for the scaling
subgroup. The corrected fields are consistent with (5.16) (\(u\) of weight \(n\)) and make
\(\widetilde H\), \(I\), \(J\) and \((u,\widetilde H)^{(1)}\) satisfy (5.16) with the stated weights
(checked symbolically); with the printed fields \(I\) is not invariant.
Published: [Olver EIS 2nd printing], p. 148, (5.15).
Target: [O95.05.5.04].

### O95-E05.5.02. Constant factor in (5.19)

Status: Confirmed.
Location: §5.5, p. 150, (5.19), first line.
Printed: \(J=u^{(2/n)}D_xI=u^{(6/n)-3}(u,H)^{(1)}\).
Correct: \(J=u^{2/n}D_xI=n^{-2}u^{(6/n)-3}(u,\widetilde H)^{(1)}\) (equivalently
\(n^{-2}(n-1)^{-1}u^{(6/n)-3}(u,H)^{(1)}\) with \(H=(n-1)\widetilde H\) as in (3.46)).
Evidence: \(D_xI=\frac1n\big[u^{(4/n)-2}D_x\widetilde H+(\frac4n-2)u^{(4/n)-3}u_x\widetilde
H\big]=n^{-2}u^{(4/n)-3}\big[nuD_x\widetilde H-(2n-4)u_x\widetilde H\big]\), and the bracket is
\((u,\widetilde H)^{(1)}\) by (5.17). The explicit second line of (5.19) is correct (checked
symbolically).
Target: [O95.05.5.05].

### O95-E05.5.03. Constant factor in (5.21)

Status: Confirmed.
Location: §5.5, p. 150, (5.21).
Printed: \(dI/du=u_x^{-1}D_xI=-u_x^{-2}(u_x,I)^{(1)}\).
Correct: \(dI/du=u_x^{-1}D_xI=-\frac12u_x^{-2}(u_x,I)^{(1)}\).
Evidence: by (5.20) with \(k=0\), \((u_x,I)^{(1)}=-2u_xD_xI\).
Target: [O95.05.5.07].

### O95-E05.5.04. Weight of the factors of \(S\)

Status: Confirmed.
Location: §5.5, p. 151, sentence after (5.22).
Printed: \(S\) is "the ratio of relative invariants of weight 4".
Correct: weight \(-8\).
Evidence: \(u_x\) has weight \(-2\), so \(u_x^4\) has weight \(-8\); the numerator is \(-1\) times
the Hessian \(\widetilde H\) of \(u_x\), of weight \(2(-2)-4=-8\); both satisfy (5.16) with
\(k=-8\) (checked symbolically).
Target: [O95.05.5.07].

### O95-E05.5.05. Order of pseudo-stabilization after (5.23)

Status: Confirmed.
Location: §5.5, p. 152, paragraph after (5.23).
Printed: "The intermediate cases \(0<k<r-1\) are when the orbit dimension pseudo-stabilizes at
order \(k\)".
Correct: at order \(k-1\).
Evidence: (5.23) gives \(s_{k-1}=k+1=s_k\) and \(s_k<s_{k+1}\); Example 5.8 (\(k=1\), \(s_0=s_1\))
and Theorem 5.24 (\(k=r-2\), pseudo-stabilization at \(r-3\)) agree with \(k-1\). The orbit
dimensions of Case 1.7a were recomputed for \(r=3,\dots,6\).
Target: [O95.05.5.08].

### O95-E05.5.06. Table reference for Lie's differential invariants

Status: Confirmed.
Location: §5.5, p. 152 ("his results are summarized in Table 6"), and §5.6, p. 156
("according to Table 6, the fundamental differential invariant can always be taken to be
linear").
Correct: Table 5 in both places.
Evidence: Table 5 (p. 474) is "Differential Invariants of Transformation Groups in
\(\mathbb C^2\)"; Table 6 (p. 475) is "Primitive Lie Algebras of Vector Fields in \(\mathbb R^2\)".
Pages 153–154 correctly cite Table 5.
Target: [O95.05.5.09], [O95.05.6.04].

### O95-E05.8.01. Macaulay's function \(\mu_p\)

Status: Confirmed.
Location: §5.8, p. 167, Lemma 5.45, (5.32)–(5.33), the example after them; p. 168,
Theorem 5.47 and the definition of \(\mu_p^n\).
Printed: \(l=\binom{k_1+p-1}p+\binom{k_2+p-2}{p-1}+\cdots+\binom{k_s+p-s}{p-s+1}\),
\(1\le s\le p\), \(\mu_p(l)=\binom{k_1+p}p+\cdots+\binom{k_s+p-s+1}{p-s+1}\); example
\(\mu_2(4)=8\); Theorem 5.47: \(d_{n+1}\ge\mu_p(d_n)\).
Correct: \(p\) should be replaced by \(p-1\) in (5.32)–(5.33):
\(l=\sum_{i=1}^s\binom{k_i+p-1-i}{p-i}\), \(1\le s\le p-1\),
\(\mu_p(l)=\sum_{i=1}^s\binom{k_i+p-i}{p-i}\); then \(\mu_2(4)=5\).
Evidence: with the printed \(\mu_p\), Theorem 5.47 fails already for a principal ideal: for one
form \(P\) of degree \(n\), \(d_n=1\) and \(d_{n+1}=p<p+1=\mu_p(1)\); for \(\mathcal I=(x)\subset
\mathbb R[x,y]\), \(d_4=4\), \(d_5=5<8\). The corrected \(\mu_p\) equals the size of the upper
shadow of the initial lex segment of \(l\) monomials of degree \(n\) (the Macaulay minimum) for
all \(1\le l\le p_n\) (checked by enumeration for \(p=2,3,4\), \(n=4,6\)), and it satisfies
\(\mu_p(p_n)=p_{n+1}\), which the source uses (\(\mu_p^n(l)=\mu_p(l)\) for \(l\le p_n\)). Theorem
5.48 is correct with the corrected \(\mu_p\).
Target: [O95.05.8.03], [O95.05.8.04].

### O95-E05.8.02. Factor in the gradient identity of Example 5.50

Status: Confirmed.
Location: §5.8, p. 172, Example 5.50.
Printed: \(u_x^2+u_y^2=\frac12r^{-2}[(-yu_x+xu_y)^2+(xu_x+yu_y)^2]\).
Correct: \(u_x^2+u_y^2=r^{-2}[(-yu_x+xu_y)^2+(xu_x+yu_y)^2]\).
Evidence: \((-yu_x+xu_y)^2+(xu_x+yu_y)^2=(x^2+y^2)(u_x^2+u_y^2)\).
Target: [O95.05.8.06].

### O95-E05.8.03. Strict convexity inequality in Lemma 5.46

Status: Confirmed.
Location: §5.8, p. 167, Lemma 5.46, (5.34).
Printed: if \(l=i_1+\cdots+i_q=j_1+\cdots+j_r\) with nonincreasing positive parts and
\(i_1>j_1\), then \(\mu_p(l)\le\mu_p(i_1)+\cdots+\mu_p(i_q)<\mu_p(j_1)+\cdots+\mu_p(j_r)\).
Correct: the first inequality holds; the second, strict, inequality is false as stated, both for
the printed \(\mu_p\) and for the corrected one of [O95-E05.8.01].
Evidence: printed \(\mu_2\) (\(\mu_2(1..6)=3,5,6,8,9,10\)): \(l=5=4+1=3+2\) gives
\(\mu_2(4)+\mu_2(1)=11=\mu_2(3)+\mu_2(2)\). Corrected \(\mu_2(l)=l+1\): \(l=4=3+1=2+2\) gives
\(6=6\). Exhaustive search for \(l\le12\): the first inequality never fails; the second fails
often, even in non-strict form, and for \(p\ge3\) also under dominance of the partitions. The
proof of Theorem 5.48 needs only that \(\sum_a\mu_p(l_a)\), subject to \(0\le l_a\le p_n\) and
\(\sum_al_a=l\), is minimal for the greedy choice (as many \(l_a=p_n\) as possible); this is
evident for \(p=2\) (corrected \(\mu_2(l)=l+1\)) but is not established here for \(p\ge3\).
Target: [O95.05.8.03], [O95.05.8.04].

### Conventions and notation (not errata)

- §5.5: the first transvectant of relative differential invariants is
  \((R,S)^{(1)}=kR\,D_xS-l\,D_xR\,S\) for weights \(k,l\) ((5.17), (5.20)). This is the negative
  of (3.44) for \(r=1\), which gives \(mF'G-nFG'\). Even transvectants (e.g. \(\widetilde H\)) agree.
- §5.5, (5.16): a relative differential invariant of weight \(k\) transforms with the multiplier
  \((\gamma x+\delta)^{-k}\) of (5.14), so \(u\) has weight \(n\). \(\widetilde H\) omits the factor
  \(n-1\) of (3.46).
- p. 163, Example 5.39: the formula \(h_{-1}=\frac12(q+1)q=r\) is Green's convention. With it,
  \(k_1=h_1-2h_0+h_{-1}\), which agrees with (5.29) under the source's convention
  \(h_{-1}=r-1\) and the "+1" case.
- Theorem 5.24 is stated for point transformation groups; Table 5 also covers the contact cases.
- Example 4.20 and Example 5.18 use Lie's case numbers with \(x\) and \(u\) as in the source's
  examples, which may differ from the variable names in Tables 1–3.
- p. 171, Theorem 5.49: [Olver EIS 2nd printing], p. 171, lines 20 and −8, lowers the bound on the order of the
  fundamental differential invariants from \(n+2\) to \(n+1\), and [Olver EIS 2nd printing], p. 171, lines −7 to −3,
  deletes the following sentence, which states the bound \(n+1\) in the special case
  \(s_n\le q^{(n)}\). The printed bound is implied by the corrected one, so it is not an error;
  the synopsis [O95.05.8.05] states the printed bound. The stronger bound is not proved in the
  book; it is the bound of the later moving-frame theory (a moving frame of order \(n\) yields
  generating differential invariants of order at most \(n+1\)) and was not checked here.

## Chapter 6. Symmetries of Differential Equations

### O95-E06.2.01. Inversional symmetry of the heat equation

Status: Confirmed.
Location: §6.2 (Infinitesimal Methods), p. 184, the two displays after Example 6.10.
Printed: the group of \(\mathbf v_6\) is
\((x,t,u)\mapsto\big(\frac{x}{1-4\varepsilon t},\frac{t}{1-4\varepsilon t},u\sqrt{1-4\varepsilon t}
\exp\{\frac{-x\varepsilon x^2}{1-4\varepsilon t}\}\big)\), and the transformed solution is
\(u=\frac{1}{1+4\varepsilon t}\exp\{\frac{-\varepsilon x^2}{1+4\varepsilon t}\}
f\big(\frac{x}{1+4\varepsilon t},\frac{t}{1+4\varepsilon t}\big)\).
Correct: the exponent in the group action is \(-\varepsilon x^2/(1-4\varepsilon t)\), and the
prefactor of the transformed solution is \((1+4\varepsilon t)^{-1/2}\).
Evidence: The flow of \(\mathbf v_6=4xt\partial_x+4t^2\partial_t-(x^2+2t)u\partial_u\) has
\(\tilde t=t/(1-4\varepsilon t)\), \(\tilde x=x/(1-4\varepsilon t)\) and
\(\frac{d}{d\varepsilon}\log\tilde u=-(\tilde x^2+2\tilde t)\), which is satisfied by
\(\log\tilde u=\log u+\frac12\log(1-4\varepsilon t)-\varepsilon x^2/(1-4\varepsilon t)\); the
printed exponent is not even homogeneous under the scaling symmetry. For \(f\equiv1\),
\(u=(1+4\varepsilon t)^{-k}\exp\{-\varepsilon x^2/(1+4\varepsilon t)\}\) gives
\(u_t-u_{xx}=0\) for \(k=\frac12\) but \(u_t-u_{xx}=-2\varepsilon(1+4\varepsilon t)^{-2}
\exp\{\cdots\}\ne0\) for \(k=1\). The text on the same page itself states the particular solution
\(c(1+4\varepsilon t)^{-1/2}\exp[\cdots]\).
Target: [O95.06.2.05].

### O95-E06.3.01. Quotient group in the normalizer reduction theorem

Status: Confirmed.
Location: §6.3 (Integration of Ordinary Differential Equations), p. 190, Theorem 6.23.
Printed: "the \(H\)-reduced equation \(\Delta/H=0\) admits the quotient group \(G_H/G\), where
\(G_H=\{g\mid g\cdot H\cdot g^{-1}\subset H\}\) is the normalizer subgroup".
Correct: the quotient group \(G_H/H\).
Evidence: \(G_H\subset G\), so \(G_H/G\) is not a quotient group unless \(G_H=G\), and then it is
trivial. The proof shows that \(\mathbf w\) induces a symmetry of the reduced equation iff
\([\mathbf v,\mathbf w]=c\mathbf v\), i.e. \(\mathbf w\in\mathfrak g_H\), and that \(\mathbf v\)
(which generates \(H\)) acts trivially on the reduced variables \(y,w=v_y\); the induced action is
that of \(G_H/H\).
Published: [Olver EIS 2nd printing], p. 190, line 9. [Olver EIS 1st printing], p. 190, lines 8–9, replaces the first
printing's "admits the corresponding normalizer subgroup \(G_H\) as a symmetry group" by the
quotient group \(G_H/H\); the supplied printing carries that change with \(G_H/G\) for
\(G_H/H\).
Target: [O95.06.3.04].

### O95-E06.3.02. Implicit solution of the homogeneous equation (6.26)

Status: Confirmed.
Location: §6.3, p. 188, Example 6.20, last line.
Printed: \(v=h(y)=\int dy/\{F(y)-my\}\), "thereby defining \(u\) implicitly: \(\log x=h(u/x)\)".
Correct: \(\log x=h(u/x^m)\).
Evidence: The rectifying coordinates are \(y=u/x^m\), \(v=\log x\). For \(m=2\), \(F\equiv0\)
(\(u_x=0\)): \(h(y)=-\frac12\log y+c\); \(\log x=h(u/x^2)\) gives \(u=e^{2c}\), a solution, while
\(\log x=h(u/x)\) gives \(u=e^{2c}/x\), which is not.
Published: [Olver EIS 2nd printing], p. 188, line −2.
Target: [O95.06.3.02].

### O95-E06.4.01. Rotationally invariant second order equations

Status: Confirmed.
Location: §6.4 (Characterization of Invariant Differential Equations), p. 192, (6.32).
Printed: \(u_{xx}=(1+u_x)^{3/2}H\big(\sqrt{x^2+u^2},\frac{xu_x-u}{x+uu_x}\big)\).
Correct: \(u_{xx}=(1+u_x^2)^{3/2}H\big(\sqrt{x^2+u^2},\frac{xu_x-u}{x+uu_x}\big)\).
Evidence: The display is obtained by solving \(F(r,w,\kappa)=0\) for \(u_{xx}\), with
\(\kappa=(1+u_x^2)^{-3/2}u_{xx}\) as stated in the preceding sentence. With the printed factor the
equation is not rotation invariant: the circle \(x^2+u^2=1\) has \(\kappa\equiv-1\), i.e.
\(u_{xx}=-(1+u_x^2)^{3/2}\), and is a solution of the corrected equation with \(H\equiv-1\), but
at the point \(x=\frac12\), \(u=\frac{\sqrt3}2\) (\(u_x=-1/\sqrt3\)) the printed right side
\(-(1-1/\sqrt3)^{3/2}\approx-0.27\) differs from \(u_{xx}=-8/(3\sqrt3)\approx-1.54\).
Published: [Olver EIS 2nd printing], p. 192, (6.32).
Target: [O95.06.4.02].

### O95-E06.4.02. Riccati form of Schwarz's theorem

Status: Confirmed.
Location: §6.4, p. 195, Theorem 6.28, last sentence.
Printed: "Alternatively, \(x=w_{uu}/w_u\), where \(w\) is an arbitrary solution to the Riccati
equation \(w_u=\frac12w^2+\widehat F(u)\)."
Correct: \(w=x_{uu}/x_u\) satisfies \(w_u=\frac12w^2+\widehat F(u)\); conversely \(x\) is recovered
from a solution \(w\) by two quadratures, \(x=\int C\exp(\int w\,du)\,du+D\).
Evidence: \(\{x;u\}=(x_{uu}/x_u)_u-\frac12(x_{uu}/x_u)^2\), so \(\{x;u\}=\widehat F\) is exactly
the Riccati equation for \(w=x_{uu}/x_u\). For \(\widehat F=0\), \(w=-2/(u+c)\) gives
\(w_{uu}/w_u=-2/(u+c)\): the printed formula yields only a one-parameter family, while the
general solution \((\alpha u+\beta)/(\gamma u+\delta)\) (Corollary 6.29) has three parameters,
e.g. \(x=u\) is not of the printed form.
Published: [Olver EIS 2nd printing], p. 195, line −4, changes the sentence to "Alternatively,
\(w=x_{uu}/x_u\) is an arbitrary solution …"; it does not say how \(x\) is recovered from
\(w\).
Target: [O95.06.4.05].

### O95-E06.4.03. Sign of the Wronskian in the parametric solutions

Status: Confirmed.
Location: §6.4, p. 196, (6.48); p. 197, (6.53); p. 198, Theorem 6.30, (6.56).
Printed: with \(\omega=\varphi\psi_u-\varphi_u\psi\): \(v=u_x=\psi(u)^2/\omega\) (6.48);
\(w=\psi_x/\psi=\psi\psi_u/\omega\) (6.53); in (6.56) \(x=\varphi/\psi\),
\(y=\frac1\psi\frac{d\psi}{dx}=\frac{\psi\psi_u}{\omega}\).
Correct: \(v=-\psi^2/\omega\) and \(w=\psi_x/\psi=-\psi\psi_u/\omega\); in (6.56) the dependent
variable is the Chazy unknown \(w\), not \(y\) (which denotes a differential invariant on
p. 197): \(w=\frac1\psi\frac{d\psi}{dx}=-\psi\psi_u/\omega\).
Evidence: From \(x=\varphi/\psi\), \(dx/du=(\varphi_u\psi-\varphi\psi_u)/\psi^2=-\omega/\psi^2\),
so \(u_x=-\psi^2/\omega\) and \(\psi_x/\psi=\psi_u/(\psi\,dx/du)=-\psi\psi_u/\omega\). Example:
\(\psi=u\), \(\varphi=1\) (solutions of \(\psi''=0\)) give \(\omega=1\), \(x=1/u\), \(u=1/x\),
\(u_x=-u^2\) and \(w=u_{xx}/(2u_x)=-1/x=-u\), whereas the printed formulas give \(+u^2\) and
\(+u\). The pair \(\varphi=\psi\int du/\psi^2\) of (6.42) has \(\omega=-1\), consistent with the
corrected sign and \(u_x=\psi^2\).
Published: [Olver EIS 2nd printing], p. 198, (6.56), changes \(y\) to \(w\) only; the sign of the
Wronskian in (6.48), (6.53) and (6.56) is not corrected.
Target: [O95.06.4.06], [O95.06.4.07], [O95.06.4.08].

### O95-E06.4.04. Constant in the invariant \(y\)

Status: Confirmed.
Location: §6.4, p. 197, (6.50) and the following sentence.
Printed: \(y=\frac2{s^2}\frac{dr}{du}=24+\frac{w_{xxx}-12ww_{xx}+18w_x^2}{(w_x-w^2)^2}\); "Once we know
the solution \(y=24+K(t)\) …".
Correct: \(y=-24+\frac{w_{xxx}-12ww_{xx}+18w_x^2}{(w_x-w^2)^2}\), and the reduced solution is
\(y=-24+K(t)\) (so that (6.51) holds as printed).
Evidence: With \(v_x=2wv\), \(s=(vv_{xx}-\frac32v_x^2)/v^4=2(w_x-w^2)/v^2\) and \(d/du=v^{-1}D_x\),
a direct computation gives \(r=2(w_{xx}-6ww_x+4w^3)/v^3\) (which reproduces the printed \(t\)) and
\[
\frac{2}{s^2}\frac{dr}{du}=\frac{w_{xxx}-12ww_{xx}-6w_x^2+48w^2w_x-24w^4}{(w_x-w^2)^2}
=-24+\frac{w_{xxx}-12ww_{xx}+18w_x^2}{(w_x-w^2)^2}.
\]
The source's own p. 198 is consistent only with \(-24\): for the Chazy equation (\(K=\alpha\)) it
states \(\frac{r}{s^2}\frac{dr}{ds}=\beta=\frac12(\alpha-24)\), i.e. \(y=2\beta=\alpha-24\).
Target: [O95.06.4.07].

### O95-E06.4.05. The separable equation for \(t\)

Status: Confirmed.
Location: §6.4, p. 197, (6.52).
Printed: \(s\,\dfrac{dt}{ds}=\dfrac{K(t)}{t}-\dfrac{3t}{2}\).
Correct: \(s\,\dfrac{dt}{ds}=\dfrac{K(t)-24}{2t}-\dfrac{3t}{2}\).
Evidence: \(t=rs^{-3/2}\) and \(dr/ds=(dr/du)/r=ys^2/(2r)\) give
\(s\,dt/ds=y/(2t)-\frac32t\), and \(y=-24+K(t)\) (O95-E06.4.04). Check on the Chazy case
\(K=\alpha\): from \(r^2=\frac23\beta s^3+c\), \(t^2=\frac23\beta+cs^{-3}\), so
\(2ts\,dt/ds=-3cs^{-3}=-3t^2+2\beta\), i.e. \(s\,dt/ds=\beta/t-\frac32t\) with
\(\beta=\frac12(\alpha-24)\), matching the correction and not the printed \(\alpha/t-\frac32t\).
Target: [O95.06.4.07].

### O95-E06.4.06. Polar form of the rotationally invariant second order equation

Status: Confirmed.
Location: §6.4, p. 192, display after (6.32).
Printed: \(r\theta_{rr}=(1+\theta_r^2)H(r,r\theta_r)-r^2\theta_r^3-2\theta_r\).
Correct: \(r\theta_{rr}=(1+r^2\theta_r^2)^{3/2}H(r,r\theta_r)-r^2\theta_r^3-2\theta_r\).
Evidence: For a curve \(\theta=\theta(r)\) the velocity and acceleration in the polar frame are
\((1,r\theta_r)\) and \((-r\theta_r^2,2\theta_r+r\theta_{rr})\), so
\(\kappa=(r\theta_{rr}+2\theta_r+r^2\theta_r^3)/(1+r^2\theta_r^2)^{3/2}\) (checked symbolically
against the Cartesian formula for \(\theta=r\)), and \(w=(xu_x-u)/(x+uu_x)=r\theta_r\); (6.32) is
\(\kappa=H(r,w)\).
Published: [Olver EIS 2nd printing], p. 192, displayed formula after (6.32).
Target: [O95.06.4.02].

### O95-E06.5.01. Size of the Lie determinant (6.61)

Status: Confirmed.
Location: §6.5 (Lie Determinants), p. 201, (6.61).
Printed: the determinant of the array with rows
\((\xi_\kappa,\varphi_\kappa,\varphi^1_\kappa,\dots,\varphi^{r-1}_\kappa)\), \(\kappa=1,\dots,r\).
Correct: rows \((\xi_\kappa,\varphi_\kappa,\varphi^1_\kappa,\dots,\varphi^{r-2}_\kappa)\).
Evidence: The rows are the coefficients of the prolongations \(\mathbf v_\kappa^{(r-2)}\) on
\(J^{r-2}\), of dimension \(r\); the printed array is \(r\times(r+1)\). Example 6.34 (\(r=4\)) uses
the \(4\times4\) determinant with columns up to \(\varphi^2\).
Published: [Olver EIS 2nd printing], p. 201, (6.61).
Target: [O95.06.5.02].

### O95-E06.9.01. Index labels in Wilczynski's invariants

Status: Confirmed.
Location: §6.9 (Differential Operators), p. 217, Theorem 6.59, (6.106).
Printed: "for each \(k=0,\dots,n-3\), the function
\(v^k(x)=\sum_{k=i}^{n-3}(-1)^{i+k}\frac{k!(n+1-i)!(2n+2-i-k)!}{i!(k-i)!(n+1-k)!(2n+2-2i)!}
\frac{d^{k-i}r^k}{dx^{k-i}}\) is a relative invariant of weight \((2k-2n,n-k)\)".
Correct: the free index is \(i\): for \(i=0,\dots,n-3\),
\(v^i=\sum_{k=i}^{n-3}(\text{same coefficient})\,d^{k-i}r^k/dx^{k-i}\) has weight
\((2i-2n,n-i)\).
Evidence: As printed the summation index coincides with the free index of the left side. With
\(i\) free, the case \(n=4\), \(i=0\) gives \(v^0=r^0-\frac12r^1_x\) (coefficient
\(-\frac{1!\,5!\,9!}{0!\,1!\,4!\,10!}=-\frac12\)), the invariant \(s-\frac12r_x\) of weight
\((-8,4)\) in Exercise 6.58, and \(v^1=r^1\) of weight \((-6,3)\); the weights are consistent
since \(r^k\) has weight \((2k-2n,n-k)\) and each derivative lowers the first weight by \(2\).
Target: [O95.06.9.09].

### O95-E06.9.02. Exponents in the solutions of \(u_n=0\)-equivalent equations

Status: Confirmed.
Location: §6.9, p. 217, Theorem 6.60 (iv).
Printed: \(u(x)=\sum_ic_iw_1(x)^iw_2(x)^{n-i}\).
Correct: \(u(x)=\sum_{i=0}^{n-1}c_iw_1(x)^iw_2(x)^{n-1-i}\).
Evidence: For \(u_n=0\) itself, take \(w_1=x\), \(w_2=1\) (basis of solutions of \(w''=0\)): the
solutions are the polynomials of degree \(\le n-1\), i.e. \(w_1^iw_2^{n-1-i}\),
\(i=0,\dots,n-1\). The printed products \(w_1^iw_2^{n-i}\) include \(x^n\), which is not a
solution, and there are \(n+1\) of them. The weight \(n-1\) of \(u\) in (6.99) also corresponds
to degree \(n-1\).
Target: [O95.06.9.10].

### O95-E06.9.03. Coefficients in the gauge factor (6.84)

Status: Confirmed.
Location: §6.9, p. 213, (6.84).
Printed: \(\eta(x)=|p^n(x)|^{(1-n)/(2n)}\exp\Big\{\int^x\frac{p^{n-1}(y)}{np^n(y)}dy\Big\}\).
Correct: \(\eta(x)=|f^n(x)|^{(1-n)/(2n)}\exp\Big\{\int^x\frac{f^{n-1}(y)}{nf^n(y)}dy\Big\}\), with
\(f^k\) the coefficients of \(\mathcal D\) (6.76).
Evidence: In (6.82) the \(p^k\) are the coefficients of the normal form, which has leading
coefficient \(\pm1\) and no \(D^{n-1}\) term; read with these, (6.84) would give \(\eta\equiv1\).
(6.83) uses \(f^n\), and Example 6.50 (\(n=2\), \(f^2=f\), \(f^1=g\)) gives
\(\eta=f^{-1/4}\exp\int g/(2f)\) (6.86), the corrected formula.
Published: [Olver EIS 2nd printing], p. 213, (6.84).
Target: [O95.06.9.02].

### O95-E06.10.01. Linear independence does not give a linear ODE

Status: Confirmed.
Location: §6.10 (Applications to the Geometry of Curves), p. 218, Proposition 6.63.
Printed: "Any set of \(n\) linearly independent functions \(u^1(x),\dots,u^n(x)\) forms a basis
for the solution space to a homogeneous linear \(n\)-th order ordinary differential equation."
Correct: if the Wronskian \(W_n=\det(D_x^iu^a)\) is nonzero on the interval, the \(u^a\) form a
basis of solutions of the nonsingular equation \(\sum_kW_kD_x^ku=0\); linear independence alone
is not enough.
Evidence: Let \(f(x)=e^{-1/x^2}\) for \(x>0\), \(f(x)=0\) for \(x\le0\), and \(u^1=f(x)\),
\(u^2=f(-x)\) on \(\mathbb R\) (\(n=2\)). They are smooth and linearly independent, but on
\(x>0\) \(u^2\equiv0\) and on \(x<0\) \(u^1\equiv0\), so every coefficient \(W_k\) of the
construction vanishes identically; and no equation \(a_2u''+a_1u'+a_0u=0\) with \(a_2\) nowhere
zero has both as a basis of solutions, since a solution vanishing on an interval vanishes
identically. The proof itself notes that singular points are zeros of \(W_n\).
Target: [O95.06.10.01].

### O95-E06.10.02. Signs of the coefficients in the proof of Proposition 6.63

Status: Confirmed.
Location: §6.10, p. 218, last line (proof of Proposition 6.63).
Printed: "we can set \(f^k(x)=W^k(x)\), where \(W^k(x)\) is the \(n\times n\) determinant obtained by
omitting the \(k^{\rm th}\) column" of the matrix of derivatives.
Correct: \(f^k(x)=(-1)^kW^k(x)\) (up to a common sign).
Evidence: The equation is the \((n+1)\times(n+1)\) determinant with first row
\((u,D_xu,\dots,D_x^nu)\) and rows \((u^a,D_xu^a,\dots,D_x^nu^a)\); expansion along the first row
gives \(\sum_k(-1)^kW^kD_x^ku\). For \(n=1\), \(u^1=e^x\): \(W^0=W^1=e^x\); the printed choice gives
\(u+u_x=0\), with solution \(e^{-x}\), the corrected one \(u-u_x=0\).
Published: [Olver EIS 2nd printing], p. 218, line −2.
Target: [O95.06.10.01].

### Conventions and notation (not errata)

- The Schwarzian derivative is \(\{x;u\}=(x_ux_{uuu}-\frac32x_{uu}^2)/x_u^2\); the invariant \(s\)
  of (6.36) is \(-\{x;u\}\), and in (6.40) the Schrödinger equation is
  \(\psi''-\frac12F\psi=0\) with \(F=s\), while (6.43) uses \(\widehat F=\{x;u\}\) and
  \(\psi''+\frac12\widehat F\psi=0\).
- In §6.9 the coefficients of an operator are written \(f^k\) in (6.76), and those of the
  normal forms (6.82), (6.93) are written \(p^k\); superscripts are labels. For the \(p\)'s in
  (6.84) see [O95-E06.9.03].
- Gauge equivalence \(\bar{\mathcal D}=\eta\cdot\mathcal D\cdot\eta^{-1}\) means
  \(w\mapsto\eta\,\mathcal D[w/\eta]\); (6.88) and (6.90) were checked in this reading.
- In Example 6.21 the letters \(a,b\) in \(u=(ax+b)^{1/(1-a)}\) denote both the equation's
  parameter and integration constants; the synopsis renames the constants.
- Example 6.47 refers to Example 6.34 for the hodograph transformation; the cross-reference is
  not to the intended example, which has no bearing on the mathematics.

## Chapter 7. Symmetries of Variational Problems

### O95-E07.3.01. Sign in the hodograph example

Status: Confirmed.
Location: §7.3 (Invariance of the Euler–Lagrange Equations), p. 231, Example 7.12, last line.
Printed: \(\mathrm E(L)=-2u_{xx}=-2\bar u_{\bar x}^{-3}\bar u_{\bar x\bar x}=-\mathrm E(\bar L)\).
Correct: \(\mathrm E(L)=-2u_{xx}=2\bar u_{\bar x}^{-3}\bar u_{\bar x\bar x}=-\mathrm E(\bar L)\).
Evidence: With \(\bar x=u\), \(\bar u=x\): \(u_x=1/\bar u_{\bar x}\) and
\(u_{xx}=-\bar u_{\bar x\bar x}/\bar u_{\bar x}^3\), so \(-2u_{xx}=2\bar u_{\bar x\bar x}/\bar
u_{\bar x}^3\). For \(\bar L=1/\bar u_{\bar x}\),
\(\mathrm E(\bar L)=-D_{\bar x}(-\bar u_{\bar x}^{-2})=-2\bar u_{\bar x}^{-3}\bar u_{\bar x\bar x}\);
the middle term as printed equals \(+\mathrm E(\bar L)\), contradicting the final equality (which,
with \(\mathrm F=-1\), is the correct instance of (7.21)).
Published: [Olver EIS 2nd printing], p. 231, lines −4 and −1, changes \(\mathrm E(\bar L)\) to
\(\bar{\mathrm E}(\bar L)\), the Euler operator in the barred variables (as the synopsis writes
it); it does not correct the sign of the middle term.
Target: [O95.07.3.02].

### O95-E07.4.01. Variational defect in the potential Boussinesq example

Status: Confirmed.
Location: §7.4 (Symmetries of Variational Problems), p. 237, Example 7.23, display before
Definition 7.24.
Printed: the criterion (7.34) for \(\mathbf v=c_1\mathbf v_1+c_2\mathbf v_2+c_3\mathbf v_3+\mathbf
v_f+\mathbf v_h\) requires \(\frac14c_3(-3u_{xt}^2+u_{xx}^3-3u_{xxx}^2)+h'(t)u_{xt}=0\).
Correct: \(-\frac12c_3(3u_{xt}^2+u_{xx}^3-3u_{xxx}^2)+h'(t)u_{xt}=0\), i.e.
\(-3c_3L+h'(t)u_{xt}=0\) with \(L=\frac12u_{xt}^2+\frac16u_{xx}^3-\frac12u_{xxx}^2\). The conclusion
(\(c_3=0\), \(h\) constant) is unchanged.
Evidence: For \(\mathbf v_3=x\partial_x+2t\partial_t\), \(\mathrm{Div}\,\xi=3\) and the prolongation
coefficients are \(-3u_{xt}\), \(-2u_{xx}\), \(-3u_{xxx}\) on \(\partial_{u_{xt}}\),
\(\partial_{u_{xx}}\), \(\partial_{u_{xxx}}\); hence
\(\mathbf v_3^{(3)}(L)+3L=(-3u_{xt}^2-u_{xx}^3+3u_{xxx}^2)+(\frac32u_{xt}^2+\frac12u_{xx}^3-
\frac32u_{xxx}^2)=-3L\), consistent with \(L\,dx\wedge dt\) scaling by \(\lambda^{-3}\) under
\((x,t)\mapsto(\lambda x,\lambda^2t)\). The printed polynomial is not proportional to \(L\)
(the signs of the \(u_{xt}^2\) and \(u_{xx}^3\) terms relative to \(u_{xxx}^2\) differ). For
\(\mathbf v_h=h(t)x\partial_u\) the only nonzero prolonged coefficient is \(h'(t)\) on
\(\partial_{u_{xt}}\), giving \(h'u_{xt}\).
Target: [O95.07.4.03].

### O95-E07.5.01. Euler–Lagrange equation in polar coordinates

Status: Confirmed.
Location: §7.5 (Invariant Variational Problems), p. 239, Example 7.28.
Printed: "the variational problem becomes \(\frac12\int F(r,r\theta_r)r\,dr\), with Euler–Lagrange
equation \(D_r[\frac12r^2F(r,r\theta_r)]=0\) … leading to \(r^2F(r,r\theta_r)=c\)".
Correct: the problem is \(\int F(r,r\theta_r)r\,dr\) (since \((x+uu_x)dx=r\,dr\)); its
Euler–Lagrange equation is \(D_r[r^2F_w(r,r\theta_r)]=0\), \(F_w=\partial F/\partial w\), with
first integral \(r^2F_w(r,r\theta_r)=c\).
Evidence: \(d(\frac12(x^2+u^2))=(x+uu_x)dx=r\,dr\). The Lagrangian \(rF(r,r\theta_r)\) depends on
\(\theta\) only through \(\theta_r\), so \(\mathrm E=-D_r[\partial(rF)/\partial\theta_r]=
-D_r[r^2F_w]\). For \(F=w^2\) (\(L=r^3\theta_r^2\)) the Euler–Lagrange equation is
\(D_r(2r^3\theta_r)=0\), whereas the printed \(D_r[\frac12r^4\theta_r^2]=0\) is a different
equation (e.g. \(\theta=r^{-2}\) satisfies the former, \(D_r(-4)=0\), but not the latter,
\(D_r(2r^{-2})\ne0\)). The factor \(\frac12\) is harmless.
Target: [O95.07.5.02].

### O95-E07.7.01. Arguments of the Lagrangian in rectifying coordinates

Status: Confirmed.
Location: §7.7 (First Integrals), p. 243, proof of Corollary 7.37 (lines 18 and 20).
Printed: "the Lagrangian \(L(x,v_y,v_{yy},\dots)\) is independent of \(v\)"; "the Euler–Lagrange
equations have the form \(D_yP(x,v_y,v_{yy},\dots,v_{n-1})=0\)".
Correct: \(L(y,v_y,v_{yy},\dots)\) and \(D_yP(y,v_y,v_{yy},\dots)=0\).
Evidence: In the rectifying coordinates \((y,v)\) of Theorem 6.19 the independent variable is
\(y\); \(x\) is in general a function of \(y\) and \(v\), so a function of
\((x,v_y,v_{yy},\dots)\) depends on \(v\). The proof ends with the reduced Lagrangian
\(L(y,w,w_y,\dots)-cw\).
Published: [Olver EIS 2nd printing], p. 243, lines 18 and 20.
Target: [O95.07.7.02].

### Conventions and notation (not errata)

- The Euler operator is \(\mathrm E_\alpha=\sum_J(-D)_J\partial/\partial u^\alpha_J\) (no sign
  change); for \(\frac12u_x^2-V(u)\) the Euler–Lagrange expression is \(-u_{xx}-V'(u)\).
- "Nonsingular" for a scalar \(n\)-th order Lagrangian means \(\partial^2L/\partial u_n^2\ne0\).
  The classification theorems 7.30–7.32 are local and over \(\mathbb C\) ("complex point
  transformation"); real forms differ.
- The point-transformation coefficients in (7.14) are \(\alpha=\psi_u\), \(\beta=\psi_x\),
  \(\gamma=\chi_u\), \(\delta=\chi_x\), so \(\bar p=(\alpha p+\beta)/(\gamma p+\delta)\).
- In Lemma 7.16, "Lagrangian form of degree \(n\)" means a Lagrangian of order \(n\).

## Chapter 8. Equivalence of Coframes

### O95-E08.5.01. Maurer–Cartan coframe of \(A(1)\) in Example 8.17

Status: Confirmed.
Location: §8.5 (The Classifying Manifolds), p. 269, Example 8.17, last paragraph.
Printed: the map \(a=1/(x+y)\), \(b=(x-y)/(x+y)\) "maps the coframe (8.27) to the Maurer–Cartan
coframe \(\hat\alpha^1=\frac1{2\lambda}(-\alpha^1+\alpha^2)\),
\(\hat\alpha^2=-\frac1{2\mu}(\alpha^1+\alpha^2)\)".
Correct: \(\hat\alpha^1=\frac\lambda2(-\alpha^1+\alpha^2)\),
\(\hat\alpha^2=-\frac\mu2(\alpha^1+\alpha^2)\).
Evidence: Pulling back \(\alpha^1=da/a\), \(\alpha^2=db-(b/a)da\) gives
\(\alpha^1=-(dx+dy)/(x+y)\) and \(\alpha^2=(dx-dy)/(x+y)\), so
\(-\alpha^1+\alpha^2=2\,dx/(x+y)\) and \(\alpha^1+\alpha^2=-2\,dy/(x+y)\). The printed forms pull back
to \(dx/(\lambda(x+y))\) and \(dy/(\mu(x+y))\), which equal \(\theta^1=\lambda\,dx/(x+y)\),
\(\theta^2=\mu\,dy/(x+y)\) only if \(\lambda^2=\mu^2=1\). With the corrected coefficients the
structure constants are those stated, \(C^1_{12}=-1/\mu\), \(C^2_{12}=1/\lambda\)
(\(J=1/\mu\), \(K=-1/\lambda\)).
Target: [O95.08.5.04].

### O95-E08.7.01. Rank of the structure invariants as a matrix rank

Status: Confirmed.
Location: §8.7 (Remarks and Extensions), p. 278, paragraph before (8.39), and (8.39).
Printed: "\(\rho_s\) equals the rank of the \(\frac12m^2(m-1)\times(\binom{m+s}{s}-1)\) matrix
\(\widetilde Z^{(s)}\) whose entries are the derived invariants \(T_\sigma\),
\(\sigma=(i,j,k,l_1,\dots,l_r)\), of orders \(1\le r\le s+1\); here \((i,j,k)\) labels the row and
\((l_1,\dots,l_r)\) the column", hence \(\mathcal C^{(s)}\subset\{\mathrm{rank}\,\widetilde
Z^{(s)}=\rho_s\}\).
Correct: \(\rho_s\) is the rank of the \(q_s(m)\times m\) matrix \((T_{\sigma,l})\) whose rows are
indexed by the structure invariants \(\sigma\) of order \(\le s\) and whose columns are indexed by
the last derivative index \(l\) (the coframe expression of the Jacobian of \(\mathbf T^{(s)}\)).
For \(s=0\) the printed statement agrees with this.
Evidence: The number of columns \((l_1,\dots,l_r)\), \(1\le r\le s+1\), nondecreasing, is
\(\binom{m+s+1}{s+1}-1\), not \(\binom{m+s}{s}-1\) (for \(s=0\) the latter is \(0\)). More
seriously, the printed matrix has the wrong rank. Take on \(\{x+y>0\}\subset\mathbb R^2\) the coframe
\(\theta^1=e^{-(x+y)}dx\), \(\theta^2=\sqrt{2(1-e^{-(x+y)})}\,dy\). Then \(J=1/D\),
\(K=J^2\), \(D=\sqrt{2(1-e^{-(x+y)})}\), and all invariants are functions of \(x+y\), so
\(\rho_0=\rho_1=1\). The printed \(2\times5\) matrix with rows
\((J_1,J_2,J_{11},J_{12},J_{22})\) and \((K_1,\dots,K_{22})\) has rank \(2\): with \(K=J^2\), the
second row minus \(2J\) times the first is \((0,0,2J_1^2,2J_1J_2,2J_2^2)\ne0\) (at
\((x,y)=(\frac12,\frac13)\) the rank is \(2\) numerically), whereas the \(6\times2\) Jacobian
matrix of \((J,K,J_1,J_2,K_1,K_2)\) has rank \(1\).
Target: [O95.08.7.02].

### Conventions and notation (not errata)

- Structure functions: \(d\theta^i=\sum_{j<k}T^i_{jk}\theta^j\wedge\theta^k\); then
  \([\partial_{\theta^j},\partial_{\theta^k}]=-\sum_iT^i_{jk}\partial_{\theta^i}\) and
  \(T^i_{jk}=-C^i_{jk}\) for right-invariant Maurer–Cartan forms (the source notes the sign change).
  The wedge product is the determinant without factorial factor (Chapter 1 convention).
- Higher coframe derivatives are composed from the left, (8.18).
- "Overlap" of classifying manifolds is in the sense of Definition 1.19 (agreement on open
  pieces), not equality.
- Example 8.23 asserts a reflection symmetry \((x,y)\mapsto(-x,-y)\) of (8.28) for odd \(n\); this
  map does not preserve the domain \(\{x+y>0\}\) of Example 8.12 and is a symmetry of the coframe
  on \(\{x+y\ne0\}\); recorded in the synopsis, not as an erratum.

## Chapter 9. Formulation of Equivalence Problems

Checked, with no further errata: the transformation rules and invariant
combination of Example 9.9; the normalizations (9.42)–(9.46) and the structure equations
(9.47)–(9.48) of Example 9.13 (verified for general \(L(x,u,p)\)); the structure groups (9.23),
(9.26) and \(\widehat G_p\) (closure under multiplication); (9.17)–(9.18).

### O95-E09.3.01. Fiber-preserving subgroup and symmetric form in Example 9.9

Status: Confirmed.
Location: §9.3 (Normalization), p. 293, Example 9.9, line 7, (9.30) and (9.32).
Printed: "The Cartan formulation is given by (9.21), (9.22), with \(a_4=0\)"; the third equation of
(9.30) and of (9.32) is \(\bar a_6\,\omega^3=a_6\,\omega^3\).
Correct: \(a_4=a_5=0\); \(\bar a_6\,\bar\omega^3=a_6\,\omega^3\).
Evidence: By (9.22), \(\theta^3=a_4\omega^1+a_5\omega^2+a_6\omega^3\) with \(\omega^3=dx\); a
fiber-preserving map \(\bar x=\varphi(x)\) has \(d\bar x=\varphi_x\,dx\), so \(a_4=a_5=0\), as the
third equation of (9.30) and p. 349 (the subgroup \(G_f\)) have it. The symmetric form
\(\bar g\bar\omega=g\omega\) has the barred coframe on the left, as in the first two equations,
and \(\bar\omega^3=\varphi_x\omega^3\) gives the stated rule \(\bar a_6\varphi_x=a_6\).
Published: [Olver EIS 2nd printing], p. 293, line 7, and p. 293, (9.30) & (9.32) (two items).
Target: [O95.09.3.02].

### Conventions and notation (not errata)

- Pull-backs are omitted: \(\bar\omega=g\omega\) means \(\Phi^*\bar\omega=g(x)\omega\).
- Coframes are column vectors and structure groups act by left multiplication, so the structure
  groups (9.23), (9.26) are lower triangular.
- The rank of a two-form is half the rank of its coefficient matrix (Chapter 1 convention), so a
  rank \(r\) two-form leads to an \(Sp(2r)\)-valued problem.

## Chapter 10. Cartan's Equivalence Method

### O95-E10.2.01. Sign of the absorption equations

Status: Confirmed.
Location: §10.2 (Absorption and Normalization), p. 309, (10.14).
Printed: \(\sum_\kappa A^i_{j\kappa}z^\kappa_k-A^i_{k\kappa}z^\kappa_j=-T^i_{jk}\).
Correct: \(\sum_\kappa A^i_{k\kappa}z^\kappa_j-A^i_{j\kappa}z^\kappa_k=-T^i_{jk}\), i.e.
\(B^i_{jk}[z]=-T^i_{jk}\).
Evidence: By (10.9), \(B^i_{jk}[z]=\sum_\kappa(A^i_{k\kappa}z^\kappa_j-A^i_{j\kappa}z^\kappa_k)\), and
(10.9) itself follows from substituting \(\alpha^\kappa=\sum_kz^\kappa_k\theta^k\) into
\(\sum A^i_{j\kappa}\alpha^\kappa\wedge\theta^j\). Absorption requires \(B[z]+T=0\), which the text
states as \(\mathbf B[z]=-\mathbf T\) immediately before (10.14); the printed left side of (10.14) is
\(-B^i_{jk}[z]\).
Target: [O95.10.2.01].

### O95-E10.2.02. Summation range in the absorbed Maurer–Cartan forms

Status: Confirmed.
Location: §10.2 (Absorption and Normalization), p. 309, (10.12).
Printed: \(\pi^\kappa=\alpha^\kappa-\sum_{i=1}^{p}z^\kappa_i\theta^i\).
Correct: \(\pi^\kappa=\alpha^\kappa-\sum_{i=1}^{m}z^\kappa_i\theta^i\).
Evidence: The index \(i\) runs over the \(m\) lifted coframe elements \(\theta^1,\dots,\theta^m\), as
in (10.7) (with the summation corrected in [O95-E10.2.03]) and (10.13); \(p\) is not defined in
this context.
Published: [Olver EIS 2nd printing], p. 309, (10.12).
Target: [O95.10.2.01].

### O95-E10.2.03. Summation index in the reduced Maurer–Cartan forms (10.7)

Status: Confirmed.
Location: §10.2 (Absorption and Normalization), p. 307, line 13 and (10.7).
Printed: \(\widetilde\alpha^\kappa=\sum_kz^\kappa_j(x)\,\theta^j\) (line 13);
\(\alpha^\kappa\mapsto\sum_{k=1}^rz^\kappa_j\,\theta^j\) (10.7).
Correct: \(\widetilde\alpha^\kappa=\sum_jz^\kappa_j(x)\,\theta^j\);
\(\alpha^\kappa\mapsto\sum_{j=1}^mz^\kappa_j\,\theta^j\).
Evidence: The summand depends on \(j\), not \(k\); \(j\) runs over the \(m\) lifted coframe
elements, while \(r\) counts the Maurer–Cartan forms \(\alpha^1,\dots,\alpha^r\) (cf. (10.9)).
(10.8)–(10.9) follow from the corrected sum.
Published: [Olver EIS 2nd printing], p. 307, line 13, and p. 307, (10.7) (two items).
Target: [O95.10.2.01].

### O95-E10.3.01. Sign of the \(p\)-terms in the invariants \(J\) and \(K\) (direct equivalence)

Status: Confirmed.
Location: §10.3 (Equivalence Problems for Differential Operators), pp. 316–317, (10.30) and
(10.33).
Printed: \(J=\varepsilon_2\sqrt{|u/f|}\big((uf_x+3pf)/(2u)-g\big)\);
\(K=-\frac32fq+\frac34fp^2/u+\frac12p(f_x+g)+u(2ff_{xx}-f_x^2+2f_xg-4fg_x)/(4f)\).
Correct: \(J=\varepsilon_2\sqrt{|u/f|}\big((uf_x-3pf)/(2u)-g\big)\);
\(K=-\frac32fq+\frac34fp^2/u-\frac12p(f_x+g)+u(2ff_{xx}-f_x^2+2f_xg-4fg_x)/(4f)\).
Evidence: For \(f=1\), \(g=h=0\), \(u>0\) the coframe (10.28) is \(\theta^1=u^{-1/2}dx\),
\(\theta^2=(du-p\,dx)/u\), \(\theta^3=u^{-1/2}\{(dp-q\,dx)-(p/u)(du-p\,dx)\}\), and a direct expansion
of \(d\theta^3\) gives the coefficient \(-\frac32pu^{-1/2}\) of \(\theta^1\wedge\theta^3\), whereas the
printed \(J\) is \(+\frac32pu^{-1/2}\). For general \(f,g,h\) (computed with \(f=e^x+2\),
\(g=\sin x\), \(h=x^2\)) the coefficient of \(\theta^1\wedge\theta^3\) is
\(\sqrt{u/f}\,(uf_x-3pf-2ug)/(2u)\), the identity \(dJ=\kappa_1K\theta^1+\frac12J\theta^2-
\frac32\theta^3\) holds for this \(J\), and \(K=\kappa_1\varepsilon_1\sqrt{|fu|}\widehat D_xJ\) then
has \(-\frac12p(f_x+g)\). The corrected \(J\) is also the one for which (10.34) and (10.35) hold: in
\(\partial\widetilde K/\partial\theta^1=\kappa_1b|\widetilde K|^{3/2}-\frac23J\widetilde K\) the
terms \(\sqrt{fu}\,ap\) cancel only with \(-3pf\). The discrepancy does not depend on the signs
\(\varepsilon_1,\varepsilon_2,\kappa_1\).
Target: [O95.10.3.02].

### O95-E10.3.02. Coframe derivative \(\partial/\partial\theta^3\) (direct equivalence)

Status: Confirmed.
Location: §10.3 (Equivalence Problems for Differential Operators), p. 316, (10.31).
Printed: \(\partial F/\partial\theta^3=\varepsilon_2\sqrt{|f/u|}\,(F_p-(g/f)F_q)\).
Correct: \(\partial F/\partial\theta^3=\varepsilon_2\sqrt{|u/f|}\,(F_p-(g/f)F_q)\).
Evidence: The \(dp\)-coefficient of \(\theta^3\) in (10.28) is \(\varepsilon_2\sqrt{|f/u|}\), and no
other coframe element contains \(dp\) except \(\theta^4\); the vector field dual to \(\theta^3\) must
therefore have \(\partial_p\)-component \(\varepsilon_2\sqrt{|u/f|}\). The other three formulas in
(10.31) and (10.32) agree with the inverse of the coframe matrix computed explicitly.
Target: [O95.10.3.02].

### O95-E10.3.03. Misplaced factor \(u\) in the gauge-equivalence normalization

Status: Confirmed.
Location: §10.3 (Equivalence Problems for Differential Operators), p. 319, torsion display, group
normalizations and (10.40).
Printed: \(T^3_{14}=a_3/(a_1fu)\); \(a_1=\varepsilon_1/(u\sqrt{|f|})\), \(a_2=-\varepsilon_2p\sqrt{|f|}\),
\(a_3=\varepsilon_2\sqrt{|f|}\); \(\theta^1=\varepsilon_1dx/(u\sqrt{|f|})\),
\(\theta^3=\varepsilon_2\sqrt{|f|}\{(dp-q\,dx)-(p/u)(du-p\,dx)\}\).
Correct: \(T^3_{14}=a_3u/(a_1f)\); \(a_1=\varepsilon_1/\sqrt{|f|}\), \(a_2=-\varepsilon_2p\sqrt{|f|}/u\),
\(a_3=\varepsilon_2\sqrt{|f|}/u\); \(\theta^1=\varepsilon_1dx/\sqrt{|f|}\),
\(\theta^3=\varepsilon_2(\sqrt{|f|}/u)\{(dp-q\,dx)-(p/u)(du-p\,dx)\}\).
Evidence: With \(\omega^4=dI\), \(I=(fq+gp)/u+h\), one has \(dq=(u/f)\,dI+\dots\), so the
\(\theta^1\wedge\theta^4\) coefficient of \(d\theta^3\ni a_3\,dx\wedge dq\) is \(a_3u/(a_1f)\).
Normalizing \(T^2_{13}=1/(a_1a_3u)=\kappa_1\) and \(T^3_{14}=1\) gives the corrected parameters.
The printed \(\theta^1\) is not closed (\(d(dx/u)\ne0\)), contradicting \(d\theta^1=0\) in (10.41);
with the corrected coframe the structure equations (10.41) hold exactly with \(J\) as in (10.42),
and the coframe derivatives \(\partial/\partial\theta^1=\varepsilon_1\sqrt{|f|}\widehat D_x\),
\(\partial/\partial\theta^3\), \(\partial/\partial\theta^4\) of (10.43) are those of the corrected
coframe. (Computed with \(f=e^x+2\), \(g=\sin x\), \(h=x^2\).)
Target: [O95.10.3.04].

### O95-E10.3.04. Sign of the \(du\)-term of \(\theta^4\) (gauge equivalence)

Status: Confirmed.
Location: §10.3 (Equivalence Problems for Differential Operators), p. 319, (10.40).
Printed: \(\theta^4=\frac fu\,dq+\frac gu\,dp+\frac{fq+gp}{u^2}\,du+\{\frac{f_xq+g_xp}u+h_x\}\,dx\).
Correct: \(\theta^4=dI=\frac fu\,dq+\frac gu\,dp-\frac{fq+gp}{u^2}\,du+\{\frac{f_xq+g_xp}u+h_x\}\,dx\).
Evidence: \(\theta^4=\omega^4=dI\) with \(I=(fq+gp)/u+h\) by (10.39), and
\(\partial I/\partial u=-(fq+gp)/u^2\). With the printed sign \(d\theta^4\ne0\), contradicting (10.41).
Target: [O95.10.3.04].

### O95-E10.3.05. Coframe derivative \(\partial/\partial\theta^2\) and \(R\) (gauge equivalence)

Status: Confirmed.
Location: §10.3 (Equivalence Problems for Differential Operators), p. 320, (10.43)–(10.44).
Printed: \(\partial F/\partial\theta^2=F_u+pF_p-\frac{fq+pg(1-u)}fF_q\);
\(R=\frac{fqp+gp^2}u-(gq+f_xq+g_xp+h_xu)\).
Correct: \(\partial F/\partial\theta^2=uF_u+pF_p+qF_q\);
\(R=\frac1f\Big[\frac{fqp+gp^2}u-(gq+f_xq+g_xp+h_xu)\Big]\).
Evidence: The dual vector field \(e_2\) must annihilate \(\theta^4=dI\); \((u\partial_u+p\partial_p+
q\partial_q)I=0\) because \(I-h\) is homogeneous of degree 0 in \((u,p,q)\), and it satisfies
\(\theta^1(e_2)=\theta^3(e_2)=0\), \(\theta^2(e_2)=1\). The printed field gives
\(e_2(I)=-(fq+gp)/u^2-fq/u+2gp/u\ne0\) in general. Differentiating \((fq+gp)/u+h=\lambda\) and
solving for \(u_{xxx}\) gives the corrected \(R\) (division by \(f\), as in (10.32)). Both formulas
agree with the inverse of the corrected coframe matrix of [O95-E10.3.03].
Target: [O95.10.3.04].

### O95-E10.4.01. Rank zero table: the square root Lagrangian

Status: Confirmed.
Location: §10.4 (Fiber-preserving Equivalence of Scalar Lagrangians), p. 326, table, third row.
Printed: \(\sqrt{u_x+\sigma u^2}\): \(I_2=4\); symmetry generators \(\partial_x\), \(x\partial_x-u\partial_u\),
\(\sigma x^2\partial_x-(2\sigma xu+1)\partial_u\).
Correct: \(I_2=4\sigma\); third generator \(\sigma x^2\partial_x-(2\sigma xu-1)\partial_u\).
Evidence: From (10.59)–(10.60) for \(L=\sqrt{p+\sigma u^2}\): \(I_1=-1\), \(I_2=4\sigma\), \(I_3=0\)
(also \(J_2=4\sigma\) in the point problem, cf. [O95-E10.6.04]). Since \(L\mapsto cL\) scales
\(I_2\) by \(c^{-2}\) and \(u\mapsto\lambda u\) maps \(\sqrt{p+\sigma u^2}\) to
\(\sqrt\lambda\sqrt{\bar p+\lambda\sigma\bar u^2}\), \(4\sigma\) is consistent, while a value
independent of \(\sigma\) is not (for \(\sigma=0\) the row would be \(p^{1/2}\), with \(I_2=0\)).
Solving the variational symmetry condition \(\mathrm{pr}\,\mathbf v(L)+L\,D_x\xi=0\) with
\(\xi=\xi(x)\) quadratic and \(\phi\) affine in \(u\) gives exactly the span of \(\partial_x\),
\(x\partial_x-u\partial_u\), \(\sigma x^2\partial_x-2\sigma xu\partial_u+\partial_u\); for the
printed third generator \(\mathrm{pr}\,\mathbf v(L)+L\,D_x\xi=-2\sigma u/L\ne0\).
Target: [O95.10.4.03].

### O95-E10.6.01. Sign of \(J_1\) in the point-equivalence structure equations

Status: Confirmed.
Location: §10.6 (Lagrangian Equivalence under Point Transformations), p. 330, (10.70).
Printed: \(d\zeta^1=J_1\zeta^1\wedge\zeta^3+\zeta^2\wedge\zeta^3\).
Correct: \(d\zeta^1=-J_1\zeta^1\wedge\zeta^3+\zeta^2\wedge\zeta^3\), with \(J_1\) as in (10.71).
Evidence: For constant \(I_1\) (e.g. \(L=p^\alpha\)), \(\zeta^1=\sqrt{I_1}\theta^1\) and (10.58) give
\(d\zeta^1=\sqrt{I_1}(-I_1\theta^1\wedge\theta^3+\theta^2\wedge\theta^3)=-\frac{I_1+1}{\sqrt{I_1}}
\zeta^1\wedge\zeta^3+\zeta^2\wedge\zeta^3\), and \(J_1=(I_1+1)/\sqrt{I_1}\) by (10.71). The second
Jacobi identity in (10.74), \(\partial J_2/\partial\zeta^3-\partial J_3/\partial\zeta^2+J_1J_2=0\),
follows from \(d^2\zeta^3=0\) only with the corrected sign. Recomputed also for
\(L=e^{xu}p^3+up^2+x\).
Target: [O95.10.6.02].

### O95-E10.6.02. Formula for \(J_2\)

Status: Confirmed.
Location: §10.6 (Lagrangian Equivalence under Point Transformations), p. 330, (10.71).
Printed: \(J_2=\frac12\,\partial I_3/\partial\theta^1+I_2-\frac14I_3^2\).
Correct: \(J_2=\frac12\,\partial I_3/\partial\theta^2+I_2-\frac14I_3^2\).
Evidence: Expanding \(d\zeta^3\) with \(\zeta^3=\sqrt{I_1}(\theta^3-\frac12I_3\theta^1)\),
\(\theta^1\wedge\theta^2=\zeta^1\wedge\zeta^2/\sqrt{I_1}\) and (10.58), the coefficient of
\(\zeta^1\wedge\zeta^2\) is \(I_2+\frac12\partial I_3/\partial\theta^2-\frac14I_3^2\). For
\(L=e^{xu}p^3+up^2+x\) at \((x,u,p)=(0.3,0.7,1.1)\) the structure coefficient is \(0.027885\),
equal to the corrected formula; the printed formula gives \(0.028780\), and only the corrected
\(J_2\) satisfies the Jacobi identity (10.74).
Target: [O95.10.6.02].

### O95-E10.6.03. Coframe derivatives for the point-equivalence coframe

Status: Confirmed.
Location: §10.6 (Lagrangian Equivalence under Point Transformations), p. 331, (10.73).
Printed: \(\partial F/\partial\zeta^1=I_1^{-1/2}(\partial F/\partial\theta^2-\partial F/\partial\theta^1
+\frac12I_3\partial F/\partial\theta^3)\); \(\partial F/\partial\zeta^3=I_1^{-1/2}\partial F/
\partial\theta^2\).
Correct: \(\partial F/\partial\zeta^1=I_1^{-1/2}(\partial F/\partial\theta^1-\partial F/\partial\theta^2
+\frac12I_3\partial F/\partial\theta^3)\); \(\partial F/\partial\zeta^3=I_1^{-1/2}\partial F/
\partial\theta^3\).
Evidence: (10.69) is \(\zeta=M\theta\) with \(M=\begin{pmatrix}r&0&0\\1&1&0\\-\frac12I_3r&0&r
\end{pmatrix}\), \(r=\sqrt{I_1}\); the frame dual to \(\zeta\) is obtained from the columns of
\(M^{-1}=\begin{pmatrix}1/r&0&0\\-1/r&1&0\\I_3/(2r)&0&1/r\end{pmatrix}\), giving the corrected
formulas. With the printed \(\partial/\partial\zeta^3\), \(\zeta^3(\partial/\partial\zeta^3)=0\).
(The formula for \(\partial/\partial\zeta^2\) is correct.)
Target: [O95.10.6.02].

### O95-E10.6.04. Invariant \(J_2\) of the square root Lagrangian

Status: Confirmed.
Location: §10.6 (Lagrangian Equivalence under Point Transformations), p. 332, first paragraph.
Printed: "The square root Lagrangians \(\sqrt{p+\sigma u^2}\) have invariants \(\widehat J=0\),
\(J_2=2\sigma\), \(J_3=0\)".
Correct: \(\widehat J=0\), \(J_2=4\sigma\), \(J_3=0\).
Evidence: Here \(I_1=-1\), \(I_2=4\sigma\), \(I_3=0\) (see [O95-E10.4.01]), so
\(J_2=\frac12\partial I_3/\partial\theta^2+I_2-\frac14I_3^2=4\sigma\). Directly from the coframe
(10.69) with \(\sigma=\frac23\): the coefficient of \(\zeta^1\wedge\zeta^2\) in \(d\zeta^3\) is
\(\frac83\). The conclusion (inequivalence for different \(\sigma\)) is unchanged.
Target: [O95.10.6.03].

### O95-E10.6.05. Closed form of \(\widehat K\)

Status: Confirmed.
Location: §10.6 (Lagrangian Equivalence under Point Transformations), p. 332, (10.75).
Printed: \(\widehat K=\partial J_1/\partial\zeta^3=\sqrt{L/L_{pp}}\,\partial J_1/\partial p=
\dfrac{2L^2L_{pp}L_{pppp}-2LL_pL_{pp}L_{ppp}+6LL_{pp}^3-3L_p^2L_{pp}^2-3L^2L_{ppp}^2}
{2LL_{pp}^3}\).
Correct: the denominator is \(4LL_{pp}^3\).
Evidence: With \(J_1=(LL_{ppp}+3L_pL_{pp})/(2\sqrt{LL_{pp}^3})\),
\(\sqrt{L/L_{pp}}\,\partial J_1/\partial p\) simplifies symbolically (for general \(L(p)\), \(L,L_{pp}>0\))
to the printed numerator over \(4LL_{pp}^3\). Numerically, for \(L=(p^3+2p+5)^{1/3}\) at \(p=0.7\):
\(\sqrt{L/L_{pp}}\,J_1'=-11.539\), printed closed form \(-23.079\). The printed fraction equals
\(\partial\widehat J/\partial\zeta^3\) divided by \(J_1\), i.e. \(2\,\partial J_1/\partial\zeta^3\).
Target: [O95.10.6.03].

### O95-E10.7.01. Sign of \(\widehat K\) in terms of covariants

Status: Confirmed.
Location: §10.7 (Applications to Classical Invariant Theory), p. 334, (10.76).
Printed: \(\widehat K=-\dfrac{n(n-1)}{4(n-2)}\dfrac{FU}{H^3}\).
Correct: \(\widehat K=\dfrac{n(n-1)}{4(n-2)}\dfrac{FU}{H^3}\), with \(\widehat K=\partial J_1/\partial
\zeta^3\) as defined in (10.75).
Evidence: For \(n=3,4,5\) (forms \(p^3+2p+5\), \(p^4+3p^2+p+2\), \(p^5+p^2-p+3\) at \(p=0.7\), where
\(L,L_p,L_{pp}>0\)) the value of \(\sqrt{L/L_{pp}}\,\partial J_1/\partial p\) is \(-11.539\),
\(2.218\), \(-6.781\), and \(\frac{n(n-1)}{4(n-2)}FU/H^3\) takes the same values, while the printed
expression has the opposite sign. \(\widehat K\) does not depend on the branch of the square root
(\(J_1\) and \(\partial/\partial\zeta^3\) change sign together), and \(U=(H,T)^{(1)}\) does not depend
on the sign convention for the first transvectant (it enters twice). The formula for \(\widehat J\)
in (10.76) is correct. Since \(K^*\) is used only up to a constant factor, Theorems 10.10–10.12 are
unaffected.
Target: [O95.10.7.01].

### O95-E10.7.02. Normalization of the Hessian in the quartic formulas and (10.81)

Status: Normalization check.
Location: §10.7 (Applications to Classical Invariant Theory), p. 336, quartic syzygy, the
identity for \(U\), the parametrization of \(J^*,K^*\), and (10.81).
Printed: \(T^2=-\frac{32}9H^3+2^93^2iQ^2H-2^{12}3^4jQ^3\), \(U=2^93^2(108jQ^2-iQH)\),
\(J^*=2^93^2(-72jS^3+iS^2)-\frac{32}9\), \(K^*=2^93^2(108jS^3-iS^2)\); (10.81):
\(QU+T^2+\frac{8(n-2)^2}{(n-1)^2}H^3=0\).
Correct: with \(H=\frac12(F,F)^{(2)}\), \(T=(F,H)^{(1)}\), \(U=(H,T)^{(1)}\) as defined on pp. 333–334
(the normalization in which \(L_{pp}=L^{1-2n}H/(n^2(n-1))\), (10.76) and the cubic relation
\(T^2+H^3+FU=0\) hold): \(T^2=-\frac{16}9H^3+2^{10}3^2iQ^2H-2^{14}3^4jQ^3\),
\(U=2^{10}3^2(216jQ^2-iQH)\), \(J^*=2^{10}3^2(-144jS^3+iS^2)-\frac{16}9\),
\(K^*=2^{10}3^2(216jS^3-iS^2)\), and (10.81) reads \(QU+T^2+\frac{4(n-2)^2}{(n-1)^2}H^3=0\). The
printed quartic formulas and (10.81) are all correct for the Hessian \(H'=\frac12H=
\frac14(F,F)^{(2)}\) (with \(T'=\frac12T\), \(U'=\frac14U\)).
Evidence: For the quartic \(3-p+2p^2+5p^3-2p^4\), solving \(T^2+cH^3=\alpha Q^2H+\beta Q^3\) gives
\(c=\frac{16}9\) uniquely (no solution with \(c=\frac{32}9\)), with \(\alpha,\beta\) matching
\(2^{10}3^2i\), \(-2^{14}3^4j\) for the classical invariants \(i=ae-4bd+3c^2\),
\(j=ace+2bcd-c^3-ad^2-b^2e\) of \(ax^4+4bx^3y+6cx^2y^2+4dxy^3+ey^4\). For \(F=p^n+1\),
\(n=3,4,5,6\), \(FU+T^2+kH^3=0\) holds with \(k=1,\frac{16}9,\frac94,\frac{64}{25}\), i.e.
\(4(n-2)^2/(n-1)^2\). At \(n=3\), the printed (10.81) (\(k=2\)) contradicts \(T^2+H^3+FU=0\),
which (10.79) asserts for every cubic. Whether Chapter 3 ((3.35), (3.47)) normalizes \(H\) as
\(\frac14(F,F)^{(2)}\) should be checked against that chapter.
Target: [O95.10.7.03].

### O95-E10.7.03. Implicit equation of the quartic classifying curve

Status: Confirmed.
Location: §10.7 (Applications to Classical Invariant Theory), p. 336, display after the
parametrization of \(J^*,K^*\).
Printed: \(9j^2(J^*+K^*+\frac{32}9)^3=i^3(J^*-\frac32K^*+\frac{32}9)^2\).
Correct (for the printed parametrization): \(243\,j^2(J^*+\frac23K^*+\frac{32}9)^3=
32\,i^3(J^*+K^*+\frac{32}9)^2\).
Evidence: From the printed parametrization, \(J^*+K^*+\frac{32}9=2^93^2\cdot36jS^3\) and
\(J^*+\frac23K^*+\frac{32}9=2^93^2\cdot\frac13iS^2\); eliminating \(S\) gives the corrected
equation, which vanishes identically in \(S,i,j\) on substitution. On the curve the printed
left side is a multiple of \(j^5S^9\), while the right side is a polynomial in \(S\) with terms of
degrees 4, 5 and 6, so the printed equation does not hold on the curve. The stated conclusions (dependence only on \(j^2/i^3\); a line iff
\(i=0\) or \(j=0\)) hold for the corrected equation.
Target: [O95.10.7.03].

### O95-E10.8.01. Normalization of \(\partial/\partial\theta^1\) (second order Lagrangians)

Status: Confirmed.
Location: §10.8 (Second Order Variational Problems), p. 341, (10.98).
Printed: \(\partial F/\partial\theta^1=\frac1{L_q^3}\big(-L_q\frac{\partial(L,F)}{\partial(u,q)}+
P\frac{\partial(L,F)}{\partial(p,q)}\big)\).
Correct: \(\partial F/\partial\theta^1=\frac1{LL_q^3}\big(-L_q\frac{\partial(L,F)}{\partial(u,q)}+
P\frac{\partial(L,F)}{\partial(p,q)}\big)\).
Evidence: For the printed field \(e_1\), \(e_1(u)=1/L_q\) and \(e_1(x)=0\), so
\(\theta^1(e_1)=LL_q\cdot e_1(u)=L\ne1\) for \(\theta^1=LL_q(du-p\,dx)\). With the factor \(1/L\) the
four fields of (10.98) are exactly dual to the coframe (10.92) (checked for
\(L=2+up+xq+\frac12q^2+\frac13u^2q^3\)).
Target: [O95.10.8.02].

### O95-E10.8.02. Signs in \(I_4\) and \(I_8\)

Status: Confirmed.
Location: §10.8 (Second Order Variational Problems), p. 341, list of invariants after (10.98).
Printed: \(I_4=-\partial(\log|LL_q|)/\partial\theta^4-1=LL_{qq}/L_q^2\);
\(I_8=-\frac1L\partial^2L/\partial\theta^4\partial\theta^3\).
Correct: \(I_4=\partial(\log|LL_q|)/\partial\theta^4-1=LL_{qq}/L_q^2\);
\(I_8=\frac1L\partial^2L/\partial\theta^4\partial\theta^3\).
Evidence: \(\partial/\partial\theta^4=(L/L_q)\partial_q\) gives
\(\partial\log|LL_q|/\partial\theta^4=1+LL_{qq}/L_q^2\), so the printed first expression equals
\(-2-LL_{qq}/L_q^2\), not \(LL_{qq}/L_q^2\); the structure coefficient of \(\theta^1\wedge\theta^4\) in
\(d\theta^1\) is \(-(1+LL_{qq}/L_q^2)\). For \(I_8\): \(dL=(\partial L/\partial\theta^3)\theta^3+
L\theta^4\), and the \(\theta^3\wedge\theta^4\) component of \(d^2L=0\) with \(d\theta^3=-\theta^3
\wedge\theta^4\) and (10.97) gives \(LI_8=\partial^2L/\partial\theta^4\partial\theta^3\); the
\(\theta^1\wedge\theta^3\) and \(\theta^2\wedge\theta^3\) components give the printed \(I_6\), \(I_7\).
Numerically (same \(L\) as in [O95-E10.8.01]) the structure coefficients agree with the corrected
formulas.
Target: [O95.10.8.02].

### O95-E10.8.03. Sign in the modified Euler–Lagrange expression

Status: Confirmed.
Location: §10.8 (Second Order Variational Problems), p. 341, (10.99).
Printed: \(\mathrm E^*(L)=L_u-D_x^*(L_p)-(D_x^*)^2(L_q)\).
Correct: \(\mathrm E^*(L)=L_u-D_x^*(L_p)+(D_x^*)^2(L_q)\), the expression (10.84) with \(r,s\) replaced
by \(R,S\) as the text says; then \(I_5=\mathrm E^*(L)/(L^2L_q)\).
Evidence: For \(L=2+up+xq+\frac12q^2+\frac13u^2q^3\) at \((x,u,p,q)=(\frac15,\frac13,\frac12,\frac27)\)
the coefficient of \(\theta^1\wedge\theta^3\) in \(d\theta^2\) is \(0.125382\); \(\mathrm E^*/(L^2L_q)\)
is \(0.125382\) with \(+(D_x^*)^2L_q\) and \(-0.121300\) with the printed sign.
Target: [O95.10.8.02].

### O95-E10.8.04. Middle expression for \(I_5\)

Status: Open check.
Location: §10.8 (Second Order Variational Problems), p. 341, formula for \(I_5\).
Printed: \(I_5=-\frac1L\frac{\partial}{\partial\theta^3}\big(\frac P{L_q}\big)+
\frac{P^2-PL_q+L_pL_q}{L^2L_q^2}=\frac{\mathrm E^*(L)}{L^2L_q}\).
Correct: not determined; \(I_5=\mathrm E^*(L)/(L^2L_q)\) holds with \(\mathrm E^*\) as corrected in
[O95-E10.8.03].
Evidence: At the point and for the Lagrangian of [O95-E10.8.03] the middle expression evaluates to
\(0.033181\), while the structure coefficient \(I_5\) is \(0.125382\); no choice of signs of the four
terms of the middle expression gives \(0.125382\).
Target: [O95.10.8.02].

### O95-E10.8.05. The invariant that gives the second order Euler–Lagrange equation

Status: Confirmed.
Location: §10.8 (Second Order Variational Problems), p. 341, line −3.
Printed: "Therefore, \(I_4\) provides an 'invariant second order version of the Euler–Lagrange
equation'".
Correct: \(I_5\).
Evidence: By the list of invariants on the same page, \(I_5=\mathrm E^*(L)/(L^2L_q)\) is built from
the modified Euler–Lagrange expression (10.99), while \(I_4=LL_{qq}/L_q^2\) is not.
Published: [Olver EIS 2nd printing], p. 341, line −3.
Target: [O95.10.8.02].

### Conventions and notation (not errata)

- Sections of Chapter 10 are unnumbered in the source; ids use table-of-contents order.
- The rank zero symmetry generators of the table on p. 326 are infinitesimal generators of
  fiber-preserving variational (not divergence) symmetries; \(\partial_x+\alpha\partial_u\) in the
  first row may be replaced by \(\partial_x\).
- In §10.6 the invariants are complex (\(b_5=\sqrt{I_1}\)); \(J_1\), \(J_3\) depend on the branch, while
  \(\widehat J=J_1^2\), \(J_2\) and \(\widehat K\) do not.
- In §10.7, \((F,G)^{(1)}\) for forms of degrees \(m,n\) is computed from the inhomogeneous
  representatives; \(T^2\), \(U\) and all displayed relations are independent of its sign convention.

## Chapter 11. Involution

### O95-E11.5.01. Fourth structure equation of (11.20) mislabelled

Status: Confirmed.
Location: §11.5 (Contact Transformations), p. 361, (11.20), fourth line.
Printed: the third and fourth lines of (11.20) both begin \(d\theta^3=\dots\); the fourth reads
\(d\theta^3=\beta^3\wedge\theta^1+\beta^4\wedge\theta^2+\gamma^3\wedge\theta^3+\gamma^4\wedge\theta^4\).
Correct: the fourth line is \(d\theta^4=\beta^3\wedge\theta^1+\beta^4\wedge\theta^2+\gamma^3\wedge
\theta^3+\gamma^4\wedge\theta^4\).
Evidence: the two printed lines give different expressions for the same \(d\theta^3\), and the
lifted coframe has four elements \(\theta^1,\dots,\theta^4\), so \(d\theta^4\) is otherwise
missing; the corresponding display (11.23) on p. 363 correctly labels the fourth line
\(d\theta^4\).
Target: [O95.11.5.01].

### O95-E11.5.02. Misprint \(\beta^2\wedge\theta^1\) in (11.23)

Status: Confirmed.
Location: §11.5 (Contact Transformations), p. 363, (11.23), third line.
Printed: \(d\theta^3=\beta^1\wedge\theta^1+\beta^2\wedge\theta^1+\gamma^1\wedge\theta^3\).
Correct: \(d\theta^3=\beta^1\wedge\theta^1+\beta^2\wedge\theta^2+\gamma^1\wedge\theta^3\).
Evidence: (11.20) has \(\beta^2\wedge\theta^2\) in \(d\theta^3\), and the normalizations
\(\alpha^2\equiv0\), \(\alpha^4\equiv\gamma^1+\gamma^4\), \(\gamma^2\equiv0\),
\(\alpha^1\equiv2\gamma^1+\gamma^4\) do not affect the \(\beta\)'s. With the corrected line and the
eight forms \(\gamma^1,\gamma^4,\alpha^3,\beta^1,\beta^2,\gamma^3,\beta^3,\beta^4\), the
homogeneous absorption system has a 13-dimensional solution space and the reduced characters are
\(s'=(4,3,1,0)\), as stated in the text (\(4+6+3=13\), involutive). With the printed line, the
same computation gives \(r^{(1)}=14\) and \(s'=(4,2,1,1)\), with \(4+4+3+4=15\ne14\), so the
printed system would not satisfy Cartan's test and would contradict the text's \(r^{(1)}=13\),
\(s'_2=3\).
Target: [O95.11.5.02].

### O95-E11.6.01. Darboux ranks of the three-dimensional canonical forms

Status: Confirmed.
Location: §11.6 (Darboux' Theorem), pp. 365–366, Cases 1–3.
Printed: the canonical forms \(\omega=e^x\,dy+dz\), \(\omega=e^{-x}dy\), \(\omega=dx\) are
called one-forms "of Darboux rank two", "of Darboux rank one" and "of Darboux rank zero".
Correct: by Definition 1.41 (the rank is the largest \(r\) with \(\omega_r\ne0\), where
\(\omega_1=\omega\), \(\omega_2=d\omega\), \(\omega_3=\omega\wedge d\omega\)), the three
forms have rank three, two and one respectively.
Evidence: \(\omega=dx\ne0\) has \(\omega_1\ne0=\omega_2\), so rank one, not zero (rank zero
means \(\omega=0\)); \(\omega=e^{-x}dy\) has \(d\omega=-e^{-x}dx\wedge dy\ne0\),
\(\omega\wedge d\omega=0\), so rank two; \(\omega=e^x\,dy+dz\) has
\(\omega\wedge d\omega=e^x\,dx\wedge dy\wedge dz\ne0\), so rank three. Theorem 1.42 gives
the canonical forms \(dx^1\), \(x^1dx^2\), \(x^1dx^2+dx^3\) for ranks one, two, three, and
Exercise 13.7 (p. 411) uses Definition 1.41 correctly ("Darboux rank at most two" for
\(\omega\wedge d\omega=0\)).
Target: [O95.11.6.02].

### O95-E11.8.01. The torsion coefficients \(S_i\) are not \(\partial T_3/\partial\theta^i\)

Status: Confirmed.
Location: §11.8 (Equivalence of Nonclosed Two-Forms), p. 370, Case 2, line after the display
\(d\theta^3=S_1\theta^1\wedge\theta^3+S_2\theta^2\wedge\theta^3\).
Printed: "contains two essential torsion coefficients: \(S_i=\partial T_3/\partial\theta^i\),
\(i=1,2\)."
Correct: \(S_i=-T_3^{-1}\,\partial T_3/\partial\theta^i\), \(i=1,2\).
Evidence: with \(dT=T_3\theta^3\) and \(dT_3=\sum_i(\partial T_3/\partial\theta^i)\theta^i\), the
identity \(0=d^2T=dT_3\wedge\theta^3+T_3\,d\theta^3\) gives
\(T_3\,d\theta^3=-(\partial T_3/\partial\theta^1)\,\theta^1\wedge\theta^3-(\partial T_3/
\partial\theta^2)\,\theta^2\wedge\theta^3\). The vanishing conditions \(S_1=S_2=0\) used for the
branching are unaffected, and the infinitesimal action \(dS_1\equiv-S_1\alpha^1-S_2\alpha^3\),
\(dS_2\equiv-S_1\alpha^2+S_2\alpha^1\) printed next holds for the corrected \(S_i\) (it follows
from \(d^2\theta^3=0\) alone).
Target: [O95.11.8.04].

### O95-E11.8.02. Sign in the canonical forms (11.33)

Status: Confirmed.
Location: §11.8 (Equivalence of Nonclosed Two-Forms), p. 371, (11.33).
Printed: with \(T=z\), the canonical forms of Case 2a are
\(\omega^1=dx\), \(\omega^2=\exp\big[-\int z\,dz/H(z)\big]dy\), \(\omega^3=dz/H(z)\).
Correct: \(\omega^2=\exp\big[+\int z\,dz/H(z)\big]dy\) (other forms unchanged); then \(T=z\) and
\(T_3=H(T)\).
Evidence: put \(E(z)=\exp[\varepsilon\int z\,dz/H(z)]\), \(\varepsilon=\pm1\), so
\(\Omega=\omega^1\wedge\omega^2=E\,dx\wedge dy\), \(\mathbf v=H(z)\partial_z\) (from
\(\langle\omega^3;\mathbf v\rangle=1\)), and
\(d\Omega=E'(z)\,dz\wedge dx\wedge dy=\varepsilon\,\frac{z}{H}E\,dx\wedge dy\wedge dz=
\varepsilon z\,\omega^1\wedge\omega^2\wedge\omega^3\). Hence \(T=\varepsilon z\). The printed
choice \(\varepsilon=-1\) gives \(T=-z\) and \(T_3=-H(z)=-H(-T)\), contradicting "\(T=z\)" and the
classifying relation \(T_3=H(T)\); \(\varepsilon=+1\) gives \(T=z\), \(dT=dz=H\,\omega^3\), so
\(T_1=T_2=0\), \(T_3=H(T)\), and \(d\omega^3=0\) (\(S_1=S_2=0\)) as required.
Target: [O95.11.8.04].

### Conventions and notation (not errata)

- The source writes "degree of indeterminancy" for \(r^{(1)}\); the synopsis keeps this term.
- Structure equations are written \(d\theta^i=\sum A^i_{j\kappa}\alpha^\kappa\wedge\theta^j+\dots\)
  with right-invariant Maurer–Cartan forms \(\alpha^\kappa\); the modified forms \(\pi^\kappa\) of
  the absorbed equations are redefined from display to display (stated in the source, p. 358).
- "Depends on \(s'_k\) arbitrary functions of \(k\) variables" is a statement of functional
  generality via Cartan–Kähler; compatible Cauchy data in fewer variables are also involved.
- Generic (open-set) hypotheses such as \(S\ne0\) or \((T_1,T_2)\ne0\) are stated once in a
  footnote (p. 365) and apply to all branches.

## Chapter 12. Prolongation of Equivalence Problems

### O95-E12.2.01. Isometry group of the hyperbolic plane

Status: Confirmed.
Location: §12.2 (Equivalence of Surfaces), p. 381, Proposition 12.3.
Printed: for constant curvature \(\kappa<0\) "the connected component of the symmetry group has
the structure of \(SL(2,\mathbb R)\)".
Correct: its Lie algebra is \(\mathfrak{sl}(2,\mathbb R)\); for the hyperbolic plane the
connected isometry group is \(PSL(2,\mathbb R)=SL(2,\mathbb R)/\{\pm I\}\), and for a general
surface of constant negative curvature only the local group (up to local isomorphism) is
determined.
Evidence: \(SL(2,\mathbb R)\) acts on the upper half-plane by \(z\mapsto(az+b)/(cz+d)\), and
\(-I\) acts trivially, so the effective connected isometry group is \(PSL(2,\mathbb R)\), which
is not isomorphic to \(SL(2,\mathbb R)\) (the latter has centre \(\{\pm I\}\), the former trivial
centre). The Cartan method used in the proof only yields the Maurer–Cartan structure equations,
i.e. the local group.
Target: [O95.12.2.05].

### O95-E12.2.02. The mixed second derived invariant \(\hat\kappa_{12}\) in (12.27)

Status: Confirmed.
Location: §12.2 (Equivalence of Surfaces), p. 382, (12.27), second line.
Printed: \(\hat\kappa_{12}=\sin t\cos t\,\tilde\kappa_{11}-2\sin t\cos t\,\tilde\kappa_{12}+\sin t
\cos t\,\tilde\kappa_{22}\).
Correct: \(\hat\kappa_{12}=\sin t\cos t\,(\tilde\kappa_{11}-\tilde\kappa_{22})+(\cos^2t-\sin^2t)
\,\tilde\kappa_{12}\).
Evidence: at \(t=0\) the lifted coframe is \(\boldsymbol\theta=\boldsymbol\omega\) and
\(\partial/\partial\theta^i=\partial/\partial\omega^i+(\cdot)\partial_t\) with the coefficients
of (12.25), so \(\hat\kappa_{12}|_{t=0}=\mathbf v_1\mathbf v_2\kappa+J\kappa_1=\tilde\kappa_{12}\),
whereas the printed expression vanishes at \(t=0\). Applying the first-order operators of (12.25)
to \(\hat\kappa_2=\sin t\,\kappa_1+\cos t\,\kappa_2\) gives the corrected formula, i.e.
\((\hat\kappa_{ij})=R(\tilde\kappa_{ij})R^T\) with
\(R=\begin{pmatrix}\cos t&-\sin t\\ \sin t&\cos t\end{pmatrix}\), consistent with the printed
\(\hat\kappa_{11}\) and \(\hat\kappa_{22}\).
Target: [O95.12.2.06].

### O95-E12.2.03. The invariant \(\sigma_1\) in (12.28)

Status: Confirmed.
Location: §12.2 (Equivalence of Surfaces), p. 383, (12.28), first line.
Printed: \(\sigma_1=\kappa_1\kappa_2(\tilde\kappa_{11}-\tilde\kappa_{22})+2(\kappa_1^2-\kappa_2^2)
\tilde\kappa_{12}\).
Correct: \(\sigma_1=\kappa_1\kappa_2(\tilde\kappa_{11}-\tilde\kappa_{22})+(\kappa_2^2-\kappa_1^2)
\tilde\kappa_{12}\), i.e. \(\sigma_1=(\kappa^\perp)^T\tilde\kappa\,\kappa\) with
\(\kappa=(\kappa_1,\kappa_2)\), \(\kappa^\perp=(\kappa_2,-\kappa_1)\); with this \(\sigma_1\),
(12.31) \(J^*=-\sigma_1/\rho^3\) holds as printed.
Evidence: \(\sigma_1\) must be unchanged when \((\kappa_1,\kappa_2)\) and \((\tilde\kappa_{ij})\)
are rotated together (it arises by eliminating \(t\)). Take \(\kappa=(1,0)\),
\(\tilde\kappa=\begin{pmatrix}0&1\\1&0\end{pmatrix}\); rotating by \(45^\circ\) gives
\(\kappa=(1,1)/\sqrt2\), \(\tilde\kappa=\mathrm{diag}(-1,1)\). The printed expression takes the
values \(2\) and \(-1\), the corrected one \(-1\) and \(-1\). Numerically, for
\(ds^2=dx^2+h^2dy^2\), \(h=2+x^3y+xy^2+y\), at \((x,y)=(0.3,0.7)\) the adapted coframe (12.30) has
\(J^*=-0.319759\); the corrected \(\sigma_1/\rho^3=0.319759\), the printed one gives
\(-0.396936\); \(K^*=\sigma_2/\rho^3=-0.114052\) as printed.
Target: [O95.12.2.06], [O95.12.2.08].

### O95-E12.2.04. Metric of a surface of revolution

Status: Confirmed.
Location: §12.2 (Equivalence of Surfaces), p. 383, proof of Theorem 12.6.
Printed: for \(x=r\cos v\), \(y=r\sin v\), \(z=f(r)\): \(ds^2=r^2\,dr^2+\{1+f'(r)^2\}\,dv^2\).
Correct: \(ds^2=\{1+f'(r)^2\}\,dr^2+r^2\,dv^2\).
Evidence: \(dx^2+dy^2+dz^2=dr^2+r^2dv^2+f'(r)^2dr^2\). The corrected form is the one used in the
next lines (\(u=\int\sqrt{1+f'^2}\,dr\), \(r=h(u)\), \(ds^2=du^2+h(u)^2dv^2\)).
Target: [O95.12.2.07].

### O95-E12.4.01. Sign and index in the orthogonal absorption equations (12.35)–(12.36)

Status: Confirmed.
Location: §12.4 (Equivalence of Riemannian Manifolds), pp. 387–388, (12.35)–(12.36).
Printed: \(z^i_{kj}-z^i_{jk}=T^i_{jk}\) (12.35), and hence
\(-2z^i_{jk}=T^i_{jk}+T^j_{ik}+T^k_{ji}\) (12.36).
Correct: with \(\pi=\rho-z\boldsymbol\theta\) as in (12.2), (12.44), the absorption equations are
\(z^i_{jk}-z^i_{kj}=T^i_{jk}\) (the sign convention of (11.7)), with unique skew solution
\(2z^i_{jk}=T^i_{jk}+T^j_{ki}+T^k_{ji}\).
Evidence: substituting \(\rho^i_j=\pi^i_j+\sum_kz^i_{jk}\theta^k\) into (12.34) gives
\(d\theta^i=\sum_j\pi^i_j\wedge\theta^j+\sum_{j<k}(z^i_{kj}-z^i_{jk}+T^i_{jk})\theta^j\wedge
\theta^k\), so absorption requires \(z^i_{jk}-z^i_{kj}=T^i_{jk}\), as in (11.7) with
\(A^i_{j\kappa}\) the identity. Independently of the sign, (12.36) does not follow from either
form of (12.35): for a random tensor \(T^i_{jk}\) skew in \(j,k\) (\(m=4\)), the unique solution of
the printed (12.35) with \(z^i_{jk}=-z^j_{ik}\) satisfies \(-2z^i_{jk}=T^i_{jk}+T^j_{ki}+
T^k_{ji}\) to machine precision, while the printed right side \(T^i_{jk}+T^j_{ik}+T^k_{ji}\)
differs from \(-2z^i_{jk}\) by up to \(5.1\) in the same example. The index pattern
\(T^j_{ki}\) is forced: \(T^i_{jk}+T^j_{ki}+T^k_{ji}\) is skew in \(i,j\), as \(z^i_{jk}\) must be,
whereas \(T^i_{jk}+T^j_{ik}+T^k_{ji}\) is not.
Target: [O95.12.4.01].

### O95-E12.4.02. The connection coefficients \(\hat\Gamma\) in (12.41)

Status: Confirmed.
Location: §12.4 (Equivalence of Riemannian Manifolds), pp. 388–389, (12.41)–(12.42).
Printed: \(z^i_{jk}=-\sum r^i_lr^j_pr^k_q\hat\Gamma^l_{qp}\) with
\(\hat\Gamma^l_{pq}=\frac12(K^l_{pq}+K^p_{lq}+K^q_{lp})\), and "the \(\hat\Gamma\)'s are just the
components of the symmetric Levi-Civita connection", \(\hat\nabla_k(\mathbf v_j)=\sum_i
\hat\Gamma^i_{jk}\mathbf v_i\) (12.42).
Correct: the Levi-Civita coefficients in the convention (12.42) are
\(\hat\Gamma^l_{pq}=\frac12(K^l_{pq}+K^p_{ql}+K^q_{pl})\), and then
\(z^i_{jk}=\sum r^i_lr^j_pr^k_q\hat\Gamma^l_{pq}\) (equivalently, the printed formula for \(z\) is
right numerically, but its \(\hat\Gamma\) equals \(-\hat\Gamma_{\rm LC}{}^l_{qp}\)).
Evidence: in an orthonormal frame, metric compatibility of \(\hat\nabla\) in the convention
(12.42) requires \(\hat\Gamma^i_{jk}=-\hat\Gamma^j_{ik}\). The printed
\(\hat\Gamma^l_{pq}+\hat\Gamma^p_{lq}=K^l_{pq}+K^p_{lq}\), which is not zero in general (e.g.
\(m=2\), \(d\omega^1=J\omega^1\wedge\omega^2\): \(\hat\Gamma^1_{12}+\hat\Gamma^1_{12}=2K^1_{12}
=2J\)); the corrected \(\hat\Gamma\) satisfies the skew-symmetry and
\(\hat\Gamma^i_{jk}-\hat\Gamma^i_{kj}=K^i_{jk}\) (torsion-freeness (12.43)), and is given by the
Koszul formula \(2\langle\hat\nabla_{\mathbf v_k}\mathbf v_j,\mathbf v_i\rangle=\langle[\mathbf
v_k,\mathbf v_j],\mathbf v_i\rangle-\langle[\mathbf v_k,\mathbf v_i],\mathbf v_j\rangle-\langle
[\mathbf v_j,\mathbf v_i],\mathbf v_k\rangle\) with (12.39). The curvature formula (12.48) is
correct for the corrected \(\hat\Gamma\) (it is \(R(\mathbf v_k,\mathbf v_l)\mathbf v_j\) in the
convention (12.42)). Numerically (\(m=4\), random \(K\)), the solution \(z\) of the corrected
(12.35) agrees with \(\sum r r r\hat\Gamma^l_{pq}\) (corrected \(\hat\Gamma\), \(R=I\)) to
\(10^{-15}\).
Target: [O95.12.4.02].

### O95-E12.4.03. Constant sectional, not scalar, curvature in Theorem 12.12

Status: Confirmed.
Location: §12.4 (Equivalence of Riemannian Manifolds), p. 393, line 2 and Theorem 12.12.
Printed: \(R^i_{jkl}=a(\delta^i_k\delta_{lj}-\delta^i_l\delta_{kj})\) "means that the manifold
has constant scalar curvature"; the isometry group "has maximal dimension \(\frac12m(m+1)\) if
and only if \(M\) has constant scalar curvature".
Correct: maximal dimension holds if and only if \(M\) has constant sectional curvature
(equivalently \(R^i_{jkl}=a(\delta^i_k\delta_{lj}-\delta^i_l\delta_{kj})\) with \(a\) constant).
Evidence: \(M=S^2\times\mathbb R\) with the product of the unit round metric and the line has
constant scalar curvature \(2\), but sectional curvature \(1\) on planes tangent to \(S^2\) and
\(0\) on mixed planes; its isometry group \(O(3)\times E(1)\) has dimension \(3+1=4<6=
\frac12\cdot3\cdot4\). For \(m=2\) the two notions coincide.
Target: [O95.12.4.08].

### O95-E12.4.04. Isometry group of hyperbolic space

Status: Confirmed.
Location: §12.4 (Equivalence of Riemannian Manifolds), p. 393, Theorem 12.12.
Printed: hyperbolic space \(H^m\) "with isometry group \(O(m,1)\)".
Correct: the isometry group of \(H^m\) is \(O^+(m,1)\), the index-two subgroup of \(O(m,1)\)
preserving the upper sheet of the hyperboloid \(x_0^2-x_1^2-\dots-x_m^2=1\) (isomorphic to
\(O(m,1)/\{\pm I\}\)); its Lie algebra is \(\mathfrak{so}(m,1)\).
Evidence: \(-I\in O(m,1)\) interchanges the two sheets of the hyperboloid, so \(O(m,1)\) does not
act on the hyperboloid model \(H^m\) (upper sheet); the elements preserving \(H^m\) form
\(O^+(m,1)\), which acts effectively and transitively by isometries.
Target: [O95.12.4.08].

### O95-E12.5.01. Sign of the particular solution in (12.52)

Status: Confirmed.
Location: §12.5 (The Indeterminate Case), pp. 394–395, (12.51)–(12.53).
Printed: \(\boldsymbol\pi=\boldsymbol\alpha-(K[w]+S)\boldsymbol\theta\) (12.51), but
\(\boldsymbol\varpi=\boldsymbol\alpha+S\boldsymbol\theta\) "obtained ... by setting all the free
variables to zero" (12.52), and \(\boldsymbol\pi=\boldsymbol\varpi+K[w]\boldsymbol\theta\).
Correct: \(\boldsymbol\varpi=\boldsymbol\alpha-S\boldsymbol\theta\) and
\(\boldsymbol\pi=\boldsymbol\varpi-K[w]\boldsymbol\theta\) (the sign of \(K[w]\) is immaterial,
since \(w\) ranges over a vector space; the group (12.53) then has \(-K[w]\) or, after
\(w\mapsto-w\), \(K[w]\) in its lower block).
Evidence: setting \(w=0\) in (12.51) gives \(\boldsymbol\alpha-S\boldsymbol\theta\); this sign
agrees with (12.2) and with the worked example (12.60), e.g.
\(\varpi^1=\alpha^1-(a_2/a_1)\theta^3\).
Published: [Olver EIS 2nd printing], p. 395, (12.52), changes \(+S\boldsymbol\theta\) to
\(-S\boldsymbol\theta\); it leaves \(\boldsymbol\pi=\boldsymbol\varpi+K[w]\boldsymbol\theta\),
whose sign is immaterial.
Target: [O95.12.5.01].

### O95-E12.6.01. Missing sign in the invariant \(K_2\) of (12.73)

Status: Confirmed.
Location: §12.6 (Second Order Ordinary Differential Equations), p. 406, (12.73), \(K_2\).
Printed: numerator
\(\hat D_x^2Q_{pp}-4\hat D_xQ_{up}-Q_p\hat D_xQ_{pp}\,6Q_{uu}-3Q_uQ_{pp}+4Q_pQ_{up}\) (no operator
between \(Q_p\hat D_xQ_{pp}\) and \(6Q_{uu}\)).
Correct: \(\hat D_x^2Q_{pp}-4\hat D_xQ_{up}-Q_p\hat D_xQ_{pp}+6Q_{uu}-3Q_uQ_{pp}+4Q_pQ_{up}\).
Evidence: \(K_2\) must vanish for every equation point-equivalent to \(u_{xx}=0\). For the image of
\(u_{xx}=0\) under \(x=X+U^2/3+XU\), \(u=U+X^2-U^3/5\), the numerator with \(+6Q_{uu}\) vanishes
(\(\approx10^{-14}\) at two test points), while with \(-6Q_{uu}\) it takes the values \(627.68\)
and \(-15.00\). With \(+6Q_{uu}\), \(u_{xx}=3uu_x-u^3\) (linearizable, Example 12.20) gives \(0\),
and \(u_{xx}=u^2\) (not linearizable, Exercise 12.23) gives \(12\).
Published: [Olver EIS 2nd printing], p. 406, (12.73).
Target: [O95.12.6.05].

### Conventions and notation (not errata)

- The source writes \(\partial^2\kappa/\partial\omega^1\partial\omega^2\) for
  \(\mathbf v_1(\mathbf v_2\kappa)\); the frame derivatives do not commute, and
  \(\mathbf v_1\mathbf v_2-\mathbf v_2\mathbf v_1=-J\mathbf v_1-K\mathbf v_2\).
- In (12.45) the source writes the curvature term as \(\sum_kS^i_{jkl}\theta^k\wedge\theta^l\);
  the identification \(S=\) (rotated) \(\hat R\) holds with the sum over \(k<l\).
- Prolonged structure groups are written as block lower-triangular subgroups of
  \(GL(m+r)\); their sign conventions for \(K[w]\) are immaterial.
- Theorem 12.19 (i) says the eight-dimensional point symmetry group is "necessarily isomorphic
  to \(SL(3)\)": as a local group this means Lie algebra \(\mathfrak{sl}(3,\mathbb R)\); the global
  projective group \(PGL(3,\mathbb R)\) is in fact isomorphic to \(SL(3,\mathbb R)\), so no
  correction is needed.
- The source's "symmetric connection" means torsion-free connection.

## Chapter 13. Differential Systems

### O95-E13.1.01. Sign in the integral-surface equations of Example 13.5

Status: Confirmed.
Location: §13.1 (Differential Systems and Ideals), p. 411, Example 13.5, displayed system.
Printed: the graph of \(z=\varphi(x,y)\) is integral for \(\omega=a\,dx+b\,dy+c\,dz\) iff
\(c\,\varphi_x=a\), \(c\,\varphi_y=b\).
Correct: \(c\,\varphi_x=-a\), \(c\,\varphi_y=-b\) (all coefficients evaluated at
\((x,y,\varphi(x,y))\)).
Evidence: the pullback of \(\omega\) to the graph is \((a+c\varphi_x)dx+(b+c\varphi_y)dy\). For
\(\omega=dz-y\,dx\) (\(a=-y\), \(b=0\), \(c=1\)) the integral surfaces \(z=xy+\mathrm{const}\)
have \(\varphi_x=y=-a\). The stated compatibility condition \((a/c)_y=(b/c)_x\) is unaffected by
the sign (it must be read with total derivatives along the graph).
Published: [Olver EIS 2nd printing], p. 411, lines 12–13.
Target: [O95.13.1.03].

### O95-E13.2.01. Sign of \(d\theta_i\) for contact forms

Status: Confirmed.
Location: §13.2 (Equivalence of Differential Systems), p. 416, line 13.
Printed: \(d\theta_i=\theta_{i+1}\wedge dx\) for \(\theta_i=du_i-u_{i+1}dx\).
Correct: \(d\theta_i=-du_{i+1}\wedge dx=dx\wedge\theta_{i+1}=-\theta_{i+1}\wedge dx\).
Evidence: \(d\theta_i=-du_{i+1}\wedge dx\) and \(\theta_{i+1}\wedge dx=du_{i+1}\wedge dx\). The
conclusion \(d\theta_i\in\mathcal I_n\) iff \(i\le n-2\) is unaffected.
Target: [O95.13.2.02].

### O95-E13.2.02. The derived contact ideal is larger than \(\mathcal I_{n-1}\)

Status: Confirmed.
Location: §13.2 (Equivalence of Differential Systems), p. 416, lines 11–15.
Printed: "the derived contact ideal can be identified with the \((n-1)\)st order contact ideal:
\(\delta\mathcal I_n=\mathcal I_{n-1}\)", and \(\delta^k\mathcal I_n=\mathcal I_{n-k}\).
Correct: with Definition 13.16, \(\delta\mathcal I_n\supsetneq\mathcal I_{n-1}\) in general; what
holds is \((\delta\mathcal I_n)^{(1)}=\mathcal I_{n-1}^{(1)}\) (the derived Pfaffian system), and
the ideal generated by the one-forms of \(\delta^k\mathcal I_n\) is \(\mathcal I_{n-k}\). The
invariance argument for Bäcklund's theorem goes through with these one-form parts, which are
also preserved by Proposition 13.17.
Evidence: \(\Omega=dx\wedge\theta_{n-1}\in\mathcal I_n\) and
\(d\Omega=-dx\wedge dx\wedge du_n=0\in\mathcal I_n\), so \(\Omega\in\delta\mathcal I_n\); but
modulo \(\theta_0,\dots,\theta_{n-2}\), \(\Omega\equiv dx\wedge du_{n-1}\ne0\), so
\(\Omega\notin\mathcal I_{n-1}\). Similarly \(\theta_{n-1}\wedge du_n\in\delta\mathcal I_n\).
Target: [O95.13.2.02].

### O95-E13.3.01. Signs in Example 13.23

Status: Confirmed.
Location: §13.3 (Vector Field Systems), p. 419, Example 13.23.
Printed: \(d\omega^1=(dy-2z\,dx)\wedge dz=\frac{dz}{1+z^2}\wedge(\omega^2-2z\omega^1)\),
\(d\omega^2=(dx+2z\,dy)\wedge dz=\frac{dz}{1+z^2}\wedge(\omega^1+2z\omega^2)\).
Correct: \(d\omega^1=-\frac{dz}{1+z^2}\wedge(\omega^2-2z\omega^1)\),
\(d\omega^2=-\frac{dz}{1+z^2}\wedge(\omega^1+2z\omega^2)\) (the first equalities are right).
Evidence: \(dz\wedge(\omega^2-2z\omega^1)=(1+z^2)(dz\wedge dy-2z\,dz\wedge dx)=-(1+z^2)(dy-2z\,dx)
\wedge dz\), and \(dz\wedge(\omega^1+2z\omega^2)=(1+z^2)(dz\wedge dx+2z\,dz\wedge dy)=
-(1+z^2)(dx+2z\,dy)\wedge dz\). The conclusion that the ideal is closed is unaffected.
Target: [O95.13.3.05].

### Conventions and notation (not errata)

- The source's "rank" of an exterior ideal (Definition 13.11) is the dimension of the span of its
  one-forms at a point; the "rank" of a vector field system is \(\dim\mathcal V|_x\); the rank of
  a single one-form is that of Definition 1.41.
- "Simply generated" means generated by one-forms (Pfaffian system).
- The provisional notion "\(n\)-integrable" (p. 413) is superseded in Chapter 15 by conditions on
  ordinary/regular integral elements.

## Chapter 14. Frobenius' Theorem

### O95-E14.3.01. Indices in the Goursat normal form

Status: Confirmed.
Location: §14.3 (Characteristics and Normal Forms), pp. 430–431, Theorem 14.14, conclusion.
Printed: "there exist local coordinates \(x,u_0,u_1,\dots,u_{m-2}\), such that
\(\omega^i=du_i-u_{i+1}\,dx\)", \(i=1,\dots,m-2\).
Correct: \(\omega^i=du_{i-1}-u_i\,dx\), \(i=1,\dots,m-2\). These are the contact forms
\(\theta_0,\dots,\theta_{m-3}\) of \(J^{m-2}\) in the coordinates \(x,u_0,\dots,u_{m-2}\).
Evidence: for \(i=m-2\) the printed form involves \(u_{m-1}\), which is not among the \(m\)
coordinates. With the correct indices, \(d\omega^i=dx\wedge du_i\equiv-\omega^{i+1}\wedge dx\)
modulo \(\omega^1,\dots,\omega^i\) for \(i\le m-3\), with \(\pi=dx\). Also
\(d\omega^{m-2}=dx\wedge du_{m-2}\not\equiv0\) modulo \(\mathcal I\). These match the hypotheses
(14.17), and the ideal is \(\mathcal I_{m-2}\) on \(J^{m-2}E\).
Target: [O95.14.3.04].

### O95-E14.4.01. Order of vanishing ranks in the example after Definition 14.21

Status: Confirmed.
Location: §14.4 (The Technique of the Graph), p. 436, lines 5–7.
Printed: for \(I(x)=x^n\), "at \(x=0\), \(\rho_s=0\) for \(s<n\)".
Correct: \(\rho_s(0)=0\) for \(s<n-1\) (that is, \(s\le n-2\)), and \(\rho_{n-1}(0)=1\). The
conclusion that the order at \(0\) is unbounded in \(n\) still holds.
Evidence: \(I\) has order \(0\). \(\rho_s(0)\) is the rank at \(0\) of
\(x\mapsto(I,I',\dots,I^{(s)})\). Its differential there is
\((I'(0),\dots,I^{(s+1)}(0))\), which is nonzero iff \(s+1\ge n\), since \(I^{(n)}(0)=n!\) and lower
derivatives vanish. For example, \(n=1\): \(I=x\) has \(\rho_0(0)=1\), but the printed text would
give \(\rho_0(0)=0\).
Target: [O95.14.4.04].

### Conventions and notation (not errata)

- In (14.14), the third characteristic condition is printed as "\(=0\)". It holds only modulo
  \(\theta\) and \(\omega\), as (14.15) shows. This is recorded as a Precise form in O95.14.3.02.
- The proof of Theorem 14.24 (p. 438) refers to "Theorem 14.24" where Theorem 14.18 (the rank zero
  case) is meant. This is a cross-reference slip.
- "Covering map" (p. 441) means a surjective local diffeomorphism. It is not required to be a
  covering in the topological sense.
- Theorem 14.15 excludes only \(q=2\). The case \(q=1\) (Darboux's contact normal form) is
  included.
- \(\delta\mathcal I=\{0\}\) in Theorem 14.15 refers to the derived Pfaffian system.

## Chapter 15. The Cartan–Kähler Existence Theorem

### O95-E15.3.01. Uniqueness clause of the Cartan–Kähler theorem

Status: Confirmed.
Location: §15.3 (Sufficient Conditions), p. 456, Theorem 15.7, last sentence.
Printed: "In particular, the integral submanifold is unique if and only if \(\tilde s_n=0\)."
Correct: if \(\tilde s_n=0\), the integral submanifold is unique once an
\((n-1)\)-dimensional integral submanifold \(N'\subset N\) is prescribed (with \(TN'|_x\) a regular
integral element in \(E\)). Without that Cauchy data it is in general not unique. Theorem 15.8 says
it then depends on \(s_k\) functions of \(k\) variables, with \(s_k\) the last nonzero character.
"Only if" is correct.
Evidence: on \(\mathbb R^4\) with coordinates \((x,y,u,p)\), take \(\mathcal I\) generated by
\(\theta=du-p\,dy\) and \(d\theta=-dp\wedge dy\). At the origin take
\(E=\operatorname{span}(\partial_y,\partial_x)\), ordered \(\mathbf v_1=\partial_y\),
\(\mathbf v_2=\partial_x\). Then \(\tilde s_0=s_0=1\). The polar form of \(\mathbf v_1\) is
\(\mathbf v_1\lrcorner d\theta=dp\), which is independent of \(\theta\), so
\(\tilde s_1=s_1=1\). Hence \(E\) is a regular integral element, with
\(\tilde s_2=4-2-1-1=0\). But for every constant \(a\), the surface \(u=ay^3\), \(p=3ay^2\) is
integral (\(du-p\,dy=3ay^2dy-3ay^2dy=0\)) and passes through \(0\) with tangent plane \(E\) (its
tangent vectors there are \(\partial_x\) and \(\partial_y\)). Distinct values of \(a\) give distinct
germs. This agrees with Theorem 15.8 (\(s_1=1\): one function of one variable, \(u=f(y)\)).
Target: [O95.15.3.02].

### Conventions and notation (not errata)

- (15.38) prints the termwise inequality \(s'_k\le s_k\). The argument given (submatrix ranks)
  proves it for partial sums, \(s'_1+\dots+s'_k\le s_1+\dots+s_k\). That is the form used in
  O95.15.5.01. The partial-sum form is enough for (15.45) by Abel summation:
  \(\sum_{k<m}(m-k)s_k=\sum_{k<m}(s_1+\dots+s_k)\).
- The source uses the same accented letter for the pointwise ranks of a flag and for the
  pseudo-character \(\tilde s_n\). The synopsis writes \(\tilde s_k\) for both. They agree on
  regular flags.
- "Degree of indeterminancy" is the source's spelling.

## Tables

### O95-ET.6.01. Complex types of Cases 6.2 and 6.3 in Table 6

Status: Confirmed.
Location: Table 6 (Primitive Lie Algebras of Vector Fields in \(\mathbb R^2\)), p. 475, Cases 6.2
and 6.3, column "\(\mathbb C\) Type".
Printed: 1.1 for both cases.
Correct: 1.2 for both cases.
Evidence: In the complex coordinates \(z=x+iu\), \(w=x-iu\) the generators of Case 6.2 are
\(\partial_z+\partial_w\), \(z\partial_z+w\partial_w\), \(z^2\partial_z+w^2\partial_w\); with
\(X=z\), \(U=1/(w-z)\) they become \(\partial_X\), \(X\partial_X-U\partial_U\),
\(X^2\partial_X-(2XU+1)\partial_U\), which is Case 1.2. The isotropy subalgebra at a point of the
open orbit is spanned by a semisimple element for Cases 1.2, 6.2 (rotations about \(i\) in the
upper half plane) and 6.3 (rotations about an axis), but by a nilpotent element for Case 1.1
(at \((0,u_0)\), \(u_0\ne0\), it is spanned by \(x^2\partial_x-2xu\partial_u\)).
Published: [Olver EIS 2nd printing], p. 475, Table 6, Cases 6.2 and 6.3, column 5.
Target: [O95.T.6.01].

### Conventions and notation (not errata)

- Apart from [O95-ET.6.01], no errata were found in the entries checked (listed in the synopsis
  entries O95.T.1.01–O95.T.7.01). The unchecked entries are recorded as printed.
- Table 6, Case 6.1: [Olver EIS 2nd printing], p. 475, suggests writing \(\beta\) for the parameter \(\alpha\) of
  Case 6.1, since it is not the parameter \(\alpha\) of the complex type 1.7 (\(k=1\)) to which the
  case corresponds; the relation between the two is left as an exercise. This is a notational
  suggestion; the synopsis keeps the printed letter.

## Published corrections to material outside the synopses

The published lists also correct the following statements and formulas, all in proofs or
examples that the synopsis does not state. They have no erratum entry and no synopsis target.
They are listed here so that this file accounts for every mathematical item of the lists. Each was
checked on the page image.

- §5.4, p. 144, line 10, (5.10): in \(\xi^i_\mu=\sum_\nu a^\nu_\mu\xi^i_\nu\) the coefficients are
  the \(A^\nu_\mu\) of (5.9). [Olver EIS 2nd printing], p. 144, line 10. Proof of Theorem 5.11, outlined in
  [O95.05.4.01] without (5.10).
- §5.7, p. 159, lines 5, 15 and 18: in the proof of Lemma 5.34 the wedge products
  \(d_{n+1}K_1\wedge\dots\wedge d_{n+1}K_r\) should be
  \(d_{n+1}[\mathcal DK_1]\wedge\dots\wedge d_{n+1}[\mathcal DK_r]\) (\(d_{n+1}K_\nu=0\) for
  \(K_\nu\) of order \(n\)). [Olver EIS 2nd printing], p. 159, lines 5, 15 & 18. [O95.05.7.02] states the lemma.
- §6.3, p. 190, lines 18 and 22: in the proof of Theorem 6.23 the vector field is
  \(\mathbf w=\eta\partial_y+\zeta\partial_v+\zeta^y\partial_{v_y}\), not \(\dots+\zeta\partial_u+\dots\),
  and the generator of \(H\) is \(\mathbf v=\partial_v\), not \(\partial_y\). [Olver EIS 2nd printing], p. 190, line 18,
  and p. 190, line 22 (two items). [O95.06.3.04] states the theorem.
- §7.1, p. 226, line 6: in the proof of Theorem 7.3,
  \(\widehat P(x,u^{(2n)})=\int_0^1R(t,x,u^{(2n)})\,dt\) with the \(p\)-tuple \(R\) of the preceding
  identity, not \(P\). [Olver EIS 2nd printing], p. 226, line 6. [O95.07.1.03] states the theorem.
- §11.0, p. 349, line −12: in Example 11.1 the absorbed form is
  \(\pi^1=\alpha^1-T^1_{12}\theta^2-T^1_{13}\theta^3\), a one-form, not
  \(\alpha^1-T^1_{12}\theta^1\wedge\theta^2-T^1_{13}\theta^1\wedge\theta^3\). [Olver EIS 2nd printing], p. 349,
  line −12. [O95.11.0.02] does not state the absorbed forms.
- §14.1, p. 423, (14.4): the map is \(\Phi(t,s)\), not \(\Phi(t,w)\). [Olver EIS 2nd printing], p. 423, (14.4). The
  proof outline in [O95.14.1.01] writes \(\Phi(t,s)\).
- §14.5, p. 446, line 5: in the proof of Theorem 14.30 the equivalence is between the
  restrictions of \(\boldsymbol\theta\) to \(U\) and \(\widetilde U\), not \(U\) and \(V\). [Olver EIS 2nd printing],
  p. 446, line 5. [O95.14.5.04] states the theorem.

[Olver EIS 2nd printing]: https://www-users.cse.umn.edu/~olver/book_/eis2.pdf
[Olver EIS 1st printing]: https://www-users.cse.umn.edu/~olver/book_/eis1.pdf
