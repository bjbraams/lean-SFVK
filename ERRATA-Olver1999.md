# Errata and source checks: Olver, Classical Invariant Theory (1999)

Reference: Peter J. Olver, *Classical Invariant Theory*, London Mathematical Society Student
Texts 44, Cambridge University Press, 1999. The local copy is
[References/Olver1999ClassicalInvariantTheory-CambridgeLMSST44.pdf](References/Olver1999ClassicalInvariantTheory-CambridgeLMSST44.pdf).

Locators use printed page numbers. To get the one-based PDF page number, add 22.

## Status vocabulary

- **Confirmed.** A contradiction is exhibited. It may be a direct calculation, a special case
  or counterexample, a numerical evaluation, a standard definition fixed in the source, or a
  conflict between two displays of the source.
- **Normalization check.** Two displays cannot both hold under one stated convention. An
  unstated change of basis, coordinate, branch or normalization may explain the difference.
  The synopsis fixes one convention and states the conversion.
- **Open check.** A suspected problem that is not settled. The entry states the uncertainty
  and the conjectured correction. Formalization is expected to decide it.

Each erratum gives:

- the location, as chapter, section (the synopsis numbering of the source's unnumbered
  sections), printed page, line where useful (negative lines are counted from the bottom) and
  equation or result number;
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries;
- where the same error is listed in the published corrections list below, a Published line
  citing the item by its page and formula or line, and saying how its correction differs from
  ours.

Synopsis entries cite errata by id. An erratum id \(\mathrm{O99\text{-}E}cc.s.nn\) is the
\(nn\)-th erratum located in section \(s\) of chapter \(cc\).

## Published errata lists

The author maintains a list of corrections on his web page:

- [Olver CIT corrections], by P. J. Olver: *Corrections and Comments on Classical Invariant
  Theory, by Peter J. Olver, London Math. Soc. Student Texts, vol. 44, Cambridge University
  Press, Cambridge, 1999*, last modified October 7, 2018.

The list refers to the 1999 edition; the local copy ("First published 1999", "Transferred to
digital printing 2003") has the same pagination, and every listed error that was checked is
present in it. The list locates an item by printed page and formula or line; a Published line
cites it in this form. Besides corrections, the list contains comments (for instance on the
discussion of semi-invariants on pp. 218–221 and the remark on p. 92); the comments that bear on
statements of the synopsis are treated like corrections. Some published corrections are
incomplete or differ from ours; the Published line then says so, with the evidence in the entry.
Published corrections to statements that the synopsis does not cover are listed in the section
"Published corrections to material outside the synopses" at the end of this file. Items of the
list that concern only wording, typography, historical remarks, the index or the bibliography
are not recorded here.

## Scope

These are observations about this edition, not an official publisher list. No claim is made
that formulas without an erratum are free of errors. Formulas that the synopsis marks "as
printed" were transcribed from the page images without an independent check. Corrected
formulas in the synopsis are statements to be formalized. They are not Lean proofs.
Garbling of the PDF text layer is not treated as an error of the printed book; every erratum
was checked on the page image.

Each chapter section ends with a list of conventions and notation that are not errata, for
example the source's sign of the quadratic discriminant or its use of "order" for the degree
in the coefficients.

## Summary by chapter

- Chapter 1. Prelude — Quadratic Polynomials and Quadratic Forms: 11 entries, 2 errata (Confirmed 2).
- Chapter 2. Basic Invariant Theory for Binary Forms: 41 entries, 10 errata (Confirmed 9, Normalization check 1).
- Chapter 3. Groups and Transformations: 23 entries, 3 errata (Confirmed 3).
- Chapter 4. Representations and Invariants: 34 entries, 10 errata (Confirmed 10).
- Chapter 5. Transvectants: 22 entries, 3 errata (Confirmed 3).
- Chapter 6. Symbolic Methods: 33 entries, 5 errata (Confirmed 5).
- Chapter 7. Graphical Methods: 17 entries, 8 errata (Confirmed 8).
- Chapter 8. Lie Groups and Moving Frames: 53 entries, 10 errata (Confirmed 10).
- Chapter 9. Infinitesimal Methods: 33 entries, 5 errata (Confirmed 5).
- Chapter 10. Multivariate Polynomials: 20 entries, 6 errata (Confirmed 5, Open check 1).
- Total: 287 entries, 62 errata (Confirmed 60, Normalization check 1, Open check 1).

## Chapter 1. Prelude — Quadratic Polynomials and Quadratic Forms

### O99-E01.1.01. Sign of the real double-root canonical form

Status: Confirmed.
Location: §1.1, p. 4, table "Affine Canonical Forms for Real Quadratic Polynomials", row II,
and the preceding sentence "The remaining cases are as in the complex version".
Printed: under real affine changes of variable, a real quadratic with \(\Delta=0\), \(a\ne0\)
has the canonical form \(p^2\).
Correct: the canonical forms are \(p^2\) for \(a>0\) and \(-p^2\) for \(a<0\); they are not
equivalent under real affine maps.
Evidence: under \(\bar p=\alpha p+\beta\) with \(\bar Q(\bar p)=Q(p)\) one has
\(\bar a=a/\alpha^2\), so the sign of the leading coefficient is invariant for real
\(\alpha\). Thus \(Q(p)=-p^2\) (\(a=-1\), \(\Delta=0\)) is never mapped to \(p^2\). The complex
argument "scale the coordinate \(p\) to reduce the multiple to unity" needs \(\alpha=\sqrt a\).
The projective table on p. 9 does keep both signs (\(\pm1\)).
Target: [O99.01.1.04].

### O99-E01.2.01. Discriminant of the linear canonical form

Status: Confirmed.
Location: §1.2, p. 9, paragraph on unimodular (area-preserving) transformations.
Printed: the inversion \(\bar p=-1/p\) maps \(kp\) to \(-k\bar p\), "both of which have
discriminant \(\Delta=k^2\)".
Correct: both have discriminant \(\Delta=-k^2/4\).
Evidence: \(Q(p)=kp=ap^2+2bp+c\) has \(a=c=0\), \(b=k/2\), so \(\Delta=ac-b^2=-k^2/4\) by (1.3).
For \(k=2\): \(Q=2p\), \(\Delta=-1\ne4\). The conclusion (\(kp\sim k'p\) only if \(k'=\pm k\))
is unaffected. The real-case remark that \(k(p^2+1)\) and \(kp\) are distinguished by the sign
of the discriminant agrees with the corrected value (\(k^2>0\), \(-k^2/4<0\)).
Target: [O99.01.2.07].

### Conventions and notation (not errata)

- (1.3): the source's discriminant of \(ap^2+2bp+c\) is \(\Delta=ac-b^2\), the negative of the
  usual \(b^2-ac\); the footnote on p. 2 says the sign is chosen for later generalizations.
- (1.6), (1.11): \(\bar Q\) is defined by \(\bar Q(\bar p)=Q(p)\), i.e. \(\bar Q=Q\circ
  (\text{transformation})^{-1}\).
- Tables on pp. 4, 8, 9 list a "canonical form" for each class; the real affine table lists
  \(k(p^2+1)\) and \(k(p^2-1)\) with a residual parameter \(k\), which is an invariant
  (\(k=\pm\Delta/a\)).

## Chapter 2. Basic Invariant Theory for Binary Forms

### O99-E02.4.01. Range of the scalar in the definition of homogeneity

Status: Confirmed.
Location: §2.4, p. 20, Definition 2.6 and Theorem 2.7; p. 21, Proposition 2.9.
Printed: \(Q\) is homogeneous of degree \(n\) if \(Q(\lambda\mathbf x)=\lambda^nQ(\mathbf x)\) for
all \(\mathbf x\) (the range of \(\lambda\) is not stated); a differentiable \(Q\) is
homogeneous of degree \(n\) iff \(xQ_x+yQ_y=nQ\); every homogeneous function of degree \(n\) is
\(y^nF(x/y)\).
Correct: Theorem 2.7 holds for positive homogeneity (\(\lambda>0\)); Proposition 2.9 holds for
homogeneity with all \(\lambda\ne0\) (on \(y\ne0\)). No single reading of Definition 2.6 makes
both true.
Evidence: \(Q=(x^2+y^2)^{3/2}\) is \(C^2\) on \(\mathbb R^2\) and satisfies \(xQ_x+yQ_y=3Q\), but
\(Q(-\mathbf x)=Q(\mathbf x)\ne-Q(\mathbf x)\), so it is not homogeneous for \(\lambda=-1\) (the
"if" part of Theorem 2.7 fails for \(\lambda<0\); the proof integrates \(h'=(n/\lambda)h\) from
\(\lambda=1\), which reaches only \(\lambda>0\)). The same \(Q\) is positively homogeneous of
degree \(3\) but is not \(y^3F(x/y)\): \(F(p)=Q(p,1)=(1+p^2)^{3/2}\) would force
\(Q(p,-1)=-(1+p^2)^{3/2}<0\), while \(Q>0\).
Target: [O99.02.4.01], [O99.02.4.02], [O99.02.4.04].

### O99-E02.4.02. The smooth homogeneous function of Exercise 2.8

Status: Confirmed.
Location: §2.4, p. 20, Exercise 2.8.
Printed: \(Q(x,y)=x^2\exp(x^2/y^2)\) for \(y\ne0\), \(Q=0\) for \(y=0\), is a smooth, globally
defined homogeneous function of degree \(2\).
Correct: with \(\exp(-x^2/y^2)\) the function is homogeneous of degree \(2\), continuous on
\(\mathbb R^2\) and \(C^\infty\) on \(\mathbb R^2\setminus\{0\}\), but it is not \(C^2\) at the
origin; no non-polynomial homogeneous function of degree \(2\) is \(C^2\) on all of
\(\mathbb R^2\).
Evidence: as printed, \(Q(1,y)=e^{1/y^2}\to\infty\) as \(y\to0\), so \(Q\) is not even
continuous at \((1,0)\). For any \(Q\) of class \(C^2\) near \(0\) with \(Q(\lambda\mathbf x)=
\lambda^2Q(\mathbf x)\) (\(\lambda>0\)), \(Q(\mathbf x)=\lim_{\lambda\to0^+}\lambda^{-2}Q(\lambda
\mathbf x)=\frac12D^2Q(0)(\mathbf x,\mathbf x)\), a quadratic form; \(x^2e^{-x^2/y^2}\) is not a
quadratic form (it vanishes on both axes, so it would be \(cxy\), but its values at \((1,1)\) and
\((1,-1)\) are both \(e^{-1}\)).
Published: [Olver CIT corrections], p. 20, Exercise 2.8. The list supplies the minus sign in
the exponent only; the corrected function is still not smooth at the origin, as shown above.
Target: [O99.02.4.03].

### O99-E02.6.01. Bar over \(J\) in the definition of a covariant

Status: Confirmed.
Location: §2.6, p. 25, (2.20), Definition 2.21.
Printed: \(J(\mathbf a,\mathbf x)=(\alpha\delta-\beta\gamma)^k\,\bar J(\bar{\mathbf a},\bar{\mathbf x})\).
Correct: \(J(\mathbf a,\mathbf x)=(\alpha\delta-\beta\gamma)^k\,J(\bar{\mathbf a},\bar{\mathbf x})\),
with the same function \(J\) on both sides.
Evidence: the definition requires one function \(J\) of the coefficients and the variables that
is unchanged up to the determinantal factor; \(\bar J\) is not defined. The text that follows
("invariants are just covariants that do not explicitly depend on \(\mathbf x\)") requires (2.20)
to reduce to the invariance condition (2.19), \(I(\mathbf a)=(\alpha\delta-\beta\gamma)^kI(\bar{\mathbf a})\),
which has no bar on \(I\).
Published: [Olver CIT corrections], p. 25, (2.20). Same correction.
Target: [O99.02.6.02].

### O99-E02.7.01. Vanishing Hessian over the reals

Status: Confirmed.
Location: §2.7, p. 26, Proposition 2.23.
Printed: a binary form \(Q(x,y)\) has vanishing Hessian iff \(Q(x,y)=(cx+dy)^n\).
Correct: over \(\mathbb C\) as printed (\(n\ge1\)); for real forms (which the chapter explicitly
includes, p. 12) \(H\equiv0\) iff \(Q=\pm(cx+dy)^n\) with \(c,d\) real; the sign is needed for
even \(n\).
Evidence: \(Q=-x^2\) has \(H=Q_{xx}Q_{yy}-Q_{xy}^2=(-2)(0)-0=0\), but \((cx+dy)^2\ge0\) for real
\(c,d\). The general proof on p. 91, which integrates \(Q'=kQ^{(n-1)/n}\) to \(Q=(ap+b)^n\), needs complex
\(a,b\) for \(Q=-p^2\).
Target: [O99.02.7.02], [O99.05.2.02].

### O99-E02.7.02. Sign of the discriminant of the cubic Hessian

Status: Normalization check.
Location: §2.7, p. 27, (2.25).
Printed: the discriminant of the quadratic Hessian (2.24) "is
\(\tilde\Delta=\frac14(a_0a_3-a_1a_2)^2-(a_1a_3-a_2^2)(a_0a_2-a_1^2)\)", and \(\tilde\Delta=
\frac14\Delta\).
Correct: \(\tilde\Delta\) as displayed equals \(\frac14\Delta\), but it is the negative of the
discriminant of \(\frac1{36}H\) in the book's convention (1.3), \(\Delta=ac-b^2\) for
\(ax^2+2bxy+cy^2\) (also used on p. 38 and in (2.46)). In that convention
\(\Delta[\frac1{36}H]=-\frac14\Delta\) and \(\Delta[H]=-324\Delta\).
Evidence: \(\frac1{36}H=Ax^2+2Bxy+Cy^2\) with \(A=a_1a_3-a_2^2\), \(B=\frac12(a_0a_3-a_1a_2)\),
\(C=a_0a_2-a_1^2\), so \(AC-B^2=-\tilde\Delta\). Symbolic check: \(\tilde\Delta/\Delta=\frac14\)
identically, and \(\Delta[H]/\Delta=-324=-36^2/4\) for e.g. \(Q=x^3+2x^2y-xy^2+5y^3\), in agreement
with (2.46). The conclusion (multiple root of \(Q\) iff multiple root of \(H\)) is unaffected.
Target: [O99.02.7.03].

### O99-E02.7.03. Vanishing of the quartic invariant \(j\)

Status: Confirmed.
Location: §2.7, p. 29, lines after (2.30).
Printed: "\(j=0\) if and only if \(Q\) can be written as the sum of two fourth powers,
\(Q=(ap+b)^4+(cp+d)^4\)".
Correct: for a quartic with four distinct roots, \(j=0\) iff \(Q\) is a sum of two fourth powers;
in general \(j=0\) iff \(Q\) is such a sum or has a root of multiplicity at least \(3\).
Evidence: \(Q=x^3y\) has \(a_3=\frac14\) and all other \(a_i=0\), so \(j=-a_0a_3^2-\dots=0\) (and
\(i=0\)). A sum of two fourth powers of linear forms is either \(c\ell^4\) (dependent forms) or
equivalent to \(x^4+y^4\) (four simple roots); \(x^3y\) has a triple and a simple root, so it is
neither.
Target: [O99.02.7.06].

### O99-E02.11.01. Definition of subresultants

Status: Confirmed.
Location: §2.11, p. 37, Exercise 2.38.
Printed: the \(k\)-th subresultant \(\mathbf R_k\) is the \((m+n-2k)\times(m+n-2k)\) determinant
obtained by deleting the first and last \(k\) rows and columns from (2.42); \(P,Q\) have exactly
\(k\) common roots (with multiplicity) iff \(\mathbf R_0=\dots=\mathbf R_{k-1}=0\ne\mathbf R_k\).
Correct: delete the last \(k\) rows of each of the two blocks (the \(\tilde a\)-rows and the
\(\tilde b\)-rows) and the last \(2k\) columns (the principal subresultant coefficient); then the
criterion holds when \(\tilde a_m\tilde b_n\ne0\).
Evidence: \(P=(p-1)^2(p+1)\) (\(m=3\)) and \(Q=(p-1)^2\) (\(n=2\)) have \(k=2\) common roots. The
Sylvester matrix has rows \((1,-1,-1,1,0)\), \((0,1,-1,-1,1)\), \((1,-2,1,0,0)\), \((0,1,-2,1,0)\),
\((0,0,1,-2,1)\); deleting the first and last row and column leaves a \(3\times3\) determinant
equal to \(-4\ne0\), so the printed \(\mathbf R_1\ne0\) although two roots are common. The
corrected \(\mathbf R_0,\mathbf R_1,\mathbf R_2\) are \(0,0,1\). Random examples with
\(\deg\gcd=1,2,3\) confirm the corrected criterion.
Published: [Olver CIT corrections], pp. 36–37, (2.42). The list keeps the deletion rule of
Exercise 2.38 and instead reverses the order of the \(\tilde b\)-rows in (2.42), with a compensating
sign. This is equivalent to the correction above: after the reversal, the rows and columns that
remain after deleting the first and last \(k\) rows and columns are the last \(n-k\)
\(\tilde a\)-rows and the last \(m-k\) \(\tilde b\)-rows restricted to columns \(k+1,\dots,m+n-k\),
which are the rows kept above shifted by \(k\) columns; the determinants agree up to sign (in the
example above the reordered matrix gives \(\mathbf R_1=0\)). The list's sign factor
\((-1)^k\) with \(k\) the integer part of \(n/2\) should be \((-1)^{\lfloor m/2\rfloor}\): (2.42) has
\(m\) rows of \(\tilde b\)'s (p. 36), and reversing \(r\) rows multiplies the determinant by
\((-1)^{r(r-1)/2}=(-1)^{\lfloor r/2\rfloor}\).
Target: [O99.02.11.03].

### O99-E02.11.02. Discriminant as a product over root pairs

Status: Confirmed.
Location: §2.11, p. 38, (2.45), Theorem 2.39.
Printed: for \(Q\) in normal factored form, \(\Delta[Q]=\prod_{\alpha\ne\beta}(x_\alpha y_\beta-
y_\alpha x_\beta)^2\).
Correct: \(\Delta[Q]=n^{-n}\prod_{\alpha\ne\beta}(x_\alpha y_\beta-y_\alpha x_\beta)=
(-1)^{n(n-1)/2}n^{-n}\prod_{\alpha<\beta}(x_\alpha y_\beta-y_\alpha x_\beta)^2\), with \(\Delta[Q]\)
defined by (2.44).
Evidence: for \(n=2\), \(Q=(y_1x-x_1y)(y_2x-x_2y)\) has \(a_2=y_1y_2\), \(a_1=-\frac12(x_1y_2+
x_2y_1)\), \(a_0=x_1x_2\), so \(\Delta=a_0a_2-a_1^2=-\frac14(x_1y_2-x_2y_1)^2\), while the printed
product is \((x_1y_2-x_2y_1)^4\). Exact evaluation of (2.44) with roots \([2,1],[-1,4],[3,-2],
[5,3]\) gives \(\Delta[Q]/\prod_{\alpha\ne\beta}=\frac14,\frac1{27},\frac1{256}\) for
\(n=2,3,4\). The printed product over ordered pairs counts each pair twice.
Published: [Olver CIT corrections], p. 38, (2.45). Same correction.
Target: [O99.02.11.04].

### O99-E02.11.03. Derivative of the factored form in the proof of Theorem 2.39

Status: Confirmed.
Location: §2.11, p. 38, proof of Theorem 2.39.
Printed: \(Q=\prod_\alpha(xy_\alpha-yx_\alpha)\), so \(\partial Q/\partial x=\sum_\beta
\prod_{\alpha\ne\beta}(xy_\alpha-yx_\alpha)\).
Correct: \(\partial Q/\partial x=\sum_\beta y_\beta\prod_{\alpha\ne\beta}(xy_\alpha-yx_\alpha)\).
Evidence: for \(n=1\), \(Q=xy_1-yx_1\) has \(Q_x=y_1\), not \(1\). With the factor \(y_\beta\),
(2.43) gives \(\mathbf R[Q,Q_x]=\prod_\alpha Q_x(\mathbf x_\alpha)=\big(\prod_\alpha y_\alpha\big)
\prod_{\alpha\ne\beta}(x_\alpha y_\beta-y_\alpha x_\beta)=a_n\prod_{\alpha\ne\beta}(x_\alpha y_\beta-
y_\alpha x_\beta)\), which leads to the corrected (2.45) in [O99-E02.11.02].
Published: [Olver CIT corrections], p. 38, display after (2.45). Same correction.
Target: [O99.02.11.04].

### O99-E02.12.01. Sign of the resultant of a cubic and its Hessian

Status: Confirmed.
Location: §2.12, p. 41, (2.46), Exercise 2.43.
Printed: \(\mathbf R[Q,H]=6^6\Delta^2\).
Correct: \(\mathbf R[Q,H]=-6^6\Delta^2\).
Evidence: \(Q=x^3-xy^2=x(x-y)(x+y)\) has normal-form roots \([0,1],[1,1],[-1,1]\),
\(H=-12x^2-4y^2\), so by (2.43) \(\mathbf R[Q,H]=H(0,1)H(1,1)H(-1,1)=(-4)(-16)(-16)=-1024\); here
\(a_1=-\frac13\), \(\Delta=4a_1^3a_3=-\frac4{27}\), \(6^6\Delta^2=1024\). The Sylvester determinant
(2.42) gives the same value, and for \(Q=x^3+2x^2y-xy^2+5y^3\) it gives
\(\mathbf R[Q,H]/\Delta^2=-46656\). The other five identities in (2.46) check exactly.
Target: [O99.02.12.03].

### Conventions and notation (not errata)

- p. 29: the source calls the root configuration with \(j=0\) an "anharmonic quadruplet"; the
  classical term is *harmonic* (cross-ratio \(-1\)), as for the roots of \(x^4+y^4\).
- (2.38)–(2.43): resultants use forms written without binomial coefficients; the discriminant
  (2.44) is evaluated on such coefficients of \(Q\) and \(Q_x\) but normalized by the binomial
  coefficient \(a_n\).
- p. 34: in the discussion of trace, the letter \(k\) denotes the order of \(K\), not its weight.
- p. 40: the counts of invariants and covariants in Sylvester's table (with Dixmier–Lazard
  corrections) are reported as historical data and are not part of the synopsis.

## Chapter 3. Groups and Transformations

### O99-E03.2.01. Projective linear group in even dimension

Status: Confirmed.
Location: §3.2, p. 49, Example 3.24.
Printed: for \(n\) even, "we can identify \(PSL(n,\mathbb R)\simeq SL(n,\mathbb R)/\{\pm\mathbb 1\}\)",
where \(PSL(n,\mathbb R)=GL(n,\mathbb R)/\{\lambda\mathbb 1\}\).
Correct: for \(n\) even, \(SL(n,\mathbb R)/\{\pm\mathbb 1\}\) is isomorphic to the index-two
subgroup \(\{[A]\mid\det A>0\}\) of \(GL(n,\mathbb R)/\{\lambda\mathbb 1\}\); the full quotient is
not isomorphic to it in general.
Evidence: \(\det(\lambda A)=\lambda^n\det A\) has the sign of \(\det A\) for \(n\) even, so the
sign of the determinant is well defined on \(GL(n,\mathbb R)/\{\lambda\mathbb 1\}\) and
\([\mathrm{diag}(-1,1,\dots,1)]\) is not the class of any matrix of determinant \(1\). For
\(n=2\), \(GL(2,\mathbb R)/\{\lambda\mathbb 1\}\) has two connected components (it contains the
orientation-reversing map \(p\mapsto-p\) of \(\mathbb R\mathbb P^1\)), while
\(SL(2,\mathbb R)/\{\pm\mathbb 1\}\) is connected.
Published: [Olver CIT corrections], p. 49, Example 3.24, last sentence: for \(n\) even
\(PSL(n,\mathbb R)\) has two components, and \(SL(n,\mathbb R)\) is a two-fold covering of the
identity component \(PSL^+(n,\mathbb R)=SL(n,\mathbb R)/\{\pm\mathbb 1\}\). Same correction.
Target: [O99.03.2.05].

### O99-E03.4.01. Two affine symmetries of the isosceles triangle

Status: Confirmed.
Location: §3.4, p. 56, the six \(3\times3\) matrices after Example 3.43 (second row, middle and
right).
Printed: \(\begin{pmatrix}-\frac12&\frac12&\frac12\\-\frac32&\frac12&\frac12\\0&0&1
\end{pmatrix}\) and \(\begin{pmatrix}-\frac12&-\frac12&\frac12\\-\frac12&\frac32&-\frac12\\0&0&1
\end{pmatrix}\).
Correct: \(\begin{pmatrix}-\frac12&\frac12&\frac12\\-\frac32&-\frac12&\frac12\\0&0&1\end{pmatrix}\)
(the 3-cycle \((1,0)\mapsto(0,-1)\mapsto(0,1)\mapsto(1,0)\)) and
\(\begin{pmatrix}-\frac12&-\frac12&\frac12\\-\frac32&\frac12&\frac12\\0&0&1\end{pmatrix}\) (the
transposition of \((1,0)\) and \((0,-1)\)).
Evidence: the first printed matrix maps the vertex \((0,1)\) to \((1,1)\) and \((0,-1)\) to
\((0,0)\); the second maps \((1,0)\) to \((0,-1)\), \((0,1)\) to \((0,1)\) but \((0,-1)\) to
\((1,-2)\). Neither is a symmetry of \(\{(1,0),(0,1),(0,-1)\}\). Solving \(Av_i+b=v_{\pi(i)}\) for
the six permutations \(\pi\) gives the four printed correct matrices and the two corrected
ones.
Target: [O99.03.4.02].

### O99-E03.5.01. Number of orbits of real quadratic forms

Status: Confirmed.
Location: §3.5, pp. 59–60, Example 3.53.
Printed: "there are four different canonical forms for real quadratic forms, and hence there
are four distinct orbits": \(\mathcal O_+=\{ac>b^2\}\), \(\mathcal O_-=\{ac<b^2\}\),
\(\mathcal O_0=\{ac=b^2,\ a^2+b^2+c^2\ne0\}\), \(\mathcal O_*=\{0\}\).
Correct: there are six orbits; \(\mathcal O_+\) splits by the sign of \(a\) (positive and negative
definite forms) and \(\mathcal O_0\) by the sign of \(a+c\) (\(x^2\) and \(-x^2\)), in agreement with
the six real canonical forms of Chapter 1 (p. 9).
Evidence: under (1.12) \(\bar Q(\bar{\mathbf x})=Q(\mathbf x)\), so the set of values of \(Q\) is
invariant; \(x^2+y^2\) takes only values \(\ge0\) and \(-x^2-y^2\) only values \(\le0\), so they
lie in different orbits though both have \(\Delta=1>0\); likewise \(x^2\) and \(-x^2\). The same
page lists the canonical forms \(\pm(x^2+y^2)\) and \(\pm x^2\) separately.
Target: [O99.03.5.02].

### Conventions and notation (not errata)

- Example 3.24, Example 3.41: the source writes \(PSL(n,\mathbb R)\) for
  \(GL(n,\mathbb R)/\{\lambda\mathbb 1\}\), usually written \(PGL(n,\mathbb R)\).
- Exercise 3.9: the source's \(GL(n,\mathbb Z)\) denotes all invertible (in \(GL(n,\mathbb R)\))
  integer matrices, not the usual group of integer matrices with determinant \(\pm1\).
- Exercise 3.50 calls \(\mathbb C\mathbb P^1\) the "complex projective plane"; it is the complex
  projective line (the source's own footnote on p. 18 asks to avoid "complex plane").
- (3.6): \((ijk)\) denotes the permutation \(1\mapsto i\), \(2\mapsto j\), \(3\mapsto k\), not cycle
  notation.

## Chapter 4. Representations and Invariants

### O99-E04.1.01. Permutation matrices as a homomorphism

Status: Confirmed.
Location: §4.1, p. 63, Example 4.3.
Printed: \(A_\pi(x)=(x_{\pi(1)},\dots,x_{\pi(n)})\), and \(\rho:\pi\mapsto A_\pi\) is a group
monomorphism \(S_n\to GL(n)\).
Correct: \(A_\pi(x)=(x_{\pi^{-1}(1)},\dots,x_{\pi^{-1}(n)})\) (equivalently \(A_\pi e_i=e_{\pi(i)}\)) gives a
monomorphism; the printed rule gives \(A_{\pi\sigma}=A_\sigma A_\pi\), an anti-homomorphism (the
group law of \(S_n\) being composition, Example 3.27).
Evidence: with \(y=A_\sigma x\), \(y_i=x_{\sigma(i)}\), the printed rule gives \((A_\pi y)_i=
y_{\pi(i)}=x_{\sigma(\pi(i))}\), so \(A_\pi A_\sigma=A_{\sigma\circ\pi}\). For \(n=3\),
\(\pi=(1\,2)\), \(\sigma=(2\,3)\): \(\pi\circ\sigma\) maps \(1\mapsto2\), \(2\mapsto3\), \(3\mapsto1\), and
\(A_{\pi\circ\sigma}x=(x_2,x_3,x_1)\), while \(A_\pi A_\sigma x=A_\pi(x_1,x_3,x_2)=(x_3,x_1,x_2)\).
(The set of six matrices displayed is correct as a set.)
Target: [O99.04.1.02].

### O99-E04.1.02. Change of basis in Example 4.5

Status: Confirmed.
Location: §4.1, p. 66, first display (continuation of Example 4.5).
Printed: \(\tilde A\tilde e_1=\tilde Ae_2=-\beta e_1+\alpha e_2=\alpha\tilde e_1+\beta\tilde e_2\),
\(\tilde A\tilde e_2=-\tilde Ae_1=-\delta e_1+\gamma e_2=\gamma\tilde e_1+\delta\tilde e_2\).
Correct: \(\tilde A\tilde e_1=-\gamma e_1+\alpha e_2=\alpha\tilde e_1+\gamma\tilde e_2\),
\(\tilde A\tilde e_2=-\delta e_1+\beta e_2=\beta\tilde e_1+\delta\tilde e_2\).
Evidence: \(\tilde A=\begin{pmatrix}\delta&-\gamma\\-\beta&\alpha\end{pmatrix}\) has second column
\((-\gamma,\alpha)\) and first column \((\delta,-\beta)\). The printed lines give the matrix
\(\begin{pmatrix}\alpha&\gamma\\\beta&\delta\end{pmatrix}=A^{\mathsf T}\) in the basis \(\tilde e\),
contradicting the stated conclusion; the corrected lines give \(A\), as claimed.
Target: [O99.04.1.05].

### O99-E04.3.01. Shear step in the proof of Theorem 4.15

Status: Confirmed.
Location: §4.3, p. 71, proof of Theorem 4.15.
Printed: \((x,y)\mapsto(x+\beta y,y)\) maps \(x^ky^{n-k}\) to \(\sum_{i=0}^k\binom ki\beta^ix^iy^{n-i}\).
Correct: \(\sum_{i=0}^k\binom ki\beta^{k-i}x^iy^{n-i}\).
Evidence: \((x+\beta y)^ky^{n-k}=\sum_i\binom kix^i(\beta y)^{k-i}y^{n-k}\); for \(k=n=1\), \(x\mapsto
x+\beta y\), whose \(y\)-coefficient is \(\beta\), while the printed sum gives \(\beta x+y\). The
argument (all monomials \(x^iy^{n-i}\), \(i\le k\), occur) is unaffected.
Target: [O99.04.3.04].

### O99-E04.3.02. Completeness of the list \(\rho_{n,k}\)

Status: Confirmed.
Location: §4.3, pp. 71–72, Remark after Theorem 4.15.
Printed: "the representations \(\rho_{n,k}\) provide a complete list of all irreducible
finite-dimensional representations of \(GL(2)\)".
Correct: they exhaust the irreducible finite-dimensional *rational* (polynomial in the matrix
entries and \(\det^{-1}\)) representations of \(GL(2,\mathbb C)\); continuous representations
need not be of this form.
Evidence: \(A\mapsto|\det A|^{1/2}\) is a one-dimensional (hence irreducible) continuous
representation of \(GL(2,\mathbb R)\) and of \(GL(2,\mathbb C)\); it is not \(\rho_{0,k}=(\det A)^k\)
for any integer \(k\) (take \(A=2\cdot\mathbb 1\): \(|\det A|^{1/2}=2\), \((\det A)^k=4^k\)), nor
\(\rho_{n,k}\) with \(n\ge1\) (dimension \(n+1\ge2\)). Likewise \(A\mapsto\operatorname{sign}\det A\) for
\(GL(2,\mathbb R)\).
Target: [O99.04.3.04].

### O99-E04.4.01. Normalization of the power sums

Status: Confirmed.
Location: §4.4, p. 75, Exercise 4.24.
Printed: \(P_k(x)=\varsigma((x_1)^k)=\sum(x_i)^k\).
Correct: \(P_k=\sum_ix_i^k=n\,\varsigma(x_1^k)\).
Evidence: by (4.10), \(\varsigma(x_1^k)=\frac1{n!}\sum_{\pi}x_{\pi(1)}^k=\frac1n\sum_ix_i^k\); for
\(n=2\), \(k=1\): \(\varsigma(x_1)=\frac12(x_1+x_2)\). Compare (4.11), where \(\sigma_1=\binom n1
\varsigma(x_1)\) carries the factor \(n\).
Target: [O99.04.4.05].

### O99-E04.4.02. Coefficients of a polynomial in terms of its roots

Status: Confirmed.
Location: §4.4, p. 75, Exercise 4.25.
Printed: \(c_k=(-1)^{n-k}c_n\sigma_k(p_1,\dots,p_n)\), \(k=1,\dots,n\).
Correct: \(c_k=(-1)^{n-k}c_n\sigma_{n-k}(p_1,\dots,p_n)\), \(k=0,\dots,n\) (\(\sigma_0=1\)).
Evidence: \(c_n\prod_\nu(p-p_\nu)=c_n\sum_j(-1)^j\sigma_jp^{n-j}\). For \(n=2\), \(c_2(p-p_1)(p-p_2)\) has
\(c_1=-c_2(p_1+p_2)=-c_2\sigma_1\) and \(c_0=c_2p_1p_2=c_2\sigma_2\); the printed formula gives
\(c_1=-c_2\sigma_1\) but \(c_2=c_2\sigma_2\), false for \(p_1p_2\ne1\).
Target: [O99.04.4.05].

### O99-E04.5.01. Index range of the elementary multi-symmetric polynomials

Status: Confirmed.
Location: §4.5, p. 78, (4.16).
Printed: \(\sigma_I(\mathbf x^1,\dots,\mathbf x^m)=\binom nk\varsigma(x^{i_1}_1x^{i_2}_2\cdots x^{i_k}_k)\),
\(I=(i_1,\dots,i_k)\), \(1\le i_\kappa\le n\).
Correct: the superscripts label the \(m\) vectors, so \(1\le i_\kappa\le m\) (with \(1\le k\le n\);
nondecreasing \(I\) suffice).
Evidence: \(\mathbf x^i\) is defined for \(i=1,\dots,m\) only, so \(x^{i_\kappa}\) with \(i_\kappa>m\) is
undefined when \(n>m\); for \(m<n\) the printed range omits nothing but refers to nonexistent
vectors, and for \(m>n\) it omits e.g. \(\sigma_{(m)}=\sum_jx^m_j\). The worked example has \(m=n=2\)
and does not distinguish the two.
Target: [O99.04.5.04].

### O99-E04.7.01. When the weight of a relative invariant is a multiplier

Status: Confirmed.
Location: §4.7, p. 83, sentence after Definition 4.40.
Printed: "as long as \(R\not\equiv0\) satisfies (4.25), the weight function \(\mu\) must necessarily
be a multiplier for the group action".
Correct: (4.21) follows at every \(x\) with \(R(x)\ne0\); \(\mu\) is a multiplier if \(R\) vanishes
nowhere (or if \(\mu\) is otherwise known to be one).
Evidence: (4.25) gives \(\mu(gh,x)R(x)=\mu(g,h\cdot x)\mu(h,x)R(x)\), which says nothing where
\(R(x)=0\). Example: \(G=\{e\}\) acting on \(\mathbb R\), \(R(x)=x\), \(\mu(e,x)=1\) for \(x\ne0\) and
\(\mu(e,0)=2\): (4.25) holds and \(R\not\equiv0\), but \(\mu(e,0)\ne1\).
Target: [O99.04.7.01].

### O99-E04.7.02. Projective line in the covariant interpretation

Status: Confirmed.
Location: §4.7, p. 84, first paragraph.
Printed: "In the case of projective coordinates, where \(J:\mathcal P^{(n)}\times\mathbb C\mathbb P^2
\to\mathbb C\)".
Correct: \(J:\mathcal P^{(n)}\times\mathbb C\mathbb P^1\to\mathbb C\).
Evidence: the projective coordinate \(p=x/y\) of \(\mathbf x\in\mathbb C^2\setminus\{0\}\) lives on
\(\mathbb C\mathbb P^1=\mathbb P(\mathbb C^2)\) (Definition 2.4); \(\mathbb C\mathbb P^2\) would
correspond to three homogeneous variables.
Target: [O99.04.7.03].

### O99-E04.7.03. Multiplier of the gradient

Status: Confirmed.
Location: §4.7, pp. 84–85, Exercise 4.42, the paragraph before (4.27), and the last paragraph
before Exercise 4.43.
Printed: the gradient of an absolute invariant is a vector-valued relative invariant "for the
Jacobian multiplier"; for \(GL(2)\) on \(\mathbb R^2\), \(\nabla J\) of an absolute covariant is a
relative invariant "for the identity multiplier"; for \(J\) of weight \(k\), for "the
matrix-valued multiplier \(\mu(A)=(\det A)^k\cdot A\)".
Correct: \(\nabla I(g\cdot x)=J(g,x)^{-\mathsf T}\nabla I(x)\), so the multiplier is the
contragredient Jacobian \(J(g,x)^{-\mathsf T}\); for \(GL(2)\) it is \(A^{-\mathsf T}\) for absolute
\(J\), in agreement with (4.28), and \((\det A)^{-k}A^{-\mathsf T}\) for weight \(k\).
Evidence: the chain rule gives \(\nabla_xI(x)=J(g,x)^{\mathsf T}(\nabla I)(g\cdot x)\). Example: the
absolute covariant \(J=ax+by\) (a linear form of weight \(0\)) has \(\nabla J=(a,b)\), and by (4.5)
\((\bar a,\bar b)=A^{-\mathsf T}(a,b)\); for \(A=\mathrm{diag}(2,1)\) this is \((a/2,b)\), not
\(A(a,b)=(2a,b)\). For weight \(k\), \(J(\mathbf a,\mathbf x)=(\det A)^k\bar J(\bar{\mathbf a},
\bar{\mathbf x})\) gives \(\bar\nabla\bar J=(\det A)^{-k}A^{-\mathsf T}\nabla J\). (In dimension two
\(A^{-\mathsf T}\) is conjugate to \((\det A)^{-1}A\) by Example 4.5, so the printed multipliers are
correct only up to this equivalence and a determinant power.)
Target: [O99.04.7.04].

### Conventions and notation (not errata)

- (4.14): \(a_{ijk}=\frac12(\mathbf x_j-\mathbf x_i)\wedge(\mathbf x_j-\mathbf x_k)\) is the signed area
  with the orientation opposite to the usual \(\frac12(\mathbf x_j-\mathbf x_i)\wedge(\mathbf x_k-
  \mathbf x_i)\); it is positive for clockwise \(\mathbf x_i,\mathbf x_j,\mathbf x_k\).
- (4.6): \(\rho_{n,k}\) acts on forms of weight \(-k\) in the sense of Definition 2.27
  (\(\bar Q=(\det A)^kQ\circ A^{-1}\)).
- (4.20): multiplier representations are written \(\bar F(g\cdot x)=\mu(g,x)F(x)\), so the
  multiplier of the classical weight-\(k\) invariants is \((\det A)^{-k}\), the reciprocal of the
  factor in (2.19).
- Example 4.32: the source's \(\varsigma\) in (4.16) acts by simultaneous permutation of the lower
  indices.

## Chapter 5. Transvectants

### O99-E05.2.01. Last coefficient of the covariant \(V\)

Status: Confirmed.
Location: §5.2, p. 92, (5.16), Exercise 5.8.
Printed: \(V=Q^3Q''''-4\frac{n-3}nQ^2Q'Q'''+6\frac{(n-2)(n-3)}{n^2}QQ'^2Q''+\frac{(n-1)(n-2)(n-3)}{n^3}
(Q')^4\), with \(U=(Q,T)^{(1)}=n^3(n-1)V-3\frac{n-2}{n-1}H^2\) (5.15).
Correct: the last term of \(V\) is \(-3\frac{(n-1)(n-2)(n-3)}{n^3}(Q')^4\); with this \(V\), (5.15)
holds identically (and (5.14) is correct).
Evidence: computing \(U=(3n-6)Q'T-nQT'\) from (5.11) and (5.14) gives
\(U-\big(n^3(n-1)V_{\rm printed}-3\frac{n-2}{n-1}H^2\big)=-4(n-1)^2(n-2)(n-3)(Q')^4\) identically.
Special case \(n=4\), \(Q(p)=p\) (the form \(xy^3\)): \(H=-9\), \(T=-36\), \(U=6\cdot(-36)=-216\), while the
printed right side is \(64\cdot3\cdot\frac3{32}-162=-144\); the corrected \(V=-\frac9{32}\) gives
\(-54-162=-216\). Direct evaluation of the homogeneous transvectants for random forms of degrees
\(4,5,6\) confirms the corrected formula; for \(n=3\) both versions agree.
Published: [Olver CIT corrections], p. 92, (5.16). Same correction.
Target: [O99.05.2.04].

### O99-E05.5.01. Leading term of the Moyal bracket

Status: Confirmed.
Location: §5.5, p. 98, sentence after (5.34).
Printed: \([\![P,Q]\!]_t=t\{P,Q\}+O(t^3)\).
Correct: with the normalization (5.34), \([\![P,Q]\!]_t=\{P,Q\}+O(t^2)\); the expansion
\(t\{P,Q\}+O(t^3)\) holds for \(\frac12(P\star_tQ-Q\star_tP)\).
Evidence: \(P\star_tQ-Q\star_tP=\sum_n\frac{t^n}{n!}(1-(-1)^n)(P,Q)^{(n)}=2t(P,Q)^{(1)}+\frac{t^3}3
(P,Q)^{(3)}+\dots\) by (5.8), so dividing by \(2t\) gives \(\{P,Q\}+\frac{t^2}6(P,Q)^{(3)}+\dots\);
equivalently \(\sinh(t\Omega)/t=\Omega+t^2\Omega^3/6+\dots\). For \(P=x\), \(Q=y\):
\([\![x,y]\!]_t=1\), not \(t\).
Published: [Olver CIT corrections], p. 98, next to last line. Same correction.
Target: [O99.05.5.03].

### O99-E05.2.02. Third transvectant in projective coordinates (5.11)

Status: Confirmed.
Location: §5.2, p. 90, Example 5.7, third formula of (5.11).
Printed: \((Q,R)^{(3)}=m(m-1)(m-2)Q'''R-3(m-1)(m-2)(n-2)Q''R'+3(m-2)(n-1)(n-2)-n(n-1)(n-2)QR''\).
Correct: \((Q,R)^{(3)}=m(m-1)(m-2)Q'''R-3(m-1)(m-2)(n-2)Q''R'+3(m-2)(n-1)(n-2)Q'R''
-n(n-1)(n-2)QR'''\).
Evidence: the general formula (5.10) with \(r=3\) gives the terms
\(3!\,(-1)^k\binom{n-3+k}k\binom{m-k}{3-k}Q^{(3-k)}R^{(k)}\), \(k=0,\dots,3\): the coefficients are
\(m(m-1)(m-2)\), \(-3(n-2)(m-1)(m-2)\), \(3(n-1)(n-2)(m-2)\) and \(-n(n-1)(n-2)\), multiplying
\(Q'''R\), \(Q''R'\), \(Q'R''\) and \(QR'''\). As printed the third term has no derivatives and the
last has the wrong order.
Published: [Olver CIT corrections], p. 90, third formula of (5.11). Same correction.
Target: [O99.05.2.01].

### Conventions and notation (not errata)

- Definition 5.2: \((Q,R)^{(r)}\) carries no normalizing factor, so \(H=\frac12(Q,Q)^{(2)}\) and the
  constants in (2.47), (2.48), Exercise 5.3 refer to this normalization.
- (5.10)–(5.16): primes are derivatives in \(p\), and the degree \(n\) of \(Q\) (as a form) enters the
  coefficients; e.g. \(H\) of \(Q(p)=p\) regarded as a quartic is \(-9\), not \(0\).
- §5.3: symbolic letters label variable slots; repeated functions in a tensor product occupy
  distinct slots, and \(\Omega_{\alpha\alpha}=0\).

## Chapter 6. Symbolic Methods

### O99-E06.4.01. Sign of the bracket matrix factorization

Status: Confirmed.
Location: §6.4, p. 111, Example 6.20.
Printed: a factorization of the matrix of brackets as a product of the matrix of symbolic
variables with a second factor whose columns are \((-\eta,\xi)\), stated to equal the bracket
matrix.
Correct: with the second factor's columns taken as \((\eta,-\xi)\), the product equals the bracket
matrix \(([\alpha\beta])\); the printed right-hand side equals its negative. The conclusion that the
determinant vanishes is unaffected.
Evidence: multiplying out the \(3\times3\) case entrywise: the \((\alpha,\beta)\) entry of the printed
product is \(\xi_\beta\eta_\alpha-\eta_\beta\xi_\alpha=-[\alpha\beta]\) with
\([\alpha\beta]=\xi_\alpha\eta_\beta-\eta_\alpha\xi_\beta\).
Target: [O99.06.4.03].

### O99-E06.5.01. Constant in the symbolic form of the cubic discriminant

Status: Confirmed.
Location: §6.5, p. 117, Example 6.26, (6.38).
Printed: \(\Delta=\tfrac1{1296}\operatorname{tr}\big(\Omega_{\alpha\beta}^2\Omega_{\alpha\gamma}
\Omega_{\beta\delta}\Omega_{\gamma\delta}^2\big)(Q\otimes Q\otimes Q\otimes Q)\), with symbolic form
\([\alpha\beta]^2[\alpha\gamma][\beta\delta][\gamma\delta]^2\) for \(\Delta\).
Correct: \(\operatorname{tr}\big(\Omega_{\alpha\beta}^2\Omega_{\alpha\gamma}\Omega_{\beta\delta}
\Omega_{\gamma\delta}^2\big)(Q^{\otimes4})=-2592\,\Delta\), so
\(\Delta=-\tfrac1{2592}\operatorname{tr}(\cdots)\); the bracket monomial is the symbolic form of
\(-2\Delta\).
Evidence: exact evaluation for the generic cubic \(Q=\sum\binom3ia_ix^iy^{3-i}\) with
\(\Delta=a_0^2a_3^2-6a_0a_1a_2a_3+4a_0a_2^3+4a_1^3a_3-3a_1^2a_2^2\) as in (2.22): the trace
equals \(-2592\Delta\) identically in \(a_0,\dots,a_3\).
Target: [O99.06.5.05].

### O99-E06.6.01. Index conditions in the polarization rule (6.40) and the Capelli identity (6.42)

Status: Confirmed.
Location: §6.6, p. 118, (6.40) and (6.42).
Printed: \(\pi_{\alpha\beta}[\gamma\delta]=[\alpha\delta]\) if \(\beta=\gamma\), \([\gamma\alpha]\) if
\(\beta=\delta\), \(0\) otherwise; and \((\pi_{\alpha\alpha}+1)\pi_{\beta\beta}-\pi_{\beta\alpha}
\pi_{\alpha\beta}=[\alpha\beta]\,\Xi_{\alpha\beta}\), without conditions on the indices.
Correct: (6.40) holds for \(\alpha\ne\beta\) and \(\gamma\ne\delta\); (6.42) holds for
\(\alpha\ne\beta\).
Evidence: for \(\gamma=\delta=\beta\ne\alpha\), \([\beta\beta]=\xi_\beta\eta_\beta-\eta_\beta\xi_\beta=0\),
so \(\pi_{\alpha\beta}[\beta\beta]=0\), while the first case of (6.40) gives \([\alpha\beta]\ne0\).
For \(\alpha=\beta\) in (6.42), the left side is \((\pi_{\alpha\alpha}+1)\pi_{\alpha\alpha}-
\pi_{\alpha\alpha}^2=\pi_{\alpha\alpha}\), which is nonzero on \(\xi_\alpha\), while the right side
contains \([\alpha\alpha]=0\).
Published: [Olver CIT corrections], p. 118, (6.40) and (6.42). Same correction.
Target: [O99.06.6.01], [O99.06.6.02].

### O99-E06.7.01. Sign of the covariant derivative bracket

Status: Confirmed.
Location: §6.7, p. 123, after (6.52).
Printed: replacing \(\xi_\beta\) in \([\alpha\beta]\) by the modified gradient gives \(\pi_{\alpha\beta}\).
Correct: the substitution gives \(-\pi_{\alpha\beta}\).
Evidence: with \([\alpha\beta]=\xi_\alpha\eta_\beta-\eta_\alpha\xi_\beta\), carrying out the
substitution defined on p. 123 term by term gives the negative of the operator \(\pi_{\alpha\beta}\)
as defined in (6.52).
Target: [O99.06.7.01].

### O99-E06.8.01. Sign in the Stroh identity (6.61)

Status: Confirmed.
Location: §6.8, p. 127, (6.61).
Printed: \(nM=(n-p-q+1)[\cdots][\gamma\delta]+(n-q-r+1)[\cdots][\alpha\delta]\).
Correct: \(nM=-(n-p-q+1)[\cdots][\gamma\delta]+(n-q-r+1)[\cdots][\alpha\delta]\).
Evidence: evaluating both sides as transvectant expressions for the generic quintic (\(n=5\)) with
\((p,q,r)=(3,2,2)\) and \((2,1,1)\): the identity holds with the minus sign and fails with the
printed sign.
Target: [O99.06.8.03].

### Conventions and notation (not errata)

- The classical texts multiply the transvectant by falling-factorial normalizing factors; the
  source and the synopsis use the unnormalized transvectant, so constants differ from classical
  tables by these factors.

## Chapter 7. Graphical Methods

### O99-E07.3.01. Coefficients in the rational expression of Z (7.11)

Status: Confirmed.
Location: §7.3, p. 140, Exercise 7.7, (7.11).
Printed: \(QZ\) expressed with coefficients \(\tfrac{6(n-2)}n\) of \(T^2\),
\(\tfrac{3(n-2)^3}{n(n-1)^2}\) of \(H^3\) and \(\tfrac n{n-3}\) of \(Q^2HI\).
Correct: \(QZ=-\tfrac{3(n-2)}nT^2-\tfrac{12(n-2)^3}{n(n-1)^2}H^3+\tfrac{2n}{n-3}Q^2HI\), with
\(Z=(H,T)^{(1)}\).
Evidence: exact computation for generic forms of degree \(n=4,5,6\); the three coefficients are
determined uniquely by the fit, and the corrected rational functions of \(n\) reproduce all three
cases.
Target: [O99.07.3.03].

### O99-E07.3.02. Right-hand side of (7.12)

Status: Confirmed.
Location: §7.3, p. 140, Exercise 7.8, (7.12).
Printed: the right-hand side of (7.12) for \(Q^3J\) is identical to that of (7.11).
Correct: \(Q^3J=-\tfrac{6(n-2)(n-3)^3}{n^3(n-1)}T^2-\tfrac{24(n-2)^3(n-3)^3}{n^3(n-1)^3}H^3+
\tfrac{6(n-2)(n-3)}{n(n-1)}Q^2HI\), with \(J\) the triangle covariant of Exercise 7.8.
Evidence: exact computation for generic forms of degree \(n=4,\dots,8\); the corrected
coefficients reproduce all five cases.
Target: [O99.07.3.04].

### O99-E07.4.01. Definition of resonance

Status: Confirmed.
Location: §7.4, p. 140, Definition 7.9 and the following remark.
Printed: resonance is defined by an integer relation among the degrees in which the integer
vector \(k\) is not required to be nonzero; a following remark says that systems with irrational
degrees are non-resonant.
Correct: the combination must be nontrivial (\(k\ne0\)); otherwise every system is resonant. The
claim about irrational degrees is false.
Evidence: \(k=0\) satisfies the printed condition for every system. The degrees \(\sqrt2\) and
\(2-\sqrt2\) are irrational, but their sum is the integer \(2\), which gives a relation of the
type in Definition 7.9 with \(k\ne0\).
Target: [O99.07.4.01].

### O99-E07.4.02. Sign of the d-term in the partial transvectant identity

Status: Confirmed.
Location: §7.4, p. 141, operator identity and traced formula before Theorem 7.10.
Printed: \(\operatorname{tr}\Omega_{\alpha\beta}(\Omega_{\beta\gamma})^s=\tfrac{e-s}{e+f-2s}
(P,(Q,R)^{(s)})^{(1)}+\tfrac d{e+f-2s}P(Q,R)^{(s+1)}\).
Correct: \(\operatorname{tr}\Omega_{\alpha\beta}(\Omega_{\beta\gamma})^s=\tfrac{e-s}{e+f-2s}
(P,(Q,R)^{(s)})^{(1)}-\tfrac d{e+f-2s}P(Q,R)^{(s+1)}\) (degrees \(d,e,f\) of \(P,Q,R\)).
Evidence: evaluation with generic polynomials of several degrees \((d,e,f)\) and \(s=1,2\); the
identity holds only with the minus sign.
Target: [O99.07.4.02].

### O99-E07.4.03. Coefficients in the arc-moving formula (7.15)

Status: Confirmed.
Location: §7.4, p. 142, Lemma 7.11, (7.15).
Printed: the coefficients \(v_\lambda-k_\lambda\) and \(v_\mu-k_\mu\) multiply \(F_I\) and \(F_J\)
respectively.
Correct: \((v_\lambda-k_\lambda)F_J=(v_\mu-k_\mu)F_I+(v_0-r+1)\tilde F_K\).
Evidence: multiplying by \(v^K\) and comparing with (7.14), only the corrected form is consistent;
it also agrees with the worked example on p. 141.
Target: [O99.07.4.03].

### O99-E07.5.01. Cubic discriminant as a transvectant

Status: Confirmed.
Location: §7.5, p. 146, Example 7.16.
Printed: \(\Delta=\tfrac16(Q,T)^{(3)}\).
Correct: \((Q,T)^{(3)}=-7776\,\Delta\), so \(\Delta=-\tfrac1{7776}(Q,T)^{(3)}\).
Evidence: exact computation for the generic cubic with \(H=\tfrac12(Q,Q)^{(2)}\), \(T=(Q,H)^{(1)}\)
and the source's \(\Delta\).
Target: [O99.07.5.03].

### O99-E07.5.02. Coefficient of JQ in the reduced discriminant digraph

Status: Confirmed.
Location: §7.5, p. 148.
Printed: final coefficient of \(JQ\) equal to \(\tfrac{n(n-1)(n-2)}{2(n-3)^3}\); intermediate
values \(A=-\tfrac{n-2}{n-3}IH\) and \(B=\tfrac12[\cdots]\).
Correct: the coefficient of \(JQ\) is \(\tfrac{n(n-1)(n-2)}{3(n-3)^3}\); the coefficient
\(-\tfrac{2(n-2)^2}{(n-3)^2}\) of \(IH\) is correct. The intermediate values \(A\), \(B\) are not
consistent with the final result.
Evidence: exact computation for generic forms of degree \(n=4,\dots,7\).
Target: [O99.07.5.04].

### O99-E07.5.03. The quartic covariant U (7.17)

Status: Confirmed.
Location: §7.5, p. 149, Exercise 7.18, (7.17).
Printed: \(U=2^93^2Q(108jQ-iH)\).
Correct: \(U=(Q,T)^{(1)}=2^93^2iQ^2-\tfrac83H^2\). The printed expression has order 5 in the
coefficients whereas \(U\) has order 4. Separately, \((H,T)^{(1)}=2^{10}3^2Q(216jQ-iH)\).
Evidence: exact computation for the generic quartic with \(i=\tfrac1{1152}(Q,Q)^{(4)}\),
\(j=\tfrac1{12^5}(Q,H)^{(4)}\).
Target: [O99.07.5.06].

### Conventions and notation (not errata)

- Digraphs with double bonds represent repeated brackets \([\alpha\beta]^2\).
- On p. 137 an intermediate step "\(-D=2TH+D\)" is inconsistent, but the final result \(D=TH\)
  is correct.
- In Example 7.16 "the first digraph is equivalent to \(-H^2\)" is loose: for the cubic it equals
  \(-\tfrac12H^2\) in the source's normalization.

## Chapter 8. Lie Groups and Moving Frames

### O99-E08.3.01. The irrational torus flow is not free

Status: Confirmed.
Location: §8.3, p. 158, Example 8.15.
Printed: for irrational \(\alpha\) the action of \(\mathbb R\) on \(\mathbb R^4\) is free (regular).
Correct: points with \(x=y=0\) are fixed by \(t=2\pi/\alpha\), and the origin is fixed by all \(t\);
the action is free only on the set where both planes have nonzero components, and regular only on
\(\mathbb R^4\setminus\{0\}\).
Evidence: the action rotates \((x,y)\) by angle \(t\) and \((z,w)\) by \(\alpha t\); at
\((0,0,z,w)\) the element \(t=2\pi/\alpha\) acts trivially.
Target: [O99.08.3.03].

### O99-E08.5.01. Distances do not determine SE(2)-equivalence

Status: Confirmed.
Location: §8.5, p. 168.
Printed: two configurations of points are \(SE(2)\)-equivalent iff their mutual distances agree,
"provided the points do not all lie on a single triangle".
Correct: equal mutual distances characterize \(E(2)\)-equivalence; \(SE(2)\)-equivalence needs in
addition the orientation (sign of the signed areas), except when all points are collinear.
Evidence: \((0,0),(1,0),(0,1)\) and its mirror image \((0,0),(1,0),(0,-1)\) have the same mutual
distances, but no rotation-translation maps one to the other with the labelling preserved.
Target: [O99.08.5.01].

### O99-E08.8.01. Sign of the derivative of J (8.42)

Status: Confirmed.
Location: §8.8, p. 180, (8.42).
Printed: \(dJ/ds\) with the sign opposite to the correct one.
Correct: with \(d/ds=(Q/\sqrt H)\,d/dp\) from (8.41),
\(\dfrac{dJ}{ds}=\dfrac{3T^2}{2nH^3}-\dfrac U{nH^2}=\dfrac1n\big(\tfrac32J^2-K\big)\).
Alternatively the printed formula holds with the opposite orientation of \(ds\).
Evidence: numerical evaluation at random coefficients and points for \(n=4,5,6\).
Target: [O99.08.8.04].

### O99-E08.8.02. Invariant differentiation formulas (8.43)–(8.45)

Status: Confirmed.
Location: §8.8, p. 181, (8.43)–(8.45).
Printed: \(m\) is called the weight of \(Z\); the second equality of (8.43) and the first term of
(8.45) carry a plus sign.
Correct: \(m\) must be the degree of \(Z\) (for the \(Z_m\) family the degree is \((n-2)\) times the
weight). With \(m\) the degree, the second equality of (8.43) needs a minus sign, (8.44) is
correct, and
\(\dfrac{dN}{ds}=-\dfrac{(Q,Z)^{(1)}}{nH^{(m+n-2)/(2n-4)}}+\dfrac m{n(2n-4)}JN\).
Evidence: numerical evaluation for several \(Z\) (\(Z=Q,H,T\)) and \(n=4,5\).
Target: [O99.08.8.05].

### O99-E08.8.03. Factorial in the prolonged action (8.32)

Status: Confirmed.
Location: §8.8, p. 178, (8.32).
Printed: \(\bar Q^{(m)}=\dfrac1{\Delta^m\sigma^{n-m}}\sum_{j=0}^m(-1)^{m-j}\binom mj
\dfrac{(n-j)!}{(m-j)!}\gamma^{m-j}\sigma^jQ^{(j)}\).
Correct: the factor is \(\dfrac{(n-j)!}{(n-m)!}=(n-j)(n-j-1)\cdots(n-m+1)\), the falling factorial
of length \(m-j\).
Evidence: for \(m=1\) the printed \(j=0\) term is \(-n!\,\gamma u\), while (8.31) gives
\(\bar v=(\sigma v-n\gamma u)/(\Delta\sigma^{n-1})\); for \(m=2\), \(j=0\), the printed factor
\(n!/2\) differs from \(n(n-1)\) in \(\bar w\). With \((n-j)!/(n-m)!\) the formula reproduces all four
displays \(\bar v,\bar w,\bar z,\bar y\) of (8.31), e.g. for \(m=3\) the coefficients
\(-n(n-1)(n-2)\), \(3(n-1)(n-2)\), \(-3(n-2)\), \(1\).
Published: [Olver CIT corrections], p. 178, (8.32). Same correction.
Target: [O99.08.8.01].

### O99-E08.8.04. The moving frame entries \(\gamma\), \(\delta\) (8.37)

Status: Confirmed.
Location: §8.8, p. 179, (8.37).
Printed: \(\gamma=\frac1nQ^{(1-n)/n}\), \(\delta=Q^{1/n}-\frac1npQ^{(1-n)/n}\).
Correct: \(\gamma=\frac1nQ^{(1-n)/n}Q'\), \(\delta=Q^{1/n}-\frac1npQ^{(1-n)/n}Q'\).
Evidence: (8.35) gives \(\gamma=\frac1nu^{(1-n)/n}v\) with \(v=Q'(p)\), and (8.34) gives
\(\delta=\sqrt[n]u-\gamma p\); the printed \(\gamma\) contradicts (8.35) unless \(Q'=1\), and the
printed \(\delta\) is \(\sqrt[n]u-\gamma p\) with the printed \(\gamma\). With the printed \(\gamma\)
the normalization \(\bar v=0\) fails: by (8.31), \(\bar v\) is proportional to \(\sigma v-n\gamma u
=Q^{1/n}(Q'-1)\).
Published: [Olver CIT corrections], p. 179, (8.37). Same correction.
Target: [O99.08.8.02].

### O99-E08.9.01. Derivative of the ellipse curvature (8.51)

Status: Confirmed.
Location: §8.9, p. 184, Example 8.54, (8.51).
Printed: \(\kappa_s=\dfrac{3(r^2-1)xy}{r\,(a^2+(r^2-1)x^2)^{3}}\).
Correct: \(\kappa_s=\dfrac{3a^2(r^2-1)xy}{(a^2+(r^2-1)x^2)^3}\). With this \(\kappa_s\) the signature
relation (8.52) holds; with the printed one it fails, and the printed expression has the wrong
dimension in \(a\).
Evidence: direct differentiation of \(\kappa\) along the ellipse parametrization, and numerical
check of (8.52) at sample points.
Target: [O99.08.9.03].

### O99-E08.11.01. Sign of T for a monomial (8.57)

Status: Confirmed.
Location: §8.11, p. 190, (8.57).
Printed: \(T=-2(n-1)k(n-k)(2k-n)p^{3k-3}\).
Correct: \(T=2(n-1)k(n-k)(2k-n)p^{3k-3}\); \(H\), \(U\), \(J^2\), \(K\) are as printed.
Evidence: \(T=(Q,H)^{(1)}=nQ'H-(2n-4)QH'\) for \(Q=p^k\),
\(H=-(n-1)k(n-k)p^{2k-2}\) gives \(-(n-1)k(n-k)[nk-(2n-4)(k-1)]p^{3k-3}\)
\(=2(n-1)k(n-k)(2k-n)p^{3k-3}\).
Target: [O99.08.11.04].

### O99-E08.11.02. The subresultant index test counts base-locus roots

Status: Confirmed.
Location: §8.11, pp. 192–193, (8.60)–(8.62), Theorem 8.67; Corollary 8.68(a).
Printed: the index \(k\) of a nonsingular binary form is \(\deg\) of the gcd (computed by
subresultants) of \(A=H(q)^3T(p)^2-T(q)^2H(p)^3\) and \(B=H(q)^2U(p)-U(q)H(p)^2\) in \(p\), and
\(k=6n-12\) is maximal.
Correct: common zeros of \(H,T,U\) (in particular every multiple root of \(Q\)) are common roots of
\(A,B\) for every \(q\), although they lie outside the signature domain \(H\ne0\); these factors,
and multiplicities, must be removed before counting. The bound \(k\le4n-8\) for the symmetry index
remains valid. Whether the value \(6n-12\) is attained when \(Q\) has multiple roots is not
settled here.
Evidence: \(Q=x^2y(x-y)\) (roots of multiplicity \(2,1,1\), not equivalent to a monomial). In the
chart \(y=1\): \(H=-3p^2(3p^2-4p+4)\), \(T=36p^5(p-2)\), \(U=-72p^6(3p^2-8p+8)\). Over
\(\mathbb Q(q)\), \(\gcd_p(A,B)=p^4(p-q)(pq-p-q)\); the subresultant degrees are \(12,8,7,6\), so
the printed test gives index \(6\), whereas the true index (number of admissible solutions) is
\(2\).
Published: [Olver CIT corrections], pp. 192–193, polynomials \(A\) and \(B\): common factors of the
rational covariants must be cancelled before multiplying out; and p. 193, Corollary 8.68(a), which
should read only \(k\le6n-12\), equality failing when \(A(p,q)=0\) has multiple roots or \(T\) and
\(H\) have common factors (details in Berchenko–Olver, *Symmetries of polynomials*, J. Symb. Comp.
29 (2000) 485–514). This agrees with the correction above and the bound stated in the synopsis.
Target: [O99.08.11.06], [O99.08.11.07].

### O99-E08.11.03. J in the quartic signature curve (8.70)

Status: Confirmed.
Location: §8.11, p. 195, Example 8.70, (8.70).
Printed: \(9j^2(K+\tfrac83)^3=2i^3(K-\tfrac12J+\tfrac{16}9)^2\).
Correct: \(9j^2(K+\tfrac83)^3=2i^3(K-\tfrac12J^2+\tfrac{16}9)^2\), where \(J^2=T^2/H^3\) is the
signature coordinate of (8.69).
Evidence: eliminating \(S\) from (8.69), \(J^2=-\tfrac{16}9+4iS^2-12jS^3\),
\(K=-\tfrac83+2iS^2\): then \(K-\tfrac12J^2+\tfrac{16}9=6jS^3\) and \((K+\tfrac83)^3=8i^3S^6\),
which gives the corrected relation.
Published: [Olver CIT corrections], p. 195, (8.70). Same correction.
Target: [O99.08.11.10].

### Conventions and notation (not errata)

- Example 8.14 (discriminant classifies quadratics) holds over \(\mathbb C\); over \(\mathbb R\),
  \(\pm(x^2+y^2)\) have equal discriminants but are not equivalent.
- Theorem 8.66 counts symmetry groups modulo the kernel \(\{\lambda\mathbb 1:\lambda^n=1\}\) of the
  action.
- In Example 8.69 (p. 195) the letter \(J\) denotes \(J^2=T^2/H^3\).
- The cubic signature segment includes the point \(a=0\) at the real zeros of \(T\).
- On p. 180 \(dx\) is written for \(d\bar p\).
- In Theorem 8.61 "weight \(n\)" is the source's wording for the representation \(\rho_{n,0}\).

## Chapter 9. Infinitesimal Methods

### O99-E09.1.01. Real logarithms of 2 x 2 matrices (Exercise 9.6)

Status: Confirmed.
Location: §9.1, p. 201, Exercise 9.6.
Printed: a real \(2\times2\) matrix is the exponential of a real matrix iff either both eigenvalues
are positive, or the matrix is diagonalizable and has only one negative eigenvalue.
Correct: iff its eigenvalues are a non-real conjugate pair, or both are positive, or the matrix is
\(\lambda\mathbb 1\) with \(\lambda<0\) (consistent with Proposition 9.5).
Evidence: the rotation \(\begin{pmatrix}0&-1\\1&0\end{pmatrix}=\exp\begin{pmatrix}0&-\pi/2\\
\pi/2&0\end{pmatrix}\) has eigenvalues \(\pm i\), neither positive nor negative.
Target: [O99.09.1.03].

### O99-E09.4.01. Ambient space in the infinitesimal invariance criterion (Theorem 9.28)

Status: Confirmed.
Location: §9.4, p. 210, Theorem 9.28.
Printed: "Let \(G\subset GL(n)\) be a connected Lie group acting on \(X\subset\mathbb R^n\)."
Correct: \(G\subset GL(n)\) acting on \(X\subset\mathbb R^m\), with \(m\) unrelated to \(n\).
Evidence: the chapter's transformation groups act on \(X\subset\mathbb R^m\) (p. 208, Theorem
9.21), and the theorem is applied to \(SL(2)\subset GL(2)\) acting on the space of binary forms of
degree \(n\), of dimension \(n+1\) (Proposition 9.33, p. 213), and on \((\mathbf a,\mathbf x)\)-space
(Theorem 9.34). As printed the hypothesis excludes these applications.
Published: [Olver CIT corrections], p. 210, Theorem 9.28. Same correction.
Target: [O99.09.4.01].

### O99-E09.6.01. Leading coefficient of the cubic (Example 9.47)

Status: Confirmed.
Location: §9.6, p. 219, Example 9.47.
Printed: \(\hat Q=a_0\).
Correct: \(\hat Q=a_3\), the coefficient of \(x^3\) (with \(Q=\sum\binom3ia_ix^iy^{3-i}\)). The
printed \(\hat H\) and \(\hat T\) are correct, and \(\hat T^2+\hat H^3=2^43^6\hat Q^2\Delta\) holds
with \(\hat Q=a_3\).
Evidence: \(Q(x,0)=a_3x^3\). For \(a=(a_0,a_1,a_2,a_3)=(1,1,0,2)\): \(\hat H=36\cdot2=72\),
\(\hat T=108\cdot4=432\), \(\hat T^2+\hat H^3=559872\), \(\Delta=a_0^2a_3^2-6a_0a_1a_2a_3+4a_0a_2^3+
4a_1^3a_3-3a_1^2a_2^2=12\); then \(2^43^6a_3^2\Delta=559872\), while \(2^43^6a_0^2\Delta=139968\).
Published: [Olver CIT corrections], p. 219, last line. Same correction.
Target: [O99.09.6.04].

### O99-E09.6.02. Leading terms are not semi-invariants (Proposition 9.45, Theorem 9.49)

Status: Confirmed.
Location: §9.6, pp. 217–219, Definition 9.40, (9.45), Proposition 9.45; §9.7, p. 221,
Theorem 9.49.
Printed: a semi-invariant is a function invariant under the upper triangular unimodular group
\(U\), so \(\mathbf v_-(F)=0=\mathbf v_0(F)\) (9.45); "the leading term of any polynomial covariant
is a semi-invariant" (Proposition 9.45), its leading coefficient a "relative semi-invariant of
weight \(n\)"; Theorem 9.49 assumes that \(L(\mathbf a,x)=K(\mathbf a)x^n\) is a
\(y\)-independent semi-invariant.
Correct: the leading coefficient \(K(\mathbf a)\) of a covariant of degree \(d\) is a
semi-invariant in the classical sense, a relative invariant of \(U\): \(\mathbf v_-(K)=0\),
\(\mathbf v_0(K)=dK\) (index \(d\)). The leading term \(L=Kx^d\) satisfies \(\mathbf v_0(L)=0\) but
\(\mathbf v_-(L)=-dKx^{d-1}y\ne0\), so it is not \(U\)-invariant. Theorem 9.49 holds with the
hypothesis that \(K\) is a polynomial semi-invariant of index \(d\) in this sense; then
\((\mathbf v_+)^{d+1}K=0\) and (9.51) is the covariant with leading term \(Kx^d\). Under (9.32),
\(\mathbf v_0\) multiplies the monomial \(a_{i_1}\cdots a_{i_o}\) by \(2(i_1+\cdots+i_o)-on\), so the
index of an isobaric polynomial of order \(o\) and classical weight \(w=i_1+\cdots+i_o\) is
\(2w-on\); the invariants of Definition 9.40 are the semi-invariants of index \(0\).
Evidence: for the cubic covariant \(J=Q\) (\(d=3\)), \(K=a_3\) and \(L=a_3x^3\); by (9.32)
\(\mathbf v_-(a_3)=0\), \(\mathbf v_0(a_3)=3a_3\), \(\mathbf v_0(a_3x^3)=3a_3x^3-3a_3x^3=0\) and
\(\mathbf v_-(a_3x^3)=-3a_3x^2y\). In the proof of Proposition 9.45 the identity
\(J(\mathbf a,\lambda x,0)=J(\bar{\mathbf a},x,0)\) uses only \(y=0\), where the shear
\(x\mapsto\lambda x+\beta y\) acts trivially. In general a nonzero \(y\)-independent \(L=Kx^d\),
\(d\ge1\), always has \(\mathbf v_-(L)\ne0\), since the term \(-y\,\partial_xL\) cannot cancel
against \(\mathbf v_-(K)x^d\); so the hypothesis of Theorem 9.49 as printed is never met. For the
corrected hypothesis, \(K_k=(\mathbf v_+)^kK\) satisfies \(\mathbf v_0K_k=(d-2k)K_k\) and
\(\mathbf v_-K_k=k(d-k+1)K_{k-1}\) by [O99-E09.7.01]; the nonzero \(K_k\) have distinct
\(\mathbf v_0\)-eigenvalues and lie in the finite-dimensional space of polynomials of the order of
\(K\), so some \(K_{N+1}=0\ne K_N\), and \(0=\mathbf v_-K_{N+1}=(N+1)(d-N)K_N\) gives \(N=d\).
Published: [Olver CIT corrections], pp. 218–221, comment on semi-invariants: same correction of
the definition (index \(2\operatorname{wt}F-\operatorname{ord}F\cdot\deg Q\), with \(\operatorname{wt}\)
the classical weight), of Proposition 9.45 and of the proof of \((\mathbf v_+)^{n+1}K=0\) in
Theorem 9.49.
Target: [O99.09.6.01], [O99.09.6.03], [O99.09.7.03].

### O99-E09.7.01. Sign of v0 in the commutation formulas (9.47)–(9.49)

Status: Confirmed.
Location: §9.7, p. 220, (9.47)–(9.49); p. 221, proof of Theorem 9.49 ("\(\mathbf v_0(K)=-nK\)");
p. 222, proof of Theorem 9.52.
Printed: \(\mathbf v_0\mathbf v_-=\mathbf v_-(\mathbf v_0-2)\),
\(\mathbf v_0\mathbf v_+=\mathbf v_+(\mathbf v_0+2)\), \(\mathbf v_+\mathbf v_-=\mathbf v_-\mathbf
v_++\mathbf v_0\), stated as a rewriting of (9.19); correspondingly
\(\mathbf v_0(\mathbf v_\mp)^k=(\mathbf v_\mp)^k(\mathbf v_0\mp2k)\),
\(\mathbf v_+(\mathbf v_-)^k=(\mathbf v_-)^k\mathbf v_++(\mathbf v_-)^{k-1}[k\mathbf v_0-k(k-1)]\),
\(\mathbf v_-(\mathbf v_+)^k=(\mathbf v_+)^k\mathbf v_-+(\mathbf v_+)^{k-1}[-k\mathbf v_0-k(k-1)]\),
and \(\mathbf v_0(K)=-nK\) for the leading coefficient.
Correct: (9.19) (and the operators (9.32)) give \(\mathbf v_0\mathbf v_-=\mathbf v_-(\mathbf
v_0+2)\), \(\mathbf v_0\mathbf v_+=\mathbf v_+(\mathbf v_0-2)\), \(\mathbf v_+\mathbf v_-=\mathbf
v_-\mathbf v_+-\mathbf v_0\), hence \(\mathbf v_0(\mathbf v_\mp)^k=(\mathbf v_\mp)^k(\mathbf
v_0\pm2k)\), \(\mathbf v_+(\mathbf v_-)^k=(\mathbf v_-)^k\mathbf v_+-(\mathbf v_-)^{k-1}[k\mathbf
v_0+k(k-1)]\), \(\mathbf v_-(\mathbf v_+)^k=(\mathbf v_+)^k\mathbf v_-+(\mathbf v_+)^{k-1}[k\mathbf
v_0-k(k-1)]\), and \(\mathbf v_0(K)=+dK\) for a covariant of degree \(d\). The printed formulas are
those for \(-\mathbf v_0\). Lemma 9.48, (9.51), the Hilbert operators (9.52), Theorem 9.52 and the
key identity \(\mathbf v_-(\mathbf v_+)^k(\mathbf v_-)^kF=(\mathbf v_+)^k(\mathbf v_-)^{k+1}F+
k(k+1)(\mathbf v_+)^{k-1}(\mathbf v_-)^kF\) (isobaric \(F\)) are unaffected.
Evidence: for the binary cubic with (9.32), direct symbolic computation on a generic function
gives \([\mathbf v_-,\mathbf v_0]=-2\mathbf v_-\), \([\mathbf v_+,\mathbf v_0]=2\mathbf v_+\),
\([\mathbf v_-,\mathbf v_+]=\mathbf v_0\) as in (9.19). On \(F=a_0^2a_2xy^3+a_1x^2\) the printed
\(\mathbf v_0\mathbf v_-F=\mathbf v_-(\mathbf v_0-2)F\) fails and the corrected one holds; the
corrected forms of (9.49) hold for \(k=1,2,3\). For \(K=a_1a_3-a_2^2\) (leading coefficient of
\(\tfrac1{36}H\), \(d=2\)), \(\mathbf v_0K=2K\).
Published: [Olver CIT corrections], p. 220, (9.47)–(9.49), and p. 221, line −5
(\(\mathbf v_0(K)=nK\)) with the corrected proof steps of Theorems 9.49 and 9.52 that the list
places on p. 221 (in this copy the displays for \(\mathbf v_-\{(\mathbf v_+)^kK\}\) and
\(\mathbf v_-(\mathbf v_+)^k(\mathbf v_-)^k\) are on p. 222). Same correction; the list's bottom
display confirms that the key identity with \(+k(k+1)\) is unaffected.
Target: [O99.09.7.01].

### Conventions and notation (not errata)

- In Example 9.31 (p. 213) the displayed coefficient transformation rules, differentiated at
  \(t=0\), give \(-\mathbf v_+,-\mathbf v_0,-\mathbf v_-\) in the order listed rather than
  \(\mathbf v_-,\mathbf v_0,\mathbf v_+\) "respectively"; the generators (9.27) themselves agree
  with (9.12) and (9.28).
- In Proposition 9.45 and Theorem 9.49 the letter \(n\) denotes the degree of the covariant \(J\),
  not necessarily the degree of the form \(Q\); "weight \(n\)" of the semi-invariant \(K\) means
  \(K(\bar{\mathbf a})=\lambda^{-n}K(\mathbf a)\) under \(U\).
- Lemma 9.44 says "invertible" for the map to leading terms; it is injective, and Theorem 9.49
  identifies its image with the polynomials \(K(\mathbf a)x^d\) whose coefficient \(K\) is a
  semi-invariant of index \(d\) (see [O99-E09.6.02]).

## Chapter 10. Multivariate Polynomials

### O99-E10.1.01. Factor 2 in the ternary quadratic (10.3)

Status: Confirmed.
Location: §10.1, p. 231, (10.3), (10.4); used in §10.4, pp. 237–238, (10.18), (10.19).
Printed: \(Q=ax^2+2bxy+cy^2+dxz+eyz+fz^2\), \(Q(p,q)=ap^2+2bpq+cq^2+dp+eq+f\), and
\(\Delta=\tfrac18H[Q]=\det\begin{pmatrix}a&b&d\\b&c&e\\d&e&f\end{pmatrix}\), described as a
multiple of the determinant of the coefficient matrix.
Correct: \(Q=ax^2+2bxy+cy^2+2dxz+2eyz+fz^2\) and \(Q(p,q)=ap^2+2bpq+cq^2+2dp+2eq+f\); then the
coefficient matrix is \(M=\begin{pmatrix}a&b&d\\b&c&e\\d&e&f\end{pmatrix}\), \(\tfrac18H[Q]=\det M\),
and (10.19) is built on \(M\).
Evidence: for the printed (10.3) the Hessian matrix is
\(\begin{pmatrix}2a&2b&d\\2b&2c&e\\d&e&2f\end{pmatrix}\); at \(a=c=f=d=1\), \(b=e=0\) its
determinant is \(6\) while \(8\det M=0\). With \(2dxz+2eyz\) the Hessian matrix is \(2M\) and
\(H[Q]=8\det M\) identically.
Target: [O99.10.1.03], [O99.10.4.03].

### O99-E10.5.01. Signs in the second fundamental theorem relations (10.23), (10.24)

Status: Confirmed.
Location: §10.5, p. 240, (10.23), (10.24).
Printed: \(\sum_{j=1}^{p+1}[\alpha_1\cdots\alpha_{j-1}\alpha_{j+1}\cdots\alpha_{p+1}]
[\alpha_j\beta_1\cdots\beta_{p-1}]=0\) and
\(\sum_{j=1}^{p+1}[\alpha_1\cdots\alpha_{j-1}\alpha_{j+1}\cdots\alpha_{p+1}](\alpha_j\mathbf x)=0\).
Correct: both sums carry the sign \((-1)^j\).
Evidence: \(m=p=2\), \(\alpha_1=(1,0)\), \(\alpha_2=(0,1)\), \(\alpha_3=(1,1)\), \(\beta_1=(1,0)\): the
three terms of the printed (10.23) are \(0,-1,-1\) (sum \(-2\)); with signs \(0+1-1=0\). For
(10.24) with \(\mathbf x=(0,1)\): printed terms \(0,1,1\) (sum \(2\)); with signs \(0-1+1=0\).
Target: [O99.10.5.02].

### O99-E10.6.01. Constant in the cubic invariant J of the biquadratic

Status: Confirmed.
Location: §10.6, p. 243, display for \(J\).
Printed: \(J=\tfrac1{1536}(C,Q)^{(2,2)}=\det(a^{ij}_{kl})\) (the displayed six-term determinant).
Correct: \((C,Q)^{(2,2)}=768\det(a^{ij}_{kl})\), so \(J=\tfrac1{768}(C,Q)^{(2,2)}\) (or the
right-hand side is \(\tfrac12\det\)).
Evidence: exact computation for the generic biquadratic (10.27) with
\(C=\tfrac12(Q,Q)^{(1,1)}=Q_{xu}Q_{yv}-Q_{xv}Q_{yu}\) (verified) and the \((2,2)\)-transvectant
(10.28): \(\tfrac1{1536}(C,Q)^{(2,2)}=\tfrac12\det\). The companion normalizations
\(\Delta_{\mathbf x}=\tfrac12(Q,Q)^{(2,0)}\), \(C\) and \(I=\tfrac1{32}(Q,Q)^{(2,2)}\) check exactly.
Target: [O99.10.6.03].

### O99-E10.6.02. Signs of the discriminants in the example after Proposition 10.22

Status: Confirmed.
Location: §10.6, p. 244, example after Proposition 10.22.
Printed: for \(Q=x^2u^2+xyv^2\), \(\Delta_{\mathbf w}=-4x^3y\) and \(\Delta_{\mathbf x}=v^4\).
Correct: with (10.30), \(\Delta_{\mathbf w}=Q_{uu}Q_{vv}-Q_{uv}^2=4x^3y\) and
\(\Delta_{\mathbf x}=Q_{xx}Q_{yy}-Q_{xy}^2=-v^4\). The root multiplicities stated (triple and simple;
quadruple) are unaffected.
Evidence: \(Q_{uu}=2x^2\), \(Q_{vv}=2xy\), \(Q_{uv}=0\); \(Q_{xx}=2u^2\), \(Q_{yy}=0\),
\(Q_{xy}=v^2\).
Target: [O99.10.6.04].

### O99-E10.6.03. The covariant R_w in the Hilbert basis (10.31)

Status: Confirmed.
Location: §10.6, p. 245, (10.31).
Printed: \(R_{\mathbf w}=(Q,\Delta_{\mathbf w})^{(0,1)}\).
Correct: \(R_{\mathbf w}=(Q,\Delta_{\mathbf w})^{(1,0)}\), the counterpart of
\(R_{\mathbf x}=(Q,\Delta_{\mathbf x})^{(0,1)}\).
Evidence: \(\Delta_{\mathbf w}\) depends only on \(\mathbf x\), so \(\Theta\) annihilates
\(Q\otimes\Delta_{\mathbf w}\) and the printed \((0,1)\)-transvectant vanishes identically.
Target: [O99.10.6.05].

### O99-E10.6.04. Terms of wrong bidegree in the canonical forms

Status: Open check.
Location: §10.6, p. 245, table of canonical forms, forms 3 and 7.
Printed: form 3 \(x^2u^2-x^2v^2+xyu^2+xyuv^2\); form 7 \(x^2u^2+xyuv^2\).
Correct: the term \(xyuv^2\) has bidegree \((2,3)\) and cannot occur in a biquadratic; the
conjectured intended term is \(xyv^2\). Which bidegree-\((2,2)\) monomial is meant should be
checked against the cited classification (reference [165] of the source).
Evidence: bidegree count; checked on the page image at high resolution.
Target: [O99.10.6.05].

### Conventions and notation (not errata)

- On p. 234 "the theorem is true if \(n\le4\)" uses \(n\) for the number of variables (elsewhere
  \(m\)); Hesse's claim holds for \(m\le4\) variables.
- The dual form (10.19) equals \(-\mathbf u^T\operatorname{adj}(M)\mathbf u\); "whose coefficient
  matrix is the adjunct" holds up to sign.
- In (10.27) upper indices of \(a^{ij}_{kl}\) refer to \(\mathbf w=(u,v)\), lower ones to
  \(\mathbf x=(x,y)\).
- The Hilbert basis list (10.31) omits the normalizing constants used in (10.30) and the displays
  for \(C\), \(I\), \(J\).

## Published corrections to material outside the synopses

The published list also corrects the following statement. The synopsis does not state it, so it
has no erratum entry and no synopsis target. It is listed here so that this file accounts for
every mathematical item of the list.

- §2.12, p. 40, table of the numbers of generating invariants and covariants of binary forms of
  degrees \(2,\dots,12\): [Olver CIT corrections], p. 40, states (after A. E. Brouwer) that
  Sylvester's number of invariants for degree \(10\) is \(99\), not \(104\) as printed, that
  Sylvester's counts for degrees \(7,9,10,12\) are understated, and gives the values known in
  2015: invariants \(1,1,2,4,5,30,9,92,106,\ge113\) and covariants
  \(2,4,5,23,26,147,69,\ge476,\ge510,\ge989\) for degrees \(2,3,4,5,6,7,8,9,10,12\). The printed
  value \(104\) was checked on the page image; the counts are numerical data, outside the scope
  of the synopsis.

[Olver CIT corrections]: https://www-users.cse.umn.edu/~olver/book_/invcor.pdf
