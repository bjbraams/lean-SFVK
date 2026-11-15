# Errata and source checks: Olver, Applications of Lie Groups to Differential Equations (1986)

Reference: Peter J. Olver, *Applications of Lie Groups to Differential Equations*, Graduate Texts
in Mathematics 107, Springer-Verlag, New York, first edition, 1986. The local copy is
[Olver 1986](References/Olver1986ApplicationsLieGroupsDifferentialEquations-SpringerGTM107.pdf).
Synopsis: [SYNOPSIS-Olver1986](SYNOPSIS-Olver1986.md).

Locators use printed page numbers. To get the one-based PDF page number, add 25 (except printed
pp. 119–122, which are PDF pp. 146, 147, 144, 145 in the local copy).

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

- the location, as chapter, section, printed page and equation or numbered item (line numbers,
  where given, are counted from the top of the page, negative ones from the bottom);
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- where the same error is listed in one of the published corrections lists below, a Published
  line citing the item by its second-edition page and line and giving the first-edition location,
  and saying how its correction differs from ours;
- the target synopsis entries.

Synopsis entries cite errata by id. An erratum id \(\mathrm{O86\text-E}cc.s.nn\) is the
\(nn\)-th erratum located in section \(s\) of chapter \(cc\) (\(s=0\) for chapter-level material
outside the numbered sections, such as the exercises).

## Published errata lists

P. J. Olver publishes no corrections list for the first edition (1986). His web page has two lists
for the second edition (Graduate Texts in Mathematics 107, Springer-Verlag, New York, 1993):

- [Olver 1993 corrections], by P. J. Olver: *Corrections to the First Printing of Olver, P.J.,
  Applications of Lie Groups to Differential Equations, Second Edition, Springer–Verlag, New York,
  1993*, last updated September 27, 2026 (62 items).
- [Olver 1993 corrected-printing corrections], by P. J. Olver: *Corrections to the Corrected
  Printing and Paperback Edition of Olver, P.J., Applications of Lie Groups to Differential
  Equations, Second Edition, Springer–Verlag, New York, 1993*, last updated September 27, 2026
  (47 items). It repeats the items of the first list that the corrected printing did not fix,
  with one change: on 2nd ed. p. 36 it only corrects "\(\varepsilon,\theta\in V\)" to
  "\((\varepsilon,\theta)\in V\)" in the reformulated Theorem 1.34.

Both lists locate an item by second-edition page and line (negative line numbers counted from the
bottom of the page), and these page numbers do not match the 1986 pagination. The second edition
also renumbered some results and exercises, and added and rewrote material. Each list item was
located in the 1986 edition by section, theorem, example or exercise number and by the content of
the formula or sentence, and the 1986 page images were checked to see whether the 1986 text has
the same error. Only errors present in the 1986 text are recorded. A Published line cites the
item by its second-edition locator and gives the 1986 location in parentheses, e.g.
"[Olver 1993 corrections], 2nd ed. p. 167, l. 2 (1986: p. 171, Definition 2.81)". Items that
concern material new in the second edition, or text that is already correct in the 1986 edition,
are not recorded here. Published corrections to formulas or statements that are correct as
printed in 1986 are recorded in the chapter's notes (not errata), with the evidence. Published
corrections to statements that the synopsis does not cover are listed in the section "Published
corrections to material outside the synopses" at the end of this file. Items that concern only
wording, spelling, notation without mathematical effect, cross-references, the chapter notes, the
index or the bibliography are not recorded here.

## Scope

These are observations about the first edition (1986), not an official publisher list and not an
assertion about the second edition (1993). No claim is made that formulas without an erratum are
free of errors. Formulas that the synopsis marks "as printed" were transcribed from the page
images without an independent check. Corrected formulas in the synopsis are statements to be
formalized. They are not Lean proofs. Garbling of the PDF text layer is not an erratum; every
erratum was checked on the page image.

Each chapter section ends with a list of conventions and notation that are not errata, for
example the right-invariant convention for Lie algebras of Lie groups, under which the matrix
bracket is \([A,B]=BA-AB\).

## Summary by chapter

- Chapter 1. Introduction to Lie Groups: 92 entries, 6 errata (Confirmed 6).
- Chapter 2. Symmetry Groups of Differential Equations: 93 entries, 8 errata (Confirmed 8).
- Chapter 3. Group-Invariant Solutions: 67 entries, 10 errata (Confirmed 10).
- Chapter 4. Symmetry Groups and Conservation Laws: 39 entries, 5 errata (Confirmed 5).
- Chapter 5. Generalized Symmetries: 72 entries, 13 errata (Confirmed 13).
- Chapter 6. Finite-Dimensional Hamiltonian Systems: 36 entries, 7 errata (Confirmed 7).
- Chapter 7. Hamiltonian Methods for Evolution Equations: 30 entries, 2 errata (Confirmed 2).
- Total: 429 entries, 51 errata (Confirmed 51).

## Chapter 1. Introduction to Lie Groups

### O86-E01.1.01. Level sets of the torus function in the example to Theorem 1.13

Status: Confirmed.
Location: §1.1, pp. 12–13, example following Theorem 1.13.
Printed: For \(F(x,y,z)=x^2+y^2+z^2-2\sqrt{2(x^2+y^2)}\), the level set \(\{F=c\}\) is a torus for
\(-2<c<\sqrt2-2\) and a "sphere with indented corners" for \(c\ge\sqrt2-2\).
Correct: With \(r=\sqrt{x^2+y^2}\), \(F=(r-\sqrt2)^2+z^2-2\). The level set \(\{F=c\}\) is the torus
of tube radius \(\sqrt{c+2}\) about the circle \(\{r=\sqrt2,z=0\}\) for \(-2<c<0\), and a surface
meeting the \(z\)-axis for \(c\ge0\). The threshold is \(c=0\), not \(c=\sqrt2-2\).
Evidence: The tube radius \(\sqrt{c+2}\) is less than the core radius \(\sqrt2\) exactly when
\(c<0\). For \(c=-0.3\), which exceeds \(\sqrt2-2\approx-0.586\), the tube radius is
\(\sqrt{1.7}\approx1.304<\sqrt2\approx1.414\), so \(\{F=-0.3\}\) is a torus that does not meet the
\(z\)-axis. On the \(z\)-axis (\(r=0\)), \(F=z^2\), so \(\{F=c\}\) meets the axis iff \(c\ge0\).
Target: [O86.01.1.07].

### O86-E01.1.02. Composite of two parametrizations of the figure eight

Status: Confirmed.
Location: §1.1, p. 10, Example 1.10(c).
Printed: For the two one-to-one immersions \(\phi,\tilde\phi:\mathbb R\to\mathbb R^2\) onto the figure
eight, "the composition \(\phi\circ\tilde\phi^{-1}:\mathbb R\to\mathbb R\) is not a continuous map".
Correct: \(\phi^{-1}\circ\tilde\phi:\mathbb R\to\mathbb R\) is not continuous.
Evidence: \(\tilde\phi^{-1}\) is defined on the figure eight and \(\phi\) takes values in
\(\mathbb R^2\), so \(\phi\circ\tilde\phi^{-1}\) maps the figure eight to \(\mathbb R^2\) (it is the
identity of the figure eight); the map \(\mathbb R\to\mathbb R\) comparing the two parameters is
\(\phi^{-1}\circ\tilde\phi\). It is discontinuous at \(0\): \(\phi^{-1}\tilde\phi(0)=0\), but for
small \(t\ne0\), \(\tilde\phi(t)\approx(-2t,8t)\) is not near \(\phi(s)\approx(2s,8s)\) for small
\(s\), so \(\phi^{-1}\tilde\phi(t)\) is large (\(\phi(s)\) returns to the origin only as
\(s\to\pm\infty\)).
Published: [Olver 1993 corrections], 2nd ed. p. 10, l. 6 (1986: p. 10, Example 1.10(c)).
[Olver 1993 corrected-printing corrections], 2nd ed. p. 10, l. 6.
Target: [O86.01.1.05].

### O86-E01.2.01. Domain of the inverse in Example 1.21

Status: Confirmed.
Location: §1.2, p. 19, Example 1.21.
Printed: For \(m(x,y)=(2xy-x-y)/(xy-1)\) on \(V=\{|x|<1\}\), the inverse \(i(x)=x/(2x-1)\) is
"defined for \(x\in V_0=\{x:|x|<\frac12\}\)".
Correct: \(V_0=\{x:-1<x<\frac13\}\), the largest interval about \(0\) on which \(i(x)\in V\).
Evidence: Definition 1.20 requires \(i:V_0\to V\). For \(x=0.4\in\{|x|<\frac12\}\),
\(i(x)=0.4/(-0.2)=-2\notin V\). For \(-1<x<\frac13\), \(2x-1<0\) and \(|x|<|2x-1|\) (both
\(x<1-2x\) and \(-x<1-2x\) hold), so \(|i(x)|<1\); at \(x=\frac13\), \(i(x)=-1\).
Published: [Olver 1993 corrections], 2nd ed. p. 19, l. 17 (1986: p. 19, Example 1.21).
[Olver 1993 corrected-printing corrections], 2nd ed. p. 19, l. 17.
Target: [O86.01.2.07].

### O86-E01.3.01. Commuting flows need a connected parameter domain

Status: Confirmed.
Location: §1.3, pp. 37–38, Theorem 1.34 and its proof.
Printed: \(\exp(\varepsilon\mathbf v)\exp(\delta\mathbf w)x=\exp(\delta\mathbf w)\exp(\varepsilon
\mathbf v)x\) (1.34) "for all \(\varepsilon,\delta\in\mathbb R\), \(x\in M\), such that both sides
are defined" iff \([\mathbf v,\mathbf w]=0\). The proof asserts that the set \(V\) of
\((\delta,\varepsilon)\) at which both sides are defined is connected.
Correct: If \([\mathbf v,\mathbf w]=0\), then for each \(x\), (1.34) holds for all
\((\varepsilon,\delta)\) in the connected component containing \((0,0)\) of the set of
\((\varepsilon,\delta)\) at which both sides are defined; conversely, if (1.34) holds for all
sufficiently small \(\varepsilon,\delta\) at every \(x\), then \([\mathbf v,\mathbf w]=0\). The
"if" direction of the printed version (all \(\varepsilon,\delta\) with both sides defined) is
false.
Evidence: Let \(M=\{(r,\theta):r>0,\ \theta\in\mathbb R\}\) be the universal cover of \(\mathbb
R^2\setminus\{0\}\), with \(\mathbf v=\cos\theta\,\partial_r-r^{-1}\sin\theta\,\partial_\theta\),
\(\mathbf w=\sin\theta\,\partial_r+r^{-1}\cos\theta\,\partial_\theta\), the lifts of
\(\partial_x,\partial_y\); \([\mathbf v,\mathbf w]=0\). Start at the lift of \((1,-\frac12)\) with
\(\theta=-\arctan\frac12\), and take \(\varepsilon=-2\), \(\delta=1\). Then \(\exp(\varepsilon\mathbf
v)\exp(\delta\mathbf w)x\) moves to \((1,\frac12)\) and then left above the origin, ending at
\((-1,\frac12)\) with \(\theta=\pi-\arctan\frac12\); \(\exp(\delta\mathbf w)\exp(\varepsilon\mathbf
v)x\) moves left below the origin to \((-1,-\frac12)\) and then up, ending at \((-1,\frac12)\) with
\(\theta=-\pi-\arctan\frac12\). Both sides are defined and they differ by \(2\pi\) in \(\theta\).
The set \(V\) of the proof is not connected here (for \(\varepsilon=-2\) the paths through the
origin are excluded).
Published: [Olver 1993 corrections], 2nd ed. p. 36, l. 9, and p. 37, ll. 7–14 (1986: pp. 37–38,
Theorem 1.34 and its proof), which gives the corrected statement and this counterexample.
[Olver 1993 corrected-printing corrections], 2nd ed. p. 36, l. 9, corrects only the notation
\((\varepsilon,\theta)\in V\) in the already corrected statement.
Target: [O86.01.3.12].

### O86-E01.0.01. Diagonal matrices on one-parameter subgroups of SL(2)

Status: Confirmed.
Location: Exercise 1.28(b), p. 74.
Printed: \(M=\mathrm{diag}(\lambda,\lambda^{-1})\in SL(2)\), \(\lambda\ne0\), lies on exactly one
one-parameter subgroup of \(SL(2)\) if \(\lambda>0\), on infinitely many if \(\lambda=-1\), and on
none if \(-1\ne\lambda<0\).
Correct: "Exactly one" holds for \(\lambda>0\), \(\lambda\ne1\). For \(\lambda=1\) (and for
\(\lambda=-1\)) \(M\) lies on infinitely many one-parameter subgroups.
Evidence: For \(\lambda=1\), \(M=I\) lies on every one-parameter subgroup \(\exp(\varepsilon A)\),
\(A\in\mathfrak{sl}(2)\).
Target: [O86.01.0.17].

### O86-E01.0.02. The conformal group of R^m is not SO(m+1)

Status: Confirmed.
Location: Exercise 1.31, p. 75.
Printed: For \(m\ge3\), the conformal group of \(\mathbb R^m\) is isomorphic to \(SO(m+1)\).
Correct: For \(m\ge3\), the (local) conformal group of \(\mathbb R^m\) is locally isomorphic to
\(SO(m+1,1)\). The rotations of \(S^m\), transported by stereographic projection, form a subgroup
locally isomorphic to \(SO(m+1)\).
Evidence: By Exercise 1.30(b), the conformal group has dimension \((m+1)(m+2)/2\), while
\(\dim SO(m+1)=m(m+1)/2\). For \(m=3\) these are \(10\ne6\). Also, the conformal group contains the
noncompact group of dilations \(x\mapsto\lambda x\), \(\lambda>0\), while \(SO(m+1)\) is compact.
Target: [O86.01.0.20].

### Conventions and notation (not errata)

- The Lie algebra of a Lie group consists of right-invariant vector fields (Definition 1.44). So
  the bracket on \(\mathfrak{gl}(n)\) is \([A,B]=BA-AB\) (Example 1.47), and the left-invariant
  bracket is its negative (Exercise 1.33). The sign of the \(\mathfrak{sl}(2)\) table
  (O86.01.4.12) follows this convention. Mathlib's `GroupLieAlgebra` and `Ring.lie_def` use the
  opposite sign.
- Manifolds, Lie groups and local transformation groups are assumed connected (pp. 13, 17, 22).
  So the "other such Lie group \(G\)" covered by \(G^*\) in Theorem 1.22 is connected. This is not
  an omitted hypothesis.
- "Submanifold" means an immersed submanifold (the image of a one-to-one immersion). Embedded
  submanifolds are called "regular".
- \(T(n)\) denotes the unitriangular group in Example 1.17 and the group of nonsingular upper
  triangular matrices in Exercise 1.15.
- In Exercise 1.25 the derived subalgebra is written as \(\{[\mathbf v,\mathbf w]:\mathbf v,
  \mathbf w\in\mathfrak g\}\). Its linear span is meant.
- Exercise 1.23 ("every complex Lie group contains a two-dimensional subgroup") is read as a
  statement about complex groups of complex dimension at least \(2\), or about real dimension
  \(2\). Under either reading it holds (O86.01.0.14).
- Exercise 1.33(c) asks to prove the naturality \(d\Psi_g(\psi(\mathbf v)|_x)=\psi(\mathbf
  v)|_{g\cdot x}\) for left-invariant \(\mathbf v\). With \(\psi\) defined by (1.46), one has
  \(d\Psi_g(\psi(\mathbf v)|_x)=\psi(\mathrm{Ad}(g)\mathbf v)|_{g\cdot x}\) under either convention.
  The intended reading of \(\psi\) on \(\mathfrak g_L\) is not fixed in the source, so this is
  recorded as a precise form in O86.01.0.22 rather than as an erratum.
- The classification in Example 1.58 of finite-dimensional Lie algebras of vector fields on the
  line is local, up to local diffeomorphism.
- Exercise 1.8, p. 71: the list [Olver 1993 corrections], 2nd ed. p. 70, Exercise 1.8, adds "with
  \(r>0\)" to "in polar coordinates". On \(M=\mathbb R^2\setminus\{0\}\) polar coordinates already
  have \(r>0\), so this is no erratum for the 1986 text. Note that \(\Psi\) is a local group of
  transformations (Definition 1.25): for \(0<r<1\) the radius \(re^{-\varepsilon}+1-e^{-\varepsilon}\)
  reaches \(0\) at \(\varepsilon=\log(1-r)<0\).

## Chapter 2. Symmetry Groups of Differential Equations

### O86-E02.3.01. Coefficient \(\xi\) of the rotation generator in Example 2.37

Status: Confirmed.
Location: §2.3, p. 116, l. 1, Example 2.37.
Printed: For \(\mathbf v=-u\partial_x+x\partial_u\), "In this case \(\phi=x\), \(\xi=u\)".
Correct: \(\phi=x\), \(\xi=-u\).
Evidence: \(\mathbf v=\xi\partial_x+\phi\partial_u\) with \(\mathbf v=-u\partial_x+x\partial_u\). The
computation on the same page uses \(\xi=-u\): \(\phi^x=D_x(\phi-\xi u_x)+\xi u_{xx}=D_x(x+uu_x)
-uu_{xx}=1+u_x^2\). The results stated in the synopsis are unaffected.
Published: [Olver 1993 corrections], 2nd ed. p. 113, l. 4 (1986: p. 116, l. 1, Example 2.37).
Target: [O86.02.3.11].

### O86-E02.4.01. The generic vector field in Example 2.43

Status: Confirmed.
Location: §2.4, p. 126, Example 2.43.
Printed: \(\mathbf v=\xi\partial_x+\eta\partial_y+\tau\partial_\tau+\phi\partial_u\), "where
\(\xi,\eta,\tau,\phi\) depend on \(x,y,t,u\)".
Correct: \(\mathbf v=\xi\partial_x+\eta\partial_y+\tau\partial_t+\phi\partial_u\).
Evidence: The independent variables of the wave equation (2.61) are \(x,y,t\); there is no
variable \(\tau\), which is the coefficient of \(\partial_t\). The generators (2.65) are written in
terms of \(\partial_t\).
Published: [Olver 1993 corrections], 2nd ed. p. 123, l. 5 (1986: p. 126, l. 5, Example 2.43).
[Olver 1993 corrected-printing corrections], 2nd ed. p. 123, l. 5.
Target: [O86.02.4.05].

### O86-E02.6.01. Number of equations in the k-th prolongation of a system

Status: Confirmed.
Location: §2.6, p. 171, Definition 2.81.
Printed: The \(k\)-th prolongation \(\Delta^{(k)}\) consists of the \(\binom{p+k-1}{k}\cdot l\)
equations \(D_J\Delta_\nu=0\), \(\nu=1,\dots,l\), \(0\le\#J\le k\).
Correct: The number of multi-indices with \(0\le\#J\le k\) is \(\sum_{j=0}^k\binom{p+j-1}{j}=
\binom{p+k}{k}\). So \(\Delta^{(k)}\) has \(\binom{p+k}{k}\cdot l\) equations. (\(\binom{p+k-1}{k}\)
counts only the multi-indices of order exactly \(k\).)
Evidence: The source's own example on the same page: the first prolongation of the heat equation
(\(p=2\), \(l=1\), \(k=1\)) lists the \(3\) equations \(u_t=u_{xx}\), \(u_{xt}=u_{xxx}\),
\(u_{tt}=u_{xxt}\), whereas \(\binom{2}{1}=2\) and \(\binom{3}{1}=3\). This also agrees with
\(\dim U^{(n)}=q\binom{p+n}{n}\) on p. 98.
Published: [Olver 1993 corrections], 2nd ed. p. 167, l. 2 (1986: p. 171, Definition 2.81).
[Olver 1993 corrected-printing corrections], 2nd ed. p. 167, l. 2.
Target: [O86.02.6.09].

### O86-E02.6.02. Infinitesimal criterion at points of local solvability is not sufficient

Status: Confirmed.
Location: §2.6, pp. 165–166, Theorem 2.72.
Printed: If \(\Delta=0\) is a system of maximal rank, a local group of transformations \(G\) is a
symmetry group iff \(\mathrm{pr}^{(n)}\mathbf v(\Delta_\nu)(x_0,u_0^{(n)})=0\), \(\nu=1,\dots,l\),
for every infinitesimal generator \(\mathbf v\) and every point \((x_0,u_0^{(n)})\in\mathcal
S_\Delta\) at which the system is locally solvable. "The proof is immediate."
Correct: Only the "only if" direction holds: if \(G\) is a symmetry group, it maps points of local
solvability to points of local solvability (it maps solutions to solutions), and differentiating
\(\Delta(\mathrm{pr}^{(n)}\exp(\varepsilon\mathbf v)\cdot z)=0\) at \(\varepsilon=0\) gives the
criterion at each such point \(z\). The "if" direction is false in general; it holds when every
point of \(\mathcal S_\Delta\) is locally solvable, i.e. for nondegenerate systems (Theorem 2.71).
Evidence: The first-order system \(u_x=0\), \(u_y=xu^2\) (\(p=2\), \(q=1\)) has maximal rank. Cross
differentiation gives \(0=u_{xy}=u^2+2xuu_x=u^2\), so its only solution is \(u\equiv0\), and the
points of local solvability are those with \(u=u_x=u_y=0\). For \(\mathbf v=\partial_u\),
\(\mathrm{pr}^{(1)}\mathbf v(u_x)=0\) and \(\mathrm{pr}^{(1)}\mathbf v(u_y-xu^2)=-2xu\), which
vanish there. But the translations \(u\mapsto u+\varepsilon\) map the solution \(u=0\) to
\(u=\varepsilon\), which is not a solution for \(\varepsilon\ne0\).
Published: [Olver 1993 corrections], 2nd ed. p. 162, Theorem 2.72 (1986: pp. 165–166, Theorem
2.72), which gives this counterexample and attributes the failure to the integrability condition
\(u^2=0\), which is not of maximal rank. [Olver 1993 corrected-printing corrections], 2nd ed.
p. 162.
Target: [O86.02.6.03].

### O86-E02.0.01. Navier–Stokes has one scaling symmetry fewer than Euler

Status: Confirmed.
Location: Exercise 2.15, p. 181.
Printed: The symmetry group of the Navier–Stokes equations \(\mathbf u_t+\mathbf u\cdot\nabla
\mathbf u=-\nabla p+\nu\Delta\mathbf u\), \(\nabla\cdot\mathbf u=0\) (\(\mathbf u\in\mathbb R^2\) or
\(\mathbb R^3\)) is the same as that of the Euler equations (\(\nu=0\)).
Correct: For \(\nu\ne0\), of the two Euler scalings \(\mathbf d_1=\mathbf x\cdot\nabla_{\mathbf x}+
t\partial_t\) and \(\mathbf d_2=t\partial_t-\mathbf u\cdot\nabla_{\mathbf u}-2p\partial_p\) of
(2.73), only the combination \(\mathbf d_1+\mathbf d_2=\mathbf x\cdot\nabla_{\mathbf x}+2t
\partial_t-\mathbf u\cdot\nabla_{\mathbf u}-2p\partial_p\) is a symmetry. The other Euler symmetries
(moving frames with arbitrary \(\boldsymbol\alpha(t)\), time translation, rotations, pressure
changes \(\theta(t)\partial_p\)) persist. So the Navier–Stokes symmetry algebra is a proper
subalgebra, of codimension one, of the Euler algebra.
Evidence: Under \(\mathbf d_1\), \((\mathbf x,t,\mathbf u,p)\mapsto(\lambda\mathbf x,\lambda t,
\mathbf u,p)\): the terms \(\mathbf u_t\), \(\mathbf u\cdot\nabla\mathbf u\) and \(\nabla p\) scale
by \(\lambda^{-1}\), but \(\nu\Delta\mathbf u\) scales by \(\lambda^{-2}\). Under \(\mathbf d_2\),
\((\mathbf x,\lambda t,\lambda^{-1}\mathbf u,\lambda^{-2}p)\): the first three scale by
\(\lambda^{-2}\), but \(\nu\Delta\mathbf u\) scales by \(\lambda^{-1}\). Under \((\lambda\mathbf
x,\lambda^2t,\lambda^{-1}\mathbf u,\lambda^{-2}p)\) all four terms scale by \(\lambda^{-3}\).
Target: [O86.02.0.06].

### O86-E02.0.02. Missing exclusions in the group classification of nonlinear heat conduction

Status: Confirmed.
Location: Exercise 2.18(b),(c), p. 182.
Printed: (b) If \(K(u)=(au+b)^m\) with \(m\ne-4/3\), \(a\ne0\), the symmetry group is
four-dimensional. (c) For \(K(u)=ce^{\alpha u}\) there is a four-parameter group.
Correct: (b) also needs \(m\ne0\). (c) needs \(c\ne0\) and \(\alpha\ne0\).
Evidence: For \(m=0\), \(K=(au+b)^0=1\). For \(\alpha=0\), \(K=c\). In both cases \(K\) is constant,
and \(u_t=D_x(K u_x)\) is the (rescaled) heat equation. By part (e) and Example 2.41 its symmetry
group is infinite-dimensional.
Target: [O86.02.0.07].

### O86-E02.0.03. Nondegeneracy condition for the projective group of the plane

Status: Confirmed.
Location: Exercise 2.26(a), p. 184.
Printed: The symmetry group of \(u_{xx}=0\) is the projective group \((x,u)\mapsto\bigl(
\frac{ax+bu+c}{\alpha x+\beta u+\gamma},\frac{dx+eu+f}{\alpha x+\beta u+\gamma}\bigr)\), where
\(a\beta-b\alpha\ne0\) and \(d\beta-e\alpha\ne0\).
Correct: The condition is \(\det\begin{pmatrix}a&b&c\\d&e&f\\\alpha&\beta&\gamma\end{pmatrix}\ne0\).
Evidence: The identity transformation (\(a=e=\gamma=1\), all other coefficients \(0\)) has
\(a\beta-b\alpha=0\) and \(d\beta-e\alpha=0\), so the printed conditions exclude it.
Target: [O86.02.0.14].

### O86-E02.0.04. Maximal symmetry dimension n + 4 requires n ≥ 3

Status: Confirmed.
Location: Exercise 2.26(b) and Exercise 2.27, p. 184.
Printed: The symmetry group of \(d^nu/dx^n=0\) is \((n+4)\)-dimensional (2.26(b)). A single
\(n\)-th order ODE has at most an \((n+4)\)-parameter symmetry group for \(n\ge2\) (2.27).
Correct: Both statements hold for \(n\ge3\). For \(n=2\), the maximal dimension is \(8\), attained
by \(u_{xx}=0\).
Evidence: By Exercise 2.26(a) on the same page, the symmetry group of \(u_{xx}=0\) is
eight-dimensional, which exceeds \(n+4=6\). (For \(n=1\) every first order ODE has an
infinite-dimensional symmetry group.)
Target: [O86.02.0.14].

### Conventions and notation (not errata)

- "Symmetry group" means a group of point transformations of \(X\times U\) that maps solutions to
  solutions (Definition 2.23). The infinitesimal criterion (2.25) is sufficient under the maximal
  rank condition. It is necessary only for nondegenerate (locally solvable) systems
  (Theorem 2.71).
- The characteristic of \(\mathbf v=\sum\xi^i\partial_{x^i}+\sum\phi_\alpha\partial_{u^\alpha}\) is
  \(Q_\alpha=\phi_\alpha-\sum_i\xi^iu^\alpha_i\) (2.48), and \(\phi^J_\alpha=D_JQ_\alpha+\sum_i\xi^i
  u^\alpha_{J,i}\).
- Theorem 2.16 on functional dependence is stated without a constant-rank hypothesis. The
  chapter Notes supply a proof (Brown's theorem plus Whitney's theorem on zero sets), so this is
  not an omission.
- In Example 2.55 the curvature is written \(\kappa=w_y(1+w^2)^{-3/2}+w\,y^{-1}(1+w^2)^{-1/2}\) in
  terms of \(y=\sqrt{x^2+u^2}\), \(w=(xu_x-u)/(x+uu_x)\). The identity holds on the branch
  \(x+uu_x>0\). On \(x+uu_x<0\) the right-hand side is \(-\kappa\), because \((1+w^2)^{1/2}=
  y\sqrt{1+u_x^2}/|x+uu_x|\). Recorded as a precise form in O86.02.5.09.
- In Example 2.43, "the ten vector fields" (2.65) generate the conformal algebra. The general
  solution of the defining equations has eleven constants: the eleventh gives \(u\partial_u\),
  which is listed separately with \(\alpha\partial_u\).
- In Example 2.65 the source uses the letter \(c\) for two different constants of integration in
  \(6(x-c)u_x^3+3cu_x+2=0\). The synopsis writes \(\tilde c\) for the second one.
- Printed pp. 119–122 are bound out of order in the local PDF copy: printed pp. 119, 120, 121, 122
  are PDF pp. 146, 147, 144, 145.

## Chapter 3. Group-Invariant Solutions

### O86-E03.2.01. Error-function solution of the heat equation

Status: Confirmed.
Location: §3.2, p. 196, l. 2, Example 3.3(b).
Printed: For \(a=0\) one obtains the probability solution \(u(x,t)=k^*\operatorname{erf}
(x/\sqrt{2t})+\tilde k^*\).
Correct: \(u(x,t)=k^*\operatorname{erf}\bigl(x/(2\sqrt t)\bigr)+\tilde k^*\).
Evidence: For \(a=0\) the reduced equation \(v_{yy}+\frac12yv_y=0\), \(y=x/\sqrt t\), gives
\(v_y=Ce^{-y^2/4}\), \(v=C'\operatorname{erf}(y/2)+C''\). Directly,
\(u=\operatorname{erf}(x/\sqrt{2t})\) gives \(u_t-u_{xx}=\frac{x}{\sqrt{2\pi}\,t^{3/2}}e^{-x^2/2t}
\ne0\) (it solves \(u_t=\frac12u_{xx}\)), while \(\operatorname{erf}(x/(2\sqrt t))\) solves
\(u_t=u_{xx}\). The neighbouring Hermite solutions \(t^{-(n+1)/2}e^{-x^2/4t}\mathrm{He}_n(x/\sqrt
{2t})\), \(n=0,\dots,3\), were checked to solve \(u_t=u_{xx}\) as printed.
Target: [O86.03.2.02].

### O86-E03.2.02. Wave number of the cnoidal waves

Status: Confirmed.
Location: §3.2, p. 197, Example 3.4(a).
Printed: \(u=a\,\mathrm{cn}^2[\lambda(x-ct)+\delta]+m\) with \(\lambda=\sqrt{(r_3-r_1)/6}\).
Correct: \(\lambda=\sqrt{(r_3-r_1)/12}\) (with \(k=\sqrt{(r_3-r_2)/(r_3-r_1)}\), \(a=r_3-r_2\),
\(m=r_2\) as printed).
Evidence: (3.12) reads \(v_y^2=\frac13(r_3-v)(v-r_2)(v-r_1)\). With \(r_1=-1\), \(r_2=\frac12\),
\(r_3=2\) and \(v=(r_3-r_2)\mathrm{cn}^2(\lambda y,k)+r_2\), the residual
\(\frac12v_y^2+\frac16(v-r_1)(v-r_2)(v-r_3)\) at \(y=0.37\) is \(0\) (to machine precision) for
\(\lambda^2=(r_3-r_1)/12\) and \(0.0672\) for \(\lambda^2=(r_3-r_1)/6\).
Target: [O86.03.2.04].

### O86-E03.2.03. The function \(\omega(r)\) in Kapitanskii's solutions

Status: Confirmed.
Location: §3.2, p. 201, solution for \(k<0\).
Printed: \(\hat u(r)=ar^{-1}\cosh(br^2+\delta)\), hence \(\omega(r)=-\dfrac{\arctan\exp(br^2+
\delta)}{2ab^2}\).
Correct: \(\omega(r)=\dfrac{\arctan\exp(br^2+\delta)}{ab}+\omega_0\).
Evidence: For \(\omega=\omega(r)\) the second equation of (3.18) is \(\hat u\,\omega_r=1\), so
\(\omega_r=r/(a\cosh(br^2+\delta))\); since \(\frac d{dr}\arctan e^{br^2+\delta}=br\,
\mathrm{sech}(br^2+\delta)\), the corrected \(\omega\) satisfies it, while the printed one gives
\(\hat u\omega_r=-1/(2b)\). The other printed data (\(\xi=-2ab\sinh(br^2+\delta)\),
\(\eta=-2b\sinh(br^2+\delta)\), \(k=-4a^2b^2\), \(l=-4ab^2\), the ODE for \(\hat u\)) were checked
symbolically and are correct.
Target: [O86.03.2.11].

### O86-E03.2.04. SO(3)-invariant solutions of the Euler equations exist

Status: Confirmed.
Location: §3.2, p. 201, l. 6.
Printed: Since the projected action of \(SO(3)\) on \(\mathbb R^3\) has two-dimensional orbits, the
transversality condition fails and no reduced system can be constructed; "Thus no
\(SO(3)\)-invariant solutions exist."
Correct: \(SO(3)\)-invariant solutions cannot be constructed by the reduction method of §3.1. They
do exist.
Evidence: \(\mathbf u=0\), \(p=f(t)\) is an \(SO(3)\)-invariant solution of (3.13) on
\(\mathbb R^3\). Nontrivial ones exist on \(\mathbb R^3\setminus\{0\}\): \(\mathbf u=c(t)\mathbf
x/|\mathbf x|^3=\nabla\varphi\), \(\varphi=-c(t)/|\mathbf x|\), is divergence free, and the
Bernoulli pressure \(p=-\varphi_t-\frac12|\mathbf u|^2=c'(t)/|\mathbf x|-c(t)^2/(2|\mathbf x|^4)\)
gives \(\mathbf u_t+(\mathbf u\cdot\nabla)\mathbf u=\nabla(\varphi_t+\frac12|\mathbf u|^2)=-\nabla
p\). Both satisfy \(\mathbf u(R\mathbf x)=R\mathbf u(\mathbf x)\), \(p(R\mathbf x)=p(\mathbf x)\).
Published: [Olver 1993 corrections], 2nd ed. p. 197, l. −10 (1986: p. 201, l. 6), which replaces
"exist" by "can be constructed by this technique".
Target: [O86.03.2.10].

### O86-E03.3.01. Row label in the KdV adjoint table

Status: Confirmed.
Location: §3.3, p. 206, table (3.24), last row.
Printed: The last row is labelled \(\mathbf v_2\) (entries \(e^\varepsilon\mathbf v_1,e^{3\varepsilon}
\mathbf v_2,e^{-2\varepsilon}\mathbf v_3,\mathbf v_4\)).
Correct: The last row is labelled \(\mathbf v_4\): the entries are \(\mathrm{Ad}(\exp(\varepsilon
\mathbf v_4))\mathbf v_j\).
Evidence: \([\mathbf v_4,\mathbf v_1]=-\mathbf v_1\), \([\mathbf v_4,\mathbf v_2]=-3\mathbf v_2\),
\([\mathbf v_4,\mathbf v_3]=2\mathbf v_3\) give the printed entries via (3.23); the second row is
already labelled \(\mathbf v_2\) and has different entries. All other entries were checked by
summing the Lie series.
Target: [O86.03.3.07].

### O86-E03.3.02. Sign of \(\tilde a_4\) in Case 1 of the heat classification

Status: Confirmed.
Location: §3.3, p. 209, Case 1.
Printed: Choosing \(\beta\) to be either real root of \(4a_6\beta^2-2a_4\beta+a_2=0\) and
\(\alpha=a_6/(8\beta a_6-2a_4)\), then \(\tilde a_2=\tilde a_6=0\) "while \(\tilde a_4=
\sqrt{\eta(\mathbf v)}\ne0\)".
Correct: \(\tilde a_4=\pm\sqrt{\eta(\mathbf v)}\), the sign depending on the root chosen; the
conclusion (equivalence to a multiple of \(\mathbf v_4+\cdots\)) is unaffected.
Evidence: For \(a_2=a_6=1\), \(a_4=3\) (\(\eta=5\)) the two roots give \((\tilde a_2,\tilde a_4,
\tilde a_6)=(0,\sqrt5,0)\) and \((0,-\sqrt5,0)\) in (3.26). Invariance of \(\eta\) under (3.26) was
verified symbolically.
Target: [O86.03.3.11].

### O86-E03.3.03. Generator in Example 3.17(a)

Status: Confirmed.
Location: §3.3, p. 212, Example 3.17(a).
Printed: \(\mathbf v_4+a\mathbf v_3=x\partial_x+2t\partial_t+2au\partial_u\).
Correct: \(\mathbf v_4+2a\mathbf v_3=x\partial_x+2t\partial_t+2au\partial_u\) (equivalently,
\(\mathbf v_4+a\mathbf v_3=x\partial_x+2t\partial_t+au\partial_u\) with invariants
\(y=x/\sqrt t\), \(v=t^{-a/2}u\)).
Evidence: \(\mathbf v_3=u\partial_u\), \(\mathbf v_4=x\partial_x+2t\partial_t\); the invariants
\(y=x/\sqrt t\), \(v=t^{-a}u\) and the solutions \(t^ae^{-x^2/8t}\{\cdots\}\) used in the example
belong to \(x\partial_x+2t\partial_t+2au\partial_u\) (the scaling \((\lambda x,\lambda^2t,
\lambda^{2a}u)\) of Example 3.3). The family (3.27a), \(a\in\mathbb R\), is unchanged by the
reparametrization.
Target: [O86.03.3.15].

### O86-E03.3.04. Argument of the parabolic cylinder functions in Example 3.17(b)

Status: Confirmed.
Location: §3.3, p. 212, Example 3.17(b).
Printed: \(u=(4t^2+1)^{-1/4}\{kW(-\frac a2,\frac x{\sqrt{8t^2+2}})+\tilde kW(-\frac a2,
\frac{-x}{\sqrt{8t^2+2}})\}\exp\{\cdots\}\).
Correct: the second argument is \(\pm\sqrt2\,y=\pm\dfrac{2x}{\sqrt{8t^2+2}}=\pm\dfrac{\sqrt2\,x}
{\sqrt{4t^2+1}}\).
Evidence: The reduced equation \(v_{yy}+(a+y^2)v=0\), \(y=x/\sqrt{4t^2+1}\), was verified
symbolically. \(W(b,z)\) solves \(w_{zz}+(\frac14z^2-b)w=0\), so \(W(-\frac a2,\lambda y)\) solves
it iff \(\lambda^4/4=1\), i.e. \(\lambda=\sqrt2\). Numerically, with \(a=0.7\), \(y=0.43\), the
residual of \(v_{yy}+(a+y^2)v\) is \(10^{-16}\) for \(v=W(-a/2,\sqrt2y)\) and \(0.53\) for the
printed \(v=W(-a/2,y/\sqrt2)\).
Target: [O86.03.3.15].

### O86-E03.4.01. Indices in the proof of the Pi theorem

Status: Confirmed.
Location: §3.4, p. 220, proof of Theorem 3.22.
Printed: "The exponents \(t_j\) satisfy the linear system \(\sum_jt_j\beta_{jk}=0\) for
\(k=1,\dots,r\)"; "global coordinates on the quotient manifold \(G/M\)".
Correct: \(k=1,\dots,m-s\) (one equation per power product \(\pi^k\)); the quotient manifold is
\(M/G\).
Evidence: The \(\beta_{\cdot k}\), \(k=1,\dots,m-s\), are the basis of \(\ker A\) chosen in
(3.29)–(3.30); \(r\) is the number of fundamental units.
Target: [O86.03.4.06].

### O86-E03.0.01. Argument of the blast-wave similarity function

Status: Confirmed.
Location: Exercise 3.7, p. 243.
Printed: \(R=(t^2E/\rho_0)^{1/5}\,h\bigl[p_0(t^6E^2/\rho_0^3)^{1/5}\bigr]\).
Correct: \(R=(t^2E/\rho_0)^{1/5}\,h\bigl[p_0\bigl(t^6/(E^2\rho_0^3)\bigr)^{1/5}\bigr]\).
Evidence: With dimensions \([E]=ML^2T^{-2}\), \([\rho_0]=ML^{-3}\), \([p_0]=ML^{-1}T^{-2}\), the
printed argument has dimension \(M^{4/5}L^{8/5}T^{-8/5}\), so it is not dimensionless; the
corrected one is \((p_0^5t^6/(E^2\rho_0^3))^{1/5}\), dimensionless, and small for small \(t\) as the
exercise states.
Published: [Olver 1993 corrections], 2nd ed. p. 238, Exercise 3.7 (1986: p. 243, Exercise 3.7).
[Olver 1993 corrected-printing corrections], 2nd ed. p. 238, Exercise 3.7.
Target: [O86.03.0.01].

### Conventions and notation (not errata)

- p. 203–204, (3.21): with right-invariant vector fields \(\mathrm{ad}\,\mathbf v|_{\mathbf
  w}=[\mathbf w,\mathbf v]\), the opposite of the usual sign; the Lie series (3.23) then reads
  \(\mathbf w-\varepsilon[\mathbf v,\mathbf w]+\cdots\) with the vector-field commutator. The
  adjoint tables (3.24) and of Example 3.13 follow this convention and were verified with it.
- p. 197: the source calls \(v_{yy}+\frac12v^2+by+c=0\) and \(w_{yy}=\frac1{18}w^3+\frac13yw+k\)
  the first and second Painlevé transcendents; they are those equations after rescaling of
  \(v,y\) (resp. \(w,y\)).
- p. 200: \(\int_0^rs^{-3}h[\frac12s^2-\sigma(t)]^2ds\) diverges at \(0\) unless
  \(h(-\sigma)=0\); any antiderivative in \(r\) may be used (the synopsis writes \(\int^r\)).
- p. 214, Theorem 3.18: the quotient "manifold" may fail the Hausdorff axiom of Definition 1.1, as
  the footnote and Example 3.20 state.
- Exercise 3.20(c), p. 245: "Theorem 3.37" refers to Theorem 3.38 (Proposition 3.37 is the
  transversality criterion).
- p. 206: the list [Olver 1993 corrections], 2nd ed. p. 202, ll. 13–14, changes the justification
  of the convergence of the Lie series (3.23) from "(3.22) is a linear system of ordinary
  differential equations" to "linear, constant coefficient system". The 1986 statement is correct:
  (3.22), \(dw/d\varepsilon=\mathrm{ad}\,\mathbf v|_w\) on the finite-dimensional \(\mathfrak g\), is
  linear with constant coefficients, and (3.23) is its matrix exponential.

## Chapter 4. Symmetry Groups and Conservation Laws

### O86-E04.1.01. Sign in the hodograph check of Example 4.9

Status: Confirmed.
Location: §4.1, p. 256, Example 4.9, display after (4.11).
Printed: \(\mathsf E_u(L)=-u_{xx}=-\tilde u_{\tilde x}^{-3}\tilde u_{\tilde x\tilde x}=-\mathsf
E_{\tilde u}(\tilde L)\).
Correct: \(\mathsf E_u(L)=-u_{xx}=\tilde u_{\tilde x}^{-3}\tilde u_{\tilde x\tilde x}=-\mathsf
E_{\tilde u}(\tilde L)\).
Evidence: With \(\tilde x=u\), \(\tilde u=x\): \(u_x=1/\tilde u_{\tilde x}\) and
\(u_{xx}=u_x\frac{d}{d\tilde x}(\tilde u_{\tilde x}^{-1})=-\tilde u_{\tilde x}^{-3}\tilde
u_{\tilde x\tilde x}\). For \(\tilde L=(2\tilde u_{\tilde x})^{-1}\), \(\mathsf E_{\tilde u}(\tilde
L)=D_{\tilde x}\bigl(\frac1{2\tilde u_{\tilde x}^2}\bigr)=-\tilde u_{\tilde x}^{-3}\tilde
u_{\tilde x\tilde x}\). The end relation \(\mathsf E_u(L)=-\mathsf E_{\tilde u}(\tilde L)\) agrees
with (4.11) (Jacobian \(-1\)); only the middle term has the wrong sign.
Target: [O86.04.1.08].

### O86-E04.3.01. Difference of characteristics in Example 4.25

Status: Confirmed.
Location: §4.3, p. 271, Example 4.25.
Printed: \(Q-\tilde Q=(-(u_{tt}-u_{xx}),-(v_{tt}-v_{xx}))\).
Correct: \(Q-\tilde Q=(-(u_{tt}-u_{xx}),-(u_{xt}-v_{xx}))\).
Evidence: \(Q=(-u_{tt},-u_{xt})\) and \(\tilde Q=(-u_{xx},-v_{xx})\) as printed on the same page.
The corrected difference is again trivial, since \(u_t=v_x\) gives \(u_{xt}=v_{xx}\) on solutions.
Target: [O86.04.3.08].

### O86-E04.4.01. Inversional conservation laws in elastostatics

Status: Confirmed.
Location: §4.4, p. 283, Example 4.32.
Printed: For \(W\) homogeneous of degree \(p\) the inversions are
\(\sum_j(x^ix^j-\delta^i_j|x|^2)\partial_{x^j}\), with conservation laws \(\sum_iD_iC^i_j=\sum_iD_i
\{\sum_k(x^jx^k-\delta^k_j|x|^2)(\sum_\alpha u^\alpha_k\,\partial W/\partial u^\alpha_i-\delta^k_i
W)\}=0\), and for non-homogeneous \(W\) the divergence identities \(\sum_iD_iC^i_j=x^j[pW-
\sum_{\alpha,k}u^\alpha_k\,\partial W/\partial u^\alpha_k]\).
Correct: Replace \(\delta|x|^2\) by \(\frac12\delta|x|^2\) in the generators and in \(C^i_j\)
(the generators are half the conformal inversions \(2x^jx^k-\delta^k_j|x|^2\)); then, for
isotropic \(W(\nabla u)\), \(\sum_iD_iC^i_j=x^j[\sum_{\alpha,k}u^\alpha_k\,\partial W/\partial
u^\alpha_k-pW]\) on solutions, which vanishes when \(W\) is homogeneous of degree \(p\).
Evidence: The field \(\sum_k(x^jx^k-\delta^k_j|x|^2)\partial_{x^k}\) is not conformal
(\(\partial_l\xi^k+\partial_k\xi^l=2x^j\delta_{kl}-\delta_{jk}x^l-\delta_{jl}x^k\)). Take \(p=2\),
\(q=1\), \(W=|\nabla u|^2\) (homogeneous of degree \(2\), isotropic) and the solution \(u=x\) of
\(\Delta u=0\): the printed \(C_1=(-y^2,-xy)\) has \(\mathrm{Div}\,C_1=-x\ne0\), while the corrected
\(C_1=(\frac12(x^2-y^2),-xy)\) has divergence \(0\). For \(W=|\nabla u|^4\) (not of degree \(p=2\)),
\(u=x\) is a solution and the corrected \(C_1=(\frac32(x^2-y^2),-xy)\) has divergence
\(2x=x(\sum u_kW_{u_k}-pW)\), opposite in sign to the printed right-hand side. A symbolic check
with \(W=\exp|\nabla u|^2\) confirms the corrected identity modulo the Euler–Lagrange expression.
Target: [O86.04.4.04].

### O86-E04.4.02. Inversional density \(I_x\) for the wave equation

Status: Confirmed.
Location: §4.4, p. 285, table of Example 4.36, row "Inversions", first line.
Printed: \(I_x=xD-yA+\frac12xuu_t+tM_x\).
Correct: \(I_x=xD+yA+\frac12xuu_t+tM_x\).
Evidence: The Noether density for \(\mathbf i_x\) (characteristic \((x^2-y^2+t^2)u_x+2xyu_y+2xtu_t+
xu\), \(\tau=2xt\), \(B_t=0\)) is \((x^2-y^2+t^2)u_xu_t+2xyu_yu_t+xuu_t+2xtE\), which equals
\(xD+yA+\frac12xuu_t+tM_x\) and differs from the printed \(I_x\) by \(2yA\). The printed \(I_y=yD-
xA+\frac12yuu_t+tM_y\) is correct (checked the same way), and the reflection \(x\leftrightarrow y\)
(which maps \(\mathbf i_y\) to \(\mathbf i_x\), \(A\) to \(-A\), \(M_y\) to \(M_x\)) maps it to
the corrected \(I_x\). \(I_t\), \(D\), \(A\), \(M_x\) were checked as printed.
Published: [Olver 1993 corrections], 2nd ed. p. 280, table (1986: p. 285, table of Example 4.36).
[Olver 1993 corrected-printing corrections], 2nd ed. p. 280, table.
Target: [O86.04.4.07].

### O86-E04.4.03. Dilatational identity for the wave equation

Status: Confirmed.
Location: §4.4, p. 286, Example 4.36.
Printed: \(-\frac d{dt}\iint\frac12u^2\,dx\,dy=\iint(xP_x+yP_y)\,dx\,dy+\mathcal Et+\hat{\mathcal
C}\).
Correct: \(-\frac d{dt}\iint\frac14u^2\,dx\,dy=\iint(xP_x+yP_y)\,dx\,dy+\mathcal Et+\hat{\mathcal
C}\).
Evidence: The conserved density is \(D=xP_x+yP_y+\frac12uu_t+tE\) and
\(\frac12uu_t=D_t(\frac14u^2)\); integrating \(D\) gives the corrected identity with
\(\hat{\mathcal C}=-\iint D\).
Target: [O86.04.4.07].

### Conventions and notation (not errata)

- p. 279, Corollary 4.30: the \(P\) of (4.41) equals \(A+L\xi\), the negative of the
  \(P=-(A+L\xi)\) of the proof of Theorem 4.29; it satisfies \(\mathrm{Div}\,P=-Q\cdot\mathsf
  E(L)\), so its characteristic is \(-Q\). The corollary only asserts a conservation law, which
  holds. Likewise the characteristics listed in the table of Example 4.36 are \(-Q\) for the
  listed densities, which are the negatives of the Noether densities \(-(A+L\xi)+B\).
- p. 254, (4.6)–(4.8): \(\det J>0\) (orientation-preserving changes of variables) is assumed.
- §4.3: all systems are assumed totally nondegenerate (Definition 2.83); Theorem 4.26 also
  requires normality.

## Chapter 5. Generalized Symmetries

### O86-E05.1.01. Polynomial symmetries of an evolution equation need not commute

Status: Confirmed.
Location: §5.1, p. 311, Theorem 5.20; its proof, p. 312, ll. 7–14; used on p. 321 after
Theorem 5.32.
Printed: If \(u_t=P(u,u_1,\dots,u_n)\) is a polynomial evolution equation in one spatial variable
with \(P\ne cu_x\), and \(\mathbf v_Q,\mathbf v_R\) are symmetries with \(x,t\)-independent
polynomial characteristics, then \([\mathbf v_Q,\mathbf v_R]=0\). The proof asserts that the
bracket characteristic \(\mathrm{pr}\,\mathbf v_Q(R)-\mathrm{pr}\,\mathbf v_R(Q)\) of two such
polynomials cannot contain terms linear in the \(u_k\).
Correct: The statement is false without further hypotheses. Only the Lie algebra property
(Proposition 5.17) holds in general; commutativity has to be proved for the particular hierarchy
(for KdV it follows from the bi-Hamiltonian structure, Theorem 7.24(ii) with Example 7.22).
Evidence: For the heat equation \(P=u_{xx}\), take \(Q=1\), \(R=u\). Both are symmetries:
\(\mathrm{pr}\,\mathbf v_Q(P)=0=\mathrm{pr}\,\mathbf v_P(Q)\) and \(\mathrm{pr}\,\mathbf v_R(P)=
u_{xx}=\mathrm{pr}\,\mathbf v_P(R)\). Their bracket has characteristic \(\mathrm{pr}\,\mathbf
v_Q(R)-\mathrm{pr}\,\mathbf v_R(Q)=1-0=1\ne0\). Positive-order examples also exist:
\(Q=u_{xx}+1\), \(R=u_{xx}+u\) are symmetries with bracket characteristic \(1\). The algebraic claim
in the proof fails too: for \(Q=u^2\), \(R=1\) the bracket characteristic is \(-2u\).
Target: [O86.05.1.16], [O86.05.2.09].

### O86-E05.1.02. A nonelementary symmetry does not force linearity in the highest derivative

Status: Confirmed.
Location: §5.1, p. 312, Theorem 5.22, (5.31); proof pp. 312–314.
Printed: If \(u_t=P(u,\dots,u_n)\) (polynomial) admits a polynomial symmetry \(\mathbf v_Q\),
\(Q=Q(u,\dots,u_m)\), that is not a linear combination of \(\mathbf v_0=u_x\partial_u\) and
\(\mathbf v_P\), then \(P=\lambda u_n+\tilde P(u,\dots,u_{n-1})\) with \(\lambda\ne0\) constant.
Correct: False as stated; no general replacement is asserted here. The proof's coefficient
comparisons (5.34)–(5.36) assume that \(\partial P/\partial u_n\) and \(\partial Q/\partial u_m\)
do not involve the derivatives \(u_{n+m-1}\), \(u_{n+m-2}\) being compared, which fails for small
orders, and the case \(Q\) constant is not excluded.
Evidence: (i) \(P=u_{xx}^2\), \(Q=1\): \(\mathrm{pr}\,\mathbf v_Q(P)=0=\mathrm{pr}\,\mathbf v_P(Q)\),
\(Q\) is not a combination of \(u_x\) and \(u_{xx}^2\), and \(P\) is not linear in \(u_{xx}\).
(ii) \(P=u_x^2\), \(Q=u_x^3\): \(\mathrm{pr}\,\mathbf v_Q(P)=2u_xD_x(u_x^3)=6u_x^3u_{xx}=
3u_x^2D_x(u_x^2)=\mathrm{pr}\,\mathbf v_P(Q)\), \(Q\) is not a combination of \(u_x\) and \(u_x^2\),
and \(P\) is not linear in \(u_x\). In (ii), (5.34) would require
\(nP_nD_xQ_m=mQ_mD_xP_n\), i.e. \(2u_x\cdot6u_xu_{xx}=3u_x^2\cdot2u_{xx}\), which is false: the
derivation of (5.34) breaks down because \(P_1,Q_1\) depend on \(u_{n+m-1}=u_1\).
Target: [O86.05.1.17].

### O86-E05.3.01. Sign of \(q_t\) in the adjoint for Burgers' equation

Status: Confirmed.
Location: §5.3, p. 324, Example 5.34, last display.
Printed: \(\mathsf D_\Delta^*(q)=q_t-q_{xx}+uq_x=0\).
Correct: \(\mathsf D_\Delta^*(q)=-q_t-q_{xx}+uq_x=0\).
Evidence: The same example gives \(\mathsf D_\Delta^*=-D_t-D_x^2+uD_x\), which applied to
\(q(x,t)\) gives \(-q_t-q_{xx}+uq_x\). The conclusion (\(q\) constant) is unaffected: the
coefficient of \(u\) gives \(q_x=0\), then \(q_t=0\).
Published: [Olver 1993 corrections], 2nd ed. p. 331, second display (1986: p. 324, Example 5.34).
[Olver 1993 corrected-printing corrections], 2nd ed. p. 331, second display.
Target: [O86.05.3.04].

### O86-E05.3.02. Sign of the potential in the Kepler Lagrangian

Status: Confirmed.
Location: §5.3, p. 328, Example 5.43, last line, and p. 329, displays of
\(\mathrm{pr}^{(1)}\mathbf v_x(L)\).
Printed: \(L=\tfrac12(\dot x^2+\dot y^2+\dot z^2)-\mu r^{-1}\) for the Kepler problem
\(\ddot{\mathbf x}+\mu r^{-3}\mathbf x=0\); \(\mathrm{pr}^{(1)}\mathbf v_x(L)=\cdots+\mu r^{-3}
[(y^2+z^2)\dot x-xy\dot y-xz\dot z]=D_t[\dot x(y\dot y+z\dot z)-x(\dot y^2+\dot z^2)+\mu r^{-1}x]\),
which "vanishes on solutions", so that \(R_x\) is a first integral.
Correct: \(L=\tfrac12(\dot x^2+\dot y^2+\dot z^2)+\mu r^{-1}\). Then
\(\mathrm{pr}^{(1)}\mathbf v_x(L)=D_t[\dot x(y\dot y+z\dot z)-x(\dot y^2+\dot z^2)-\mu r^{-1}x]\)
(still a total derivative, so \(\mathbf v_x\) is variational), but this does not vanish on
solutions; the first integral obtained from the characteristic form (Noether) is
\(R_x=\dot x(y\dot y+z\dot z)-x(\dot y^2+\dot z^2)+\mu r^{-1}x\), as printed.
Evidence: The Euler–Lagrange equations of the printed \(L\) are \(\ddot{\mathbf x}-\mu r^{-3}
\mathbf x=0\) (repulsive), not the stated equations. A symbolic computation confirms that the
printed \(\mathrm{pr}^{(1)}\mathbf v_x(L)\) identity holds for \(L\) with \(-\mu r^{-1}\) and
that for \(L\) with \(+\mu r^{-1}\) the total derivative is that of the expression with
\(-\mu r^{-1}x\). With \(Q\) the characteristic of \(\mathbf v_x\), \(Q\cdot\mathsf E(L)=
-D_t R_x\) for the correct \(L\), and \(D_tR_x=0\) on solutions of \(\ddot{\mathbf x}=
-\mu r^{-3}\mathbf x\).
Target: [O86.05.3.10].

### O86-E05.3.03. Sign of the Runge–Lenz vector

Status: Confirmed.
Location: §5.3, p. 329, Example 5.43, display of \(\mathbf R\).
Printed: \(\mathbf R=(R_x,R_y,R_z)=\dot{\mathbf x}\times\mathbf A-\mu\mathbf x/|\mathbf x|=
\dot{\mathbf x}\times(\mathbf x\times\dot{\mathbf x})-\mu\mathbf x/|\mathbf x|\).
Correct: With \(R_x\) as printed, \(\mathbf R=\mathbf A\times\dot{\mathbf x}+\mu\mathbf x/|\mathbf
x|=-(\dot{\mathbf x}\times\mathbf A-\mu\mathbf x/|\mathbf x|)\).
Evidence: \(\dot{\mathbf x}\times(\mathbf x\times\dot{\mathbf x})=\mathbf x|\dot{\mathbf x}|^2-
\dot{\mathbf x}(\mathbf x\cdot\dot{\mathbf x})\) has first component \(x(\dot y^2+\dot z^2)-
\dot x(y\dot y+z\dot z)\), the negative of the kinetic part of the printed \(R_x\); the
\(\mu\)-terms also have opposite signs. Both vectors are conserved, being negatives of each
other.
Target: [O86.05.3.10].

### O86-E05.3.04. Two rows of the table of second-order conservation laws of the wave equation

Status: Confirmed.
Location: §5.3, p. 334, Example 5.47, table, rows 4 and 5.
Printed: Row \(D_x\mathscr R_{xy}D_x\): characteristic \(-yu_{xxx}+xu_{xyy}+u_{xy}\), density
\(u_{xt}(xu_{xy}-yu_{xx})\). Row \(D_x\mathscr R_{xy}D_y-\frac12D_x^2-\frac12D_y^2\): characteristic
\(-yu_{xxy}+xu_{xyy}-\frac12u_{xx}+\frac12u_{yy}\), density \(u_{xx}(yu_{yt}+\frac12u_t)-u_{yy}
(xu_{xt}+\frac12u_t)\).
Correct: Row 4 characteristic \(-yu_{xxx}+xu_{xxy}+u_{xy}\) (density as printed). Row 5 density
\(-u_{xx}(yu_{yt}+\frac12u_t)+u_{yy}(xu_{xt}+\frac12u_t)\) (characteristic as printed).
Evidence: With \(\mathscr R_{xy}=xD_y-yD_x\), \(D_x\mathscr R_{xy}D_xu=D_x(xu_{xy}-yu_{xx})=
u_{xy}+xu_{xxy}-yu_{xxx}\). For a density \(T\) depending on \(u_t\) through \(v=u_t\) and its
\(x,y\)-derivatives, \(D_tT+\mathrm{Div}_{x,y}X=Q\,(u_{tt}-u_{xx}-u_{yy})\) with
\(Q=\mathsf E_v(T)\); the table lists \(-Q\) (row 1: \(T=u_{xx}u_{xt}\), \(\mathsf E_v(T)=-u_{xxx}\),
listed \(u_{xxx}\)). A symbolic computation gives \(-\mathsf E_v\) of the row 4 density as
\(-yu_{xxx}+xu_{xxy}+u_{xy}\), and \(-\mathsf E_v\) of the printed row 5 density as the negative of
the listed characteristic; both densities are conserved (the spatial Euler operators of
\(D_tT\), reduced by \(u_{tt}=u_{xx}+u_{yy}\), vanish).
Published: [Olver 1993 corrections], 2nd ed. p. 340, lines 4 and 5 of the table (1986: p. 334,
Example 5.47). [Olver 1993 corrected-printing corrections], 2nd ed. p. 340, lines 4 and 5.
Target: [O86.05.3.14].

### O86-E05.4.01. Number of components in the Helmholtz theorem

Status: Confirmed.
Location: §5.4, p. 355, Theorem 5.68, first line.
Printed: "Let \(P[u]\in\mathcal A^p\) be defined over a vertically star-shaped region …".
Correct: \(P[u]\in\mathcal A^q\).
Evidence: \(P\) is to equal \(\mathsf E(L)\in\mathcal A^q\), \(\mathsf D_P\) must be a square
\(q\times q\) operator to be self-adjoint, and (5.85) pairs \(u\in\mathbb R^q\) with \(P\).
Published: [Olver 1993 corrections], 2nd ed. p. 364, Theorem 5.92, first line (1986: p. 355,
Theorem 5.68). [Olver 1993 corrected-printing corrections], 2nd ed. p. 364, Theorem 5.92.
Target: [O86.05.4.10].

### O86-E05.4.02. Missing power of \(\lambda\) in the base term \(b_k\)

Status: Confirmed.
Location: §5.4, p. 364, (5.113), second line.
Printed: \(b_k(x)=\int_0^1x^kL(\lambda x,0)\,d\lambda\).
Correct: \(b_k(x)=\int_0^1\lambda^{p-1}x^kL(\lambda x,0)\,d\lambda\).
Evidence: \(b\) comes from the Poincaré homotopy (1.69) applied to the \(p\)-form
\(L(x,0)dx^1\wedge\cdots\wedge dx^p\); evaluating the interior product at \(\lambda x\) scales the
\(p-1\) differentials and \(x^k\) by \(\lambda^p\), and (1.69) divides by \(\lambda\). Check:
\(p=2\), \(L\equiv1\) (so \(\mathsf E(L)=0\)): the printed formula gives \(b=(x^1,x^2)\),
\(\mathrm{Div}\,b=2\ne1\); the corrected one gives \(b=\tfrac12(x^1,x^2)\), \(\mathrm{Div}\,b=1\).
For \(p=1\) the two agree.
Target: [O86.05.4.15], [O86.05.4.16].

### O86-E05.4.03. Number of components in Theorem 5.80

Status: Confirmed.
Location: §5.4, p. 365, Theorem 5.80, first line.
Printed: "Let \(P\in\mathcal A^q\) and let \(L=\mathrm{Div}\,P\)".
Correct: \(P\in\mathcal A^p\).
Evidence: \(\mathrm{Div}\,P=\sum_{k=1}^pD_kP_k\) and (5.114) is stated for \(k=1,\dots,p\).
Target: [O86.05.4.16].

### O86-E05.4.04. Missing power of \(\lambda\) in \(q_{jk}\)

Status: Confirmed.
Location: §5.4, p. 365, (5.115), second line.
Printed: \(q_{jk}(x)=\int_0^1\{x^jP_k(\lambda x,0)-x^kP_j(\lambda x,0)\}\,d\lambda\).
Correct: \(q_{jk}(x)=\int_0^1\lambda^{p-2}\{x^jP_k(\lambda x,0)-x^kP_j(\lambda x,0)\}\,d\lambda\).
Evidence: Poincaré homotopy (1.69) of the \((p-1)\)-form \(\sum_k(-1)^{k-1}P_k(x,0)dx^{\hat k}\)
gives the factor \(\lambda^{p-1}/\lambda\). Check: \(p=3\), \(P=(1,0,0)\) (a null divergence
depending on \(x\) only): the printed \(q\) gives \(\sum_jD_jq_{j1}=D_2x^2+D_3x^3=2\ne P_1\); with
the factor \(\lambda\) one gets \(1\). For \(p=2\) (the case worked in the source) the two agree.
Target: [O86.05.4.16].

### O86-E05.0.01. Commutation criterion in Exercise 5.4

Status: Confirmed.
Location: Exercises, p. 369, Exercise 5.4.
Printed: For polynomials \(P=p(u)u_x+\tilde p(u)\), \(Q=q(u)\), \(\mathbf v_P\) and \(\mathbf v_Q\)
commute iff \(p\) is constant and either \(\tilde p=0\) or \(q=0\).
Correct: They commute iff \(q=0\), or \(p\) is constant and \(q\tilde p'=q'\tilde p\) (for
polynomials: \(\tilde p=cq\), so \(Q\) is a combination of \(P\) and \(u_x\)).
Evidence: The bracket characteristic is \(\mathrm{pr}\,\mathbf v_P(Q)-\mathrm{pr}\,\mathbf
v_Q(P)=q'\tilde p-q\tilde p'-qp'u_x\). For \(p=1\), \(\tilde p=u\), \(q=u\) it vanishes although
\(\tilde p\ne0\ne q\); for \(q=0\) it vanishes for every \(p\).
Target: [O86.05.0.03].

### O86-E05.0.02. Elementary sine-Gordon conservation law in Exercise 5.21

Status: Confirmed.
Location: Exercises, p. 372, Exercise 5.21, first display.
Printed: \(D_t(\tfrac12u_t^2)+D_x(\cos u)=0\) for \(u_{xt}=\sin u\).
Correct: \(D_x(\tfrac12u_t^2)+D_t(\cos u)=0\) (characteristic form
\(D_x(\tfrac12u_t^2)+D_t(\cos u)=u_t(u_{xt}-\sin u)\)).
Evidence: \(D_t(\tfrac12u_t^2)+D_x(\cos u)=u_tu_{tt}-u_x\sin u\), which does not vanish on
solutions (on the solution manifold \(u_t,u_{tt},u_x\) are free jet coordinates).
Target: [O86.05.0.06].

### O86-E05.0.03. Skew-adjoint Fréchet derivatives (Exercise 5.31)

Status: Confirmed.
Location: Exercises, p. 374, Exercise 5.31.
Printed: For \(p=q=1\), \(\mathsf D_P\) is skew-adjoint iff \(P(x,u^{(2n+1)})\) is linear in
\(u,u_x,\dots,u_{2n+1}\).
Correct: Skew-adjointness of \(\mathsf D_P\) implies that \(P\) is affine in \(u,\dots,u_{2n+1}\),
\(P=a(x)+\sum_kc_k(x)u_k\); conversely such a \(P\) has \(\mathsf D_P=\sum_kc_kD_x^k\), which is
skew-adjoint only under conditions on the \(c_k\).
Evidence: \(P=u\) is linear but \(\mathsf D_P=1\) is self-adjoint, not skew-adjoint.
Target: [O86.05.0.08].

### Conventions and notation (not errata)

- The source writes \(\mathsf D_P\) (sans-serif D) for the Fréchet derivative and \(D_i\) for total
  derivatives; the synopsis keeps this.
- The bracket of evolutionary fields has characteristic \(\mathrm{pr}\,\mathbf v_Q(R)-
  \mathrm{pr}\,\mathbf v_R(Q)=\mathsf D_R(Q)-\mathsf D_Q(R)\) (5.22), the commutator of the
  prolonged fields.
- Flows of generalized vector fields (5.14), Theorem 5.10, Proposition 5.40 and (5.28) are
  conditional on existence and uniqueness for evolution equations, as the source states
  (p. 304); the synopsis keeps these hypotheses explicit.
- \(D_x^{-1}\) acts only on total \(x\)-derivatives and is defined up to an additive constant
  (p. 320); the recursion-operator statements for KdV are on this domain.
- In Example 5.47 the dilatation operator \(\mathscr D\) is replaced by \(\mathscr M=\mathscr D+
  \tfrac12\) to obtain a conservation law; this is a stated modification, not an erratum.
- In (5.116) and the table of Example 5.47 the formulas are recorded as printed, except rows 4
  and 5 of the table, which were checked ([O86-E05.3.04]).
- Exercise 5.41, pp. 376–377: the list [Olver 1993 corrections], 2nd ed. p. 387, Exercise 5.51,
  adds "totally nondegenerate" to the hypotheses and deletes the first sentence of the hint
  ("First reduce to the case of a homogeneous conservation law"), which is valid only for
  polynomial conservation laws. In the 1986 text total nondegeneracy is the blanket hypothesis of
  Chapter 5 (p. 296), so the statement [O86.05.0.11] is not affected; hints are not synopsized.

## Chapter 6. Finite-Dimensional Hamiltonian Systems

### O86-E06.2.01. Sign of \(\{\theta,\phi\}\) on the spheres in \(\mathfrak{so}(3)^*\)

Status: Confirmed.
Location: §6.2, p. 393, Example 6.20.
Printed: \(\{\theta,\phi\}=-u\cdot(\nabla\theta\times\nabla\phi)=-1/(\rho\sin\phi)\), so the induced
bracket is \(\{\tilde F,\tilde H\}=-(\rho\sin\phi)^{-1}(\tilde F_\theta\tilde H_\phi-
\tilde F_\phi\tilde H_\theta)\).
Correct: \(\{\theta,\phi\}=-u\cdot(\nabla\theta\times\nabla\phi)=+1/(\rho\sin\phi)\), and
\(\{\tilde F,\tilde H\}=(\rho\sin\phi)^{-1}(\tilde F_\theta\tilde H_\phi-\tilde F_\phi
\tilde H_\theta)\).
Evidence: With \(u=\rho(\cos\theta\sin\phi,\sin\theta\sin\phi,\cos\phi)\),
\(\nabla\theta=(\rho\sin\phi)^{-1}(-\sin\theta,\cos\theta,0)\) and
\(\nabla\phi=\rho^{-1}(\cos\theta\cos\phi,\sin\theta\cos\phi,-\sin\phi)\), so
\(\nabla\theta\times\nabla\phi=-(\rho^2\sin\phi)^{-1}\hat u\) and
\(-u\cdot(\nabla\theta\times\nabla\phi)=1/(\rho\sin\phi)\). A symbolic evaluation at
\(u=(1/2,1/3,1/5)\) gives \(6\sqrt{13}/13=1/(\rho\sin\phi)>0\). Consistent with Example 6.23:
there \(\{\theta,z\}=-1\) with \(z=\rho\cos\phi\), and \(\{\theta,\rho\cos\phi\}=-\rho\sin\phi
\{\theta,\phi\}=-1\) requires \(\{\theta,\phi\}=+1/(\rho\sin\phi)\).
Target: [O86.06.2.05].

### O86-E06.2.02. Orientation of the canonical pair in the proof of Darboux' theorem

Status: Confirmed.
Location: §6.2, p. 395, proof of Theorem 6.22.
Printed: \(Q\) is chosen with \(\hat{\mathbf v}_P(Q)=\{Q,P\}=1\), giving
\(\hat{\mathbf v}_p=\partial_q\), \(\hat{\mathbf v}_q=-\partial_p\); then "the bracket relations
\(\{p,q\}=1\), …" and the structure matrix in \((p,q,y)\) is printed with first row
\((0,1,0)\) and second row \((-1,0,0)\).
Correct: The construction gives \(\{q,p\}=1\), i.e. \(\{p,q\}=-1\), and the structure matrix has
first row \((0,-1,0)\), second row \((1,0,0)\), in agreement with the canonical bracket (6.1),
(6.2) used in the statement of the theorem.
Evidence: \(\{q,p\}=\hat{\mathbf v}_p(q)=\partial_q(q)=1\) directly from the printed
\(\hat{\mathbf v}_p=\partial_q\); equally \(\{p,q\}=\hat{\mathbf v}_q(p)=-\partial_p(p)=-1\).
Target: [O86.06.2.07].

### O86-E06.3.01. Sign in the reduced equation for \(q\)

Status: Confirmed.
Location: §6.3, p. 402, proof of Theorem 6.35, structure matrix and (6.27b).
Printed: \(J(p,q,y)=\begin{pmatrix}0&1&0\\-1&0&a\\0&-a^T&\tilde J\end{pmatrix}\) and
\(dq/dt=-\partial H/\partial p+\sum_ja^j\,\partial H/\partial y^j\) (6.27b).
Correct: With \(\hat{\mathbf v}_P=\partial_q\) one has \(\{q,p\}=1\), so
\(J(p,q,y)=\begin{pmatrix}0&-1&0\\1&0&a\\0&-a^T&\tilde J\end{pmatrix}\) and
\(dq/dt=\partial H/\partial p+\sum_ja^j\,\partial H/\partial y^j\).
Evidence: \(dq/dt=\{q,H\}=\{q,p\}H_p+\sum_j\{q,y^j\}H_{y^j}\) and
\(\{q,p\}=\hat{\mathbf v}_P(q)=1\). Example 6.36 (p. 403) applies the theorem and obtains
\(dq/dt=H_p+H_y=y\) for \(H=y^2-py+\tfrac12p^2+V(r)\), which agrees with the corrected sign
(\(H_p+H_y=(-y+p)+(2y-p)=y\)) and not with the printed one.
Target: [O86.06.3.04].

### O86-E06.3.02. Sign of the reduced Hamiltonian in Proposition 6.37

Status: Confirmed.
Location: §6.3, p. 405, (6.31b) and the following sentence.
Printed: \(dy^i/dq=\sum_j\tilde J^{ij}(y)\,(\partial H/\partial y^j)/(\partial H/\partial p)=
\sum_j\tilde J^{ij}(y)\,\partial K/\partial y^j\); the system is Hamiltonian with Hamiltonian
function \(K(w,q,y)\).
Correct: \(dy^i/dq=\sum_j\tilde J^{ij}(y)\,(\partial H/\partial y^j)/(\partial H/\partial p)=
-\sum_j\tilde J^{ij}(y)\,\partial K/\partial y^j\); the reduced Hamiltonian is \(-K\). The
conclusion of Proposition 6.37 is unaffected.
Evidence: Differentiating \(H(K(w,q,y),q,y)=w\) in \(y^j\) gives \(H_p\,K_{y^j}+H_{y^j}=0\), i.e.
\(\partial K/\partial y^j=-(\partial H/\partial y^j)/(\partial H/\partial p)\).
Target: [O86.06.3.06].

### O86-E06.3.03. Co-adjoint action for the group of Example 6.40

Status: Confirmed.
Location: §6.3, p. 412, after Proposition 6.47.
Printed: \(\mathrm{Ad}^*g(c_1\omega_1+c_2\omega_2)=e^{-\varepsilon_2}c_1\omega_1+
(\varepsilon_1\varepsilon_2^{-1}(e^{-\varepsilon_2}-1)c_1+c_2)\omega_2\) for
\(g=\exp(\varepsilon_1\mathbf v+\varepsilon_2\mathbf w)\).
Correct: The \(\omega_2\)-coefficient is \(c_2+\varepsilon_1\varepsilon_2^{-1}(1-e^{-\varepsilon_2})
c_1\). The stated isotropy groups (\(G_a\) trivial unless \(c_1=0\)) are unaffected.
Evidence: Equivariance (6.37) with \(P=p\,\omega_1+(pq+\tilde p)\omega_2\): the flow of
\(\varepsilon_1\mathbf v+\varepsilon_2\mathbf w\), \(\mathbf v=\partial_q\),
\(\mathbf w=-p\partial_p+q\partial_q+\partial_{\tilde q}\), is \(p\mapsto e^{-\varepsilon_2}p\),
\(q\mapsto e^{\varepsilon_2}q+\varepsilon_1\varepsilon_2^{-1}(e^{\varepsilon_2}-1)\),
\(\tilde p\mapsto\tilde p\), so \(P_1\mapsto e^{-\varepsilon_2}c_1\) and
\(P_2=pq+\tilde p\mapsto c_2+\varepsilon_1\varepsilon_2^{-1}(1-e^{-\varepsilon_2})c_1\).
Integrating the generator (6.24) directly (\(\mathrm{ad}^*\) with \([\mathbf v,\mathbf w]=\mathbf v\))
gives the same result; to first order the coefficient is \(c_2+\varepsilon_1c_1\), whereas the
printed formula gives \(c_2-\varepsilon_1c_1\).
Target: [O86.06.3.13].

### O86-E06.0.01. A fixed point forces \(a=0\) only on its own symplectic leaf

Status: Confirmed.
Location: Exercises, p. 418, Exercise 6.2.
Printed: If \(\hat{\mathbf v}_P\), \(P=P(x)\), is a Hamiltonian symmetry of a time-independent
Hamiltonian system, then \(P(x(t))=at+b\) on each solution; if the system has a fixed point
\(x_0\), then \(a=0\) and \(P\) is a first integral.
Correct: \(a=\{P,H\}\) is a distinguished function, constant on symplectic leaves; a fixed
point \(x_0\) gives \(a=0\) on the leaf through \(x_0\). \(P\) is a first integral when \(M\) is
symplectic and connected, but not in general on a Poisson manifold.
Evidence: On \(\mathbb R^3\) with the canonical bracket in \((p,q,z)\) (\(z\) distinguished), take
\(H=zp\), \(P=q\). Then \(\hat{\mathbf v}_H=z\partial_q\), \(\{P,H\}=z\) is distinguished, so
\([\hat{\mathbf v}_H,\hat{\mathbf v}_P]=\hat{\mathbf v}_{\{P,H\}}=\hat{\mathbf v}_z=0\) by (6.8) and \(\hat{\mathbf v}_P=
-\partial_p\) is a Hamiltonian symmetry. Every point with \(z=0\) is fixed, yet
\(q(t)=q_0+z_0t\) with \(a=z_0\ne0\) for \(z_0\ne0\).
Target: [O86.06.0.01].

### O86-E06.0.02. Nondegeneracy hypothesis in Ostrogradsky's construction

Status: Confirmed.
Location: Exercises, p. 420, Exercise 6.16.
Printed: For \(\int L(t,u^{(n)})dt\), \(u\in\mathbb R\), with \(q^k=u_{k-1}\), \(p^k=\sum_{j\ge
k}(-D_t)^{j-k}\partial L/\partial u_j\) and \(H=-L+p^1q^2+\cdots+p^{n-1}q^n+p^nu_n\), "where
\(u_n\) is determined implicitly from the equation for \(p^n\)", \(u\) solves the Euler–Lagrange
equation iff \((p,q)\) solves Hamilton's equations.
Correct: Assume \(\partial^2L/\partial u_n^2\ne0\), so that \(p^n=\partial L/\partial u_n\) can be
solved locally for \(u_n\) in terms of \(t,q,p^n\).
Evidence: For \(n=1\) and \(L=uu_t\), \(p^1=\partial L/\partial u_t=u\) does not involve \(u_t\),
so \(u_1\) is not determined and \(H\) is not defined as a function of \((p,q)\); here every \(u\)
solves the Euler–Lagrange equation \(u_t-u_t=0\).
Published: [Olver 1993 corrections], 2nd ed. p. 430, Exercise 6.16 (1986: p. 420, Exercise
6.16). [Olver 1993 corrected-printing corrections], 2nd ed. p. 430, Exercise 6.16.
Target: [O86.06.0.03].

### Conventions and notation (not errata)

- \(\hat{\mathbf v}_H(F)=\{F,H\}\) (6.4), hence \(\hat{\mathbf v}_{\{F,H\}}=[\hat{\mathbf v}_H,
  \hat{\mathbf v}_F]\) (6.8); the minus sign relative to \([\hat{\mathbf v}_F,\hat{\mathbf v}_H]\)
  is a convention, not an error.
- Hamiltonian group actions require \(\{P_i,P_j\}=-\sum_kc^k_{ij}P_k\) (Definition 6.41), matching
  the right-invariant Lie algebra convention of Chapter 1; with the \(\mathfrak{so}(3)\) basis of
  Example 6.9 the Lie–Poisson bracket is \(-u\cdot(\nabla F\times\nabla H)\).
- The source says "distinguished function" for a Casimir function.
- In Theorem 6.35 the source writes \(a=a(p,q,y)\); the Jacobi identity forces \(a\) to be
  independent of \(q\). This over-generality is harmless.
- Example 6.34's boost generator and Example 6.39's quadrature constants are recorded as printed.

## Chapter 7. Hamiltonian Methods for Evolution Equations

### O86-E07.1.01. Last term in the Jacobi computation for the second KdV operator

Status: Confirmed.
Location: §7.1, p. 429, Example 7.6, last display.
Printed: \(\int P\,\mathrm{pr}\,\mathbf v_{\mathcal E(R)}(\mathcal E)Q\,dx=\int[\tfrac23PR_{xxx}Q_x+
\tfrac13PR_{xxxx}Q+\tfrac49uPR_xQ_x+\tfrac29u_xPRQ_x+\tfrac29uPR_{xx}Q+\tfrac13u_xPR_xQ+
\tfrac19u_xPRQ]\,dx\).
Correct: The last term is \(\tfrac19u_{xx}PRQ\).
Evidence: \(\mathrm{pr}\,\mathbf v_{\mathcal ER}(\mathcal E)=\tfrac23(\mathcal ER)D_x+
\tfrac13D_x(\mathcal ER)\) with \(\mathcal ER=R_{xxx}+\tfrac23uR_x+\tfrac13u_xR\), and
\(\tfrac13D_x(\mathcal ER)=\tfrac13R_{xxxx}+\tfrac29uR_{xx}+\tfrac13u_xR_x+\tfrac19u_{xx}R\); the
\(R\)-term comes only from \(\tfrac13D_x(\tfrac13u_xR)\). All other printed terms agree.
Target: [O86.07.1.07].

### O86-E07.0.01. Number of conserved moments for \(u_t=D_x^mQ\)

Status: Confirmed.
Location: Exercises, p. 456, Exercise 7.8(b).
Printed: Every evolution equation \(u_t=D_x^mQ\), \(x,u\in\mathbb R\), conserves the first
\(m+1\) moments \(\mathcal M_j=\int x^ju\,dx\), \(j=0,1,\dots,m\).
Correct: Only the first \(m\) moments, \(j=0,\dots,m-1\), are conserved in general.
Evidence: \(\frac{d}{dt}\int x^ju\,dx=\int x^jD_x^mQ\,dx=(-1)^m\int(D_x^mx^j)Q\,dx\), which vanishes
for \(j<m\) but equals \((-1)^mm!\int Q\,dx\) for \(j=m\). For \(m=1\), \(Q=u\), the solution
\(u=f(x+t)\) has \(\int xu\,dx=\mathcal M_1(0)-t\,\mathcal M_0\), not constant when
\(\mathcal M_0\ne0\). The same count appears in Example 7.16: for KdV (\(m=1\)) \(\int xu\,dx\)
is linear in \(t\), not constant.
Target: [O86.07.0.02].

### Conventions and notation (not errata)

- The KdV equation in Chapter 7 is \(u_t=u_{xxx}+uu_x\) (as in Chapter 5); other normalizations
  (e.g. \(u_t=u_{xxx}+6uu_x\)) rescale \(\mathcal E\) and the \(\mathcal H_n\).
- \(\hat{\mathbf v}_{\{\mathcal P,\mathcal Q\}}=[\hat{\mathbf v}_{\mathcal Q},\hat{\mathbf
  v}_{\mathcal P}]\) (7.22) follows the sign convention of (6.8).
- Characteristics of point symmetries are given "up to sign" in Examples 7.16 and 7.17 (e.g. the
  rotation's \(\omega\)-characteristic is \(-(y\omega_x-x\omega_y)\) with the convention
  \(Q=\phi-\xi u_x-\eta u_y\)); this does not affect the conservation laws.
- Variational identities are formal; boundary terms are dropped, and the Euler-equation bracket
  needs modification on bounded domains (Notes, p. 453).
- \(\mathcal D^{-1}\) in recursion operators is formal; Theorem 7.24 assumes explicitly that each
  \(K_{n-1}\) lies in the image of \(\mathcal D\).

## Published corrections to material outside the synopses

The published lists also correct the following statements and formulas of the 1986 text. The
synopsis does not state them, so they have no erratum entry and no synopsis target. They are listed
here so that this file accounts for every mathematical item of the lists that applies to the first
edition.

- §1.1, p. 5: the torus \(T^2\) "can be covered by two coordinate charts"
  \(U_1=\{0<\theta<2\pi,\ 0<\rho<2\pi\}\), \(U_2=\{\pi<\theta<3\pi,\ \pi<\rho<3\pi\}\). These miss
  the point \((\theta,\rho)=(0,\pi)\) (\(\theta\equiv0\) is not in \(U_1\), \(\rho\equiv\pi\) is not
  in \(U_2\)); a third chart such as \(U_3=\{\frac12\pi<\theta<\frac52\pi,\
  \frac12\pi<\rho<\frac52\pi\}\) is needed. [Olver 1993 corrections], 2nd ed. p. 5, ll. 24–27, gives
  this correction. Checked. Near [O86.01.1.02], which mentions \(T^2\) but not these charts.
- §1.5, pp. 65–66, proof of the Poincaré lemma: in the display
  \(\exp(\varepsilon\mathbf v_0)^*[\omega|_{\exp(\varepsilon\mathbf v_0)x}]=\exp(\varepsilon
  \mathbf v_0)^*[\sum_I\alpha_I(e^\varepsilon x)dx^I]=\sum_I\alpha_I(e^\varepsilon x)e^{k
  \varepsilon}dx^I\) (p. 65, last line) the middle term is to be deleted, and in
  \(h_0^\varepsilon(\omega)=-\int_{\log\varepsilon}^1(\mathbf v_0\lrcorner\omega)[\lambda x]\,
  d\lambda/\lambda\) "(using the change of variables \(\lambda=\log\tilde\varepsilon\))" (p. 66)
  the lower limit is \(e^\varepsilon\) and the substitution is \(\lambda=e^{\tilde\varepsilon}\).
  [Olver 1993 corrections], 2nd ed. p. 64, ll. 10, 18, 19, gives these corrections. Checked: with
  \(\lambda=e^{\tilde\varepsilon}\), \(\tilde\varepsilon\in[\varepsilon,0]\) maps to
  \(\lambda\in[e^\varepsilon,1]\) and \(d\tilde\varepsilon=d\lambda/\lambda\). The formulas
  (1.67)–(1.69) stated in [O86.01.5.13] are unaffected.
- §2.1, pp. 82–83, proofs of Proposition 2.6 and Theorem 2.8: the final step writes an element of
  \(G_x\) as a product of exponentials of infinitesimal generators and applies the one-parameter
  result factor by factor. For a local group action, \(g=g_1g_2\) with \(g,g_1,g_2\in G_x\) does
  not guarantee that \(g_1\cdot(g_2\cdot x)\) is defined. [Olver 1993 corrections], 2nd ed.
  pp. 79–81, replaces this step by an open-and-closed argument on the connected \(G_x\). The 1986
  proofs have the same gap; the statements are unaffected. Checked against the 1986 text.
- §2.3, p. 109, derivation of (2.31): in \(\sum_l\frac{\partial^2\Xi^k_{-\varepsilon}}{\partial
  \tilde x^j\partial\tilde x^l}(\Xi_{-\varepsilon}(x))\frac{d\Xi^l_\varepsilon}{d\varepsilon}(x)\)
  the argument should be \(\Xi_\varepsilon(x)\). [Olver 1993 corrections], 2nd ed. p. 106,
  l. −5, gives this correction. Checked; the term vanishes at \(\varepsilon=0\) in either form, so
  (2.31) is unaffected.
- §3.1, p. 190: in the chain rule \(\frac{\partial u}{\partial x}=\frac{\partial}{\partial
  x}[\delta(\hat x,y,v)]=\frac{\partial\delta}{\partial\hat x}+\frac{\partial\delta}{\partial y}
  \frac{\partial\eta}{\partial x}+\frac{\partial\delta}{\partial v}\frac{\partial v}{\partial y}
  \frac{\partial\eta}{\partial x}\) the first term should be \(\frac{\partial\delta}{\partial\hat
  x}\frac{\partial\hat x}{\partial x}\) (the parametric variables \(\hat x\) are only part of
  \(x\)). [Olver 1993 corrections], 2nd ed. p. 187, l. 14, gives this correction. Checked.
- Exercise 4.13(a), p. 290: the claim that the reduced system \(\Delta/G\) for the \(G\)-invariant
  solutions of an Euler–Lagrange system with a regular variational (or divergence) symmetry group
  is again an Euler–Lagrange system on \(M/G\) is turned into a question by [Olver 1993
  corrections], 2nd ed. p. 285, l. 7, which refers to I. M. Anderson and M. Fels, Symmetry
  reduction of variational bicomplexes and the principle of symmetric criticality, Amer. J. Math.
  119 (1997) 609–670, for the conditions under which it holds. Not checked independently.

[Olver 1993 corrections]: https://www-users.cse.umn.edu/~olver/book_/sym1.pdf
[Olver 1993 corrected-printing corrections]: https://www-users.cse.umn.edu/~olver/book_/sym2.pdf
[O86.01.0.17]: SYNOPSIS-Olver1986.md#o8601017-the-exponential-map-of-sl2
[O86.01.0.20]: SYNOPSIS-Olver1986.md#o8601020-conformal-maps-from-rotations-of-the-sphere
[O86.01.1.02]: SYNOPSIS-Olver1986.md#o8601102-elementary-examples-of-manifolds
[O86.01.1.05]: SYNOPSIS-Olver1986.md#o8601105-immersed-submanifolds-and-examples
[O86.01.1.07]: SYNOPSIS-Olver1986.md#o8601107-implicitly-defined-submanifolds
[O86.01.2.07]: SYNOPSIS-Olver1986.md#o8601207-a-local-group-that-is-not-global
[O86.01.3.12]: SYNOPSIS-Olver1986.md#o8601312-commuting-flows
[O86.01.5.13]: SYNOPSIS-Olver1986.md#o8601513-homotopy-operators-and-the-proof-of-the-poincaré-lemma
[O86.02.0.06]: SYNOPSIS-Olver1986.md#o8602006-navierstokes-versus-euler-symmetries
[O86.02.0.07]: SYNOPSIS-Olver1986.md#o8602007-group-classification-of-nonlinear-heat-conduction
[O86.02.0.14]: SYNOPSIS-Olver1986.md#o8602014-symmetries-of-u_xx--0-maximal-symmetry-of-odes
[O86.02.3.11]: SYNOPSIS-Olver1986.md#o8602311-second-prolongation-of-rotations-curvature
[O86.02.4.05]: SYNOPSIS-Olver1986.md#o8602405-symmetry-algebra-of-the-wave-equation-in-21-dimensions
[O86.02.6.03]: SYNOPSIS-Olver1986.md#o8602603-necessity-of-the-infinitesimal-criterion
[O86.02.6.09]: SYNOPSIS-Olver1986.md#o8602609-prolongation-of-systems-total-nondegeneracy
[O86.03.0.01]: SYNOPSIS-Olver1986.md#o8603001-mach-number-and-blast-wave-scaling-laws
[O86.03.2.02]: SYNOPSIS-Olver1986.md#o8603202-scale-invariant-solutions-of-the-heat-equation
[O86.03.2.04]: SYNOPSIS-Olver1986.md#o8603204-travelling-waves-of-the-kortewegde-vries-equation
[O86.03.2.10]: SYNOPSIS-Olver1986.md#o8603210-no-so3-invariant-solutions-of-the-euler-equations
[O86.03.2.11]: SYNOPSIS-Olver1986.md#o8603211-additional-symmetry-of-a-reduced-system-kapitanskiis-solutions
[O86.03.3.07]: SYNOPSIS-Olver1986.md#o8603307-adjoint-table-of-the-kdv-symmetry-algebra
[O86.03.3.11]: SYNOPSIS-Olver1986.md#o8603311-the-adjoint-invariant-of-the-heat-algebra
[O86.03.3.15]: SYNOPSIS-Olver1986.md#o8603315-classification-of-heat-invariant-solutions
[O86.03.4.06]: SYNOPSIS-Olver1986.md#o8603406-the-pi-theorem
[O86.04.1.08]: SYNOPSIS-Olver1986.md#o8604108-euler-operator-under-point-transformations-of-the-plane
[O86.04.3.08]: SYNOPSIS-Olver1986.md#o8604308-characteristics-in-the-wave-equation-example
[O86.04.4.04]: SYNOPSIS-Olver1986.md#o8604404-conservation-laws-of-hyperelasticity
[O86.04.4.07]: SYNOPSIS-Olver1986.md#o8604407-the-ten-geometric-conservation-laws-of-the-wave-equation
[O86.05.0.03]: SYNOPSIS-Olver1986.md#o8605003-elementary-results-on-symmetries-and-recursion-operators
[O86.05.0.06]: SYNOPSIS-Olver1986.md#o8605006-noether-type-results-in-exercises
[O86.05.0.08]: SYNOPSIS-Olver1986.md#o8605008-operator-identities
[O86.05.0.11]: SYNOPSIS-Olver1986.md#o8605011-higher-order-divergences-and-homogeneous-systems
[O86.05.1.16]: SYNOPSIS-Olver1986.md#o8605116-polynomial-evolution-equations-the-commutativity-theorem
[O86.05.1.17]: SYNOPSIS-Olver1986.md#o8605117-leading-coefficient-of-an-equation-with-a-nonelementary-symmetry
[O86.05.2.09]: SYNOPSIS-Olver1986.md#o8605209-the-kdv-hierarchy
[O86.05.3.04]: SYNOPSIS-Olver1986.md#o8605304-conservation-laws-of-burgers-equation
[O86.05.3.10]: SYNOPSIS-Olver1986.md#o8605310-the-rungelenz-vector-of-the-kepler-problem
[O86.05.3.14]: SYNOPSIS-Olver1986.md#o8605314-conservation-laws-of-the-two-dimensional-wave-equation
[O86.05.4.10]: SYNOPSIS-Olver1986.md#o8605410-helmholtz-conditions-the-inverse-problem
[O86.05.4.15]: SYNOPSIS-Olver1986.md#o8605415-null-lagrangians-as-explicit-divergences
[O86.05.4.16]: SYNOPSIS-Olver1986.md#o8605416-null-divergences-as-explicit-total-curls
[O86.06.0.01]: SYNOPSIS-Olver1986.md#o8606001-first-integrals-and-distinguished-functions
[O86.06.0.03]: SYNOPSIS-Olver1986.md#o8606003-hamiltonjacobi-and-ostrogradsky
[O86.06.2.05]: SYNOPSIS-Olver1986.md#o8606205-symplectic-spheres-in-mathfrakso3
[O86.06.2.07]: SYNOPSIS-Olver1986.md#o8606207-darboux-theorem
[O86.06.3.04]: SYNOPSIS-Olver1986.md#o8606304-reduction-of-order-by-a-first-integral
[O86.06.3.06]: SYNOPSIS-Olver1986.md#o8606306-reduction-by-the-hamiltonian-itself
[O86.06.3.13]: SYNOPSIS-Olver1986.md#o8606313-residual-symmetry-group-of-a-level-set
[O86.07.0.02]: SYNOPSIS-Olver1986.md#o8607002-conservation-laws-moments-and-noether
[O86.07.1.07]: SYNOPSIS-Olver1986.md#o8607107-the-two-hamiltonian-structures-of-the-kdv-equation
