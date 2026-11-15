# Errata and source checks: Bluman–Kumei (1989)

Reference: George W. Bluman and Sukeyuki Kumei, *Symmetries and Differential Equations*,
Applied Mathematical Sciences 81, Springer-Verlag, New York, 1989. The local copy is
[References/BlumanKumei1989SymmetriesDifferentialEquations-Springer.AMS.pdf](References/BlumanKumei1989SymmetriesDifferentialEquations-Springer.AMS.pdf).
Companion synopsis: [SYNOPSIS-BK](SYNOPSIS-BK.md).

Locators use printed page numbers. To get the one-based PDF page number, add 12.

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

- the location, as section, printed page, equation or theorem number, and line where useful
  (negative line numbers count from the bottom of the page);
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries.

Synopsis entries cite errata by id. An erratum id \(\mathrm{BK}\text{-}\mathrm Ecc.s.nn\) is
the \(nn\)-th erratum located in section \(s\) of chapter \(cc\).

## Scope

These are observations about this edition, not an official publisher list. No claim is made
that formulas without an erratum are free of errors. Formulas that the synopsis marks "as
printed" were transcribed from the page images without an independent check. Corrected
formulas in the synopsis are statements to be formalized. They are not Lean proofs.

Missing hypotheses are recorded as errata only when the stated claim is false without them
(for example a global or pointwise claim that fails at a fixed point of the group). The
book's standing convention that all statements are local, on domains where the relevant
Jacobians and denominators are nonzero, is not itself an erratum; it is stated in the
synopsis Conventions.

Each chapter section ends with a list of conventions and notation that are not errata.

## Summary by chapter

- Chapter 1. Dimensional Analysis, Modelling, and Invariance: 16 entries, 0 errata.
- Chapter 2. Lie Groups of Transformations and Infinitesimal Transformations: 55 entries, 2 errata (Confirmed 2).
- Chapter 3. Ordinary Differential Equations: 49 entries, 5 errata (Confirmed 5).
- Chapter 4. Partial Differential Equations: 49 entries, 9 errata (Confirmed 8, Normalization check 1).
- Chapter 5. Noether's Theorem and Lie–Bäcklund Symmetries: 28 entries, 2 errata (Confirmed 2).
- Chapter 6. Construction of Mappings Relating Differential Equations: 27 entries, 3 errata (Confirmed 3).
- Chapter 7. Potential Symmetries: 18 entries, 5 errata (Confirmed 4, Normalization check 1).
- Total: 242 entries, 26 errata (Confirmed 24, Normalization check 2).

## Chapter 1. Dimensional Analysis, Modelling, and Invariance

No errata were found in Chapter 1. The Pi-theorem, the scaling reductions of the heat
equation and the Blasius boundary value problem, and the formulas checked there hold as
printed.

### Conventions and notation (not errata)

- Dimension exponents are real; quantities raised to real powers are taken positive, as the
  source assumes implicitly for measured quantities.
- The scaling (change of units) group of §1.2 acts on the measured values, not on the
  fundamental dimensions; the Pi-theorem's dimensionless groups are determined up to the
  choice of a basis of the kernel of the dimension matrix.

## Chapter 2. Lie Groups of Transformations and Infinitesimal Transformations

### BK-E02.2.01. Lie series of a merely smooth function

Status: Confirmed.
Location: §2.2.3, p. 42, Corollary 2.2.3-1, (2.33).
Printed: for any infinitely differentiable function \(F(x)\),
\(F(x^*)=F(e^{\varepsilon X}x)=e^{\varepsilon X}F(x)=\sum_k\frac{\varepsilon^k}{k!}X^kF(x)\).
Correct: the identity holds for \(|\varepsilon|\) small when \(F\) (and the group) is
real-analytic near the orbit; for \(F\in C^\infty\) the series is only the Taylor series of
\(\varepsilon\mapsto F(x^*)\) at \(\varepsilon=0\) and need not converge to it.
Evidence: \(n=1\), \(X=\partial_x\) (translations \(x^*=x+\varepsilon\)),
\(F(x)=e^{-1/x^2}\) (\(F(0)=0\)), \(x=0\): every \(X^kF(0)=F^{(k)}(0)=0\), so the series is
\(0\), while \(F(x^*)=e^{-1/\varepsilon^2}\ne0\) for \(\varepsilon\ne0\). The proofs of
Theorems 2.2.4-1, 2.2.4-2 and 2.2.7-3 rely on (2.33); their conclusions remain true for
\(C^1\) functions through the identity \(\frac{d}{d\varepsilon}F(x^*)=(XF)(x^*)\) (2.30).
Target: [BK.02.2.07], [BK.02.2.09].

### BK-E02.2.02. Canonical coordinates require a nonvanishing generator

Status: Confirmed.
Location: §2.2.5, p. 45, Theorem 2.2.5-3.
Printed: any Lie group of transformations (2.6) can be transformed to canonical
coordinates (2.47), with no restriction on the point.
Correct: canonical coordinates exist on a neighbourhood of every point \(x_0\) with
\(\xi(x_0)\ne0\), and do not exist on any neighbourhood of a zero of \(\xi\).
Evidence: in canonical coordinates the generator is \(\partial/\partial y_n\), which vanishes
nowhere, and a change of coordinates maps a zero of a vector field to a zero (by (2.45)).
For the rotations \(X=-y\partial_x+x\partial_y\) of \(\mathbb R^2\), \(X=0\) at the origin,
so no canonical coordinates exist on any neighbourhood of the origin; the source's own
choice \(r=\sqrt{x^2+y^2}\), \(s=\tan^{-1}(y/x)\) is singular there.
Target: [BK.02.2.12].

### Conventions and notation (not errata)

- The projective generators \(X_1,X_2\) in the commutator table (2.180) are the negatives of
  the generators obtained from (2.155) for \(\varepsilon_1,\varepsilon_2\); the table is
  consistent with the generators as listed with it.
- Definition 2.4.4-2 (solvability by a chain \(\mathcal L^{(k-1)}\) an ideal of
  \(\mathcal L^{(k)}\), not of \(\mathcal L\)) is equivalent, for finite-dimensional real Lie
  algebras, to the usual definition by the derived series.
- Lie series \(e^{\varepsilon X}\) are used formally throughout the chapter; identities
  between them hold as identities of formal power series in \(\varepsilon\), and as
  identities of functions for analytic data (see [BK-E02.2.01]).
- The source writes the letter \(X\) for both the transformation \(x^*=X(x;\varepsilon)\) and
  the generator.

## Chapter 3. Ordinary Differential Equations

### BK-E03.1.01. Constant of integration for homogeneous equations

Status: Confirmed.
Location: §3.1.2 (2), p. 94, (3.17).
Printed: \(y=\exp\big[\int^{y/x}G(r)\,dr\big]+C\).
Correct: \(y=C\exp\big[\int^{y/x}G(r)\,dr\big]\), \(C>0\) (on \(y>0\)).
Evidence: (3.16) gives \(s=\log y=\int^{y/x}G(r)dr+C\), and exponentiating multiplies by
\(e^C\). Example: \(y'=y/x+1\), \(F(r)=r+1\), \(G(r)=(r+1)/r\), \(\int G=r+\log r\); the
corrected formula gives \(y=C(y/x)e^{y/x}\), i.e. \(y=x\log(x/C)\), which solves the ODE
(\(y'=\log(x/C)+1=y/x+1\)). The family \(y=x\log(x/2)\) is not of the printed form: the
printed formula would need \(y-C=(y/x)e^{y/x}=y/2\) for all \(x\), impossible with
constant \(C\).
Target: [BK.03.1.04].

### BK-E03.3.01. Sign of the \(y_1^3\) coefficient in the Blasius determining polynomial

Status: Confirmed.
Location: §3.3.4 (2), p. 123, (3.135).
Printed: the coefficient of \((y_1)^3\) is \(-[\eta_{yyy}-3\xi_{xyy}-\frac12y\xi_{yy}]\).
Correct: \(+[\eta_{yyy}-3\xi_{xyy}-\frac12y\xi_{yy}]\).
Evidence: in \(\eta^{(3)}\) the coefficient of \(y_1^3\) is \(\eta_{yyy}-3\xi_{xyy}\) (from
(2.113)), and in \(\frac12y\eta^{(2)}\) it is \(-\frac12y\xi_{yy}\); the \(y_1^3\) terms of
(3.134) therefore sum to \(+(\eta_{yyy}-3\xi_{xyy}-\frac12y\xi_{yy})y_1^3\) (direct
expansion of (3.134) with general \(\xi,\eta\)). The determining equation (3.136d) derived
from it is the same up to an overall sign, so the result (3.140) is unaffected.
Target: [BK.03.3.10].

### BK-E03.4.01. Lie algebras on the plane without two-dimensional subalgebras

Status: Confirmed.
Location: §3.4, pp. 128–129.
Printed: every \(r\)-parameter Lie group of transformations acting on \(\mathbb R^2\)
(\(r\ge2\)) has a two-parameter subgroup, so an \(n\)-th order ODE admitting an
\(r\)-parameter group (\(2\le r\le n\)) can be reduced by at least two orders.
Correct: this holds unless the Lie algebra is isomorphic to \(\mathfrak{so}(3)\); a real Lie
algebra of dimension \(\ge2\) without a two-dimensional subalgebra is isomorphic to
\(\mathfrak{so}(3)\), and \(\mathfrak{so}(3)\) does act on the plane.
Evidence: \(X_1=-y\partial_x+x\partial_y\), \(X_2=\frac12(1+x^2-y^2)\partial_x+xy\partial_y\),
\(X_3=xy\partial_x+\frac12(1-x^2+y^2)\partial_y\) (rotations of the sphere in stereographic
coordinates) satisfy \([X_1,X_2]=-X_3\), \([X_2,X_3]=-X_1\), \([X_3,X_1]=-X_2\) (direct
computation). In \(\mathfrak{so}(3)\cong(\mathbb R^3,\times)\) the bracket of two independent
vectors \(a,b\) is \(a\times b\), which is orthogonal to \(\mathrm{span}(a,b)\), so no
two-dimensional subspace is closed under the bracket.
Target: [BK.03.4.01].

### BK-E03.4.02. Sign in the reduced third-stage equation

Status: Confirmed.
Location: §3.4.3, p. 143, (3.192).
Printed: \(\dfrac{dy_{(3)}}{dx_{(3)}}=-\dfrac{y}{y_1^2}\,\dfrac{[\cdots]}{[\cdots]}\).
Correct: the overall sign is \(+\), with the same brackets.
Evidence: with the printed sign, substituting (3.193) does not give (3.194)
\(dy_{(3)}/dx_{(3)}=-(1+2x_{(3)})\); with \(+\) it does. Direct differentiation of
\(x_{(3)}=yy_2/y_1^2\), \(y_{(3)}=y^2(y_1y_3-2y_2^2)/y_1^4\) along a solution of (3.193)
gives \(dy_{(3)}/dx_{(3)}+1+2x_{(3)}=0\) identically, confirming (3.194).
Target: [BK.03.4.08].

### BK-E03.4.03. Sign of \(c_1\) in the quadrature for \(y_{(2)}\)

Status: Confirmed.
Location: §3.4.3, p. 143, (3.197).
Printed: \(\dfrac{dS}{dR}=\dfrac1R+\dfrac1{R^2-c_1}\) with \(R=x_{(2)}y_{(2)}\),
\(S=\log y_{(2)}\).
Correct: \(\dfrac{dS}{dR}=\dfrac1R+\dfrac1{R^2+c_1}\); the logarithmic case printed as
"\(c_1=C_1^2>0\)" corresponds to \(c_1=-C_1^2<0\).
Evidence: from (3.196), \(x_{(2)}^2y_{(2)1}=-R-R^2-c_1\), and
\(dR/dx_{(2)}=y_{(2)}+x_{(2)}y_{(2)1}=-(R^2+c_1)/x_{(2)}\), \(dS/dx_{(2)}=y_{(2)1}/y_{(2)}
=-(R+R^2+c_1)/(Rx_{(2)})\); dividing gives \(dS/dR=(R^2+R+c_1)/(R(R^2+c_1))
=1/R+1/(R^2+c_1)\). Since both signs of \(c_1\) are treated, the final family of solutions
is unaffected.
Target: [BK.03.4.08].

### Conventions and notation (not errata)

- Cross-reference slips that do not affect the mathematics: "(3.43) of ODE (3.37)" (§3.2.2)
  refers to (3.27); "the projective group (2.179) admitted by (3.126)" refers to (3.129);
  "Theorem 2.4.2-2" on p. 128 refers to Definition/Theorem 2.4.4-2 (solvability); the label
  "(3.114a)" is used for the Blasius equation without being displayed.
- In (3.171) the coordinate \(s=\log v\) satisfies \(Xs=2\) rather than \(1\) for the
  induced generator; it is a canonical coordinate up to a constant factor, which does not
  affect the quadrature.
- Theorem 3.3.1-1 and the reductions of §§3.2–3.4 are local; they assume tacitly that
  \(r_x+r_yy_1\ne0\) (respectively \(u_x+u_yy_1\ne0\), \(\partial v/\partial y_1\ne0\)), and
  solutions in the excluded set (such as invariant solutions) are treated separately in §3.6.
- The argument of §3.6.1 that separatrices and envelope solutions are invariant solutions
  presumes that the separatrix (envelope) is isolated among such curves; the synopsis records
  this as a precise form, not as an erratum.
- The bounds quoted in §3.7 for the dimension of the symmetry group of a system of \(m\)
  ODEs of order \(n\) (\(2(m+1)^2\) for \(n=2\), \(2m^2+mn+2\) for \(n>2\)) are stated as in
  the source, with its references.

## Chapter 4. Partial Differential Equations

### BK-E04.2.01. Theorem 4.2.3-1(i) needs the normalization \(A_{11\cdots1}=1\)

Status: Confirmed.
Location: §4.2.3, p. 174, Theorem 4.2.3-1, (4.35)–(4.36).
Printed: For a \(k\)-th order PDE \(A_{i_1\cdots i_k}(x,u)u_{i_1\cdots i_k}=g(x,u,\ldots,
\underset{k-1}u)\) admitting \(X\), with \(a_j=A_{11\cdots1j}\): if the coefficients do not satisfy
\(A_{i_1\cdots i_k}=(-1)^ka_{i_1}\cdots a_{i_k}\), then \(\partial\xi_i/\partial u=0\) for all
\(i\).
Correct: Part (i) requires the equation to be normalized with \(A_{11\cdots1}=1\) (solved for
\(u_{11\cdots1}\)), so that \(a_j\) is the normalized first row of the symbol. Without this
normalization (i) is false; with it, the examples below are consistent with the theorem.
Evidence: \(u_{22}=0\) in \((x_1,x_2)\) has \(A_{22}=1\), \(A_{11}=A_{12}=0\), so \(a_1=a_2=0\) and
(4.36) fails (\(A_{22}=1\ne a_2^2=0\)); yet the equation admits \(X=u\partial_{x_2}\): the
solutions are \(u=a(x_1)x_2+b(x_1)\), and \(x_2^*=x_2+\varepsilon u\), \(u^*=u\) gives
\(u^*=(a x_2^*+b)/(1+\varepsilon a)\), again a solution. Likewise \(2u_{11}=0\) has \(A_{11}=2\),
\(a_1=2\), and (4.36) fails (\(2\ne4\)), while \(u\partial_{x_1}\) is admitted. After normalizing to
\(u_{11}=0\), (4.36) holds and part (ii) gives only \(\partial\xi_2/\partial u=0\), consistent
with \(u\partial_{x_1}\).
Target: [BK.04.2.07].

### BK-E04.2.02. Theorem 4.2.3-7 fails for degenerate second-order linear equations

Status: Confirmed.
Location: §4.2.3, p. 175, Theorem 4.2.3-7; used on p. 176 and p. 188.
Printed: If a linear PDE of order \(k\ge2\) in solved form (4.29) admits
\(X=\xi_i(x,u)\partial_{x_i}+\eta(x,u)\partial_u\), then \(\partial\xi_i/\partial u=0\),
\(i=1,\ldots,n\), and \(\partial^2\eta/\partial u^2=0\).
Correct: The conclusion holds for \(k\ge3\) (a linear equation is of the form (4.40), so
Theorem 4.2.3-5 applies) and, for \(k=2\), under the hypothesis of Theorem 4.2.3-2 (no point
change of the independent variables brings the equation to the form
\(u_{11}=G(x,u,\underset1u)\)). For a second-order equation of the form (4.38) it can fail.
Evidence: \(u_{11}=0\) in independent variables \((x_1,x_2)\) is linear and admits
\(X=u\partial_{x_1}\): its solutions are \(u=a(x_2)x_1+b(x_2)\), and \(x_1^*=x_1+\varepsilon u\),
\(x_2^*=x_2\), \(u^*=u\) gives \(u^*=(a(x_2)x_1^*+b(x_2))/(1+\varepsilon a(x_2))\), linear in
\(x_1^*\), on the patch \(1+\varepsilon a\ne0\). Here \(\partial\xi_1/\partial u=1\). This is
consistent with Theorem 4.2.3-3, which for the form (4.38) only gives
\(\partial\xi_i/\partial u=0\) for \(i\ge2\). The applications on pp. 176 and 188 (heat and
biharmonic equations) reach correct generator forms, but for the heat equation (which has the
form (4.38)) the form (4.41) follows from the determining equations, not from the theorem.
Target: [BK.04.2.08].

### BK-E04.2.03. Commutators of the wave-speed family (i) depend on the antiderivative and fail for \(A=C\)

Status: Confirmed.
Location: §4.2.4, p. 185, generators \(X_1,\ldots,X_4\) for \(c(x_1)\) of form (i) and the line
"The nonzero commutators ... are".
Printed: \([X_1,X_2]=(C-A)X_1\), \([X_1,X_3]=X_2\), \([X_2,X_3]=(C-A)X_3\), for
\(X_3\) containing the indefinite integral \(\int(Bx_1^2+Cx_1+D)c^{-2}dx_1\).
Correct: Write \(Q=Bx_1^2+Cx_1+D\). For \(A\ne C\) the table holds when the antiderivative is
taken as \(-Q^2/(2(A-C)c^2)\); another choice adds a multiple of \(X_1\) to \(X_3\), and then
\([X_2,X_3]\) has an extra multiple of \(X_1\). For \(A=C\) (so \(c=Q\)) the commutators are
\([X_1,X_3]=X_2\), \([X_2,X_3]=X_1\), \([X_1,X_2]=0\).
Evidence: With \(c=Q E\), \(E=\exp[(A-C)\int dx_1/Q]\), \(G'=Q/c^2\), the
\(\partial_{x_2}\)-component
of \([X_2,X_3]-(C-A)X_3\) is \(2(A-C)G+E^{-2}\), a constant (its derivative vanishes); it is zero
iff \(G=-E^{-2}/(2(A-C))\). For \(A=C\), \(E=1\) and the constant is \(1\), so
\([X_2,X_3]=X_1\); this cannot be removed by changing the constant in \(G\), since
\([X_2,X_1]=(A-C)X_1=0\). (Symbolic computation with \(c\) and \(G\) as above.)
Target: [BK.04.2.14].

### BK-E04.2.04. Commutators for the exponential wave speed

Status: Confirmed.
Location: §4.2.4, pp. 186–187, case (iv), \(c(x_1)=Ae^{Bx_1}\).
Printed: "The commutator table is the same as for (i) with \(C-A\) replaced by \(-AB\)", i.e.
\([X_1,X_2]=-ABX_1\), \([X_1,X_3]=X_2\), \([X_2,X_3]=-ABX_3\).
Correct: For the printed generators \(X_1=\partial_{x_2}\),
\(X_2=\partial_{x_1}-Bx_2\partial_{x_2}+\frac12Bu\partial_u\),
\(X_3=Ax_2\partial_{x_1}-\frac12[ABx_2^2+(AB)^{-1}e^{-2Bx_1}]\partial_{x_2}+\frac12ABx_2u\partial_u\):
\([X_1,X_2]=-BX_1\), \([X_1,X_3]=AX_2\), \([X_2,X_3]=-BX_3\). Equivalently, with \(X_3/A\) in place
of
\(X_3\), the table of (i) with \(C-A\) replaced by \(-B\).
Evidence: \([X_1,X_2]=\partial_{x_2}(\text{coefficients of }X_2)=-B\partial_{x_2}\);
\([X_1,X_3]=A\partial_{x_1}-ABx_2\partial_{x_2}+\frac12ABu\partial_u=AX_2\); a direct computation
gives \([X_2,X_3]=-ABx_2\partial_{x_1}+[\frac12AB^2x_2^2+\frac1{2A}e^{-2Bx_1}]\partial_{x_2}
-\frac12AB^2x_2u\partial_u=-BX_3\). For \(A=1\) the printed table is correct.
Target: [BK.04.2.15].

### BK-E04.2.05. Scaling generator of the two-dimensional cubic Schrödinger equation

Status: Confirmed.
Location: Exercises 4.2, p. 195, Exercise 17, \(X_4\).
Printed: \(X_4=x_1\partial_{x_1}+x_2\partial_{x_2}+2x_3\partial_{x_3}\) for
\(u_{11}+u_{22}+r|u|^2u=iu_3\), \(r\) constant.
Correct: \(X_4=x_1\partial_{x_1}+x_2\partial_{x_2}+2x_3\partial_{x_3}-u\partial_u\) (and
\(-\bar u\partial_{\bar u}\)) when \(r\ne0\); the printed form is correct only for \(r=0\).
Evidence: Under \(x^*=\lambda x\), \(x_3^*=\lambda^2x_3\), \(u^*=u\) the terms \(u_{11}+u_{22}\) and
\(iu_3\) scale by \(\lambda^{-2}\) while \(r|u|^2u\) is unchanged; with \(u^*=\lambda^{-1}u\) all
three terms scale by \(\lambda^{-3}\). The same book lists \(-u\partial_u-2v\partial_v\) in the
scaling generator \(X_4\) of the coupled system of Exercise 4.3-11 (p. 215).
Target: [BK.04.2.19].

### BK-E04.3.01. Conductivity case IV of the potential system lacks a multiplicative constant

Status: Normalization check.
Location: §4.3.4, p. 208, Case IV,
\(K(u)=\frac1{u^2+pu+q}\exp\bigl[r\int\frac{du}{u^2+pu+q}\bigr]\).
Printed: Case IV is stated for this \(K\) with arbitrary \(p,q,r\) (\(p^2-4q-r^2\ne0\)), without a
constant factor, while Cases II and III carry the factor \(\lambda\).
Correct: The five-parameter group, with the same \(X_5\), is admitted by
\(K=\frac{\lambda}{u^2+pu+q}\exp\bigl[r\int\frac{du}{u^2+pu+q}\bigr]\) for every constant
\(\lambda\ne0\). The factor can be normalized away by a scaling of \(x_2\) (and, for \(r\ne0\) and
\(\lambda>0\), by the integration constant), but the source states no such normalization.
Evidence: The symmetry condition for \(X_5=v\partial_{x_1}+(r-p)x_2\partial_{x_2}-(u^2+pu+q)
\partial_u-(qx_1+pv)\partial_v\) was verified for \((p,q,r)=(0,1,3)\) and \((1,2,\frac12)\) with
\(\lambda=1\) and \(\lambda=5\). For \(r=0\), \(p=0\), \(q=1\) the printed formula gives only
\(K=1/(1+u^2)\), whereas \(K=2/(1+u^2)\) also admits \(X_5\); comparing logarithmic derivatives,
\(2/(1+u^2)\) is not of the printed form for any \(p,q,r\).
Target: [BK.04.3.07].

### BK-E04.4.01. Misprinted scaling generator for the axisymmetric wave equation

Status: Confirmed.
Location: §4.4.1, p. 225, (4.198a).
Printed: \(X_1=x_1\frac{\partial}{\partial x_2}+x_2\frac{\partial}{\partial x_2}-u\frac\partial
{\partial u}\).
Correct: \(X_1=x_1\frac{\partial}{\partial x_1}+x_2\frac{\partial}{\partial x_2}-u\frac\partial
{\partial u}\).
Evidence: \(X_1\) is the case \(\alpha=1\), \(\lambda=-1\), \(\beta=\gamma=0\) of (4.194a–c), which
gives \(\xi_1=x_1\); the invariant form \(u=x_2^{-1}F_1(x_1/x_2)\) derived from it in (4.199)
requires \(\xi_1=x_1\). (Checked on the page image at 200 dpi.)
Target: [BK.04.4.09].

### BK-E04.4.02. Sign of the Green's function \(y(x_1;\lambda)\)

Status: Confirmed.
Location: §4.4.2, p. 235, display after (4.239).
Printed: \(y(x_1;\lambda)=\frac{\sinh\sqrt\lambda x_1\,\sinh\sqrt\lambda(\hat x_1-1)}{\sqrt\lambda
\sinh\sqrt\lambda}\) for \(0<x_1<\hat x_1\), and \(\frac{\sinh\sqrt\lambda\hat
x_1\,\sinh\sqrt\lambda
(x_1-1)}{\sqrt\lambda\sinh\sqrt\lambda}\) for \(\hat x_1<x_1<1\).
Correct: \(\sinh\sqrt\lambda(1-\hat x_1)\) and \(\sinh\sqrt\lambda(1-x_1)\) in place of
\(\sinh\sqrt\lambda(\hat x_1-1)\) and \(\sinh\sqrt\lambda(x_1-1)\) (overall sign change).
Evidence: For the printed \(y\), the jump \(y'(\hat x_1^+)-y'(\hat x_1^-)=[\sinh(a\hat x_1)
\cosh(a(\hat x_1-1))-\cosh(a\hat x_1)\sinh(a(\hat x_1-1))]/\sinh a=1\) (\(a=\sqrt\lambda\)), so it
solves \(y''-\lambda y=+\delta(x_1-\hat x_1)\), not (4.239). The corrected \(y\) has jump \(-1\);
its residues at \(\lambda=-n^2\pi^2\) give the positive series (4.240), which is the correct heat
kernel (it is positive for small \(x_2\)), while the printed \(y\) would give its negative.
Target: [BK.04.4.13].

### BK-E04.4.03. Fundamental solution of the Fokker–Planck equation with drift \(\alpha/x_1+\beta x_1\)

Status: Confirmed.
Location: Exercises 4.4, p. 246, Exercise 8(c), (4.272).
Printed: \(u=\beta\sqrt{\frac{\hat x_1\zeta}{2\sinh\beta x_2}}\bigl(\frac{\hat
x_1}{x_1}\bigr)^{\alpha/2}
\exp\bigl[\frac12(1-\alpha)\beta x_2-\frac14\beta(1+\coth\beta x_2)(x_1-\hat x_1e^{-\beta x_2})^2
\bigr]I_{-\frac12-\frac12\alpha}(\beta\hat x_1\zeta)\), \(\zeta=x_1/(2\sinh\beta x_2)\).
Correct: replace \((x_1-\hat x_1e^{-\beta x_2})^2\) by \(x_1^2+\hat x_1^2e^{-2\beta x_2}\)
(equivalently, multiply the printed formula by \(e^{-\beta\hat x_1\zeta}\)).
Evidence: Numerically, at \(\alpha=0.3\), \(\beta=0.6\), \(\hat x_1=0.9\), the printed \(u\) leaves
the
residual \(u_2-u_{11}-(\phi u)_1\approx-1.53\) at \((x_1,x_2)=(0.7,0.5)\) and has total mass
\(\int_0^\infty u\,dx_1\approx2.36\) at \(x_2=0.5\) (diverging as \(x_2\to0\)); the corrected
formula has residual \(<10^{-30}\) and mass \(1.0000\) at \(x_2=0.5\) and \(x_2=0.02\). The extra
factor is \(\exp[\frac12\beta(1+\coth\beta x_2)x_1\hat x_1e^{-\beta x_2}]=e^{\beta\hat x_1\zeta}\).
Target: [BK.04.4.16].

### Conventions and notation (not errata)

- The source uses \(X\) both for the infinitesimal generator and for the first group map
  \(x^*=X(x,u;\varepsilon)\), and \(X_i\) both for generators and for similarity variables
  (e.g. §4.2.1, §4.3.2).
- In the examples \(x_2\) is time; the heat equation is written \(u_{11}=u_2\) and the wave
  equation \(u_{22}=c^2(x_1)u_{11}\).
- §4.3.3, (4.112): the form of generators for linear systems is stated as a conjecture and
  then assumed; it is not a theorem of the book (see [BK.04.3.03]).
- §4.4: boundary conditions with Dirac deltas are used formally; transformation rules such as
  \(x\delta'(x)=-\delta(x)\) are distributional identities.

## Chapter 5. Noether's Theorem and Lie–Bäcklund Symmetries

### BK-E05.2.01. Sign in the equivalence of a first-order Lie–Bäcklund generator with a contact generator

Status: Confirmed.
Location: §5.2.4, pp. 270–271, Theorem 5.2.4-4, (5.58a–c) and its proof.
Printed: Any Lie–Bäcklund generator \(W(x,u,\underset1u)\partial_u\) is equivalent to the contact
group generator with \(\xi_j=\partial W/\partial u_j\), \(\eta=u_i\partial W/\partial u_i-W\),
\(\eta^{(1)}_j=-\partial W/\partial x_j-u_j\partial W/\partial u\).
Correct: That contact generator is equivalent to \(-W\partial_u\). The generator equivalent to
\(W\partial_u\) has \(\xi_j=-\partial W/\partial u_j\), \(\eta=W-u_i\partial W/\partial u_i\),
\(\eta^{(1)}_j=\partial W/\partial x_j+u_j\partial W/\partial u\).
Evidence: By Theorem 5.2.3-1, \(\xi_j\partial_{x_j}+\eta\partial_u\) is equivalent to
\((\eta-u_j\xi_j)\partial_u\); the proof itself computes
\(\eta-\xi_ju_j=u_iW_{u_i}-W-u_jW_{u_j}=-W\).
Example: \(W=u_1\) (\(n=1\)) gives \(\xi=1\), \(\eta=0\), i.e. \(\partial_x\), whose characteristic
is
\(-u_1\), not \(u_1\). Theorem 5.2.4-3 is consistent, since there \(W=\xi_ju_j-\eta\) is defined as
minus the characteristic.
Target: [BK.05.2.14].

### BK-E05.3.01. Order of the product \(R_5\) of recursion operators

Status: Confirmed.
Location: §5.3.2, p. 290, line after (5.117).
Printed: \(R_5=R_2R_3\), with \(R_5[u]=\frac14[tu_1^2-xu_1-2tu_2]-(tu_1-\frac12x)D_x+tD_x^2\) on
p. 289.
Correct: \(R_5=R_3R_2\); \(R_2R_3=R_5+\frac12=R_5+\frac12R_1\).
Evidence: With \(R_2=\frac12u_1-D_x\), \(R_3=\frac12(tu_1-x)-tD_x\):
\(R_2R_3=\frac14u_1(tu_1-x)-\frac12tu_1D_x-\frac12(tu_2-1)-\frac12(tu_1-x)D_x+tD_x^2\), whose
zeroth-order part contains the extra constant \(+\frac12\) (from \(D_x(x)=1\)), while
\(R_3R_2=\frac14(tu_1-x)u_1-\frac12(tu_1-x)D_x-\frac12tu_2-\frac12tu_1D_x+tD_x^2\) equals the
printed \(R_5\). The conclusion that only \(R_2,R_3\) are independent is unaffected, since
\(R_1=1\) is in the list.
Target: [BK.05.3.05].

### Conventions and notation (not errata)

- §5.2.3: the source's "equivalence" of generators means equal action on functions to first
  order in \(\varepsilon\) (Theorem 5.2.3-1); \(U\sim\hat U\) iff their characteristics
  \(\eta-u_i\xi_i\) agree.
- §5.2.4: the characteristic function \(W=\xi_ju_j-\eta\) is minus the characteristic
  \(Q=\eta-\xi_ju_j\) used in Olver (1986).
- §5.3.3: \(D_x^{-1}\) is defined on compactly supported functions (5.123); applying it to
  \(u\) or \(u_t\) and the resulting "nonlocal symmetries" are formal.
- §5.2.7: the KdV equation is normalized as \(v_t+vv_x+v_{xxx}=0\).

## Chapter 6. Construction of Mappings Relating Differential Equations

### BK-E06.4.01. Sign of the exponent in the linearized telegraph system

Status: Confirmed.
Location: §6.4.1, p. 324, (6.81a), and p. 325, (6.87a).
Printed: \(\partial F^2/\partial X_2-e^{-X_2}\partial F^1/\partial X_1=0\) (6.81a) and
\(\partial w^2/\partial z_2-e^{-z_2}\partial w^1/\partial z_1=0\) (6.87a); (6.81b) and (6.87b)
carry \(e^{-X_2}\), \(e^{-z_2}\).
Correct: \(\partial F^2/\partial X_2-e^{X_2}\partial F^1/\partial X_1=0\) and
\(\partial w^2/\partial z_2-e^{z_2}\partial w^1/\partial z_1=0\); (6.81b), (6.87b) are correct as
printed.
Evidence: Put \(z_1=x_1-u^2\), \(z_2=x_2-\log u^1\), \(w^1=x_1\), \(w^2=e^{x_2}\) (6.86), so that
\(x_1=w^1\), \(u^2=w^1-z_1\), \(e^{x_2}=w^2\), \(u^1=w^2e^{-z_2}\). Inverting the Jacobian of
\((z_1,z_2)\) with respect to \((x_1,x_2)\) and substituting into (6.78a,b): (6.78a) becomes
\(w^1_{z_2}=e^{-z_2}w^2_{z_1}\) (= (6.87b)), and (6.78b) becomes \(w^2_{z_2}=e^{z_2}w^1_{z_1}\).
With the printed (6.87a) in place of the latter, the pull-back of the target system is
\(u^1_{x_2}=e^{2x_2}(u^2_{x_1}-1)+u^1\) instead of (6.78b); with the corrected sign the residual
of (6.78b) vanishes identically. For (6.81): the generator (6.80) with \(F=(X_1,-e^{-X_2})\)
satisfies the printed (6.81a,b) but is not a symmetry of (6.78), while
\(F=(-e^{-X_2},X_1)\) satisfies the corrected system and is a symmetry; substituting a general
\(F(X_1,X_2)\) into the determining equations gives exactly
\(F^1_{X_2}=e^{-X_2}F^2_{X_1}\), \(F^2_{X_2}=e^{X_2}F^1_{X_1}\).
Target: [BK.06.4.05].

### BK-E06.4.02. Variables interchanged in the heat equation of Exercise 6.4-7

Status: Confirmed.
Location: Exercises 6.4, p. 336, Exercise 7(b), (6.151).
Printed: \(g(x_1,x_2)\) satisfies \(\partial g/\partial x_1-\partial^2g/\partial x_2^2=0\).
Correct: \(\partial g/\partial x_2-\partial^2g/\partial x_1^2=0\).
Evidence: Under the map of Exercise 7(c), \(w^1=-e^{-u^2/4}\), \(w^2=\frac12u^1e^{-u^2/4}\), the
generator \(f(z)\partial_{w^1}+f_{z_1}(z)\partial_{w^2}\) of the target system
\(w^1_{z_2}=w^2_{z_1}\), \(w^1_{z_1}=w^2\) (for \(f\) solving the target heat equation
\(f_{z_2}=f_{z_1z_1}\), as printed in 7(c)) pulls back to
\(\delta u^2=4fe^{u^2/4}\), \(\delta u^1=e^{u^2/4}(2f_{x_1}+u^1f)\), i.e. (6.150) with \(g=f\).
Directly: the linearized system (6.149) applied to the characteristics of (6.150) leaves, after
using (6.149), the residual \(0\) in (6.149a) and \(4e^{u^2/4}(g_{x_2}-g_{x_1x_1})\) in (6.149b).
With the printed (6.151) this residual is \(4e^{u^2/4}(g_{x_2}-g_{x_1x_2x_2})\neq0\) in general
(e.g. \(g=e^{4x_1+2x_2}\), which solves the printed (6.151) and gives \(-56e^{u^2/4}g\)).
Target: [BK.06.4.11].

### BK-E06.5.01. Signs in the multiplier for the parabolic equation

Status: Confirmed.
Location: §6.5.1, p. 343, the formulas for \(\log G(x)\) and \(W'\) after (6.191).
Printed: \(\log G=-\frac14x_1^2A_1'/A_1+x_1B_1/A_1+W(x_2)\), \(W'=B_2T'-A_2B_1(T')^{3/2}\).
Correct: \(\log G=-\frac14x_1^2A_1'/A_1-x_1B_1/A_1+W(x_2)\), \(W'=-B_2T'+A_2B_1(T')^{3/2}\).
Evidence: By (6.171a) with \(\tau_1=0\), \(\xi_1=A_1\), \(\phi_{1,x_1}=(T')^{1/2}=1/A_1\),
\(\phi_{2,x_1}=0\) and \(f_1=\frac12x_1A_1'+B_1\) (6.175c):
\((\log G)_{x_1}=-f_1/A_1=-\frac12x_1A_1'/A_1-B_1/A_1\). By (6.171b) the \(x_1\)-free part of
\((\log G)_{x_2}=-[f_1\phi_{1,x_2}+f_2\phi_{2,x_2}]\) is \(-[B_1D'+B_2T']=A_2B_1(T')^{3/2}-B_2T'\).
Independently, for \(u=G^{-1}w(\phi_1,\phi_2)\) the coefficient of \(w_{z_1}\) in
\(u_{11}+u_2+Vu\) is \(G^{-1}(-2(\log G)_{x_1}(T')^{1/2}+x_1((T')^{1/2})'+D')\), which vanishes iff
\((\log G)_{x_1}=-\frac12x_1A_1'/A_1-B_1/A_1\). A symbolic check with \(T'=P(x_2)^2\), arbitrary
\(P,B_1,B_2\), \(q_2,q_1,A_2\) from (6.185a,b), (6.187), (6.191) and \(q_0\) from (6.188) (with
integration constant \(c\)), applied to \(w=e^{az_1+bz_2}\), gives
\(u_{11}+u_2+Vu=G^{-1}T'(a^2+b+r)w\) with \(r=c\) equal to the printed constant
\(r=\frac12A_1'A_1-B_1^2+B_2+q_0A_1^2\) for the corrected signs, and a residual
\(-4aB_1-2x_1B_1'/P+4B_1^2-2B_2\) for the printed ones. The criterion (6.184), (6.175)–(6.191)
and the formulas for \(\phi_1,\phi_2,D\) and \(r\) are correct.
Target: [BK.06.5.04].

### Conventions and notation (not errata)

- §6.4: the source writes \(u^1,u^2\) (superscripts) for two dependent variables; in Exercises
  6.4-6, 6.4-7 \(e^{u^2/4}\) means \(\exp(u^2/4)\) with \(u^2\) the second component.
- §6.5.1, Theorem 6.5.1-1: \(\log G=\int\alpha(x_1,x_2)\,dx_2\) is to be read with the
  \(x_1\)-dependent integration "constant" fixed so that \(\partial_{x_1}\log G=\beta\); this is
  possible by \(\beta_{x_2}=\alpha_{x_1}\) and is what (6.171a,b) give.
- §6.5.1, case \(m=0\): \(\tau_1,\xi_2\) are arbitrary; the printed mapping \(z_1=x_1\),
  \(z_2=x_2\) corresponds (up to interchanging \(z_1,z_2\)) to \(\tau_1=\xi_2=1\).
- Exercise 6.4-7(c): "transforms (6.150a,b)" refers to the system (6.149a,b).

## Chapter 7. Potential Symmetries

### BK-E07.2.01. Variables interchanged in the heat equation for the Burgers potential symmetries

Status: Confirmed.
Location: §7.2.1, p. 357, (7.16b); also used for (7.18), p. 357.
Printed: \(\psi(x)\) is any solution of \(\partial\psi/\partial x_1-\partial^2\psi/\partial
x_2^2=0\).
Correct: \(\partial\psi/\partial x_2-\partial^2\psi/\partial x_1^2=0\).
Evidence: For (7.18), \(Y=e^{v/4}\psi\partial_v\) on (7.17) \(v_{11}-v_2-\frac14v_1^2=0\): with
\(Q=e^{v/4}\psi\), the linearized equation is \(Q_{11}-Q_2-\frac12v_1Q_1=e^{v/4}[\psi_{11}-\psi_2+
\frac14\psi(v_{11}-v_2-\frac14v_1^2)]=e^{v/4}(\psi_{x_1x_1}-\psi_{x_2})\) on solutions, so \(Y\) is
a
symmetry iff \(\psi_{x_2}=\psi_{x_1x_1}\). For (7.16a) on (7.15), the linearized system applied to
the
characteristics leaves the residual \(0\) in (7.15a) and \(4e^{v/4}(\psi_{x_2}-\psi_{x_1x_1})\) in
(7.15b). With the printed condition this residual is \(4e^{v/4}(\psi_{x_2}-\psi_{x_1x_2x_2})\),
nonzero
e.g. for \(\psi=e^{4x_1+2x_2}\). The same misprint occurs in (6.151) [BK-E06.4.02].
Target: [BK.07.2.04].

### BK-E07.2.02. Conductivity formula lacks a multiplicative constant

Status: Normalization check.
Location: §7.2.1, p. 358, Theorem 7.2.1-1, (7.21) and case (ii) on p. 359; also p. 360, case
(iv), and (7.86), p. 376.
Printed: \(K(u)=\frac1{u^2+pu+q}\exp\bigl[r\int\frac{du}{u^2+pu+q}\bigr]\), \(p,q,r\) arbitrary,
as the necessary and sufficient condition, while case (i) carries a factor \(\lambda\) in
\(K=\lambda(u+\kappa)^{-2}\).
Correct: \(K(u)=\frac{\lambda}{u^2+pu+q}\exp\bigl[r\int\frac{du}{u^2+pu+q}\bigr]\), \(\lambda\ne0\),
or else the theorem must be stated up to the equivalence \(x_2\mapsto\lambda x_2\)
(\(K\mapsto\lambda K\)).
Evidence: \(X_S=v\partial_{x_1}+(r-p)x_2\partial_{x_2}-(u^2+pu+q)\partial_u-(qx_1+pv)\partial_v\)
(7.23)
satisfies the symmetry conditions of (7.20) for \(K=c\,((u-1)/(u+2))^{1/3}/((u-1)(u+2))\)
(\(p=1,q=-2,r=1\)) with \(c=1\) and \(c=5\), and for \(K=5/(u^2+1)\) and \(K=-1/(u^2+1)\)
(\(p=0,q=1,r=0\)). Comparing logarithmic derivatives, \(5/(u^2+1)\) is of the printed form only if
\((r-p-2u)(u^2+1)=-2u(u^2+pu+q)\), i.e. \(p=r=0\), \(q=1\), which gives \(1/(u^2+1)\); so it is not
covered. For \(r\ne0\) a positive factor can be absorbed into the integration constant, but a factor
\(\lambda<0\), or any \(\lambda\ne1\) when \(r=0\), cannot. The same remark applies to §4.3.4, Case
IV
[BK-E04.3.01].
Target: [BK.07.2.05], [BK.07.2.06].

### BK-E07.2.03. Coefficient in the generator \(Y_7\) of the integrated heat equation

Status: Confirmed.
Location: §7.2.1, p. 360, (7.27b).
Printed: \(Y_7=-x_1[(v+\kappa x_1)^2+\lambda x_2]\partial_{x_1}+4\lambda x_2^2\partial_{x_2}+
[\kappa x_1(v+\kappa x_1)^2+2\lambda x_2(2v+3\kappa x_1)]\partial_v\).
Correct: the \(\partial_{x_1}\) coefficient is \(-x_1[(v+\kappa x_1)^2+2\lambda x_2]\), as in
(7.22b).
Evidence: \(Y_7\) is the projection of \(X_{S2}\) (7.22b) (which drops only the \(\partial_u\) term,
cf. Exercise 7.2-3(a)(ii)). Directly, for \(K(v_1)v_{11}-v_2=0\) with
\(K=\lambda(v_1+\kappa)^{-2}\),
the linearized equation evaluated on the characteristic of \(Y_7\) vanishes identically with
\(2\lambda x_2\) and, with the printed \(\lambda x_2\), leaves
\(\lambda[x_1v_1(v_1+\kappa)^3-2\kappa\lambda x_2v_{11}]/(v_1+\kappa)^3\neq0\).
Target: [BK.07.2.06].

### BK-E07.2.04. Exponential speeds omitted from the solutions of \((c/c')''=0\)

Status: Confirmed.
Location: §7.2.2, p. 363, (7.43).
Printed: "The solution of (7.41) is \(c(x_1)=(Ax_1+B)^C\)."
Correct: The solutions with \(c'\ne0\) are \(c=(Ax_1+B)^C\) and \(c=Ke^{Ax_1}\).
Evidence: \((c/c')''=0\) means \(c/c'=\alpha x_1+\beta\); for \(\alpha\ne0\) this gives
\(c=k(\alpha x_1+\beta)^{1/\alpha}\) (= (7.43)), and for \(\alpha=0\), \(c=Ke^{x_1/\beta}\). For
\(c=e^{Ax_1}\): \(H=c'/c=A\) is constant, so (7.39) holds; \(c/c'=1/A\), so (7.40) and (7.41) hold;
(7.42) gives \(\frac34A^4e^{4Ax_1}\ne0\). This is the case \(c=e^{x_1}\) of (7.35). The conclusion
(7.45) is unaffected.
Target: [BK.07.2.08].

### BK-E07.2.05. Missing factors in the implicit solutions of (7.42)

Status: Confirmed.
Location: §7.2.2, p. 363, (7.44a,b).
Printed: \(\sqrt c-\arctan C\sqrt c=Ax_1+B\) and
\(2\sqrt c+\log|(\sqrt c-C)/(\sqrt c+C)|=Ax_1+B\), \(A,B,C\) arbitrary.
Correct: \(\sqrt c-C^{-1}\arctan(C\sqrt c)=Ax_1+B\) and
\(2\sqrt c+C\log|(\sqrt c-C)/(\sqrt c+C)|=Ax_1+B\). The printed forms are correct only for
\(C=1\) (the case used for (7.48)–(7.49)).
Evidence: (7.42) is invariant under \(c\mapsto kc\) and translations of \(x_1\), and has the
first-integral families \(c'=k(c+m)/\sqrt c\). With \(s=\sqrt c\):
\(dx_1=\frac2k\frac{s^2}{s^2+m}ds\).
For \(m=C^{-2}\) this integrates to \(s-C^{-1}\arctan(Cs)\), for \(m=-C^2\) to
\(s+\frac C2\log|(s-C)/(s+C)|\). Numerically, with \(s'=A/F'(s)\) from \(F(s)=Ax_1+B\) and
\((A,C,s)=(1.3,0.7,2.1)\), the left side of (7.42) equals \(-114.7\) for the printed (7.44a) and
\(0\) (to \(10^{-13}\)) for the corrected one; for (7.44b) with \((1.3,1.6,3.3)\) it equals
\(-6.83\)
printed and \(0\) corrected; both agree at \(C=1\).
Target: [BK.07.2.08].

### Conventions and notation (not errata)

- §7.2.1–7.2.5: superscripts on \(u\) index components (\(u^1,u^2\)); \(e^{u^2/4}\) and similar mean
  the exponential of the second component.
- §7.2.1 case \(\mu=0\) is stated "to within scalings and translations of \(x_1\)"; scalings of
  \(c\) itself are also used implicitly (e.g. \(c=e^{x_1}\) for \(Ke^{Ax_1}\)).
- §7.3.1: the sufficiency statement for (7.101) uses \(\lambda\) for the exponent constant called
  \(r\) in (7.21); it is unrelated to the \(\lambda\) of (7.97).

[BK.02.2.07]: SYNOPSIS-BK.md#bk02207-lie-series-for-functions
[BK.02.2.09]: SYNOPSIS-BK.md#bk02209-invariant-functions
[BK.02.2.12]: SYNOPSIS-BK.md#bk02212-canonical-coordinates
[BK.03.1.04]: SYNOPSIS-BK.md#bk03104-homogeneous-first-order-equations
[BK.03.3.10]: SYNOPSIS-BK.md#bk03310-determining-equations-of-the-blasius-equation
[BK.03.4.01]: SYNOPSIS-BK.md#bk03401-two-dimensional-subalgebras
[BK.03.4.08]: SYNOPSIS-BK.md#bk03408-example-a-fourth-order-ode-with-a-three-parameter-solvable-group
[BK.04.2.07]: SYNOPSIS-BK.md#bk04207-structure-theorems-for-admitted-generators-theorems-423-1-to-423-3
[BK.04.2.08]: SYNOPSIS-BK.md#bk04208-structure-theorems-for-admitted-generators-theorems-423-4-to-423-7
[BK.04.2.14]: SYNOPSIS-BK.md#bk04214-wave-equation-with-variable-speed-the-case-sigma0
[BK.04.2.15]: SYNOPSIS-BK.md#bk04215-wave-equation-with-variable-speed-special-cases-of-i
[BK.04.2.19]: SYNOPSIS-BK.md#bk04219-exercises-42-symmetry-groups-of-further-scalar-pdes
[BK.04.3.03]: SYNOPSIS-BK.md#bk04303-determining-equations-for-systems-linear-systems
[BK.04.3.07]: SYNOPSIS-BK.md#bk04307-group-classification-of-the-nonlinear-heat-potential-system
[BK.04.4.09]: SYNOPSIS-BK.md#bk04409-fundamental-solution-of-the-axisymmetric-wave-equation
[BK.04.4.13]: SYNOPSIS-BK.md#bk04413-heat-equation-on-a-finite-interval
[BK.04.4.16]: SYNOPSIS-BK.md#bk04416-exercises-44-fundamental-solutions
[BK.05.2.14]: SYNOPSIS-BK.md#bk05214-liebäcklund-generators-of-first-order-are-contact-generators
[BK.05.3.05]: SYNOPSIS-BK.md#bk05305-recursion-operators-of-the-integrated-burgers-equation
[BK.06.4.05]: SYNOPSIS-BK.md#bk06405-linearization-of-a-nonlinear-telegraph-system
[BK.06.4.11]: SYNOPSIS-BK.md#bk06411-exercises-64
[BK.06.5.04]: SYNOPSIS-BK.md#bk06504-parabolic-equations-criterion-and-mapping
[BK.07.2.04]: SYNOPSIS-BK.md#bk07204-burgers-equation-potential-symmetries
[BK.07.2.05]: SYNOPSIS-BK.md#bk07205-nonlinear-heat-conduction-classification-of-potential-symmetries
[BK.07.2.06]: SYNOPSIS-BK.md#bk07206-the-integrated-nonlinear-heat-equation
[BK.07.2.08]: SYNOPSIS-BK.md#bk07208-point-symmetries-of-r-versus-s
