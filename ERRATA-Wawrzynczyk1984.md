# Errata and source checks: Wawrzyńczyk (1984)

Reference: Antoni Wawrzyńczyk, *Group Representations and Special Functions*, examples and
problems prepared by Aleksander Strasburger, translated by Bogdan Ziemian, D. Reidel /
PWN–Polish Scientific Publishers, 1984. The local copy (a scan without text layer) is
[References/Wawrzyńczyk1984GroupRepresentationsSpecialFunctions-ReidelKluwer.pdf](References/Wawrzyńczyk1984GroupRepresentationsSpecialFunctions-ReidelKluwer.pdf).
Synopsis: [SYNOPSIS-Wawrzynczyk1984](SYNOPSIS-Wawrzynczyk1984.md).

Locators use printed page numbers; printed page \(p\) is PDF page \(p+15\) throughout. Line
numbers, where given, count from the top of the page; negative line numbers count from the
bottom.

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
- the location, as section, printed page and equation, theorem, example or problem number;
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries.

Synopsis entries cite errata by id. An erratum id \(\mathrm{W84\text-E}cc.s.nn\) is the
\(nn\)-th erratum located in section \(s\) of chapter \(cc\) (\(s=0\) for chapter-level
material before the first section). Errata in the Table of Formulas use the scheme stated in
that chapter of this file.

## Scope

These are observations about this edition, not an official publisher list. No claim is made
that formulas without an erratum are free of errors. Every erratum was checked on the page
image; misreadings of the scan by OCR are not errata. Formulas that the synopsis marks "as
printed" were transcribed from the page images without an independent check. Corrected
formulas in the synopsis are statements to be formalized. They are not Lean proofs.

Each chapter section ends with a list of conventions and notation that are not errata, for
example a sign or normalization convention that differs from a modern reference.

## Summary by chapter

- Chapter 1. Groups and Homogeneous Spaces: 63 entries, 10 errata (Confirmed 10).
- Chapter 2. Representations of Locally Compact Groups: 27 entries, 3 errata (Confirmed 2, Normalization check 1).
- Chapter 3. Decomposition Theory of Unitary Representations: 33 entries, 7 errata (Confirmed 6, Normalization check 1).
- Chapter 4. Representations of Compact Groups: 37 entries, 2 errata (Confirmed 2).
- Chapter 5. Theory of Spherical Functions: 25 entries, 1 erratum (Confirmed 1).
- Chapter 6. The Euler \(\Gamma\)- and \(B\)-Functions: 15 entries, 3 errata (Confirmed 2, Normalization check 1).
- Chapter 7. Bessel Functions: 15 entries, 5 errata (Confirmed 5).
- Chapter 8. Theory of Jacobi and Legendre Polynomials: 35 entries, 13 errata (Confirmed 13).
- Chapter 9. Gegenbauer Polynomials: 21 entries, 12 errata (Confirmed 12).
- Chapter 10. Jacobi and Legendre Functions: 32 entries, 13 errata (Confirmed 11, Normalization check 2).
- Chapter 11. Harmonic Analysis on the Lobatschevsky Space: 45 entries, 10 errata (Confirmed 10).
- Chapter 12. The Laguerre Polynomials: 39 entries, 8 errata (Confirmed 8).
- Chapter 13. The Hypergeometric Equation: 39 entries, 15 errata (Confirmed 14, Open check 1).
- Chapter 14. Affine Transformations: 30 entries, 4 errata (Confirmed 3, Normalization check 1).
- Chapter 15. Symmetric Spaces: 28 entries, 3 errata (Confirmed 3).
- Chapter 16. General Harmonic Analysis on a Symmetric Space: 10 entries, 0 errata.
- Chapter 17. Semisimple Algebras. Semisimple Groups. Symmetric Spaces of the Non-Compact Type: 41 entries, 8 errata (Confirmed 8).
- Chapter 18. Harmonic Analysis on Symmetric Spaces of the Non-Compact Type: 36 entries, 13 errata (Confirmed 13).
- Formula collection. Table of Formulas: 44 entries, 34 errata (Confirmed 34).
- Total: 615 entries, 164 errata (Confirmed 157, Normalization check 6, Open check 1).

## Chapter 1. Groups and Homogeneous Spaces

Synopsis: Chapter 1 of [SYNOPSIS-Wawrzynczyk1984](SYNOPSIS-Wawrzynczyk1984.md).

### W84-E01.1.01. Automorphisms must be bijective

Status: Confirmed.
Location: §1.1, p. 2, last definition.
Printed: "A homomorphism of a group onto itself is called an automorphism."
Correct: An automorphism is a bijective homomorphism of a group onto itself.
Evidence: Multiplication by 2 on \(\mathbb Q/\mathbb Z\) is a surjective homomorphism with
non-zero kernel \(\{0,\tfrac12\}\), so it is not invertible; with the printed definition
\(\mathrm{Aut}\,G\) would not be a group.
Target: [W84.01.1.03].

### W84-E01.3.01. Real and imaginary parts of a complex matrix

Status: Confirmed.
Location: §1.3, p. 43, Example 3(b).
Printed: \(g=g_1+ig_2\in GL(n,\mathbb C)\) "where \(g_i\in GL(n,\mathbb R)\)".
Correct: \(g_1,g_2\in M_n(\mathbb R)\); they need not be invertible. The map
\(j(g)=\begin{pmatrix}g_1&g_2\\-g_2&g_1\end{pmatrix}\) is an injective homomorphism into
\(GL(2n,\mathbb R)\) as printed.
Evidence: \(g=iI_n\) has \(g_1=0\notin GL(n,\mathbb R)\); likewise \(g=I_n\) has \(g_2=0\).
Target: [W84.01.3.02].

### W84-E01.4.01. Equivariance of the local trivialization of \(G\to G/H\)

Status: Confirmed.
Location: §1.4, p. 53, Theorem 1.4.1.
Printed: the diffeomorphism \(j:O\times H\to\pi^{-1}(O)\) satisfies \(j(p,h'h)=h'\cdot j(p,h)\).
Correct: \(j(p,hh')=j(p,h)h'\) (and \(\pi(j(p,h))=p\)); e.g. \(j(p,h)=s(p)h\) for a local
analytic section \(s\).
Evidence: \(\pi^{-1}(O)\) is a union of left cosets \(gH\), stable under right multiplication by
\(H\) but not under left multiplication: for \(G=\mathbb R^2\rtimes SO(2)\) (rigid motions),
\(H=SO(2)\), \(G/H=\mathbb R^2\), left multiplication by \(h'\in H\setminus\{e\}\) moves the coset
over \(p\ne0\) to the coset over \(h'p\ne p\), so \(h'\cdot j(p,h)\notin\pi^{-1}(p)\). The text after
the theorem ("the multiplication by the elements of \(H\) is preserved") describes the right
action.
Target: [W84.01.4.01].

### W84-E01.4.02. Fundamental vector fields give an antihomomorphism

Status: Confirmed.
Location: §1.4, p. 56, proof of Lemma 1.4.3 and Remark; p. 57, Theorem 1.4.4(2).
Printed: \([X,Y]^*f(m)=[X,Y]f_m(e)=XYf_m(e)-YXf_m(e)=X^*Y^*f(m)-Y^*X^*f(m)\), and "the mapping
\(\mathfrak g\ni X\to X^*\in\mathcal T(M)\) is a homomorphism"; in Theorem 1.4.4 the isomorphism
\(\mathfrak g\cong\mathcal G^*\) is "provided by the mapping \(X\to X^*\)".
Correct: With \(X^*f(m)=\frac d{dt}f(\exp(tX)m)|_{t=0}\) and the Lie algebra \(\mathfrak g\) defined
by left-invariant fields (§1.3), \([X,Y]^*=-[X^*,Y^*]\): \(X\mapsto X^*\) is an antihomomorphism,
\(X\mapsto-X^*\) a homomorphism. The first sentence of the Remark (homomorphism when \(T_eG\)
carries the bracket of right-invariant fields) is correct; that algebra is anti-isomorphic to
\(\mathfrak g\) (via \(X\mapsto-X\) it is isomorphic), so the conclusion does not follow.
Evidence: For left-invariant fields, \(XYf_m(e)=\partial_s\partial_tf(\exp sX\exp tY\,m)\), whereas
\(X^*Y^*f(m)=\partial_s\partial_tf(\exp tY\exp sX\,m)\). Example 2 on p. 57 itself finds
\([X_3^*,X_1^*]=-2X_1^*=-[X_3,X_1]^*\).
Target: [W84.01.4.04].

### W84-E01.4.03. Generator of the lower triangular subgroup on \(P^1\mathbb R\)

Status: Confirmed.
Location: §1.4, p. 57, Example 2.
Printed: \(X_2^*f(x)=\frac d{dt}f\big(\frac x{xt+1}\big)\big|_{t=0}=x^2\frac{df}{dx}(x)\).
Correct: \(X_2^*f(x)=-x^2\frac{df}{dx}(x)\).
Evidence: \(\frac d{dt}\frac x{xt+1}\big|_{t=0}=-\frac{x^2}{(xt+1)^2}\big|_{t=0}=-x^2\). Consistency:
with \(X_1^*=d/dx\), \(X_3^*=2x\,d/dx\), the corrected field gives
\([X_1^*,X_2^*]=-2x\,d/dx=-X_3^*=-[X_1,X_2]^*\), in accordance with [W84-E01.4.02], while the
printed sign would give \(+X_3^*\), contradicting the relation \([X_3^*,X_1^*]=-[X_3,X_1]^*\)
checked in the same example.
Target: [W84.01.4.05].

### W84-E01.4.04. The invariant area form on the lower hemisphere

Status: Confirmed.
Location: §1.4, p. 61, Example 6, last two displays.
Printed: \(c_-(x)=-\frac1{x^3}\), and "an \(SO(3)\)-invariant 2-form on \(S^2\) is given on the set
\(U_+\cup U_-\) by the formula \(x=\frac1{|x^3|}dx^1\wedge dx^3\)".
Correct: \(c_-(x)=\frac1{x^3}\), and \(\omega=\frac1{x^3}\,dx^1\wedge dx^2\) on \(U_+\cup U_-\)
(\(|x^3|\) gives the invariant measure, not the form).
Evidence: The same page states \(c_-(-p)=-1\); \(-1/x^3\) equals \(+1\) at \(-p=(0,0,-1)\), while
\(1/x^3=-1\) there. Directly: the rotation \(R(x_1,x_2,x_3)=(x_1,-x_2,-x_3)\in SO(3)\) maps \(U_+\)
to \(U_-\) and \(R^*(c_-\,dx^1\wedge dx^2)=-c_-\circ R\,dx^1\wedge dx^2\); invariance gives
\(c_-(Rx)=-c_+(x)=-1/x_3=1/(Rx)_3\). The printed "\(dx^1\wedge dx^3\)" is not a form in the chart
\((x_1,x_2)\).
Target: [W84.01.4.08].

### W84-E01.5.01. Normalization of the invariant volume on \(S^n\)

Status: Confirmed.
Location: §1.5, p. 66, Problem 5(d).
Printed: \(\omega=\frac12\pi^{-n/2}\Gamma(\frac n2)\,\frac{dx^1\wedge\cdots\wedge dx^n}{|x^{n+1}|}\).
Correct: \(\omega=\frac{\Gamma(\frac{n+1}2)}{2\pi^{(n+1)/2}}\,\frac{dx^1\wedge\cdots\wedge dx^n}
{x^{n+1}}\) on the hemispheres \(x^{n+1}\ne0\); with \(|x^{n+1}|\) the expression is the density of
the normalized invariant measure.
Evidence: The volume of \(S^n\) is \(2\pi^{(n+1)/2}/\Gamma(\frac{n+1}2)\); the printed constant is
the reciprocal volume of \(S^{n-1}\). For \(n=2\) the printed constant is \(1/(2\pi)\), but
\(\int_{S^2}\frac{dx^1dx^2}{|x^3|}=2\int_{r<1}\frac{dA}{\sqrt{1-r^2}}=4\pi\), so the normalization
constant is \(1/(4\pi)\), as Problem 5(c) of the same page states. For the sign of the form see
[W84-E01.4.04].
Target: [W84.01.5.03].

### W84-E01.6.01. The involution of \(L^1(G)\) needs complex conjugation

Status: Confirmed.
Location: §1.6, p. 79, (1.6.18).
Printed: \(f^*(g):=f(g^{-1})\,\delta_G(g^{-1})\).
Correct: \(f^*(g)=\overline{f(g^{-1})}\,\delta_G(g^{-1})\).
Evidence: Without conjugation \(f\mapsto f^*\) is complex linear, so \((f,h)\mapsto\mu(f^**h)\) is
bilinear and cannot be the Hermitian form of Proposition 2.5.1 (p. 118), and \(U(f^*)=U(f)^*\)
(2.7.4) fails: for \(G=\mathbb R\), \(U\) the trivial one-dimensional representation and
\(f=i\cdot1_{[0,1]}\), \(U(f)=i\), \(U(f)^*=-i\), but the printed \(f^*\) gives \(U(f^*)=\int f=i\).
The computation of (2.5.3) on p. 121 uses \(\overline{f(g)}\).
Target: [W84.01.6.07].

### W84-E01.8.01. Indices in the composition series of a solvable algebra

Status: Confirmed.
Location: §1.8, p. 90, after the definition of solvability.
Printed: a sequence \(\mathfrak g=\mathfrak g^1\supset\cdots\supset\mathfrak g^{n-1}\supset
\mathfrak g^n=0\) "such that \(\mathfrak g^{i-1}\) is an ideal in \(\mathfrak g^i\) and the quotients
\(\mathfrak g^{i+1}/\mathfrak g^i\) are abelian".
Correct: \(\mathfrak g^{i+1}\) is an ideal in \(\mathfrak g^i\) and \(\mathfrak g^i/\mathfrak g^{i+1}\)
is abelian.
Evidence: In the printed chain \(\mathfrak g^{i-1}\supset\mathfrak g^i\), so the larger space cannot
be an ideal of the smaller one, and \(\mathfrak g^{i+1}/\mathfrak g^i\) is a quotient of a subspace
by a larger one. Problem 8 on p. 94 states the corrected form.
Target: [W84.01.8.01].

### W84-E01.8.02. Killing form of \(\mathfrak{sl}(n,K)\)

Status: Confirmed.
Location: §1.8, p. 95, Problem 12, Hint.
Printed: "the Killing form of \(\mathfrak{sl}(n,K)\) is equal to \(4n\,\mathrm{tr}(XY)\)".
Correct: \(B(X,Y)=2n\,\mathrm{tr}(XY)\).
Evidence: For \(n=2\) and \(H=\mathrm{diag}(1,-1)\), \(\mathrm{ad}H\) has eigenvalues \(2,-2,0\), so
\(B(H,H)=8\), while \(\mathrm{tr}(H^2)=2\): \(B=4\,\mathrm{tr}=2n\,\mathrm{tr}\); the printed formula
gives 16.
Target: [W84.01.8.05].

### Conventions and notation (not errata)

- p. 4: the definition of a subgroup does not state that \(H\) is non-empty; this is
  implicit.
- p. 3, Example 2(c): \(\det:GL(n,K)\to K\) takes values in the multiplicative group \(K_*\).
- p. 4: the right translation is \(r_gx=xg^{-1}\), so \(g\mapsto r_g\) is a left action;
  \((r_g\mu)(E)=\mu(Eg)\) and \(r_x\,dg=\delta_G(x)\,dg\) (pp. 74–75). The source's
  \(\delta_G\) is the reciprocal of Mathlib's `modularCharacter`.
- p. 56, Remark, and §2.8: the source sometimes identifies \(\mathfrak g\) with right-invariant
  vector fields; the synopsis uses left-invariant fields and records sign changes.
- p. 60, Example 5: "Theorem 1.4.6" refers to Proposition 1.4.7, and "Examples 1 and 2"
  to Examples 4 and 5.
- p. 76, Example 3(c): \(DG=\{xyx^{-1}y^{-1}\}\) denotes the subgroup generated by the
  commutators.
- p. 72: formula (1.6.4) is labelled Corollary 1.6.3; the proof of Proposition 1.6.6 refers
  to "Lemma 1.6.3" for Lemma 1.6.4.
- p. 104, (2.2.2) (used from §1.7): \(\rho(h)\) for \(h\in\Gamma\) is \(\delta_\Gamma(h)/
  \delta_G(h)\), which presumes the normalization \(\rho(e)=1\).
- The OCR text of these pages renders \(\delta\) and \(\varrho\) inconsistently; all formulas
  above were read from the page images.

## Chapter 2. Representations of Locally Compact Groups

Synopsis: Chapter 2 of [SYNOPSIS-Wawrzynczyk1984](SYNOPSIS-Wawrzynczyk1984.md).

### W84-E02.5.01. Bound for a positive definite function is not strict

Status: Confirmed.
Location: §2.5, p. 124, Proposition 2.5.4(4).
Printed: \(|\omega(g)|<\omega(e)\).
Correct: \(|\omega(g)|\le\omega(e)\).
Evidence: At \(g=e\) the printed inequality reads \(\omega(e)<\omega(e)\); the constant function
\(1\) and every unitary character \(\chi\) (with \(|\chi(g)|=1=\chi(e)\)) are positive definite.
The proof on p. 124 yields \(\le\).
Target: [W84.02.5.04].

### W84-E02.8.01. Sign in the action of \(\mathfrak g\) by differential operators

Status: Normalization check.
Location: §2.8, p. 130, (2.8.1); p. 132, (2.8.5) and Example 1.
Printed: \(Xf(g)=\lim_{t\to0}\frac{f(a_X(t)g)-f(g)}t\) (2.8.1), and \(dU(X)U(f)x=U(Xf)x\) (2.8.5);
Example 1 uses \(Xf(g)=\lim t^{-1}(f(\exp(-tX)g)-f(g))\).
Correct: With (2.8.1) as printed, \(dU(X)U(f)x=-U(Xf)x\) and \(X\mapsto X\) is an
antihomomorphism for the bracket of §1.3. With \(Xf(g)=\frac d{dt}f(\exp(-tX)g)|_{t=0}\)
(Example 1), which is the differential of the left regular representation, (2.8.5) holds and
\(X\mapsto X\) is a homomorphism. The synopsis uses the latter.
Evidence: \(U_{\exp tX}U(f)x=\int f(g)U_{\exp(tX)g}x\,dg=\int f(\exp(-tX)g)U_gx\,dg\) by left
invariance of \(dg\); differentiating at \(t=0\) gives \(U(\tilde Xf)x\) with
\(\tilde Xf(g)=\frac d{dt}f(\exp(-tX)g)|_{0}\), the negative of (2.8.1).
Target: [W84.02.8.01].

### W84-E02.8.02. The Schrödinger representation as printed is not a homomorphism

Status: Confirmed.
Location: §2.8, p. 133, Example 2.
Printed: for \(g=\begin{pmatrix}1&a&c\\0&1&b\\0&0&1\end{pmatrix}\),
\(U(g)f(x)=e^{ic}e^{-ibx}f(x+a)\), with \(dU(X_a)=-\frac d{dx}\), \(dU(X_b)=-ix\), \(dU(X_c)=i\).
Correct: \(U(g)f(x)=e^{ic}e^{ibx}f(x+a)\), with \(dU(X_a)=\frac d{dx}\), \(dU(X_b)=ix\),
\(dU(X_c)=i\). (Equivalently \(e^{ic}e^{-ibx}f(x-a)\), whose differential is the printed one.)
Evidence: \(g(a,b,c)g(a',b',c')=g(a+a',b+b',c+c'+ab')\). Symbolic computation gives
\(U(g)U(g')U(gg')^{-1}=e^{-2iab'}\) for the printed formula and \(1\) for the corrected one. The
printed differential is not that of the printed \(U\), since \(\frac d{dt}f(x+t)|_{t=0}=+f'(x)\);
the differential of the printed \(U\), \((\frac d{dx},-ix,i)\), violates the commutation relation:
\([\frac d{dx},-ix]=-i\ne dU(X_c)\).
Target: [W84.02.8.03].

### Conventions and notation (not errata)

- p. 98, Proposition 2.1.2(b): the topology on \(C_c(G,V)\) is called "compact convergence";
  the intended topology for continuity of \(L\) is the inductive-limit topology (the uniform
  topology also works).
- p. 104, (2.2.2): \(\rho(h)\), \(h\in\Gamma\), means \(\delta_\Gamma(h)/\delta_G(h)\) (with
  \(\rho(e)=1\)).
- p. 105: "\(\rho(hg)/\rho(g)\) is the Radon–Nikodym derivative of \(dh\mu\)" refers, in the
  notation of §1.7, to \(\mathcal S_\mu(h,g\Gamma)=d(h^{-1}\mu)/d\mu\).
- p. 116, Theorem 2.4.1(2): the bar denotes the conjugate (contragredient) representation of
  Example 2, §2.3.
- p. 125: the right regular representation in §2.6 is \(R_g\varphi(h)=\varphi(hg)\) without the
  factor \(\delta^{1/2}\) of p. 102.
- p. 140, Problem 15(a): "Proposition 2.3.4" refers to Proposition 2.5.4.

## Chapter 3. Decomposition Theory of Unitary Representations

### W84-E03.1.01. Product of decomposable operators

Status: Confirmed.
Location: §3.1, p. 149, last paragraph (after the definition of diagonal operators).
Printed: if \(A\) and \(B\) are decomposable, then \(A\circ B\) is the decomposable operator of
the operator field \(x\mapsto A(x)+B(x)\).
Correct: \(A\circ B\) is the decomposable operator of the field \(x\mapsto A(x)B(x)\).
Evidence: By (3.1.4), \((A(Bf))(x)=A(x)\bigl(B(x)f(x)\bigr)\). For \(A=B=\mathrm{id}\) the printed
field is \(2\,\mathrm{id}\) while \(A\circ B=\mathrm{id}\).
Target: [W84.03.1.09].

### W84-E03.2.01. Eigenfunctions of the Laplacian constant on parallel hyperplanes

Status: Confirmed.
Location: §3.2, p. 156, Proposition 3.2.8.
Printed: every eigenfunction of \(\Delta\) constant on the hyperplanes \((x-x_0|p)=0\) is
proportional to \(f_{p,\lambda}(x)=Ae^{\lambda(x|p)}+B\), \(A,B\in\mathbb C\).
Correct: such an eigenfunction is \(Ae^{\lambda(x|p)}+Be^{-\lambda(x|p)}\) (eigenvalue
\(\lambda^2|p|^2\), \(\lambda\ne0\)) or \(A+B(x|p)\) (eigenvalue \(0\)).
Evidence: A function constant on these hyperplanes is \(f(x)=\phi((x|p))\), and
\(\Delta f=|p|^2\phi''((x|p))\), so \(\Delta f=cf\) is the ODE \(|p|^2\phi''=c\phi\). For the printed
form, \(\Delta f=\lambda^2|p|^2Ae^{\lambda(x|p)}\) equals \(c(Ae^{\lambda(x|p)}+B)\) only if
\(cB=0\); so with \(B\ne0\) it is an eigenfunction only when \(\lambda A=0\), i.e. when \(f\) is
constant. The eigenfunction \(\cosh x_1\) (\(p=e_1\), eigenvalue 1) is not of the printed form.
Target: [W84.03.2.06].

### W84-E03.3.01. Paley–Wiener: the restriction to \(\mathbb R^n\) lies in \(\mathcal S\), not \(\mathcal D\)

Status: Confirmed.
Location: §3.3, p. 157, Theorem 3.3.1.
Printed: an entire function \(h\) on \(\mathbb C^n\) is the Fourier transform of a function of
class \(\mathcal D(\mathbb R^n)\) iff \(h\) restricted to \(\mathbb R^n\) is of class
\(\mathcal D(\mathbb R^n)\) and \(|h(x+iy)|\le Ce^{b|y|}\).
Correct: "\(h\) restricted to \(\mathbb R^n\) is of class \(\mathcal S(\mathbb R^n)\)", with the same
growth condition (equivalently, \(|h(z)|\le C_N(1+|z|)^{-N}e^{b|\operatorname{Im}z|}\) for all
\(N\)).
Evidence: If \(f\in\mathcal D(\mathbb R^n)\) and \(\hat f|_{\mathbb R^n}\) has compact support, then
\(\hat f\), being entire, vanishes on an open subset of \(\mathbb R^n\) and hence identically, so
\(f=0\) by (3.2.4). The printed criterion is thus satisfied only by \(h=0\), while every nonzero
\(f\in\mathcal D\) has a nonzero transform with the stated properties (p. 157 and Proposition
3.2.2(3) give \(\hat f|_{\mathbb R^n}\in\mathcal S\)).
Target: [W84.03.3.01].

### W84-E03.6.01. Missing factor \(1/2\pi\) in the \(L^1\) inversion formula

Status: Confirmed.
Location: Problems to Chapter 3, p. 170, Problem 10(d).
Printed: if \(f,\hat f\in L^1(\mathbb R)\), then \(g(x)=\int_{\mathbb R}\hat f(p)e^{-ipx}d\lambda(p)\)
equals \(f\) a.e.
Correct: \(g(x)=\frac1{2\pi}\int_{\mathbb R}\hat f(p)e^{-ipx}d\lambda(p)\) equals \(f\) a.e.
Evidence: In Problem 10(a), \(\int h_\sigma\,d\lambda=1\) with
\(h_\sigma(x)=\sigma/(\pi(\sigma^2+x^2))\) forces \(d\lambda\) to be Lebesgue measure. By 10(b),
\(f*h_\sigma(x)=\frac1{2\pi}\int e^{-\sigma|p|}\hat f(p)e^{-ipx}dp\), which tends to
\(\frac1{2\pi}\int\hat fe^{-ipx}dp\) as \(\sigma\to0\). Example: \(f=e^{-x^2/2}\) has
\(\hat f=\sqrt{2\pi}e^{-p^2/2}\) and \(\int\hat f\,dp=2\pi\ne f(0)\). This also agrees with (3.2.4).
Target: [W84.03.6.07].

### W84-E03.6.02. Definition of an eigenvector

Status: Confirmed.
Location: Problems to Chapter 3, p. 171, Problem 12.
Printed: a non-zero \(x\) is an eigenvector of \(A\) if there is \(\lambda\in\mathbb C\) with
\(Ax=x\).
Correct: \(Ax=\lambda x\).
Evidence: As printed, \(\lambda\) plays no role and every eigenvalue would be \(1\); the problem
then asks for the spectrum of \(f\mapsto h*f\), whose eigenvalues are \(\hat h(n)\).
Target: [W84.03.6.08].

### W84-E03.6.03. Sign of the frequency in the Poisson integral series

Status: Normalization check.
Location: Problems to Chapter 3, p. 172, Problem 14(a)–(c).
Printed: \(A(re^{i\theta})=\sum_kr^{|k|}\hat f(k)e^{ik\theta}\) equals
\(\frac1{2\pi}\int_0^{2\pi}P(r,\theta-t)f(e^{it})dt\), and (a) uses
\(\hat f(0)+2\sum_{k\ge1}\hat f(k)z^k\).
Correct: with the coefficient \(\hat f(k)=\frac1{2\pi}\int_0^{2\pi}f(e^{it})e^{ikt}dt\) of p. 160,
\(A(re^{i\theta})=\sum_kr^{|k|}\hat f(-k)e^{ik\theta}\) and (a) uses
\(\hat f(0)+2\sum_{k\ge1}\hat f(-k)z^k\). The printed formulas hold with the other common
convention \(\hat f(k)=\frac1{2\pi}\int f(e^{it})e^{-ikt}dt\). The synopsis keeps the p. 160
convention.
Evidence: Expanding \(P(r,\theta)=\sum_kr^{|k|}e^{ik\theta}\) gives
\(\frac1{2\pi}\int P(r,\theta-t)f(e^{it})dt=\sum_kr^{|k|}e^{ik\theta}\hat f(-k)\). For \(f(z)=z\),
\(\hat f(k)=\delta_{k,-1}\): the printed series gives \(re^{-i\theta}\), the Poisson integral
\(re^{i\theta}\).
Target: [W84.03.6.08].

### W84-E03.6.04. Mellin transform of a derivative

Status: Confirmed.
Location: Problems to Chapter 3, p. 172, Problem 15.
Printed: \(\mathcal M(f')(p+1)=(1-p)\mathcal Mf(p)\).
Correct: \(\mathcal M(f')(p+1)=-p\,\mathcal Mf(p)\). The second formula,
\(\mathcal M(vf')(p)=-p\,\mathcal Mf(p)\), is correct as printed.
Evidence: With \(\mathcal Mf(\lambda)=\int_0^\infty f(v)v^{\lambda-1}dv\) (3.4.2), integration by parts
for \(f\in C^1_c(\mathbb R_+)\) gives \(\int f'(v)v^p\,dv=-p\int f(v)v^{p-1}dv\). At \(p=0\) the left
side is \(\int f'=0\), whereas the printed right side is \(\int f(v)v^{-1}dv>0\) for \(f\ge0\),
\(f\ne0\).
Target: [W84.03.6.09].

### Conventions and notation (not errata)

- The Fourier transform on \(\mathbb R^n\) is \(\hat f(p)=\int e^{i(p|x)}f(x)dx\) (3.2.1), with
  Plancherel factor \((2\pi)^{-n}\) (3.2.2) and inversion kernel \((2\pi)^{-n}e^{-i(p|x)}\) (3.2.4);
  "isometry" in Theorem 3.2.6 (p. 156) holds after scaling by \((2\pi)^{-n/2}\). On \(\mathbb T\)
  the coefficient is \(\hat f(n)=\int f(z)z^n\,dm\) (p. 160), the opposite sign to Mathlib's
  `fourierCoeff`.
- p. 144, Example 1: the example of \(SO(2)\) on \(\mathbb R^2\) is introduced as showing that
  unitarity cannot be dropped from Corollary 3.1.4; the representation is orthogonal, and what
  the example shows is that the corollary needs complex scalars.
- p. 149, Proposition 3.1.8: "the operator defined by (3.1.3)" refers to (3.1.4).
- p. 166, Theorem 3.6.3: "normalization of the Haar measure \(dg\) on \(G\)" means the measure
  \(d\hat g\) on \(\widehat G\); the derivation of (3.6.3) cites "Theorem 3.5.3" for the argument of
  §3.2 (Theorem 3.2.4); Theorem 3.6.4 cites "(3.5.1)" for the Fourier transformation (3.6.1).
- p. 167, Theorem 3.6.5: the positive definite function is tacitly continuous.
- p. 168, Problem 2(b): the restriction of \(V\) is to the closure of \(\operatorname{Im}T\).
- p. 169, Problem 9: \(h_n\) is the physicists' Hermite polynomial times \(e^{-x^2/2}\); in (g)
  the coefficient \((e_n|f)\) is linear in \(f\) under the inner product convention of the header.

## Chapter 4. Representations of Compact Groups

### W84-E04.4.01. Matrix of the 3-cycle in the two-dimensional representation of \(S_3\)

Status: Confirmed.
Location: §4.4, p. 188, Example 1.
Printed: \(U^{\kappa_1}(\sigma_2)=\begin{pmatrix}e^{\frac23\pi i}&e^{\frac23\pi i}\\
e^{\frac23\pi i}&e^{\frac23\pi i}\end{pmatrix}\), \(\sigma_2=(1\,2\,3)\).
Correct: \(U^{\kappa_1}(\sigma_2)=\begin{pmatrix}e^{\frac23\pi i}&0\\0&e^{\frac43\pi i}\end{pmatrix}\) in
the basis \(f_1,f_2\) of the example.
Evidence: The printed matrix has determinant \(0\), so it is not invertible. In
\(H^{\kappa_1}=\{f:f(gk)=\kappa_1(k^{-1})f(g)\}\) with \((U_gf)(x)=f(g^{-1}x)\), \(f_1\) supported on
\(C_3\) and \(f_2\) on \(\sigma_4C_3\): \(U_{\sigma_2}f_1(e)=f_1(\sigma_2^{-1})=\kappa_1(\sigma_2)\), and
\(\sigma_2^{-1}\sigma_4=\sigma_4\sigma_2\) gives \(U_{\sigma_2}f_2(\sigma_4)=\kappa_1(\sigma_2)^{-1}\). The
corrected matrices satisfy \(U(\sigma_2)^3=I\), \(U(\sigma_4)^2=I\) and
\(U(\sigma_4)U(\sigma_2)U(\sigma_4)=U(\sigma_2)^{-1}\), and give the character values \(2,-1,0\) of
§4.6, Example 1.
Target: [W84.04.4.05].

### W84-E04.7.01. The representations \(U^k\) of \(O(2)\)

Status: Confirmed.
Location: §4.7, p. 198, Example 1.
Printed: the representations \(U^k\), \(k\in\mathbb Z\), "are irreducible—the representations \(U^l\)
and \(U^k\) are unequivalent except for the case \(l=-k\)".
Correct: \(U^k\) is irreducible for \(k\ne0\), and \(U^l\cong U^k\) iff \(l=\pm k\). \(U^0\) is reducible:
\(U^0\cong1\oplus\det\).
Evidence: \(U^0(r(\varphi))=I\) and \(U^0(r(\varphi)s)=\begin{pmatrix}0&1\\1&0\end{pmatrix}\), so
\(e_1\pm e_2\) span invariant lines carrying \(1\) and \(\det\). For \(k\ne0\), a line invariant
under \(\operatorname{diag}(e^{ik\varphi},e^{-ik\varphi})\) is a coordinate axis, which
\(U^k(s)\) exchanges. The character of \(U^k\) is \(2\cos k\varphi\) on rotations and \(0\) on
reflections, so it determines \(|k|\). The decomposition of \(L\) printed on p. 199 uses only
\(k\ge1\).
Target: [W84.04.7.05].

### Conventions and notation (not errata)

- p. 176: the rank-one operator is printed \(T_hh_1=(h_1|h)h\), which is linear in \(h_1\) only if
  the inner product is linear in the first argument. The rest of the chapter (the inner product
  (4.1.2) as \(\operatorname{tr}(T^*S)\) in Problem 2, (4.5.1)–(4.5.5), (4.6.7), (4.7.1)–(4.7.6),
  Problem 18) uses the convention of the header (conjugate-linear in the first argument); the
  synopsis writes \(T_hh_1=(h|h_1)h\). The computation of \(S_h^*\) on p. 191 omits the conjugate
  of \(f\) in \((f|S_hx)\) for the same reason.
- p. 180, proof of Theorem 4.2.3: "This concludes the proof of Proposition 4.2.2" refers to
  Theorem 4.2.3, and \((L^2(M))'\) is identified with \(L^2(M)\) (printed \(L^2(G)\)).
- p. 185, proof of Corollary 4.4.1: "\(TT^*\) is an isometry" means that \(TT^*\in L_G(H)\) is a
  positive multiple of the identity.
- p. 186: \(\widehat G\) is introduced as "the space of the equivalence classes of unitary
  representations"; irreducible representations are meant.
- p. 189: the identity \(w_{x,h}=\overline{w_{h,x}}\) holds after \(g\mapsto g^{-1}\):
  \(w_{x,h}(g)=\overline{w_{h,x}(g^{-1})}\); the resulting step \(c(h)(x|x)=c(x)(h|h)\) uses the
  inversion invariance of Haar measure (unimodular \(G\)), as Problem 17 assumes.
- p. 192, (4.6.6): \(\chi^*\) is taken with the involution of (1.6.18); \(\chi^*=\chi\) for unitary
  representations of unimodular groups.
- p. 206, Problem 19, hint: the cross-reference "Problem 12, § 1.16" does not exist (Chapter 1 has
  §§1.1–1.8).

## Chapter 5. Theory of Spherical Functions

### W84-E05.1.01. Convolution of a spherical function with a right-\(K\)-invariant function

Status: Confirmed.
Location: §5.1, p. 218, Theorem 5.1.7 (1) and the last line of its proof.
Printed: \(\Phi*f=\check\Phi(f)\,\Phi\) for \(f\in\mathcal C_0(G/K)\); the proof ends with
\(\Phi(x)\int_G\Phi(g^{-1})f(g)dg\).
Correct: \(\Phi*f=\check w(f)\,\Phi=\Big(\int_Gw(g^{-1})f(g)dg\Big)\Phi\).
Evidence: The proof's own step \(\int_G\int_K\Phi(xkg^{-1})dk\,f(g)dg\) equals
\(\Phi(x)\int_Gw(g^{-1})f(g)dg\) by the spherical equation \(\int_K\Phi(xkh)dk=\Phi(x)w(h)\).
Counterexample to the printed form: \(G=\mathbb R\), \(K=\{0\}\), \(w(x)=e^{ix}\) and \(\Phi=2w\)
satisfy \(\Phi(x+h)=\Phi(x)w(h)\); then \(\Phi*f=\check w(f)\Phi\) while
\(\check\Phi(f)\Phi=2\check w(f)\Phi\), which differ whenever \(\check w(f)\ne0\). Parts (2) and (3)
are correct as printed.
Target: [W84.05.1.12].

### Conventions and notation (not errata)

- p. 209: the projection onto the line \(\mathbb Cv\) is written \(P_\chi x=(v|x)v\), which is the
  form for an inner product conjugate-linear in the first argument; with the convention of the
  header it is \((x|v)v\). Theorem 5.1.1 holds under either convention.
- p. 210, proof of Lemma 5.1.3(a): "(5.1.2)" refers to (5.1.5); p. 226, proof of Lemma 5.4.1:
  "Lemma 5.1.7" refers to Theorem 5.1.5.
- p. 226, Example 1(f): the embedding of \(SO(n-1)\) is the upper left block and
  \(S=\mathrm{diag}(-1,\dots,-1,1)\); the fixed group of \(\sigma\) is
  \(S(O(n-1)\times O(1))\), which contains \(SO(n-1)\) as identity component, as the
  definition of a symmetric pair requires.

## Chapter 6. The Euler \(\Gamma\)- and \(B\)-Functions

### W84-E06.2.01. Range of validity of the Fourier form of the Mellin transform

Status: Confirmed.
Location: §6.2, p. 247, (6.2.5).
Printed: \(\mathcal Mf(z)=\frac{\Gamma(z)}{2\pi}e^{-i\frac\pi2z}\int_{-\infty}^{+\infty}\hat f(x)
x^{-z}dx\) for \(\mathrm{Re}\,z>0\).
Correct: The formula holds for \(0<\mathrm{Re}\,z<1\), with \(x^{-z}\) read as the boundary value
\((x-i0)^{-z}\) (\(=|x|^{-z}e^{i\pi z}\) for \(x<0\)) obtained from \(c\to0^-\) in (6.2.4).
Evidence: Near \(x=0\), \(\hat f(x)\to\hat f(0)=\int f\), which is nonzero for \(f\ge0\), \(f\ne0\);
\(\int_{-1}^1|x|^{-\mathrm{Re}\,z}dx=\infty\) for \(\mathrm{Re}\,z\ge1\), so the integral diverges
(e.g. \(z=1\) gives a non-integrable \(1/x\) singularity), while \(\mathcal Mf(1)=\int f\) is
finite. For \(x<0\) the limit of \(w^{-z}\) as \(w=x+ic\), \(c\to0^-\), has \(\arg w\to-\pi\),
not the principal value \(+\pi\).
Target: [W84.06.2.01].

### W84-E06.2.02. Phases in the Fourier transforms of \(x_\pm^{z-1}\)

Status: Normalization check.
Location: §6.2, p. 247, the two displays after (6.2.5).
Printed: \(\mathcal F\tau_+^{z-1}(x)=\Gamma(z)x^{-z}e^{-i\frac\pi2z}\),
\(\mathcal F\tau_-^{z-1}(x)=\Gamma(z)x^{-z}e^{i\frac\pi2z}\).
Correct: With the source's Fourier transform \(\hat f(p)=\int e^{ipx}f(x)dx\) ((3.2.1), and
(6.2.1)), for \(x>0\): \(\mathcal F\tau_+^{z-1}(x)=\Gamma(z)x^{-z}e^{+i\pi z/2}\) and
\(\mathcal F\tau_-^{z-1}(x)=\Gamma(z)x^{-z}e^{-i\pi z/2}\). The printed formulas hold for the
kernel \(e^{-ixt}\).
Evidence: By Lemma 6.1.2 with \(u=-ix+\varepsilon\), \(\varepsilon\to0^+\),
\(\int_0^\infty t^{z-1}e^{ixt}dt=\Gamma(z)(-ix)^{-z}=\Gamma(z)x^{-z}e^{i\pi z/2}\) for \(x>0\).
Check at \(z=\frac12\), \(x=1\): \(\int_0^\infty t^{-1/2}e^{it}dt=\sqrt\pi\,e^{i\pi/4}\) (Fresnel),
not \(\sqrt\pi\,e^{-i\pi/4}\). The synopsis uses the convention (3.2.1).
Target: [W84.06.2.02].

### W84-E06.3.01. Sign of the integral \(\int_0^\infty b^q(1+b)^{-1}db\)

Status: Confirmed.
Location: §6.3, p. 251, line after (6.3.11) ("The final result is \(\pi/\sin\pi q\)").
Printed: \(\Gamma(1+q)\Gamma(-q)=\int_0^\infty b^q(1+b)^{-1}db=\frac{\pi}{\sin\pi q}\),
\(-1<\mathrm{Re}\,q<0\).
Correct: \(\int_0^\infty b^q(1+b)^{-1}db=\frac{\pi}{\sin\pi(q+1)}=-\frac{\pi}{\sin\pi q}\).
Evidence: At \(q=-\frac12\): \(\Gamma(\frac12)^2=\pi\) and \(\int_0^\infty b^{-1/2}(1+b)^{-1}db=\pi\),
while \(\pi/\sin(-\pi/2)=-\pi\). The reflection formula (6.3.12) follows correctly from the
corrected value with \(z=-q\) via \(\Gamma(1-z)\Gamma(z)\).
Target: [W84.06.3.03].

### Conventions and notation (not errata)

- p. 252: "\(\Gamma(\frac12)=\sqrt\pi\) by (6.3.11)" refers to the reflection formula (6.3.12).
- Problem 3(a), p. 255, states the contour formula for \(z\in\mathbb C\); it is meaningful for
  \(z\notin\mathbb Z\) (at positive integers both the integral and \(e^{2\pi iz}-1\) vanish).

## Chapter 7. Bessel Functions

### W84-E07.3.01. Angle in the expansion of \(J_0\)

Status: Confirmed.
Location: §7.3, p. 266, (7.3.7).
Printed: \(J_0(r)=\sum_{k\in\mathbb Z}(-1)^ke^{ik\theta}J_k(r_1)J_k(r_2)\), obtained from Graf's
formula (7.3.4) with \(n=0\), where \(r_1+r_2e^{i\theta_2}=re^{i\theta}\).
Correct: \(J_0(r)=\sum_{k\in\mathbb Z}(-1)^ke^{ik\theta_2}J_k(r_1)J_k(r_2)\).
Evidence: Setting \(m=0\) in (7.3.4) gives \(\sum_kJ_{-k}(r_1)J_k(r_2)e^{ik\theta_2}=J_0(r)\), and
\(J_{-k}=(-1)^kJ_k\). Numerically, for \(r_1=1.3\), \(r_2=0.7\), \(\theta_2=0.9\) (so
\(r=1.8212\), \(\theta=0.3036\)): \(J_0(r)=0.328524\); the sum with \(\theta_2\) gives
\(0.328524\), the sum with \(\theta\) gives \(0.236167\).
Target: [W84.07.3.02].

### W84-E07.4.01. Missing square in the Plancherel identity of Theorem 7.4.1

Status: Confirmed.
Location: §7.4, p. 270, Theorem 7.4.1, and p. 271, end of the proof.
Printed: \(\frac1{2\pi}\int_0^\infty\|F_\beta f\|^2\beta\,d\beta=\|f\|_{L^2(\mathbb C)}\) (and
\(\int_0^\infty\beta\|F_\beta f\|^2d\beta=2\pi\|f\|_{L^2(\mathbb C)}\) in the proof).
Correct: \(\frac1{2\pi}\int_0^\infty\|F_\beta f\|^2\beta\,d\beta=\|f\|^2_{L^2(\mathbb C)}\).
Evidence: The left side is quadratic and the printed right side homogeneous of degree one in
\(f\) (replace \(f\) by \(2f\)). The proof's own computation is
\(\int_0^\infty\beta\int_{\mathbb T}|\hat f(\alpha\beta)|^2d\alpha\,d\beta=\frac1{2\pi}
\|\hat f\|_2^2=2\pi\|f\|_2^2\) by the Plancherel formula \(\|\hat f\|_2^2=4\pi^2\|f\|_2^2\).
Target: [W84.07.4.01].

### W84-E07.4.02. Problem 7: a sum of odd-order Bessel functions

Status: Confirmed.
Location: Problem 7, p. 275.
Printed: \(z(z^2+1)=z\sum_{n\ge0}(2n+1)^3J_{2n+1}(z)\).
Correct: \(z(z^2+1)=2\sum_{n\ge0}(2n+1)^3J_{2n+1}(z)\).
Evidence: From \(\sin(z\sin\varphi)=2\sum_{n\ge0}J_{2n+1}(z)\sin(2n+1)\varphi\) (generating
function), the coefficient of \(\varphi^3\) is \(-(z+z^3)/6\) on the left and
\(-\frac13\sum(2n+1)^3J_{2n+1}(z)\) on the right. Numerically at \(z=1.7\): \(z(z^2+1)=6.6130\),
\(\sum(2n+1)^3J_{2n+1}(1.7)=3.3065\), so the printed right side is \(5.6211\).
Target: [W84.07.4.05].

### W84-E07.4.03. Problem 17: the Gegenbauer formula for \(J_0\)

Status: Confirmed.
Location: Problem 17, pp. 277–278.
Printed: \(J_0(r)=\sum_{m\ge0}\varepsilon_mJ_m(r_1)J_m(r_2)\cos\theta_2\), with \(r,r_1,r_2,\theta_2\)
as in (7.3.4).
Correct: \(J_0(r)=\sum_{m\ge0}\varepsilon_m(-1)^mJ_m(r_1)J_m(r_2)\cos m\theta_2\).
Evidence: This is the real form of the corrected (7.3.7) ([W84-E07.3.01]). For \(r_1=1.3\),
\(r_2=0.7\), \(\theta_2=0.9\): \(J_0(r)=0.328524\), the corrected sum is \(0.328524\), the printed
sum is \(0.566911\). (The familiar form without \((-1)^m\) uses
\(r^2=r_1^2+r_2^2-2r_1r_2\cos\theta_2\), but (7.3.4) gives \(r^2=r_1^2+r_2^2+2r_1r_2\cos\theta_2\).)
Target: [W84.07.3.02].

### W84-E07.4.04. Problem 21: left-hand side should be \(J_n\)

Status: Confirmed.
Location: Problem 21, p. 278.
Printed: \(J_0(z)=\frac{2^nn!}{(2n)!}z^n\big(1+\frac{d^2}{dz^2}\big)^nJ_0(z)\).
Correct: \(J_n(z)=\frac{2^nn!}{(2n)!}z^n\big(1+\frac{d^2}{dz^2}\big)^nJ_0(z)\).
Evidence: For \(n=1\), Bessel's equation gives \(J_0+J_0''=-J_0'/z=J_1/z\), so the right side
is \(J_1(z)\ne J_0(z)\). Numerically at \(z=1.7\) the right side equals \(0.577765=J_1\),
\(0.281739=J_2\), \(0.085150=J_3\) for \(n=1,2,3\), while \(J_0(1.7)=0.397985\).
Target: [W84.07.4.05].

### Conventions and notation (not errata)

- Chapter 7 uses the inner product conjugate-linear in the first argument:
  \(t_{mn}(g)=(e_m|T(g)e_n)=\int\overline{e_m}\,T(g)e_n\,d\alpha\) ((7.2.2)).
- p. 261, proof of Proposition 7.2.1: "Proposition 5.1.9" refers to Lemma 5.2.2 and
  "Theorem 5.1.4" to Theorem 5.2.3.
- p. 270: \(\frac i2dz\wedge d\bar z\) denotes Lebesgue measure \(dx\,dy\) on \(\mathbb C\).
- (7.3.9) is printed with exponent \(e^{i(q-2p)\theta}\); this agrees with the form
  \(e^{i(2p-q)\theta}\) obtained directly from (7.3.8) by the substitution \(\theta\mapsto
  \pi-\theta\).

## Chapter 8. Theory of Jacobi and Legendre Polynomials

### W84-E08.1.01. Evaluation point in the derivative formula for \(t^l_{jk}\)

Status: Confirmed.
Location: §8.1, p. 280, the two displays before (8.1.3).
Printed: \(\frac{d^{l+j}}{dy^{l+j}}[(y-1)^{l+k}(y+1)^{l-k}]\big|_{y=\gamma\beta+\frac12}\).
Correct: evaluation at \(y=2\beta\gamma+1\).
Evidence: The substitution \(\frac{y-1}2=(\alpha z+\gamma)\beta\) gives \(y=2\beta(\alpha z+\gamma)+1\),
which is \(2\beta\gamma+1\) at \(z=0\). For \(g=g(\theta)\), \(2\beta\gamma+1=1-2\sin^2\frac\theta2=
\cos\theta\), the point used in (8.1.4), whereas \(\gamma\beta+\frac12=\frac12\cos\theta\).
Target: [W84.08.1.02].

### W84-E08.1.02. Power of 2 in the \(x\)-form of (8.1.4)

Status: Confirmed.
Location: §8.1, p. 281, (8.1.4), second display.
Printed: \(P^l_{jk}(x)=\sqrt{\frac{(l-j)!}{(l+k)!(l-k)!(l+j)!}}(1+x)^{\frac{j+k}2}(1-x)^{\frac{j-k}2}
2^{-l-j}i^{j-k}\frac{d^{l+j}}{dx^{l+j}}[(x-1)^{l+k}(x+1)^{l-k}]\).
Correct: the factor is \(2^{-l}\), not \(2^{-l-j}\).
Evidence: \(\cos^{j+k}\frac\theta2\sin^{j-k}\frac\theta2=2^{-j}(1+x)^{\frac{j+k}2}(1-x)^{\frac{j-k}2}\),
so the first display's \(2^{j-l}\) becomes \(2^{-l}\). Direct computation of the coefficient of
\(e_j\) in \(T^l_{g(\theta)}e_k\) at \(l=1\), \(j=1\), \(k=0\), \(x=0.3\) gives
\(P^1_{10}=0.674537\,i\); the printed formula gives \(0.337268\,i\). The two agree only for
\(j=0\).
Target: [W84.08.1.03].

### W84-E08.1.03. Relation between \(P^l_{jk}\) and Jacobi polynomials

Status: Confirmed.
Location: §8.1, p. 281, (8.1.9).
Printed: \(P^l_{jk}(x)=P^{(k-j,-k-j)}_{l+j}(x)(1-x)^{\frac{k-j}2}(1+x)^{\frac{-k-j}2}i^{k-j}
\sqrt{\frac{(l+k)!(l-k)!}{(l+j)!(l-j)!}}\).
Correct: \(P^l_{jk}(x)=i^{k-j}2^j\sqrt{\frac{(l+j)!(l-j)!}{(l+k)!(l-k)!}}(1-x)^{\frac{k-j}2}
(1+x)^{-\frac{k+j}2}P^{(k-j,-k-j)}_{l+j}(x)\).
Evidence: Inserting the Rodrigues formula (8.1.5) with \(n=l+j\), \(\alpha=k-j\), \(\beta=-k-j\) into the
corrected (8.1.4) gives the corrected form. Numerically at \(x=0.3\): \(P^1_{01}=0.674537\,i\),
printed \(1.349074\,i\); \(P^1_{10}=0.674537\,i\), printed \(0.168634\,i\); the corrected formula
reproduces the matrix elements for all tested \((l,j,k)\), including half-integral \(l\).
Target: [W84.08.1.05].

### W84-E08.3.01. Sign in the subtraction formula (8.3.15)

Status: Confirmed.
Location: §8.3, p. 294, (8.3.15).
Printed: \(P^l_{mn}(\cos(\theta_1-\theta_2))=\sum_k(-1)^{k-m}P^l_{mk}(\cos\theta_1)P^l_{kn}(\cos\theta_2)\).
Correct: the sign is \((-1)^{k-n}\).
Evidence: (8.3.13) with \(\gamma=\pi\), \(\varphi=0\), \(\psi=\pi\) gives
\(P^l_{mn}(\cos\theta)e^{in\pi}=\sum_kP^l_{mk}P^l_{kn}e^{ik\pi}\). Numerically, \(l=2\), \(m=-2\),
\(n=-1\), \(\theta_1=1\), \(\theta_2=0.6\): \(P^2_{-2,-1}(\cos0.4)=0.374048\,i\); the sum with
\((-1)^{k-n}\) gives \(0.374048\,i\), with \((-1)^{k-m}\) it gives \(-0.374048\,i\). The two signs
agree when \(m-n\) is even, in particular in the unitarity relation derived from it.
Target: [W84.08.3.05].

### W84-E08.4.01. Index in the lowering recurrence (8.4.11)

Status: Confirmed.
Location: §8.4, p. 297, (8.4.11).
Printed: \(\sqrt{1-z^2}\frac d{dz}P^l_{mk}+\frac{m-kz}{\sqrt{1-z^2}}P^l_{mk}=-i\sqrt{(l+k)(l-k+1)}
P^l_{m,k+1}\).
Correct: the right side is \(-i\sqrt{(l+k)(l-k+1)}P^l_{m,k-1}\) (from \(dL(H_-)\) in (8.4.7)).
Evidence: For \(l=m=k=\frac12\), \(P^{1/2}_{\frac12\frac12}(\cos\theta)=\cos\frac\theta2\) and
\(P^{1/2}_{\frac12,-\frac12}(\cos\theta)=i\sin\frac\theta2\); the left side equals
\(\sin\frac\theta2\), which is \(-i\cdot1\cdot P^{1/2}_{\frac12,-\frac12}\), while the printed right side
involves the nonexistent index \(k+1=\frac32\) (zero). The text's next step ("(8.4.11) for the
parameters \(l,m,k+1\)") also requires \(k-1\).
Target: [W84.08.4.04].

### W84-E08.5.01. Mehler–Dirichlet formula: constant and range

Status: Confirmed.
Location: §8.5, p. 299, display after (8.5.4), the change of variable, and (8.5.5).
Printed: \(P_l(\cos\theta)=\frac2\pi\int_0^\pi\frac{\sin[(l+\frac12)t(\theta,\varphi)]}{\sin\frac12t(\theta,
\varphi)}d\varphi\); \(\sin\frac12t\,dt=\cos\frac12\theta\sin\varphi\,d\varphi\);
\(P_l(\cos\theta)=\frac2\pi\int_0^\pi\frac{\sin t(l+\frac12)}{\sqrt{\cos^2\frac12\theta-\cos^2\frac12t}}dt
=\frac2\pi\int_0^\pi\frac{\sin t(l+\frac12)}{\sqrt{2(\cos\theta-\cos t)}}dt\).
Correct: \(P_l(\cos\theta)=\frac1\pi\int_0^\pi\frac{\sin(l+\frac12)t}{\sin\frac12t}d\varphi\),
\(\sin\frac12t\,dt=\cos\frac12\theta\sin\frac12\varphi\,d\varphi\), and
\(P_l(\cos\theta)=\frac1\pi\int_\theta^\pi\frac{\sin(l+\frac12)t}{\sqrt{\cos^2\frac\theta2-\cos^2\frac t2}}
dt=\frac{\sqrt2}\pi\int_\theta^\pi\frac{\sin(l+\frac12)t}{\sqrt{\cos\theta-\cos t}}dt\).
Evidence: The normalized measure on \(K\) is \(\frac1{4\pi}d\varphi\) on \([-2\pi,2\pi]\), and the
integrand is even and \(2\pi\)-periodic for integer \(l\), so \(\int_Kdk=\frac1\pi\int_0^\pi d\varphi\).
As \(\varphi\) runs over \([0,\pi]\), \(t\) runs over \([\theta,\pi]\); for \(t<\theta\) the radicand is
negative. Numerically, \(l=3\), \(\theta=0.9\): \(P_3(\cos0.9)=-0.331941\); the printed first integral
gives \(-0.663883\), the printed last integral over \([0,\pi]\) is not real, the corrected forms
give \(-0.331941\).
Target: [W84.08.5.02].

### W84-E08.7.01. Problem 9: missing sign in the sum for \(P^l_{rs}\)

Status: Confirmed.
Location: Problem 9, p. 314.
Printed: \(P^l_{rs}(z)=(-1)^{\frac{-r-s}2}\big[\frac{(l-s)!(l-r)!}{(l+s)!(l+r)!}\big]^{\frac12}
\big(\frac{1+z}{1-z}\big)^{\frac{r+s}2}\sum_{k=\max(r,s)}^l\frac{(l+k)!}{(l-k)!(k-s)!(k-r)!}
\big(\frac{1-z}2\big)^k\).
Correct: the summand carries the factor \((-1)^k\) (equivalently \(((z-1)/2)^k\)).
Evidence: For \(l=2\), \(r=-1\), \(s=1\), \(z=0.3\): \(P^2_{-1,1}(0.3)=-0.56\) from (8.1.11); the
printed sum gives \(1.54\), the corrected one \(-0.56\). With \(r=m\), \(s=0\) the corrected
formula reduces to Problem 15, which has \((-1)^j\).
Target: [W84.08.7.06].

### W84-E08.7.02. Problem 14: sign and summation range in the explicit formula for \(P^m_l\)

Status: Confirmed.
Location: Problem 14, p. 315.
Printed: \(P^m_l(x)=\frac{(-1)^{l+m}(l+m)!}{2^l(l-m)!}(1-x^2)^{-\frac m2}\sum_k\frac{(-1)^k(2k)!
x^{2k-l+m}}{k!(l-k)!(2k-l+m)!}\), summed over \(0\le k\le l\), \(2k\ge l+m\).
Correct: \(P^m_l(x)=\frac{(-1)^l(l+m)!}{2^l(l-m)!}(1-x^2)^{-\frac m2}\sum_{0\le k\le l,\,2k\ge l-m}
\frac{(-1)^k(2k)!x^{2k-l+m}}{k!(l-k)!(2k-l+m)!}\) (from (8.1.7) for \(P^{-m}_l\) and Problem 13);
equivalently \(P^m_l(x)=\frac{(-1)^{l+m}}{2^l}(1-x^2)^{\frac m2}\sum_{2k\ge l+m}\frac{(-1)^k(2k)!
x^{2k-l-m}}{k!(l-k)!(2k-l-m)!}\).
Evidence: At \(x=0.3\): \(P^1_3=0.787000\), printed \(0.785427\); \(P^2_3=4.095\), printed
\(0.040055\); both corrected forms give the exact values.
Target: [W84.08.7.06].

### W84-E08.7.03. Problem 17(a): factorial in Schläfli's integral for \(P^m_l\)

Status: Confirmed.
Location: Problem 17(a), p. 317.
Printed: \(P^m_l(z)=\frac{(-1)^m(1-z^2)^{m/2}}{2^ll!}\frac{(l-m)!}{2\pi i}\oint\frac{(t^2-1)^l}
{(t-z)^{l+m+1}}dt\).
Correct: \((l+m)!\) in place of \((l-m)!\) (Cauchy's formula for the \((l+m)\)-th derivative in
(8.1.7)).
Evidence: \(l=3\), \(m=1\), \(z=0.3\): \(P^1_3=0.787000\); the printed expression gives
\(0.065583\) (smaller by \(2!/4!\)).
Target: [W84.08.7.08].

### W84-E08.7.04. Problem 17(b): lower parameter of the hypergeometric function

Status: Confirmed.
Location: Problem 17(b), p. 317.
Printed: \(P^m_l(z)=(-\frac12)^m\frac{(l+m)!}{(l-m)!m!}(1-z^2)^{\frac m2}F(m-l,m+l+1,m+l;\frac12(1-z))\).
Correct: \(F(m-l,m+l+1;m+1;\frac12(1-z))\).
Evidence: \(l=3\), \(m=1\), \(z=0.3\): \(P^1_3=0.787000\); with third parameter \(m+1\) the formula
gives \(0.787000\), with \(m+l\) it gives \(-1.767172\). For \(m=0\) the printed version would give
\(F(-l,l+1;l;\cdot)\ne P_l\), contradicting Problem 16(g).
Target: [W84.08.7.08].

### W84-E08.7.05. Problem 17(e): signs in the recurrences for \(P^m_l\)

Status: Confirmed.
Location: Problem 17(e), p. 317.
Printed: \(\frac d{dz}P^m_l=(1-z^2)^{-\frac12}P^{m+1}_l-\frac{mz}{1-z^2}P^m_l\) and
\((2l+1)(1-z^2)^{\frac12}P^m_l=P^{m+1}_{l+1}-P^{m+1}_{l-1}\).
Correct: with \(P^m_l\) as in (8.1.7) (Condon–Shortley phase):
\(\frac d{dz}P^m_l=-(1-z^2)^{-\frac12}P^{m+1}_l-\frac{mz}{1-z^2}P^m_l\) and
\((2l+1)(1-z^2)^{\frac12}P^m_l=P^{m+1}_{l-1}-P^{m+1}_{l+1}\).
Evidence: \(l=3\), \(m=1\), \(z=0.3\): \(\frac d{dz}P^1_3=-4.552177\), the printed right side is
\(4.033276\); \(7\sqrt{0.91}\,P^1_3(0.3)=5.255250\) while \(P^2_4-P^2_2=-5.255250\). For \(m=0\),
\(l=1\): \(P^1_1=-\sqrt{1-z^2}\) and \(P_1'=1\), so the first printed formula gives \(-1\).
Target: [W84.08.7.08].

### W84-E08.7.06. Problem 22(d): factor in the recurrence

Status: Confirmed.
Location: Problem 22(d), p. 320.
Printed: \(2i\frac{m-nz}{\sqrt{1-z^2}}P^l_{mn}=\sqrt{(l+n)(l-n+1)}P^l_{m,n-1}-\sqrt{(l-n)(l+m+1)}
P^l_{m,n+1}\).
Correct: \(\sqrt{(l-n)(l+n+1)}\) in the second term (difference of (8.4.10) and (8.4.11)).
Evidence: For \(l=2\), \(m=1\), \(n=0\), \(z=0.3\) the printed identity fails by \(0.0985\), the
corrected one holds to rounding; the printed version is correct only when \(m=n\).
Target: [W84.08.4.04].

### W84-E08.7.07. Problem 23(a): Euler angle \(\varphi\)

Status: Confirmed.
Location: Problem 23(a), p. 320.
Printed: \(\tan\varphi=\frac{\sin\varphi_2}{\sin\theta_1\cos\theta_2}\).
Correct: \(\tan\varphi=\frac{\sin\theta_2}{\sin\theta_1\cos\theta_2}\) (from (8.3.11) with
\(\gamma=\frac\pi2\)); no variable \(\varphi_2\) occurs in part (a).
Evidence: For \(\theta_1=0.8\), \(\theta_2=0.5\) the Euler angle of \(a(\theta_1)k(\frac\pi2)a(\theta_2)\)
has \(\tan\varphi=0.761550=\sin\theta_2/(\sin\theta_1\cos\theta_2)\); \(\cos\theta=\cos\theta_1\cos\theta_2\)
and \(\tan\psi=\sin\theta_1/(\cos\theta_1\sin\theta_2)\) are correct.
Target: [W84.08.3.05].

### Conventions and notation (not errata)

- (8.1.7) defines \(P^m_l\) with the Condon–Shortley phase \((-1)^m\); Problem 13 relates it to
  \(P^l_{m0}\) by \(P^m_l=i^m\sqrt{(l+m)!/(l-m)!}\,P^l_{m0}\).
- Matrix elements in Chapter 8 are coefficients with respect to the dual basis,
  \(t^l_{jk}(g)=\langle e^j,T_ge_k\rangle\); with the inner product (8.2.1) this is \((e_j|T_ge_k)\) for
  either convention of linearity.
- The normalization (8.7.13), \(C(l,l',k;l,-l',l-l')>0\), coincides with the Condon–Shortley
  convention (checked against the standard \(\langle l\,l\,l'\,{-l'}|k\,l-l'\rangle\) for
  \((l,l')=(2,1),(\frac32,1),(3,\frac32),(2,2)\)).
- p. 293: "special case of formula (8.3.8)" refers to (8.3.9), and "the left-hand side of
  (8.3.10)" to (8.3.12); p. 301: "Proposition 8.1.6" refers to Proposition 8.6.1; p. 308:
  "(7.8.10)" is (8.7.10).


## Chapter 9. Gegenbauer Polynomials

### W84-E09.2.01. (9.2.2): sign in the dimension of \(J^l_n/\tau(J^{l-2}_n)\)

Status: Confirmed.
Location: §9.2, p. 325, (9.2.2) and the display for \(\dim K^l_n\).
Printed: \(\dim J^l_n/\tau(J^{l-2}_n)=\dim K^l_n=\frac{(2l-n-2)(n+l-3)!}{(n-2)!\,l!}\).
Correct: \(\frac{(2l+n-2)(n+l-3)!}{(n-2)!\,l!}\) (as printed for \(\dim H^l\) on p. 335).
Evidence: \(\binom{n+l-1}{l}-\binom{n+l-3}{l-2}=\frac{(2l+n-2)(n+l-3)!}{(n-2)!\,l!}\); for \(n=3\),
\(l=1\) the quotient is \(J^1_3\), of dimension 3, while the printed formula gives \(-3\).
Target: [W84.09.2.01].

### W84-E09.2.02. (9.2.6): coefficient in \(\Delta(r^{2k}f_1)\)

Status: Confirmed.
Location: Lemma 9.2.6, p. 328, (9.2.6).
Printed: \(\Delta(r^{2k}f_1)=2k(n+2l-2k-1)r^{2k-2}f_1+r^{2k}\Delta f_1\).
Correct: \(2k(n+2l-2k-2)\) for \(f_1\) homogeneous of degree \(l-2k\) (the next display on the
page uses \(n+2l-2k-2\), and \(k=1\) gives the printed \(2n+4l-8\)).
Evidence: \(\Delta(r^{2k}f_1)=2k(n+2k-2)r^{2k-2}f_1+4k(l-2k)r^{2k-2}f_1+r^{2k}\Delta f_1\); for
\(n=3\), \(l=2\), \(k=1\), \(f_1=1\): \(\Delta r^2=6\), the printed coefficient gives \(8\).
Target: [W84.09.2.05].

### W84-E09.2.03. Projection \(P^lx_n^l\): last factor of the denominator

Status: Confirmed.
Location: §9.2, p. 329, display after (9.2.8).
Printed: \(P^lw_0(x)=\sum_k\frac{(-1)^kl!\,r^{2k}x_n^{l-2k}}{k!\,2^k(l-2k)!\,(n+2l-4)\cdots(n+2l-2k+1)}\).
Correct: the last factor is \((n+2l-2k-2)\), as in (9.2.8), since
\(\Delta^kx_n^l=\frac{l!}{(l-2k)!}x_n^{l-2k}\).
Evidence: For \(n=3\), \(l=2\) the harmonic projection is \(x_3^2-\frac13r^2\) (\(\Delta=2-2=0\)),
with denominator \(n+2l-4=3\) for \(k=1\); the printed last factor would be \(n+2l-1=6\).
Target: [W84.09.2.06].

### W84-E09.3.01. Gegenbauer equation in \(\theta\): eigenvalue

Status: Confirmed.
Location: §9.3, p. 331, display before (9.3.1).
Printed: \(\frac{\partial^2}{\partial\theta^2}C^p_l(\cos\theta)+2p\cot\theta\frac\partial{\partial\theta}
C^p_l(\cos\theta)+l(2p+1)C^p_l(\cos\theta)=0\).
Correct: \(l(2p+l)\) in the last term, as in (9.3.1).
Evidence: For \(p=1\), \(l=2\), \(C^1_2(\cos\theta)=2\cos2\theta+1\): the first two terms give
\(-16\cos2\theta-8\), which is cancelled by \(l(l+2p)C=8(2\cos2\theta+1)\) but not by
\(l(2p+1)C=6(2\cos2\theta+1)\).
Target: [W84.09.3.01].

### W84-E09.3.02. Proof of Corollary 9.3.2: ratio \(C^p_{l+1}(1)/C^p_l(1)\)

Status: Confirmed.
Location: Corollary 9.3.2, proof, p. 332.
Printed: \(C^p_{l+1}(1)=\frac{2p+1}{l+1}C^p_l(1)\).
Correct: \(C^p_{l+1}(1)=\frac{2p+l}{l+1}C^p_l(1)\) (put \(t=1\) in (9.3.4)); this gives the stated
\(C^p_l(1)=\Gamma(2p+l)/(l!\,\Gamma(2p))\).
Evidence: \(p=1\): \(C^1_l(1)=l+1\); \(C^1_3(1)=4=\frac43C^1_2(1)\), while the printed ratio gives 3.
Target: [W84.09.3.02].

### W84-E09.4.01. (9.4.5): missing factor \(1/\sqrt\pi\)

Status: Confirmed.
Location: §9.4, p. 334, (9.4.5).
Printed: \(\omega^l_n(g)=\frac{\Gamma(\frac{n-1}2)}{\Gamma(\frac{n-2}2)}\int_0^\pi(\cos\varphi-i\sin\varphi
\cos\theta)^l\sin^{n-3}\theta\,d\theta\).
Correct: the constant is \(\frac{\Gamma(\frac{n-1}2)}{\sqrt\pi\,\Gamma(\frac{n-2}2)}\) (normalized
measure on \(S^{n-2}\) in the variable \(\theta_{n-2}\)); (9.4.6) as printed is consistent with the
corrected constant.
Evidence: For \(l=0\) the left side is 1 and \(\int_0^\pi\sin^{n-3}\theta\,d\theta=\sqrt\pi\,
\Gamma(\frac{n-2}2)/\Gamma(\frac{n-1}2)\). For \(n=3\), \(l=3\), \(\varphi=0.7\): printed right side
\(-0.050892\), \(P_3(\cos0.7)=-0.028713\); ratio \(\sqrt\pi\).
Target: [W84.09.4.02].

### W84-E09.4.02. (9.4.7)–(9.4.8): normalization of the reproducing formula

Status: Confirmed.
Location: §9.4, p. 334, (9.4.7)–(9.4.8).
Printed: \(\omega^l_n(x)=C^p_l(x_n)\frac{l!\,\Gamma(n-2)}{\Gamma(n+l-2)}\) "is a normalized
\(K\)-invariant vector in \(H^l\)", and \(\omega^l_n(gx_0)=\int_{S^{n-1}}\omega^l_n(g^{-1}x)
\omega^l_n(x)\,dm(x)\).
Correct: \(\omega^l_n\) is normalized by \(\omega^l_n(x_0)=1\) and has \(\|\omega^l_n\|^2_{L^2(m)}=
1/\dim H^l\); the identity is \(\omega^l_n(gx_0)=\dim H^l\int_{S^{n-1}}\omega^l_n(g^{-1}x)
\omega^l_n(x)\,dm(x)\) (or use the unit vector \((\dim H^l)^{1/2}\omega^l_n\)).
Evidence: At \(g=e\) the printed identity reads \(1=\|\omega^l_n\|^2=1/\dim H^l\) by (9.4.10). The
constant \(\frac{l+p}\pi\) in (9.4.9), which is correct (checked numerically for
\((p,l,\varphi)=(\frac12,3,0.7),(1,2,1.1),(\frac32,4,0.4)\)), includes the factor \(\dim H^l\).
Target: [W84.09.4.03].

### W84-E09.4.03. (9.4.12)–(9.4.13): \(\Gamma(2p+1)\) for \(\Gamma(2p+l)\)

Status: Confirmed.
Location: §9.4, p. 336, (9.4.12) and (9.4.13).
Printed: \(a_l=\frac{2^{2p-1}l!(l+p)\Gamma^2(p)}{\pi\Gamma(2p+1)}\int f C^p_l(1-x^2)^{p-\frac12}dx\) and
\(\sum_l\frac{\pi\Gamma(2p+1)}{2^{2p-1}l!(l+p)\Gamma^2(p)}|a_l|^2\).
Correct: \(\Gamma(2p+l)\) in both places (from (9.4.11) and Theorem 9.4.1).
Evidence: For \(f=C^p_l\) the coefficient must be \(a_l=1\); by (9.4.11) the printed formula gives
\(a_l=\Gamma(2p+l)/\Gamma(2p+1)\), e.g. \(3\) for \(p=1\), \(l=2\).
Target: [W84.09.4.05].

### W84-E09.5.01. Derivation of (9.5.2): the \(K\)-orbit and the rotation \(g\)

Status: Confirmed.
Location: §9.5, p. 337, text before (9.5.2).
Printed: for \(x=(0,\dots,\sin\theta,\cos\theta)\) and "\(g\) the rotation group of the coordinates
\((x_1,\dots,x_{n-1})\)", \(kx\) runs through "vectors of the form \((s,\sin\theta)\) where \(s\)
belongs to the sphere \(S^{n-2}\) of radius \(\cos\theta\)", whose last coordinate is
\(\cos\theta\cos\theta_1\).
Correct: \(Kx=\{(s,\cos\theta):s\in\mathbb R^{n-1},\ |s|=\sin\theta\}\), the last coordinate of
\(s\) is \(\sin\theta\cos\theta_1\), and \(g\) is the rotation by \(\varphi\) in the
\((x_{n-1},x_n)\)-plane; then the \(n\)-th coordinate of \(gkx\) is
\(\sin\varphi\sin\theta\cos\theta_1+\cos\varphi\cos\theta\) as printed, and (9.5.2) is correct.
Evidence: \(K\) fixes \(x_n\), so \(kx\) has last coordinate \(\cos\theta\); a rotation in
\((x_1,\dots,x_{n-1})\) belongs to \(K\) and would not change \(\omega^l_n\). (9.5.2) checked
numerically for \((p,l,\varphi,\theta)=(\frac12,3,0.7,0.9),(1,2,1.1,0.9),(\frac32,4,0.4,0.9)\).
Target: [W84.09.5.01].

### W84-E09.5.02. Problem 10(a): range of \(s\) in the even case

Status: Confirmed.
Location: Problem 10(a), p. 342.
Printed: for even \(n=2s+2\), \(s=0,1,\dots\): \(C^p_l(t)=C^s_l(t)=\frac1{2^{s-1}(s-1)!(l+s)}
\frac{d^s}{dt^s}T_{l+s}(t)\).
Correct: \(s=1,2,\dots\) (\((s-1)!\) is undefined at \(s=0\), and \(C^0_l=0\) for \(l\ge1\) by
(9.2.9)).
Evidence: For \(s\ge1\) the formula holds (checked for \((s,l)=(1,2),(2,3),(3,1)\) at \(t=0.3\));
it follows from \(T_k'=kC^1_{k-1}\) and (9.3.2).
Target: [W84.09.5.05].

### W84-E09.5.03. Problem 11(a): argument of the explicit sum

Status: Confirmed.
Location: Problem 11(a), p. 343.
Printed: \(C^\lambda_l(z)=\sum_{n=0}^l\frac{(-1)^n\Gamma(\lambda+n)\Gamma(l+2\lambda+n)}
{n!\,\Gamma(\lambda)\Gamma(2n+2\lambda)(l-n)!}\big(\frac{1-z}2\big)^n\).
Correct: the power is \((2(1-z))^n\); equivalently the coefficient of \(\big(\frac{1-z}2\big)^n\) is
\(\frac{(-1)^n\Gamma(l+2\lambda+n)}{n!\,\Gamma(2\lambda)(\lambda+\frac12)_n(l-n)!}\), matching the
hypergeometric form, which is printed correctly.
Evidence: By the duplication formula \(\frac{\Gamma(\lambda+n)}{\Gamma(\lambda)\Gamma(2\lambda+2n)}=
\frac{4^{-n}}{\Gamma(2\lambda)(\lambda+\frac12)_n}\). For \(\lambda=0.7\), \(l=3\), \(z=0.3\):
\(C^\lambda_3=-0.598332\); the printed sum is \(0.442033\), the corrected sum \(-0.598332\).
Target: [W84.09.5.06].

### W84-E09.5.04. Problem 11: the case \(\lambda=0\)

Status: Confirmed.
Location: Problem 11, p. 343.
Printed: "Let \(\lambda\in\mathbb R\) satisfy \(\lambda>-\frac12\)"; (a) "\(C^\lambda_l\) is a polynomial,
of degree \(l\) precisely"; (c) the norm \(\pi\frac{2^{1-2\lambda}\Gamma(l+2\lambda)}{\Gamma(l+1)
(l+\lambda)(\Gamma(\lambda))^2}\).
Correct: add \(\lambda\ne0\) (for \(\lambda=0\) the generating function is \(1\) and
\(C^0_l=0\) for \(l\ge1\)).
Evidence: \((1-2tz+z^2)^0=1\); the leading coefficient \(2^l(\lambda)_l/l!\) vanishes at \(\lambda=0\).
Target: [W84.09.5.06].

### Conventions and notation (not errata)

- \(p=\frac{n-2}2\) is fixed by \(n\) in §§9.2–9.5, so (9.3.1)–(9.4.13) are derived only for
  \(2p\in\mathbb N\); Problems 10–11 extend them to real parameters.
- (9.4.6) and (9.4.5) use \((\cos\varphi-i\sin\varphi\cos\theta)^l\); replacing \(i\) by \(-i\)
  (\(\theta\mapsto\pi-\theta\)) gives the same integral.
- In (9.1.2), \(\sin\theta_1=r_1/r_2=|x_1|/r_2\) determines \(\theta_1\in[0,2\pi)\) only together
  with the sign of \(x_1\).
- Cross-reference and index slips: p. 328, the Euler sum \(\sum_jx_j\partial_jf_1\) starts at
  \(j=1\) (printed \(j=0\)); p. 332, "by (9.2.1)" refers to (9.2.6); p. 336, "formula (9.1.9)"
  refers to the expansion formula of Chapter 5 (§5.2); Problem 9, hint: (9.3.4) is applied with
  \(p\to p+1\), \(l\to l-1\) (printed "\(l\) by \(l+1\)").

## Chapter 10. Jacobi and Legendre Functions

### W84-E10.1.01. (10.1.4): the subgroups \(\mathfrak t(A)\) and \(\mathfrak t(N)\)

Status: Confirmed.
Location: §10.1, p. 347, (10.1.4).
Printed: \(\mathfrak t(A)=\Big\{\begin{pmatrix}\cosh\frac t2&\sinh\frac t2\\-i\sinh\frac t2&\cosh\frac t2
\end{pmatrix}\Big\}\), \(\mathfrak t(N)=\Big\{\begin{pmatrix}1+\frac t2i&\frac t2\\-\frac t2&1-\frac t2i\end{pmatrix}\Big\}\).
Correct: \(\mathfrak t(a(t))=\begin{pmatrix}\cosh\frac t2&i\sinh\frac t2\\-i\sinh\frac t2&\cosh\frac t2\end{pmatrix}\)
(as printed on p. 367) and \(\mathfrak t(n(t))=\begin{pmatrix}1+\frac t2i&\frac t2\\\frac t2&1-\frac t2i\end{pmatrix}\).
Evidence: From \(a=\frac12(\alpha+\delta+i(\beta-\gamma))\), \(b=\frac12(\beta+\gamma+i(\alpha-\delta))\) (p. 345):
for \(a(t)\), \(b=i\sinh\frac t2\); for \(n(t)\), \(b=\bar b=\frac t2\). The printed matrices have
determinants \(\cosh^2\frac t2+i\sinh^2\frac t2\) and \(1+\frac{t^2}2\), so they are not in \(SU(1,1)\).
Target: [W84.10.1.02].

### W84-E10.1.02. Theorem 10.1.2: lower row of the Euler-angle matrix

Status: Confirmed.
Location: Theorem 10.1.2, p. 348.
Printed: lower row \(\big(\sinh\frac\tau2e^{i\frac{\varphi-\psi}2},\ \cosh\frac\tau2e^{i\frac{\varphi+\psi}2}\big)\).
Correct: \(\big(\sinh\frac\tau2e^{-i\frac{\varphi-\psi}2},\ \cosh\frac\tau2e^{-i\frac{\varphi+\psi}2}\big)\) (the form
\(\begin{pmatrix}a&b\\\bar b&\bar a\end{pmatrix}\); the matrix is printed so on p. 361).
Evidence: The printed matrix has determinant \(\cosh^2\frac\tau2e^{i(\varphi+\psi)}-\sinh^2\frac\tau2e^{i(\varphi-\psi)}
\ne1\) in general; with the correction, \(k(\varphi_1)a(\tau)k(\varphi_2)\) has these entries for
\(\varphi=\varphi_1+\frac\pi2\), \(\psi=\varphi_2-\frac\pi2\), as used in (10.2.18).
Target: [W84.10.1.03].

### W84-E10.1.03. Normalizations of the Haar measure and of \(dm\)

Status: Normalization check.
Location: §10.1, pp. 347–349 (Iwasawa form of \(dg\), (10.1.5)); (10.5.2), p. 369; Problem 2,
p. 378.
Printed: \(dg=\frac{e^t}{4\pi}d\varphi\,dt\,ds\) (\(\varphi\in[-2\pi,2\pi]\)); \(dg=\frac1{8\pi}\sinh\tau\,d\tau\,d\varphi\,d\psi\)
(10.1.5); \(dg=\frac1{4\pi}e^td\theta\,dt\,d\xi\) (10.5.2); Problem 2: \(dm(z)=\frac12\sinh2\tau\,d\tau\,d\theta=
(1-(x^2+y^2))^{-2}dx\,dy\) for \(z=\tanh\tau\,e^{i\theta}\).
Correct: these define different multiples of the Haar measure. For a \(K\)-bi-invariant
\(f(g)=F(\cosh\tau)\) the Iwasawa form and (10.5.2) give \(\int_Gf\,dg=2\pi\int_0^\infty F(\cosh\tau)
\sinh\tau\,d\tau\), while (10.1.5) gives \(\int_0^\infty F(\cosh\tau)\sinh\tau\,d\tau\). The induced measure on
\(D\) is \(dm=\sinh\tau\,d\tau\,d\varphi=4(1-|z|^2)^{-2}dx\,dy\) (\(z=\tanh\frac\tau2e^{i\varphi}\)) for the Iwasawa
form, \(\frac1{2\pi}\sinh\tau\,d\tau\,d\varphi=\frac2\pi(1-|z|^2)^{-2}dx\,dy\) for (10.1.5), and Problem 2 states
\((1-|z|^2)^{-2}dx\,dy\). §10.5 ((10.5.4)–(10.5.9), Theorem 10.5.5) uses the Iwasawa normalization.
Evidence: For \(F(x)=e^{-x}\): by Lemma 10.5.1, \(\iint e^{-\cosh t-\frac12\xi^2e^t}e^tdt\,d\xi=\sqrt{2\pi}
\int e^{-\cosh t}e^{t/2}dt=2\sqrt{2\pi}K_{1/2}(1)=2\pi e^{-1}\), whereas \(\int_0^\infty e^{-\cosh\tau}\sinh\tau\,d\tau=
e^{-1}\). In horocyclic coordinates \((1-|z|^2)^{-2}dx\,dy=\frac14dt\,d\xi\) (checked numerically). The
standard Mehler–Fock normalization (W84-E10.5.02) confirms the factor \(2\pi\) of the Iwasawa form in
(10.5.7).
Target: [W84.10.1.02], [W84.10.1.03], [W84.10.5.01], [W84.10.5.08].

### W84-E10.1.04. Theorem 10.1.2: range of \(\tau\)

Status: Confirmed.
Location: Theorem 10.1.2, p. 348.
Printed: the map is "a continuous bijection onto \(SU(1,1)-\{\mathcal K\}\)" on
\([0,2\pi[\times]-\infty,\infty[\times[-2\pi,2\pi[\).
Correct: the domain is \([0,2\pi)\times(0,\infty)\times[-2\pi,2\pi)\), as stated in the text before the
theorem ("restricting the domain to \(0\le\varphi<2\pi\) and \(\tau>0\)").
Evidence: \((\varphi,-\tau,\psi)\) and \((\varphi\pm\pi,\tau,\psi\mp\pi)\) give the same matrix, since the change
multiplies \(e^{i(\varphi-\psi)/2}\) by \(-1\) and fixes \(\varphi+\psi\); \(\tau=0\) gives \(\mathcal K\).
Target: [W84.10.1.03].

### W84-E10.4.01. Spherical representations: condition on \(l\) and the index of \(\mathfrak P\)

Status: Confirmed.
Location: §10.4, p. 365, after Theorem 10.4.2.
Printed: "spherical representations are obtained for \(\sigma=(0,l)\) where \(l\) is an odd integer"
and \(u^\sigma_{00}(a)=\mathfrak P^{\frac{-l+1}2}_{00}(\cosh\tau)=\mathfrak P_{-\frac{l+1}2}(\cosh\tau)\).
Correct: irreducible spherical representations are obtained for \(\sigma=(0,l)\) with \(l\) not an odd
integer (\(\sigma\in\Omega\)), and \(u^\sigma_{00}(a)=\mathfrak P^{-\frac{l+1}2}_{00}(\cosh\tau)=\mathfrak P^{\frac{l-1}2}_{00}
(\cosh\tau)\).
Evidence: By Theorem 10.4.2 and Problem 19, \(U^{(0,l)}\) is reducible exactly for odd \(l\); every
\(U^{(0,l)}\) contains the \(K\)-fixed vector \(e^0_0\). By (10.2.21) \(u_{00}=\mathfrak P_{-\frac12(l+1)}\), and by
(10.3.7) \(\mathfrak P^\zeta_{00}=\mathfrak P^{-\zeta-1}_{00}\), which gives \(\frac{l-1}2\), not \(\frac{1-l}2\); e.g. for
\(l=0\), \(\mathfrak P_{-1/2}\ne\mathfrak P_{1/2}\) (at \(\tau=1\): \(0.940862\) and \(1.188678\)).
Target: [W84.10.4.02].

### W84-E10.4.02. Relation between \(\zeta\) and \(\sigma\)

Status: Confirmed.
Location: §10.4, p. 367, after (10.4.9).
Printed: "\(\zeta=-l+\frac12\) (see (10.2.15))".
Correct: \(\zeta=-\frac12(l+1)\), as in (10.2.15) and (10.2.19).
Evidence: (10.2.15): \(u^\sigma_{mn}(a)=(-1)^{m-n}\mathfrak P^{-\frac12(l+1)}_{m+\frac\varepsilon2,n+\frac\varepsilon2}\).
Target: [W84.10.4.03].

### W84-E10.5.01. Derivative of the Abel transform: sign

Status: Confirmed.
Location: §10.5, p. 371 (and the second line of the computation on p. 372).
Printed: \(F_f'(\cosh\tau)=\frac i{2\pi\sinh\tau}\int_{-\infty}^\infty\hat f(\nu)\nu e^{-i\nu\tau}d\nu\).
Correct: \(F_f'(\cosh\tau)=\frac{-i}{2\pi\sinh\tau}\int_{-\infty}^\infty\hat f(\nu)\nu e^{-i\nu\tau}d\nu\); with this sign the
computation on p. 372 gives (10.5.7), using
\(\mathrm{p.v.}\int_{-\infty}^\infty\frac{e^{-i\nu\tau}}{\sinh(\tau/2)}d\tau=-2\pi i\tanh(\pi\nu)\).
Evidence: Differentiate \(F_f(\cosh\tau)=\frac1{2\pi}\int\hat f(\nu)e^{-i\nu\tau}d\nu\) in \(\tau\):
\(\sinh\tau\,F_f'(\cosh\tau)=\frac1{2\pi}\int\hat f(\nu)(-i\nu)e^{-i\nu\tau}d\nu\). With the printed sign the chain
on p. 372 gives \(-\frac1{2\pi}\int_0^\infty\hat f\nu\tanh(\pi\nu)d\nu\). (10.5.7) itself is correct.
Target: [W84.10.5.03].

### W84-E10.5.02. Mehler–Fock transform: constants

Status: Confirmed.
Location: §10.5, p. 373, display before (10.5.11), (10.5.12); p. 374, (10.5.13).
Printed: \(\hat f(\nu)=\pi\int_0^\infty f(\tanh\frac\tau2)\sinh\tau\,\mathfrak P_{i\nu-\frac12}(\cosh\tau)d\tau\);
\(F(\tau)=\frac1{2\pi^2}\int_0^\infty\tilde F(\nu)\mathfrak P_{-\frac12+i\nu}(\cosh\tau)\nu\tanh(\pi\nu)d\nu\);
\(\int_0^\infty|F|^2\sinh\tau\,d\tau=\frac1{2\pi^2}\int_0^\infty|\tilde F|^2\nu\tanh(\pi\nu)d\nu\).
Correct: \(\hat f(\nu)=2\pi\int_0^\infty\cdots\) (normalization (10.5.2) used in (10.5.4)–(10.5.9)); the
constant in (10.5.12) and (10.5.13) is \(1\):
\(F(\tau)=\int_0^\infty\tilde F(\nu)\mathfrak P_{-\frac12+i\nu}(\cosh\tau)\nu\tanh(\pi\nu)d\nu\),
\(\int_0^\infty|F|^2\sinh\tau\,d\tau=\int_0^\infty|\tilde F|^2\nu\tanh(\pi\nu)d\nu\).
Evidence: (10.5.11)–(10.5.13) involve only \(F\) and \(\tilde F\), so the constants are independent of the
Haar normalization. For \(F(\tau)=e^{-\cosh\tau}\), \(\tilde F(\nu)=\sqrt{2/\pi}\,K_{i\nu}(1)\) (checked at
\(\nu=0.7\)); numerically \(\int_0^\infty\tilde F\nu\tanh(\pi\nu)d\nu=0.367879=F(0)\) and
\(\int_0^\infty\tilde F^2\nu\tanh(\pi\nu)d\nu=0.067668=\int_0^\infty e^{-2\cosh\tau}\sinh\tau\,d\tau\). The printed
\(\pi\) and \(\frac1{2\pi^2}\) are also mutually inconsistent with (10.5.9).
Target: [W84.10.5.04].

### W84-E10.5.03. (10.5.14): exponent of \(\delta(h(g^{-1}k))\)

Status: Confirmed.
Location: §10.5, p. 375, (10.5.14).
Printed: \(f(g\cdot0)=\frac1{2\pi}\int_0^\infty\int_K\delta^{i\nu-\frac12}(h(g^{-1}k))\int_Gf(y\cdot0)
\delta^{-i\nu+\frac12}(h(y^{-1}k))dm(y)\,\nu\tanh(\pi\nu)d\nu\).
Correct: \(\delta^{i\nu+\frac12}(h(g^{-1}k))\), as in the formula for \(\omega_\nu(g^{-1}y\cdot0)\) printed just
above.
Evidence: The display before (10.5.14) gives \(\omega_\nu(g^{-1}y\cdot0)=\int_K\delta^{-i\nu+\frac12}(h(y^{-1}k))
\delta^{i\nu+\frac12}(h(g^{-1}k))dk\), from (10.3.3). Since \(\delta(h(g^{-1}k))\) is the Poisson kernel \(P(g\cdot0,k)\) and
\(\int_KP(z,k)^sdk=\mathfrak P_{-s}(\cosh\tau)\) for \(z=\tanh\frac\tau2e^{i\varphi}\), at \(y=e\) the corrected kernel gives
\(\int_K\delta^{i\nu+\frac12}(h(g^{-1}k))dk=\mathfrak P_{-\frac12-i\nu}=\omega_\nu(g)\), the printed one
\(\mathfrak P_{\frac12-i\nu}=\mathfrak P_{-\frac32+i\nu}\ne\omega_\nu(g)\). The inversion kernel \(e_{2i\nu+1}\) of (10.5.17)
corresponds to the corrected exponent.
Target: [W84.10.5.05].

### W84-E10.5.04. (10.5.15): definition of \(e_\lambda\)

Status: Confirmed.
Location: §10.5, p. 375, (10.5.15).
Printed: \(e_\lambda(gK,kM):=\delta^{-\frac12\lambda}(h(g^{-1}k))\).
Correct: \(e_\lambda(gK,kM):=\delta^{\frac12\lambda}(h(g^{-1}k))\).
Evidence: By the Remark after Proposition 10.3.1, \(\delta(h(g^{-1}k))=e_{-1}(g,k)^{-2}\), with \(e_{-1}\) from
(10.2.10); so the printed definition gives \(e_{-1}=\delta^{1/2}=e_{-1}^{-1}\). The corrected definition agrees
with (10.5.16), with \(e_\lambda=(\cosh\tau+\sinh\tau\sin(\theta-\varphi))^{-\lambda/2}\) (p. 375), with the kernels
\(e_{1-2i\nu}=\delta^{\frac12-i\nu}\) and \(e_{1+2i\nu}=\delta^{\frac12+i\nu}\) of Theorem 10.5.5 obtained from
(10.5.14), and with \(\Delta e_\lambda=\lambda(\lambda-2)e_\lambda\) (p. 377): \(\delta(h(g^{-1}k))\) is the Poisson
kernel \(P\), and \(\Delta P^s=4s(s-1)P^s\) for the metric (10.1.6), \(s=\lambda/2\).
Target: [W84.10.5.06], [W84.10.5.07].

### W84-E10.5.05. (10.5.16): denominator

Status: Confirmed.
Location: §10.5, p. 375, (10.5.16).
Printed: \(e_{-1}(gK,kM)=\big(\frac{1-2r\cos(\varphi-\theta)+r^2}{1-r}\big)^{1/2}\).
Correct: denominator \(1-r^2\), as on p. 355.
Evidence: With \(r=\tanh\frac\tau2\), \(\cosh\tau=\frac{1+r^2}{1-r^2}\), \(\sinh\tau=\frac{2r}{1-r^2}\), so
\(\cosh\tau+\sinh\tau\sin(\theta-\varphi)=\frac{1+r^2+2r\sin(\theta-\varphi)}{1-r^2}\).
Target: [W84.10.5.06].

### W84-E10.5.06. Problem 8: coordinates and metric for the Laplace–Beltrami operator

Status: Normalization check.
Location: Problem 8, p. 382.
Printed: "in terms of the polar coordinates \(z=\tanh\tau\,e^{i\theta}\) on \(D\),
\(\Delta=\frac{\partial^2}{\partial\tau^2}+\coth\tau\frac\partial{\partial\tau}+\frac1{\sinh^2\tau}\frac{\partial^2}{\partial\theta^2}\)",
\(\Delta\mathfrak P_{i\nu-\frac12}=-(\frac14+\nu^2)\mathfrak P_{i\nu-\frac12}\), \((\Delta f,f)\le-\frac14\|f\|^2\).
Correct: the printed operator is the Laplace–Beltrami operator for \(z=\tanh\frac\tau2e^{i\theta}\) and the
metric \(4(dx^2+dy^2)/(1-|z|^2)^2\); for the metric (10.1.6) it is \(4(\partial_\tau^2+\coth\tau\,\partial_\tau+
\sinh^{-2}\tau\,\partial_\theta^2)\) (same \(z\)), with eigenvalue \(-(1+4\nu^2)\) and bound \(-\|f\|^2\).
Evidence: With \(z=\tanh\frac\tau2e^{i\theta}\), (10.1.6) becomes \(\frac14(d\tau^2+\sinh^2\tau\,d\theta^2)\); with
\(z=\tanh\tau\,e^{i\theta}\) it becomes \(d\tau^2+\frac14\sinh^22\tau\,d\theta^2\). \(\mathfrak P_\zeta\) satisfies
\(\partial_\tau^2u+\coth\tau\,\partial_\tau u=\zeta(\zeta+1)u\) in the variable of \(\cosh\tau\) (Problem 9(a)).
Target: [W84.10.5.10].

### W84-E10.5.07. Problem 14(c): order of the indices

Status: Confirmed.
Location: Problem 14(c), p. 386.
Printed: \(\sum_k\mathfrak P^{-\frac12+i\nu}_{mk}(\cosh\tau)\mathfrak P^{-\frac12-i\nu}_{kn}(\cosh\tau)=\delta_{mn}\).
Correct: \(\sum_k\mathfrak P^{-\frac12+i\nu}_{mk}(\cosh\tau)\mathfrak P^{-\frac12-i\nu}_{nk}(\cosh\tau)=\delta_{mn}\)
(equivalently \(\sum_k(-1)^{n-k}\mathfrak P^\zeta_{mk}\mathfrak P^\zeta_{kn}=\delta_{mn}\), Problem 14(b) at \(\tau_1=\tau_2\)).
Evidence: (10.3.7) gives \(\mathfrak P^\zeta_{kn}=(-1)^{n-k}\mathfrak P^{-\zeta-1}_{nk}\); \(\mathfrak P^\zeta_{mn}\ne\mathfrak P^\zeta_{nm}\)
in general (\(\zeta=0.37\), \(\tau=0.8\): \(\mathfrak P_{12}=0.80389\), \(\mathfrak P_{21}=-0.21369\)). For \(\nu=0.6\),
\(\tau=0.8\), \((m,n)=(1,1)\) the printed sum is \(0.44875-0.04577i\); the corrected sum is \(1\), and
\(0\) for \((m,n)=(1,2),(0,1)\).
Target: [W84.10.5.13].

### Conventions and notation (not errata)

- The \(L^2(K)\) inner product of §§10.2–10.3 is conjugate-linear in the first argument,
  \((e_m|U e_n)=\frac1{4\pi}\int\bar e_mUe_n\), opposite to the header convention.
- \(\mathfrak P^m_\zeta\) of (10.2.16) is the type-3 Legendre function without the factor \((-1)^m\);
  \(\mathfrak P^\zeta_{mn}\) differs from Vilenkin's \(\mathfrak P^l_{mn}\) by the indexing and the substitution
  \(\theta\to-\theta\).
- Three normalizations of Haar measure occur (see [W84-E10.1.03]); the inversion and Plancherel
  formulas of §10.5 are stated for the Iwasawa normalization.
- p. 356: "\(\cos\tau-\sinh\tau\cos\theta\)" is \(\cosh\tau-\sinh\tau\cos\theta\); p. 359: "formula (10.7.5)
  in this chapter" refers to (1.7.5); p. 362: the "sphere with centre \(g_1\cdot0\) and radius
  \(\cosh\tau_2\)" has radius \(\frac{\tau_2}2\) in the metric (10.1.6); p. 365: "formula (10.3.6)" refers to
  (10.3.7)/(10.3.9); p. 367: "formula (10.4.12)" refers to (8.4.12); (10.5.17): \(\tilde f(\lambda,b)\) is
  \(\tilde f(\nu,b)\); Problem 9(e): "formulas (10.3.7)" refers to (10.3.10); Problems 14–15: "addition
  formula (10.3.8)" refers to (10.3.11) and "mean value formula (10.3.10)" to (10.3.13); Problem 20(a):
  the printed "or \(l\ge0\) or" reads "or".

## Chapter 11. Harmonic Analysis on the Lobatschevsky Space

### W84-E11.2.01. Second polar coordinate of the hyperboloid

Status: Confirmed.
Location: §11.2, p. 397, Proposition 11.2.1.
Printed: \(p=(\cosh t,\ \sinh t\sin\theta\cos\varphi,\ \sinh t\sin\theta\cos\varphi,\ \sinh t\cos\theta)\).
Correct: the third coordinate is \(\sinh t\sin\theta\sin\varphi\).
Evidence: with two equal coordinates the image lies in the hyperplane \(p_1=p_2\) and the map is
not onto \(\mathcal H\); e.g. \(p=(\cosh1,\sinh1,0,0)\) (\(t=1\), \(\theta=\frac\pi2\), \(\varphi=0\) in
the corrected form) is not attained. The corrected point \(k\,a(t)w\) satisfies
\(p_0^2-p_1^2-p_2^2-p_3^2=\cosh^2t-\sinh^2t=1\).
Target: [W84.11.2.03].

### W84-E11.2.02. The three forms of the invariant measure on \(\mathcal H\) disagree

Status: Confirmed.
Location: §11.2, p. 400, (11.2.13).
Printed: \(\int_{\mathcal H}f\,dm=\frac1{4\pi}\int f\sinh^2t\sin\theta\,d\varphi\,d\theta\,dt=\frac i2
\int f(a(t)n(\beta)w)\,d\beta\wedge d\bar\beta\,dt\), with \(dm=dp_1dp_2dp_3/p_0\).
Correct: with the polar normalization used in §§11.3–11.6,
\(dm=\frac{dp_1dp_2dp_3}{4\pi p_0}=\frac1{4\pi}\sinh^2t\sin\theta\,dt\,d\theta\,d\varphi
=\frac i{8\pi}\,d\beta\wedge d\bar\beta\,dt\).
Evidence: In horospherical coordinates \(p_0+p_3=e^{-t}\) and \(dp_1dp_2dp_3/p_0=d^2\beta\,dt\)
(\(d^2\beta\) Lebesgue measure on \(\mathbb C\)), and \(\frac i2d\beta\wedge d\bar\beta=d^2\beta\). For
\(f=e^{-p_0}\): the polar form gives \(\int_0^\infty e^{-\cosh t}\sinh^2t\,dt=K_1(1)=0.60191\), while the
printed horospherical form and \(\int e^{-p_0}dp/p_0\) give \(4\pi K_1(1)=7.5639\). The Plancherel
constant \(2/\pi\) of Theorems 11.3.1 and 11.4.1 holds only for the polar-normalized measure
(checked with \(f=e^{-p_0}\)-type radial functions).
Target: [W84.11.2.07], [W84.11.6.01], [W84.11.6.02].

### W84-E11.3.01. Missing factors \(i\) in the polar form of the spherical transform

Status: Confirmed.
Location: §11.3, p. 401, (11.3.3) and the following unnumbered inversion formula.
Printed: \(\hat f(\nu)=\frac1\nu\int_0^\infty\sinh t\,f\sin\nu t\,dt=\frac1{2\nu}\int_{-\infty}^\infty
\sinh t\,f\,e^{i\nu t}dt\); \(f\sinh t=\frac1\pi\int\nu\hat f(\nu)e^{-i\nu t}d\nu\).
Correct: \(\frac1{2i\nu}\int_{-\infty}^\infty\sinh t\,f\,e^{i\nu t}dt\) and
\(f\sinh t=\frac i\pi\int_{-\infty}^\infty\nu\hat f(\nu)e^{-i\nu t}d\nu\).
Evidence: for odd \(g\), \(\int_{-\infty}^\infty g(t)e^{i\nu t}dt=2i\int_0^\infty g(t)\sin\nu t\,dt\). The
two slips cancel, so (11.3.4)–(11.3.6) are correct.
Target: [W84.11.3.02], [W84.11.3.03].

### W84-E11.4.01. Plane wave versus modular function: \(s_1\) and \(s_0\)

Status: Confirmed.
Location: §11.4, p. 403, (11.4.5).
Printed: \(e_\mu(p,s_1)=(\cosh t-\sinh t\cos\theta)^{-\mu}=\delta(h(g^{-1}))^{\mu/2}\) for \(p=gw\).
Correct: the first equality holds with \(s_1=(1,0,0,1)\); the second holds with \(s_0=(1,0,0,-1)\):
\(e_\mu(gw,s_0)=\delta(h(g^{-1}))^{\mu/2}\).
Evidence: for \(g=a(t)\), \(p=a(t)w=(\cosh t,0,0,-\sinh t)\): \([p|s_1]=e^t\), so \(e_\mu(p,s_1)=e^{-\mu
t}\), whereas \(h(a(-t))=a(-t)\) has \(\delta=|e^{-t/2}|^{-4}=e^{2t}\), so \(\delta^{\mu/2}=e^{\mu t}\);
\([p|s_0]=e^{-t}\) gives \(e_\mu(p,s_0)=e^{\mu t}\). The identity
\(S_g(g,ks_0)=\delta(h(gk))=e_2(g^{-1}w,ks_0)\) on p. 404 uses \(s_0\).
Target: [W84.11.4.02].

### W84-E11.4.02. Index in the normalization of \(h_{lm}\)

Status: Confirmed.
Location: §11.4, p. 407, (11.4.17).
Printed: \(\sqrt{(l-k)!/(l+k)!}\) in \(h_{lm}\).
Correct: \(\sqrt{(l-m)!/(l+m)!}\); no index \(k\) occurs in (11.4.17).
Evidence: with \(m\) the factor makes \(\frac12\int_0^\pi|h_{lm}|^2\sin\theta\,d\theta\cdot\frac1{2\pi}
\int d\varphi=1\) (standard normalization of \(P^m_l\)), as required for an orthonormal basis of
\(L^2(B,ds)\).
Target: [W84.11.4.08].

### W84-E11.4.03. Constant and conjugation in the expansion (11.4.14)

Status: Confirmed.
Location: §11.4, p. 406, (11.4.14).
Printed: \(f(p)=\frac1{\pi^2}\sum_j\int\nu^2\tilde f_{\nu,j}\Phi_{\nu,j}(p)\,d\nu\).
Correct: \(f(p)=\frac2\pi\sum_j\int_0^\infty\nu^2\tilde f_{\nu,j}\overline{\Phi_{\nu,j}(p)}\,d\nu\).
Evidence: substituting \(\tilde f(\nu,s)=\sum_j\tilde f_{\nu,j}h_j(s)\) into (11.4.12) gives
\(\int_Be_{-i\nu+1}(p,s)h_j(s)ds=\overline{\Phi_{\nu,j}(p)}\) and keeps the constant \(2/\pi\); the
source's own (11.4.24) has \(2/\pi\) and \(\bar\Phi\).
Target: [W84.11.4.08].

### W84-E11.4.04. Radial factor of \(\Phi_{\nu,(l,0)}\): sign and factorial

Status: Confirmed.
Location: §11.4, pp. 407–410, displays before (11.4.18), (11.4.18) first line, (11.4.19), (11.4.20),
(11.4.22).
Printed: the displays before (11.4.18) and the first line of (11.4.18) carry a factor
\((-1)^l\) relative to the second line; (11.4.19) has \(\sqrt\pi\,2^{(2l+1)/2}(2l+1)!\) on the right;
(11.4.20) and (11.4.22) follow from (11.4.19).
Correct: two sign slips cancel, and the second line of (11.4.18) is correct. In (11.4.19) the factor
\((2l+1)!\) should be \(l!\). Consequently
\(\Phi_{\nu,(l,0)}(a(t)w)=\frac{\Gamma(-i\nu)}{\Gamma(-i\nu-l)}\sqrt{\frac{\pi(2l+1)}2}\,
(\sinh t)^{-1/2}\mathfrak P^{-l-1/2}_{-i\nu-1/2}(\cosh t)\), and (11.4.20), (11.4.22) as printed carry a
spurious factor \((2l+1)!/l!\).
Evidence: comparing the printed (11.4.19) with the direct integral
\(\frac{\sqrt{2l+1}}2\int_{-1}^1P_l(y)(\cosh t-y\sinh t)^{-i\nu-1}dy\) at \(\nu=0.7\), \(t=0.9\): the
ratio printed/true is \(6\), \(60\), \(840\) for \(l=1,2,3\), i.e. \((2l+1)!/l!\); analytically the
corrected form follows from the Laplace integral for \(\mathfrak P^\mu_\lambda\) (Chapter 10,
Problem 13(b)). For \(l=0\) both give \(\sin\nu t/(\nu\sinh t)\).
Target: [W84.11.4.09], [W84.11.4.10].

### W84-E11.5.01. Angular term of the Laplace–Beltrami operator

Status: Confirmed.
Location: §11.5, p. 411, (11.5.3).
Printed: \(\dots+\frac1{\sin^2\theta\sin^2\varphi}\frac{\partial^2}{\partial\varphi^2}\).
Correct: \(\frac1{\sin^2\theta}\frac{\partial^2}{\partial\varphi^2}\).
Evidence: \(f=\sin\theta\cos\varphi\) (the restriction of \(p_1/\sinh t\)) must satisfy
\(\Delta_{S^2}f=-2f\), which holds with \(\frac1{\sin^2\theta}\partial_\varphi^2\). With the printed term,
at \(\theta=\frac\pi2\), \(\varphi=\frac\pi4\) the angular part gives \(-0.7071-1.4142=-2.1213=-3f\)
(\(f=0.7071\)) instead of \(-2f=-1.4142\).
Target: [W84.11.5.01].

### W84-E11.6.01. Horospherical evaluation needs \(s_0\)

Status: Confirmed.
Location: §11.6, p. 414, derivation of (11.6.2); also (11.6.5), p. 416.
Printed: \(\tilde f(\nu,k\cdot s_1)=\int\int f(ka(t)n(\beta)w)[a(t)n(\beta)w|s_1]^{-i\nu-1}\dots=
\int e^{(i\nu+1)t}\hat f(ka(t)\xi_0)dt\).
Correct: the step requires the base isotropic vector \(s_0=(1,0,0,-1)\), for which
\([a(t)n(\beta)w|s_0]=e^{-t}\) is independent of \(\beta\); the formula reads
\(\tilde f(\nu,k\cdot s_0)=\int e^{(i\nu+1)t}\hat f(ka(t)\xi_0)dt\).
Evidence: \(a(t)n(\beta)w=(\cosh t+\frac12|\beta|^2e^{-t},\dots)\) gives
\([a(t)n(\beta)w|s_1]=(1+|\beta|^2)e^t\), which depends on \(\beta\), while
\([a(t)n(\beta)w|s_0]=e^{-t}\).
Target: [W84.11.6.01], [W84.11.6.02].

### W84-E11.7.01. Commutator of two boosts

Status: Confirmed.
Location: Problems, p. 421, Problem 5(b).
Printed: \([H_j,H_k]=-\sum_lc^l_{jk}H_l\).
Correct: \([H_j,H_k]=-\sum_lc^l_{jk}R_l\).
Evidence: with the matrices of Problem 5(a), \(H_1=E_{01}+E_{10}\), \(H_2=E_{02}+E_{20}\) give
\([H_1,H_2]=E_{12}-E_{21}=-R_3\) (a rotation in the \((p_1,p_2)\)-plane), not a multiple of \(H_3\);
the other two printed relations check.
Target: [W84.11.7.06].

### Conventions and notation (not errata)

- \(dm\) is normalized by the polar form \(\frac1{4\pi}\sinh^2t\sin\theta\,dt\,d\theta\,d\varphi\)
  throughout §§11.3–11.6 (see W84-E11.2.02).
- (11.2.14) writes \(d\varphi\,d\theta\,d\psi\) for the normalized Haar measure \(dk\) of \(SU(2)\)
  without the Euler-angle density \(\sin\theta\); Problem 6(b) recovers the correct form.
- Theorem 11.7.1 is stated for \(\nu\notin i\mathbb Z\); the proof's obstruction factor
  \(\eta(\nu,l)\) vanishes only for \(\nu\in i\mathbb N\).
- An intermediate display in the proof of Theorem 11.5.1 (the step "\(D_rf+De=0\)") has a sign
  slip without effect on the result.
- p. 416: "Laplace–Beltrani" is "Laplace–Beltrami".

## Chapter 12. The Laguerre Polynomials

### W84-E12.1.01. \(\bar w\) for \(w\) in the matrix elements (12.1.13)

Status: Confirmed.
Location: §12.1, pp. 428–429, (12.1.13) (and its symbolic form for \(\lambda=1\)).
Printed: \(u^\lambda_{nm}(g(w,0))=(n!/m!)^{1/2}\exp(-\frac12\lambda(w|w))\,\bar w^{m-n}\lambda^{\frac{m-n}2}
L^{m-n}_n(\lambda(w|w))\).
Correct: \(u^\lambda_{nm}(g(w,0))=(e_n|\mathcal U^\lambda_ge_m)=(n!/m!)^{1/2}\exp(-\frac12\lambda|w|^2)
\,w^{m-n}\lambda^{\frac{m-n}2}L^{m-n}_n(\lambda|w|^2)\).
Evidence: \(\lambda=1\), \(n=0\), \(m=1\): \((\mathcal U_ge_1)(z)=e^{-|w|^2/2-\bar wz}(z+w)\), whose value at
\(z=0\) (the coefficient of \(e_0=1\), (12.1.10)) is \(e^{-|w|^2/2}w\), not \(e^{-|w|^2/2}\bar w\). The
derivation (12.1.11) with \(s=\bar wz\) also gives \(w^{m-n}\), and the addition formula (12.2.4)
derived from (12.1.13) carries \((r_2e^{i\varphi})^{m-k}\), \((re^{i\psi})^{m-n}\), consistent with
\(w^{m-n}\). The printed form is the complex conjugate of the matrix element.
Target: [W84.12.1.05], [W84.12.1.07].

### W84-E12.2.01. Exponent in the integral representation

Status: Confirmed.
Location: §12.2, p. 430, (12.2.2).
Printed: \(\exp(-\lambda(z+|z|)^2)\).
Correct: \(\exp(-\lambda(z+|z|^2))\), as in the line before (12.2.2).
Evidence: the line before (12.2.2) has \(\exp(-\lambda(z+|z|^2))\) from multiplying (12.2.1) by
\(e^{-\lambda|z|^2}\); with the corrected exponent, \(k=0\), \(m=0\), \(\lambda=1\) gives
\(\frac1\pi\int e^{-z-|z|^2}dz=1=L^0_0\) (the term \(e^{-z}\) averages to \(1\) over circles).
Target: [W84.12.2.02].

### W84-E12.3.01. Differential–difference relation (12.3.7)

Status: Confirmed.
Location: §12.3, p. 431, (12.3.7).
Printed: \(t\frac{dF_{nm}}{dt}+\frac{m-n}tF_{nm}=\sqrt mF_{n,m-1}+\sqrt{m+1}F_{n,m+1}\).
Correct: \(t\,F_{nm}+\frac{m-n}tF_{nm}=\sqrt mF_{n,m-1}+\sqrt{m+1}F_{n,m+1}\) (no derivative).
Evidence: \(F_{nm}(t)=(n!/m!)^{1/2}e^{-t^2/2}t^{m-n}L^{m-n}_n(t^2)\); for \(n=0\), \(m=1\):
\(F_{00}=e^{-t^2/2}\), \(F_{01}=te^{-t^2/2}\), \(F_{02}=\frac{t^2}{\sqrt2}e^{-t^2/2}\); the right side is
\((1+t^2)e^{-t^2/2}\), the corrected left side \(tF_{01}+F_{01}/t=(t^2+1)e^{-t^2/2}\), the printed left side
\(tF_{01}'+F_{01}/t=(1+t-t^3)e^{-t^2/2}\). The corrected relation was verified symbolically for
\(n=0,1,2\), \(m=1,2,3\).
Target: [W84.12.3.03].

### W84-E12.3.02. Lower index in the derivative formula

Status: Confirmed.
Location: §12.3, p. 432, (12.3.11), first identity.
Printed: \(\frac d{dx}L^k_n(x)=-L^{k+1}_n(x)\).
Correct: \(\frac d{dx}L^k_n(x)=-L^{k+1}_{n-1}(x)\).
Evidence: \(n=1\), \(k=1\): \(L^1_1=2-x\), derivative \(-1=-L^2_0\), whereas \(-L^2_1=x-3\). The relation
\(L^k_n=L^{k+1}_n-L^{k+1}_{n-1}\) printed below is consistent with the corrected form.
Target: [W84.12.3.06].

### W84-E12.4.01. Sign of \(\alpha^2\) in the generating function (12.4.5)

Status: Confirmed.
Location: §12.4, p. 435, (12.4.5).
Printed: \(\pi^{-1/4}\exp(\alpha^2-2z\alpha-\frac12z^2)=\sum_n\frac{2^{n/2}}{(n!)^{1/2}}\alpha^n\psi_n(z)\).
Correct: \(\pi^{-1/4}\exp(-\alpha^2-2z\alpha-\frac12z^2)\).
Evidence: (12.4.4) with \(\psi=\psi_0\) and \(\alpha=t/\sqrt2\) gives
\(\exp(-\frac14t^2-\frac t{\sqrt2}z)\pi^{-1/4}e^{-(z+t/\sqrt2)^2/2}=\pi^{-1/4}\exp(-\alpha^2-2z\alpha-
\frac12z^2)\). At \(z=0\) the coefficient of \(\alpha^2\) on the right is
\(\frac2{\sqrt2}\psi_2(0)=-\pi^{-1/4}\) (from (12.4.7), \(H_2(0)=-2\)); the printed left side gives
\(+\pi^{-1/4}\). The corrected form is consistent with (12.4.6)–(12.4.7).
Target: [W84.12.4.04].

### W84-E12.6.01. Norm of the Laguerre polynomials

Status: Confirmed.
Location: §12.6, p. 441, last display.
Printed: \(\int_0^\infty e^{-r}r^kL^k_m(r)L^k_n(r)\,dr=\frac{n!}{(n+k)!}\delta_{nm}\).
Correct: \(\frac{(n+k)!}{n!}\delta_{nm}\).
Evidence: \(n=m=1\), \(k=1\): \(\int_0^\infty e^{-r}r(2-r)^2dr=2\), while the printed value is
\(\frac12\). The preceding derivation also drops the square on \(L^k_n\) in
\(\int e^{-r}r^k(L^k_n(r))^2dr\) and inverts \(d_T^{-1}\cdot\frac{(n+k)!}{n!}\); with \(d_T=1\) the
corrected value follows.
Target: [W84.12.6.03].

### W84-E12.6.02. Ratio \(x/y\) in Problem 5

Status: Confirmed.
Location: Problems, p. 442, Problem 5, first identity.
Printed: \(\sum_l\big(\frac xy\big)^lL^{m-l}_l(x^2)L^{l-n}_n(y^2)=\big(1+\frac yx\big)^m\big(1+\frac xy\big)^{-n}
e^{-xy}L^{m-n}_n((x+y)^2)\).
Correct: \(\big(\frac yx\big)^l\) on the left.
Evidence: \(m=n=0\): the left side is \(\sum_l\frac{(-x^2)^l}{l!}(x/y)^l=e^{-x^3/y}\) (printed) versus
\(e^{-xy}\) on the right; with \((y/x)^l\) it is \(e^{-xy}\). For \(m=3\), \(n=2\), \(x=0.7\), \(y=1.3\) the
corrected sum and the right side both equal \(-3.966565\); the printed sum gives \(0.628511\).
Target: [W84.12.6.06].

### W84-E12.6.03. Factorial in the explicit sum of Problem 6

Status: Confirmed.
Location: Problems, p. 442, Problem 6.
Printed: \(L^l_n(x)=\sum_{k=0}^n\frac{(n+l)!}{(k+l+1)!}\frac{(-x)^k}{k!(n-k)!}\).
Correct: \(\frac{(n+l)!}{(k+l)!}\).
Evidence: \(n=1\), \(l=0\): the printed sum gives \(1-\frac x2\), but \(L^0_1(x)=1-x\).
Target: [W84.12.6.07].

### Conventions and notation (not errata)

- \((z|w)=\sum_j\bar z_jw_j\) is conjugate-linear in the first argument, as in the rest of the
  book; matrix elements are \(u_{nm}=(e_n|\mathcal U e_m)\).
- (12.4.3) is stated for \(n=1,2,3,\dots\); the recursion starts at \(n=0\).
- (12.3.6) has a stray letter "G" before \(F_{n,m+1}\).
- p. 426: "inequality (11.1.7)" means (12.1.7). §12.6, p. 439: the raising operator is defined
  by (12.3.8) (printed "(12.3.6)") and the recurrences are (12.3.9).
- Problem 7: the exponent is \(-\frac{xz}{1-z}\); the typesetting suggests \(x^z\).
- Problem 10: \(e^x=e^{1/4}\sum H_n(x)/(2^nn!)\) is correct as printed.

## Chapter 13. The Hypergeometric Equation

### W84-E13.1.01. Denominator of the Papperitz coefficient \(q\)

Status: Confirmed.
Location: §13.1, p. 451.
Printed: \(\dots\frac1{(z-\zeta)(z-\eta)(z-\zeta)}\).
Correct: \(\frac1{(z-\xi)(z-\eta)(z-\zeta)}\).
Evidence: the indicial equation at \(z=\xi\) requires \(\lim(z-\xi)^2q(z)=\alpha\alpha'\); with the
printed denominator \((z-\xi)^2q\) vanishes at \(\xi\) and has a pole of order two at \(\zeta\).
Target: [W84.13.1.07].

### W84-E13.1.02. Exponent \(\gamma'\) of the hypergeometric equation at \(z=1\)

Status: Confirmed.
Location: §13.1, p. 452, parameters before (13.1.10).
Printed: \(\gamma'=c-a-1\).
Correct: \(\gamma'=c-a-b\).
Evidence: the Fuchs relation \(0+(1-c)+0+\gamma'+a+b=1\) forces \(\gamma'=c-a-b\); directly, at \(z=1\)
(13.1.10) has \(p_0=a+b+1-c\), \(q_0=0\), so the exponents are \(0\) and \(c-a-b\). The source's
P-symbol on p. 453 has \(c-a-b\).
Target: [W84.13.1.08].

### W84-E13.1.03. Direction of the exponent shift by \(W(\alpha_1,\beta_1,\gamma_1)\)

Status: Confirmed.
Location: §13.1, p. 452.
Printed: \(W(\alpha_1,\beta_1,\gamma_1)(z)=(z-\xi)^{-\alpha_1}(z-\eta)^{-\beta_1}(z-\zeta)^{-\gamma_1}\), and
\(W\cdot P\{\alpha,\beta,\gamma;\alpha',\beta',\gamma'\}=P\{\alpha+\alpha_1,\dots\}\).
Correct: either \(W=(z-\xi)^{\alpha_1}(z-\eta)^{\beta_1}(z-\zeta)^{\gamma_1}\) or the shifted exponents are
\(\alpha-\alpha_1\), etc.
Evidence: multiplying a solution \((z-\xi)^\alpha(1+O(z-\xi))\) by \((z-\xi)^{-\alpha_1}\) gives exponent
\(\alpha-\alpha_1\) at \(\xi\).
Target: [W84.13.1.09].

### W84-E13.1.04. Reduced P-symbol violates the Fuchs relation

Status: Confirmed.
Location: §13.1, p. 452, last P-symbol.
Printed: exponents \((0,\alpha')\), \((0,1-\alpha'-\gamma')\), \((\gamma,\gamma')\).
Correct: \((0,\alpha')\), \((0,1-\alpha'-\gamma-\gamma')\), \((\gamma,\gamma')\).
Evidence: the sum of the printed exponents is \(1+\gamma\), which equals \(1\) only if \(\gamma=0\).
Target: [W84.13.1.09].

### W84-E13.1.05. Sign of the Legendre coefficients for \(\nu=-n\)

Status: Confirmed.
Location: §13.1, p. 455, Example 1.
Printed: \(c_s(-n)=\frac{(-1)^{s-1}(n+s-1)!}{(s!)^2(n-s-1)!}c_0=(-1)c_s(n-1)\).
Correct: \(c_s(-n)=\frac{(-1)^s(n+s-1)!}{(s!)^2(n-s-1)!}c_0=c_s(n-1)\).
Evidence: the recursion \(s^2c_s=(s-1-\nu)(s+\nu)c_{s-1}\) at \(\nu=-2\), \(s=1\) gives
\(c_1=(0+2)(1-2)c_0=-2c_0\), and \(\frac{(-1)^1\,2!}{1\cdot0!}=-2\); the printed sign gives \(+2\). With the
printed sign, \(P_{n-1}\) would not be the stated solution for \(\nu=-n\) (it is, by the symmetry
\(\nu\mapsto-\nu-1\) of the equation).
Target: [W84.13.1.11].

### W84-E13.1.06. Index in the Bessel coefficients \(c_{2\nu+2s}(-\nu)\)

Status: Confirmed.
Location: §13.1, p. 456, Example 2.
Printed: \(c_{2\nu+2s}(-\nu)=\frac{(-1)^s}{2^{2s}s!(\nu+1)\cdots(\nu+k)}c_{2\nu}\), \(s=1,2,\dots\).
Correct: \(\frac{(-1)^s}{2^{2s}s!(\nu+1)\cdots(\nu+s)}c_{2\nu}\).
Evidence: the recursion \(c_r[(r-\nu)^2-\nu^2]+c_{r-2}=0\) at \(r=2\nu+2s\) gives
\(c_{2\nu+2s}=-c_{2\nu+2s-2}/(4s(\nu+s))\); no index \(k\) is defined.
Target: [W84.13.1.12].

### W84-E13.2.01. Exponents in the numerator of (13.2.6)

Status: Confirmed.
Location: §13.2, p. 462, (13.2.6).
Printed: numerator \(\int_{\mathcal D}s^{q-1}(1-s)^{c-q-1}(1-zs)^{-b}ds\).
Correct: \(\int_{\mathcal D}s^{a-1}(1-s)^{c-a-1}(1-zs)^{-b}ds\), matching the denominator.
Evidence: no \(q\) is defined in Theorem 13.2.2; the proof's (13.2.7) and Corollary 13.2.3 use
\(s^{a-1}(1-s)^{c-a-1}\), and at \(z=0\) the quotient must be \(1\).
Target: [W84.13.2.04].

### W84-E13.2.02. Gauss's summation formula

Status: Confirmed.
Location: §13.2, p. 463, (13.2.9).
Printed: \(F(a,b,c;1)=B(b,c-b-a)/B(c-a,a)\).
Correct: \(F(a,b,c;1)=B(a,c-a-b)/B(a,c-a)=\frac{\Gamma(c)\Gamma(c-a-b)}{\Gamma(c-a)\Gamma(c-b)}\).
Evidence: letting \(z\to1\) in (13.2.8) gives \(B(c-a,a)^{-1}\int_0^1s^{a-1}(1-s)^{c-a-b-1}ds\). For
\(a=1\), \(b=2\), \(c=4\): \(F(1,2,4;1)=\sum_s\frac{6}{(s+2)(s+3)}=3\), while the printed value is
\(B(2,1)/B(3,1)=\frac{1/2}{1/3}=\frac32\). The same misprint occurs in the Table of Formulas, p. 648.
Target: [W84.13.2.06].

### W84-E13.3.01. Power of 2 in the first form of (13.3.6)

Status: Confirmed.
Location: §13.3, p. 464, (13.3.6), first expression.
Printed: denominator \(2\,\Gamma(l+m+1)(n-m)!\).
Correct: \(2^l\,\Gamma(l+m+1)(n-m)!\).
Evidence: at \(z=1.7\) the printed first form divided by the second form equals \(2^{1-l}\) (checked
for \((l,m,n)=(1,0,1),(2,0,1),(2,1,1),(3,1,2),(3,0,3),(4,2,3)\)); at \(l=m=n=0\) the first form gives
\(\frac12\) whereas \(\mathfrak P^0_{00}=1\) (the second form gives \(1\)).
Target: [W84.13.3.03].

### W84-E13.4.01. Coefficient in the equation for \(F(a,b,c;z/b)\)

Status: Confirmed.
Location: §13.4, p. 466, (13.4.3).
Printed: \(z(b-z)u''+\{bc-(a-b-1)z\}u'-abu=0\).
Correct: \(\{bc-(a+b+1)z\}\).
Evidence: substituting \(z\mapsto z/b\) in (13.1.10) and multiplying by \(b\) gives \(bc-(a+b+1)z\). For
\(a=b=c=1\), \(u=F(1,1,1;z)=1/(1-z)\): the corrected equation holds identically, while the printed one
leaves the residual \(4z/(1-z)^2\) (\(=8\) at \(z=\frac12\)).
Target: [W84.13.4.02].

### W84-E13.4.02. Normalization of the double-loop integral for \({}_1F_1\)

Status: Confirmed.
Location: §13.4, pp. 466–467, (13.4.4)–(13.4.5).
Printed: \({}_1F_1(a,c;z)=\frac{\Gamma(c)}{\Gamma(c-a)\Gamma(a)}\int_{\mathcal D}t^{a-1}(1-t)^{c-a-1}e^{zt}dt\).
Correct: the loop integral must be divided by \((1-e^{-2\pi i(c-a)})(e^{2\pi ia}-1)\), as in
(13.2.5) and Theorem 13.2.2; equivalently use the quotient of loop integrals of Theorem 13.2.2.
Evidence: at \(z=0\), \(a=\frac12\), \(c=2\): by (13.2.5) the loop integral equals
\((1-e^{-3\pi i})(e^{\pi i}-1)B(\frac12,\frac32)=(2)(-2)\frac\pi2\), so the printed right side is
\(\frac{\Gamma(2)}{\Gamma(\frac32)\Gamma(\frac12)}\cdot(-2\pi)=-4\neq1={}_1F_1(a,c;0)\). Formula (13.4.6)
on \([0,1]\) is correct.
Target: [W84.13.4.03].

### W84-E13.4.03. Starting index of the series for \(Q_\nu\)

Status: Confirmed.
Location: Problems, p. 470, Problem 8(c).
Printed: \(Q_\nu(z)=\sqrt\pi\sum_{r=1}^\infty\frac{\Gamma(\nu+2r+1)}{r!\,\Gamma(\nu+r+\frac32)}(2z)^{-\nu-2r-1}\).
Correct: the sum starts at \(r=0\).
Evidence: \(\nu=0.6\), \(z=2.5\): \(Q_\nu=2^{-\nu-1}\int_{-1}^1(1-t^2)^\nu(z-t)^{-\nu-1}dt=0.125478\), equal
to the sum from \(r=0\) and to the hypergeometric form; the sum from \(r=1\) is \(0.010241\).
Target: [W84.13.4.08].

### W84-E13.4.04. Normalization of the figure-eight integral for \(Q_\nu\)

Status: Open check.
Location: Problems, pp. 469–470, Problem 8(b).
Printed: \(Q_\nu(z)=\frac1{4i\sin\nu\pi}\int_{\mathcal C}\frac{(t^2-1)^\nu}{(z-t)^{\nu+1}}dt\), to be shown
equal to \(2^{-\nu-1}\int_{-1}^1(1-t^2)^\nu(z-t)^{-\nu-1}dt\).
Correct: probably the figure-eight integral needs a factor \(2^{-\nu}\)
(Whittaker–Watson §15.32 has \(Q_\nu(z)=\frac1{4i\sin\nu\pi}\int\frac{(t^2-1)^\nu}{2^\nu(z-t)^{\nu+1}}dt\)).
Evidence: collapsing the contour onto \([-1,1]\) gives \(\frac{\pm2i\sin\nu\pi\cdot\ldots}{4i\sin\nu\pi}
\int_{-1}^1\) with no power of \(2\); the target \(2^{-\nu-1}\) then needs \(2^{-\nu}\) in the
integrand. The orientation and the branch of \((t^2-1)^\nu\) on the contour were not verified.
Target: [W84.13.4.08].

### W84-E13.4.05. A false contiguous relation in Problem 13

Status: Confirmed.
Location: Problems, p. 471, Problem 13, second identity.
Printed: \(F(a+1,b+1,c;z)-F(a,b,c;z)=\frac{abz}cF(a+1,b+1,c+1;z)\).
Correct: false as stated; no single correction is implied (compare the first identity,
\(F(a,b+1,c;z)-F(a,b,c;z)=\frac{az}cF(a+1,b+1,c+1;z)\), which is correct).
Evidence: the coefficient of \(z\) on the left is \(\frac{(a+1)(b+1)-ab}c=\frac{a+b+1}c\), on the right
\(\frac{ab}c\). Numerically at \(a=0.3\), \(b=0.7\), \(c=1.9\), \(z=0.4\): left \(0.7528\), right
\(0.0642\).
Target: [W84.13.4.12].

### W84-E13.4.06. Non-integrality condition near \(z=1\)

Status: Confirmed.
Location: Problems, pp. 471–472, Problem 16(a).
Printed: "provided \(a-b-c\) is not an integer".
Correct: provided \(c-a-b\notin\mathbb Z\) (the difference of the exponents \(0\), \(c-a-b\) at \(1\)).
Evidence: \(a=\frac12\), \(b=\frac14\), \(c=\frac34\): \(a-b-c=-\frac12\notin\mathbb Z\), but \(c-a-b=0\) and
\(u_2=(1-z)^0F(\frac12,\frac14,1;1-z)=u_1\), so the two solutions coincide.
Target: [W84.13.4.13].

### Conventions and notation (not errata)

- Theorem 13.1.1: "\(c_0\) and \(c_2\)" means the initial coefficients \(c_0\), \(c_1\).
- The hypergeometric function is defined for \(c\notin\{0,-1,-2,\dots\}\) (the source says "not a
  negative integer"; \(c=0\) is also excluded by the series).
- Example 1 writes \(d^2u/dz^2\) for \(d^2u/d\xi^2\) after the change of variable.
- The proof of Theorem 13.2.2 cites "Proposition 13.1.2" for Proposition 13.2.1.
- (13.4.2) is said to converge for \(|z|<1\); the series is entire, as the confluence argument on
  p. 466 shows.
- Problem 4(b): the substitution is \(u=e^{z^2/2}y\).
- (13.2.9) and its Table-of-Formulas copy (p. 648) are the same misprint (W84-E13.2.02).

## Chapter 14. Affine Transformations

### W84-E14.3.01. Factor 2 in the bracket of basic fields

Status: Normalization check.
Location: §14.3, p. 489, Proposition 14.3.1 and its proof.
Printed: \([E(t),E(s)]=-(\Phi(E(t),E(s)))^*-E(\Omega(E(t),E(s)))\).
Correct: with \(d\) normalized by (14.2.4), \([E(t),E(s)]=-2(\Phi(E(t),E(s)))^*-2E(\Omega(E(t),E(s)))\)
(Kobayashi–Nomizu, Prop. III.2.3 form); the printed coefficients hold for
\(d\omega(X,Y)=X\omega(Y)-Y\omega(X)-\omega([X,Y])\).
Evidence: the proof uses \(d\omega(X,Y)=X\omega(Y)-Y\omega(X)-\omega([X,Y])\), while (14.2.4), used in
Example 1 (\(d\theta=-\frac12[\theta\wedge\theta]\)) and in Theorem 14.3.1, gives
\(d\omega(X,Y)=\frac12(\dots)\). For \(E(t),E(s)\) horizontal with \(\omega(E)\) constant,
\(\Omega(E(t),E(s))=d\omega(E(t),E(s))=-\frac12\omega([E(t),E(s)])\).
Target: [W84.14.3.06].

### W84-E14.5.01. Unit normal in the hypersurface connection

Status: Confirmed.
Location: §14.5, p. 497, Example 2.
Printed: \(\nabla_XY=D_XY+(D_XN|Y)N\) for "a normal field \(N\)".
Correct: \(N\) must be a unit normal field (as in Problem 14).
Evidence: replacing \(N\) by \(2N\) multiplies the correction term by \(4\), while the tangential
projection \(D_XY-(D_XY|N)N/|N|^2\) is unchanged; only for \(|N|=1\) does
\((D_XN|Y)=-(D_XY|N)\) make the formula the tangential projection.
Target: [W84.14.5.03].

### W84-E14.7.01. Cartan–Hadamard requires completeness

Status: Confirmed.
Location: §14.7, p. 508, Theorem 14.7.4.
Printed: "If \(M\) is simply connected, then for every \(p\in M\) the mapping \(\mathrm{Exp}_p\) is a
diffeomorphism of \(T_p(M)\) onto \(M\)" (for negative curvature).
Correct: add the hypothesis that \(M\) is complete (and connected).
Evidence: an open geodesic disc of radius \(1\) in the hyperbolic plane is simply connected with
\(K\equiv-1\), but \(\mathrm{Exp}_p\) at its centre is defined only on the open unit disc of \(T_p\), not
on all of \(T_p(M)\).
Target: [W84.14.7.05].

### W84-E14.7.02. Unit-speed half-circle geodesic

Status: Confirmed.
Location: §14.7, p. 506, Example 1.
Printed: \(y=\alpha(\coth t)^{-1}\).
Correct: \(y=\alpha(\cosh t)^{-1}\) (with \(x=\alpha\tanh t+\beta\)).
Evidence: the first integral \(x'=y^2/\alpha\) of the geodesic equation and \(x=\alpha\tanh t+\beta\) give
\(y^2=\alpha x'=\alpha^2\mathrm{sech}^2t\); then \((x-\beta)^2+y^2=\alpha^2\) (a half-circle) and
\(((x')^2+(y')^2)/y^2=1\). With \(\coth\) the curve is not on the circle.
Target: [W84.14.7.03].

### Conventions and notation (not errata)

- The Bianchi identity of Theorem 14.3.1 is printed \(d\Phi(HX,HY)=0\); \(d\Phi\) is a 3-form, so
  read \(d\Phi(HX,HY,HZ)=0\).
- The exterior derivative is normalized by (14.2.4) (factor \(\frac1{k+1}\)); Mathlib's
  `extDeriv` has no such factor.
- Theorems 14.7.2–14.7.3 are quoted without proof and tacitly assume \(M\) connected.

## Chapter 15. Symmetric Spaces

### W84-E15.5.01. Uniqueness of the invariant Riemannian structure

Status: Confirmed.
Location: §15.5, p. 537, Theorem 15.5.1.
Printed: "\(G/H\) has a unique Riemannian structure invariant with respect to \(G\) and to all
symmetries".
Correct: such a structure exists; it is unique only up to the choice of an \(\mathrm{Ad}(H)\)-invariant
inner product on \(\mathfrak p\) (in particular never unique: \(cg\), \(c>0\), is again invariant).
Evidence: for \(S^2=SO(3)/SO(2)\) the round metrics of all radii are \(SO(3)\)-invariant and invariant
under the antipodal-type symmetries \(S_x\); for \(\mathbb R^n=M(n)/SO(n)\) every multiple of the
Euclidean metric is invariant.
Target: [W84.15.5.02].

### W84-E15.5.02. Sign of the curvature tensor of \(G/H\)

Status: Confirmed.
Location: §15.5, p. 542, (15.5.2).
Printed: \(R(d\pi X,d\pi Y)d\pi Z=d\pi([[X,Y],Z])\).
Correct: \(R(d\pi X,d\pi Y)d\pi Z=-d\pi([[X,Y],Z])\).
Evidence: (15.5.3) \(K(X\vee Y)=Q([[X,Y],X],Y)\) for orthonormal \(X,Y\) follows from (14.7.3)
\(K=-g(R(X,Y)X,Y)\) only with the minus sign; Problem 10(c) also has \(-d\pi[[X,Y],Z]\). For
\(S^2=SO(3)/SO(2)\), \(X=E_{13}-E_{31}\), \(Y=E_{23}-E_{32}\) (orthonormal for \(-\frac12\mathrm{Tr}\,AB\)):
\([[X,Y],X]=Y\), so (15.5.3) gives \(K=+1\), while the printed (15.5.2) with (14.7.3) gives \(K=-1\).
Target: [W84.15.5.07].

### W84-E15.6.01. Sign of the trace form on \(\mathfrak p\) for the Grassmannian

Status: Confirmed.
Location: Problems, p. 549, Problem 12(c).
Printed: "\(\frac12\mathrm{Tr}\,AB\) is positive definite on \(\mathfrak p\)".
Correct: \(-\frac12\mathrm{Tr}\,AB\) (equivalently \(\frac12\mathrm{Tr}\,AB^t\)) is positive definite.
Evidence: for \(A=\begin{pmatrix}0&X\\-X^t&0\end{pmatrix}\in\mathfrak p\),
\(\mathrm{Tr}\,A^2=-2\,\mathrm{Tr}(X^tX)<0\) for \(X\ne0\).
Target: [W84.15.6.05].

### Conventions and notation (not errata)

- Theorem 15.6.2 is stated for symmetric pairs; its proof uses Lemma 15.6.1, which assumes \(K\)
  compact, as does the notion of Gelfand pair in Chapter 5.
- Proof of Theorem 15.6.2: "Lemma 15.7.1" is Lemma 15.6.1, and "Corollary 15.5.6(2)" refers to
  Corollary 15.5.5(2).
- §15.3: "the smallest subgroup of \(G(M)\)" should read "of \(\mathrm{Aff}\,M\)".
- Problem 8's hint cites "Lemma 13.6.3" and "Theorem 18.2.7"; neither matches the intended
  results (Lemma 15.2.4, Theorem 15.2.7 are probably meant).
- Example 2 in §15.5 refers to "Problem 13" for the Grassmann manifold; it is Problem 12.

## Chapter 16. General Harmonic Analysis on a Symmetric Space

No errata were found in Chapter 16.

### Conventions and notation (not errata)

- The equation number (16.1.1) is used twice (p. 550 and p. 553).
- p. 558, (16.1.15): the integration is written \(d\lambda\); it is the Plancherel measure \(d\nu\)
  of Theorem 16.1.5.
- The chapter assumes a Gelfand pair of Lie groups with \(G\) separable; compactness of \(G\) is
  not assumed (only of \(K\)).

## Chapter 17. Semisimple Algebras. Semisimple Groups. Symmetric Spaces of the Non-Compact Type

### W84-E17.1.01. Intermediate expansion of the Killing form of \(\mathfrak u(n)\)

Status: Confirmed.
Location: §17.1, Example 1, p. 563.
Printed: \(B(H,H)=-2(n-1)\sum_rx_r^2-4\sum_{r\ne s}x_rx_s\) (as the intermediate step), and
\(-(\mathrm{Tr}H)^2=\sum x_r^2=\sum x_r^2+2\sum_{r\ne s}x_rx_s\).
Correct: \(B(H,H)=-2\sum_{r<s}(x_r-x_s)^2=-2(n-1)\sum_rx_r^2+2\sum_{r\ne s}x_rx_s\), and
\(-(\mathrm{Tr}H)^2=(\sum_rx_r)^2=\sum_rx_r^2+\sum_{r\ne s}x_rx_s\) for \(H=\mathrm{diag}(ix_1,\dots,
ix_n)\).
Evidence: For \(n=2\), \(x=(1,1)\), \(H\) is central and \(B(H,H)=0\); the printed intermediate
expression gives \(-2\cdot2-4\cdot2=-12\). The final formula \(B(X,Y)=2n\,\mathrm{Tr}XY-2\,\mathrm{Tr}X
\,\mathrm{Tr}Y\) is correct (for \(n=2\), \(x=(1,0)\): \(2\cdot2\cdot(-1)-2\cdot(-1)=-2=-2(1-0)^2\)).
Target: [W84.17.1.04].

### W84-E17.1.02. Values \(B(X_{rs},X_{rs})\), \(B(Y_{rs},Y_{rs})\)

Status: Confirmed.
Location: §17.1, Example 1, p. 564.
Printed: \(B(X_{rs},X_{rs})=-2=B(Y_{rs},Y_{rs})\).
Correct: \(B(X_{rs},X_{rs})=B(Y_{rs},Y_{rs})=-4n\).
Evidence: \(X_{rs}^2=-(E_{rr}+E_{ss})\) and \(\mathrm{Tr}X_{rs}=0\), so the source's own formula gives
\(2n\,\mathrm{Tr}X_{rs}^2=-4n\); likewise for \(Y_{rs}\). Direct computation of
\(\mathrm{Tr}(\mathrm{ad}X_{12})^2\) on \(\mathfrak u(3)\) gives \(-12\).
Target: [W84.17.1.04].

### W84-E17.2.01. The extra real form of \(\mathfrak o(2k,\mathbb C)\)

Status: Confirmed.
Location: §17.2, Example 1, p. 566.
Printed: for even \(p+q\) there is another real form, \(\mathfrak{sp}(n)\).
Correct: for \(p+q=2k\) the additional real form is \(\mathfrak o^*(2k)\).
Evidence: \(\dim\mathfrak{sp}(k)=k(2k+1)\ne k(2k-1)=\dim\mathfrak o(2k,\mathbb C)\) (complex dimension), so
\(\mathfrak{sp}\) cannot be a real form; Problem 7(f)–(g) on p. 599 of the source itself gives
\(\mathfrak o^*(2n)\).
Target: [W84.17.2.02].

### W84-E17.5.01. \(MAN\) is a semidirect, not a direct, product

Status: Confirmed.
Location: §17.5, p. 586.
Printed: \(MAN\) is the direct product of \(M\) and \(AN\).
Correct: \(MAN\) is the semidirect product \(M\ltimes AN\) (\(AN\) normal in \(MAN\)).
Evidence: For \(G=SO_0(3,1)\), \(M\cong SO(2)\) acts on \(N\cong\mathbb R^2\) by rotations,
\(mn_xm^{-1}=n_{mx}\), so \(M\) and \(N\) do not commute. Problem 18(a) of the source (p. 603)
states the semidirect product.
Target: [W84.17.5.01].

### W84-E17.5.02. Fixed point property: compactness omitted

Status: Confirmed.
Location: §17.5, Definition, p. 587; used in Theorems 17.5.1–17.5.2, p. 588.
Printed: \(\Gamma\) has the fixed point property if every continuous representation on a locally
convex space has a fixed point in every invariant convex set \(Q\).
Correct: \(Q\) must be a non-empty compact convex invariant set.
Evidence: With the printed definition Theorem 17.5.1 fails for \(\Gamma=\mathbb R\): the action
\(t\mapsto\begin{pmatrix}1&t\\0&1\end{pmatrix}\) on \(\mathbb R^2\) preserves the convex line
\(Q=\{(x,1)\}\), on which it is \(x\mapsto x+t\), without a fixed point. The proofs of both
theorems use compactness (Markov–Kakutani, and the Haar average over \(M\)).
Target: [W84.17.5.02].

### W84-E17.6.01. Problem 4(a): repeated \(\mathbb CE_{rs}\)

Status: Confirmed.
Location: §17.6, Problem 4(a), p. 597.
Printed: \(\mathfrak g_{rs}=\mathbb CE_{rs}\oplus\mathbb CE_{rs}\oplus\mathbb C(E_{rr}-E_{ss})\).
Correct: \(\mathfrak g_{rs}=\mathbb CE_{rs}\oplus\mathbb CE_{sr}\oplus\mathbb C(E_{rr}-E_{ss})\).
Evidence: The printed sum is not direct and is two-dimensional; the copy of
\(\mathfrak{sl}(2,\mathbb C)\) needs \(E_{sr}\).
Target: [W84.17.6.07].

### W84-E17.6.02. Problem 4(b): condition for vanishing Cartan number

Status: Confirmed.
Location: §17.6, Problem 4(b), p. 597.
Printed: the Cartan number vanishes if \(p\ne s\) and \(q\ne r\).
Correct: it vanishes iff \(\{p,q\}\cap\{r,s\}=\emptyset\).
Evidence: \((r,s)=(1,2)\), \((p,q)=(1,3)\) satisfies the printed condition, but
\([E_{11}-E_{22},E_{13}]=E_{13}\), i.e. \(\alpha_{13}(H_{12})\ne0\): the Cartan number is \(1\).
Target: [W84.17.6.07].

### W84-E17.6.03. Problem 7(d): the two real forms of \(\mathfrak{sl}(2,\mathbb C)\)

Status: Confirmed.
Location: §17.6, Problem 7(d), p. 599.
Printed: the compact form \(\mathfrak{sl}(2,\mathbb C)\) and the non-compact form
\(\mathfrak{sl}(2,\mathbb C)\).
Correct: the compact form \(\mathfrak{su}(2)\) and the non-compact form \(\mathfrak{sl}(2,\mathbb R)\).
Evidence: A real form of \(\mathfrak{sl}(2,\mathbb C)\) has real dimension 3; \(\mathfrak{sl}(2,\mathbb C)\)
itself has real dimension 6 and is not compact.
Target: [W84.17.6.08].

### Conventions and notation (not errata)

- Numbering: Theorem 17.2.4 and Lemma 17.2.4 share a number; Theorem 17.3.2 is followed by
  Theorem 17.3.4; (17.4.2) is used twice.
- Cross-reference slips: "Proposition 17.1.1" on p. 562 means Proposition 17.1.2;
  "Theorem 17.2.7(3)" on p. 585 means Theorem 17.2.6(3); "Theorem 17.4.2" in Example 2 of §17.4
  means Proposition 17.4.2; "Example 10" in Problem 20 means Example 1 of §17.5.
- p. 582: "abelian subspaces of \(\mathfrak k\)" means maximal abelian subspaces of \(\mathfrak p\).
- pp. 583, 632: "rank of \(W\)" means the order \(|W|\).
- "Reduced root" means restricted root; "Borel subgroup" is the source's name for \(AN\);
  "differentiation" means derivation.
- \(S^n\) is used for the unit sphere of \(\mathbb R^n\) (dimension \(n-1\)).

## Chapter 18. Harmonic Analysis on Symmetric Spaces of the Non-Compact Type

### W84-E18.1.01. Poisson kernel: direction of the Jacobian

Status: Confirmed.
Location: §18.1, p. 609, (18.1.11) and its proof; used again on p. 611.
Printed: \(\frac{dg\cdot b}{db}:=e^{-2\rho(H(g^{-1}k))}\), \(b=kM\).
Correct: \(\frac{d(g^{-1}\cdot b)}{db}=e^{-2\rho(H(g^{-1}k))}\); equivalently
\(\frac{d(g\cdot b)}{db}=e^{-2\rho(H(gk))}\).
Evidence: For \(G=SL(2,\mathbb R)\), \(B=S^1\), a fixed \(g\) and \(b=kM\), the numerical Jacobian of
\(b\mapsto g\cdot b\) is \(0.19433\), equal to \(e^{-2H(gk)}\); the printed expression
\(e^{-2H(g^{-1}k)}\) equals \(0.87483\). (Here \(2\rho=2\alpha\) with \(\alpha(H)=\) the \(\mathfrak a\)-coordinate.)
Target: [W84.18.1.05].

### W84-E18.1.02. Example 1 of §18.1: sign of \(\lambda\) in the plane waves

Status: Confirmed.
Location: §18.1, Example 1, p. 612.
Printed: \(e_{\lambda,kM}(gK)=e^{\lambda\alpha(H(g^{-1}k))}\), \(e_{\lambda,b}(x)=|\langle x,\tilde s\rangle|^\lambda\),
\(e_{\lambda,b}(x_t)=(\cosh t-s^1\sinh t)^\lambda\).
Correct: with (18.1.1)–(18.1.2), \(e_{\lambda,kM}(gK)=e^{-\lambda\alpha(H(g^{-1}k))}\),
\(e_{\lambda,b}(x)=|\langle x,\tilde s\rangle|^{-\lambda}\), \(e_{\lambda,b}(x_t)=(\cosh t-s^1\sinh t)^{-\lambda}\).
Evidence: For \(x=a_t\cdot o\) and \(b=eM\), \(A(x,b)=tH\) (since \(x=a_t\cdot o\) lies on the horocycle
\(a_t\cdot\xi_0\)), so \(e_{\lambda,b}(x)=e^{\lambda t}\); but \(|\langle x,e_1+e_{n+1}\rangle|=|\sinh t-\cosh t|
=e^{-t}\), so \(|\langle x,\tilde s\rangle|^{\lambda}=e^{-\lambda t}\). The final formula for \(\varphi_\lambda\)
is correct because \(\Phi_\lambda\) is even in \(\lambda\).
Target: [W84.18.1.08].

### W84-E18.3.01. Harish-Chandra image of the Laplacian

Status: Confirmed.
Location: §18.3, Example, p. 621.
Printed: \(\Gamma_\Delta(i\lambda)=-(\langle\lambda|\lambda\rangle-\langle\rho|\rho\rangle)\).
Correct: \(\Gamma_\Delta(i\lambda)=-(\langle\lambda|\lambda\rangle+\langle\rho|\rho\rangle)\).
Evidence: On \(\mathbb H^3\) (\(\rho=1\)), \(\Phi_\lambda(t)=\frac{\sin\lambda t}{\lambda\sinh t}\) and
\(\Delta=\partial_t^2+2\coth t\,\partial_t\) give \(\Delta\Phi_\lambda=-(\lambda^2+1)\Phi_\lambda\). The source's
own (18.4.4) (p. 625) has the \(+\) sign.
Target: [W84.18.3.03].

### W84-E18.4.01. Harish-Chandra series: exponent and recurrence

Status: Confirmed.
Location: §18.4, p. 625, (18.4.5) and the recurrence below it.
Printed: \(\psi_\lambda(\exp H)=e^{(-i\lambda-\rho)(H)}\sum\gamma_\mu e^{-\mu(H)}\); recurrence
\((\langle\mu,\mu\rangle-2i\mu)\gamma_\mu=2\sum_\alpha m_\alpha\sum_k\gamma_{\mu-2k}(\langle\mu+\rho-2k\alpha,\alpha\rangle-
i\alpha)\).
Correct: \(\psi_\lambda(\exp H)=e^{\langle i\lambda-\rho,H\rangle}\sum\gamma_\mu e^{-\mu(H)}\) and
\((\langle\mu,\mu\rangle-2i\langle\mu,\lambda\rangle)\gamma_\mu=2\sum_{\alpha\in\Sigma_+}m_\alpha\sum_{k\ge1}
\gamma_{\mu-2k\alpha}(\langle\mu+\rho-2k\alpha,\alpha\rangle-i\langle\alpha,\lambda\rangle)\).
Evidence: The printed exponent conflicts with (18.4.8)–(18.4.9) and with the hyperplanes
\(S_\mu\). Substituting the series in \(R(\Omega)\psi=-(\langle\lambda,\lambda\rangle+\langle\rho,\rho\rangle)\psi\) with
\(R(\Omega)\) of (18.4.3) and \(\coth\alpha=1+2\sum_{k\ge1}e^{-2k\alpha}\), and collecting
\(e^{\langle i\lambda-\rho-\mu,H\rangle}\), gives the corrected recurrence; the printed \(2i\mu\),
\(i\alpha\) and \(\gamma_{\mu-2k}\) are not scalars/elements of \(L\) as written. In rank one it
reduces to the recurrence of §18.5 (with \(4q\), cf. W84-E18.5.02).
Target: [W84.18.4.02].

### W84-E18.4.02. Theorem 18.4.1: \(\mu=0\) must be excluded

Status: Confirmed.
Location: §18.4, Theorem 18.4.1, p. 625.
Printed: convergence for \(\lambda\notin\bigcup_{\mu\in L}S_\mu\).
Correct: \(\lambda\notin\bigcup_{\mu\in L\setminus\{0\}}S_\mu\).
Evidence: \(S_0=\{\lambda:0=0\}=\mathfrak a^*_{\mathbb C}\), so the printed hypothesis is never satisfied.
Target: [W84.18.4.02].

### W84-E18.5.01. Rank-one example: the transformed radial equation

Status: Confirmed.
Location: §18.5, Example, p. 627.
Printed: \(F''+(-2i\lambda+2\rho+g)F'+2\rho(\rho+i\lambda)(1-g)F=0\) (as printed, for
\(f=e^{(i\lambda-\rho)t}F\)).
Correct: \(F''+(g+2i\lambda-2\rho)F'+(\rho-i\lambda)(2\rho-g)F=0\).
Evidence: Substituting \(f=e^{(i\lambda-\rho)t}F\) in \(f''+gf'+(\lambda^2+\rho^2)f=0\) gives
\(F''+(2(i\lambda-\rho)+g)F'+[(i\lambda-\rho)^2+g(i\lambda-\rho)+\lambda^2+\rho^2]F=0\), and the bracket
equals \((i\lambda-\rho)(g-2\rho)\) (symbolic check). With the corrected equation the recurrence for
\(\Gamma_m\) (as corrected in W84-E18.5.02) follows from \(g-2\rho=2p\sum_{k\ge1}e^{-2kt}+4q\sum_{k\ge1}
e^{-4kt}\).
Target: [W84.18.5.01].

### W84-E18.5.02. Rank-one recurrence: coefficient of the \(2\alpha\) term

Status: Confirmed.
Location: §18.5, Example, p. 628.
Printed: \(\Gamma_m=\frac1{m(m-2i\lambda)}[2p\sum\dots+2q\sum_{k}\Gamma_{m-4k}(\dots)]\).
Correct: the coefficient of the second sum is \(4q\).
Evidence: \(2q\coth2t=2q+4q\sum_{k\ge1}e^{-4kt}\). Numerically, at \(p=3\), \(q=2\), \(\lambda=0.37\),
\(t=1.1\), the series with \(4q\) satisfies the radial equation with residual \(2.5\cdot10^{-31}\); with
\(2q\) the residual is \(8.4\cdot10^{-3}\).
Target: [W84.18.5.01].

### W84-E18.5.03. Helgason's product (18.5.4): missing normalization in higher rank

Status: Confirmed.
Location: §18.5, p. 629, (18.5.4).
Printed: \(c(\lambda)=\prod_{\alpha\in\Sigma_0^+}\Gamma(\frac12(m_\alpha+m_{2\alpha}+1))2^{\frac12m_\alpha+m_{2\alpha}}
e(\lambda)d(\lambda)\), without a constant.
Correct: a constant \(c_0\) fixed by \(c(-i\rho)=1\) is needed in rank \(\ge2\).
Evidence: For \(G=SL(3,\mathbb C)\) (\(m_\alpha=2\), three positive roots), Theorem 18.5.1 gives
\(c(\lambda)=2/\prod_\alpha\lambda_\alpha\) (with \(\lambda_\alpha=\langle i\lambda,\alpha\rangle/\langle\alpha,\alpha\rangle\)), whereas
(18.5.4) gives \(1/\prod_\alpha\lambda_\alpha\), so that \(c(-i\rho)=\frac12\). The two displays of the
source conflict; in rank one they agree with (18.5.2).
Target: [W84.18.5.04].

### W84-E18.5.04. Definition of \(e(\lambda)\): product, not sum

Status: Confirmed.
Location: §18.5, p. 630, (18.5.6).
Printed: \(e(\lambda)^{-1}=\sum_{\alpha\in\Sigma_0^+}\Gamma(\dots)\Gamma(\dots)\).
Correct: \(e(\lambda)^{-1}=\prod_{\alpha\in\Sigma_0^+}\Gamma(\dots)\Gamma(\dots)\).
Evidence: Only the product makes (18.5.4) multiplicative over \(\Sigma_0^+\), as required by the
Gindikin–Karpelevich formula (18.5.3), and reproduces (18.5.2) in rank one.
Target: [W84.18.5.04].

### W84-E18.5.05. Zeros of \(c^{-1}\) near \(\mathfrak a^*\)

Status: Confirmed.
Location: §18.5, property (2), p. 630.
Printed: the only zero of \(c^{-1}\) in a cylinder \(\{|\mathrm{Im}\lambda|<\varepsilon\}\) is \(\lambda=0\).
Correct: in that tube the zeros of \(c^{-1}\) lie on the hyperplanes \(\langle\lambda,\alpha\rangle=0\),
\(\alpha\in\Sigma_0^+\); \(\lambda=0\) is the only zero only in rank one.
Evidence: For complex \(G\), \(c(\lambda)^{-1}\) is a constant times \(\prod_{\alpha\in\Sigma_+}\langle i\lambda,
\alpha\rangle\) (Theorem 18.5.1 with \(m_\alpha=2\)); for \(SL(3,\mathbb C)\) it vanishes on the three real
root hyperplanes, e.g. at \(\lambda\ne0\) with \(\langle\lambda,\alpha_1\rangle=0\).
Target: [W84.18.5.05].

### W84-E18.6.01. Plancherel density in (18.6.3)

Status: Confirmed.
Location: §18.6, p. 632, (18.6.3).
Printed: \(|c(\lambda)|^2\,d\lambda\).
Correct: \(|c(\lambda)|^{-2}\,d\lambda\).
Evidence: Theorem 18.6.1 (p. 631) and (18.6.4)–(18.6.5) use \(|c(\lambda)|^{-2}\); in rank one,
\(\mathbb H^3\) gives \(c(\lambda)=1/(i\lambda)\) and the Plancherel density \(\propto\lambda^2=|c|^{-2}\).
Target: [W84.18.6.02].

### W84-E18.7.01. Definition of \(\Lambda_-\)

Status: Confirmed.
Location: §18.7, p. 640, (18.7.14).
Printed: \(\mathcal F(\Lambda_-f):=c(\lambda)^{-1}\mathcal Ff\), the same as the definition of \(\Lambda_+\).
Correct: \(\mathcal F(\Lambda_-f)=c(-\lambda)^{-1}\mathcal Ff\) (\(=\overline{c(\lambda)}^{-1}\mathcal Ff\) for real
\(\lambda\)), so that \(\Lambda_-\Lambda_+\) is the multiplier \(|c(\lambda)|^{-2}\) needed in Theorem 18.7.4.
Evidence: With the printed definition \(\Lambda_-\Lambda_+\) has multiplier \(c(\lambda)^{-2}\), which is not
real: in rank one at a sample real \(\lambda\), \(c(\lambda)=0.36-0.51i\), so \(c^{-2}\ne|c|^{-2}\), and
(18.7.17) would conflict with the Plancherel formula of Theorem 18.6.2 via (18.7.13).
Target: [W84.18.7.05].

### W84-E18.8.01. Paley–Wiener theorem (2): holomorphy omitted

Status: Confirmed.
Location: §18.8, Theorem 18.8.1(2), p. 645.
Printed: the spherical transform maps \(C_c^\infty(K\backslash G/K)\) onto the \(W\)-invariant
functions on \(\mathfrak a^*_{\mathbb C}\) of exponential growth.
Correct: onto the \(W\)-invariant entire (holomorphic) functions of exponential growth.
Evidence: A non-zero \(W\)-invariant \(\psi\in C_c^\infty(\mathfrak a^*_{\mathbb C})\) satisfies the growth
condition (it is bounded with compact support) but is not a transform: every \(\tilde f\) with
\(f\in C_c^\infty\) is entire, and a compactly supported entire function vanishes.
Target: [W84.18.8.03].

### Conventions and notation (not errata)

- Thm 18.8.1(1): "holomorphic on \(\mathfrak a^*_{\mathbb C}\times B\)" means holomorphic in \(\lambda\) and
  \(C^\infty\) in \(b\).
- (18.1.12): the spherical coefficient is written \(\langle\mathcal U^\lambda(g)f_0,f_0\rangle\); with
  \(f_0=1\) both argument orders give the same integral.
- (18.6.5): "\(|c(x)|\)" is a misprint for \(|c(\lambda)|\).
- Proof of Lemma 18.7.3: "\(m\in N\)" means \(m\in M\) (proof only).
- The equation numbers (18.3.2) and (18.4.7) are not printed.
- Normalizations of \(d\lambda\), \(da\), \(dn\) and \(dm\) in the Plancherel and inversion formulas
  are not specified; constants are correct only up to these normalizations.
- p. 618 the Kostant irreducibility statement is cited without proof; it is consistent with
  Theorems 18.5.4–18.5.5.

## Formula collection. Table of Formulas

### W84-EF.1.01. \(\Gamma\) at half-integers

Status: Confirmed.
Location: Table, p. 646.
Printed: \(\Gamma(n-\frac12)=\frac{(2n)!\sqrt\pi}{2^{2n}n!}\).
Correct: \(\Gamma(n+\frac12)=\frac{(2n)!\sqrt\pi}{2^{2n}n!}\).
Evidence: At \(n=1\) the right side is \(\sqrt\pi/2=\Gamma(\frac32)\), while \(\Gamma(\frac12)=\sqrt\pi\).
Target: [W84.F.1.01].

### W84-EF.1.02. Continuation formula for \(\Gamma\)

Status: Confirmed.
Location: Table, p. 646.
Printed: \(\Gamma(z)=\frac{\Gamma(z-n)}{(z-n-1)\cdots z}\), \(\mathrm{Re}z>0\).
Correct: \(\Gamma(z)=\frac{\Gamma(z+n)}{z(z+1)\cdots(z+n-1)}\) for \(\mathrm{Re}z>-n\), \(z\notin-\mathbb Z_+\).
Evidence: At \(z=2\), \(n=1\) the printed form gives \(\Gamma(1)/(0\cdot\dots)\), undefined; the
corrected form gives \(\Gamma(3)/2=1=\Gamma(2)\). The corrected form follows from \(\Gamma(z+1)=z\Gamma(z)\)
and is the one that extends \(\Gamma\) to \(\mathrm{Re}z>-n\).
Target: [W84.F.1.01].

### W84-EF.1.03. \(|\Gamma(ix)|^2\): \(\sinh\), not \(\sin\)

Status: Confirmed.
Location: Table, p. 646.
Printed: \(|\Gamma(ix)|^2=\frac\pi{x\sin\pi x}\).
Correct: \(|\Gamma(ix)|^2=\frac\pi{x\sinh\pi x}\), \(x\in\mathbb R\setminus\{0\}\).
Evidence: At \(x=1\): \(|\Gamma(i)|^2=0.27203\), \(\pi/\sinh\pi=0.27203\); \(\pi/\sin\pi\) is infinite.
Target: [W84.F.1.02].

### W84-EF.1.04. \(|\Gamma(\frac12+ix)|^2\): modulus omitted

Status: Confirmed.
Location: Table, p. 646.
Printed: \(\Gamma(\frac12+ix)^2=\frac\pi{\cosh\pi x}\).
Correct: \(|\Gamma(\frac12+ix)|^2=\frac\pi{\cosh\pi x}\).
Evidence: At \(x=1\), \(\Gamma(\frac12+i)^2\) is non-real (\(\approx-0.0902-0.2556i\)), while
\(|\Gamma(\frac12+i)|^2=0.27101=\pi/\cosh\pi\).
Target: [W84.F.1.02].

### W84-EF.1.05. Duplication formula: argument

Status: Confirmed.
Location: Table, p. 646.
Printed: \(\Gamma(2x)=\frac{2^{2x-1}}{\sqrt\pi}\Gamma(z)\Gamma(x+\frac12)\).
Correct: \(\Gamma(2x)=\frac{2^{2x-1}}{\sqrt\pi}\Gamma(x)\Gamma(x+\frac12)\).
Evidence: The printed right side depends on an unbound \(z\); at \(x=1\) the corrected form gives
\(\frac2{\sqrt\pi}\cdot1\cdot\frac{\sqrt\pi}2=1=\Gamma(2)\).
Target: [W84.F.1.02].

### W84-EF.1.06. Gauss's limit formula

Status: Confirmed.
Location: Table, p. 646.
Printed: \(\Gamma(z)=\lim_n\frac{n!\,z^n}{z(z+1)\cdots(z+n)}\), \(z=0,-1,-2,\dots\).
Correct: \(\Gamma(z)=\lim_n\frac{n!\,n^z}{z(z+1)\cdots(z+n)}\), \(z\ne0,-1,-2,\dots\).
Evidence: At \(z=1\) the printed quotient is \(n!/(n+1)!\to0\ne\Gamma(1)\); the corrected quotient is
\(n/(n+1)\to1\). At \(z\in-\mathbb Z_+\) the denominator vanishes.
Target: [W84.F.1.03].

### W84-EF.1.07. Beta integral over \((0,\infty)\)

Status: Confirmed.
Location: Table, p. 646.
Printed: \(B(x,y)=\int_0^\infty t^{x-1}(1-t)^{-x-y}dt\).
Correct: \(B(x,y)=\int_0^\infty t^{x-1}(1+t)^{-x-y}dt\).
Evidence: At \(x=y=1\): \(\int_0^\infty(1+t)^{-2}dt=1=B(1,1)\); the printed integrand has a
non-integrable singularity at \(t=1\).
Target: [W84.F.1.04].

### W84-EF.1.08. Trigonometric beta integral: upper limit

Status: Confirmed.
Location: Table, p. 647.
Printed: \(B(x,y)=2\int_0^{2\pi}\cos^{2x-1}\varphi\sin^{2y-1}\varphi\,d\varphi\).
Correct: upper limit \(\pi/2\).
Evidence: At \(x=y=1\), \(2\int_0^{2\pi}\cos\varphi\sin\varphi\,d\varphi=0\), while
\(2\int_0^{\pi/2}\cos\varphi\sin\varphi\,d\varphi=1=B(1,1)\).
Target: [W84.F.1.04].

### W84-EF.1.09. Beta integral with \(1+t^2\): exponent \(y\) omitted

Status: Confirmed.
Location: Table, p. 647.
Printed: \(B(\frac{x+1}2,y-\frac{x+1}2)=2\int_0^\infty\frac{t^x}{1+t^2}dt\).
Correct: \(B(\frac{x+1}2,y-\frac{x+1}2)=2\int_0^\infty\frac{t^x}{(1+t^2)^y}dt\).
Evidence: At \(x=0\), \(y=2\): \(B(\frac12,\frac32)=\pi/2\) and \(2\int_0^\infty(1+t^2)^{-2}dt=\pi/2\); the
printed integral is \(\pi\).
Target: [W84.F.1.04].

### W84-EF.2.01. Euler product: half-plane

Status: Confirmed.
Location: Table, p. 647.
Printed: \(\zeta(z)\prod_p(1-p^{-z})=1\) for \(\mathrm{Re}z>0\).
Correct: for \(\mathrm{Re}z>1\).
Evidence: For \(0<\mathrm{Re}z\le1\) the Dirichlet series and the product do not converge
absolutely; at \(z=1\) the product \(\prod_p(1-p^{-1})\) diverges to \(0\) and \(\zeta\) has a pole.
Target: [W84.F.2.01].

### W84-EF.3.01. Gauss's sum \(F(a,b;c;1)\)

Status: Confirmed.
Location: Table, p. 648.
Printed: \(F(a,b;c;1)=\frac{B(b,c-b-a)}{B(c-a,a)}\).
Correct: \(F(a,b;c;1)=\frac{\Gamma(c)\Gamma(c-a-b)}{\Gamma(c-a)\Gamma(c-b)}=\frac{B(a,c-a-b)}{B(a,c-a)}\),
\(\mathrm{Re}(c-a-b)>0\).
Evidence: At \((a,b,c)=(1,2,4)\): \(F(1,2;4;1)=\sum_s\frac{(2)_s}{(4)_s}=3\) and
\(\Gamma(4)\Gamma(1)/(\Gamma(3)\Gamma(2))=3\); the printed quotient is \(B(2,1)/B(3,1)=\frac{1/2}{1/3}=\frac32\).
Target: [W84.F.3.02].

### W84-EF.3.02. Contiguous relation

Status: Confirmed.
Location: Table, p. 649.
Printed: \(F(a+1,b+1;c;z)-F(a,b;c;z)=\frac{abz}cF(a+1,b+1;c+1;z)\).
Correct: \(F(a,b+1;c;z)-F(a,b;c;z)=\frac{az}cF(a+1,b+1;c+1;z)\) (and symmetrically in \(a,b\)).
Evidence: At \(a=0.3\), \(b=0.7\), \(c=1.9\), \(z=0.2\): printed left side \(0.27155\), printed right
side \(0.02612\). The corrected relation holds there to working precision and follows by comparing
coefficients: \(\frac{(a)_s}{(c)_ss!}[(b+1)_s-(b)_s]=\frac{(a)_s(b+1)_{s-1}s}{(c)_ss!}\).
Target: [W84.F.3.03].

### W84-EF.3.03. Quadratic transformation: argument

Status: Confirmed.
Location: Table, p. 649.
Printed: \(F(2a,2b;a+b+\frac12;z)=F(a,b;a+b+\frac12;\frac{4z}{z-1})\).
Correct: \(F(2a,2b;a+b+\frac12;z)=F(a,b;a+b+\frac12;4z(1-z))\) (\(\mathrm{Re}z<\frac12\)).
Evidence: At \(a=0.3\), \(b=0.4\), \(z=0.2\) (sample point): left side \(1.09237\), corrected right side
\(1.09237\), printed right side \(0.92688\). The corrected form is DLMF 15.8.18.
Target: [W84.F.3.03].

### W84-EF.6.01. Closed forms of \(P^l_{kj}\)

Status: Confirmed.
Location: Table, pp. 653–654 (definition, Jacobi form, finite sum, the \(p\)-sum on p. 654).
Printed: the derivative definition without the factor \(2^{-l}\); the Jacobi-polynomial form with an
extra power of 2; the finite sum without the square root over the factorials and with range
\(t\le l-j\); the \(p\)-sum \(\sum_p\frac{(l+p)!}{(l-p)!(j+p)!(k+p)!}(\frac{1-x}{1+x})^p\) with its prefactor;
hypothesis \(|k|,|j|<l\).
Correct: the forms of W84.F.6.02 (= W84.08.1.03, W84.08.1.05, W84.08.1.06): factor \(2^{-l}\) in
the derivative form; square root \([(l+k)!(l-k)!(l+j)!(l-j)!]^{1/2}\) and range
\(\max(0,j-k)\le t\le\min(l-k,l+j)\) in the sum; \(|k|,|j|\le l\).
Evidence: The table's own value \(P^l_{ll}(z)=(\frac{1+z}2)^l\) (p. 655) is the test. At \(l=1\),
\(k=j=1\): the printed derivative form gives \(1+x\), the printed Jacobi form \((1+x)/4\), the
printed sum \(1+x\); the correct value is \((1+x)/2\). At \(l=1\), \(k=j=0\) (where \(P^1_{00}=P_1=x\))
the printed \(p\)-sum gives \(1+2\frac{1-x}{1+x}\). The corrected forms agree with each other, with
the symmetries, orthogonality \(\int|P^l_{mn}|^2=\frac2{2l+1}\), the four relations on p. 654 and the
special values on p. 655, checked for \(l\le2\) at \(x=0.3\). See also W84-E08.1.02 and
W84-E08.1.03.
Target: [W84.F.6.02].

### W84-EF.6.02. Contour integral for \(P^l_{kj}\)

Status: Confirmed.
Location: Table, p. 654.
Printed: a contour integral for \(P^l_{mj}(\cos\theta)\) whose integrand differs from
(8.1.7) in the signs and exponents of the two linear factors.
Correct: \(P^l_{kj}(\cos\theta)=\frac1{2\pi i}\sqrt{\frac{(l+k)!(l-k)!}{(l+j)!(l-j)!}}\oint(\zeta\cos\frac\theta2+
i\sin\frac\theta2)^{l+j}(i\zeta\sin\frac\theta2+\cos\frac\theta2)^{l-j}\zeta^{-l-k-1}d\zeta\) (W84.08.1.07 with
\(k\leftrightarrow j\), using \(P^l_{kj}=P^l_{jk}\)).
Evidence: At \(l=1\), \(m=j=0\) the printed integral gives \(0\) instead of \(P_1(x)=x\) (\(x=0.3\)).
The corrected integral reproduces the closed form of W84.F.6.02 at all \((l,k,j)\) with \(l\le2\)
tested.
Target: [W84.F.6.02].

### W84-EF.7.01. Hypergeometric form of \(P^n_l\) on \((-1,1)\)

Status: Confirmed.
Location: Table, p. 656, first display.
Printed: \(P^n_l(x)=\frac{\Gamma(l+n+1)}{\Gamma(l-n+1)n!}(\frac{x-1}{x+1})^{n/2}F(l+1,-l;n+1;\frac{1-x}2)\) on
\((-1,1)\).
Correct: on \((-1,1)\), \(P^n_l(x)=(-1)^n\frac{(l+n)!}{(l-n)!n!}(\frac{1-x}{1+x})^{n/2}F(l+1,-l;n+1;
\frac{1-x}2)\).
Evidence: For odd \(n\) and \(x\in(-1,1)\), \((\frac{x-1}{x+1})^{n/2}\) is non-real on every branch,
while \(P^n_l\) is real; with the principal branch the printed form equals \((-i)^n\) times the
true value. Example: \(l=1\), \(n=1\), \(x=0.3\): \(P^1_1(0.3)=-\sqrt{0.91}=-0.95394\), the corrected form
gives \(-0.95394\). The printed form is the correct one for \(x>1\) (Hobson's function, p. 662).
Target: [W84.F.7.01].

### W84-EF.7.02. Schläfli integral for \(P^m_l\)

Status: Confirmed.
Location: Table, p. 656.
Printed: factor \((l-m)!\) and denominator \((t-z)^{l+m-1}\).
Correct: factor \((l+m)!\) and denominator \((t-z)^{l+m+1}\).
Evidence: Differentiating Schläfli's integral for \(P_l\) \(m\) times gives the corrected form. At
\((l,m)=(2,1)\), \(x=0.3\): printed value \(0.1302\), true \(P^1_2(0.3)=-3x\sqrt{1-x^2}=-0.8585\), corrected
form \(-0.8585\). Compare W84-E08.7.03.
Target: [W84.F.7.01].

### W84-EF.7.03. Recurrence \((2l+1)\sqrt{1-z^2}P^m_l\): sign

Status: Confirmed.
Location: Table, p. 657.
Printed: \((2l+1)(1-z^2)^{1/2}P^m_l=P^{m+1}_{l+1}-P^{m+1}_{l-1}\).
Correct: \((2l+1)(1-z^2)^{1/2}P^m_l=P^{m+1}_{l-1}-P^{m+1}_{l+1}\), with the table's convention
\(P^m_l=(-1)^m(1-z^2)^{m/2}\frac{d^m}{dz^m}P_l\).
Evidence: At \(l=2\), \(m=1\), \(z=0.3\): left side \(-4.095\), printed right side \(+4.095\). The
printed sign is correct for the convention without \((-1)^m\). Compare W84-E08.7.05.
Target: [W84.F.7.03].

### W84-EF.8.01. Mehler–Dirichlet formula: constant

Status: Confirmed.
Location: Table, p. 657.
Printed: \(P_l(\cos\theta)=\frac2\pi\int_\theta^\pi\frac{\sin(l+\frac12)t}{\sqrt{\cos^2\frac\theta2-\cos^2\frac t2}}dt\).
Correct: \(\frac2\pi\int_\theta^\pi\frac{\sin(l+\frac12)t}{\sqrt{2(\cos\theta-\cos t)}}dt=\frac1\pi\int_\theta^\pi\frac{
\sin(l+\frac12)t}{\sqrt{\cos^2\frac\theta2-\cos^2\frac t2}}dt\).
Evidence: \(2(\cos\theta-\cos t)=4(\cos^2\frac\theta2-\cos^2\frac t2)\), so the printed form is twice the
correct one; at \(l=0\) the printed integral equals \(2\) instead of \(P_0=1\). Compare W84-E08.5.01.
Target: [W84.F.8.01].

### W84-EF.8.02. Recurrence \((2l+1)zP_l'\)

Status: Confirmed.
Location: Table, p. 658.
Printed: \((2l+1)zP_l=(l+1)P_{l-1}'+lP_{l+1}'\).
Correct: \((2l+1)zP_l'=(l+1)P_{l-1}'+lP_{l+1}'\).
Evidence: At \(l=1\): \(3zP_1'=3z\) and \(2P_0'+P_2'=3z\), while \(3zP_1=3z^2\).
Target: [W84.F.8.02].

### W84-EF.10.01. Contour integral for \(\mathfrak P^l_{mn}\): exponent of \(z\)

Status: Confirmed.
Location: Table, p. 660.
Printed: exponent \(z^{m-n-1}\).
Correct: exponent \(z^{m-l-1}\).
Evidence: At \(m=n=0\), \(l=2\), \(\tau=0.9\): the corrected integral gives \(P_2(\cosh0.9)=2.5806\), the
printed one \(\frac14\sinh^20.9=0.2634\). The corrected form is the coefficient extraction from the
generating function of W84.F.10.02 and agrees with the hypergeometric forms on p. 660.
Target: [W84.F.10.01].

### W84-EF.10.02. Addition formula for \(\mathfrak P^l_{mn}\): the angle \(\varphi\)

Status: Confirmed.
Location: Table, p. 660.
Printed: \(e^{i\varphi}=\frac{\sinh\tau_1\cos\tau_2+\cosh\tau_1\sinh\tau_2\cos\gamma+i\sinh\tau_2\sin\gamma}{\sinh\frac12\tau}\).
Correct: \(e^{i\varphi}=\frac{\sinh\tau_1\cosh\tau_2+\cosh\tau_1\sinh\tau_2\cos\gamma+i\sinh\tau_2\sin\gamma}{\sinh\tau}\).
Evidence: \(|e^{i\varphi}|\) must be \(1\); at a sample point (\(\tau_1=0.7\), \(\tau_2=0.4\), \(\gamma=1\))
the printed expression has modulus \(2.023\), the corrected one modulus \(1\), and with it the
addition formula holds numerically for integer \(l\).
Target: [W84.F.10.02].

### W84-EF.12.01. Mehler integral for \(\mathfrak P_l\)

Status: Confirmed.
Location: Table, p. 663.
Printed: \(\mathfrak P_l(\cosh\tau)=\frac{\sqrt2\sin\pi l}\pi\int_0^\infty\frac{\cosh(l+\frac12)t}{\sqrt{\cosh t+\cosh\tau}}dt\),
no range of \(l\).
Correct: \(\mathfrak P_l(\cosh\tau)=-\frac{\sqrt2\sin\pi l}\pi\int_0^\infty\frac{\cosh(l+\frac12)t}{\sqrt{\cosh t+\cosh\tau}}dt\)
for \(-1<\mathrm{Re}\,l<0\).
Evidence: The integral converges only for \(|\mathrm{Re}(l+\frac12)|<\frac12\). At \(l=-0.3\), \(\tau=1\):
\(\mathfrak P_{-0.3}(\cosh1)=0.95020\), the printed form gives \(-0.95020\).
Target: [W84.F.12.01].

### W84-EF.13.01. Laguerre generating function: argument

Status: Confirmed.
Location: Table, p. 664.
Printed: \(e^{-\lambda z}(z+1)^m=\sum_nL^{m-n}_n(z)z^n\).
Correct: \(e^{-\lambda z}(1+z)^m=\sum_nL^{m-n}_n(\lambda)z^n\).
Evidence: Comparing coefficients of \(z^1\): \(m-\lambda=L^{m-1}_1(\lambda)\). The printed form has
\(L^{m-1}_1(z)=m-z\) as a coefficient depending on \(z\), and is not a power series identity.
Target: [W84.F.13.01].

### W84-EF.13.02. Second Laguerre addition formula

Status: Confirmed.
Location: Table, p. 664.
Printed: \(\sum_l(\frac xy)^lL^{m-l}_l(x^2)L^{l-n}_n(y^2)=(1+\frac yx)^m(1+\frac xy)^ne^{-xy}L^{m-n}_n((x-y)^2)\).
Correct: the real form of the (correct) third formula, obtained by \(y\mapsto iy\):
\(\sum_l(\frac yx)^lL^{m-l}_l(x^2)L^{l-n}_n(-y^2)=(1+\frac yx)^m(1+\frac xy)^{-n}e^{-xy}L^{m-n}_n(x^2-y^2)\).
Evidence: At \(m=2\), \(n=1\), \(x=0.6\), \(y=0.9\): printed left side \(-0.546\), printed right side
\(11.59\). The corrected identity gives \(5.35400\) on both sides there (and holds at \((m,n,x,y)=
(3,2,0.7,0.4)\), \((1,0,0.5,1.3)\)).
Target: [W84.F.13.02].

### W84-EF.13.03. Laguerre derivative relation

Status: Confirmed.
Location: Table, p. 665.
Printed: \(x\frac d{dx}L^k_n+(k-n)L^k_n=(n+1)L^{k-1}_{n+1}\).
Correct: \(x\frac d{dx}L^k_n=nL^k_n-(n+k)L^k_{n-1}\), equivalently \(x\frac d{dx}L^k_n+kL^k_n=(n+k)L^{k-1}_n\).
Evidence: At \(n=0\), \(k=1\): left side \(1\), right side \(L^0_1(x)=1-x\). The corrected relations
hold identically (DLMF 18.9.14, 18.9.13).
Target: [W84.F.13.03].

### W84-EF.13.04. Laguerre orthogonality constant

Status: Confirmed.
Location: Table, p. 665.
Printed: \(\int_0^\infty e^{-r}r^kL^k_mL^k_ndr=\frac{n!}{(n+k)!}\delta_{mn}\).
Correct: \(\frac{\Gamma(n+k+1)}{n!}\delta_{mn}\).
Evidence: At \(k=1\), \(n=1\): \(L^1_1=2-r\), \(\int_0^\infty e^{-r}r(2-r)^2dr=2\); the printed constant
is \(\frac12\).
Target: [W84.F.13.03].

### W84-EF.14.01. Explicit sum for \(H_n\): sign

Status: Confirmed.
Location: Table, p. 666.
Printed: \(H_n(x)=n!\sum_m\frac{(-1)^n(2x)^{n-2m}}{m!(n-2m)!}\).
Correct: \(H_n(x)=n!\sum_m\frac{(-1)^m(2x)^{n-2m}}{m!(n-2m)!}\).
Evidence: At \(n=1\) the printed sum gives \(-2x\); \(H_1=2x\) by the Rodrigues formula.
Target: [W84.F.14.01].

### W84-EF.14.02. \(H_{2m+1}\) in terms of Laguerre polynomials

Status: Confirmed.
Location: Table, p. 666.
Printed: \(H_{2m+1}(x)=(-1)^m2^{2m+1}m!\,xL^{-1/2}_m(x^2)\).
Correct: \(H_{2m+1}(x)=(-1)^m2^{2m+1}m!\,xL^{1/2}_m(x^2)\).
Evidence: At \(m=1\), \(x=0.7\): \(H_3(0.7)=8x^3-12x=-5.656\); the corrected form gives \(-5.656\), the
printed \(-0.056\).
Target: [W84.F.14.01].

### W84-EF.16.01. Mellin transform in terms of the Fourier transform

Status: Confirmed.
Location: Table, p. 667.
Printed: \(\mathcal Mf(z)=\frac{\Gamma(z)}{2\pi}e^{-i\pi z/2}\int_{-\infty}^\infty f(x)x^{-z}dx\) (\(f\) supported in
\(\mathbb R_+\)).
Correct: \(\mathcal Mf(z)=\frac{\Gamma(z)}{2\pi}\int_{\mathbb R}\hat f(x)(ix)^{-z}dx\) for \(0<\mathrm{Re}z<1\)
(principal branch; equivalently \(e^{-i\pi z/2}(x-i0)^{-z}\)), \(\hat f\) the Fourier transform.
Evidence: With \(f\) as printed the right side is \(\frac{\Gamma(z)}{2\pi}e^{-i\pi z/2}\mathcal Mf(1-z)\); at
\(z=\frac12\) and \(f\ge0\), \(f\ne0\), this would force \(\frac{\sqrt\pi e^{-i\pi/4}}{2\pi}=1\). The corrected
form is (6.2.5) of the source with the range corrected in W84-E06.2.01.
Target: [W84.F.16.01].

### W84-EF.20.01. Zonal expansion on the sphere

Status: Confirmed.
Location: Table, p. 669.
Printed: kernel \(P_l(\cos\theta\cos\theta_1-\sin\theta\sin\theta_1\cos(\varphi_1-\varphi))\) and measure
\(d\theta_1d\varphi_1\).
Correct: kernel \(P_l(\cos\theta\cos\theta_1+\sin\theta\sin\theta_1\cos(\varphi_1-\varphi))\) (the cosine of the
angle between the two points) and measure \(\sin\theta_1\,d\theta_1d\varphi_1\).
Evidence: For \(f(\varphi,\theta)=e^{\cos\theta}+\sin\theta\cos\varphi\) at \((\varphi,\theta)=(0.5,1)\), where
\(f=2.45499\), the corrected expansion truncated at \(l=8\) gives \(2.45499\); the printed kernel with
the weight \(\sin\theta_1\) gives \(0.97807\), and with neither correction \(1.92979\).
Target: [W84.F.20.01].

### W84-EF.22.01. Jacobi polynomials are not orthonormal

Status: Confirmed.
Location: Table, p. 670, system I.
Printed: \(\{P^{(\alpha,\beta)}_n\}\) is a complete orthonormal system in
\(L^2([-1,1],(1-x)^\alpha(1+x)^\beta dx)\).
Correct: \(\{h_n^{-1/2}P^{(\alpha,\beta)}_n\}\) is orthonormal, with \(h_n\) as in W84.F.22.01.
Evidence: For \(\alpha=\beta=0\), \(\int_{-1}^1P_0^2dx=2\).
Target: [W84.F.22.01].

### W84-EF.22.02. System II: normalizing factor

Status: Confirmed.
Location: Table, p. 670, system II.
Printed: \(\frac{(2l+k+1)\,k!^{1/2}}{2(2l+k)}P^l_{l+k}\).
Correct: \(\big[\frac{(2l+2k+1)k!}{2(2l+k)!}\big]^{1/2}P^l_{l+k}\).
Evidence: At \(l=0\), \(k=1\) the printed factor is \(1\), but \(\int_{-1}^1P_1^2=\frac23\). The corrected
factor is \([\frac{2n+1}2\frac{(n-l)!}{(n+l)!}]^{1/2}\) for \(n=l+k\), the standard norm of \(P^l_n\).
Target: [W84.F.22.01].

### W84-EF.23.01. Mehler–Fock transform: weight and constants

Status: Confirmed.
Location: Table, pp. 670–671.
Printed: the forward transform \(\tilde f(\nu)=\int_0^\infty f(t)\mathfrak P_{i\nu-\frac12}(\cosh t)dt\) without
the weight \(\sinh t\), and the inversion and Plancherel formulas with a factor \(\frac1{2\pi}\).
Correct: \(\tilde f(\nu)=\int_0^\infty f(t)\mathfrak P_{i\nu-\frac12}(\cosh t)\sinh t\,dt\),
\(f(\tau)=\int_0^\infty\tilde f(\nu)\mathfrak P_{-i\nu-\frac12}(\cosh\tau)\nu\tanh(\pi\nu)d\nu\) and
\(\int|f|^2\sinh\tau\,d\tau=\int|\tilde f|^2\nu\tanh(\pi\nu)d\nu\), without \(\frac1{2\pi}\).
Evidence: For \(f(t)=\cosh^{-3}t\) at \(\tau=0.8\): \(f(\tau)=0.418006\); the corrected pair returns
\(0.418006\); with the factor \(\frac1{2\pi}\) it returns \(0.0665\); without the weight \(\sinh t\) it
returns \(0.663\) (with constant 1).
Target: [W84.F.23.01].

### Conventions and notation (not errata)

- p. 667, Mellin–Plancherel: printed \(\mathcal Mf(iy)^2\) is read as \(|\mathcal Mf(iy)|^2\).
- p. 666, Hermite orthogonality: "\(H_nH_n\)" is read as \(H_mH_n\).
- p. 664, first Laguerre addition formula: the right-hand exponent printed \(m-k\) is \(m-n\).
- p. 656: a lower parameter printed "\(n+l\)" is ambiguous in print; the verified reading is used.
- p. 650: in the series for \(J_n\) the factorial "\((n+l)!\)" may read as "\((n+1)!\)" in the scan;
  the correct \((n+l)!\) is used.
- The table uses \(P^m_l\) with the factor \((-1)^m\) on \((-1,1)\) and Hobson's convention
  (no \((-1)^m\), \((z^2-1)^{m/2}\)) on \((1,\infty)\).
- Formulas marked "(as printed)" in the synopsis were not independently verified.

[W84.01.1.03]: SYNOPSIS-Wawrzynczyk1984.md#w8401103-homomorphisms-and-automorphisms
[W84.01.3.02]: SYNOPSIS-Wawrzynczyk1984.md#w8401302-lie-subgroups
[W84.01.4.01]: SYNOPSIS-Wawrzynczyk1984.md#w8401401-lie-transformation-groups-and-the-coset-manifold
[W84.01.4.04]: SYNOPSIS-Wawrzynczyk1984.md#w8401404-fundamental-vector-fields-of-an-action
[W84.01.4.05]: SYNOPSIS-Wawrzynczyk1984.md#w8401405-generators-for-sl2mathbb-r-on-p1mathbb-r-motions-of-the-plane
[W84.01.4.08]: SYNOPSIS-Wawrzynczyk1984.md#w8401408-the-invariant-area-form-on-s2
[W84.01.5.03]: SYNOPSIS-Wawrzynczyk1984.md#w8401503-problems-of-15-lie-groups-and-invariant-forms
[W84.01.6.07]: SYNOPSIS-Wawrzynczyk1984.md#w8401607-the-algebra-l1g-and-convolution-inequalities
[W84.01.8.01]: SYNOPSIS-Wawrzynczyk1984.md#w8401801-nilpotent-solvable-semisimple-and-simple-lie-algebras
[W84.01.8.05]: SYNOPSIS-Wawrzynczyk1984.md#w8401805-problems-of-18
[W84.02.5.04]: SYNOPSIS-Wawrzynczyk1984.md#w8402504-elementary-properties-of-positive-definite-functions
[W84.02.8.01]: SYNOPSIS-Wawrzynczyk1984.md#w8402801-the-enveloping-algebra-as-differential-operators
[W84.02.8.03]: SYNOPSIS-Wawrzynczyk1984.md#w8402803-the-schrödinger-representation
[W84.03.1.09]: SYNOPSIS-Wawrzynczyk1984.md#w8403109-decomposable-and-diagonal-operators
[W84.03.2.06]: SYNOPSIS-Wawrzynczyk1984.md#w8403206-invariant-differential-operators-and-plane-wave-eigenfunctions
[W84.03.3.01]: SYNOPSIS-Wawrzynczyk1984.md#w8403301-paleywiener-theorem
[W84.03.6.07]: SYNOPSIS-Wawrzynczyk1984.md#w8403607-problem-10-poisson-kernel-and-l1-inversion-on-mathbb-r
[W84.03.6.08]: SYNOPSIS-Wawrzynczyk1984.md#w8403608-problems-1114-convolution-on-mathbb-t-riemannlebesgue-poisson-integral
[W84.03.6.09]: SYNOPSIS-Wawrzynczyk1984.md#w8403609-problem-15-mellin-transform-of-derivatives
[W84.04.4.05]: SYNOPSIS-Wawrzynczyk1984.md#w8404405-example-the-irreducible-representations-of-s_3
[W84.04.7.05]: SYNOPSIS-Wawrzynczyk1984.md#w8404705-example-harmonic-analysis-on-o2
[W84.05.1.12]: SYNOPSIS-Wawrzynczyk1984.md#w8405112-convolution-with-spherical-functions
[W84.06.2.01]: SYNOPSIS-Wawrzynczyk1984.md#w8406201-mellin-transform-via-the-fourier-transform
[W84.06.2.02]: SYNOPSIS-Wawrzynczyk1984.md#w8406202-fourier-transforms-of-x_pmz-1
[W84.06.3.03]: SYNOPSIS-Wawrzynczyk1984.md#w8406303-a-mellinbarnes-integral-and-the-beta-integral-of-the-second-kind
[W84.07.3.02]: SYNOPSIS-Wawrzynczyk1984.md#w8407302-grafs-addition-formula-and-its-specializations
[W84.07.4.01]: SYNOPSIS-Wawrzynczyk1984.md#w8407401-spherical-transform-and-inversion-on-mathbb-c
[W84.07.4.05]: SYNOPSIS-Wawrzynczyk1984.md#w8407405-problems-neumann-type-series-and-integrals
[W84.08.1.02]: SYNOPSIS-Wawrzynczyk1984.md#w8408102-derivative-formula-for-the-matrix-elements
[W84.08.1.03]: SYNOPSIS-Wawrzynczyk1984.md#w8408103-the-functions-pl_jk
[W84.08.1.05]: SYNOPSIS-Wawrzynczyk1984.md#w8408105-pl_jk-as-jacobi-polynomials
[W84.08.3.05]: SYNOPSIS-Wawrzynczyk1984.md#w8408305-addition-formulas
[W84.08.4.04]: SYNOPSIS-Wawrzynczyk1984.md#w8408404-recurrences-and-the-associated-legendre-equation-for-pl_mk
[W84.08.5.02]: SYNOPSIS-Wawrzynczyk1984.md#w8408502-mehlerdirichlet-formula
[W84.08.7.06]: SYNOPSIS-Wawrzynczyk1984.md#w8408706-problems-explicit-formulas-for-pl_rs-and-pm_l
[W84.08.7.08]: SYNOPSIS-Wawrzynczyk1984.md#w8408708-problems-associated-legendre-functions
[W84.09.2.01]: SYNOPSIS-Wawrzynczyk1984.md#w8409201-homogeneous-polynomials-and-the-maps-tau-delta
[W84.09.2.05]: SYNOPSIS-Wawrzynczyk1984.md#w8409205-harmonic-decomposition
[W84.09.2.06]: SYNOPSIS-Wawrzynczyk1984.md#w8409206-the-intertwining-projection-onto-hl
[W84.09.3.01]: SYNOPSIS-Wawrzynczyk1984.md#w8409301-gegenbauers-differential-equation
[W84.09.3.02]: SYNOPSIS-Wawrzynczyk1984.md#w8409302-derivative-and-three-term-recurrences
[W84.09.4.02]: SYNOPSIS-Wawrzynczyk1984.md#w8409402-laplace-type-integral-representation
[W84.09.4.03]: SYNOPSIS-Wawrzynczyk1984.md#w8409403-product-reproducing-formula
[W84.09.4.05]: SYNOPSIS-Wawrzynczyk1984.md#w8409405-gegenbauer-expansion-and-parseval-formula
[W84.09.5.01]: SYNOPSIS-Wawrzynczyk1984.md#w8409501-mean-value-theorem-and-the-gegenbauer-addition-type-integral
[W84.09.5.05]: SYNOPSIS-Wawrzynczyk1984.md#w8409505-problem-10-special-parameters-rodrigues-formula-generating-function
[W84.09.5.06]: SYNOPSIS-Wawrzynczyk1984.md#w8409506-problem-11-gegenbauer-polynomials-for-real-lambda-frac12
[W84.10.1.02]: SYNOPSIS-Wawrzynczyk1984.md#w8410102-iwasawa-decomposition-and-haar-measure
[W84.10.1.03]: SYNOPSIS-Wawrzynczyk1984.md#w8410103-euler-angles-cartan-decomposition
[W84.10.4.02]: SYNOPSIS-Wawrzynczyk1984.md#w8410402-irreducibility
[W84.10.4.03]: SYNOPSIS-Wawrzynczyk1984.md#w8410403-recurrence-relations-and-the-associated-legendre-equation
[W84.10.5.01]: SYNOPSIS-Wawrzynczyk1984.md#w8410501-horocyclic-coordinates
[W84.10.5.03]: SYNOPSIS-Wawrzynczyk1984.md#w8410503-inversion-of-the-abel-transform-and-the-inversion-at-the-origin
[W84.10.5.04]: SYNOPSIS-Wawrzynczyk1984.md#w8410504-plancherel-and-inversion-for-radial-functions-mehlerfock-transform
[W84.10.5.05]: SYNOPSIS-Wawrzynczyk1984.md#w8410505-extension-to-arbitrary-finmathcal-dd
[W84.10.5.06]: SYNOPSIS-Wawrzynczyk1984.md#w8410506-plane-waves-on-the-disc
[W84.10.5.07]: SYNOPSIS-Wawrzynczyk1984.md#w8410507-fourier-transform-on-the-disc-inversion-and-plancherel
[W84.10.5.08]: SYNOPSIS-Wawrzynczyk1984.md#w8410508-problems-iwasawa-components-poisson-kernel-measures
[W84.10.5.10]: SYNOPSIS-Wawrzynczyk1984.md#w8410510-problem-8-laplacebeltrami-operator-on-d
[W84.10.5.13]: SYNOPSIS-Wawrzynczyk1984.md#w8410513-problems-1418-consequences-of-the-addition-theorem-and-generating-function
[W84.11.2.03]: SYNOPSIS-Wawrzynczyk1984.md#w8411203-polar-hyperbolic-coordinates-and-the-distance
[W84.11.2.07]: SYNOPSIS-Wawrzynczyk1984.md#w8411207-invariant-measures-on-mathcal-h-and-g
[W84.11.3.02]: SYNOPSIS-Wawrzynczyk1984.md#w8411302-spherical-transform-and-its-polar-form
[W84.11.3.03]: SYNOPSIS-Wawrzynczyk1984.md#w8411303-inversion-and-plancherel-theorem-for-the-spherical-transform
[W84.11.4.02]: SYNOPSIS-Wawrzynczyk1984.md#w8411402-plane-waves-on-mathcal-h
[W84.11.4.08]: SYNOPSIS-Wawrzynczyk1984.md#w8411408-eigenfunctions-phi_nuj-and-the-spherical-harmonic-expansion
[W84.11.4.09]: SYNOPSIS-Wawrzynczyk1984.md#w8411409-radial-part-of-phi_nulm
[W84.11.4.10]: SYNOPSIS-Wawrzynczyk1984.md#w8411410-phi_nuj-as-associated-legendre-functions
[W84.11.5.01]: SYNOPSIS-Wawrzynczyk1984.md#w8411501-the-wave-operator-and-the-laplacebeltrami-operator-on-mathcal-h
[W84.11.6.01]: SYNOPSIS-Wawrzynczyk1984.md#w8411601-the-gelfandgraev-horospherical-transform
[W84.11.6.02]: SYNOPSIS-Wawrzynczyk1984.md#w8411602-dual-transform-and-inversion-formula
[W84.11.7.06]: SYNOPSIS-Wawrzynczyk1984.md#w8411706-problem-the-lie-algebra-of-the-lorentz-group
[W84.12.1.05]: SYNOPSIS-Wawrzynczyk1984.md#w8412105-matrix-elements-as-taylor-coefficients
[W84.12.1.07]: SYNOPSIS-Wawrzynczyk1984.md#w8412107-matrix-elements-of-mathcal-ulambda-for-g_1
[W84.12.2.02]: SYNOPSIS-Wawrzynczyk1984.md#w8412202-integral-representation
[W84.12.3.03]: SYNOPSIS-Wawrzynczyk1984.md#w8412303-differentialdifference-equations-for-f_nm
[W84.12.3.06]: SYNOPSIS-Wawrzynczyk1984.md#w8412306-derivative-recurrence-and-differential-equation-of-lk_n
[W84.12.4.04]: SYNOPSIS-Wawrzynczyk1984.md#w8412404-generating-function-for-the-hermite-functions
[W84.12.6.03]: SYNOPSIS-Wawrzynczyk1984.md#w8412603-formal-dimension-and-laguerre-orthogonality
[W84.12.6.06]: SYNOPSIS-Wawrzynczyk1984.md#w8412606-problem-bilinear-generating-identities-from-the-addition-formula
[W84.12.6.07]: SYNOPSIS-Wawrzynczyk1984.md#w8412607-problem-explicit-sum-for-ll_n
[W84.13.1.07]: SYNOPSIS-Wawrzynczyk1984.md#w8413107-the-riemann-p-equation-and-papperitz-form
[W84.13.1.08]: SYNOPSIS-Wawrzynczyk1984.md#w8413108-the-hypergeometric-equation-as-a-p-equation
[W84.13.1.09]: SYNOPSIS-Wawrzynczyk1984.md#w8413109-reduction-of-p-equations-to-the-hypergeometric-equation
[W84.13.1.11]: SYNOPSIS-Wawrzynczyk1984.md#w8413111-example-the-legendre-equation
[W84.13.1.12]: SYNOPSIS-Wawrzynczyk1984.md#w8413112-example-the-bessel-equation-and-bessel-functions-of-the-first-kind
[W84.13.2.04]: SYNOPSIS-Wawrzynczyk1984.md#w8413204-analytic-continuation-of-f-by-a-double-loop-integral
[W84.13.2.06]: SYNOPSIS-Wawrzynczyk1984.md#w8413206-gausss-summation-formula
[W84.13.3.03]: SYNOPSIS-Wawrzynczyk1984.md#w8413303-legendre-functions-mathfrak-pl_mn
[W84.13.4.02]: SYNOPSIS-Wawrzynczyk1984.md#w8413402-confluence-limit
[W84.13.4.03]: SYNOPSIS-Wawrzynczyk1984.md#w8413403-integral-representations-of-_1f_1
[W84.13.4.08]: SYNOPSIS-Wawrzynczyk1984.md#w8413408-problem-legendre-functions-of-the-second-kind
[W84.13.4.12]: SYNOPSIS-Wawrzynczyk1984.md#w8413412-problem-contiguous-relations-and-the-derivative
[W84.13.4.13]: SYNOPSIS-Wawrzynczyk1984.md#w8413413-problems-convergence-second-solutions-at-0-1-infty
[W84.14.3.06]: SYNOPSIS-Wawrzynczyk1984.md#w8414306-torsion-form-and-the-bracket-of-basic-fields
[W84.14.5.03]: SYNOPSIS-Wawrzynczyk1984.md#w8414503-induced-connection-on-a-hypersurface
[W84.14.7.03]: SYNOPSIS-Wawrzynczyk1984.md#w8414703-example-the-poincaré-half-plane
[W84.14.7.05]: SYNOPSIS-Wawrzynczyk1984.md#w8414705-exponential-map-in-non-positive-curvature
[W84.15.5.02]: SYNOPSIS-Wawrzynczyk1984.md#w8415502-invariant-riemannian-structures-from-riemann-pairs
[W84.15.5.07]: SYNOPSIS-Wawrzynczyk1984.md#w8415507-curvature-of-riemannian-symmetric-spaces
[W84.15.6.05]: SYNOPSIS-Wawrzynczyk1984.md#w8415605-problem-the-real-grassmannian
[W84.17.1.04]: SYNOPSIS-Wawrzynczyk1984.md#w8417104-killing-form-of-mathfrak-un-and-mathfraksun
[W84.17.2.02]: SYNOPSIS-Wawrzynczyk1984.md#w8417202-real-forms-of-mathfrakslnmathbb-c-and-mathfrak-onmathbb-c
[W84.17.5.01]: SYNOPSIS-Wawrzynczyk1984.md#w8417501-the-boundary-bkmgman
[W84.17.5.02]: SYNOPSIS-Wawrzynczyk1984.md#w8417502-fixed-point-property
[W84.17.6.07]: SYNOPSIS-Wawrzynczyk1984.md#w8417607-problems-36-cartan-subalgebras-cartan-numbers
[W84.17.6.08]: SYNOPSIS-Wawrzynczyk1984.md#w8417608-problems-78-real-forms-and-conjugacy
[W84.18.1.05]: SYNOPSIS-Wawrzynczyk1984.md#w8418105-poisson-kernel-as-a-jacobian
[W84.18.1.08]: SYNOPSIS-Wawrzynczyk1984.md#w8418108-plane-waves-and-spherical-functions-on-lobachevsky-space
[W84.18.3.03]: SYNOPSIS-Wawrzynczyk1984.md#w8418303-the-harish-chandra-homomorphism
[W84.18.4.02]: SYNOPSIS-Wawrzynczyk1984.md#w8418402-harish-chandra-series
[W84.18.5.01]: SYNOPSIS-Wawrzynczyk1984.md#w8418501-rank-one-the-radial-equation-and-the-series
[W84.18.5.04]: SYNOPSIS-Wawrzynczyk1984.md#w8418504-helgasons-gamma-product-form-of-c
[W84.18.5.05]: SYNOPSIS-Wawrzynczyk1984.md#w8418505-harish-chandras-integral-and-analytic-properties-of-c
[W84.18.6.02]: SYNOPSIS-Wawrzynczyk1984.md#w8418602-plancherel-and-inversion-for-the-helgasonfourier-transform
[W84.18.7.05]: SYNOPSIS-Wawrzynczyk1984.md#w8418705-the-operators-lambda_pm-and-helgasons-inversion-formula
[W84.18.8.03]: SYNOPSIS-Wawrzynczyk1984.md#w8418803-paleywiener-theorem
[W84.F.1.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f101-definition-and-elementary-values-of-gamma
[W84.F.1.02]: SYNOPSIS-Wawrzynczyk1984.md#w84f102-reflection-duplication-values-on-vertical-lines
[W84.F.1.03]: SYNOPSIS-Wawrzynczyk1984.md#w84f103-gausss-limit-formula
[W84.F.1.04]: SYNOPSIS-Wawrzynczyk1984.md#w84f104-the-beta-function
[W84.F.10.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f1001-definition-and-contour-integral
[W84.F.10.02]: SYNOPSIS-Wawrzynczyk1984.md#w84f1002-addition-formulas-and-generating-function
[W84.F.12.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f1201-representations-addition-theorem-equation
[W84.F.13.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f1301-rodrigues-formula-and-generating-functions
[W84.F.13.02]: SYNOPSIS-Wawrzynczyk1984.md#w84f1302-addition-formulas
[W84.F.13.03]: SYNOPSIS-Wawrzynczyk1984.md#w84f1303-recurrences-equation-orthogonality-explicit-form
[W84.F.14.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f1401-definition-and-properties
[W84.F.16.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f1601-mellin-inversion-and-plancherel-relation-to-the-fourier-transform
[W84.F.2.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f201-definition-mellin-representation-euler-product
[W84.F.20.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f2001-spherical-harmonics
[W84.F.22.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f2201-orthonormal-bases-of-polynomials
[W84.F.23.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f2301-mehlerfock-inversion-and-plancherel
[W84.F.3.02]: SYNOPSIS-Wawrzynczyk1984.md#w84f302-integral-representations-and-gausss-sum
[W84.F.3.03]: SYNOPSIS-Wawrzynczyk1984.md#w84f303-elementary-properties
[W84.F.6.02]: SYNOPSIS-Wawrzynczyk1984.md#w84f602-the-functions-pl_kj-closed-forms
[W84.F.7.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f701-explicit-forms
[W84.F.7.03]: SYNOPSIS-Wawrzynczyk1984.md#w84f703-recurrences-and-the-associated-legendre-equation
[W84.F.8.01]: SYNOPSIS-Wawrzynczyk1984.md#w84f801-explicit-forms-and-integral-representations
[W84.F.8.02]: SYNOPSIS-Wawrzynczyk1984.md#w84f802-recurrences-and-legendres-equation
