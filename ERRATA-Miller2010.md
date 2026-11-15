# Errata and source checks: Miller 2010

Reference: Willard Miller, Jr., *The Lie theory approach to special functions*, lecture notes,
University of Minnesota, dated November 5, 2010; 57 printed pages. The local copy is
[References/Miller2010LieTheoryApproachSpecialFunctions-LectureNotesUnivMinnesota.pdf](References/Miller2010LieTheoryApproachSpecialFunctions-LectureNotesUnivMinnesota.pdf).
Synopsis: [SYNOPSIS-Miller2010](SYNOPSIS-Miller2010.md).

Locators use printed page numbers. To get the one-based PDF page number, add 1 (the PDF has an
unnumbered title page). Line numbers, where given, count from the top of the printed page;
negative line numbers count from the bottom.

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
- the location, as chapter or section, printed page and equation or position;
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries.

Synopsis entries cite errata by id. An erratum id M10-Ecc.s.nn is the nn-th erratum located in
section s of chapter cc (s = 0 for material before the first section of a chapter and for
chapters without sections).

## Scope

These are observations about this version of the lecture notes, not an official list. No claim
is made that formulas without an erratum are free of errors. Formulas that the synopsis marks
"as printed" were transcribed from the page images without an independent check. Corrected
formulas in the synopsis are statements to be formalized. They are not Lean proofs. Garbling
of the PDF text layer is not an erratum; every erratum below was checked on the page image.

Each chapter section ends with a list of conventions and notation that are not errata, for
example a sign convention that differs from a modern reference.

## Summary by chapter

- Chapter 1. Preliminaries: 12 entries, 1 erratum (Confirmed 1).
- Chapter 2. Special functions as matrix elements: 22 entries, 6 errata (Confirmed 6).
- Chapter 3. Symmetries of differential equations: 15 entries, 10 errata (Confirmed 10).
- Chapter 4. Symmetry characterization of variable separation for the Helmholtz and Schrödinger equations: 22 entries, 6 errata (Confirmed 6).
- Chapter 5. Clebsch–Gordan coefficients and orthogonal polynomials: 6 entries, 5 errata (Confirmed 5).
- Chapter 6. Harmonic analysis and lattice subgroups: 15 entries, 1 erratum (Confirmed 1).
- Chapter 7. Significant research opportunities and challenges: 1 entry, 0 errata.
- Total: 93 entries, 29 errata (Confirmed 29).

## Chapter 1. Preliminaries

### M10-E01.3.01. Representations into bounded operators need not be unital

Status: Confirmed.
Location: §1.3, p. 9, Definition 5 and (1.1)–(1.2).
Printed: a representation is a homomorphism \(g\mapsto\mathbf T(g)\) of \(G\) into the space of
bounded linear operators on \(V\); "it follows that" \(\mathbf T(g)^{-1}=\mathbf T(g^{-1})\) and
\(\mathbf T(e)=I\).
Correct: the homomorphism must take values in the group of bounded invertible operators (or
\(\mathbf T(e)=I\) must be required); then (1.1)–(1.2) follow.
Evidence: \(\mathbf T(g)=0\) for all \(g\) (or \(\mathbf T(g)=P\), a fixed projection
\(\ne0,I\)) is a multiplicative map into the bounded operators with \(\mathbf T(e)\ne I\) and
\(\mathbf T(g)\) not invertible.
Target: [M10.01.3.01].

### Conventions and notation (not errata)

- p. 9, Definition 7: "proper subspace" means a closed invariant subspace other than \(\{0\}\)
  and \(V\), as the following sentence makes clear ([M10.01.3.01]).
- p. 10, §1.4: \(N\) (not defined in the text) is the order of \(G\) ([M10.01.4.01]).
- p. 9, Definition 6: \(GL(\infty,\mathbb C)\) is informal (invertible infinite matrices).

## Chapter 2. Special functions as matrix elements

### M10-E02.1.01. Explicit Euler-angle matrix

Status: Confirmed.
Location: §2.1, p. 14, display of \(R_z(\varphi)R_x(\theta)R_z(\psi)\).
Printed: an array whose first row is \(\cos\varphi\cos\psi-\sin\varphi\sin\psi\cos\theta\),
\(\sin\varphi\cos\psi+\cos\varphi\sin\psi\cos\theta\), \(\sin\psi\sin\theta\); the second row
contains four entries \(-\cos\varphi\sin\psi-\sin\varphi\cos\psi\cos\theta\),
\(\sin\varphi\sin\theta\), \(-\sin\varphi\sin\psi+\cos\varphi\cos\psi\cos\theta\),
\(-\cos\varphi\sin\theta\), and the third row two entries \(\cos\psi\sin\theta\), \(\cos\theta\).
Correct: the matrix of [M10.02.1.02]; its first row is
\((\cos\varphi\cos\psi-\sin\varphi\sin\psi\cos\theta,\ -\cos\varphi\sin\psi-\sin\varphi\cos\psi
\cos\theta,\ \sin\varphi\sin\theta)\) and its third row \((\sin\psi\sin\theta,\ \cos\psi\sin
\theta,\ \cos\theta)\).
Evidence: direct multiplication of the three matrices of p. 13. The printed entries are those
of the transpose \(A^t=A^{-1}\), with the entries \(\sin\varphi\sin\theta\) and
\(-\cos\varphi\sin\theta\) of its third row and the entry \(\cos\psi\sin\theta\) of its second
row displaced; e.g. the printed \((1,2)\) entry \(\sin\varphi\cos\psi+\cos\varphi\sin\psi\cos
\theta\) is the \((2,1)\) entry of the product (at \(\theta=0\) the product is
\(R_z(\varphi+\psi)\), whose \((1,2)\) entry is \(-\sin(\varphi+\psi)\)).
Target: [M10.02.1.02].

### M10-E02.1.02. Hypergeometric parameters in the \(SO(3)\) matrix elements

Status: Confirmed.
Location: §2.1, p. 14, first line of the display for \(T^\ell_{km}(\varphi,\theta,\psi)\).
Printed: \(\ldots\frac{[\sin\theta]^{m-k}(1+\cos\theta)^{\ell+k-m}}{2^\ell\Gamma(m-k+1)}\,
{}_2F_1\bigl(-\ell,-k;\,m-1;\,\frac{\cos\theta-1}{\cos\theta+1}\bigr)\).
Correct: \({}_2F_1\bigl(-\ell-k,\,m-\ell;\,m-k+1;\,\frac{\cos\theta-1}{\cos\theta+1}\bigr)\), with
the prefactor unchanged.
Evidence: for \(k=m=0\) the printed formula gives \(((1+\cos\theta)/2)^\ell\), since an upper
parameter \(-k=0\) makes the \({}_2F_1\) equal to 1, whereas the source itself states
\(T^\ell_{00}=P_\ell(\cos\theta)\) (p. 15); for \(\ell=1\) this is \((1+\cos\theta)/2\ne\cos
\theta\). The corrected formula agrees with the generating function of p. 14 for all
\(\ell\le2\), \(m\ge k\), at \((\varphi,\theta,\psi)=(0.3,0.7,-0.4)\) (e.g. \(\ell=2\), \(k=-1\),
\(m=1\): both give \(-0.227493+0.191615i\)), and with \(T^\ell_{00}=P_\ell(\cos\theta)\).
Target: [M10.02.1.04].

### M10-E02.2.01. Spin of the \(SU(2)\) restriction

Status: Confirmed.
Location: §2.2, p. 17, paragraph after the addition theorem.
Printed: "\(D_{0m}(\phi,\theta,\psi)\sim Y^m_\ell(\theta,\phi)\) is a spherical harmonic, where
\(\ell=2u\)."
Correct: \(\ell=u\) (for integral \(u\)); the matrix elements involved are those with the
weight-zero index, i.e. index \(j=u\) in the basis \(z^j\), \(0\le j\le2u\).
Evidence: \(T_u\) has dimension \(2u+1\), while the \(SO(3)\) representation containing
\(Y^m_\ell\) has dimension \(2\ell+1\); \(\ell=2u\) would give dimension \(4u+1\). For
half-integral \(u\) the representation does not factor through \(SO(3)\) at all
(\(T_u(-I)=(-1)^{2u}I\)).
Target: [M10.02.2.03].

### M10-E02.2.02. Unitarity range of the holomorphic \(SU(1,1)\) representations

Status: Confirmed.
Location: §2.2, p. 18, lines 1–6.
Printed: restricted to \(SU(1,1)\), "the representation is unitary and irreducible for \(u=n\)
where \(2n\) is a positive integer."
Correct: \(u=-n\) with \(2n\) a positive integer (more generally \(2u=-\kappa\), \(\kappa>0\),
on the universal cover), with \(\langle z^j,z^k\rangle=\delta_{jk}j!/(\kappa)_j\).
Evidence: the representation is defined on p. 17 only for \(2u\notin\{0,1,2,\dots\}\), so
\(u=n\), \(2n\in\{1,2,\dots\}\), is excluded by the source itself; for such \(u\) the
polynomials of degree \(\le2u\) form a finite-dimensional invariant subspace. For
\(\kappa=2,3\) and \(a=\sqrt{1.16}e^{0.3i}\), \(b=0.4e^{1.1i}\) the normalized matrix
\(B_{\ell j}[(\kappa)_\ell j!/(\ell!(\kappa)_j)]^{1/2}\) has orthonormal columns (checked for
\(j,k\le3\), sums truncated at \(\ell<200\)).
Target: [M10.02.2.05].

### M10-E02.2.03. Signed Mellin inversion for \(x<0\)

Status: Confirmed.
Location: §2.2, p. 19, inversion formula.
Printed: \(f(x)=\frac1{2\pi i}\int_{a-i\infty}^{a+i\infty}f_+(\lambda)(-x)^{-\lambda}d\lambda\)
for \(x<0\) (and \(f_+\) for \(x>0\)).
Correct: \(F_-(\lambda)\) for \(x<0\) and \(F_+(\lambda)\) for \(x>0\).
Evidence: \(F_+\) depends only on \(f|_{(0,\infty)}\), so it cannot determine \(f\) on
\((-\infty,0)\): for \(f\) supported in \((-\infty,0)\), \(F_+\equiv0\) while \(f\ne0\).
Target: [M10.02.2.09].

### M10-E02.2.04. Arguments in the kernel addition theorem

Status: Confirmed.
Location: §2.2, p. 19, "Addition theorems", left-hand matrix.
Printed: left side
\(\begin{pmatrix}K_{++}(\lambda,\mu;u;AB)&K_{+-}(\lambda,\mu;u;A)\\K_{-+}(\lambda,\mu;u;A)&
K_{--}(\lambda,\mu;u;A)\end{pmatrix}\).
Correct: all four entries have argument \(AB\).
Evidence: with \(A=I\) the right side is the kernel matrix of \(B\) (the kernel of \(I\) being the
identity), while the printed \((1,2)\) entry is \(K_{+-}(\lambda,\mu;u;I)=0\); for
\(B=\begin{pmatrix}0&-1\\1&0\end{pmatrix}\), which exchanges the half-lines, \(K_{+-}(B)\ne0\).
Target: [M10.02.2.10].

### Conventions and notation (not errata)

- p. 14: \(T^\ell_{km}=\langle\mathbf T(A)v_m,v_k\rangle\); the symbols \(P^{a,b}_\ell\) are
  defined implicitly by the display of p. 14 and satisfy \(P^{0,-m}_\ell=P^m_\ell\) with the
  Ferrers–Condon–Shortley sign \((-1)^m\) included in \(P^m_\ell\) ([M10.02.1.04],
  [M10.02.1.08]). The relations of p. 15 (symmetry, bound, \(T^\ell_{0m}\), orthogonality
  integral) were checked numerically for \(\ell\le3\) with the generating function as definition.
- p. 15: the orthogonality integral uses \(P^{k,m}_\ell\) (not \(P^{-k,m}_\ell\)); this is the
  same family with \(k\) replaced by \(-k\), and is correct as printed.
- p. 14: \(\beta=ie^{i(\phi-\psi)/2}\sin\frac\theta2\) uses \(\phi\) for \(\varphi\).
- p. 16: "\(\mathrm{trace}(A)=0\)" refers to the Lie algebra element \(\mathcal A\).
- p. 18, Example 2: the branch of \((bx+d)^{2u}\) for \(bx+d<0\) is not specified; the
  synopsis uses \(|bx+d|^{2u}\) times a character of the sign ([M10.02.2.08]).
- p. 19: the kernels \(K_{\pm\pm}\) include the factor \(1/(2\pi i)\) of the inversion formula,
  so the integrals over \(\mu\) and \(\nu\) carry \(d\mu\), \(d\nu\) only; \(K_{++}\) for the
  hyperbolic rotation was checked by numerical integration (e.g. \(\lambda=0.45\),
  \(\mu=-0.3\), \(u=-0.8\), \(\theta=1.7\): both sides \(0.3979478724\)).
- p. 17: "\(f\) analytic" in the infinite-dimensional models means analytic near \(z=0\); the
  addition theorem for \(B_{\ell j}\) is local ([M10.02.2.04]).

## Chapter 3. Symmetries of differential equations

### M10-E03.0.01. Symmetry operators and commutation

Status: Confirmed.
Location: Chapter 3, p. 20, Definition 8.
Printed: "\(S\) is a symmetry operator for \(D\Phi=\lambda\Phi\) if \(S\) maps local solutions
\(\Phi\) to local solutions \(S\Phi\). This is basically equivalent to the requirement that
\([S,D]=0\)."
Correct: \([S,D]=0\) is sufficient but not necessary; a sufficient condition covering the
general case is \((D-\lambda)S=R(D-\lambda)\) for some differential operator \(R\).
Evidence: \(D=\partial_x\), \(\lambda=0\), \(S=x\partial_x\): \(S\) maps every solution
(a constant) to \(0\), a solution, but \([D,S]=\partial_x\ne0\).
Target: [M10.03.0.01].

### M10-E03.1.01. Signs in the \(\partial_{u_1}\), \(\partial_{u_2}\) recurrences

Status: Confirmed.
Location: §3.1, p. 22, first display.
Printed: \(\partial_{u_1}\Phi\binom{\alpha,\beta}\gamma=\alpha\Phi\binom{\alpha+1,\beta}\gamma\),
\(\partial_{u_2}\Phi\binom{\alpha,\beta}\gamma=\beta\Phi\binom{\alpha,\beta+1}\gamma\).
Correct: \(-\alpha\Phi\binom{\alpha+1,\beta}\gamma\) and \(-\beta\Phi\binom{\alpha,\beta+1}\gamma\).
Evidence: termwise, \(\Phi=\sum_kc_ku_1^{-\alpha-k}u_2^{-\beta-k}u_3^{\gamma-1+k}u_4^k\) with
\(c_k=\frac{(\alpha)_k(\beta)_k}{(\gamma)_kk!}\), and \(\partial_{u_1}\) multiplies the \(k\)-th
term by \(-(\alpha+k)\), while \((\alpha+k)(\alpha)_k=\alpha(\alpha+1)_k\). At \(u_4=0\):
\(\partial_{u_1}(u_1^{-\alpha}u_2^{-\beta}u_3^{\gamma-1})=-\alpha u_1^{-\alpha-1}u_2^{-\beta}
u_3^{\gamma-1}\).
Target: [M10.03.1.02].

### M10-E03.1.02. Symmetry group of the wave equation

Status: Confirmed.
Location: §3.1, p. 22, bullet: "Here the full local symmetry group is \(SL(6)\)."
Printed: \(SL(6)\).
Correct: the conformal symmetry algebra of the four-dimensional complex wave equation is
\(\mathfrak{so}(6,\mathbb C)\cong\mathfrak{sl}(4,\mathbb C)\) (dimension 15); with the identity
operator adjoined, \(\mathfrak{gl}(4,\mathbb C)\) (dimension 16). The local group is
\(SL(4,\mathbb C)\) (up to coverings and the scalar factor).
Evidence: the source's own list has 4 operators \(\partial_{u_j}\), 3 dilation combinations and
8 further conformal symmetries, 15 in all, besides the identity; \(\dim\mathfrak{sl}(6,\mathbb C)
=35\). The conformal algebra of the Laplace equation in \(n\) complex variables is
\(\mathfrak{so}(n+2,\mathbb C)\), of dimension \((n+2)(n+1)/2=15\) for \(n=4\).
Target: [M10.03.1.03].

### M10-E03.1.03. Factor in the raising recurrence for Jacobi polynomials

Status: Confirmed.
Location: §3.1, p. 22, last display.
Printed: \([(x^2-1)\frac d{dx}+(\alpha-\beta+(\alpha+\beta+2)x)]P^{(\alpha+1,\beta+1)}_{n-1}(x)
=nP^{(\alpha,\beta)}_n(x)\).
Correct: right side \(2nP^{(\alpha,\beta)}_n(x)\).
Evidence: \(\alpha=\beta=0\), \(n=1\): \(P^{(1,1)}_0=1\), so the left side is \(2x\), while
\(P_1^{(0,0)}=x\). Symbolic check for \(n=1,2,3\) with general \(\alpha,\beta\).
Target: [M10.03.1.05].

### M10-E03.1.04. Constant term of \(P^{(\alpha,\beta)}_1\)

Status: Confirmed.
Location: §3.1, p. 23, line 4.
Printed: \(P^{(\alpha,\beta)}_1(x)=\frac{\alpha+\beta}2+\frac12(\alpha+\beta+2)x\).
Correct: \(P^{(\alpha,\beta)}_1(x)=\frac{\alpha-\beta}2+\frac12(\alpha+\beta+2)x\).
Evidence: from the definition on p. 23,
\(P_1=(\alpha+1)\bigl(1-\frac{\alpha+\beta+2}{\alpha+1}\frac{1-x}2\bigr)=\frac{\alpha-\beta}2+
\frac{\alpha+\beta+2}2x\); the printed version fails the reflection
\(P_1^{(\alpha,\beta)}(-x)=-P_1^{(\beta,\alpha)}(x)\) and orthogonality: for \(\alpha=0\), \(\beta=1\), \(\int_{-1}^1(-\frac12+\frac32x)(1+x)\,dx=0\), whereas the printed \(\frac12+\frac32x\) gives \(\int_{-1}^1(\frac12+\frac32x)(1+x)\,dx=2\).
Target: [M10.03.1.04].

### M10-E03.1.05. Sign in the Jacobi differential equation

Status: Confirmed.
Location: §3.1, p. 23, display after "standard Sturm–Liouville eigenvalue equation".
Printed: \((1-x^2)P''_n+[\beta-\alpha-(\alpha+\beta+2)x]P'_n=n(\alpha+\beta+n+1)P_n\).
Correct: right side \(-n(\alpha+\beta+n+1)P^{(\alpha,\beta)}_n\).
Evidence: \(\alpha=\beta=0\), \(n=1\), \(P_1=x\): the left side is \(-2x\), the printed right side
\(2x\).
Target: [M10.03.1.06].

### M10-E03.1.06. Eigenvalues of \(\tau^*\tau\)

Status: Confirmed.
Location: §3.1, p. 24, display "\(\lambda_n=n(\alpha+\beta+n-1)\)".
Printed: \(\lambda_n=n(\alpha+\beta+n-1)\).
Correct: \(\lambda_n=n(\alpha+\beta+n+1)\).
Evidence: by the two recurrences (corrected as in [M10-E03.1.03]),
\(\tau^*\tau P_n=\frac{n+\alpha+\beta+1}2\cdot2nP_n\); for \(\alpha=\beta=0\), \(n=1\):
\(\tau^*\tau x=(x^2-1)\cdot0+2x\cdot1=2x\), so \(\lambda_1=2\), not \(0\). Also
\(\tau^*\tau=-(\text{operator of the Jacobi equation})\), consistent with [M10-E03.1.05].
Target: [M10.03.1.08].

### M10-E03.1.07. Parity factor in the Jacobi reflection

Status: Confirmed.
Location: §3.1, p. 24, last display.
Printed: \(P^{(\alpha,\beta)}_n(-x)=P^{(\beta,\alpha)}_n(x)\).
Correct: \(P^{(\alpha,\beta)}_n(-x)=(-1)^nP^{(\beta,\alpha)}_n(x)\).
Evidence: \(\alpha=\beta=0\), \(n=1\): \(P_1(-x)=-x\ne x\). The Gram–Schmidt argument of the
source fixes the polynomials only up to their leading coefficients, which change by
\((-1)^n\) under \(x\mapsto-x\).
Target: [M10.03.1.09].

### M10-E03.1.08. Recurrence for the Jacobi norms

Status: Confirmed.
Location: §3.1, p. 25, first display.
Printed: \(\frac12(\alpha+\beta+n+1)M_{n-1}(\alpha+1,\beta+1)=-nM_n(\alpha,\beta)\).
Correct: right side \(2nM_n(\alpha,\beta)\).
Evidence: both norms are positive for \(\alpha,\beta>-1\), so the printed sign is impossible.
Legendre, \(n=1\): \(M_0(1,1)=\int_{-1}^1(1-x^2)dx=\frac43\), left side \(\frac43\);
\(M_1(0,0)=\frac23\), so \(2nM_1=\frac43\) while \(-nM_1=-\frac23\). The factor 2 comes from
\(\tau^*P^{(\alpha+1,\beta+1)}_{n-1}=2nP^{(\alpha,\beta)}_n\).
Target: [M10.03.1.10].

### M10-E03.1.09. Pointwise limit in the Stirling argument

Status: Confirmed.
Location: §3.1, pp. 25–26, display with \(k\to\infty\) and the sentence following it.
Printed: "Letting \(k\to+\infty\) we find from Stirling's formula that the integrand of the
left-hand side converges to 1 and that \(h(\alpha,\beta)\equiv2\)."
Correct: the integrand does not converge to 1; it tends to \(0\) for every \(x\ne0\) and to
\(+\infty\) at \(x=0\). The conclusion \(h\equiv2\) is true; it follows by Laplace's method (the
integrand is asymptotic to \(2\sqrt{k/\pi}\,e^{-kx^2}\) near \(x=0\), with integral tending to 2)
or from the beta integral.
Evidence: \(\alpha=\beta=0\): the integrand is \(\bigl(\frac{1-x^2}4\bigr)^k\frac{(2k+1)!}{(k!)^2}\);
at \(x=\frac12\) it is \((3/16)^k(2k+1)!/(k!)^2\sim2\sqrt{k/\pi}\,(3/4)^k\to0\), at \(x=0\) it is
\(\sim2\sqrt{k/\pi}\to\infty\), and its integral equals 2 for every \(k\).
Target: [M10.03.1.11].

### Conventions and notation (not errata)

- p. 23: \(\langle g_1,g_2\rangle_{\alpha,\beta}=\int g_1g_2\rho_{\alpha,\beta}\) is called a
  "complex inner product" but is bilinear; since \(\tau,\tau^*\) have real coefficients, the
  arguments hold equally for the Hermitian form ([M10.03.1.07]).
- p. 20, Definition 8: the conformal symmetry \(\tilde S\) maps \(\Phi\) to "\(S\Phi\)" (for
  \(\tilde S\Phi\)).
- p. 22: the eight conformal symmetries are named but not displayed; the example
  \(E_{\alpha\beta\gamma}\Phi=(\gamma-1)\Phi\binom{\alpha-1,\beta-1}{\gamma-1}\) is recorded as
  printed ([M10.03.1.03]).
- p. 25: the general Jacobi norm \(M_n\) is not stated; the synopsis supplies it
  ([M10.03.1.10]).

## Chapter 4. Symmetry characterization of variable separation for the Helmholtz and Schrödinger equations

### M10-E04.2.01. First-order symmetries for arbitrary parameters

Status: Confirmed.
Location: §4.2, p. 36, Remark 4.
Printed: "For \(\gamma_1,\dots,\gamma_{n+1}\) arbitrary, the only first order symmetry is
multiplication by a constant."
Correct: this holds for generic \(\gamma\), not for all \(\gamma\).
Evidence: Remark 2 on the same page: for \(\gamma_1=\dots=\gamma_{n+1}=\frac12\) the first-order
symmetries form \(\mathfrak{so}(n+1)\). Also for \(n=2\), \(\gamma_1=\gamma_2=\frac32\) and
\(\gamma_3\) arbitrary, \(K=\rho L_{12}\rho^{-1}\), \(\rho^{-1}=(x_1x_2)^{1/2}
(1-x_1-x_2)^{\gamma_3/2-1/4}\), \(L_{12}=2\sqrt{x_1x_2}(\partial_{x_2}-\partial_{x_1})\),
satisfies \([H,K]=0\) (symbolic check).
Target: [M10.04.2.09].

### M10-E04.2.02. Degree preservation by the operators \(S_{ij}\)

Status: Confirmed.
Location: §4.2.1, p. 38, fourth bullet of CONCLUSIONS.
Printed: "each \(S_{ij}\) maps polynomials of maximum order \(m_k\) in \(x_k\) to polynomials of
the same type".
Correct: each \(S_{ij}\) maps polynomials of total degree \(\le M\) to polynomials of total
degree \(\le M\) (which suffices for the conclusion that separated bases are polynomial). The
coordinatewise statement holds for \(H\) (p. 33, p. 40), not for the \(S_{ij}\).
Evidence: \(S_{12}x_1^2=8x_1x_2+8(\gamma_1x_2-\gamma_2x_1)x_1\) has degree 1 in \(x_2\), while
\(x_1^2\) has degree 0 in \(x_2\).
Target: [M10.04.2.10], [M10.04.2.12].

### M10-E04.2.03. Argument of the radial Jacobi factor in the simplex form

Status: Confirmed.
Location: §4.2.2, p. 40, display of \(\psi_{jm}(x_1,x_2)\).
Printed: \(\psi_{jm}=(x_1+x_2)^mP^{(\gamma_1+\gamma_2+2m-1,\gamma_3-1)}_{j-m}(2x_1+2x_2-1)
P^{(\gamma_2-1,\gamma_1-1)}_m(\frac{2x_1}{x_1+x_2}-1)\).
Correct: the radial factor is \(P^{(\gamma_1+\gamma_2+2m-1,\gamma_3-1)}_{j-m}(1-2x_1-2x_2)\)
(equivalently \((-1)^{j-m}P^{(\gamma_3-1,\gamma_1+\gamma_2+2m-1)}_{j-m}(2x_1+2x_2-1)\)). The
angular form \(\psi_{jm}[\theta,\phi]\) on p. 41, with argument \(\cos2\theta=1-2(x_1+x_2)\), is
correct as printed.
Evidence: in \(u_2=x_1+x_2\) the weight is \(u_2^{2m+\gamma_1+\gamma_2-1}(1-u_2)^{\gamma_3-1}\),
which in \(y=1-2u_2\) is \((1-y)^{2m+\gamma_1+\gamma_2-1}(1+y)^{\gamma_3-1}\) up to a constant;
symbolically, for \(j=2\) the corrected \(\psi_{2m}\), \(m=0,1,2\), satisfy
\(H\psi=-2(G+1)\psi\), while the printed \(\psi_{20},\psi_{21}\) do not (only \(m=j\), where the
radial factor is constant, survives). It also agrees with \(\Theta_2\) of p. 39.
Target: [M10.04.2.16].

### M10-E04.2.04. Relation between \(u\) and \(q\)

Status: Confirmed.
Location: §4.2.2, p. 41, last display.
Printed: \(u=-4q-(e_1+e_2+e_3)j(j+G-1)\).
Correct: \(u=-4q-4(e_1+e_2+e_3)j(j+G-1)\), with \(q\) the constant in the Heun equation of p. 41.
Evidence: transforming \(H\) and \(\mathcal M\) to the ellipsoidal coordinates gives
\(H=(\mathcal L_x-\mathcal L_y)/(x-y)\) and \(\mathcal M=-4(y\mathcal L_x-x\mathcal L_y)/(x-y)
+4(e_1+e_2+e_3)H\), with \(\mathcal L_\lambda\) the operator of the Heun equation (checked
exactly on \(f=x_1,x_2,x_1^2,x_1x_2,x_1x_2^2\) at two points, for \((e_1,e_2,e_3)=(0,1,3)\) and
\((1,2,5)\), \((\gamma_1,\gamma_2,\gamma_3)=(\frac23,\frac75,\frac54)\); fitting
\(\mathcal M=A\,Q+B\,H\) gives \(A=-4\) and \(B=16\), resp. \(32\), i.e. \(B=4\sum e_i\)). On a
Heun product \(H\psi=-j(j+G-1)\psi\) and \((y\mathcal L_x-x\mathcal L_y)/(x-y)\,\psi=q\psi\). The
correction is also what makes the printed \(X_0\) (with the term of [M10-E04.2.06] corrected)
agree with the direct computation.
Target: [M10.04.2.18], [M10.04.2.19].

### M10-E04.2.05. Factor in \(X_{-1}(m,j)\)

Status: Confirmed.
Location: §4.2.2, p. 42, display of \(X_{-1}(m,j)\).
Printed: \(X_{-1}(m,j)=\frac{4(e_1-e_2)(\gamma_1+\gamma_2+m+j-1)(-m+j+1)(\gamma_2-1)(\gamma_1-1)}
{(\gamma_1+\gamma_2+2m-1)(\gamma_1+\gamma_2+2m-2)}\).
Correct: the factor \((\gamma_2-1)(\gamma_1-1)\) is \((\gamma_2+m-1)(\gamma_1+m-1)\).
Evidence: expanding \(\mathcal M\psi_{jm}\) (with the corrected \(\psi_{jm}\) of
[M10-E04.2.03]) in the basis \(\psi_{jm'}\) for \(\gamma=(\frac23,\frac75,\frac54)\),
\(e=(1,3,\frac72)\): for \(j=2\), \(m=1\) the coefficient of \(\psi_{20}\) is \(-\frac{6832}{713}\),
the printed \(X_{-1}(1,2)=\frac{976}{713}\) (ratio \(-7=\gamma_1\gamma_2/((\gamma_1-1)(\gamma_2-1))\));
for \(m=2\) the ratio is \(-30=(\gamma_1+1)(\gamma_2+1)/((\gamma_1-1)(\gamma_2-1))\). With the
corrected factor all coefficients agree for \(j=2,3\), and \(X_1\) agrees as printed.
Target: [M10.04.2.19].

### M10-E04.2.06. A term of \(X_0(m,j)\)

Status: Confirmed.
Location: §4.2.2, p. 42, second line of the display of \(X_0(m,j)-u\).
Printed: \(+4\frac{(e_1-e_2)m\gamma_3(\gamma_1-\gamma_2)(m+\gamma_2)}{(\gamma_1+\gamma_2+2m-2)
(\gamma_1+\gamma_2+2m)}\).
Correct: \((m+\gamma_2)\) is \((m+\gamma_1+\gamma_2-1)\). With this and [M10-E04.2.04], the printed
display gives \(X_0(m,j)=(\text{printed right side})-4q-u\), i.e. the formula in
[M10.04.2.19].
Evidence: symbolic computation of the diagonal coefficient of \(\mathcal M\psi_{jm}\) for general
\(\gamma\), \(e\): for \(j=1\), \(m=1\) the \((e_1-e_2)\)-part is
\(2\gamma_3(e_1-e_2)(\gamma_1-\gamma_2)/(\gamma_1+\gamma_2)\); the corrected two terms give
\(\frac{2\gamma_3(\gamma_1-\gamma_2)(e_1-e_2)[-(a-2)+2a]}{a(a+2)}\) with \(a=\gamma_1+\gamma_2\),
which equals it, while \((m+\gamma_2)\) gives the bracket \(4-\gamma_1+\gamma_2\ne a+2\). Likewise
verified for \((j,m)=(2,1),(2,2),(3,1)\) and numerically for all \(m\le j\le3\).
Target: [M10.04.2.19].

### Conventions and notation (not errata)

- §4.2: the source writes \(x\) for \(\sum_ix_i\); the index \(n+1\) of \(\gamma\) and the index 0
  of \(S_{0i}\), \(L_{0i}\), \(z_0\) refer to the same coordinate (index 3 in §4.2.2).
- p. 34: \(\Delta_n\) is defined from the metric \(g_{ij}\), which is four times the round
  metric of \(S^n\); so \(\Delta_n=\frac14\Delta_{S^n}\) ([M10.04.2.05]).
- p. 33 and p. 40: property 1 of \(H\) (coordinatewise degree preservation) is correct as
  printed; only the corresponding claim for \(S_{ij}\) on p. 38 fails ([M10-E04.2.02]).
- p. 36: \(8H=\sum_{i,j=1}^nS_{ij}+2\sum_iS_{0i}\) sums over ordered pairs with \(S_{ii}=0\);
  correct as printed. p. 39: \(S_k=\frac18\sum_{i,j=1}^{k+1}S_{ij}\) likewise (checked for
  \(n=3\), \(k=1,2\)).
- p. 35: the gauge formula and \(V_n\) are correct as printed (symbolic check for \(n=2,3\)); in
  the form \(V_n=-\frac14\sum_{i=0}^n\frac{q_i(q_i-1)}{x_i}+\frac14Q(Q+n-1)\),
  \(q_i=\gamma_i-\frac12\), \(Q=\sum q_i\).
- p. 37: indices of \(L_{ij}\), \(1\le i<j\le n+1\), are a relabelling of \(0\le i<j\le n\).
- p. 43: the determinant lists the basis in the order \(m=j,j-1,\dots,0\); correct as printed.
- p. 39: the eigen-equation for \(\Theta_1\) and the formulas for \(H\) in spherical coordinates
  and for \(d\tilde\omega\) are correct as printed (symbolic check \(n=2,3\)).

## Chapter 5. Clebsch–Gordan coefficients and orthogonal polynomials

### M10-E05.0.01. Lie algebra of \(SU(2)\)

Status: Confirmed.
Location: Chapter 5, p. 44, "\(L(SU(2))=s\ell(2,R)=\{\dots\}\)".
Printed: \(s\ell(2,R)\).
Correct: \(\mathfrak{su}(2)\).
Evidence: the displayed matrices \(\begin{pmatrix}ix_3&-x_2+ix_1\\x_2+ix_1&-ix_3\end{pmatrix}\) are
anti-Hermitian and traceless, i.e. \(\mathfrak{su}(2)\), which is compact; \(\mathfrak{sl}(2,
\mathbb R)\) is not isomorphic to \(\mathfrak{so}(3)\), contrary to the line "This algebra is
isomorphic to \(so(3)\)".
Target: [M10.05.0.01].

### M10-E05.0.02. The matrix \(L^3\)

Status: Confirmed.
Location: Chapter 5, p. 44, display of \(L^+,L^-,L^3\).
Printed: \(L^3=\begin{pmatrix}\frac12&0\\0&\frac12\end{pmatrix}\).
Correct: \(L^3=\begin{pmatrix}\frac12&0\\0&-\frac12\end{pmatrix}\), as on p. 16.
Evidence: the printed \(L^3=\frac12I\) commutes with \(L^\pm\), contradicting
\([L^3,L^\pm]=\pm L^\pm\) on the same page, and is not traceless.
Target: [M10.05.0.01].

### M10-E05.0.03. Multiplier of the \(SU(2)\) representations

Status: Confirmed.
Location: Chapter 5, p. 44, last display.
Printed: \(T_u(A)f(z)=(\beta z+\bar\beta)^{2u}f\bigl(\frac{\alpha z-\bar\beta}{\beta z+
\bar\alpha}\bigr)\).
Correct: \((\beta z+\bar\alpha)^{2u}\).
Evidence: the formula is the restriction of \(T_u(A)f=(bz+d)^{2u}f(\frac{az+c}{bz+d})\) of p. 16
with \(a=\alpha,b=\beta,c=-\bar\beta,d=\bar\alpha\); for \(A=I\) (\(\alpha=1,\beta=0\)) the
printed multiplier is \(0^{2u}\), so \(T_u(I)\ne I\) for \(u>0\).
Target: [M10.05.0.02].

### M10-E05.0.04. Addition theorem for \(U_{nm}\)

Status: Confirmed.
Location: Chapter 5, p. 45, display "\(U_{nm}(AB)=\sum_kU_{nk}(A)D_{km}(B)\)".
Printed: \(D_{km}(B)\) in the second factor.
Correct: \(U_{km}(B)\).
Evidence: \(U\) and \(D\) (p. 16) are the matrices of \(T_u\) in the bases \(f_m\) and \(z^j\);
\(T_u(AB)=T_u(A)T_u(B)\) gives \(U(AB)=U(A)U(B)\). For \(u=\frac12\) (\(f_{-1/2}=1\),
\(f_{1/2}=-z\)) one has \(U=SDS\) with \(S=\mathrm{diag}(1,-1)\); for \(A=I\) the printed formula gives
\(U(B)=D(B)\), whose off-diagonal entries (\(\pm\beta,\pm\bar\beta\)) have the opposite sign to
those of \(U(B)\) when \(\beta\ne0\).
Target: [M10.05.0.02].

### M10-E05.0.05. Total generator \(J^3\)

Status: Confirmed.
Location: Chapter 5, p. 45, last display.
Printed: \(J^3=L^3_1\).
Correct: \(J^3=L^3_1+L^3_2\), as used on p. 46.
Evidence: with \(J^3=L^3_1\), \([J^+,J^-]=2L^3_1+2L^3_2\ne2J^3\), so the \(J\)'s would not
represent \(\mathfrak{sl}(2)\), and \(f^{(u)}_u\otimes f^{(v)}_v\) (killed by \(J^+\)) would have
\(J^3\)-weight \(u\) instead of \(u+v\).
Target: [M10.05.0.03].

### Conventions and notation (not errata)

- p. 46: "eigenfunctions of \(J^3\) with eigenvalue \(s\)" means eigenvalue \(\alpha\)
  ([M10.05.0.05]).
- p. 46: the product formula is printed without complex conjugation, valid for real
  Clebsch–Gordan coefficients ([M10.05.0.04]).
- p. 45: \(L^\pm\) lie in the complexification of \(\mathfrak{su}(2)\), as the text states.

## Chapter 6. Harmonic analysis and lattice subgroups

### M10-E06.3.01. Uniqueness of the Daubechies filters

Status: Confirmed.
Location: §6.3, p. 55, first bullet.
Printed: "Daubechies finds the unique solutions for which the Fourier transform of the impulse
response vector \(C(\omega)\) has a zero of order \(p\) at \(\omega=\pi\), where \(2p=N+1\)."
Correct: the solutions are unique only up to the choice of spectral factor; for \(p=2\) the
filter and its reversal are the two solutions (for real filters), and Daubechies' choice is
fixed by a minimum-phase convention.
Evidence: \(D_4\): \(c=\frac1{4\sqrt2}(1+\sqrt3,3+\sqrt3,3-\sqrt3,1-\sqrt3)\) and its reversal
\(\frac1{4\sqrt2}(1-\sqrt3,3-\sqrt3,3+\sqrt3,1+\sqrt3)\) are both unit, double-shift orthogonal
(\(c(0)c(2)+c(1)c(3)=0\)), and have \(H(\pi)=H'(\pi)=0\).
Target: [M10.06.3.09].

### Conventions and notation (not errata)

- §§6.1–6.2 use \(\hat g(\omega)=\int g(t)e^{-2\pi i\omega t}dt\), §6.3 uses
  \(\hat\phi(\omega)=\int\phi(t)e^{-i\omega t}dt\) ([M10.06.1.01], [M10.06.3.08]).
- p. 48: "\(\int\omega|\hat g^{[x_1,x_2]}(t)|^2d\omega\)" has \(t\) for \(\omega\).
- p. 49: "Let \(\phi\in L^2(\mathbb R)\) with \(\|g\|=1\)" means \(\|\phi\|=1\).
- p. 51, Haar example item 3 and Definition 9(2): "\(\bigcup V_m=L^2\)" is meant as density, as
  the parenthetical explanation in Definition 9 says ([M10.06.3.01], [M10.06.3.02]).
- pp. 50–51: "\(\varphi_{mn}\) generate an ON basis for \(L^2\)" states the goal of the
  construction; the scaling functions of all levels are not orthonormal together (Haar:
  \(\langle\phi_{0,0},\phi_{1,0}\rangle=1/\sqrt2\)), and the orthonormal basis obtained is the
  wavelet basis of Theorem 3 ([M10.06.3.06]).
- pp. 54–55: "the support of \(\phi\) is contained in \([0,N)\)" means that \(\phi\) vanishes
  outside \([0,N)\) (true for the cascade iterates and, for \(D_{2p}\), \(p\ge2\), since
  \(\phi(N)=0\)); the closed support is \([0,N]\) ([M10.06.3.07]).
- p. 55: "polynomials of order \(\le p-1\) can be expressed in \(V_0\)" is a pointwise
  identity with a locally finite sum; \(t^\ell\notin L^2\) ([M10.06.3.10]).
- p. 55: the matrix \(T=(\downarrow2)2HH^{tr}\) is not defined in the notes and is not recorded;
  the smoothness exponents on p. 56 are numerical regularity estimates (and the regularity
  notion \(s\) is not defined), outside the scope.
- p. 56: the normalization \(\phi(0)+\phi(1)+\phi(2)=1\) is equivalent to \(\int\phi=1\) via
  \(\sum_k\phi(k)=1\); the \(D_4\) data are correct as printed (exact check).

## Chapter 7. Significant research opportunities and challenges

### Conventions and notation (not errata)

None.

[M10.01.3.01]: SYNOPSIS-Miller2010.md#m1001301-representations-matrix-representations-irreducibility
[M10.01.4.01]: SYNOPSIS-Miller2010.md#m1001401-schur-orthogonality-for-a-finite-group
[M10.02.1.02]: SYNOPSIS-Miller2010.md#m1002102-euler-angles
[M10.02.1.04]: SYNOPSIS-Miller2010.md#m1002104-irreducible-representations-of-so3-and-their-matrix-elements
[M10.02.1.08]: SYNOPSIS-Miller2010.md#m1002108-spherical-harmonics-and-legendre-functions-as-matrix-elements
[M10.02.2.03]: SYNOPSIS-Miller2010.md#m1002203-restriction-to-su2-wigner-functions
[M10.02.2.04]: SYNOPSIS-Miller2010.md#m1002204-infinite-dimensional-representations-on-analytic-functions
[M10.02.2.05]: SYNOPSIS-Miller2010.md#m1002205-unitarity-on-su11
[M10.02.2.08]: SYNOPSIS-Miller2010.md#m1002208-principal-series-realization-of-sl2mathbb-r
[M10.02.2.09]: SYNOPSIS-Miller2010.md#m1002209-signed-mellin-transform-and-inversion
[M10.02.2.10]: SYNOPSIS-Miller2010.md#m1002210-matrix-kernels-and-their-addition-theorem
[M10.03.0.01]: SYNOPSIS-Miller2010.md#m1003001-symmetry-and-conformal-symmetry-operators
[M10.03.1.02]: SYNOPSIS-Miller2010.md#m1003102-differential-recurrences-from-partial_u_j
[M10.03.1.03]: SYNOPSIS-Miller2010.md#m1003103-conformal-symmetries-of-the-wave-equation
[M10.03.1.04]: SYNOPSIS-Miller2010.md#m1003104-jacobi-polynomials
[M10.03.1.05]: SYNOPSIS-Miller2010.md#m1003105-lowering-and-raising-recurrences-for-jacobi-polynomials
[M10.03.1.06]: SYNOPSIS-Miller2010.md#m1003106-jacobi-differential-equation
[M10.03.1.07]: SYNOPSIS-Miller2010.md#m1003107-adjoint-pair-tautau-and-the-jacobi-weight
[M10.03.1.08]: SYNOPSIS-Miller2010.md#m1003108-factorized-eigenvalue-problem-and-orthogonality
[M10.03.1.09]: SYNOPSIS-Miller2010.md#m1003109-reflection-symmetry-of-jacobi-polynomials
[M10.03.1.10]: SYNOPSIS-Miller2010.md#m1003110-recurrence-for-the-jacobi-norms
[M10.03.1.11]: SYNOPSIS-Miller2010.md#m1003111-the-beta-integral-from-recurrences
[M10.04.2.05]: SYNOPSIS-Miller2010.md#m1004205-the-metric-of-h-and-the-sphere
[M10.04.2.09]: SYNOPSIS-Miller2010.md#m1004209-generic-parameters-no-nonconstant-first-order-symmetries
[M10.04.2.10]: SYNOPSIS-Miller2010.md#m1004210-second-order-symmetries-s_ij
[M10.04.2.12]: SYNOPSIS-Miller2010.md#m1004212-orthogonal-polynomial-bases-from-separable-systems
[M10.04.2.16]: SYNOPSIS-Miller2010.md#m1004216-spherical-jacobi-basis-for-n2
[M10.04.2.18]: SYNOPSIS-Miller2010.md#m1004218-the-ellipsoidal-symmetry-operator
[M10.04.2.19]: SYNOPSIS-Miller2010.md#m1004219-action-of-mathcal-m-on-the-jacobi-basis-and-the-overlap-recurrence
[M10.05.0.01]: SYNOPSIS-Miller2010.md#m1005001-su2-and-its-lie-algebra
[M10.05.0.02]: SYNOPSIS-Miller2010.md#m1005002-irreducible-representations-of-su2
[M10.05.0.03]: SYNOPSIS-Miller2010.md#m1005003-clebschgordan-series-and-coefficients
[M10.05.0.04]: SYNOPSIS-Miller2010.md#m1005004-product-formula-for-matrix-elements
[M10.05.0.05]: SYNOPSIS-Miller2010.md#m1005005-clebschgordan-coefficients-as-orthogonal-polynomials
[M10.06.1.01]: SYNOPSIS-Miller2010.md#m1006101-timefrequency-translates-and-their-centres
[M10.06.3.01]: SYNOPSIS-Miller2010.md#m1006301-haar-scaling-function
[M10.06.3.02]: SYNOPSIS-Miller2010.md#m1006302-multiresolution-analysis
[M10.06.3.06]: SYNOPSIS-Miller2010.md#m1006306-orthogonal-wavelet-decomposition
[M10.06.3.07]: SYNOPSIS-Miller2010.md#m1006307-compact-support-and-the-cascade-algorithm
[M10.06.3.08]: SYNOPSIS-Miller2010.md#m1006308-frequency-domain-dilation-equation-and-infinite-product
[M10.06.3.09]: SYNOPSIS-Miller2010.md#m1006309-daubechies-filters
[M10.06.3.10]: SYNOPSIS-Miller2010.md#m1006310-polynomial-reproduction
