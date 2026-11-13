# Errata and source checks: Klimyk–Vilenkin, EMS 59, Part II

Reference: A. U. Klimyk and N. Ya. Vilenkin, *Representations of Lie Groups and Special
Functions*, Part II of A. A. Kirillov (ed.), *Representation Theory and Noncommutative Harmonic
Analysis II*, Encyclopaedia of Mathematical Sciences 59, Springer, 1995, Chapters 1–6,
printed pp. 155–248. The local copy is in [References](References/).

Printed page \(p\) is PDF page \(p+6\). Equation numbers restart in each chapter, so the
chapter and the section are part of every locator.

This record is independent of the errata for the three-volume work of Vilenkin and Klimyk,
which are in [ERRATA-VK](ERRATA-VK.md).

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

- the location, as volume or chapter, section, printed page and equation;
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries.

Synopsis entries cite errata by id. An erratum id \(\mathrm E cc.s.nn\) is the \(nn\)-th
erratum located in section \(s\) of chapter \(cc\).

## Scope

These are observations about this edition, not an official publisher list. No claim is made
that formulas without an erratum are free of errors. Formulas that a synopsis marks "as
printed" were transcribed from the page images without an independent check. Corrected
formulas in the synopses are statements to be formalized. They are not Lean proofs.

Each chapter section ends with a list of conventions and notation that are not errata. Two
examples are a sign convention that differs from a modern reference, and the book's
overbarred \(\in\), which means \(\notin\).

## Summary by chapter

- Chapter 1 ([SYNOPSIS-KV01](SYNOPSIS-KV01.md), 36 entries): 18 errata (Confirmed 17, Normalization
  check 1).
- Chapter 2 ([SYNOPSIS-KV02](SYNOPSIS-KV02.md), 33 entries): 13 errata (Confirmed 13).
- Chapter 3 ([SYNOPSIS-KV03](SYNOPSIS-KV03.md), 73 entries): 22 errata (Confirmed 19, Normalization
  check 1, Open check 2).
- Chapter 4 ([SYNOPSIS-KV04](SYNOPSIS-KV04.md), 73 entries): 37 errata (Confirmed 31, Normalization
  check 2, Open check 4).
- Chapter 5 ([SYNOPSIS-KV05](SYNOPSIS-KV05.md), 25 entries): 8 errata (Confirmed 7, Normalization
  check 1).
- Chapter 6 ([SYNOPSIS-KV06](SYNOPSIS-KV06.md), 50 entries): 18 errata (Confirmed 18).

Totals: Confirmed 105, Normalization check 5, Open check 6; 116 errata and 290 synopsis entries.

## Chapter 1. Representations of Lie groups relating to special functions

Synopsis: [SYNOPSIS-KV01](SYNOPSIS-KV01.md).

### E01.1.01. \(\mathrm{ad}\,H\) is self-adjoint, not skew-Hermitian

Status: Confirmed.
Location: Part II, Chapter 1, §1.1, p. 155, sentence before (2).
Printed: the operators \(\mathrm{ad}H\), \(H\in\mathfrak a\), are skew-Hermitian with
respect to \(\langle X,Y\rangle=-B(X,\theta Y)\).
Correct: they are self-adjoint (Hermitian) for this inner product; hence they are
simultaneously diagonalizable with real eigenvalues, which gives (2).
Evidence: in \(\mathfrak{sl}_2(\mathbb R)\), \(H=\mathrm{diag}(1,-1)\in\mathfrak p\) has
\([H,E_{12}]=2E_{12}\); a nonzero real eigenvalue is impossible for a skew-adjoint
operator on a real inner product space. In general
\(\langle[H,X],Y\rangle=\langle X,[H,Y]\rangle\) because \(\theta H=-H\).
Target: [KV01.1.02].

### E01.1.02. Parabolic subgroups are not obtained by enlarging \(M\) inside \(K\)

Status: Confirmed.
Location: Part II, Chapter 1, §1.1, p. 156, paragraph on parabolic subgroups.
Printed: parabolic subgroups \(P'\supseteq P\) are \(P'=M'AN\) with
\(M\subset M'\subset K\).
Correct: \(P'=M'A'N'\) with \(A'\subseteq A\), \(N'\subseteq N\), where the Levi factor
\(M'A'\) is the \(\theta\)-stable one containing \(A\); \(M'\) is in general noncompact.
Evidence: in \(SL(3,\mathbb R)\) the block upper triangular subgroup of type \((2,1)\)
contains \(P\) (upper triangular) and has Levi factor
\(S(GL(2,\mathbb R)\times GL(1,\mathbb R))\supset SL(2,\mathbb R)\), which is not
contained in \(K=SO(3)\). The second printed sentence (a uniquely determined maximal
semisimple subgroup) is correct once the Levi factor is required to be
\(\theta\)-stable and to contain \(A\).
Target: [KV01.1.04].

### E01.1.03. Positivity condition defining \(\mathfrak a^+\)

Status: Confirmed.
Location: Part II, Chapter 1, §1.1, p. 156, definition of \(\mathfrak a^+\).
Printed: \(\mathfrak a^+\) is the set of \(H\in\mathfrak a\) with \(\gamma(H)>0\) for all
restricted roots \(\gamma\); with \(A^+\) "one obtains a unique decomposition".
Correct: \(\gamma(H)>0\) for all positive restricted roots. On \(KA^+K\) the
\(A^+\)-component is unique and the \(K\)-components are unique up to
\((k,k_1)\mapsto(km,m^{-1}k_1)\), \(m\in M\).
Evidence: \(\gamma\) and \(-\gamma\) are both roots, so the printed set is empty. For
\(g=khk_1\) with \(h\in A^+\) and \(m\in M\), \(g=(km)h(m^{-1}k_1)\).
Target: [KV01.1.05].

### E01.1.04. Half-root arguments in the radial Haar density

Status: Confirmed.
Location: Part II, Chapter 1, §1.1, p. 157, (4), (5).
Printed: \(\mu(h)=\prod_{\gamma>0}[\sinh\frac{(\gamma,H)}2]^{m(\gamma)}\) and
\(\prod_{\gamma>0}[\sin\frac{(\gamma,H)}2]^{m(\gamma)}\), where \((\gamma,H)=\gamma(H)\).
Correct: \(\prod_{\gamma>0}[\sinh\gamma(H)]^{m(\gamma)}\) and
\(\prod_{\gamma>0}|\sin\gamma(H)|^{m(\gamma)}\).
Evidence: the source fixes \((\gamma,H)=\gamma(H)\) and \(h=\exp H\). In its own
coordinates (8) for \(SU(1,1)\), \(h(t)=\exp(tX/2)\) with
\(X=\begin{pmatrix}0&1\\1&0\end{pmatrix}\) has root value \(\gamma(H)=t\)
(\(m(\gamma)=1\)), while Haar measure in \(g(\varphi,t,\psi)\) is
\(\sinh t\,d\varphi\,dt\,d\psi\), not \(\sinh(t/2)\,d\varphi\,dt\,d\psi\).
Target: [KV01.1.08].

### E01.1.05. \(NKA\) and \(\bar NAN\) are not all of \(SL(2,\mathbb R)\)

Status: Confirmed.
Location: Part II, Chapter 1, §1.2, p. 157, (6).
Printed: \(SL(2,\mathbb R)=KAN=KNA=NKA=KAK=\bar NAN\); the order may be reversed.
Correct: \(SL(2,\mathbb R)=KAN=KNA=KAK\) (and \(NAK\), \(ANK\)). \(\bar NAN\) is the
open dense set \(\{\delta>0\}\) (and \(\bar NMAN=\{\delta\ne0\}\), the Gauss
decomposition); \(NKA\) and \(AKN=(NKA)^{-1}\) are proper subsets.
Evidence: \(\bar n(t)a(s)n(u)\) has lower right entry \(e^{-s}>0\), so \(-I\notin\bar NAN\).
If \(g=n(u)k(\varphi)a(s)\), then \(g'=ga(s)^{-1}\) satisfies
\(g'g'^t=n(u)n(u)^t\), whose \((1,1)\) entry gives
\(e^{-2s}g_{11}^2+e^{2s}g_{12}^2=1\); this has no solution when
\(2|g_{11}g_{12}|>1\); e.g. \(g=\begin{pmatrix}2&1\\1&1\end{pmatrix}\notin NKA\)
(numerical minimization of the distance gives \(0.64\); the same holds with upper
triangular \(N\)).
Target: [KV01.1.10].

### E01.1.06. Bruhat decomposition needs \(M\)

Status: Confirmed.
Location: Part II, Chapter 1, §1.2, p. 157, (7).
Printed: \(SL(2,\mathbb R)=NAN\cup NsAN\), \(s=\begin{pmatrix}0&1\\-1&0\end{pmatrix}\).
Correct: \(SL(2,\mathbb R)=MAN\sqcup NsMAN\), with \(MAN=\{\beta=0\}\) and
\(NsMAN=\{\beta\ne0\}\) for \(g=\begin{pmatrix}\alpha&\beta\\\gamma&\delta\end{pmatrix}\).
Evidence: with \(A=\{a(t)\}\) (positive diagonal), \(NAN\) consists of lower triangular
matrices with positive diagonal and \(NsAN\) of matrices with \(\beta>0\); thus \(-I\)
and \(\begin{pmatrix}1&-1\\0&1\end{pmatrix}\) are in neither.
Target: [KV01.1.10].

### E01.1.07. Stray symbol in \(g_n(\theta)\)

Status: Confirmed.
Location: Part II, Chapter 1, §1.3, p. 158, (10).
Printed: the \((3,2)\) entry of the lower right block of \(g_n(\theta)\) is
"\(-rm\sin\theta\)".
Correct: \(-\sin\theta\).
Evidence: \(g_n(\theta)\) must be orthogonal; "rm" is a typesetting remnant.
Target: [KV01.1.12].

### E01.1.08. Matrix \(n(\mathbf a)\) of the subgroup \(N\) of \(SO_0(n,1)\)

Status: Confirmed.
Location: Part II, Chapter 1, §1.3, p. 158, display of \(n(\mathbf a)\).
Printed: rows \((I_{n-1},\ \mathbf a^t,\ -\mathbf a^t)\),
\((\mathbf a,\ 1+\frac{(\mathbf a,\mathbf a)}2,\ -\frac{(\mathbf a,\mathbf a)}2)\),
\((\mathbf a,\ \frac{(\mathbf a,\mathbf a)}2,\ 1-\frac{(\mathbf a,\mathbf a)}2)\).
Correct: with \(\mathbf a\) a column and \(q=(\mathbf a,\mathbf a)\), rows
\((I_{n-1},\ \mathbf a,\ -\mathbf a)\), \((-\mathbf a^t,\ 1-\frac q2,\ \frac q2)\),
\((-\mathbf a^t,\ -\frac q2,\ 1+\frac q2)\).
Evidence: the printed matrix fixes \(\xi_0=(0,\dots,0,1,1)\), but its \(n\)-th column
has \([\cdot,\cdot]\)-norm \(1+2q\ne1\), so it does not preserve \([x,y]\). Among the
sign variants only the corrected matrix satisfies \(M^t\eta M=\eta\),
\(\eta=\mathrm{diag}(1,\dots,1,-1)\), and \(M\xi_0=\xi_0\) (numerical check, \(n=4\)); it
also satisfies \(n(\mathbf a)n(\mathbf b)=n(\mathbf a+\mathbf b)\).
Target: [KV01.1.12].

### E01.1.09. Sign of the hyperboloid and of the Iwasawa logarithm

Status: Confirmed.
Location: Part II, Chapter 1, §1.3, p. 158, definition of \(H_n\) and (10a).
Printed: \(H_n=\{x:[x,x]=1\}\) with base point \(x_0=(0,\dots,0,1)\);
\([x_0,kg'_n(t)n\xi_0]=[x_0,g'_n(t)\xi_0]=e^t\); \(t=\log[x_0,g\xi_0]\).
Correct: \(H_n=\{x:[x,x]=-1,\ x_{n+1}>0\}\);
\([x_0,g'_n(t)\xi_0]=-e^t\); \(t=\log(-[x_0,g\xi_0])=\log(g\xi_0)_{n+1}\).
Evidence: \([x_0,x_0]=-1\) for the form \(x_1y_1+\dots+x_ny_n-x_{n+1}y_{n+1}\), and
\([x_0,(0,\dots,0,e^t,e^t)]=-e^t<0\).
Target: [KV01.1.13].

### E01.1.10. Indices of the compact subgroups of \(U(n,1)\)

Status: Confirmed.
Location: Part II, Chapter 1, §1.4, pp. 158–159, (11).
Printed: \(K=U(n-1)\times U(1)\), \(K'=U(n-1)\),
\(U(n,1)=K'D_{n+1}AK'\), \(U(n+1)=K'D_{n+1}A_kK'\).
Correct: \(K=U(n)\times U(1)\), \(K'=U(n)\) (upper left block); with this \(K'\) both
factorizations in (11) hold.
Evidence: \(\dim_{\mathbb R}U(n,1)=(n+1)^2\), while
\(\dim(K'D_{n+1}AK')\le2(n-1)^2+2<(n+1)^2\) for \(K'=U(n-1)\). With \(K'=U(n)\),
\(KAK\) gives the factorization because the \(U(1)\) factor at place \(n+1\) equals a
central element times an element of \(U(n)\), and the central element commutes with
\(A\).
Target: [KV01.1.14].

### E01.1.11. Quadratic term in the oscillator subgroup \(S_4\)

Status: Confirmed.
Location: Part II, Chapter 1, §1.6, p. 160, definition of \(s(w,\alpha,\delta)\).
Printed: \(s(w,\alpha,\delta)=g(e^{-i\alpha}\bar w/2,\ i\delta-|w|^2/2,\ e^{-i\alpha},
\ -w/2)\).
Correct: \(s(w,\alpha,\delta)=g(e^{-i\alpha}\bar w/2,\ i\delta-|w|^2/8,\ e^{-i\alpha},
\ -w/2)\).
Evidence: with \(\alpha=\delta=0\) and \(w_1=w_2=2\) the printed matrices have
\(a=1,b=-2,d=-1\); their product has \(a=2,d=-2,b=-5\), whereas the printed family
with \(w=4\) needs \(\mathrm{Re}\,b=-8\). In general the real part of the product's
\(b\) is \(-k(|w_1|^2+|w_2|^2)-\frac14\mathrm{Re}(e^{-i\alpha_1}\bar w_1w_2)\), which
equals \(-k|w_1+e^{-i\alpha_1}w_2|^2\) only for \(k=\frac18\). The corrected value
also reproduces the Gaussian \(e^{-\rho r^2/2}\) of Chapter 2, (33).
Target: [KV01.1.18], [KV01.2.18], [KV02.2.16].

### E01.1.12. The sets \(S_2\) and \(S_3\) as printed are not groups

Status: Confirmed.
Location: Part II, Chapter 1, §1.6, p. 160, definitions of \(S_2\), \(S_3\).
Printed: \(S_2=\{g(\tau,r,s):r,s\in\mathbb R,\ \tau>0\}\);
\(S_3=\{g(i\psi,r,s):r,s\in\mathbb R,\ 0\le\psi<2\pi\}\).
Correct: \(S_2\) needs \(\tau\in\mathbb R\); \(S_3\) needs \(r,s\in\mathbb C\) (or must be
replaced by a group generated by the printed set).
Evidence: \(\tau>0\) excludes the identity. For \(S_3\),
\((i\psi,r,s)(i\psi',r',s')=(i(\psi+\psi'),\ r+e^{2i\psi}r',\ s+e^{i\psi}s')\), and
\(e^{2i\psi}r'\notin\mathbb R\) in general.
Target: [KV01.1.17], [KV01.2.17].

### E01.2.01. Unitarity line of the spherical series

Status: Confirmed.
Location: Part II, Chapter 1, §2.1, p. 161, sentence after (18).
Printed: \(T_\nu\) is unitary if \(\nu+\rho\) is pure imaginary on \(\mathfrak a\).
Correct: \(T_\nu\) (with \(f(gp)=\lambda^{-1}(h)f(g)\), \(\lambda(h)=e^{\nu(H)}\), \(N\)
generated by the positive root spaces, \(\rho\) the half-sum of positive roots) is
unitary for \(\int_K|f|^2dk\) if \(\nu-\rho\) is pure imaginary.
Evidence: the Jacobian of \(k\mapsto k_g\) (\(g^{-1}k=k_ghn\), \(h=\exp H\)) is
\(e^{-2\rho(H)}\). Numerical check for \(SL(2,\mathbb R)\), \(N\) upper triangular,
\(\nu(\mathrm{diag}(s,-s))=cs\), \(\rho(\mathrm{diag}(s,-s))=s\): for a fixed \(g\),
\(\int_K|T_\nu(g)1|^2dk=1.0000\) for \(c=1\) and \(1.0862\) for \(c=-1\).
Target: [KV01.2.01].

### E01.2.02. Multiplier in the compact boundary model (26)

Status: Confirmed.
Location: Part II, Chapter 1, §2.6, pp. 164–165, (26) and the preceding sentence.
Printed: \(T^l(g_n(\theta))f=(\cos\theta-i\sin\varphi_{n-1}\sin\theta)^lf(\dots,
\varphi'_{n-1})\); the carrier space is called "homogeneous harmonic polynomials in
\(x_1,\dots,x_n\) of power \(\le l\)".
Correct: the multiplier is \((\cos\theta-i\cos\varphi_{n-1}\sin\theta)^l\). The carrier
space is \(\bigoplus_{k=0}^l\mathcal H_k(\mathbb R^n)\) (harmonic polynomials of
degree \(\le l\), not homogeneous), restricted to \(S^{n-1}\).
Evidence: (26) is (23') with \(\sigma=l\), \(t=i\theta\) (\(\cosh i\theta=\cos\theta\),
\(\sinh i\theta=i\sin\theta\)), which gives \(\cos\varphi_{n-1}\); the printed formula
for \(\cos\varphi'_{n-1}\) also has \(\cos\varphi_{n-1}\) in its denominator. A sum of
homogeneous parts of different degrees is not homogeneous.
Target: [KV01.2.10].

### E01.2.03. Rotation action in the \(SO(n+1)\) model

Status: Confirmed.
Location: Part II, Chapter 1, §2.6, p. 165.
Printed: \(T^l(k)f(\xi)=f(k\xi)\), \(k\in SO(n)\).
Correct: \(T^l(k)f(\xi)=f(k^{-1}\xi)\), as in §2.3, p. 163.
Evidence: \(k\mapsto(f\mapsto f(k\,\cdot))\) satisfies
\(T(k_1k_2)=T(k_2)T(k_1)\), an anti-homomorphism for nonabelian \(SO(n)\), \(n\ge3\).
Target: [KV01.2.10].

### E01.2.04. Dilation multiplier in the Mellin picture

Status: Confirmed.
Location: Part II, Chapter 1, §2.8, p. 166, (32).
Printed: \(R_\lambda(g)F(w)=e^{-w}F(w)\) for \(b=0\).
Correct: \(R_\lambda(g(a,0))F(w)=a^{-w}F(w)\).
Evidence: (31) with \(b=0\) gives \(a^{-w}F(w)\); the printed form is the case \(a=e\).
Target: [KV01.2.13].

### E01.2.05. The circle representation (44) is reducible

Status: Confirmed.
Location: Part II, Chapter 1, §2.10, p. 168, sentence with (44).
Printed: (44) defines a representation of \(S_3\) in \(L^2(0,2\pi)\) which is irreducible
for \(\alpha\ne0\).
Correct: the closed subspace spanned by \(z^k\), \(k\ge0\) (the Hardy space), is
invariant, so the representation is reducible.
Evidence: \(f(z)\mapsto f(e^{i\psi}z)\) preserves the nonnegative Fourier modes, and
multiplication by \(e^{-\alpha(rz^2+sz)}\), a power series in \(z\) with only
nonnegative powers, bounded on \(|z|=1\), preserves the Hardy space.
Target: [KV01.2.17].

### E01.2.06. Fock inner product for the oscillator representations

Status: Normalization check.
Location: Part II, Chapter 1, §2.10, p. 168, (45) and the last sentence; compare
Chapter 2, §2.6, p. 181, (33).
Printed: the representations \(T_{(\rho,m)}\), \(\rho>0\), \(m\in\mathbb Z\), are unitary
for \((f_1,f_2)=\frac1\pi\int_{\mathbb C}f_1\overline{f_2}e^{-|z|^2}dx\,dy\).
Correct: the restriction to \(S_4\) of \(T_\chi\), \(\chi=(\rho,m)\), is unitary for
\(\frac\rho\pi\int f_1\overline{f_2}e^{-\rho|z|^2}dx\,dy\), with orthonormal basis
\(\rho^{n/2}z^n/\sqrt{n!}\); for (45) one must conjugate by \(f(z)\mapsto f(z/\sqrt\rho)\).
Evidence: \(T_\chi(s(w,0,0))1=e^{-\rho|w|^2/8-\rho wz/2}\) has (45)-norm squared
\(e^{-\rho|w|^2/4}e^{\rho^2|w|^2/4}\ne1\) for \(\rho\ne1\). Chapter 2, (33) is exactly
the matrix of \(T_\chi\) in the basis \(\rho^{n/2}z^n/\sqrt{n!}\) (symbolic check),
although Chapter 2 states the basis \(z^n/\sqrt{n!}\). An unstated rescaling of \(z\)
or of the inner product reconciles the displays.
Target: [KV01.2.18], [KV02.2.16].


### Conventions and notation (not errata)

- In §1.2 the source's \(N\) is lower triangular and \(\bar N\) upper triangular; with
  \(A=\{\mathrm{diag}(e^t,e^{-t})\}\) this corresponds to the positive system containing
  the root of \(E_{21}\). The synopsis keeps these labels.
- The Heisenberg group \(\{g(a,b,1,d)\}\) of §1.6 has complex parameters; "three
  dimensional" refers to complex dimension, the real form having \(a,b,d\in\mathbb R\).
- In (23), powers of \(be^{i\theta}+\bar a\) and its conjugate are combined into the
  single-valued mixed power fixed in the synopsis Conventions; for
  \(\varepsilon=\frac12\) the factor is \(|\cdot|^{2\tau}\) times the unit phase.
- The source does not state the invariant inner product on \(H_l\) for (24); it is the
  one with \((x^j,x^k)=\delta_{jk}j!(2l-j)!\) (checked for \(l\le2\)).

## Chapter 2. Matrix elements of representations and special functions

Synopsis: [SYNOPSIS-KV02](SYNOPSIS-KV02.md).

### E02.1.01. Direction of an operator function belonging to a pair

Status: Confirmed.
Location: Part II, Chapter 2, §1.4, pp. 171–172, definition of an operator function
belonging to \((Q_1,Q_2)\).
Printed: \(F\) takes values in the operators from \(\mathcal H_{Q_1}\) into
\(\mathcal H_{Q_2}\), and \(F(h_1gh_2)=Q_1(h_1)F(g)Q_2(h_2)\).
Correct: \(F(g)\) maps \(\mathcal H_{Q_2}\) into \(\mathcal H_{Q_1}\).
Evidence: the product \(Q_1(h_1)F(g)Q_2(h_2)\) is defined only for this direction; the
blocks \(T_{ri,sj}(g)\) of (10) map the \(Q_s\)-summand to the \(Q_r\)-summand.
Target: [KV02.1.05].

### E02.1.02. Dimension factors in Theorems 3 and 4

Status: Confirmed.
Location: Part II, Chapter 2, §1.4, pp. 172–173, Theorems 3 and 4.
Printed: \(F=\sum_\alpha\frac{d_rd_s}{d_\alpha}\sum a^\alpha_{ij}T^\alpha_{ri,sj}\) with
Parseval factor \(\frac{d_rd_s}{d_\alpha}\); \(f=\sum_\alpha\frac{d_r}{d_\alpha}\sum
a^\alpha_{ip}t^\alpha_{ri,p}\) with Parseval factor \(\frac{d_r}{d_\alpha}\).
Correct: the factors are \(\frac{d_\alpha}{d_rd_s}\) (Theorem 3) and
\(\frac{d_\alpha}{d_r}\) (Theorem 4), in both the expansion and the Parseval equality.
Evidence: by Theorem 1, \(\int_G\mathrm{Tr}(T^\alpha_{ri,sj}T^{\alpha*}_{ri,sj})dg
=d_rd_s/d_\alpha\) and \(\int_G\|t^\alpha_{ri,p}\|^2dg=d_r/d_\alpha\). For
\(H=\{e\}\) (\(d_r=d_s=1\)) the printed Theorem 3 gives the coefficient \(d_\alpha^{-1}\)
instead of the Peter–Weyl coefficient \(d_\alpha\) of (8).
Target: [KV02.1.06], [KV02.1.07].

### E02.2.01. Basis in which (15)–(16) and the \(S_3\) formulas hold

Status: Confirmed.
Location: Part II, Chapter 2, §2.1, p. 176 (basis before (15)); §2.7, p. 182 (basis of
\(L^2(0,2\pi)\) for \(S_3\)).
Printed: the orthonormal basis is \(e^{ip\varphi}/\sqrt{2\pi}\) (§2.1) and
\(e^{in\varphi}\) (§2.7).
Correct: (15), (16) and the §2.7 formulas are the matrix elements
\((T(g)f_n,f_m)\) for \(f_p=e^{-ip\varphi}/\sqrt{2\pi}\), as used in Chapter 3,
p. 185. In the printed basis the matrix element is \(t_{-m,-n}\).
Evidence: diagonal entries are basis independent up to relabelling. By Chapter 1, (23),
\(T_\chi(k(\varphi))e^{ip\theta}=e^{i(p-\varepsilon)\varphi}e^{ip\theta}\), while (16)
gives \(e^{-i(p+\varepsilon)\varphi}\), which is the eigenvalue on \(e^{-ip\theta}\).
For §2.7, \(T_\alpha(g(i\psi,0,0))e^{in\varphi}=e^{in\psi}e^{in\varphi}\), whereas the
source gives \(t_{mn}(\psi,0,0)=e^{-in\psi}\delta_{mn}\); also
\(e^{-\alpha(rz^2+sz)}z^n\) has only components \(z^m\), \(m\ge n\), whereas the source
has nonzero entries for \(n\ge m\). Numerically (generic \(g\), complex \(\tau\),
\(\varepsilon=0,\frac12\)), (15) agrees with the \(e^{-ip\varphi}\) model to \(10^{-20}\)
and differs from the \(e^{ip\varphi}\) model by \(\sim10^{-1}\).
Target: [KV02.2.01], [KV02.2.03], [KV02.2.17].

### E02.2.02. Exponent of \(\bar\alpha\) in the second hypergeometric formula

Status: Confirmed.
Location: Part II, Chapter 2, §2.1, p. 177, display for \(m\ge n\).
Printed: \(\alpha^{\tau-m-\varepsilon}\bar\alpha^{\,\tau+m+\varepsilon}\bar\beta^{\,m-n}\).
Correct: \(\alpha^{\tau-m-\varepsilon}\bar\alpha^{\,\tau+n+\varepsilon}\bar\beta^{\,m-n}\).
Evidence: for \(\tau=1\), \(\varepsilon=0\), \(m=1\), \(n=0\), \(g=g_t\), the integral (15)
gives \(\cosh\frac t2\sinh\frac t2\), the printed formula
\(\cosh^2\frac t2\sinh\frac t2\). Numerically, for generic \(g\) and complex \(\tau\),
the corrected formula agrees with (15) to \(10^{-21}\); it also agrees with the
following Jacobi-function formula.
Target: [KV02.2.02].

### E02.2.03. Discrete series formula (18a)

Status: Confirmed.
Location: Part II, Chapter 2, §2.1, p. 178, (18a).
Printed: for \(m\le n\le l\),
\(\mathcal P^l_{mn}(\cosh t)=[\frac{\Gamma(l-n+1)\Gamma(-l-m)}{\Gamma(l-m+1)
\Gamma(-l-n)}]^{1/2}(\sinh\frac t2)^{n-m}(\cosh\frac t2)^{m+n}P^{(m-n,m+n)}_{l-n}
(\cosh t)\).
Correct: \(\mathcal P^l_{mn}(\cosh t)=(-1)^{m-n}[\frac{\Gamma(l-n+1)\Gamma(-l-m)}
{\Gamma(l-m+1)\Gamma(-l-n)}]^{1/2}(\sinh\frac t2)^{n-m}(\cosh\frac t2)^{m+n}
P^{(n-m,m+n)}_{l-n}(\cosh t)\), i.e. \(\mathcal P^l_{mn}=(-1)^{m-n}\mathcal P^l_{nm}\)
with \(\mathcal P^l_{nm}\) from (18).
Evidence: unitarity gives \(t_{mn}(h(-t))=\overline{t_{nm}(h(t))}=t_{nm}(h(t))\) (real),
and \(h(-t)=k(\pi)h(t)k(-\pi)\) with (16)-type phases gives
\(t_{mn}(h(-t))=(-1)^{m-n}t_{mn}(h(t))\). Example: \(l=-1\), \((m,n)=(-2,-1)\): (18)
gives \(\mathcal P^l_{-1,-2}=\sqrt2\sinh\frac t2\cosh^{-3}\frac t2\), so
\(\mathcal P^l_{-2,-1}\) must be \(-\sqrt2\sinh\frac t2\cosh^{-3}\frac t2\); the printed
(18a) gives \(+\). For \(l=-1\), \((m,n)=(-3,-2)\) the printed Jacobi factor is
\(P^{(-1,-5)}_1(x)=-2(x-1)\), the corrected one \(P^{(1,-5)}_1(x)=3-x\). Numerically
(\(l=-1,-\frac32,-\frac52\), truncation at 45 weights), the matrices built from (18) and
the corrected (18a) satisfy the group law for \(h(t_1)k(\varphi)h(t_2)\) and unitarity
to \(2\cdot10^{-15}\); with the printed (18a) they are \(0.36\)–\(0.45\) and \(0.61\)–\(0.80\).
Target: [KV02.2.05].

### E02.2.04. Euler-angle phases in the discrete series and in (19)

Status: Confirmed.
Location: Part II, Chapter 2, §2.1, p. 178, display after (18a); §2.2, p. 178, (19).
Printed: \(t^{l,-}_{mn}(g(\varphi,t,\psi))=e^{-i(m'\varphi+n'\varphi)}\mathcal P^l_{mn}
(\cosh t)\); \(t^l_{mn}(g)=e^{-i(\varphi m+\varphi n)}P^l_{mn}(\cos\theta)\).
Correct: \(e^{-i(m\varphi+n\psi)}\) in both (for the discrete series the indices
\(m,n\) are already the weights; there is no \(\varepsilon\)-shift).
Evidence: \(g(\varphi,t,\psi)=k(\varphi)g_tk(\psi)\) with \(k(\psi)\) diagonal on the
weight basis, so the matrix element must depend on \(\psi\) through \(e^{-in\psi}\);
the printed phases do not depend on \(\psi\) (compare (16), printed correctly as
\(e^{-i(m'\varphi+n'\psi)}\)). The SU(2) check of [E02.2.05] confirms
\(e^{-i(m\varphi+n\psi)}\) numerically.
Target: [KV02.2.05], [KV02.2.06].

### E02.2.05. Canonical-basis phase in (19)–(20)

Status: Confirmed.
Location: Part II, Chapter 2, §2.2, p. 178, (19), (20), with Chapter 1, (24), (25).
Printed: in the canonical basis (25) of Chapter 1,
\(t^l_{mn}(u(\varphi,\theta,\psi))=e^{-i(m\varphi+n\psi)}P^l_{mn}(\cos\theta)\) with
\(P^l_{mn}\) given by (19a), and
\(t^l_{m0}=[\frac{(l-m)!}{(l+m)!}]^{1/2}e^{-im\varphi}P_l^m(\cos\theta)\).
Correct: \(t^l_{mn}(u(\varphi,\theta,\psi))=i^{\,m-n}e^{-i(m\varphi+n\psi)}P^l_{mn}
(\cos\theta)\) and \(t^l_{m0}=i^{\,m}[\frac{(l-m)!}{(l+m)!}]^{1/2}e^{-im\varphi}
P_l^m(\cos\theta)\) with \(P_l^m=(1-x^2)^{m/2}d^mP_l/dx^m\) (\(m\ge0\)). Without the
factor \(i^{m-n}\), (19) holds in the basis \((-x)^{l-k}/\sqrt{(l-k)!(l+k)!}\); in the
unphased monomial basis the factor is \((-1)^{m-n}\).
Evidence: for \(l=\frac12\), \(\theta\)-rotation \(u(\theta)\) (\(\alpha=\cos\frac\theta2\),
\(\beta=\sin\frac\theta2\)): \(T(u)(-ix)=-i(\cos\frac\theta2\,x-\sin\frac\theta2)\), so the
coefficient of \(\psi_{1/2}=1\) is \(+i\sin\frac\theta2=i^{1}P^{1/2}_{\frac12,-\frac12}\).
Numerical expansion in the canonical basis for all \(m,n\), \(l\le3\), gives exactly
the factor \(i^{m-n}\) (error \(<10^{-15}\)); in the basis \((-x)^{l-k}/\sqrt{\cdot}\)
the ratio to (19a) is 1, in the basis \(i^{l-k}x^{l-k}/\sqrt{\cdot}\) it is
\((-i)^{m-n}\). The generating function (40) of
Chapter 3 carries the same factor.
Target: [KV02.2.06], [KV02.2.07].

### E02.2.06. Argument of the hypergeometric function in (24)

Status: Confirmed.
Location: Part II, Chapter 2, §2.4, p. 179, (24).
Printed: \(\cosh^\sigma t\,F(-\frac\sigma2,-\frac{\sigma-1}2;\frac n2;\tan^2t)\).
Correct: \(\cosh^\sigma t\,F(-\frac\sigma2,\frac{1-\sigma}2;\frac n2;\tanh^2t)\).
Evidence: binomial expansion of \((1-\cos\varphi\tanh t)^\sigma\) in the integral; for
\(t\) near \(\pi/2\) the printed argument exceeds 1. Numerically (\(n=3,4,5\),
complex \(\sigma\), \(t=0.7\)) the corrected form equals the integral to \(10^{-21}\).
Target: [KV02.2.10].

### E02.2.07. Gegenbauer index in the integral for \(t^\sigma_{m0}\)

Status: Confirmed.
Location: Part II, Chapter 2, §2.4, p. 180, integral preceding (26).
Printed: \(\int_0^\pi(\cosh t-\cos\varphi\sinh t)^\sigma C_m^{(n-1)/2}(\cos\varphi)
\sin^{n-2}\varphi\,d\varphi\).
Correct: \(C_m^{(n-2)/2}(\cos\varphi)\).
Evidence: the \(SO(n-1)\)-invariant spherical harmonics on \(S^{n-1}\) are
\(C_m^{(n-2)/2}(\xi_n)\), and the printed prefactor
\(\frac{\Gamma((n-2)/2)}{2\sqrt\pi\Gamma((n-1)/2)}[\frac{m!(2m+n-2)(n-2)!}{(m+n-3)!}]^{1/2}\)
is exactly the normalization for \(C_m^{(n-2)/2}\). Numerically (\(n=3,4,5\),
\(m\le3\)) the corrected integral equals the closed form (26) to \(10^{-21}\), the
printed one differs by \(0.07\)–\(0.8\).
Target: [KV02.2.12].

### E02.2.08. Euclidean Bessel formulas (28)–(29)

Status: Confirmed.
Location: Part II, Chapter 2, §2.5, p. 181, (28), (29).
Printed: \(t^\sigma_{00}(g_r)=\Gamma(\frac{n+1}2)(\frac{-i\sigma r}2)^{-(n-1)/2}
J_{(n-1)/2}(-i\sigma r)\); \(t^\sigma_{m0}(g_r)=i^m\Gamma(\frac{n+1}2)
[\frac{(m+n-2)!(2m+n-1)}{m!(n-1)!}]^{1/2}(\frac{-i\sigma r}3)^{-(n-1)/2}
J_{m+(n-1)/2}(-i\sigma r)\).
Correct: \(t^\sigma_{00}(g_r)=\Gamma(\frac n2)(\frac{-i\sigma r}2)^{-(n-2)/2}
J_{(n-2)/2}(-i\sigma r)\); \(t^\sigma_{m0}(g_r)=i^m\Gamma(\frac n2)
[\frac{(m+n-3)!(2m+n-2)}{m!(n-2)!}]^{1/2}(\frac{-i\sigma r}2)^{-(n-2)/2}
J_{m+(n-2)/2}(-i\sigma r)\).
Evidence: the model is on \(S^{n-1}\); the printed formulas are those for \(S^n\)
(dimension shifted by one, plus the misprint 3 for 2). At \(n=2\) the zonal function
must be \(I_0(\sigma r)\) (by (23)), not a spherical-Bessel expression; at \(n=3\) the
corrected (29) is \(\sqrt{2m+1}\,i_m(\sigma r)\). Numerically (\(n=3,4,5\), \(m\le3\),
complex \(\sigma\)) the corrected formulas equal \(\int_{S^{n-1}}e^{\sigma r\xi_n}
Y_m\,d\xi\) to \(10^{-21}\); the printed ones differ by \(0.005\)–\(1.2\).
Target: [KV02.2.14].

### E02.2.09. Matrix elements of \(S_3\)

Status: Confirmed.
Location: Part II, Chapter 2, §2.7, p. 182.
Printed: \(t^\alpha_{mn}(0,0,s)=\frac{(\alpha s)^{n-m}}{(n-m)!}\) and
\(t^\alpha_{mn}(0,r,s)=\frac{(-1)^{n-m}}{(n-m)!}(\alpha r)^{(n-m)/2}H_{n-m}
\bigl(\frac{\alpha^{1/2}s}{s\sqrt r}\bigr)\), \(n\ge m\).
Correct: \(t^\alpha_{mn}(0,0,s)=\frac{(-\alpha s)^{n-m}}{(n-m)!}\) and
\(t^\alpha_{mn}(0,r,s)=\frac{(-1)^{n-m}}{(n-m)!}(\alpha r)^{(n-m)/2}H_{n-m}
\bigl(\frac{\alpha^{1/2}s}{2\sqrt r}\bigr)\) (in the basis \(e^{-in\varphi}\), see
[E02.2.01]).
Evidence: the coefficient of \(z^q\) in \(e^{-\alpha(rz^2+sz)}\) is
\(\sum_j\frac{(-\alpha r)^j(-\alpha s)^{q-2j}}{j!(q-2j)!}\); with
\(e^{2xu-u^2}=\sum H_q(x)u^q/q!\), \(u=\sqrt{\alpha r}\,z\),
\(x=-\sqrt\alpha s/(2\sqrt r)\), this is \(\frac{(-1)^q}{q!}(\alpha r)^{q/2}
H_q(\frac{\sqrt\alpha s}{2\sqrt r})\). Internally, \(r\to0\) in the printed third formula
gives \((-\alpha s)^q/q!\), contradicting the printed second formula for odd \(q\); the
printed argument contains \(s/s\).
Target: [KV02.2.17].

### E02.2.10. Constant and Jacobi parameter in (34)

Status: Confirmed.
Location: Part II, Chapter 2, §2.8, p. 182, (34).
Printed: constant \((-1)^p[\frac{(n-2)(p-p'+n-2)(m-p)!m!(-p'+n-3)!(p+n-3)!(-m')!}
{(m-p'+n-2)!(p'-m')!(-m'+n-2)!(-p')!p!}\cdot\frac{(p-m'+n-2)!}{(m+n-1)!}]^{1/2}\) and
\(P^{(p-p'+n-1,\,p+p'-m-m')}_{m-p}(\cos2\theta)\).
Correct: \((m+n-2)!\) in place of \((m+n-1)!\), and
\(P^{(p-p'+n-2,\,p+p'-m-m')}_{m-p}(\cos2\theta)\); the sign \((-1)^p\) is a basis
convention and is not verified.
Evidence: identity test: at \(\theta=0\), \(p=p'=0\) the printed formula gives
\(\sqrt{m+n-1}/(n-1)\) (e.g. \((n-1)^{-1/2}\) for the trivial representation) instead
of 1. The zonal function on \(U(n)/U(n-1)=S^{2n-1}\) is the disk polynomial with
Jacobi parameter \(n-2\) (for \(n=2\) it is the \(SU(2)\) function
\(\cos^{-m-m'}\theta P^{(0,-m-m')}_m(\cos2\theta)\)), and the unnumbered
\(U(n-1,1)\) display after (34) has the parameter \(m-m'+n-2\). An explicit model
(harmonic polynomials of bidegree \((m,-m')\) on \(\mathbb C^n\), Fischer inner
product) for \(n=3\), \((m,m')=(1,-2),(1,-3),(2,-1),(3,-1)\), and \(n=4\),
\((m,m')=(2,-1),(2,-2)\), at two values of \(\theta\), gives \(|t|\) equal to the
corrected formula (ratio exactly 1 for every \((p,p')\)), and equal to
\(\sqrt{m+n-1}\) times the printed constant with parameter \(n-2\).
Target: [KV02.2.18].

### E02.2.11. Diagonal action of \(d_n(\varphi)\)

Status: Confirmed.
Location: Part II, Chapter 2, §2.8, p. 182, display after (34).
Printed: \(t^{mm'}_{(pp')(pp')}(d_n(\varphi))=\exp i(p+p'-m-m')\).
Correct: \(\exp\bigl(i\varphi(p+p'-m-m')\bigr)\) (the sign of the exponent depends on
the realization of \(T^{mm'}\)).
Evidence: at \(\varphi=0\), \(d_n(0)=e\) and the matrix element must be 1; the printed
expression is a constant independent of \(\varphi\).
Target: [KV02.2.18].


### Conventions and notation (not errata)

- The source's \(\mathcal P^\tau_{mn}\) and \(\mathfrak P^\tau_{mn}\) are written as
  functions of \(\cosh t\), but contain \(\sinh^{m-n}(t/2)\); they are functions of
  \(t\in\mathbb R\), odd or even according to the parity of \(m-n\).
- There is no displayed equation (35) in Chapter 2: the \(U(n-1,1)\) formula on p. 183 is
  unnumbered, and the next number is (36).
- On p. 180 the source cites "expression (23a), Chap. 1"; the formula meant is (23') of
  Chapter 1.
- The constants \(A,B,C\) in (36)–(37) are not given in this Part (the source refers to
  Vilenkin and Klimyk [1984] for \(U(3)\)); (36)–(37) are therefore statements of form.
- In (31) for \(k>n\) the factor \(a^{n-k}L_k^{n-k}(-\sigma ad/c)\) is a polynomial in
  \(a\); the formula is valid at \(a=0\) in that reading.
- The basis \(z^n/\sqrt{n!}\) stated before (33) is orthonormal for (45) of Chapter 1;
  (33) holds in the basis \(\rho^{n/2}z^n/\sqrt{n!}\) of the \(\rho\)-weighted Fock
  space (see [E01.2.06]).

## Chapter 3. Functional relations for special functions related to matrix elements

Synopsis: [SYNOPSIS-KV03](SYNOPSIS-KV03.md).

### E03.1.01. Range of the boost parameter

Status: Confirmed.
Location: Part II, Chapter 3, §1.2, p. 185, line after (6).
Printed: \(0\le\varphi<2\pi\), \(0\le t<\pi\), \(-2\pi<\psi<2\pi\).
Correct: \(0\le\varphi<2\pi\), \(0\le t<\infty\), \(-2\pi<\psi<2\pi\).
Evidence: by (4), \(\cosh t\ge\cosh(t_1+t_2)\) at \(\varphi_2=0\), so \(t=t_1+t_2\) is
unbounded; the bound \(\pi\) belongs to the compact parameter \(\theta\).
Target: [KV03.1.03].

### E03.1.02. Argument of the second factor in (10)

Status: Confirmed.
Location: Part II, Chapter 3, §1.2, p. 185, (10).
Printed: \(\sum_ke^{-ik\varphi_2}P^l_{mk}(\cos\theta_1)P^l_{kn}(\cos\theta_1)\).
Correct: \(\sum_ke^{-ik\varphi_2}P^l_{mk}(\cos\theta_1)P^l_{kn}(\cos\theta_2)\).
Evidence: (10) is \(t^l(u(\theta_1)k(\varphi_2)u(\theta_2))\) expanded by the
representation law; the right side must depend on \(\theta_2\). Checked numerically for
\(l=1,\frac32,2\) with the corrected argument.
Target: [KV03.1.07].

### E03.1.03. Gamma factor in the associated Legendre addition theorem

Status: Confirmed.
Location: Part II, Chapter 3, §1.3, p. 186, (13).
Printed: \(2^{p-1}\Gamma(p)\Gamma(\sigma+1)\Gamma(-\sigma-2p)\sum_k(-1)^k
\frac{2k+2p}{\Gamma(\sigma-k+1)}\Gamma(-\sigma-k-2p)\cdots\).
Correct: \(2^{p-1}\Gamma(p)\Gamma(\sigma+1)\Gamma(-\sigma-2p)\sum_k(-1)^k
\frac{2k+2p}{\Gamma(\sigma-k+1)\Gamma(-\sigma-k-2p)}\cdots\), i.e. the coefficient is
\((-1)^k(2k+2p)(\sigma-k+1)_k(-\sigma-k-2p)_k\) times \(2^{p-1}\Gamma(p)\).
Evidence: at \(\sigma=0.37\), \(t_1=0.5\), \(t_2=0.7\), \(\varphi=1.1\), \(p=1\) the
printed series gives \(0.7877\), the left side is \(0.5822\); the corrected series agrees
to 25 digits, also at \(p=\frac32\) and at complex \(\sigma=0.37+0.6i\). The product
formula on p. 194, derived from the same coefficients, has \(\Gamma(-\sigma-m-2p)\) in the
denominator.
Target: [KV03.1.10].

### E03.1.04. Dimension condition for the Gegenbauer–Bessel addition theorem

Status: Confirmed.
Location: Part II, Chapter 3, §1.4, p. 187, sentence before (15a).
Printed: "representations of the group \(ISO(n)\), \(n<2\)".
Correct: \(n>2\), so that \(p=(n-2)/2>0\).
Evidence: (15a) contains \(\Gamma(p)\) and \(C_k^p\) with \(p=(n-2)/2\); for \(n<2\),
\(p<0\), and \(n=2\) gives \(\Gamma(0)\). Section 2.4 states the same product formula
for \(n>2\).
Target: [KV03.1.13].

### E03.1.05. Degree in the derivative of Jacobi polynomials

Status: Confirmed.
Location: Part II, Chapter 3, §1.5, p. 188, display after (18).
Printed: \(\frac d{dx}P_n^{(\alpha,\beta)}(x)=\frac12(\alpha+\beta+n+1)
P_n^{(\alpha+1,\beta+1)}(x)\).
Correct: \(\frac d{dx}P_n^{(\alpha,\beta)}(x)=\frac12(\alpha+\beta+n+1)
P_{n-1}^{(\alpha+1,\beta+1)}(x)\) for \(n\ge1\).
Evidence: differentiation lowers the degree. For \(n=1\), \(\alpha=\beta=0\), the left
side is \(1\) and the printed right side is \(P_1^{(1,1)}(x)=2x\).
Target: [KV03.1.16].

### E03.1.06. Coefficient in the addition theorem for Jacobi functions

Status: Confirmed.
Location: Part II, Chapter 3, §1.5, p. 188, (20), coefficient \(A\).
Printed: denominator factor \(\Gamma(\beta+m-l+1)\Gamma(\beta+m+l+1)\).
Correct: denominator factor \(\Gamma(\beta+m+1)\Gamma(\beta+\mu-l+1)\); all other factors
as printed. Then \(A_{00}=1\). The convergence region of the double series remains
unstated in the source and is not settled here.
Evidence: at \(t_1=t_2=0\) only \(m=l=0\) contributes and the left side is
\(R_\mu^{(\alpha,\beta)}(1)=1\), while the printed \(A_{00}=\Gamma(\beta+\mu+1)/
\Gamma(\beta+1)\). With the correction the series truncated at \(m<30\) matches
\(R_\mu^{(\alpha,\beta)}(X_h)\) to 15 digits at \(\alpha=2.3\), \(\beta=0.7\),
\(\mu=0.45\), \(t_1=0.15\), \(t_2=0.2\), \(r=0.6\), \(\psi=1.1\) (printed: \(1.2329\)
against \(1.0481\)). At \(\mu=n\) the corrected coefficient reduces (19a) to the
normalized form.
Target: [KV03.1.18].

### E03.1.07. Convergence condition in the Laguerre addition theorems

Status: Confirmed.
Location: Part II, Chapter 3, §1.6, p. 189, (21) and (22).
Printed: (21) holds "where \(|t/s|<1\)"; (22) carries the same tacit condition.
Correct: the series converge for \(t|e^\tau|<s\) (for nonintegral \(\alpha\)); the
condition \(|t/s|<1\) suffices only for \(\mathrm{Re}\,\tau\le0\), in particular for the
product formulas with \(\tau=i\varphi\).
Evidence: \(L_m^{\alpha-m}(x)\) is the coefficient of \(z^m\) in \(e^{-xz}(1+z)^\alpha\),
which has radius of convergence \(1\) for \(\alpha\notin\mathbb Z_{\ge0}\). At
\(t=0.5\), \(s=0.9\), \(\tau=1\), \(\alpha=1.7\), \(k=1\), \(\sigma=0.6+0.3i\) the terms
of (21) have moduli \(0.33\), \(6.9\cdot10^3\), \(3.0\cdot10^{10}\) at \(m=10,40,80\).
For \(t|e^\tau|<s\) both identities hold numerically, also for complex \(\tau\).
Target: [KV03.1.21], [KV03.1.22].

### E03.1.08. Missing condition in the third triangular factorization

Status: Confirmed.
Location: Part II, Chapter 3, §1.6, p. 189, "The equality
\(g_1(t)\epsilon(\tau)g_1(-s)=\epsilon(\tau)g_-(r)z(b)\)".
Printed: the identity with \(r=(t^2-s^2)/s\), \(b=(t^2-s^2)/2\), no condition on
\(\tau\).
Correct: the identity holds if and only if \(e^\tau=s/t\).
Evidence: the \((1,2)\) entry of the left side is \(te^\tau-s\), that of the right side
is \(0\). The fourth identity on pp. 189–190 states its condition \(e^\tau=t/s\).
Target: [KV03.1.20].

### E03.1.09. Parameters in the addition theorem at \(\varphi_2=\pi/2\)

Status: Confirmed.
Location: Part II, Chapter 3, §1.8, p. 191, display after (25).
Printed: \(e^{i\varphi}=\frac{\sin\theta_1\sin\theta_2+i\sin\theta_2}{\sin\theta}\) and
\(e^{i(\varphi+\psi)/2}=\frac{\sqrt2\cos((\theta_1+\theta_2)/2)+i\cos((\theta_1-
\theta_2)/2)}{2\cos(\theta/2)}\).
Correct: \(e^{i\varphi}=\frac{\sin\theta_1\cos\theta_2+i\sin\theta_2}{\sin\theta}\) and
\(e^{i(\varphi+\psi)/2}=\frac{\sqrt2[\cos((\theta_1+\theta_2)/2)+i\cos((\theta_1-
\theta_2)/2)]}{2\cos(\theta/2)}\).
Evidence: both are the compact form of (5)–(6) at \(\varphi_2=\pi/2\). At
\(\theta_1=0.7\), \(\theta_2=1.3\) the printed right sides have moduli \(1.171\) and
\(0.788\); the corrected ones have modulus \(1\) and reproduce
\(u(\theta_1)k(\pi/2)u(\theta_2)=k(\varphi)u(\theta)k(\psi)\) to 30 digits.
Target: [KV03.1.27].

### E03.1.10. Normalization of the \(SU(2)\) orthogonality relation

Status: Confirmed.
Location: Part II, Chapter 3, §1.10, p. 192, display after (29).
Printed: \(\frac1{2\pi}\int_0^{2\pi}t^l_{mn}(\theta)\overline{t^{l'}_{mn}(\theta)}
\sin\theta\,d\theta=(\dim T_l)^{-1}\delta_{ll'}\).
Correct: \(\frac12\int_0^\pi t^l_{mn}(\theta)\overline{t^{l'}_{mn}(\theta)}\sin\theta\,
d\theta=(2l+1)^{-1}\delta_{ll'}\).
Evidence: at \(l=l'=0\) the printed left side is \(\frac1{2\pi}\int_0^{2\pi}\sin\theta\,
d\theta=0\), not \(1\). The radial measure of normalized Haar measure on \(SU(2)\) is
\(\frac12\sin\theta\,d\theta\) on \([0,\pi]\); the corrected relation holds numerically
for several \((l,l',m,n)\).
Target: [KV03.1.33].

### E03.2.01. Dimension factor in the product formulas

Status: Confirmed.
Location: Part II, Chapter 3, §2.1, p. 193, (30) and (31).
Printed: the factor \(\sqrt{\dim Q_q}\) in front of the integrals.
Correct: the factor is \(\dim Q_q\).
Evidence: multiplying (3) by \(\overline{d^q_{00}(k)}\) and integrating over \(K\) gives
\(t_{0q}(h_1)t_{q0}(h_2)/\dim Q_q\), since \(\int_K|d^q_{00}|^2dk=1/\dim Q_q\). Example:
\(SO(3)\subset SO(4)\), \(q=1\): \(\int_0^\pi\cos^2\varphi\,\frac12\sin\varphi\,
d\varphi=\frac13\).
Target: [KV03.2.01], [KV03.2.02].

### E03.2.02. Order of the second Legendre function in the product formula

Status: Confirmed.
Location: Part II, Chapter 3, §2.3, p. 194, first display.
Printed: \(\ldots\mathfrak P^{-m-p}_{\sigma+p}(\cosh t_1)\mathfrak P^{-m-\sigma}_{\sigma+p}
(\cosh t_2)\).
Correct: \(\ldots\mathfrak P^{-m-p}_{\sigma+p}(\cosh t_1)\mathfrak P^{-m-p}_{\sigma+p}
(\cosh t_2)\).
Evidence: the formula is the coefficient extraction from (13), symmetric in
\(t_1,t_2\). At \(p=1\), \(m=2\), \(\sigma=0.37\), \(t_1=0.5\), \(t_2=0.7\) the integral
is \(-0.0014783\); the corrected right side agrees to 25 digits, the printed one gives
\(-0.0013589\). Also checked at \(p=\frac32\) and complex \(\sigma\).
Target: [KV03.2.07].

### E03.2.03. Argument of the second Laguerre product formula

Status: Confirmed.
Location: Part II, Chapter 3, §2.6, p. 195, second display.
Printed: \(L_k^{\alpha-k}(s^2-t^2-2ts\sin\varphi)\) and \(r^{2(\alpha-k)}\) with the same
\(r^2\).
Correct: \(r^2=s^2-t^2-2i\,ts\sin\varphi\), the value of \(s^2-t^2-2ts\sinh\tau\) at
\(\tau=i\varphi\).
Evidence: substitution of \(\tau=i\varphi\) in (22). With the factor \(i\) the formula
holds numerically (integer \(\alpha=2,3\)); without it, it fails. The single-valued form
in [KV03.2.12] holds for nonintegral \(\alpha\).
Target: [KV03.2.12].

### E03.3.01. Special case of the multiplication formula

Status: Normalization check.
Location: Part II, Chapter 3, §3.2, p. 197, display after (36a).
Printed: \(\mathfrak P^m_{\tau_1+\tau_2}(\cosh t)=\sum_n\mathfrak P^n_{\tau_1}(\cosh t)
\mathfrak P^{m-n}_{\tau_2}(\cosh t)\).
Correct: the identity holds for \(\mathfrak P^\tau_{m0}\):
\(\mathfrak P^{\tau_1+\tau_2}_{m0}=\sum_n\mathfrak P^{\tau_1}_{n0}
\mathfrak P^{\tau_2}_{m-n,0}\). For the associated Legendre functions of Chapter 2, (17),
the factors \(\Gamma(\tau+1)/\Gamma(\tau+m+1)\) must be inserted, as in [KV03.3.05].
Evidence: at \(\tau_1=0.3\), \(\tau_2=0.5\), \(m=2\), \(t=0.8\) the printed sides are
\(-0.06287\) and \(-0.05441\); the version with gamma factors agrees to 20 digits. The
printed display is correct if \(\mathfrak P^m_\tau\) denotes \(\mathfrak P^\tau_{m0}\).
Target: [KV03.3.05].

### E03.3.02. Radius of the contour for \(\mathfrak P^\tau_{mn}\)

Status: Confirmed.
Location: Part II, Chapter 3, §3.2, p. 197, display before (37).
Printed: \(\Gamma\) is the circle \(|z|=a\), \(1<a<\cosh(t/2)\).
Correct: \(\tanh(t/2)<a<\coth(t/2)\).
Evidence: the generating function (36) converges on that annulus; the integrand has
branch points at \(z=-\tanh(t/2)\) and \(z=-\coth(t/2)\). At \(t=3\), \(\tau=0.37\),
\(m=1\), \(n=0\), the circle \(a=2\) satisfies the printed condition
(\(\cosh1.5=2.35\)) but encloses \(-\coth1.5=-1.105\); the integral is \(0.3160\), while
\(\mathfrak P^\tau_{10}(\cosh3)=0.5576\), which \(a=1.05\) reproduces.
Target: [KV03.3.04].

### E03.3.03. Sign in the Mellin integrals and their inverses

Status: Confirmed.
Location: Part II, Chapter 3, §3.2, pp. 197–198, (37), (39), and the two inverse
formulas (bottom of p. 197, top of p. 198).
Printed: the prefactor \(\frac{\sin((\tau-n)\pi)}\pi\) in (37),
\(\frac{\sin(\tau\pi)}\pi\) in (39), and \(-\frac i2\) in both inverse formulas.
Correct: \(-\frac{\sin((\tau-n)\pi)}\pi\) in (37), \(-\frac{\sin(\tau\pi)}\pi\) in (39),
and \(+\frac i2=-\frac1{2i}\) in both inverse formulas.
Evidence: for \(x>1\), \(\tau=-\frac12\) the integral in (39) is positive and
\(\mathfrak P_{-1/2}(x)>0\), while \(\sin(-\pi/2)/\pi<0\). The corrected (37) holds
numerically at \(t=0.8\) for \((\tau,m,n)=(-0.4,0,0)\), \((0.6,1,0)\), \((1.3,2,1)\),
\((0.2,2,0)\), \((0.7,\frac32,\frac12)\). Mellin inversion of the corrected (39) gives
\(+\frac i2\); numerically checked at \(x=1.6\), \(w=0.7\), \(a=-\frac12\).
Target: [KV03.3.06], [KV03.3.07], [KV03.3.08].

### E03.3.04. Discrete-series generating function

Status: Confirmed.
Location: Part II, Chapter 3, §3.2, p. 198, display for \(\mathcal P^l_{mn}\).
Printed: \(\Phi(z,t)=\sum_{m=l}^{-\infty}\big[\frac{\Gamma(l-n+1)\Gamma(-l-n)}
{\Gamma(l-m+1)\Gamma(-l-m)}\big]^{1/2}\mathcal P^l_{mn}(\cosh t)\).
Correct: \(\Phi(z,t)=\sum_{m=l}^{-\infty}\big[\frac{\Gamma(l-n+1)\Gamma(-l-m)}
{\Gamma(l-m+1)\Gamma(-l-n)}\big]^{1/2}\mathcal P^l_{mn}(\cosh t)\,z^{m+l}\), for
\(|z|>\tanh(t/2)\).
Evidence: the power \(z^{m+l}\) is required by (36) with \(\tau=l\). The Laurent
coefficients of \(\Phi\), computed by contour integration at \(t=0.7\), equal the
corrected expressions for \(l=-1,-\frac32\), \(n=l,l-2\), \(m=l,\dots,l-4\) (including
\(m<n\), with the corrected Chapter 2, (18a)); the printed gamma ratio fails, e.g.
\(l=n=-1\), \(m=-3\): coefficient \(0.3010\), printed \(0.0502\).
Target: [KV03.3.09].

### E03.3.05. Kernel and substitution in the contour integral (41)

Status: Open check.
Location: Part II, Chapter 3, §3.3, p. 199, (41).
Printed: \(P^l_{mn}(\cos\theta)=\frac1{2\pi i}[\frac{(l-m)!(l+m)!}{(l-n)!(l+n)!}]^{1/2}
\oint_\Gamma w^{l-n}(\cos\frac\theta2+it\sin\frac\theta2)^{2n}
\frac{t^{m-n}dw}{\sqrt{w^2+2w\cos\theta+1}}\), with
\(t=\frac{w-\cos\theta+\sqrt{w^2+2w\cos\theta+1}}{i\sin\theta}\) and \(\Gamma\)
unspecified.
Correct: the exact coefficient form of (40) is
\(P^l_{mn}(\cos\theta)=\frac{i^{n-m}}{2\pi i}[\cdots]^{1/2}\oint_{|u|=1}B(u)^{l-n}
(\cos\frac\theta2+iu\sin\frac\theta2)^{2n}u^{m-n-1}du\),
\(B(u)=\cos\theta+\frac i2\sin\theta(u+u^{-1})\). The substitution \(w=B(u)\) gives
\(u=\frac{w-\cos\theta\pm\sqrt{w^2-2w\cos\theta+1}}{i\sin\theta}\) and
\(du/u=\pm dw/\sqrt{w^2-2w\cos\theta+1}\); the substitution \(w=-B(u)\) gives
\(u=\frac{-w-\cos\theta\pm\sqrt{w^2+2w\cos\theta+1}}{i\sin\theta}\) and a factor
\((-1)^{l-n}\). The printed \(t\) and kernel match neither, and the phase \(i^{n-m}\)
is absent. The conjectured correction is the \(w=B(u)\) version with kernel
\(\sqrt{w^2-2w\cos\theta+1}\) and the factor \(i^{n-m}\); the contour \(\Gamma\) (a
two-sheeted image of \(|u|=1\)) and the branch remain to be fixed.
Evidence: algebraic comparison with (40), which holds as printed; the generating
function derived from (41) on p. 199 uses \(\sqrt{1-2h\cos\theta+h^2}\), i.e. the kernel
\(\sqrt{w^2-2w\cos\theta+1}\) at \(w=1/h\).
Target: [KV03.3.12].

### E03.3.06. Generating functions in the degree \(l\)

Status: Confirmed.
Location: Part II, Chapter 3, §3.3, p. 199, displays after (41).
Printed: for \(|m|\le n\),
\(\sum_{l\ge n}[\frac{(l-n)!(l+n)!}{(l-m)!(l+m)!}]^{1/2}P^l_{mn}(\cos\theta)h^{l-n}
=\frac{t^{m-n}(it\sin(\theta/2)+\cos(\theta/2))^{2n}}{\sqrt{1-2h\cos\theta+h^2}}\), with
\(t\) from (41) at \(w=1/h\); and
\(\sum_{l\ge m}\frac{l!}{(l+m)!}P^m_l(\cos\theta)h^l=\frac{(it)^m}{\sqrt{1-2h\cos\theta
+h^2}}\).
Correct: with \(R=\sqrt{1-2h\cos\theta+h^2}\) and \(\rho=h\sin\theta/(1-h\cos\theta+R)\):
\(\sum_lP^l_{nn}(\cos\theta)h^{l-n}=(\cos\frac\theta2-\rho\sin\frac\theta2)^{2n}/R\)
(the printed form with \(t\) the root \(i\rho\) vanishing at \(h=0\));
\(\sum_lP^l_{-n,n}(\cos\theta)h^{l-n}=(-1)^{2n}(\sin\frac\theta2+\rho\cos\frac\theta2)
^{2n}/R\); and \(\sum_{l\ge m}\frac{l!}{(l+m)!}P^m_l(\cos\theta)h^l=\rho^m/R\) for the
Ferrers functions of Chapter 2, (20). For \(|m|<n\) the printed right side is false.
Evidence: with the printed \(t\) (root \(\sim2/(ih\sin\theta)\)) the right side is not
analytic at \(h=0\) in the needed way: for \(m=1\) the printed associated Legendre right
side behaves like \(2/(h\sin\theta)\), while the left side is \(\frac12h\sin\theta+O(h^2)\).
For \(|m|<n\) the factor \(t^{m-n}\) with the small root has a pole at \(h=0\) whereas the
left side is a power series. Numerically (\(\theta=0.9\), \(h=0.3\); also \(\theta=2.5\),
\(h=-0.6\), and complex \(h\)) the corrected formulas agree to 12 digits; at \(n=2\),
\(m=0\) the series is \(1.2661\) and the printed form with the small root has modulus
\(29.19\).
Target: [KV03.3.13].

### E03.3.07. Constants in the Gegenbauer generating function

Status: Confirmed.
Location: Part II, Chapter 3, §3.4, p. 199, first display.
Printed: \((\cosh t-\cos\varphi\sinh t)^\sigma=2^{p+1}\Gamma(\sigma+1)\Gamma(p)
\sinh^{-p}t\sum_k\frac{(-1)^k(2k-2p)}{\Gamma(\sigma-k+1)}\mathfrak P^{-k-p}_{\sigma+p}
(\cosh t)C_k^p(\cos\varphi)\).
Correct: \(2^{p-1}\Gamma(\sigma+1)\Gamma(p)\sinh^{-p}t\sum_k\frac{(-1)^k(2k+2p)}
{\Gamma(\sigma-k+1)}\mathfrak P^{-k-p}_{\sigma+p}(\cosh t)C_k^p(\cos\varphi)\).
Evidence: at \(\sigma=0.37\), \(t=0.6\), \(\varphi=0.9\) the corrected series equals
\(0.91635561282\) (the left side) for \(p=\frac12,1,\frac32\); the series with
\(2^{p+1}(k+p)\) is \(1.8327\), twice the left side, so the printed constant is off by
the factor \(4\), and \(2k-2p\) has the wrong sign at \(k=0\). The \(k=0\) term must
reproduce (24) of Chapter 2.
Target: [KV03.3.14].

### E03.4.01. Scalar action of Laplace operators

Status: Open check.
Location: Part II, Chapter 3, §4.1, pp. 200–201, before (43).
Printed: for every irreducible representation \(T\), \(T(g)\Delta_k=\Delta_kT(g)\), so by
Schur's lemma \(\Delta_k\) is a multiple of the identity in the carrier space.
Correct: for irreducible unitary representations, central elements of
\(U(\mathfrak g)\) act as scalars on the smooth vectors (Segal; for admissible
representations, Harish-Chandra); this gives (43) for matrix elements of smooth vectors.
Schur's lemma for bounded operators does not apply directly to the unbounded
\(\Delta_k\). Whether the statement holds for arbitrary irreducible (nonunitary,
nonadmissible) Banach representations is not settled here.
Evidence: \(\Delta_k\) is unbounded and defined only on smooth vectors, so the bounded
form of Schur's lemma is not applicable; the needed infinitesimal-character property is
a separate theorem.
Target: [KV03.4.03].

### E03.4.02. Sign of the \(SU(1,1)\) eigenvalue

Status: Confirmed.
Location: Part II, Chapter 3, §4.5, p. 202, last display.
Printed: \(\Delta t^\chi_{mn}(g)=\tau(\tau+1)t^\chi_{mn}(g)\).
Correct: for \(\Delta=-B_1^2-B_2^2+B_3^2\) as in (45),
\(\Delta t^\chi_{mn}=-\tau(\tau+1)t^\chi_{mn}\).
Evidence: on a zonal function \(f(t)=\mathfrak P_\tau(\cosh t)\), (45) gives
\(\Delta f=-(f''+\coth t\,f')=-\tau(\tau+1)f\) by the Legendre equation. Numerical second
derivatives along the three one-parameter subgroups at \(\tau=0.37\), \(t=0.8\) give
\(\Delta f/f=-0.5069\), \(\tau(\tau+1)=0.5069\). The differential equation on p. 203,
with \(+\tau(\tau+1)\) on the right, is correct and agrees with the corrected eigenvalue.
Target: [KV03.4.08].


### Conventions and notation (not errata)

- The source's \(P^l_{mn}(\cos\theta)\) of Chapter 2, (19a) is phase-free and real; the
  phases \(i^{m-n}\) in (40) and \(i^{n-m}\) in the integral on p. 198 are consistent with
  it. The Ferrers functions \(P^m_l\) of Chapter 2, (20) carry no Condon–Shortley sign.
- In (17a) the sign of the term \(\sin\theta_1\sin\theta_2\cos\varphi\,e^{i\psi}\)
  depends on the unstated orientation of the rotations \(g_j(\theta)\); with the same
  rotation matrix in every factor the sign is negative. Formulas (18) and (19) are
  identities in the variable (17a) as printed.
- The first Laguerre product formula on p. 195 uses the factor
  \((t+se^{i\varphi})^{k-\alpha}\) with \(s>t\); this base winds around \(0\), so the
  power is the continuous branch along \(\varphi\in[0,2\pi]\) starting from the positive
  value at \(\varphi=0\). The principal branch gives a wrong value for nonintegral
  \(\alpha\). [KV03.2.12] uses the equivalent single-valued factor
  \((s+te^{i\varphi})^{\alpha-k}\).
- Formula (36) is written with \(z^{m+\tau}\); the identity is between the Laurent
  series after division by \(z^{\tau+n}\) ([KV03.3.03]), which avoids a choice of branch
  for \(z^\tau\).
- The exclusion of poles in (13), the product formula on p. 194 and the generating
  function on p. 199 is unnecessary: the gamma ratios are Pochhammer polynomials in
  \(\sigma\).

## Chapter 4. Representations of Lie Groups in "Continuous" Bases and Special Functions

Synopsis: [SYNOPSIS-KV04](SYNOPSIS-KV04.md).

### E04.1.01. Affine gamma kernel: dilation factor

Status: Confirmed.
Location: Part II, Chapter 4, §1.2, p. 204, (1).
Printed: \(K(w,z;g)=\dfrac{\Gamma(w-z)a^{-w}}{2\pi i}\Big(-\dfrac{\lambda b}{2}\Big)^{z-w}\).
Correct: \(K(w,z;g)=\dfrac{\Gamma(w-z)a^{-w}}{2\pi i}\Big(-\dfrac{\lambda b}{a}\Big)^{z-w}
 =\dfrac{\Gamma(w-z)}{2\pi i}a^{-z}(-\lambda b)^{z-w}\).
Evidence: the preceding display on the same page is
\(K=\frac{a^{-w}}{2\pi i}\int_0^\infty e^{\lambda bx/a}x^{w-z-1}dx\); the gamma integral with rate
\(-\lambda b/a\) gives the corrected value. The printed value depends on \(a\) only through
\(a^{-w}\), which contradicts the scaling law \(\mathcal M(f(a\cdot))(w)=a^{-w}\mathcal M f(w)\)
applied to \(e^{\lambda bx}f(ax)\).
Target: [KV04.1.02].

### E04.1.02. Null-translation kernels for \(\Re R<0\)

Status: Confirmed.
Location: Part II, Chapter 4, §1.3, p. 205, (5)–(6).
Printed: \(K=\frac{\Gamma(\lambda-\mu)}{2\pi i}(Rr)^{\mu-\lambda}\) (5) and
\(K=\frac{\Gamma(\mu-\lambda)}{2\pi i}(Rr)^{\lambda-\mu}\) (6), for \(\Re R<0\).
Correct: \(K=\frac{\Gamma(\lambda-\mu)}{2\pi i}(-Rr)^{\mu-\lambda}\) (5) and
\(K=\frac{\Gamma(\mu-\lambda)}{2\pi i}(-Rr)^{\lambda-\mu}\) (6), principal powers.
Evidence: for \(g(0;-r,r)\) the defining integral is \(\frac1{2\pi i}\int_{\mathbb R}
e^{Rre^\theta+(\lambda-\mu)\theta}d\theta=\frac{\Gamma(\lambda-\mu)}{2\pi i}(-Rr)^{\mu-\lambda}\),
convergent because \(\Re(-Rr)>0\); likewise (6) with \(e^{-\theta}\). With principal branches
\((Rr)^{\mu-\lambda}=e^{\pm i\pi(\mu-\lambda)}(-Rr)^{\mu-\lambda}\ne(-Rr)^{\mu-\lambda}\) unless
\(\mu-\lambda\in\mathbb Z\).
Target: [KV04.1.04].

### E04.1.03. Signed Mellin kernels: missing \(1/(2\pi i)\)

Status: Confirmed.
Location: Part II, Chapter 4, §1.4, p. 206, (15)–(16).
Printed:
\(K_{-+}(\lambda,\mu;\chi,g_+(t))=\frac{\Gamma(\lambda)\Gamma(1-\mu)}{\Gamma(\lambda-\mu+1)}
t^{\lambda-\mu}\) and \(K_{--}(\lambda,\mu;\chi,g_+(t))=\frac{\Gamma(1-\mu)\Gamma(\mu-\lambda)}
{\Gamma(1-\lambda)}t^{\lambda-\mu}\).
Correct: both right sides carry the factor \(\frac1{2\pi i}\), as (14) and (17) do.
Evidence: all four channels come from the same integral (12)–(13), whose prefactor is
\(\frac1{2\pi i}\); the beta integrals \(\int_0^tx^{\lambda-1}(t-x)^{-\mu}dx\) and
\(\int_t^\infty x^{\lambda-1}(x-t)^{-\mu}dx\) give the gamma quotients.
Target: [KV04.1.07].

### E04.1.04. Whittaker channel (19): gamma denominator

Status: Confirmed.
Location: Part II, Chapter 4, §1.4, p. 207, (19).
Printed: \(K_{-+}(\lambda,\mu;\chi,g_1(t))=\frac1{2\pi it}\frac{\Gamma(\lambda)\Gamma(1-\mu)}
{\Gamma(\lambda-\mu-1)}M_{(1-\lambda-\mu)/2,(\lambda-\mu)/2}(t^2)\).
Correct: denominator \(\Gamma(\lambda-\mu+1)\).
Evidence: with \(\sigma=-1\), \(K_{-+}=\frac{e^{-t^2/2}}{2\pi i}\int_0^tx^{\lambda-1}e^{tx}
(t-x)^{-\mu}dx=\frac{e^{-t^2/2}}{2\pi i}t^{\lambda-\mu}B(\lambda,1-\mu)
{}_1F_1(\lambda;\lambda-\mu+1;t^2)\), which equals the corrected expression; (21) for \(g_2\) has
the same structure and is printed with \(\Gamma(\lambda-\mu+1)\).
Target: [KV04.1.08].

### E04.1.05. Parabolic-cylinder kernels: convergence conditions

Status: Confirmed.
Location: Part II, Chapter 4, §1.5, p. 207, (22)–(23).
Printed: (22) for "\(\Re\lambda>0\), \(r\ne0\), \(s\ne0\)"; (23) for "\(\Re\lambda>0\),
\(\Re\lambda s>0\)".
Correct: (22) needs \(\Re(\alpha r)>0\) (and \(\Re\lambda>0\)); (23) needs \(\Re(\alpha s)>0\).
Evidence: the defining integral \(\int_0^\infty x^{\lambda-1}e^{-\alpha(rx^2+sx)}dx\) diverges for
\(\Re(\alpha r)<0\); for \(r=0\) it is \(\Gamma(\lambda)(\alpha s)^{-\lambda}\) exactly when
\(\Re(\alpha s)>0\), a condition independent of \(\lambda\).
Target: [KV04.1.09].

### E04.1.06. Elliptic matrix element of the boost: argument

Status: Confirmed.
Location: Part II, Chapter 4, §1.6, p. 208, first display after the kernel definitions.
Printed: \(K^{11}\big(m,n;\chi,\left(\begin{smallmatrix}\cosh t&\sinh t\\\sinh t&\cosh t
\end{smallmatrix}\right)\big)=\mathfrak P^\tau_{m+\epsilon,n+\epsilon}(\cosh t)\).
Correct: argument \(\cosh2t\): in the source's \(\mathfrak P\),
\(K^{11}=\mathfrak P^\tau_{m+\epsilon,n+\epsilon}(\cosh2t)\); with the [KV02.2.01] function,
\(K^{11}=i^{m-n}\mathcal P^\tau_{m+\epsilon,n+\epsilon}(\cosh2t)\).
Evidence: the matrix has eigenvalues \(e^{\pm t}\), i.e. it is conjugate to \(g_2(2t)\), and the
same
page gives \(\mathfrak P(\cosh t)\) for \(g_2(t)\). For \(m=n=\epsilon=0\) the value is the
spherical function \(P_\tau(\cosh2t)\). Direct evaluation of
\(\frac1\pi\int(T_\chi(g)\psi_n)\overline{\psi_m}dx\) at \(\tau=-\frac12+0.4i\), \(t=0.6\) agrees
with \(i^{m-n}\mathcal P(\cosh 1.2)\) to 12 digits for \((m,n)\in\{(0,0),(1,0),(0,2),(2,1)\}\),
\(\epsilon\in\{0,\frac12\}\).
Target: [KV04.1.11].

### E04.1.07. Phase convention of \(\mathfrak P^\tau_{mn}\) in Chapter 4

Status: Normalization check.
Location: Part II, Chapter 4, §1.6, p. 208, the five \(K^{11}\) displays; §3.6, pp. 222.
Printed: \(K^{11}(m,n;\chi,g_2(t))=i^{n-m}\mathfrak P^\tau_{m+\epsilon,n+\epsilon}(\cosh t)\), and
no phase for the boost and the unipotents.
Correct: with \(\mathcal P^\tau\) defined by the circle integral of [KV02.2.01],
\(K^{11}(m,n;\chi,g_2(t))=\mathcal P^\tau_{m+\epsilon,n+\epsilon}(\cosh t)\), and the boost and
unipotent formulas carry \(i^{m-n}\). All five displays are consistent with
\(\mathfrak P^{\mathrm{Ch.4}}_{m+\epsilon,n+\epsilon}=i^{m-n}\mathcal
P^\tau_{m+\epsilon,n+\epsilon}\).
Evidence: direct numerical evaluation of all five \(K^{11}\) in the line model (see [E04.1.06]).
Whether the Chapter 2 definition of \(\mathfrak P\) itself contains this phase is not settled
here; the synopsis uses [KV02.2.01] throughout.
Target: [KV04.1.11], [KV04.3.12], [KV04.3.14].

### E04.1.08. Hyperbolic boost kernel (25): \(\cot\) for \(\coth\)

Status: Confirmed.
Location: Part II, Chapter 4, §1.6, p. 208, (25).
Printed: \(\dots\cot^{\lambda+\mu}t\cosh^{2\tau}tF(\lambda,\mu;-2\tau;-\sinh^{-2}t)\).
Correct: \(\coth^{\lambda+\mu}t\).
Evidence: \(K^{22}_{++}(g_1(t))=\frac1{2\pi i}\int_0^\infty x^{\lambda-1}(x\sinh t+\cosh t)^{2\tau}
\big(\frac{x\cosh t+\sinh t}{x\sinh t+\cosh t}\big)^{-\mu}dx\); at
\((\lambda,\mu,\tau,t)=(0.2,0.37+0.2i,-0.4,0.7)\) quadrature gives \(0.04666-0.93386i\), the
\(\coth\) formula \(0.04676-0.93488i\) (quadrature tail error \(\sim10^{-3}\)); the \(\cot\) formula
differs by the factor \((\coth t/\cot t)^{\lambda+\mu}\).
Target: [KV04.1.12].

### E04.1.09. Weyl-element kernel (30): Bessel index

Status: Confirmed.
Location: Part II, Chapter 4, §1.6, p. 209, (30).
Printed: \([J_{-2\tau+1}(2\sqrt{\lambda\mu})-(-1)^{2\epsilon}J_{2\tau+1}(2\sqrt{\lambda\mu})]\).
Correct: \([J_{-2\tau-1}(2\sqrt{\lambda\mu})-(-1)^{2\epsilon}J_{2\tau+1}(2\sqrt{\lambda\mu})]\).
Evidence: \(K^{33}(\lambda,\mu;\chi,s)=\frac1{2\pi}\int_{\mathbb
R}|x|^{2\tau}\mathrm{sgn}(x)^{2\epsilon}
e^{i\mu/x+i\lambda x}dx\) is a combination of \(H^{(1,2)}_{2\tau+1}\), hence of
\(J_{\pm(2\tau+1)}\). With the corrected index, (30) and (31) agree with the integral to 11 digits
at
\(\tau=-0.35\), \(\epsilon\in\{0,\frac12\}\), \((\lambda,\mu)\in\{(\pm0.6,\pm0.9)\}\) (all sign
combinations).
Target: [KV04.1.14].

### E04.1.10. Elliptic-to-hyperbolic kernel (35): a base

Status: Confirmed.
Location: Part II, Chapter 4, §1.6, p. 210, (35).
Printed:
\(K^{21}_-(\lambda,n;\chi,g_-(t))=(-1)^{2\epsilon}\frac{\Gamma(\lambda)\Gamma(-2\tau-\lambda)}
{\pi\Gamma(-2\tau)}(-t-i)^{\tau-n-\epsilon}(t-i)^{\tau+\lambda+n+\epsilon}F(\dots)\), \(t<0\).
Correct: \((i-t)^{\tau+\lambda+n+\epsilon}\) in place of \((t-i)^{\tau+\lambda+n+\epsilon}\),
principal
powers.
Evidence: \(\psi_n(-y)=(-1)^{2\epsilon}\psi_{-n-2\epsilon}(y)\) for \(y>0\) gives
\(K^{21}_-(\lambda,n;g_-(t))=(-1)^{2\epsilon}K^{21}_+(\lambda,-n-2\epsilon;g_-(-t))\); Pfaff's
transformation turns (34) into the corrected (35). Quadrature of
\(\frac1\pi\int_0^\infty x^{\lambda-1}\psi_n(t-x)dx\) at \(\tau=-0.8\), \(t=-0.7\),
\(\lambda\in\{0.6,0.3+0.2i\}\), \(n\in\{-1,0,1,2\}\), \(\epsilon\in\{0,\frac12\}\) agrees with the
corrected formula (ratio \(1\) to \(10^{-6}\)); the printed formula is off by
\(n\)-dependent phases (e.g. \(e^{-0.8\pi i}\) at \(n=0\), \(e^{0.8\pi i}\) at \(n=1\)). (34)
agrees with the same integral (ratio \(1\)).
Target: [KV04.1.15].

### E04.1.11. Elliptic-to-parabolic kernel (36): constant and gamma factor

Status: Confirmed.
Location: Part II, Chapter 4, §1.6, p. 210, (36).
Printed: \(K^{31}(\lambda,n;\chi,g_2(t))=\frac{2^{\tau+1}e^{\pi i(-n-\epsilon)}}
{\pi\Gamma(\varrho(n+\epsilon)-\tau)}|\lambda|^{-\tau-1}W_{-\varrho(n+\epsilon),\tau+1/2}
(2|\lambda|e^{-t})\).
Correct: \(K^{31}(\lambda,n;\chi,g_2(t))=\frac{2^{\tau+1}e^{-\pi i(n+\epsilon)}}
{\Gamma(-\varrho(n+\epsilon)-\tau)}|\lambda|^{-\tau-1}W_{-\varrho(n+\epsilon),\tau+1/2}
(2|\lambda|e^{-t})\) (no factor \(\pi\); \(\Gamma(-\varrho(n+\epsilon)-\tau)\)), for the source's
definition \(K^{31}=\frac1\pi\int(T_\chi(g)\psi_n)(x)e^{i\lambda x}dx\).
Evidence: at \(t=0\), \(\int(x+i)^{\tau-n-\epsilon}(x-i)^{\tau+n+\epsilon}e^{i\lambda x}dx\) was
computed by oscillatory quadrature at \(\tau=-0.8\) for \((n,\epsilon,\lambda)\in\{(0,0,0.7),
(1,0,\pm0.7),(-2,0,\pm0.9),(0,\frac12,0.6),(1,\frac12,-0.6)\}\); it equals \(\pi\) times the
corrected right side in every case. At \(n=0\), \(\tau=-\frac12+0.4i\): \(\int|K^{31}|^2d\lambda\)
is
\(2\) (Plancherel, \(\|\psi_0\|^2=\pi\)) for the corrected formula and \(2/\pi^2\) for the printed
one.
For \(t\ne0\) use \(K^{31}(\lambda,n;g_2(t))=e^{-(\tau+1)t}K^{31}(\lambda e^{-t},n;e)\).
Target: [KV04.1.16], [KV04.3.12], [KV04.3.14].

### E04.1.12. Discrete series: spectral normalizations and (46)

Status: Normalization check.
Location: Part II, Chapter 4, §1.7, p. 211, the three bases and (46).
Printed: \(e^2_\lambda=\frac1{\sqrt{2\pi}}x^{2i\lambda-1/2}\), \(e^3_\lambda=\lambda^{-1/2}
\delta(x-\lambda)\), and \(K^{31}(\lambda,n;l,g_2(t))=\big[\frac{2n!}{(-2l+n-1)!}\big]^{1/2}
\lambda^{-2l-1/2}e^{2lt}\exp(-\frac{\lambda e^{-t}}2)L_n^{-2l-1}(\lambda^2e^{-t})\).
Correct: \(\langle e^2_\lambda,e^2_\mu\rangle=\frac12\delta(\lambda-\mu)\), so a unitary hyperbolic
transform uses \(\pi^{-1/2}x^{2i\lambda-1/2}\) (this is the normalization in which the p. 212
display for \(K^{21}\) has \(\int|K^{21}|^2d\lambda=1\)); \(\langle e^3_\lambda,e^3_\mu\rangle=
\lambda^{-1}\delta(\lambda-\mu)\). In the explicit model of [KV04.1.19], with
\(K^{31}(\lambda,n;l,g)=\lambda^{1/2}(T(g)e^1_n)(\lambda)\), the kernel is
\(\big[\frac{2n!}{(n+k)!}\big]^{1/2}\lambda^{-2l}e^{lt}\exp(-\frac{\lambda^2e^{-t}}2)
L_n^k(\lambda^2e^{-t})\). Open: which realization and parametrization of the parabolic variable
the source intends (its §3.6 identities use \(L_n(2\lambda e^{\pm t})\) and \(e^{-\lambda e^{\pm
t}}\),
i.e. the variable \(x^2/2\)).
Evidence: the printed (46) has Gaussian \(e^{-\lambda e^{-t}/2}\) but Laguerre argument
\(\lambda^2e^{-t}\), while \(e^1_n\) pairs \(e^{-x^2/2}\) with \(L_n(x^2)\); the factor
\(e^{2lt}\) is not that of a unitary dilation. The model kernel reproduces the corrected (45)
([E04.1.13]) and yields the Laguerre series [KV04.3.15], both checked numerically.
Target: [KV04.1.19], [KV04.1.22].

### E04.1.13. Discrete-series matrix element (45)

Status: Confirmed.
Location: Part II, Chapter 4, §1.7, p. 211, (45).
Printed: \(K^{11}(m,n;l,g_2(t))=\frac{(-1)^m[(-2l+m-1)!(-2l+n-1)!m!n!]^{1/2}}{(-2l+m+n-1)!}
(\sinh\frac t2)^{m+l}(\cosh\frac t2)^{2l-m-n}F(-m,-n;2l-m-n+1;\coth^2\frac t2)\).
Correct: \(K^{11}(m,n;l,g_2(t))=(-1)^m\frac{(-2l+m+n-1)!}{[(-2l+m-1)!(-2l+n-1)!m!n!]^{1/2}}
(\sinh\frac t2)^{m+n}(\cosh\frac t2)^{2l-m-n}F(-m,-n;2l-m-n+1;\coth^2\frac t2)\).
Evidence: at \(m=n=0\) the printed form is \(\sinh^l\frac t2\cosh^{2l}\frac t2\), singular at
\(t=0\) where the value must be \(1\); the corrected form gives \(\delta_{mn}\) at \(t=0\). In the
model of [KV04.1.19], \(\int_0^\infty e^{-t/4}e^1_n(e^{-t/2}x)e^1_m(x)dx\) agrees with the corrected
formula to 15 digits for \(l\in\{-1,-\frac32\}\), \(t=\pm0.6\),
\((m,n)\in\{(0,0),(1,0),(0,1),(2,1),(1,3)\}\).
Target: [KV04.1.21], [KV04.3.15].

### E04.1.14. Jacobi form (47) of the discrete-series kernel \(K^{21}\)

Status: Confirmed.
Location: Part II, Chapter 4, §1.7, p. 211, (47).
Printed: \(K^{21}(\lambda,n;l,g_-(t))=\big[\frac{n!}{2\pi(n-2l-1)!}\big]^{1/2}\Gamma(-l-i\lambda)
2^{-l-i\lambda}(1-it)^{l+i\lambda}P_n^{(-2l-1,-n-i\lambda)}\big(\frac{it+3}{it-1}\big)\).
Correct (in the convention of the p. 212 display): \(\big[\frac{n!}{2\pi(n-2l-1)!}\big]^{1/2}
\Gamma(-l-i\lambda)2^{-l-i\lambda}(1+it)^{l+i\lambda}\big(\frac{it-1}{it+1}\big)^n
P_n^{(-2l-1,\,l-n+i\lambda)}\big(\frac{it+3}{it-1}\big)\).
Evidence: the p. 212 display \(2^{-l-i\lambda}[\frac{(n-2l-1)!}{2\pi n!}]^{1/2}
\frac{\Gamma(-l-i\lambda)}{(-2l-1)!}(1+it)^{l+i\lambda}F(-n,-l-i\lambda;-2l;\frac2{1+it})\) is
converted by \(P_n^{(\alpha,\beta)}(x)=\frac{(\alpha+1)_n}{n!}(\frac{1+x}2)^n
F(-n,-n-\beta;\alpha+1;\frac{x-1}{x+1})\). At \(l=-\frac32\), \(\lambda=0.37\), \(t=0.8\) the
corrected form equals the p. 212 display for \(n=0,\dots,3\); the printed (47) agrees with neither
the p. 212 display nor its \(t\mapsto-t\) image for \(n\ge1\).
Target: [KV04.1.23], [KV04.3.16].

### E04.1.15. Meixner–Pollaczek form of \(K^{21}\): sign of the variable

Status: Confirmed.
Location: Part II, Chapter 4, §1.8, p. 212, last display before the orthogonality relation.
Printed: \(\dots\Gamma(-l-i\lambda)e^{-in\varphi}(1-e^{-2i\varphi})^{-l-i\lambda}
P_n^{-l}(\lambda;\varphi)\).
Correct: \(P_n^{-l}(-\lambda;\varphi)\).
Evidence: the hypergeometric factor is \(F(-n,-l-i\lambda;-2l;1-e^{-2i\varphi})\), which is
\(F(-n,k+ix;2k;1-e^{-2i\varphi})\) with \(k=-l\) and \(x=-\lambda\). Numerically, at
\(l=-\frac32\), \(n=2\), \(\lambda=0.37\), \(t=0.8\), the display with \(P_n^{-l}(-\lambda)\)
reproduces the preceding \(F\)-form; with \(P_n^{-l}(\lambda)\) it does not.
Target: [KV04.1.27].

### E04.1.16. Meixner–Pollaczek norm

Status: Confirmed.
Location: Part II, Chapter 4, §1.8, p. 212, final display.
Printed: \(\int_{\mathbb R}P_m^kP_n^k|\Gamma(k+i\lambda)|^2e^{\lambda(2\varphi-\pi)}d\lambda=
\frac{\pi(2k+n-1)!}{n!}(2\sin\varphi)^{-2k}\delta_{mn}\).
Correct: \(\frac{2\pi\,\Gamma(n+2k)}{n!}(2\sin\varphi)^{-2k}\delta_{mn}\); the printed value is half
the correct one.
Evidence: \(k=1,\varphi=\pi/2,n=0\): \(\int_{\mathbb R}|\Gamma(1+ix)|^2dx=\int\frac{\pi x}{\sinh\pi
x}
dx=\frac\pi2\), while the printed value is \(\frac\pi4\). Quadrature at
\((k,\varphi,n)\in\{(1.5,2.245,2),(1,1.1,1),(0.7,0.6,3)\}\) agrees with the corrected value to 14
digits; it is the Koekoek–Swarttouw norm. It is also what \(\int|K^{21}|^2d\lambda=1\) requires.
Target: [KV04.1.28].

### E04.2.01. Hankel Barnes integrals: half-plane

Status: Confirmed.
Location: Part II, Chapter 4, §2.2, p. 214, the two displays at the top.
Printed: for \(H^{(1)}_\lambda\): "\(\Im z<0\), \(a>0\), \(a>\Re\lambda\)"; for
\(H^{(2)}_\lambda\): "\(\Im z<0\), \(a>0\), \(a>\Re\lambda\)".
Correct: \(\Im z>0\) for \(H^{(1)}_\lambda\) (precisely \(0<\arg z<\pi\)); \(\Im z<0\) for
\(H^{(2)}_\lambda\).
Evidence: the \(H^{(1)}\) integral is the Macdonald Barnes integral at \(-iz\), which converges for
\(|\arg(-iz)|<\pi/2\); numerically it reproduces \(H^{(1)}_\lambda(1.5+0.5i)\) and diverges at
\(1.5-0.5i\).
Target: [KV04.2.03].

### E04.2.02. Barnes integral for \(D_\lambda\): Gaussian factor

Status: Confirmed.
Location: Part II, Chapter 4, §2.2, p. 214, last display.
Printed: \(D_\lambda(x)=\frac{e^{-x^2/2}}{4\pi i\Gamma(-\lambda)}\int2^{-(\lambda+\mu)/2}
\Gamma(\mu)\Gamma(-\frac{\lambda+\mu}2)x^{-\mu}d\mu\).
Correct: prefactor \(e^{-x^2/4}\).
Evidence: closing to the left gives \(\frac{e^{-x^2/2}}{2\Gamma(-\lambda)}\sum_k\frac{(-x)^k}{k!}
2^{(k-\lambda)/2}\Gamma(\frac{k-\lambda}2)\), while the integral definition of \(D_\lambda\) gives
the same series with \(e^{-x^2/4}\). Numerically at \(\lambda=-0.7\), \(x=0.9\), \(a=0.3\), the
\(e^{-x^2/4}\) version equals \(D_\lambda(x)=0.650549\dots\) to 15 digits.
Target: [KV04.2.07].

### E04.2.03. Mellin transform of \(K_\nu\): group relation

Status: Confirmed.
Location: Part II, Chapter 4, §2.3, p. 215, first display.
Printed: \(g(0;r_1,r_2)g(0;r_2,0)=g(\theta;0,0)g(0;r,0)g(-\theta;0,0)\) with (56)
\(\tanh\theta=r_1/(r_1+r_2)\), \(r^2=r_2^2+2r_1r_2\).
Correct: \(g(0;r_1,r_1)g(0;r_2,0)=g(\theta;0,0)g(0;r,0)g(-\theta;0,0)\).
Evidence: the left side is \(g(0;r_1+r_2,r_1)\), whose invariants are exactly (56); the printed left
side \(g(0;r_1+r_2,r_2)\) would give \(\tanh\theta=r_2/(r_1+r_2)\), \(r^2=r_1^2+2r_1r_2\). The
derivation uses the null kernel (4) of \(g(0;r_1,r_1)\), which produces \(\Gamma(v-\lambda)
r_1^{\lambda-v}\) in (57). (57) was checked numerically, and its residue series for \(r_2>2r_1\).
Target: [KV04.2.08].

### E04.2.04. Three regimes of (58)–(59): geometry and exponent

Status: Confirmed.
Location: Part II, Chapter 4, §2.3, pp. 215–216, after (59).
Printed: for \(0<2r_1<r_2\): \(I_1=e^{-i\lambda\theta}r_1^\lambda H^{(1)}_{-\lambda}(r)\) with
\(\tanh\theta=\frac{r_1}{r_1^2-r_2^2}\); for \(I_2\): "\(\tan\theta=\frac{r_1-r_2}{r_1}\)" and
"\(\tan\theta=\frac{r_1}{r_1-r_2}\)".
Correct: \(I_1=e^{-\lambda\theta}r_1^\lambda H^{(1)}_{-\lambda}(r)\) with
\(\tanh\theta=\frac{r_1}{r_1-r_2}\); for \(I_2\), \(\tanh\theta=\frac{r_1-r_2}{r_1}\) and
\(\tanh\theta=\frac{r_1}{r_1-r_2}\).
Evidence: \(g(0;r_1,r_1)g(0;-r_2,0)=g(0;r_1-r_2,r_1)\), which for \(r_2>2r_1\) equals
\(g(\theta;0,0)g(0;-r,0)g(-\theta;0,0)\) with \(-r\cosh\theta=r_1-r_2\), \(-r\sinh\theta=r_1\);
\(\frac{r_1}{r_1^2-r_2^2}\) is not dimensionless. For \(r_1=0.5\), \(r_2=1.6\), \(\lambda=0.3\) the
convergent residue series of \(I_1\) is \(0.611193+0.418884i\), equal to
\(e^{-\lambda\theta}r_1^\lambda H^{(1)}_{-\lambda}(r)\); \(e^{-i\lambda\theta}\) gives
\(0.4689+0.4350i\). The residue series of \(I_2\) equals \(e^{-\lambda(\theta-\pi i)}r_1^\lambda
K_\lambda(r)\) with \(\tanh\theta=r_1/(r_1-r_2)\).
Target: [KV04.2.09].

### E04.2.05. Whittaker \(M\) convolution from \(SL(2,\mathbb R)\)

Status: Confirmed.
Location: Part II, Chapter 4, §2.4, p. 217, second equality after (61).
Printed: \(\frac1{2\pi i}\int\Gamma(1-\nu)\Gamma(\nu-\mu)t^\nu s^{-\nu}M_{\tau+\nu,\tau+1/2}
(\frac{i\lambda}t)d\nu=\Gamma(1-\mu)t^{-\tau}s^{-\mu}e^{i\lambda/2t}e^{-i\lambda/2(t+s)}
(t+s)^{\mu+\tau}M_{\tau+\mu,\tau+1/2}(\frac{i\lambda}{t+s})\).
Correct: either replace both \(M\)-arguments by \(-\frac{i\lambda}t\), \(-\frac{i\lambda}{t+s}\)
(the form consistent with (38)), or keep \(+i\lambda\) and replace the exponentials by
\(e^{-i\lambda/(2t)}e^{i\lambda/(2(t+s))}\).
Evidence: at \(\tau=-0.3\), \(\mu=0.2\), \(\lambda=0.9\), \(t=1\), \(s=0.6\), \(a=0.5\), quadrature
of the
left side is \(0.456601+0.668052i\); the printed right side is \(0.209631+0.781558i\); both
corrected forms agree with the quadrature to 15 digits. The first equality (with \(W\)) agrees as
printed.
Target: [KV04.2.11].

### E04.2.06. Translation series (63) for \(D_\lambda\)

Status: Confirmed.
Location: Part II, Chapter 4, §2.5, p. 217, (63).
Printed: \(D_\lambda(x+y)=e^{(2xy+y^2)}\sum_{k=0}^\infty\frac{\Gamma(\lambda+1)}
{k!\Gamma(\lambda-k+1)}y^kD_{\lambda+k}(x)\).
Correct: \(D_\lambda(x+y)=e^{-(2xy+y^2)/4}\sum_{k=0}^\infty\frac{\Gamma(\lambda+1)}
{k!\Gamma(\lambda-k+1)}y^kD_{\lambda-k}(x)\) (the residue series of (62) at the poles of
\(\Gamma(\mu-\lambda)\)); equivalently \(D_\lambda(x+y)=e^{xy/2+y^2/4}\sum_k\frac{(-y)^k}{k!}
D_{\lambda+k}(x)\).
Evidence: (62) is correct (quadrature at \(\lambda=-0.6\), \(a=-0.3\), \(x=0.6\), \(y=0.45\) agrees
to
15 digits). Its residues at \(\mu=\lambda-k\) give the first corrected series. At \(\nu=0.37\),
\(x=0.6\), \(y=0.45\) both corrected series equal \(D_\nu(x+y)=0.824918\dots\) to 15 digits. The
printed exponent lacks the factor \(-\frac14\), and the printed index \(\lambda+k\) is inconsistent
with the residues.
Target: [KV04.2.13].

### E04.2.07. Hypergeometric Mellin transform: boost parameter

Status: Confirmed.
Location: Part II, Chapter 4, §2.6, p. 218.
Printed: \(\cosh\theta=\cosh2\varphi+z\sinh2\varphi\).
Correct: \(\cosh2\theta=\cosh2\varphi+z\sinh2\varphi\), i.e.
\(\cosh^2\theta=\cosh\varphi(\cosh\varphi+z\sinh\varphi)\).
Evidence: comparing the \((2,2)\) and \((1,1)\) entries of
\(g_1(\varphi)g_-(z)=h(t_1)g_1(\theta)h(t_2)\) gives \(e^{t_1+t_2}\cosh\theta=\cosh\varphi\) and
\(e^{-t_1-t_2}\cosh\theta=\cosh\varphi+z\sinh\varphi\). The printed \(e^{4t_1},e^{4t_2}\) are
correct. At \(\varphi=0.6\), \(z=0.8\) the matrix identity holds to \(10^{-11}\) with the corrected
\(\theta\), and the Mellin identity of [KV04.2.14] then holds to 10 digits
(\(0.7616875327\) both sides, \(\lambda=0.2\), \(\mu=0.8\), \(\tau=-0.4\)).
Target: [KV04.2.14].

### E04.2.08. Range of the residue series for K_λ

Status: Confirmed.
Location: Part II, Chapter 4, §2.3, p. 215, display after (57).
Printed: \(\sum_{n=0}^\infty\frac{(-1)^n}{n!}r_1^nK_{\lambda-n}(r_2)=e^{\lambda\theta}K_\lambda(r)\)
for \(r_1>0\), \(r_2>0\), with \(\theta,r\) from (56).
Correct: the series converges to \(e^{\lambda\theta}K_\lambda(r)\) for \(r_2>2r_1\), and for
\(r_2=2r_1\) when \(\mathrm{Re}\,\lambda>-1\); it diverges for \(0<r_2<2r_1\). The Barnes integral
(57)
holds for all \(r_1,r_2>0\).
Evidence: \(K_{n-\lambda}(r_2)\sim\frac12\Gamma(n-\lambda)(2/r_2)^{n-\lambda}\) makes the
\(n\)-th term of order \((2r_1/r_2)^nn^{-\mathrm{Re}\,\lambda-1}\). With \(\rho^2=1+2r_1/r_2\), (56)
gives
\(e^{\lambda\theta}=\rho^\lambda\) and \(r=\rho r_2\), so the series is the multiplication theorem
DLMF 10.44.2, valid for \(|\rho^2-1|<1\). Numerically, at \(\lambda=0.3\), \(r_1=0.4\),
\(r_2=1.5\) the series, (57) and \(e^{\lambda\theta}K_\lambda(r)\) all equal
\(0.14774037470429596\). At \(\lambda=0.3+0.5i\), \(r_1=1\), \(r_2=1.2\), (57) equals
\(e^{\lambda\theta}K_\lambda(r)=0.1277486564721413+0.0407361894956611i\), while the 80-term
partial sum has size \(3\cdot10^{14}\). At \(\lambda=0.3\), \(r_1=2\), \(r_2=1\), (57) gives
\(0.1106613781468125\) and the partial sums diverge. At \(r_2=2r_1=1\), \(\lambda=-0.5\), the
averaged partial sums tend to \(0.2154566\); at \(\lambda=-1.5\) the terms grow like \(n^{1/2}\).
Target: [KV04.2.08].

### E04.3.01. Whittaker addition theorem: \(e^{\tau_1}\)

Status: Confirmed.
Location: Part II, Chapter 4, §3.3, p. 220, first formula.
Printed: \(e^{\tau_1}=(t-se^\tau)/r\) for \(g_1(t)\varepsilon(\tau)g_1(s)\).
Correct: \(e^{\tau_1}=(t+se^\tau)/r\).
Evidence: multiplying the triangular matrices gives \(e^{\tau_1}r=t+se^\tau\),
\(e^{\tau-\tau_1}r=s+te^\tau\), whence \(r^2=t^2+2ts\cosh\tau+s^2\) and \(b=ts\sinh\tau\) as
printed.
The printed value vanishes at \(t=s\), \(\tau=0\). (The printed value is the correct one for the
second product \(g_1(t)\varepsilon(\tau)g_1(-s)\).) The left-closure residue series of the
integral at \(\lambda=0.1\), \(\mu=0.2\), \(t=0.8\), \(s=0.6\), \(\tau=0.3\) is \(0.1146372\),
equal to
the right side with the corrected \(e^{\tau_1}\).
Target: [KV04.3.06].

### E04.3.02. Whittaker addition theorem for the crossing product

Status: Open check.
Location: Part II, Chapter 4, §3.3, p. 220, second formula.
Printed: \(\frac1{2\pi i}\int\frac{\Gamma(\nu+1/2)}{\Gamma(\lambda+\mu+\nu+1)}e^{-\tau\nu}
W_{(\lambda-\mu-\nu)/2,(\lambda-\mu+\nu)/2}(t^2)W_{(\lambda+\mu-\nu)/2,(\lambda+\mu+\nu)/2}(s^2)d\nu
 =\frac{1}{\Gamma(2\mu+1)}\frac{ts}r
\exp[(\lambda+\mu)\tau-2\mu\tau_1-ts\sinh\tau]M_{-\lambda,\mu}(r^2)\).
Correct: unknown. The geometry (\(b=-ts\sinh\tau\), \(r^2=2ts\cosh\tau-t^2-s^2\),
\(e^{\tau_1}=(t-se^\tau)/r\)) is correct. Since \(g_1(-s)\) has the crossing channel \(K_{-+}\) of
[KV04.1.08], the second factor is expected to be an \(M\)-function of \(s^2\), not
\(W(s^2)\); the exact form is not settled.
Evidence: the residue series of the printed left side did not match the right side under any of
the sign variants tested (\(\pm\tau\), \(\pm\lambda\) in the \(M\) index).
Target: [KV04.3.07].

### E04.3.03. Parabolic-cylinder addition theorem (68): \(2\pi\) for \(2\pi i\)

Status: Confirmed.
Location: Part II, Chapter 4, §3.4, p. 221, (68).
Printed: prefactor \(\frac1{2\pi}\) of the Barnes integral.
Correct: \(\frac1{2\pi i}\).
Evidence: at \(\lambda=0.9\), \(\mu=-0.6\), \(a=0.1\), \(t=0.5\), \(x_1=0.3\), \(x_2=0.8\), the
integral with
\(\frac1{2\pi i}\) equals the right side \(0.2694944473\) to 15 digits; the residue series and the
product formula, which the source derives from (68), also require \(\frac1{2\pi i}\).
Target: [KV04.3.08].

### E04.3.04. Residue series after (68)

Status: Confirmed.
Location: Part II, Chapter 4, §3.4, p. 221, display after (68).
Printed: \(\sum_{n=1}^\infty\frac{\tan^ntD_{\mu-n}(x_1)D_n(x_2)}{n!\Gamma(\mu-n+1)}=
\frac{\cos^{-\mu}tD_\mu(x_1\cos t+x_2\sin t)}{\Gamma(1+\mu)\exp[-\frac14(x_1\sin t-x_2\cos t)^2]}\),
with no range beyond the setting \(r_1=\cos^2t\), \(r_2=\sin^2t\) of (68), that is
\(0<t<\pi/2\).
Correct: \(\sum_{n=0}^\infty\frac{\tan^ntD_{\mu-n}(x_1)D_n(x_2)}{n!\Gamma(\mu-n+1)}=
\frac{\cos^{-\mu}t}{\Gamma(1+\mu)}\exp[-\tfrac14(x_1\sin t-x_2\cos t)^2]
D_\mu(x_1\cos t+x_2\sin t)\) for \(0\le t<\pi/4\), \(\mu\in\mathbb C\), \(x_1,x_2\in\mathbb R\);
also at \(t=\pi/4\) when \(x_1>0\), or \(x_1=0\) and \(\mathrm{Re}\,\mu>0\); and for \(0\le
t<\pi/2\) when
\(\mu\in\mathbb N\).
Evidence: the residue at \(n=0\) is present in the contour closure; at \(t=0\) the corrected
identity reduces to \(D_\mu(x_1)e^{-x_2^2/4}=D_\mu(x_1)D_0(x_2)\), while the printed one gives \(0\)
on the left. At \(\mu=0.4\), \(t=0.5\), \(x_1=0.3\), \(x_2=0.8\) both sides of the corrected
identity
are \(0.944267775\dots\) (15 digits). For \(\mu\notin\mathbb Z\) the large-order forms of
\(D_{\mu-n}(x_1)\), \(D_n(x_2)\) and \(1/\Gamma(\mu-n+1)\) make the \(n\)-th term of order
\(\tan^nt\,n^{-1-\mathrm{Re}\,\mu/2}e^{-x_1\sqrt n}\) times a bounded oscillating factor. At
\(\mu=0.4\),
\(t=1\), \(x_1=0.3\), \(x_2=0.8\) the terms have size \(1.0\cdot10^4\) at \(n=40\) and
\(1.7\cdot10^{11}\) at \(n=80\). At \(t=\pi/4\), \(\mu=0.4\), \(x_1=1\), \(x_2=0.5\) the series
gives \(1.036676298571\dots\) on both sides; with \(x_1=-1\) the terms grow like
\(e^{\sqrt n}\). For \(t<\pi/4\) no condition on \(\mu\) is needed: at \(\mu=-1.3+0.4i\),
\(t=0.5\), \(x_1=0.3\), \(x_2=0.8\) both sides are \(-0.2299954941183605+0.0608183057415121i\).
DLMF 12.13.5 (\(a=-\mu-\frac12\)) states \(0\le t\le\pi/4\) and \(\mathrm{Re}\,\mu\ge0\).
Target: [KV04.3.09].

### E04.3.05. First mixed identity (Whittaker product integral)

Status: Confirmed.
Location: Part II, Chapter 4, §3.6, p. 222, first display.
Printed: \(\int_{-\infty}^\infty\frac{W_{-\varrho(m+\epsilon),\tau+1/2}(2|\lambda|e^t)
W_{-\varrho(n+\epsilon),\tau+1/2}(2|\lambda|e^{-s})}{\Gamma(\tau+\varrho(m+\epsilon)+1)
\Gamma(-\tau\varrho(n+\epsilon))}|\lambda|^{-1}d\lambda=\pi^2(-i)^{n-m}
\mathfrak P^\tau_{m+\epsilon,n+\epsilon}(\cos(t+s))\).
Correct: denominator \(\Gamma(\tau+1-\varrho(m+\epsilon))\Gamma(-\tau-\varrho(n+\epsilon))\), right
side \((-i)^{n-m}\mathfrak P^\tau_{m+\epsilon,n+\epsilon}(\cosh(t+s))
 =(-1)^{m-n}\mathcal P^\tau_{m+\epsilon,n+\epsilon}(\cosh(t+s))\) (no \(\pi^2\)).
Evidence: for \(m=n=\epsilon=0\) the left side is \(\frac{2}{\Gamma(\tau+1)\Gamma(-\tau)}
\int_0^\infty W_{0,\tau+1/2}(2\lambda e^t)W_{0,\tau+1/2}(2\lambda e^{-s})\frac{d\lambda}\lambda
 =P_\tau(\cosh(t+s))\) by \(\int_0^\infty
K_\nu(ax)K_\nu(bx)dx=\frac{\pi^2P_{\nu-1/2}(\frac{a^2+b^2}{2ab})}
{4\sqrt{ab}\cos\nu\pi}\); numerically \(0.9592679763\) both sides at \(\tau=-0.3\), \(t=0.4\),
\(s=0.5\). With the corrected denominators the ratio to \(\mathcal P(\cosh(t+s))\) is
\((-1)^{m-n}\) to 10 digits for \((m,n,\epsilon)\in\{(1,0,0),(0,1,0),(1,2,0),(0,0,\frac12),
(1,-1,\frac12),(-1,1,0)\}\); with the printed \(\Gamma(\tau+\varrho(m+\epsilon)+1)\) it is not
constant. The \(\pi^2\) comes from the spurious \(\frac1\pi\) of (36) ([E04.1.11]).
Target: [KV04.3.12].

### E04.3.06. Second mixed identity (\(\mathfrak Q\)) constant

Status: Open check.
Location: Part II, Chapter 4, §3.6, pp. 222–223, second display.
Printed: the identity of [KV04.3.13].
Correct: unknown; the constant \(\frac{\sqrt\pi\,\Gamma(-\tau)c}{2^{\tau+3/2}a^{2(\lambda-\tau)}}
e^{3\pi\tau i/2}\) should be rederived.
Evidence: the identity is built from \(K^{31}(\mu,0;\chi,g_2(s))\) of (36), whose printed factor
\(\frac1\pi\) is spurious ([E04.1.11]), and from \(K^{23}\) via (42); the right side was not
checked.
Target: [KV04.3.13].

### E04.3.07. Third mixed identity (Whittaker series)

Status: Confirmed.
Location: Part II, Chapter 4, §3.6, p. 222, third display.
Printed: \(\sum_n\frac{i^n}{\Gamma(\varrho(n+\epsilon)-\tau)}W_{-\varrho(n+\epsilon),\tau+1/2}
(2|\lambda|e^{-t})\mathfrak P^\tau_{m+\epsilon,n+\epsilon}(\cosh s)=\frac{i^m}{\Gamma(\varrho(m+
\epsilon)-\tau)}W_{-\varrho(m+\epsilon),\tau+1/2}(2|\lambda|e^{-s-t})\).
Correct: \(\Gamma(-\varrho(n+\epsilon)-\tau)\) and \(\Gamma(-\varrho(m+\epsilon)-\tau)\) in the
denominators, and \(\mathfrak P^\tau_{n+\epsilon,m+\epsilon}\) (indices exchanged); in KV02.09
normalization the phases \(i^n,i^m\) become \((-1)^n,(-1)^m\) ([KV04.3.14]).
Evidence: it is \(K^{31}(g_2(t+s))=\sum_nK^{31}(g_2(t))K^{11}(n,m;g_2(s))\) with the corrected (36).
At \(\tau=-0.3\), \(t=0.2\), \(s=0.3\), the corrected identity holds to 15 digits for
\((m,\epsilon,\lambda)\in\{(0,0,0.8),(1,0,\pm0.8),(0,\frac12,0.6),(-1,\frac12,-0.6)\}\) (sum over
\(|n|\le25\)); with \(\mathcal P_{m,n}\) in place of \(\mathcal P_{n,m}\) it fails.
Target: [KV04.3.14].

### E04.3.08. Fourth mixed identity (Laguerre series)

Status: Confirmed.
Location: Part II, Chapter 4, §3.6, p. 223, first display.
Printed: \(\sum_{m=0}^\infty\frac{(-1)^m\tanh^m(s/2)}{(m+n+k)!(m+k)!}L_m^k(\lambda e^{-t})
F(-m,-n;-k-m-n;\coth^2\frac s2)=n!\exp(\frac{\lambda e^{-t}}2(1-e^{-s}))e^{-(k+1)s/2}
(\coth\frac t2)^n(\cosh\frac s2)^{k+1}L_n^k(\lambda e^{-s-t})\), "where \(k\) is a negative
integer".
Correct: coefficient \(\frac{(m+n+k)!}{(m+k)!}\) (not \(\frac1{(m+n+k)!(m+k)!}\)), factor
\(\coth^n\frac s2\) (not \(\coth^n\frac t2\)), and \(k=-2l-1\) a positive integer ([KV04.3.15]).
Evidence: the identity is the composition \(K^{31}(g_2(t))K^{11}(g_2(s))\); the printed coefficient
reflects the inverted factorial ratio of the printed (45) ([E04.1.13]). The corrected identity holds
to 18 digits at \((k,n,X,s)\in\{(1,0,0.7,0.4),(1,2,0.7,0.4),(2,1,1.3,\pm0.3),(3,3,0.5,0.6)\}\); the
printed left side gives e.g. \(0.2328\) against \(68.4165\) at \((1,2,0.7,0.4)\). The left side does
not depend on \(t\) except through \(\lambda e^{-t}\), so \(\coth\frac t2\) cannot be right.
Target: [KV04.3.15].

### E04.3.09. Fifth mixed identity (Whittaker–Jacobi)

Status: Open check.
Location: Part II, Chapter 4, §3.6, p. 223, second display.
Printed: the identity of [KV04.3.16], with \(P_n^{(-2l-1,-n-i\mu)}(\frac{is+3}{is-1})\).
Correct: unknown. If the identity was derived from the printed (47), the Jacobi factor should be
\((1+is)^{l+i\mu}(\frac{is-1}{is+1})^nP_n^{(-2l-1,l-n+i\mu)}(\frac{is+3}{is-1})\) up to the overall
prefactor ([E04.1.14]); the right side was not checked.
Evidence: the Jacobi factor coincides with that of the printed (47), which is inconsistent with the
\(F\)-form of \(K^{21}\) on p. 212 ([E04.1.14]).
Target: [KV04.3.16].

### E04.3.10. Sixth mixed identity (Bessel–Laguerre): phase

Status: Confirmed.
Location: Part II, Chapter 4, §3.6, p. 223, third display.
Printed: right side \(\lambda^{-l-1/2}e^{-2lt}\exp(-\lambda
e^t)e^{i(n-3l)\pi/2}L_n^{-2l-1}(2\lambda e^t)\).
Correct: phase \((-1)^n\) in place of \(e^{i(n-3l)\pi/2}\).
Evidence: the classical integral \(\int_0^\infty e^{-px}x^{\nu/2}J_\nu(2\sqrt{bx})L_n^\nu(cx)dx
 =(p-c)^np^{-n-\nu-1}b^{\nu/2}e^{-b/p}L_n^\nu(\frac{bc}{p(c-p)})\) with \(p=e^{-t}\), \(c=2e^{-t}\),
\(\nu=-2l-1\) gives \((-1)^n\). For \(n=0\) the printed phase \(e^{-3il\pi/2}\) is not real for
\(l=-1\), while both integrand and the remaining right side are real.
Target: [KV04.3.17].

### E04.3.11. Seventh mixed identity (Bessel–Whittaker)

Status: Open check.
Location: Part II, Chapter 4, §3.6, p. 224, first display.
Printed: \(\int_{-\infty}^\infty J_{-2l-1}(\frac{\lambda\nu}t)M_{-i\mu,-l-1/2}(-\frac{i\nu^2}{2s})
\exp(\frac{i\nu}{2s}+\frac{i\nu^2}{4s})d\nu=e^{-i\pi l}t(\frac s{t+s})^{-i\mu}
\exp(-\frac{i\lambda^2}{2t}+\frac{i\lambda^2}{4(s+t)})
\cdot M_{-i\mu,-l-1/2}(\frac{-i\lambda^2}{2(s+t)})\).
Correct: unknown. The identity is not invariant under the scaling \(\nu\to c\nu\), \(\lambda\to
c\lambda\), \(s\to c^2s\), \(t\to c^2t\) that the underlying kernels respect: the term
\(\frac{i\nu}{2s}\) and the measure \(d\nu\) (versus the factor \(t\) on the right) break it. A
quadratic term \(-\frac{i\nu^2}{2t}\) and the measure \(\nu\,d\nu\) over \((0,\infty)\) are
expected from \(K^{33}(g_+(t))\), but a numerical test of that variant did not give a constant
ratio, so the correction is not settled.
Evidence: scaling argument above.
Target: [KV04.3.18].

### E04.4.01. Hyperbolic Clebsch–Gordan coefficient: \(l\lambda\) for \(i\lambda\)

Status: Confirmed.
Location: Part II, Chapter 4, §4.1, p. 225, (72), constant \(B\).
Printed: denominator \(\Gamma(-l_1-l_2-l\lambda)\).
Correct: \(\Gamma(-l_1-l_2-i\lambda)\).
Evidence: with \(i\lambda\), \(B\) and the corrected continuous Hahn norm ([E04.4.02]) give
\(\int|\widetilde C_2|^2d\lambda_2=1\) identically (all factorials cancel), which is (74); the
lower \({}_3F_2\) parameter \(-l_1-l_2-i\lambda\) has the same form.
Target: [KV04.4.03].

### E04.4.02. Continuous Hahn weight and norm

Status: Confirmed.
Location: Part II, Chapter 4, §4.2, pp. 225–226, orthogonality relation and scalar product.
Printed: weight \(\frac1{2\pi}|\Gamma(-a-ix)\Gamma(b+ix)|^2\); norm
\(\frac{n!\Gamma(n+b+\bar b)[\Gamma(2a)\Gamma(a+b)]^2}{(2n+2a+b+\bar b-1)\Gamma(n+2a+b+\bar b-1)
\Gamma(n+2a)}\).
Correct: weight \(\frac1{2\pi}|\Gamma(a-ix)\Gamma(b+ix)|^2\) (also in the completeness scalar
product); norm with \(\Gamma(2a)^2|\Gamma(a+b)|^2\).
Evidence: the substitution \(a=-l_2\), \(\lambda_2=x\) turns \(\Gamma(-l_2-i\lambda_2)\) of (72)
into
\(\Gamma(a-ix)\); \(\Gamma(-a-ix)\) has a pole at \(x=0\) for \(a\in\mathbb Z_{>0}\), making the
\(n=0\) norm infinite. A squared norm is positive, so \(\Gamma(a+b)^2\) must be \(|\Gamma(a+b)|^2\).
At \(a=0.8\), \(b=0.6+0.3i\) quadrature agrees with the corrected norm for \(n=0,1,2\) to 15 digits
and gives \(0\) for \((m,n)=(1,2)\); it is the Koekoek–Swarttouw continuous Hahn norm with
parameters \((a,\bar b,a,b)\), \(x\mapsto-x\).
Target: [KV04.4.07].


### Conventions and notation (not errata)

- The kernels of Chapter 4 use non-uniform parabolic normalizations:
  \(K^{31}=\frac1\pi\int(T\psi_n)e^{i\lambda x}dx\), \(K^{33}=\frac1{2\pi}\int(Te_\mu)e^{i\lambda
  x}dx\),
  \(K^{32}_\omega=\frac1{2\pi i}\int(Tx_\omega^{-\mu})e^{i\lambda x}dx\),
  \(K^{21}_\pm=\frac1\pi\int_0^\infty
  x^{\lambda-1}(T\psi_n)(\pm x)dx\). With these, (25)–(40) hold as corrected; the factor \(\frac12\)
  in (41) compensates the \(\frac1\pi\) of \(K^{31}\).
- §2.6, p. 218, writes the hypergeometric Mellin identity with \(\tau\) replaced by \(-\tau\)
  relative to (25) (its \(F(\lambda,\nu;2\tau;\cdot)\) and \(0<\Re\lambda<\Re2\tau\)); with this
  substitution it is consistent with (25) and (27).
- §4.1 writes \(T^-_{l_1}\oplus T^-_{l_2}\) for the tensor product \(T^-_{l_1}\otimes T^-_{l_2}\).
- (37) prints \(K^{32}_+(\lambda,\hat\mu;\dots)\); the hat is typographical. (12) ends with
  \(d\lambda\) where \(dy\) is meant.
- §3.6 lists \(l=0,-\frac12,-1,\dots\) and §1.7 mentions \(T^+_{-l}\); the square-integrable
  negative discrete series of [KV01.2.05] has \(l\le-1\).
- (53) and (54) (Whittaker Barnes integrals) and (55) (\(M\) Barnes integral, with a contour
  separating the poles of \(\Gamma(\kappa+v)\) from those of \(\Gamma(\mu+\frac12-v)\)) are correct.

## Chapter 5. Group Representations and Integral Transforms

Synopsis: [SYNOPSIS-KV05](SYNOPSIS-KV05.md).

### E05.1.01. Macdonald reciprocal pair: \(H\) for \(K\)

Status: Confirmed.
Location: Part II, Chapter 5, §1.2, p. 228, second pair.
Printed: \(F(\mu)=\frac1{\pi i}\int_{a-i\infty}^{a+i\infty}e^{(\lambda-\mu)\pi i/2}
H_{\mu-\lambda}(x)\Phi(\lambda)\,d\lambda\).
Correct: \(F(\mu)=\frac1{\pi i}\int_{a-i\infty}^{a+i\infty}e^{(\lambda-\mu)\pi i/2}
K_{\mu-\lambda}(x)\Phi(\lambda)\,d\lambda\).
Evidence: (9)–(10) of Chapter 4 are Macdonald kernels, no unindexed \(H\) is defined, and the
kernel of multiplication by \(e^{-ix\sinh u}\) is
\(\frac1{2\pi i}\int_{\mathbb R}e^{-ix\sinh u+(\mu-\lambda)u}du
=\frac1{\pi i}e^{(\lambda-\mu)\pi i/2}K_{\mu-\lambda}(x)\) (contour shift \(u\mapsto u-i\pi/2\)).
Target: [KV05.1.03]

### E05.1.02. Elliptic–parabolic Whittaker pair is not reciprocal

Status: Confirmed.
Location: Part II, Chapter 5, §1.3, p. 229, pair with \(W_{-\varrho(n+\epsilon),\tau+1/2}\).
Printed: \(c_n=-\frac{\sin\pi(\tau+n+\epsilon)}{\pi^2}\int_{\mathbb R}\Phi(\lambda)
W_{-\varrho(n+\epsilon),\tau+1/2}(2|\lambda|e^t)|\lambda|^{-1}d\lambda\),
\(\Phi(\lambda)=\frac1\pi\sum_nW_{-\varrho(n+\epsilon),\tau+1/2}(2|\lambda|e^t)c_n\),
\(\mathrm{Re}\,\tau<\tfrac12\).
Correct: the reciprocal pair is \(c_n=\int K^{13}(n,\lambda;\chi,g)\Phi(\lambda)d\lambda\),
\(\Phi=\sum_nK^{31}(\lambda,n;\chi,g^{-1})c_n\) with the full kernels of Chapter 4, Sect. 1.6,
which carry factors depending on \(n\), \(\mathrm{sgn}\,\lambda\) and \(\tau\). An explicit
corrected Whittaker form is not given here.
Evidence: composing the printed formulas gives \(c_n=\sum_mM_{nm}c_m\) with
\(M_{nm}=-\pi^{-3}\sin\pi(\tau+n+\epsilon)\,G_{nm}\),
\(G_{nm}=\int_0^\infty[W_{-n,\mu}W_{-m,\mu}+W_{n,\mu}W_{m,\mu}](x)\,dx/x\), \(\mu=\tau+\tfrac12\),
\(\epsilon=0\). For \(\tau=-\tfrac12+0.4i\): \(M_{00}=0.1013\), \(M_{01}=0.0522\),
\(M_{11}=-0.0692\). In the unitary case \(G_{nn}>0\) while \(\sin\pi(\tau+n)\) alternates in sign,
so no constant can repair the pair; reading \(\varrho\) as a constant sign does not make
\(G\) diagonal either (\(\int_0^\infty W_{0,\mu}W_{-1,\mu}dx/x=0.604\)).
Target: [KV05.1.07]

### E05.1.03. Jacobi (Meixner–Pollaczek) pair: weight and Jacobi parameter

Status: Confirmed.
Location: Part II, Chapter 5, §1.3, p. 230, pair from the kernel (47) of Chapter 4.
Printed: weight \(|\Gamma(i\lambda-l)|^2d\lambda\), polynomials
\(P_n^{(-2l-1,-n-i\lambda)}\bigl(\frac{it+3}{it-1}\bigr)\) and
\(P_n^{(-2l-1,i\lambda-n)}\bigl(\frac{it-3}{it+1}\bigr)\).
Correct: weight \(|\Gamma(i\lambda-l)|^2e^{2\lambda\arctan t}d\lambda\), polynomials
\(P_n^{(-2l-1,\,l-n-i\lambda)}\bigl(\frac{it+3}{it-1}\bigr)\) and
\(P_n^{(-2l-1,\,l-n+i\lambda)}\bigl(\frac{it-3}{it+1}\bigr)\); all constants as printed.
Evidence: for \(f\equiv1\) (only \(c_0\ne0\)), using
\(\int_{\mathbb R}|\Gamma(k+i\lambda)|^2d\lambda=2\pi\Gamma(2k)4^{-k}\), \(k=-l\), the printed
Parseval formula reduces to \((1+t^2)^l=1\); it fails for every \(t\ne0\). With the printed
parameter
\(i\lambda-n\) the polynomials are \(F(-n,-2l+i\lambda;-2l;\cdot)\), not of Meixner–Pollaczek type,
and are not orthogonal for either weight (numerical Gram matrices at \(l=-1\), \(t=0.7\)). The
corrected pair gives the identity Gram matrix to \(10^{-17}\) for \(n,m\le2\) at
\((l,t)=(-1,0.7)\) and \((-\tfrac32,-1.3)\).
Target: [KV05.1.10]

### E05.2.01. Haar normalization in Euler coordinates

Status: Normalization check.
Location: Part II, Chapter 5, §2.1–2.2, p. 231, (7)–(8) and \(dg=(1/4\pi^2)\sinh
t\,d\varphi\,dt\,d\psi\).
Printed: the Plancherel constants \(1/(4\pi^2)\) in (7)–(8) together with
\(dg=(1/4\pi^2)\sinh t\,d\varphi\,dt\,d\psi\), with no angular ranges.
Correct: (7)–(11) are consistent when \(dg\) is normalized so that
\(\int_GF(\cosh t)\,dg=\int_1^\infty F(x)\,dx\), i.e. the angular integration has total mass
\(4\pi^2\).
Evidence: for \(f(g)=F(\cosh t)\), (8) reduces to
\((V/4\pi^2)^2(1/4\pi^2)\int|a|^2\rho\tanh\pi\rho\,d\rho=(V/4\pi^2)\int_1^\infty|F|^2dx\), with
\(V\) the total angular volume; the Mehler–Fock Plancherel formula forces \(V=4\pi^2\).
In the half-angle Euler parametrization of \(SU(1,1)\) (needed for half-integral weights) a
fundamental domain has \(V=8\pi^2\). The constants are therefore tied to an unstated choice of
angular ranges.
Target: [KV05.2.02], [KV05.2.03], [KV05.2.04]

### E05.2.02. Argument of the Jacobi function

Status: Confirmed.
Location: Part II, Chapter 5, §2.4, p. 233, below (16).
Printed:
\(\varphi_\lambda^{(\alpha,\beta)}(t)=R^{(\alpha,\beta)}_{(i\lambda-\alpha-\beta-1)/2}(t)\).
Correct:
\(\varphi_\lambda^{(\alpha,\beta)}(t)=R^{(\alpha,\beta)}_{(i\lambda-\alpha-\beta-1)/2}(\cosh2t)\).
Evidence: \(R_\mu^{(\alpha,\beta)}(x)=F(-\mu,\mu+\alpha+\beta+1;\alpha+1;(1-x)/2)\), and
\((1-\cosh2t)/2=-\sinh^2t\); at \(t=0\) the printed form gives \(R(0)\ne1=\varphi_\lambda(0)\) in
general.
Target: [KV05.2.07]

### E05.2.03. Missing factor \(\tfrac12\) in the \(J_{i\rho}-J_{-i\rho}\) transform

Status: Confirmed.
Location: Part II, Chapter 5, §2.5, p. 234, (18) and its Plancherel formula.
Printed: \(F(x)=\int_0^\infty c(\rho)[J_{-i\rho}(x)-J_{i\rho}(x)]\frac{\rho\,d\rho}{\sinh\pi\rho}
+\sum_{l\ge0}(4l+2)c_lJ_{2l+1}(x)\) and
\(\int_0^\infty|f|^2\frac{dx}x=\int_0^\infty|c(\rho)|^2\frac{\rho\,d\rho}{\sinh\pi\rho}
+\sum_{l\ge0}(4l+2)|c_l|^2\).
Correct: both continuous terms carry the factor \(\tfrac12\).
Evidence: for \(f=J_\nu\), \(\int_0^\infty J_\nu^2dx/x=1/(2\nu)\) and
\(c(\rho)=-4i\cos(\pi\nu/2)\sinh(\pi\rho/2)/(\pi(\nu^2+\rho^2))\). For \(\nu=2\) the printed right
side is \(0.29736\), the corrected one \(0.25\); for \(\nu=1.5\): \(0.37377\) against \(0.33333\).
The corrected identity also holds for \(\nu=1,2.5,3\).
Target: [KV05.2.12]

### E05.2.04. Missing discrete terms in the \(J_{i\rho}+J_{-i\rho}\) transform

Status: Confirmed.
Location: Part II, Chapter 5, §2.5, pp. 234–235, (19) and the sentence after it.
Printed: \(F(x)=\frac12\int_0^\infty
c(\rho)[J_{i\rho}(x)+J_{-i\rho}(x)]\frac{\rho\,d\rho}{\sinh\pi\rho}\),
\(\int|F|^2\frac{dx}x=\frac12\int|c|^2\frac{\rho\,d\rho}{\sinh\pi\rho}\); "Discrete summands
disappear in
(19)".
Correct: add \(\sum_{l\ge1}4l\,c_lJ_{2l}(x)\) to the expansion and \(\sum_{l\ge1}4l|c_l|^2\) to the
Plancherel formula, with \(c_l=\int_0^\infty F(x)J_{2l}(x)dx/x\).
Evidence: \(c(\rho)=4\sin(\pi\nu/2)\cosh(\pi\rho/2)/(\pi(\nu^2+\rho^2))\) for \(F=J_\nu\); for
\(\nu=2\)
it vanishes identically although \(F\ne0\). The corrected Plancherel sum equals \(1/(2\nu)\) for
\(\nu=1,1.5,2,2.5,3\); the printed one gives \(0.297,0.056,0,0.018,0.024\).
Target: [KV05.2.13]

### E05.2.05. Final Whittaker–Laguerre transform

Status: Confirmed.
Location: Part II, Chapter 5, §2.5, p. 235, last display.
Printed: continuous measure
\(\frac1{2\pi^2}\frac{\rho\tanh\pi(\rho+i\epsilon)\,d\rho}{|\Gamma(i\rho+n+\epsilon+1/2)|^2}\);
discrete terms
\(\sum_{l=\epsilon}^\infty(2l+1)c_lx^{l+1}e^{-x^2/2}L_n^{2l+1}(x)\),
\(c_l=\frac{2n!}{\pi(2l+n+1)!}\int_0^\infty f(x)x^{l-1}e^{-x^2/2}L_n^{2l+1}(x)\,dx\).
Correct: with \(\kappa=-(n+\epsilon)\), the continuous measure is
\(\pi^{-2}\rho\sinh(2\pi\rho)|\Gamma(\tfrac12-\kappa+i\rho)|^2d\rho\), and the discrete part is the
finite sum over \(0\le j<\kappa-\tfrac12\) of the projections on
\(e^{-x/2}x^{\kappa-j}L_j^{(2\kappa-2j-1)}(x)\) in \(L^2(x^{-2}dx)\), with squared norms
\(\Gamma(2\kappa-j)/(j!(2\kappa-2j-1))\) ([KV05.2.14]).
Evidence: for \(n=\epsilon=0\) the printed measure is \(4\pi^2\) times too small, and its gamma
factor
is inverted. The printed discrete functions have the Gaussian \(e^{-x^2/2}\), while
square-integrable solutions of the Whittaker equation in \(x\) decay like \(e^{-x/2}\); they exist
only for \(\kappa>\tfrac12\) and are finitely many. The corrected formula satisfies Plancherel
for \(f=x^{\nu+1}e^{-x/2}\) at \(\kappa=-1,0,0.3,1,1.2,2,2.5,3\) (e.g. \(\kappa=2\), \(\nu=1.5\):
continuous \(0.25678\) + discrete \(5.74322\) = \(\|f\|^2=6\)), and at \(\kappa=0\) it is the
Kontorovich–Lebedev transform.
Target: [KV05.2.14]


### Conventions and notation (not errata)

- §2.2, p. 232, (9) and (11): \(\sum_{l=-1-\epsilon}^{N}\) with \(N=-\min(|m|,|n|)\le-1-\epsilon\)
  is a
  descending sum over \(l=-1-\epsilon,-2-\epsilon,\dots,N\); it is empty when \(N>-1-\epsilon\), and
  there are no discrete terms when \(mn\le0\) ([KV05.2.05]).
- §2.4, p. 233, (16): both sides carry the factor \(1/\sqrt{2\pi}\), which cancels.

## Chapter 6. Group Representations and Polynomials of a Discrete Variable

Synopsis: [SYNOPSIS-KV06](SYNOPSIS-KV06.md).

### E06.1.01. Parameter range of Krawtchouk orthogonality

Status: Confirmed.
Location: Part II, Chapter 6, §1.2, p. 236, after the orthogonality relation.
Printed: "for \(0\le p\le1\) the Krawtchouk polynomials \(K_s(x;p,N)\), \(s=0,1,\dots,N\), form an
orthogonal system".
Correct: \(0<p<1\).
Evidence: \(K_s(x;p,N)=F(-x,-s;-N;p^{-1})\) is undefined at \(p=0\); at \(p=1\) the weight
\(\binom Nxp^x(1-p)^{N-x}\) is supported at \(x=N\) only and cannot carry \(N+1\) orthogonal
nonzero functions for \(N>0\) (the right side \(((1-p)/p)^s\binom Ns^{-1}\) vanishes for \(s>0\)).
Target: [KV06.1.04]

### E06.1.02. Sign of the discrete-series matrix elements

Status: Confirmed.
Location: Part II, Chapter 6, §1.3, p. 238, first two displays.
Printed: \(\mathcal P^l_{mn}(\cosh t)=[\cdots]^{1/2}\sinh^{x+s}\frac t2\cosh^{-\gamma-x-s}\frac t2
F(-x,-s;\gamma;-\sinh^{-2}\frac t2)\) and the same with \(M_s(x;\gamma,\tanh^2\frac t2)\).
Correct: both right sides carry the factor \((-1)^s\), \(s=l-m\).
Evidence: for \(s=x=1\) the printed expression tends to \(-1\) as \(t\to0\) (exact limit
computed), while \(T_l^-(e)=E\) has diagonal entries \(1\). An independent disc-model computation of
the matrix elements agrees with the corrected formula for
\((\gamma,s,x)=(3,1,2),(3,2,1),(4,2,2),(3,0,2),(5,3,1)\).
Target: [KV06.1.09], [KV06.1.10]

### E06.1.03. Meixner recurrence coefficient

Status: Confirmed.
Location: Part II, Chapter 6, §1.3, p. 238, last display.
Printed: \(cM_{s+1}-[(c-1)x+(1+c)s+s\gamma]M_s+s(s+\gamma-1)M_{s-1}=0\).
Correct: \(cM_{s+1}-[(c-1)x+(1+c)s+c\gamma]M_s+s(s+\gamma-1)M_{s-1}=0\).
Evidence: at \(s=0\), \(M_0=1\), \(M_1=\gamma+x(1-1/c)\): the printed left side is \(c\gamma\ne0\)
at
\(x=0\). The corrected recurrence holds identically for \(s\le3\)
(\(\gamma=\tfrac52\), \(c=\tfrac13\)); the printed one leaves \(\tfrac{10}3x-\tfrac{25}6\) at
\(s=1\).
Target: [KV06.1.13]

### E06.1.04. Meixner generating function exponent

Status: Confirmed.
Location: Part II, Chapter 6, §1.3, p. 239.
Printed: \(\bigl(1-\frac zc\bigr)^x(1-z)^{-\gamma-x}=\sum_{s=0}^\infty
M_s(x;\gamma,c)\frac{z^c}{s!}\).
Correct: \(\sum_{s=0}^\infty M_s(x;\gamma,c)\frac{z^s}{s!}\).
Evidence: the printed right side is \(z^c\) times a constant series; Taylor coefficients of the
left side equal \(M_s(x;\gamma,c)/s!\) (checked for \(s\le4\), \(x=2\)).
Target: [KV06.1.14]

### E06.1.05. Index in the oscillator matrix element

Status: Confirmed.
Location: Part II, Chapter 6, §1.4, p. 239, (5).
Printed: \(t^{\varrho
m}_{kn}(s_r)=(-1)^k(k!n!)^{-1/2}(r^2\varrho)^{(m+k)/2}e^{-r^2\varrho/2}c_k(n;r^2\varrho)\).
Correct: exponent \((n+k)/2\).
Evidence: unitarity requires \(\sum_n|t_{kn}|^2=1\); with \((n+k)/2\) this is
\(\frac{a^ke^{-a}}{k!}\sum_n\frac{a^n}{n!}c_k(n;a)^2=1\), i.e. (6) (\(a=r^2\varrho\)), while with
\((m+k)/2\) the sum is \(\frac{a^{m+k}e^{-a}}{k!}\sum_n\frac{c_k(n;a)^2}{n!}\), which equals \(a^m\)
for \(k=0\). The representation label \(m\) does not enter the
displacement matrix element.
Target: [KV06.1.16]

### E06.1.06. Missing complex conjugation for Krawtchouk–Meixner functions

Status: Confirmed.
Location: Part II, Chapter 6, §1.5, pp. 240–241, orthogonality relation and formula for \(a_n\).
Printed: \(\sum_{x\in\mathbb Z}M_\varrho(x,p)\mathcal K_n(x;p,i\varrho-\tfrac12)\mathcal
K_k(x;p,i\varrho-\tfrac12)
=p(\frac{1+p}p)^n\delta_{nk}\) and \(a_n=\sum M_\varrho p^{n-1}(1+p)^{-n}f(x)\mathcal
K_n(x;\dots)\).
Correct: \(\mathcal K_k\) in the orthogonality relation and \(\mathcal K_n\) in \(a_n\) are complex
conjugated.
Evidence: \(\mathcal K_n(x;p,i\varrho-\tfrac12)\) is not real (e.g. \(\mathcal
K_1(0;0.6,-\tfrac12+0.7i)
=0.400+1.558i\)). With \(\varrho=0.7\), \(p=0.6\), summing over \(|x|\le25\): with conjugation the
sums
for \((n,k)=(0,0),(0,1),(1,1)\) are \(0.6,\ 0,\ 1.6\) as required; without, \(-0.065+0.249i\),
\(0.038+0.503i\), \(0.545-0.417i\). The conjugated relation is the column orthonormality of the
unitary matrix of \(T_{(i\varrho-1/2,0)}(h(t))\).
Target: [KV06.1.19]

### E06.1.07. Summation index in the Krawtchouk–Meixner coefficient

Status: Confirmed.
Location: Part II, Chapter 6, §1.5, p. 241, formula for \(a_n\).
Printed: \(a_n=\sum_{n\in\mathbb Z}M_\varrho(x,p)p^{n-1}(1+p)^{-n}f(x)\mathcal
K_n(x;p,i\varrho-\tfrac12)\).
Correct: the sum is over \(x\in\mathbb Z\) (with \(\overline{\mathcal K_n}\), [E06.1.06]).
Evidence: \(n\) is the fixed index of the coefficient; the summand depends on \(x\).
Target: [KV06.1.19]

### E06.1.08. Empty complementary-series interval

Status: Confirmed.
Location: Part II, Chapter 6, §1.5, p. 241.
Printed: "\(\mathcal K_n(x;p,\tau)\), \(1<\tau<1\), connected with representations of the
complementary series".
Correct: the interval is empty. The intended range is presumably \(-1<\tau<0\),
\(\tau\ne-\tfrac12\) (complementary series \(\chi=(\tau,0)\)); this, and the weight and norm of the
asserted orthogonality relation, are not supplied by the source and are not verified here.
Evidence: no real \(\tau\) satisfies \(1<\tau<1\).
Target: [KV06.1.20]

### E06.2.01. Type of the hypergeometric series for CGCs

Status: Confirmed.
Location: Part II, Chapter 6, §2.1, p. 242, before (13).
Printed: "the terminating hypergeometric series
\({}_2F_2(\alpha,\beta,\gamma;\delta,\varepsilon;1)\)".
Correct: \({}_3F_2(\alpha,\beta,\gamma;\delta,\varepsilon;1)\).
Evidence: the series has three upper and two lower parameters, as in (13) itself.
Target: [KV06.2.04]

### E06.2.02. Explicit formula (13) for CGCs

Status: Confirmed.
Location: Part II, Chapter 6, §2.1, p. 242, (13).
Printed: prefactor \((-1)^{l_1-j}(2l_1)!/(l_2-l+m)!\) and
\({}_3F_2(-l_1+l_2-l,-l_1+l_2+l+1,-l_1+j;-l_1+l_2+j+1,-2l_1;1)\).
Correct: prefactor \((-1)^{l_1-j}(2l_1)!/(l_2-l_1+m)!\) and lower parameter \(-l_1+l_2+m+1\);
valid for \(l_2-l_1+m\ge0\).
Evidence: for \(l_1=l_2=\tfrac12\), \(l=0\), \(j=-k=\tfrac12\) the printed prefactor contains
\((\tfrac12)!\); over all admissible labels with \(l_1,l_2\le2\) the printed formula disagrees with
the Condon–Shortley values in 160 of 221 defined cases. The corrected formula agrees in all 1470
cases with \(l_1,l_2\le3\), \(l_2-l_1+m\ge0\). It is also what the Hahn identification of p. 243
requires: there \(\alpha+1=l_2-l_1+m+1\) and \(\alpha!=(l_2-l_1+m)!\).
Target: [KV06.2.04]

### E06.2.03. Second Hahn reflection formula

Status: Confirmed.
Location: Part II, Chapter 6, §2.2, p. 244, first display.
Printed: \(Q_n(x;\alpha,\beta,N)=\frac{(-1)^n\alpha^{(-n)}}{\beta^{(n)}}Q_n(N-x;\beta,\alpha,N)\).
Correct: \(\frac{(-1)^n\alpha^{(-n)}}{\beta^{(-n)}}=(-1)^n\frac{(\beta+1)_n}{(\alpha+1)_n}\).
Evidence: at \(x=0\) the left side is \(1\) and
\(Q_n(N;\beta,\alpha,N)=(-1)^n(\alpha+1)_n/(\beta+1)_n\).
Exact check at \(\alpha=\tfrac12\), \(\beta=\tfrac34\), \(N=4\), all \(n,x\): the corrected form
holds, the printed one fails. The first reflection formula of the same display is correct.
Target: [KV06.2.10]

### E06.2.04. Hahn difference equation coefficient

Status: Confirmed.
Location: Part II, Chapter 6, §2.2, p. 244.
Printed:
\(\{x(N+\beta-n+1)\Delta\nabla+[(\alpha+1)N-(\alpha+\beta+2)x]\Delta+n(\alpha+\beta+n+1)\}Q_n=0\).
Correct: \(x(N+\beta-x+1)\Delta\nabla\) in place of \(x(N+\beta-n+1)\Delta\nabla\).
Evidence: exact polynomial check for \(n\le4\) (\(\alpha=\tfrac12,\beta=\tfrac34,N=4\)): the
corrected equation holds identically, the printed one does not.
Target: [KV06.2.11]

### E06.2.05. Hahn integral representation: \(\alpha\) and \(\beta\) interchanged

Status: Confirmed.
Location: Part II, Chapter 6, §2.2, p. 244.
Printed: \(Q_n(x;\alpha,\beta,N)=\frac{(-1)^nn!(N+n+\alpha+\beta+1)!\beta^{(-n)}}
{2^{N+\alpha+\beta+1}N^{(n)}(N+\alpha-x)!(\beta+x)!}\int_{-1}^1(1-t)^{N+\alpha-x}(1+t)^{\beta+x}
P_n^{(\alpha,\beta)}(t)\,dt\).
Correct: the left side is \(Q_n(x;\beta,\alpha,N)\).
Evidence: exact integration for \((\alpha,\beta,N)=(1,2,3)\) and \((0,2,2)\), \(n\le2\), all \(x\):
the ratio of the printed right side to \(Q_n(x;\beta,\alpha,N)\) is \(1\) in every case, while
its ratio to \(Q_n(x;\alpha,\beta,N)\) takes values such as \(\tfrac83,\tfrac16,-\tfrac13\).
Target: [KV06.2.12]

### E06.2.06. Hahn-to-Meixner limit normalization

Status: Confirmed.
Location: Part II, Chapter 6, §2.2, p. 244, last limit formula.
Printed: \(\lim_{N\to\infty}Q_n(x;\beta-1,\frac{1-c}cN,N)=M_n(x;\beta,c)\).
Correct: the limit is \(\widetilde M_n(x;\beta,c)=M_n(x;\beta,c)/(\beta)_n\).
Evidence: at \(x=0\) every Hahn polynomial equals \(1\), whereas \(M_n(0;\beta,c)=(\beta)_n\) for
the scaled Meixner polynomials of p. 238. Symbolic limits for \(n,x\le2\) give \(\widetilde M_n\).
Target: [KV06.2.13]

### E06.2.07. Product formula (18) for Krawtchouk polynomials

Status: Confirmed.
Location: Part II, Chapter 6, §2.4, p. 245, (18).
Printed: the formula reproduced in [KV06.2.15].
Correct: not reconstructed here. The valid statement is the coupling identity (12) at
\(g=g(\theta)\), \(\sin^2(\theta/2)=p\), with the Krawtchouk form of \(t^l_{mn}\) and the corrected
CGC formula (13) ([KV06.2.15]).
Evidence: exact evaluation with \(p=\tfrac13\) in the range where all printed factorials are
defined (\(s+s'\ge N\), \(x+x'\ge N\), \(N\le N'\)): for \((N,N')=(1,2)\) it fails in 17 of 25
cases (e.g. \(s=0,s'=1,x=0,x'=2\): left side \(-2\), printed right side \(-\tfrac76\)); for
\((N,N')=(2,3),(2,2),(1,3)\) it fails in every tested case. The identity (12) itself holds exactly
([KV06.2.03]).
Target: [KV06.2.15]

### E06.2.08. Addition theorem (19) for Krawtchouk polynomials

Status: Confirmed.
Location: Part II, Chapter 6, §2.4, p. 245, (19).
Printed: the formula reproduced in [KV06.2.16].
Correct: not reconstructed here; it is to be derived from the correct form of [KV06.2.15] by CGC
orthogonality.
Evidence: exact evaluation with \(p=\tfrac13\), \(N\le\sigma,\tau\le N+N'\): for \((N,N')=(1,2)\)
it fails in 11 of 27 cases (e.g. \(n=m=1\), \(\sigma=1\), \(\tau=2\): left side is half the right
side), for \((2,3)\) in 56 of 128 and for \((2,2)\) in 31 of 81 cases.
Target: [KV06.2.16]

### E06.2.09. Meixner connection formula normalization

Status: Confirmed.
Location: Part II, Chapter 6, §2.4, p. 246, last display.
Printed: \(M_n(x;\gamma,c)=\sum_{m=0}^n\frac{n!(\beta)_m}{m!(n-m)!(\gamma)_m}u^m
F(m-n,m+\beta;m+\gamma;u)M_m(x;\beta,c')\), \(u=\frac{c'(1-c)}{c(1-c')}\), with \(M\) the scaled
polynomials of p. 238.
Correct: the formula holds for the unscaled \(\widetilde M_n=M_n/(\gamma)_n\),
\(\widetilde M_m=M_m/(\beta)_m\); for scaled polynomials the coefficient is
\(\binom nm(\gamma)_n/(\gamma)_m\).
Evidence: at \(n=1\), \(x=0\) the printed scaled form gives \(M_1(0;\gamma,c)\ne\gamma\). Exact
checks
(\(\gamma=\tfrac52,c=\tfrac13,\beta=\tfrac32,c'=\tfrac12\), \(n\le3\)): the unscaled reading holds,
the scaled reading fails. The product formula on the same page is correct for scaled \(M_n\).
Target: [KV06.2.20]

### E06.3.01. Sign in the Charlier addition theorem

Status: Confirmed.
Location: Part II, Chapter 6, §3.2, p. 248, final display.
Printed: prefactor \((-\varrho_2)^{n+k}\frac{(k+n)!(x+y-n)!}{(x+y)!(\varrho_1+\varrho_2)^k}\).
Correct: \((-1)^n\varrho_2^{n+k}\frac{(k+n)!(x+y-n)!}{(x+y)!(\varrho_1+\varrho_2)^k}\).
Evidence: for \(\varrho_1=2\), \(\varrho_2=3\), \(n=k=1\), \(x=2\), \(y=1\) the printed left side is
\(\tfrac25\) and the right side \(-\tfrac25\). The corrected sign holds for all
\(n,k,x,y\le2\); it is the inversion of (25) by Krawtchouk orthogonality.
Target: [KV06.3.07]


### Conventions and notation (not errata)

- §1.1, p. 236: in \(\alpha_m=\sum_{n\in I}f(x)\overline{F(x;m,g)}\) the summation variable is
  \(x\).
- §1.3, p. 238: "\(M_s(x;c,\gamma)\)" in the sentence after the orthogonality relation lists the
  parameters in reverse order; the definition uses \(M_s(x;\gamma,c)\).
- §2.2, p. 243: \(a^{(r)}=\Gamma(a+1)/\Gamma(a-r+1)\) (printed as "\((a)^r\)").
- §2.5, p. 247: \(\overline\in\) means "is not an element of"; the condition
  \(-\alpha-1,-\beta-\delta-1,-\gamma-1\notin\{0,\dots,n\}\) makes the \({}_4F_3\) well defined.
  It is not a finite-support condition; orthogonality on \(\{0,\dots,N\}\) needs one lower
  parameter equal to \(-N\) ([KV06.2.23]).


[E01.2.06]: #e01206-fock-inner-product-for-the-oscillator-representations
[E02.2.01]: #e02201-basis-in-which-1516-and-the-s_3-formulas-hold
[E02.2.05]: #e02205-canonical-basis-phase-in-1920
[E04.1.06]: #e04106-elliptic-matrix-element-of-the-boost-argument
[E04.1.11]: #e04111-elliptic-to-parabolic-kernel-36-constant-and-gamma-factor
[E04.1.13]: #e04113-discrete-series-matrix-element-45
[E04.1.14]: #e04114-jacobi-form-47-of-the-discrete-series-kernel-k21
[E04.4.02]: #e04402-continuous-hahn-weight-and-norm
[E06.1.06]: #e06106-missing-complex-conjugation-for-krawtchoukmeixner-functions
[KV01.1.02]: SYNOPSIS-KV01.md#kv01102-restricted-roots-and-rho
[KV01.1.04]: SYNOPSIS-KV01.md#kv01104-parabolic-subgroups
[KV01.1.05]: SYNOPSIS-KV01.md#kv01105-cartan-decomposition
[KV01.1.08]: SYNOPSIS-KV01.md#kv01108-haar-measure-in-cartan-coordinates
[KV01.1.10]: SYNOPSIS-KV01.md#kv01110-decompositions-of-sl2mathbb-r
[KV01.1.12]: SYNOPSIS-KV01.md#kv01112-subgroups-of-so_0n1-and-son1
[KV01.1.13]: SYNOPSIS-KV01.md#kv01113-hyperboloid-cone-and-the-iwasawa-parameter
[KV01.1.14]: SYNOPSIS-KV01.md#kv01114-un1-and-un1
[KV01.1.17]: SYNOPSIS-KV01.md#kv01117-the-triangular-groups-s-s_1-s_2-s_3-and-h
[KV01.1.18]: SYNOPSIS-KV01.md#kv01118-the-oscillator-group-s_4
[KV01.2.01]: SYNOPSIS-KV01.md#kv01201-nonunitary-spherical-series
[KV01.2.05]: SYNOPSIS-KV01.md#kv01205-discrete-series-of-sl2mathbb-r
[KV01.2.10]: SYNOPSIS-KV01.md#kv01210-representations-of-son1-on-the-boundary-sphere
[KV01.2.13]: SYNOPSIS-KV01.md#kv01213-the-affine-group-of-the-line
[KV01.2.17]: SYNOPSIS-KV01.md#kv01217-the-circle-operators-of-s_3
[KV01.2.18]: SYNOPSIS-KV01.md#kv01218-fock-space-representations-of-s_4
[KV02.1.05]: SYNOPSIS-KV02.md#kv02105-functions-belonging-to-representations-of-a-subgroup
[KV02.1.06]: SYNOPSIS-KV02.md#kv02106-expansion-of-operator-functions-theorem-3
[KV02.1.07]: SYNOPSIS-KV02.md#kv02107-expansion-of-vector-functions-theorem-4
[KV02.2.01]: SYNOPSIS-KV02.md#kv02201-the-case-su11-integral-representation
[KV02.2.02]: SYNOPSIS-KV02.md#kv02202-the-case-su11-hypergeometric-expressions
[KV02.2.03]: SYNOPSIS-KV02.md#kv02203-the-case-su11-jacobi-functions-and-euler-angles
[KV02.2.05]: SYNOPSIS-KV02.md#kv02205-the-case-su11-discrete-series
[KV02.2.06]: SYNOPSIS-KV02.md#kv02206-the-case-su2-jacobi-polynomials
[KV02.2.07]: SYNOPSIS-KV02.md#kv02207-the-case-su2-legendre-polynomials-and-associated-functions
[KV02.2.10]: SYNOPSIS-KV02.md#kv02210-the-case-so_0n1-zonal-spherical-functions
[KV02.2.12]: SYNOPSIS-KV02.md#kv02212-the-case-so_0n1-associated-spherical-functions
[KV02.2.14]: SYNOPSIS-KV02.md#kv02214-the-case-ison-bessel-functions
[KV02.2.16]: SYNOPSIS-KV02.md#kv02216-the-group-s_4-laguerre-functions
[KV02.2.17]: SYNOPSIS-KV02.md#kv02217-the-group-s_3-hermite-polynomials
[KV02.2.18]: SYNOPSIS-KV02.md#kv02218-the-case-un-jacobi-polynomials
[KV03.1.03]: SYNOPSIS-KV03.md#kv03103-rank-one-geometry
[KV03.1.07]: SYNOPSIS-KV03.md#kv03107-addition-theorem-for-pl_mn
[KV03.1.10]: SYNOPSIS-KV03.md#kv03110-addition-theorem-for-associated-legendre-functions
[KV03.1.13]: SYNOPSIS-KV03.md#kv03113-gegenbauer-addition-theorem-for-bessel-functions
[KV03.1.16]: SYNOPSIS-KV03.md#kv03116-derivative-of-jacobi-polynomials
[KV03.1.18]: SYNOPSIS-KV03.md#kv03118-addition-theorem-for-jacobi-functions
[KV03.1.20]: SYNOPSIS-KV03.md#kv03120-factorization-identities-in-the-triangular-group
[KV03.1.21]: SYNOPSIS-KV03.md#kv03121-first-addition-theorem-for-laguerre-polynomials
[KV03.1.22]: SYNOPSIS-KV03.md#kv03122-second-addition-theorem-for-laguerre-polynomials
[KV03.1.27]: SYNOPSIS-KV03.md#kv03127-addition-theorem-at-varphi_2pi2
[KV03.1.33]: SYNOPSIS-KV03.md#kv03133-orthogonality-of-pl_mn
[KV03.2.01]: SYNOPSIS-KV03.md#kv03201-general-product-formula
[KV03.2.02]: SYNOPSIS-KV03.md#kv03202-product-formula-for-associated-spherical-functions
[KV03.2.07]: SYNOPSIS-KV03.md#kv03207-product-formula-for-associated-legendre-functions
[KV03.2.12]: SYNOPSIS-KV03.md#kv03212-product-formulas-for-laguerre-polynomials
[KV03.3.03]: SYNOPSIS-KV03.md#kv03303-generating-function-for-mathfrak-ptau_mn
[KV03.3.04]: SYNOPSIS-KV03.md#kv03304-contour-integral-for-mathfrak-ptau_mn
[KV03.3.05]: SYNOPSIS-KV03.md#kv03305-multiplication-formulas
[KV03.3.06]: SYNOPSIS-KV03.md#kv03306-mellin-integral-for-mathfrak-ptau_mn
[KV03.3.07]: SYNOPSIS-KV03.md#kv03307-mellin-integral-for-legendre-functions
[KV03.3.08]: SYNOPSIS-KV03.md#kv03308-inverse-mellin-formulas
[KV03.3.09]: SYNOPSIS-KV03.md#kv03309-generating-function-for-discrete-series-functions
[KV03.3.12]: SYNOPSIS-KV03.md#kv03312-cauchy-integral-for-pl_mn
[KV03.3.13]: SYNOPSIS-KV03.md#kv03313-generating-functions-in-the-degree-l
[KV03.3.14]: SYNOPSIS-KV03.md#kv03314-gegenbauer-expansion-of-cosh-t-cosvarphisinh-tsigma
[KV03.4.03]: SYNOPSIS-KV03.md#kv03403-eigenvalue-equations-for-matrix-elements
[KV03.4.08]: SYNOPSIS-KV03.md#kv03408-differential-equations-from-su11
[KV04.1.02]: SYNOPSIS-KV04.md#kv04102-affine-group-of-the-line-gamma-kernel
[KV04.1.04]: SYNOPSIS-KV04.md#kv04104-iso11-null-translations
[KV04.1.07]: SYNOPSIS-KV04.md#kv04107-s_1-gamma-kernels-of-one-parameter-subgroups
[KV04.1.08]: SYNOPSIS-KV04.md#kv04108-s_1-whittaker-kernels
[KV04.1.09]: SYNOPSIS-KV04.md#kv04109-s_2-parabolic-cylinder-kernels
[KV04.1.11]: SYNOPSIS-KV04.md#kv04111-sl2mathbb-r-elliptic-matrix-elements
[KV04.1.12]: SYNOPSIS-KV04.md#kv04112-sl2mathbb-r-hyperbolic-kernels-of-boosts
[KV04.1.14]: SYNOPSIS-KV04.md#kv04114-sl2mathbb-r-parabolic-kernels
[KV04.1.15]: SYNOPSIS-KV04.md#kv04115-sl2mathbb-r-elliptic-to-hyperbolic-kernels-of-g_-t
[KV04.1.16]: SYNOPSIS-KV04.md#kv04116-sl2mathbb-r-elliptic-to-parabolic-kernels-of-g_2t
[KV04.1.19]: SYNOPSIS-KV04.md#kv04119-discrete-series-three-bases-of-l20infty
[KV04.1.21]: SYNOPSIS-KV04.md#kv04121-discrete-series-elliptic-matrix-elements-of-g_2t
[KV04.1.22]: SYNOPSIS-KV04.md#kv04122-discrete-series-elliptic-to-parabolic-kernel-of-g_2t
[KV04.1.23]: SYNOPSIS-KV04.md#kv04123-discrete-series-elliptic-to-hyperbolic-kernel-of-g_-t
[KV04.1.27]: SYNOPSIS-KV04.md#kv04127-discrete-series-kernel-as-a-meixnerpollaczek-polynomial
[KV04.1.28]: SYNOPSIS-KV04.md#kv04128-orthogonality-and-completeness-of-meixnerpollaczek-polynomials
[KV04.2.03]: SYNOPSIS-KV04.md#kv04203-barnes-integrals-for-hankel-functions
[KV04.2.07]: SYNOPSIS-KV04.md#kv04207-barnes-integral-for-the-parabolic-cylinder-function
[KV04.2.08]: SYNOPSIS-KV04.md#kv04208-mellin-transform-of-the-macdonald-function
[KV04.2.09]: SYNOPSIS-KV04.md#kv04209-mellin-transforms-of-hankel-and-macdonald-functions-with-three-regimes
[KV04.2.11]: SYNOPSIS-KV04.md#kv04211-whittaker-mellin-convolutions-from-sl2mathbb-r
[KV04.2.13]: SYNOPSIS-KV04.md#kv04213-taylor-type-translation-series-for-d_nu
[KV04.2.14]: SYNOPSIS-KV04.md#kv04214-mellin-transform-of-hypergeometric-functions
[KV04.3.06]: SYNOPSIS-KV04.md#kv04306-continual-addition-theorem-for-whittaker-functions
[KV04.3.07]: SYNOPSIS-KV04.md#kv04307-continual-addition-theorem-for-whittaker-functions-crossing-product
[KV04.3.08]: SYNOPSIS-KV04.md#kv04308-continual-addition-theorem-for-parabolic-cylinder-functions
[KV04.3.09]: SYNOPSIS-KV04.md#kv04309-residue-series-for-parabolic-cylinder-functions
[KV04.3.12]: SYNOPSIS-KV04.md#kv04312-mixed-addition-theorem-whittaker-product-integral
[KV04.3.13]: SYNOPSIS-KV04.md#kv04313-mixed-addition-theorem-whittakermacdonald-integral-and-mathfrak-q
[KV04.3.14]: SYNOPSIS-KV04.md#kv04314-mixed-addition-theorem-whittaker-series
[KV04.3.15]: SYNOPSIS-KV04.md#kv04315-mixed-addition-theorem-laguerre-series
[KV04.3.16]: SYNOPSIS-KV04.md#kv04316-mixed-addition-theorem-whittakerjacobi-integral
[KV04.3.17]: SYNOPSIS-KV04.md#kv04317-mixed-addition-theorem-bessellaguerre-integral
[KV04.3.18]: SYNOPSIS-KV04.md#kv04318-mixed-addition-theorem-besselwhittaker-integral
[KV04.4.03]: SYNOPSIS-KV04.md#kv04403-hyperbolic-clebschgordan-coefficients
[KV04.4.07]: SYNOPSIS-KV04.md#kv04407-orthogonality-and-completeness-of-continuous-hahn-polynomials
[KV05.1.03]: SYNOPSIS-KV05.md#kv05103-macdonald-reciprocal-pair
[KV05.1.07]: SYNOPSIS-KV05.md#kv05107-ellipticparabolic-reciprocal-pair
[KV05.1.10]: SYNOPSIS-KV05.md#kv05110-meixnerpollaczek-jacobi-expansion
[KV05.2.02]: SYNOPSIS-KV05.md#kv05202-fourier-inversion-on-sl2mathbb-r
[KV05.2.03]: SYNOPSIS-KV05.md#kv05203-plancherel-formula-on-sl2mathbb-r
[KV05.2.04]: SYNOPSIS-KV05.md#kv05204-euler-coordinates-on-su11-and-haar-normalization
[KV05.2.05]: SYNOPSIS-KV05.md#kv05205-expansion-of-functions-of-cosh-t-in-mn-matrix-elements
[KV05.2.07]: SYNOPSIS-KV05.md#kv05207-jacobi-functions
[KV05.2.12]: SYNOPSIS-KV05.md#kv05212-index-transform-with-j_irho-j_-irho
[KV05.2.13]: SYNOPSIS-KV05.md#kv05213-index-transform-with-j_irhoj_-irho
[KV05.2.14]: SYNOPSIS-KV05.md#kv05214-whittaker-index-transform
[KV06.1.04]: SYNOPSIS-KV06.md#kv06104-krawtchouk-orthogonality
[KV06.1.09]: SYNOPSIS-KV06.md#kv06109-discrete-series-matrix-elements-of-su11
[KV06.1.10]: SYNOPSIS-KV06.md#kv06110-meixner-polynomials
[KV06.1.13]: SYNOPSIS-KV06.md#kv06113-meixner-difference-equation-recurrence-and-difference-derivative
[KV06.1.14]: SYNOPSIS-KV06.md#kv06114-meixner-generating-function
[KV06.1.16]: SYNOPSIS-KV06.md#kv06116-oscillator-matrix-elements-and-charlier-orthogonality
[KV06.1.19]: SYNOPSIS-KV06.md#kv06119-orthogonality-of-krawtchoukmeixner-functions
[KV06.1.20]: SYNOPSIS-KV06.md#kv06120-complementary-series
[KV06.2.03]: SYNOPSIS-KV06.md#kv06203-product-of-matrix-elements
[KV06.2.04]: SYNOPSIS-KV06.md#kv06204-hypergeometric-formula-for-cgcs
[KV06.2.10]: SYNOPSIS-KV06.md#kv06210-hahn-symmetries
[KV06.2.11]: SYNOPSIS-KV06.md#kv06211-hahn-difference-equation-and-recurrences
[KV06.2.12]: SYNOPSIS-KV06.md#kv06212-integral-representation-of-hahn-polynomials
[KV06.2.13]: SYNOPSIS-KV06.md#kv06213-limits-of-hahn-polynomials
[KV06.2.15]: SYNOPSIS-KV06.md#kv06215-product-formula-for-krawtchouk-polynomials
[KV06.2.16]: SYNOPSIS-KV06.md#kv06216-addition-theorem-for-krawtchouk-polynomials
[KV06.2.20]: SYNOPSIS-KV06.md#kv06220-connection-formula-for-meixner-polynomials
[KV06.2.23]: SYNOPSIS-KV06.md#kv06223-racah-orthogonality-difference-equation-and-difference-derivative
[KV06.3.07]: SYNOPSIS-KV06.md#kv06307-addition-theorem-for-charlier-polynomials
