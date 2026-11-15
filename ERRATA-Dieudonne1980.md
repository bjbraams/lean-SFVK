# Errata and source checks: Dieudonné (1980), Special Functions and Linear Representations of Lie Groups

Reference: Jean Dieudonné, *Special Functions and Linear Representations of Lie Groups*, CBMS
Regional Conference Series in Mathematics 42, American Mathematical Society, Providence, R.I.,
1980. The local copy is
[References/Dieudonné1980SpecialFunctionsLinearRepresentationsLieGroups-AMS.CBMS42.pdf](References/Dieudonné1980SpecialFunctionsLinearRepresentationsLieGroups-AMS.CBMS42.pdf).
Synopsis: [SYNOPSIS-Dieudonne1980](SYNOPSIS-Dieudonne1980.md).

Locators use printed page numbers. To get the one-based PDF page number, add 5 (throughout the
book). Line numbers, where given, count from the top of the page; negative line numbers count
from the bottom. Equation numbers \((n)\) are the source's consecutive numbers (1)–(193).

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

- the location, as section, printed page, line and equation;
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries.

Synopsis entries cite errata by id. An erratum id \(\mathrm{D80\text{-}E}cc.s.nn\) is the
\(nn\)-th erratum located in subsection \(s\) of section §\(cc\) (two-digit section number;
\(s\) is the Roman-numeral item number in §3 and §7, and \(s=0\) otherwise).

## Scope

These are observations about this edition, not an official publisher list. No claim is made
that formulas without an erratum are free of errors. Formulas that the synopsis marks "as
printed" were transcribed from the page images without an independent check. Corrected
formulas in the synopsis are statements to be formalized. They are not Lean proofs.
Garbling of the PDF text layer is not an erratum; every printed formula quoted here was read
on the page image. The book is a survey that states many results without proof; remarks about
the state of knowledge in 1979 are not treated as errata.

Each section ends with a list of conventions and notation that are not errata, for example a
sign or normalization convention that differs from a modern reference.

## Summary by section

## Summary by chapter

- §1. Introduction: 5 entries, 0 errata.
- §2. Representations of SU(2): 14 entries, 4 errata (Confirmed 4).
- §3. The general theory of linear representations of compact groups: 15 entries, 1 erratum (Confirmed 1).
- §4. Lie theory of representations of compact connected Lie groups: 4 entries, 0 errata.
- §5. Induced representations of compact groups: 1 entry, 0 errata.
- §6. Spherical functions on compact groups: 6 entries, 0 errata.
- §7. Examples; spherical harmonics: 9 entries, 1 erratum (Confirmed 1).
- §8. The general theory of spherical functions: 9 entries, 4 errata (Confirmed 4).
- §9. Fourier and Plancherel transforms: 10 entries, 0 errata.
- §10. Extension of the Plancherel transform: 7 entries, 0 errata.
- §11. The subtleties of harmonic analysis: 6 entries, 0 errata.
- §12. Differential properties of spherical functions on Lie groups: 6 entries, 2 errata (Confirmed 2).
- §13. Spherical functions on semisimple Lie groups: 5 entries, 0 errata.
- §14. More on SL(2,R): 14 entries, 7 errata (Confirmed 7).
- §15. Automorphic functions: 5 entries, 4 errata (Confirmed 4).
- §16. Groups of isometries and Bessel functions: 5 entries, 0 errata.
- §17. Other special functions: 1 entry, 0 errata.
- Total: 122 entries, 23 errata (Confirmed 23).

## §1. Introduction

No errata.

### Conventions and notation (not errata)

- p. 1: the rotation matrix displayed after (2) is
  \(\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix}\), the transpose of the
  matrix of the rotation \((x,y)\mapsto(x\cos\theta-y\sin\theta,\ x\sin\theta+y\cos\theta)\) written
  just before; both satisfy the addition law ([D80.01.0.01]).

## §2. Representations of SU(2)

### D80-E02.0.01. Finite-dimensional representations of SL(2,C) need holomorphy

Status: Confirmed.
Location: §2, p. 5, after (17).
Printed: the \(U_N\) "constitute (up to equivalence) the only finite dimensional irreducible
representations of \(SL(2,\mathbb C)\)."
Correct: they are, up to equivalence, the finite-dimensional irreducible holomorphic
representations of \(SL(2,\mathbb C)\) (equivalently, the irreducible representations of its Lie
algebra as a complex Lie algebra). The continuous irreducible finite-dimensional representations
of \(SL(2,\mathbb C)\) as a real Lie group are the \(U_N\otimes\overline{U_M}\), \(N,M\ge0\).
Evidence: \(s\mapsto\bar s\) (\(N=0\), \(M=1\)) is a continuous irreducible two-dimensional
representation. It is not equivalent to \(U_1\): the character of \(U_1\) is \(\mathrm{tr}\,s\) and
that of \(\bar s\) is \(\overline{\mathrm{tr}\,s}\), and at \(s=\mathrm{diag}(2i,-\frac i2)\) these are
\(\frac{3i}2\ne-\frac{3i}2\).
Target: [D80.02.0.03].

### D80-E02.0.02. Range of the Euler angle \(\theta\)

Status: Confirmed.
Location: §2, p. 6, after (27).
Printed: every \(s\in SU(2)\) is \(s(\varphi,\theta,\psi)\) "with \(0\le\varphi<2\pi\),
\(0\le\theta<\pi\), \(-2\pi\le\psi<2\pi\)", the relations (28) "always hav[ing] solutions".
Correct: \(0\le\theta\le\pi\).
Evidence: by (28) \(|a|=\cos\frac\theta2>0\) for \(0\le\theta<\pi\), so the matrices with \(a=0\),
e.g. \(s=\begin{pmatrix}0&-1\\1&0\end{pmatrix}\) (\(a=0\), \(b=1\)), are not of the printed form; they are
\(s(\varphi,\pi,\psi)\) with \(e^{-i(\psi-\varphi)/2}=-i\). The text itself then says the solution is
unique "for \(|a|\ne0,1\)", which presupposes the case \(a=0\).
Target: [D80.02.0.07].

### D80-E02.0.03. Sign of the constant \(C_{lmn}\)

Status: Confirmed.
Location: §2, p. 7, (34).
Printed: \(C_{lmn}=\dfrac{(-1)^{l-n}i^{n-m}}{2^l}\sqrt{\dfrac{(l+m)!}{(l-n)!(l+n)!(l-m)!}}\).
Correct: \(C_{lmn}=\dfrac{(-1)^{l-m}i^{n-m}}{2^l}\sqrt{\dfrac{(l+m)!}{(l-n)!(l+n)!(l-m)!}}\)
(equivalently \((-1)^{l-n}i^{m-n}/2^l\cdots\)); the printed constant is off by \((-1)^{m-n}\).
Evidence: \(l=\frac12\), \(m=-\frac12\), \(n=\frac12\): by (21), \(T_l(s)\psi_{1/2}=T_l(s)1=a-bx=
a\psi_{1/2}-b\psi_{-1/2}\), so \(t^{1/2}_{-1/2,1/2}(s(0,\theta,0))=-b=-i\sin\frac\theta2\). Formula (33)
with the printed (34) gives \(C=i/\sqrt2\) and
\(P^{1/2}_{-1/2,1/2}(\cos\theta)=\frac i{\sqrt2}(1-\cos\theta)^{1/2}=+i\sin\frac\theta2\). A numerical
comparison of (33)–(34) with the matrix elements (25) for \(l=\frac12,1,\frac32\) at \(\theta=0.7\)
gives ratio exactly \((-1)^{m-n}\) in every entry; with the corrected constant all entries agree.
Target: [D80.02.0.09].

### D80-E02.0.04. Composition of Euler angles: phase of the second term

Status: Confirmed.
Location: §2, p. 8, line 1 (formula for \(e^{-i(\varphi+\psi)/2}\)).
Printed: \(e^{-i(\varphi+\psi)/2}=\dfrac{\cos(\theta_1/2)\cos(\theta_2/2)e^{-i\varphi_2/2}-
\sin(\theta_1/2)\sin(\theta_2/2)e^{-i\varphi_2/2}}{\cos\theta/2}\).
Correct: the second exponential is \(e^{+i\varphi_2/2}\).
Evidence: the \((1,1)\) entry of \(s(0,\theta_1,0)s(\varphi_2,\theta_2,0)\) is
\(\cos\frac{\theta_1}2\cos\frac{\theta_2}2e^{-i\varphi_2/2}-\sin\frac{\theta_1}2\sin\frac{\theta_2}2
e^{i\varphi_2/2}\) (the factor \(\mathrm{diag}(e^{-i\varphi_2/2},e^{i\varphi_2/2})\) multiplies the
second column of the first matrix by \(e^{i\varphi_2/2}\)), and this entry equals
\(a=e^{-i(\varphi+\psi)/2}\cos\frac\theta2\). Numerically, \(\theta_1=0.5\), \(\theta_2=0.9\),
\(\varphi_2=1.3\): \(a/\cos\frac\theta2=0.71631-0.69778i\) (unit modulus), the corrected formula gives
the same, the printed one gives \(0.71631-0.54454i\) (not of modulus 1). The formula for
\(e^{-i\varphi}\) and for \(\cos\theta\) on p. 7 check.
Target: [D80.02.0.12].

### Conventions and notation (not errata)

- §2 writes \(s=\begin{pmatrix}a&c\\b&d\end{pmatrix}\) for \(SL(2,\mathbb C)\) (upper-right entry \(c\)) and
  \(\begin{pmatrix}a&-\bar b\\b&\bar a\end{pmatrix}\) for \(SU(2)\) ([D80.02.0.03]).
- p. 7, (35): "\(k\) a positive integer" includes \(k=0\) ([D80.02.0.10]).
- p. 7, (37): the constant \(C_{lm}\) is unspecified and is not \(C_{lm0}\) of (34); (37) is (33) with
  \(n=0\) rewritten by the identity relating \((1-z^2)^{-m/2}D^{l-m}\) and \((1-z^2)^{m/2}D^{l+m}\)
  of \((1-z^2)^l\) ([D80.02.0.11]).
- p. 8, (42): \(P_l^{-k}\) is the Ferrers function of negative order; the identity was checked
  numerically with \(P_l^{-k}=(-1)^k\frac{(l-k)!}{(l+k)!}P_l^k\) ([D80.02.0.14]).

## §3. The general theory of linear representations of compact groups

### D80-E03.9.01. Clebsch–Gordan multiplicities need \(l'\ge l''\)

Status: Confirmed.
Location: §3, p. 13, (73)–(74) and the following sentence.
Printed: \(\chi_{l'}\chi_{l''}=\sum_{l=l'-l''}^{l'+l''}\chi_l\), and \(c^l_{l'l''}=1\) if
\(l'-l''\le l\le l'+l''\), \(0\) otherwise; \(H_{l'}\otimes H_{l''}\) is the sum of the \(H_l\),
\(l'-l''\le l\le l'+l''\).
Correct: the lower limit is \(|l'-l''|\) (as in (75)), with \(l-l'-l''\in\mathbb Z\); the printed
form is valid when \(l'\ge l''\), which the computation preceding (73) (summing over
\(m=-l'',\dots,l''\) and telescoping) assumes.
Evidence: \(l'=0\), \(l''=1\): \(T_0\otimes T_1=T_1\), so \(c^0_{0,1}=0\), while (74) gives
\(c^0_{0,1}=1\) since \(-1\le0\le1\).
Target: [D80.03.9.03].

### Conventions and notation (not errata)

- (48): the source writes \(\check f(s)=\overline{f(s^{-1})}\); the synopsis writes \(f^*\).
- (VII), (63): the class occurring in \(E_\rho\) is \(\bar\rho\), so \(d_\rho\) is the multiplicity of
  \(\bar\rho\), whence \(\overline{\chi_\rho}\) in (63) ([D80.03.7.01], [D80.03.7.02]).

## §4. Lie theory of representations of compact connected Lie groups

No errata.

### Conventions and notation (not errata)

None.

## §5. Induced representations of compact groups

No errata.

### Conventions and notation (not errata)

- The representation \(\sigma\) is tacitly unitary for the scalar product used on \(F\); this is
  needed for "the invariance of Haar measure shows that this representation is unitary"
  ([D80.05.0.01]).

## §6. Spherical functions on compact groups

No errata.

### Conventions and notation (not errata)

- (89): \(\omega_\rho=n_\rho^{-1}m^{(\rho)}_{11}\) presupposes the adapted basis of (85) with the
  \(K\)-fixed vector first ([D80.06.0.05]).

## §7. Examples; spherical harmonics

### D80-E07.1.01. The torus element \(s(\varphi,0,0)\)

Status: Confirmed.
Location: §7, p. 21, (94).
Printed: \(s(\varphi,0,0)=\begin{pmatrix}e^{i\varphi/2}&0\\0&e^{-i\varphi/2}\end{pmatrix}\).
Correct: \(s(\varphi,0,0)=\begin{pmatrix}e^{-i\varphi/2}&0\\0&e^{i\varphi/2}\end{pmatrix}\), as given by
(27).
Evidence: (27) with \(\theta=\psi=0\) gives \(\mathrm{diag}(e^{-i\varphi/2},e^{i\varphi/2})\) (conflict
between two displays). With the printed (94), \(T_l(s(\varphi,0,0))\psi_n=e^{+in\varphi}\psi_n\) by
(21), contradicting the sentence after (94), which uses (30): \(s(\varphi,0,0)\mapsto e^{-in\varphi}\).
The subgroup \(K\) and the conclusion \((\rho:\sigma_0)=1\) iff \(l\in\mathbb Z\) are unaffected.
Target: [D80.07.1.01].

### Conventions and notation (not errata)

- p. 22: the angle \(\theta\) between \(x\) and \(e_0\) is restricted to \(0<\theta<\pi\) where the
  \(K\)-orbit is an \((n-1)\)-sphere; bi-invariant functions are functions of
  \(\theta\in[0,\pi]\) ([D80.07.3.01]).
- p. 24: "Gegenbauer polynomial" \(G_{m,n+1}\) is normalized by \(G_{m,n+1}(1)=1\), i.e.
  \(C^{(n-1)/2}_m/C^{(n-1)/2}_m(1)\) in modern notation ([D80.07.3.07]).

## §8. The general theory of spherical functions

### D80-E08.0.01. The spherical function as a coefficient of \(L^2(G/K)\)

Status: Confirmed.
Location: §8, p. 25, (104).
Printed: \(\omega_\rho(s)=(U(s)\cdot\omega_\rho\,|\,\omega_\rho)\), \(U\) the representation of \(G\) on
\(L^2(G/K)\) (left translation).
Correct: \(\omega_\rho(s)=n_\rho\,(\omega_\rho\,|\,U(s)\omega_\rho)=n_\rho\,(U(s^{-1})\omega_\rho\,|\,
\omega_\rho)\); equivalently \((U(s)\omega_\rho\,|\,\omega_\rho)=n_\rho^{-1}\omega_\rho(s^{-1})=
n_\rho^{-1}\overline{\omega_\rho(s)}\). The unit vector \(\sqrt{n_\rho}\,\omega_\rho\) is
\(K\)-fixed and its coefficient is \(\overline{\omega_\rho}\) for \(U\), \(\omega_\rho\) for the conjugate
order of the scalar product.
Evidence: with \(\omega_\rho=t_{11}\) (D80.06.0.05), Schur orthogonality gives
\((U(s)\omega_\rho\,|\,\omega_\rho)=\int t_{11}(s^{-1}t)\overline{t_{11}(t)}\,dt=
\sum_kt_{1k}(s^{-1})\int t_{k1}\overline{t_{11}}=t_{11}(s^{-1})/n_\rho\). Two independent failures of
the printed form: (a) at \(s=e\) it gives \(\|\omega_\rho\|_2^2=1/n_\rho\ne1=\omega_\rho(e)\); e.g.
\(G=SO(3)\), \(K=SO(2)\), \(l=1\), \(\omega=\cos\theta\), \(\int_{S_2}\cos^2\theta\,d\sigma=\frac13\); (b)
for \(G=\mathbf U\), \(K=\{e\}\), \(\omega(s)=e^{is}\) (\(n_\rho=1\)):
\((U(s)\omega\,|\,\omega)=\frac1{2\pi}\int e^{i(t-s)}e^{-it}dt=e^{-is}\ne\omega(s)\).
Target: [D80.08.0.01].

### D80-E08.0.02. The fixed-point group of the reflection involution

Status: Confirmed.
Location: §8, p. 26, paragraph on \(SO(n+1,\mathbb R)\), \(SO(n,\mathbb R)\).
Printed: "we conclude that the subgroup \(K\) is exactly the subgroup of elements of \(G\) left
invariant by \(\sigma\)", \(\sigma(t)=sts^{-1}\), \(s\) the reflection in \(x_0=0\).
Correct: the fixed-point group of \(\sigma\) in \(SO(n+1)\) is \(S(O(1)\times O(n))=\{\mathrm{diag}
(\epsilon,A):\epsilon=\pm1,\ A\in O(n),\ \epsilon\det A=1\}\), which contains \(K\cong SO(n)\) with
index 2. The argument given only shows that a fixed \(t\) preserves the hyperplane \(x_0=0\), hence
\(t\cdot e_0=\pm e_0\). The Gelfand-pair conclusion survives (see D80.08.0.03 Supplementary): the
proof of Gelfand's theorem uses only \(K\subset\mathrm{Fix}(\sigma)\), \(\sigma(K)=K\) and the
decomposition.
Evidence: \(t=\mathrm{diag}(-1,-1,1,\dots,1)\in SO(n+1)\) commutes with \(s=\mathrm{diag}(-1,1,\dots,1)\)
and \(t\cdot e_0=-e_0\ne e_0\), so \(t\in\mathrm{Fix}(\sigma)\setminus K\).
Target: [D80.08.0.04].

### D80-E08.0.03. Order of factors in the decomposition \(u=vt^{-1}\)

Status: Confirmed.
Location: §8, p. 26, last line of the \(SO(n+1)\) paragraph.
Printed: "Now \(v=tu\) leaves \(e_0\) invariant, and therefore belongs to \(K\), so that we may write
\(u=vt^{-1}\)".
Correct: \(v=tu\) gives \(u=t^{-1}v\); Gelfand's condition \(x=yz\) (\(y\in K\), \(\sigma(z)=z^{-1}\)) is then
obtained for \(x=u^{-1}=v^{-1}t\) (every element being an inverse), or by applying the construction to
\(u^{-1}\).
Evidence: \(n=2\); let \(t\) be the rotation by an angle \(\alpha\notin\pi\mathbb Z\) in the
\((e_0,e_1)\)-plane, \(k\in K\) the rotation by \(\pi\) about \(e_0\), and \(u=t^{-1}k\). Then
\(ue_0=t^{-1}e_0\), the construction produces this \(t\), and \(v=tu=k\). Since \(ktk^{-1}=t^{-1}\),
\(vt^{-1}=kt^{-1}=tk\ne t^{-1}k=u\) (as \(t^2\ne1\)). The conclusion is unaffected.
Target: [D80.08.0.04].

### D80-E08.0.04. The conjugation \(c\) in the example \(SL(n,\mathbb R)\)

Status: Confirmed.
Location: §8, p. 27, lines 1–3.
Printed: "\(G_c=SL(n,\mathbb C)\), \(G=SL(n,\mathbb R)\); \(c_0\) is the mapping \(X\mapsto\bar X\), \(c\) the
mapping \(X\mapsto{}^tX^{-1}\), \(G_u\) the unitary group \(SU(n)\)".
Correct: \(c(X)={}^t\bar X^{-1}\), the conjugation of \(SL(n,\mathbb C)\) with fixed group \(SU(n)\);
its restriction to \(G=SL(n,\mathbb R)\) is \(X\mapsto{}^tX^{-1}\), whose fixed group is \(SO(n)\).
Evidence: \(c\) is required (p. 26) to be the anti-automorphism of \(G_c\) whose fixed group is
\(G_u\). The fixed group of the holomorphic map \(X\mapsto{}^tX^{-1}\) on \(SL(n,\mathbb C)\) is
\(SO(n,\mathbb C)\), which is not \(SU(n)\) (e.g. \(\mathrm{diag}(i,-i)\in SU(2)\) is not fixed:
\({}^tX^{-1}=\mathrm{diag}(-i,i)\)).
Target: [D80.08.0.05].

### Conventions and notation (not errata)

- p. 26, proof of Gelfand's theorem: "\(f(x^{-1})=\check f(x)\)" uses \(\check f\) without the complex
  conjugation of (48); with (48) the identity \(f^\sigma=\check f\) would fail for non-real \(f\). The
  argument is correct with \(\check f(x)=f(x^{-1})\), for which \((f*g)\check{}=\check g*\check f\)
  also holds ([D80.08.0.03]).
- §8, (I)–(III): "anti-automorphism" of \(G_c\) means an antiholomorphic automorphism
  ([D80.08.0.05]).

## §9. Fourier and Plancherel transforms

No errata.

### Conventions and notation (not errata)

- p. 32, (116): the cotransform \(\bar{\mathcal F}f=\mathcal F\check f\) is to be read with
  \(\check f(x)=f(x^{-1})\) (no conjugation), i.e. \(\bar{\mathcal F}f(\omega)=\int_Gf\omega\,dm_G\). With the
  conjugated \(\check f\) of (48) one would get \(\mathcal F\check f=\overline{\mathcal Ff}\) on \(Z\), and
  (116) would hold only up to complex conjugation: for \(G=\mathbb R\), \(K=\{e\}\), \(\mu=\epsilon_0\)
  the right side would be \(\int\overline{\hat f}\hat g\,d\lambda/2\pi=(g\,|\,f)\) instead of
  \((f\,|\,g)\). Formulas (118)–(124) are consistent with \(\bar{\mathcal F}f=\int f\omega\)
  ([D80.09.0.05], [D80.09.0.09]).

## §10. Extension of the Plancherel transform

No errata.

### Conventions and notation (not errata)

- \(P(G)\) (span of measures of positive type) and \(P(K\backslash G/K)\), \(P^1\), \(P^2\) (spaces of
  functions, identified with measures \(f\cdot m_G\)) use the same letter ([D80.10.0.01],
  [D80.10.0.07]).

## §11. The subtleties of harmonic analysis

No errata.

### Conventions and notation (not errata)

- p. 38, (1): Segal's theorem is cited in the form "\(\mathcal F(L^1(G))=C_0(\hat G)\) only when \(G\)
  is finite" ([D80.11.0.04]).

## §12. Differential properties of spherical functions on Lie groups

### D80-E12.0.01. The Casimir operator is not elliptic on a noncompact semisimple group

Status: Confirmed.
Location: §12, p. 41, paragraph after (143).
Printed: "when \(G\) is semisimple, there are differential operators which are both left and right
invariant (by any element of \(G\)) and elliptic (in particular a second order operator called the
Casimir operator)".
Correct: for compact semisimple \(G\) the Casimir operator is bi-invariant and elliptic. For
noncompact semisimple \(G\) no bi-invariant operator of order \(2\) built from the Casimir is
elliptic; analyticity of spherical functions follows instead from the left-\(G\)-invariant,
right-\(K\)-invariant elliptic operator \(\Omega+2\Omega_{\mathfrak k}\) (on bi-\(K\)-invariant
functions it acts as \(\Omega\)), or from the Laplace–Beltrami operator of \(G/K\).
Evidence: the principal symbol of the Casimir \(\Omega=\sum B^{ij}X_iX_j\) is the dual Killing form,
which is indefinite for noncompact semisimple \(\mathfrak g\); e.g. for \(\mathfrak{sl}(2,\mathbb R)\)
with basis \(H,E,F\), \(B(H,H)=8\), \(B(E,F)=4\), signature \((2,1)\), so the symbol vanishes on a
nonzero real cone of covectors.
Target: [D80.12.0.04].

### D80-E12.0.02. Bounded joint eigenfunctions need normalization and bi-invariance

Status: Confirmed.
Location: §12, p. 41, end of the paragraph after (143).
Printed: "it can be shown that all bounded functions which are eigenfunctions of all differential
operators having the invariance property described above are spherical functions."
Correct: a bounded continuous function that is bi-\(K\)-invariant, takes the value 1 at \(e\), and is
an eigenfunction of all left-\(G\)-, right-\(K\)-invariant differential operators is spherical.
Evidence: the constant \(2\) is a bounded joint eigenfunction but \(2(e)\ne1\). For the motion
group \(G=SO(2)\ltimes\mathbb R^2\), \(K=SO(2)\), \(g\mapsto e^{i(g\cdot0)_1}\) (first coordinate of
the translation part) is right-\(K\)-invariant, bounded, equal to 1 at \(e\), and an eigenfunction
of every such operator (these act on right-\(K\)-invariant functions as polynomials in the Laplacian
of \(\mathbb R^2\), and \(\Delta e^{ix_1}=-e^{ix_1}\)), but it is not left-\(K\)-invariant, hence not
spherical.
Target: [D80.12.0.05].

### Conventions and notation (not errata)

None.

## §13. Spherical functions on semisimple Lie groups

No errata.

### Conventions and notation (not errata)

- §13 uses the standard layout \(s=\begin{pmatrix}a&b\\c&d\end{pmatrix}\), \(s\cdot z=(az+b)/(cz+d)\),
  unlike §2 and §14 ([D80.13.0.03]).
- p. 44: "when \(\rho\) is an integer \(>0\), \(\mathfrak P_\rho\) is, up to a scalar factor, the
  corresponding Legendre polynomial": the factor is 1 (Laplace's integral) ([D80.13.0.04]).
- p. 44: "\(\mathfrak P_\rho\) is certainly bounded if \(\rho\) is purely imaginary" is a sufficient
  condition; the exact condition is \(-1\le\mathrm{Re}\,\rho\le0\) ([D80.13.0.05]).

## §14. More on SL(2,R)

### D80-E14.0.01. The inducing character of the cocycle (166)

Status: Confirmed.
Location: §14, p. 47, line after (166).
Printed: "\(\alpha(u,x_0)=\sigma_m(u)\) for \(u\in H\) and \(m=\frac12-ri\)".
Correct: \(m=ir-\frac12\).
Evidence: by (163) and (164), \(J_{u^{-1}}(x_0)=J_u(x_0)^{-1}\) for \(u\in H\), so
\(\alpha(u,x_0)=J_{u^{-1}}(x_0)^{ir-1/2}=J_u(x_0)^{-(ir-1/2)}=\sigma_{ir-1/2}(u)\) by (165).
Target: [D80.14.0.04].

### D80-E14.0.02. The odd cocycle (168)

Status: Confirmed.
Location: §14, p. 48, (168).
Printed: \(\alpha(s,x)=|bx+d|^{ir-(1/2)}\,\mathrm{sgn}(bx+d)\); "the corresponding representation is
unitary … it now has the form (153) with \(m=-1+ir\)".
Correct: \(\alpha(s,x)=|bx+d|^{1-ir}\,\mathrm{sgn}(bx+d)\) (the sign twist of the cocycle giving
(167)); in the normalization of (166) it is \(J_{s^{-1}}(x)^{ir/2-1/2}\,\mathrm{sgn}(bx+d)=
|bx+d|^{1-ir}\mathrm{sgn}(bx+d)\). The resulting representation (153) with \(m=-1+ir\) is as stated.
Evidence: for \(x'=s^{-1}\cdot x=(dx-c)/(-bx+a)\), \(bx'+d=1/(-bx+a)\). Hence the printed cocycle gives
\((\rho(s)f)(x)=|-bx+a|^{1/2-ir}\mathrm{sgn}(-bx+a)f(x')\), i.e. (153) with \(m=\frac12-ir\), and
\(\|\rho(s)f\|_2^2=\int|by+d|^{-3}|f(y)|^2\,dy\) (substituting \(x=s\cdot y\),
\(dx=dy/(by+d)^2\)), which is not \(\|f\|_2^2\): for \(s=\mathrm{diag}(t,t^{-1})\) it is
\(t^{3}\|f\|_2^2\). The corrected cocycle gives exponent \(-1+ir\) and \(\int|by+d|^{0}|f|^2=\|f\|^2\).
Target: [D80.14.0.05].

### D80-E14.0.03. Reducibility of the odd principal series at \(r=0\)

Status: Confirmed.
Location: §14, p. 48, after (168).
Printed: "All these representations may be shown to be irreducible".
Correct: all are irreducible except the odd representation \(\rho^-_0\) (form (153) with \(m=-1\)),
which is the direct sum of two irreducible representations (the limits of discrete series).
Evidence: for \(m=-1\), \(|t|^{-1}\mathrm{sgn}\,t=t^{-1}\), so
\((\rho^-_0(s)f)(x)=(-bx+a)^{-1}f\bigl((dx-c)/(-bx+a)\bigr)\). This preserves the closed subspace
\(H^2_+\subset L^2(\mathbb R)\) of boundary values of the Hardy space of the upper half-plane: if
\(F\) is holomorphic on \(\{\mathrm{Im}\,z>0\}\), so is \((-bz+a)^{-1}F((dz-c)/(-bz+a))\) (the Möbius map
\(z\mapsto(dz-c)/(-bz+a)\) has real coefficients and determinant 1, so it preserves the upper
half-plane, and \(-bz+a\ne0\) there), with the same \(H^2\) norm by unitarity. \(H^2_+\) and its
orthogonal complement \(H^2_-\) are nonzero proper invariant subspaces.
Target: [D80.14.0.06].

### D80-E14.0.04. The Cayley map of \(h\) sends the upper half-plane outside the disc

Status: Confirmed.
Location: §14, p. 48, paragraph before (168a).
Printed: "The fact that \(SL(2,\mathbb R)\) operates transitively on the half-space \(\mathrm{Im}\,z>0\)
and on \(\mathbf P_1(\mathbb R)\) is transformed by \(h\): \(z\mapsto(z+i)/(iz+1)\) into the fact that
\(G\) operates transitively on the unit disk \(|z|<1\) and on the unit circle".
Correct: \(z\mapsto(z+i)/(iz+1)\) maps \(\mathbf P_1(\mathbb R)\) onto \(|z|=1\) but maps
\(\{\mathrm{Im}\,z>0\}\) onto \(\{|z|>1\}\cup\{\infty\}\) (and the lower half-plane onto the disc). The
transitivity of \(G\) on \(\{|z|<1\}\) is true but is transported from the lower half-plane (or use
\(h^{-1}\), \(z\mapsto(z-i)/(-iz+1)\)).
Evidence: \(z=i\mapsto2i/0=\infty\); \(z=2i\mapsto3i/(-1)=-3i\), \(|-3i|>1\); for real \(z\),
\(|z+i|=|iz+1|\).
Target: [D80.14.0.07].

### D80-E14.0.05. Positive-type spherical functions are not only the \(\rho=-\frac12+ir\)

Status: Confirmed.
Location: §14, p. 50, after (175).
Printed: "we see that we only get spherical functions of positive type when the exponent \(\rho\)
in (150) has the form \(-\frac12+ir\) with \(r\) real."
Correct: the principal series give the spherical functions with \(\rho=-\frac12+ir\); the
positive-definite spherical functions of \((SL(2,\mathbb R),SO(2))\) are the \(\mathfrak P_\rho\) with
\(\rho\in-\frac12+i\mathbb R\) or \(\rho\in[-1,0]\) (trivial representation \(\rho=0\) or \(-1\);
complementary series \(-1<\rho<0\)).
Evidence: \(\omega\equiv1=\mathfrak P_0\) is a spherical function of positive type (trivial
representation) and \(0\notin-\frac12+i\mathbb R\). The complementary series give further ones
([D80-E14.0.07]).
Target: [D80.14.0.10].

### D80-E14.0.06. Exponent of the complementary-series kernel

Status: Confirmed.
Location: §14, p. 52, line 2.
Printed: \(H_m\) is the space of \(f\) for which
\(\iint_{\mathbb R^2}|x_1-x_2|^{-m}f(x_1)\overline{f(x_2)}\,dx_1\,dx_2\) is defined (\(-2<m<0\),
\(m\ne-1\)), as the invariant norm for (152).
Correct: the invariant kernel is \(|x_1-x_2|^{-m-2}\); as an ordinary integral this applies for
\(-2<m<-1\). For \(-1<m<0\) the kernel is not locally integrable and the invariant positive form is
\(\int|\hat f(\xi)|^2|\xi|^{m+1}\,d\xi\) (regularized kernel); the same Fourier form, up to a positive
constant, represents the kernel form for \(-2<m<-1\).
Evidence: for \(s=\mathrm{diag}(t,t^{-1})\), \(t>0\), (152) is \(f\mapsto t^mf(x/t^2)\), and
\(\iint|x_1-x_2|^\alpha t^{2m}f(x_1/t^2)\overline{f(x_2/t^2)}=t^{2m+4+2\alpha}\iint|x_1-x_2|^\alpha
f\bar f\). Invariance requires \(\alpha=-m-2\); the printed \(\alpha=-m\) gives the factor \(t^4\).
Equivalently, \(\int|\widehat{f_s}|^2|\xi|^{\gamma}=t^{2m+2-2\gamma}\int|\hat f|^2|\xi|^\gamma\) forces
\(\gamma=m+1\).
Target: [D80.14.0.14].

### D80-E14.0.07. The complementary series are spherical

Status: Confirmed.
Location: §14, p. 52, last sentence.
Printed: the complementary series "have no spherical functions associated with them".
Correct: each complementary-series representation has a one-dimensional space of \(K\)-fixed vectors,
spanned by \(f_0(x)=(1+x^2)^{m/2}\); its normalized coefficient is the positive-definite spherical
function \(\mathfrak P_{m/2}(\cosh\tau)\), \(-1<m/2<0\).
Evidence: for the rotation \(s=\begin{pmatrix}\cos t&-\sin t\\ \sin t&\cos t\end{pmatrix}\) (in the
layout \(\begin{pmatrix}a&c\\b&d\end{pmatrix}\)), \(-bx+a=\cos t-x\sin t\), \(dx-c=x\cos t+\sin t\), and
\(|-bx+a|^m\bigl(1+\bigl(\frac{x\cos t+\sin t}{\cos t-x\sin t}\bigr)^2\bigr)^{m/2}=
\bigl((\cos t-x\sin t)^2+(x\cos t+\sin t)^2\bigr)^{m/2}=(1+x^2)^{m/2}\). The form
\(\int|\hat f_0|^2|\xi|^{m+1}\) is finite (\(\hat f_0\) decays exponentially; near \(\xi=0\) it is bounded for \(m<-1\) and
\(O(|\xi|^{-m-1})\) for \(-1<m<0\)). In the circle model the same vector is the constant function, whose
coefficient is given by (175) with \(2l=m\).
Target: [D80.14.0.14].

### Conventions and notation (not errata)

- §14 uses the layout \(s=\begin{pmatrix}a&c\\b&d\end{pmatrix}\) of §2 for the action
  \(s\cdot x=(ax+c)/(bx+d)\), but \(\begin{pmatrix}a&b\\0&a^{-1}\end{pmatrix}\) for \(S_1\) and the standard
  layout for \(K\) and \(X\) ([D80.14.0.05], [D80.14.0.12]).
- p. 48: (167) is the representation of (166) with \(r\) replaced by \(r/2\): (166) gives
  \(|-bx+a|^{-1+2ir}\) since \(J_{s^{-1}}(s^{-1}\cdot x)=(-bx+a)^2\) ([D80.14.0.05]). Correspondingly,
  in (175) \(l=\frac12(-1+ir)\) gives \(\rho=-\frac12+\frac{ir}2\); the text's "\(\rho=-\frac12+ir\)" refers
  to the set of exponents ([D80.14.0.10]).
- p. 48: "no two of them are equivalent unless … opposite values of the real number \(r\)" is
  read with \(r\ne0\) and with equivalence holding for opposite values ([D80.14.0.06]).
- p. 49, (170): the powers are fixed so that \((a-be^{i\theta})^l\) and \((\bar a-\bar be^{-i\theta})^l\)
  are complex conjugate; the synopsis gives one explicit choice ([D80.14.0.09]).

## §15. Automorphic functions

### D80-E15.0.01. Disjointness of translates when \(-I\in\Gamma\)

Status: Confirmed.
Location: §15, p. 53, property (1) of the fundamental domain.
Printed: "(1) for any two different elements \(\gamma_1\ne\gamma_2\) in \(\Gamma\), the sets
\(\gamma_1\cdot F\) and \(\gamma_2\cdot\bar F\) have no common elements".
Correct: for \(\gamma_1\ne\pm\gamma_2\) (equivalently, index by the image of \(\Gamma\) in
\(PSL(2,\mathbb R)\)).
Evidence: \(-I\) acts trivially on \(P\); if \(-I\in\Gamma\) (as for \(SL(2,\mathbb Z)\) and its
congruence subgroups \(\Gamma_0(N)\)), \(\gamma_1=\gamma\), \(\gamma_2=-\gamma\) give
\(\gamma_1\cdot F=\gamma_2\cdot F\subset\gamma_2\cdot\bar F\), nonempty.
Target: [D80.15.0.01].

### D80-E15.0.02. \(L^2(\Gamma\backslash G/K)\) is not a subspace of \(L^2(G)\)

Status: Confirmed.
Location: §15, p. 53, last paragraph.
Printed: the functions satisfying (181) and belonging to \(L^2(G)\) "form a closed subspace
\(L^2(\Gamma\backslash G/K)\) of \(L^2(G)\)".
Correct: \(L^2(\Gamma\backslash G/K)\) is the space of functions satisfying (181) that are square
integrable on \(\Gamma\backslash G\) for the measure \(m_{\Gamma\backslash G}\) of (183).
Evidence: if \(\Gamma\) is infinite and \(g\) satisfies (181), then by (183)
\(\int_G|g|^2\,dm_G=\int_{\Gamma\backslash G}\sum_\gamma|g(\gamma s)|^2=\infty\cdot\int_{\Gamma\backslash
G}|g|^2\), so the only such \(g\in L^2(G)\) is \(0\); e.g. the constant \(1\), which lies in
\(L^2(\Gamma\backslash G/K)\) for compact \(\Gamma\backslash G\).
Target: [D80.15.0.02].

### D80-E15.0.03. The bound on the kernel \(K_f\)

Status: Confirmed.
Location: §15, p. 54, after (185).
Printed: "\(K_f\) is continuous in the compact space \((\Gamma\backslash G)\times(\Gamma\backslash G)\), and
… its norm (as continuous function) satisfies \(\|K_f\|\le N_1(f)\)".
Correct: \(K_f\) is continuous (so \(V(f)\) is Hilbert–Schmidt, hence compact, for \(f\in C_c\)); the
bound \(\|V(f)\|\le N_1(f)\) holds for the operator norm on \(L^2(\Gamma\backslash G)\), and gives the
extension of compactness to \(f\in L^1(K\backslash G/K)\).
Evidence: let \(0\le f\le1\) be continuous, bi-\(K\)-invariant, supported in a small neighbourhood \(U\)
of \(K\), with \(f=1\) on \(K\); \(N_1(f)\le m_G(U)\to0\) as \(U\) shrinks to \(K\) (\(G\) noncompact,
\(m_G(K)=0\)). All terms of (185) are \(\ge0\), so \(K_f(\dot x,\dot x)\ge f(x^{-1}x)=f(e)=1\) and
\(\|K_f\|_\infty\ge1>N_1(f)\).
Target: [D80.15.0.04].

### D80-E15.0.04. Eigenvalue in (186) versus the spherical function of (187)

Status: Confirmed.
Location: §15, p. 54, (186)–(187).
Printed: \(g*f=\langle f,\omega_n\rangle g\) (with \(\langle f,\omega\rangle=\int_Gf\omega\,dm_G\) as in §8),
and \(\omega_n(s)=h(x_0)^{-1}\int_Kg(s_0ts)\,dm_K(t)\).
Correct: with \(\omega_n\) defined by (187), \(g*f=\bigl(\int_Gf(s)\omega_n(s^{-1})\,dm_G(s)\bigr)g=
(\mathcal Ff)(\omega_n)\,g\); equivalently, keep \(\langle f,\omega_n\rangle\) and replace (187) by
\(\omega_n(s^{-1})\). The two agree when \(\omega_n(s^{-1})=\omega_n(s)\) (e.g. for
\((SL(2,\mathbb R),SO(2))\)).
Evidence: \((g*f)(s_0)=\int g(s_0s)f(s^{-1})\,ds=\int\!\int_Kg(s_0ts)\,dt\,f(s^{-1})\,ds=
g(s_0)\int\omega_n(s)f(s^{-1})\,ds\). Example: \(G=\mathbb R\), \(K=\{0\}\), \(\Gamma=\mathbb Z\),
\(H_n=\mathbb Ce^{2\pi inx}\): (187) gives \(\omega_n(s)=e^{2\pi ins}\), while
\(g*f=\bigl(\int f(s)e^{-2\pi ins}ds\bigr)g\ne\bigl(\int f\omega_n\bigr)g\) in general (take \(f\) with
\(\hat f(n)\ne\hat f(-n)\)).
Target: [D80.15.0.05].

### Conventions and notation (not errata)

- p. 53: "\(\bar F\) compact and contained in \(P\)" is the cocompact case; the text then assumes
  \(\Gamma\backslash G\) compact for general Gelfand pairs ([D80.15.0.01], [D80.15.0.02]).

## §16. Groups of isometries and Bessel functions

No errata.

### Conventions and notation (not errata)

- p. 56, (192): since \(\omega(stxt^{-1})=\omega(stx)\) by right \(K\)-invariance, (192) is the
  functional equation (107) for \(y=x\in A\) ([D80.16.0.03]).
- p. 57: "for \(\lambda\) and \(\mu\) purely imaginary, they are bounded" is a sufficient
  condition; \(\psi(r)=I_0(r\sqrt{\lambda^2+\mu^2})\) is bounded iff \(\lambda^2+\mu^2\le0\)
  ([D80.16.0.04]).

## §17. Other special functions

No errata.

### Conventions and notation (not errata)

- p. 58: "can be treated as the representations of the discrete series of \(SL(2,\mathbb R)\) in §14,
  using the Mellin transforms": in §14 the Mellin transforms (176)–(177) are applied to the
  principal series, not the discrete series ([D80.17.0.01]).

[D80.01.0.01]: SYNOPSIS-Dieudonne1980.md#d8001001-the-exponential-as-a-homomorphism
[D80.02.0.03]: SYNOPSIS-Dieudonne1980.md#d8002003-the-polynomial-representations-of-sl2c
[D80.02.0.07]: SYNOPSIS-Dieudonne1980.md#d8002007-euler-angles-on-su2
[D80.02.0.09]: SYNOPSIS-Dieudonne1980.md#d8002009-rodrigues-formula-for-pl_mn
[D80.02.0.10]: SYNOPSIS-Dieudonne1980.md#d8002010-jacobi-polynomials-and-pl_mn
[D80.02.0.11]: SYNOPSIS-Dieudonne1980.md#d8002011-legendre-polynomials-and-associated-legendre-functions
[D80.02.0.12]: SYNOPSIS-Dieudonne1980.md#d8002012-composition-of-euler-angles
[D80.02.0.14]: SYNOPSIS-Dieudonne1980.md#d8002014-multiplication-formulas
[D80.03.7.01]: SYNOPSIS-Dieudonne1980.md#d8003701-isotypic-decomposition-of-unitary-representations
[D80.03.7.02]: SYNOPSIS-Dieudonne1980.md#d8003702-finite-dimensional-representations-traces-and-equivalence
[D80.03.9.03]: SYNOPSIS-Dieudonne1980.md#d8003903-clebschgordan-decomposition
[D80.05.0.01]: SYNOPSIS-Dieudonne1980.md#d8005001-induced-representation
[D80.06.0.05]: SYNOPSIS-Dieudonne1980.md#d8006005-zonal-spherical-functions-on-compact-groups
[D80.07.1.01]: SYNOPSIS-Dieudonne1980.md#d8007101-su2-relative-to-its-diagonal-torus
[D80.07.3.01]: SYNOPSIS-Dieudonne1980.md#d8007301-setting-for-s_n
[D80.07.3.07]: SYNOPSIS-Dieudonne1980.md#d8007307-gegenbauer-polynomials
[D80.08.0.01]: SYNOPSIS-Dieudonne1980.md#d8008001-summary-of-the-compact-case
[D80.08.0.03]: SYNOPSIS-Dieudonne1980.md#d8008003-gelfands-theorem
[D80.08.0.04]: SYNOPSIS-Dieudonne1980.md#d8008004-son1son-is-a-gelfand-pair
[D80.08.0.05]: SYNOPSIS-Dieudonne1980.md#d8008005-three-classes-of-gelfand-pairs
[D80.09.0.05]: SYNOPSIS-Dieudonne1980.md#d8009005-the-plancherelgodement-theorem
[D80.09.0.09]: SYNOPSIS-Dieudonne1980.md#d8009009-inversion-via-approximate-units
[D80.10.0.01]: SYNOPSIS-Dieudonne1980.md#d8010001-plancherel-transform-on-the-span-of-positive-type-measures
[D80.10.0.07]: SYNOPSIS-Dieudonne1980.md#d8010007-the-spaces-p1-p2-and-fourier-reciprocity
[D80.11.0.04]: SYNOPSIS-Dieudonne1980.md#d8011004-negative-results-on-the-line
[D80.12.0.04]: SYNOPSIS-Dieudonne1980.md#d8012004-analyticity-in-the-semisimple-case
[D80.12.0.05]: SYNOPSIS-Dieudonne1980.md#d8012005-converse-joint-eigenfunctions
[D80.13.0.03]: SYNOPSIS-Dieudonne1980.md#d8013003-sl2mathbb-r-the-poincaré-half-plane-double-cosets
[D80.13.0.04]: SYNOPSIS-Dieudonne1980.md#d8013004-legendre-functions-of-complex-index
[D80.13.0.05]: SYNOPSIS-Dieudonne1980.md#d8013005-product-formula-boundedness
[D80.14.0.04]: SYNOPSIS-Dieudonne1980.md#d8014004-quasi-invariant-measures-and-unitary-induction
[D80.14.0.05]: SYNOPSIS-Dieudonne1980.md#d8014005-the-principal-series
[D80.14.0.06]: SYNOPSIS-Dieudonne1980.md#d8014006-irreducibility-and-equivalences-of-the-principal-series
[D80.14.0.07]: SYNOPSIS-Dieudonne1980.md#d8014007-the-quasi-unitary-group-and-the-circle-model
[D80.14.0.09]: SYNOPSIS-Dieudonne1980.md#d8014009-matrix-coefficients-of-the-principal-series-in-the-circle-model
[D80.14.0.10]: SYNOPSIS-Dieudonne1980.md#d8014010-the-spherical-principal-series
[D80.14.0.12]: SYNOPSIS-Dieudonne1980.md#d8014012-representations-induced-from-so2
[D80.14.0.14]: SYNOPSIS-Dieudonne1980.md#d8014014-the-complementary-series
[D80.15.0.01]: SYNOPSIS-Dieudonne1980.md#d8015001-fundamental-domains-of-fuchsian-groups
[D80.15.0.02]: SYNOPSIS-Dieudonne1980.md#d8015002-automorphic-functions
[D80.15.0.04]: SYNOPSIS-Dieudonne1980.md#d8015004-periodization-and-the-kernel-of-vf
[D80.15.0.05]: SYNOPSIS-Dieudonne1980.md#d8015005-spectral-decomposition-of-l2gammabackslash-gk
[D80.16.0.03]: SYNOPSIS-Dieudonne1980.md#d8016003-all-positive-definite-spherical-functions-come-from-unitary-characters
[D80.16.0.04]: SYNOPSIS-Dieudonne1980.md#d8016004-the-euclidean-motion-group-of-the-plane-j_0
[D80.17.0.01]: SYNOPSIS-Dieudonne1980.md#d8017001-a-solvable-group-and-whittaker-functions
