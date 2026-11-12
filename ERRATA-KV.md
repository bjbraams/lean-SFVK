# Errata and statement checks for Klimyk–Vilenkin, EMS 59, Part II

Reference: A. U. Klimyk and N. Ya. Vilenkin, *Representations of Lie Groups and
Special Functions*, Part II of A. A. Kirillov (ed.), *Representation Theory and
Noncommutative Harmonic Analysis II*, Encyclopaedia of Mathematical Sciences 59,
Springer, 1995. The local volume is in [References](References/).

This record covers Chapters 1–6. Printed page \(p\) is PDF page \(p+6\).
Equation numbers restart in each chapter. The chapter and subsection are therefore
part of every locator. These are observations about this edition, not an official
publisher errata list. Formula transcriptions were checked against page images
where the OCR omitted symbols or suggested a discrepancy.

**Confirmed** means a contradiction is exhibited by a direct calculation, an
identity/endpoint test, or a standard definition already fixed in the source.
**Normalization check** means the displays cannot yet be combined under one
specified convention; an unstated change of basis, coordinate, or measure may
explain the difference. **Open check** means a suspected problem is not yet
resolved and is not being presented as an established error.

Proposed corrected formulas in the synopses are mathematical acquisition targets.
They are not Lean proofs, and do not constitute an approved modification of an
existing formal theorem. Disputed printed assertions are not to be adopted silently.

## Chapter 1

### E01.01. Adjointness of split Cartan operators

**Confirmed.** §1.1, p. 155, prose before (2).
The operators \(\mathrm{ad}H\), \(H\in\mathfrak a\subset\mathfrak p\), are called
skew-Hermitian for \(-B(X,\theta Y)\). They are self-adjoint.
For \(H=\mathrm{diag}(1,-1)\) and \(X=E_{12}\) in
\(\mathfrak{sl}_2(\mathbb R)\), \([H,X]=2X\); a nonzero real eigenvalue excludes
skew-adjointness in a positive inner product.

Target: [KV01.01](SYNOPSIS-KV01.md#kv0101-cartan-involution-and-restricted-roots).

### E01.02. Higher parabolics and Levi factors

**Confirmed.** §1.1, p. 156, prose about parabolics containing \(MAN\).
Enlarging only the compact factor \(M\) inside \(K\) does not describe every
larger parabolic with the same \(A,N\). For \(SL(3,\mathbb R)\), a proper block
parabolic has a noncompact \(SL(2,\mathbb R)\) semisimple Levi factor.
Its Levi factor is not a uniquely determined embedded maximal semisimple subgroup:
different Levi factors can be conjugate by the unipotent radical.
A statement about a chosen Levi decomposition is needed.

Target: KV01.02.

### E01.03. Chamber and uniqueness qualifications

**Confirmed as a missing qualification.** §1.1, p. 156.
Positivity is required only for positive restricted roots: demanding positivity
for both \(\gamma\) and \(-\gamma\) is impossible.
The \(A\)-factor of an unrestricted \(KAK\) decomposition is unique only modulo
the Weyl group. Inside a fixed open chamber the residual compact ambiguity is
\(M\); at chamber walls it is the larger centralizer.
At the identity, all \(K\)-elements can occur in the residual ambiguity.

Target: KV01.02.

### E01.04. Half-root radial density

**Normalization check.** §1.1, p. 157, (4)–(5).
The source defines \([H,X]=\gamma(H)X\), but writes
\(\sinh(\gamma(H)/2)\) and \(\sin(\gamma(H)/2)\) in the density.
In exponential coordinates \(g=k_1e^Hk_2\), the corresponding standard density
uses \(\sinh\gamma(H)\) and \(\sin\gamma(H)\).
For \(SL(2,\mathbb R)\), \(H=\mathrm{diag}(t,-t)\) has root \(2t\).
A half-coordinate convention could explain the factor, but must be stated.

Target: KV01.03. No absolute Haar normalization is inferred from these displays.

### E01.05. Hyperboloid and Iwasawa logarithm signs

**Confirmed.** §1.3, p. 158, prose and (10a).
For the displayed form \(x_1^2+\cdots+x_n^2-x_{n+1}^2\), the claimed base point
\((0,\ldots,0,1)\) has norm \(-1\), not \(1\).
The future hyperboloid should have level \(-1\).
For \(e_0=(0,\ldots,0,1,1)\), one also has
\([x_0,h(t)e_0]=-e^t\); its real logarithm is undefined.
The logarithm of the positive last coordinate, equivalently
\(\log(-[x_0,ge_0])\), gives the intended parameter.

Target: KV01.04.

### E01.06. Unitary-group subgroup indices

**Confirmed.** §1.4, pp. 158–159, (11).
The maximal compact subgroup of \(U(n,1)\) is \(U(n)\times U(1)\), not
\(U(n-1)\times U(1)\). The accompanying \(K'\) in the stated double-coset
factorization is correspondingly misindexed.
For example \(U(1,1)\) already has a two-dimensional maximal compact torus.

Target: KV01.05. Reindex the entire formula consistently before adoption.

### E01.07. Auxiliary triangular sets are not groups as printed

**Confirmed.** §1.6, p. 160.

- The \(S_2\) restriction \(\tau>0\) excludes the identity and inverses;
  the real group requires \(\tau\in\mathbb R\).
- In the \(S_3\) display, real \(r,s\) are not preserved by multiplication
  with arbitrary diagonal phases. A phase matrix times a real translation
  generally has complex translations.
- For complex \(a,b,d\), the \(c=1\) subgroup of \(S\) is the complex
  Heisenberg group, of real dimension six. Calling it three-dimensional
  is correct over \(\mathbb C\), or for the real-parameter subgroup over
  \(\mathbb R\), but these must be distinguished.

Target: KV01.06. A corrected parameter group for \(S_3\) is not silently assumed.

### E01.08. Oscillator subgroup quadratic factor

**Confirmed.** §1.6, p. 160, display defining \(s(w,\alpha,\delta)\).
With \(a=e^{-i\alpha}\bar w/2,\ d=-w/2\), the real quadratic term in \(b\)
must be \(-|w|^2/8\), not \(-|w|^2/2\).
Take \(\alpha=\delta=0\) and real \(w_1=w_2=2\).
The printed matrices have \(a=1,d=-1,b=-2\).
Their product has \(a=2,d=-2,b=-5\), while the printed formula at \(w=4\)
requires \(b=-8\); changing the real central parameter only changes
the imaginary part of \(b\). The printed set is not closed.

The factor \(1/8\) restores closure and matches the Gaussian
\(e^{-\rho r^2/2}\) in Chapter 2, (33), when \(w=2re^{i\vartheta}\).
The synopses explicitly use this proposed normalized subgroup for oscillator
identities.

Targets: KV01.06, KV01.13, KV02.13, KV06.07, KV06.17–18.

### E01.09. Sign of the spherical unitarity parameter

**Normalization check.** §2.1, p. 161, after (18).
The equivariance and compact-picture multiplier are \(e^{-\nu(H)}\),
but the stated line is \(\nu+\rho\) imaginary.
For positive-root \(KAN\), the usual compact-picture Jacobian makes this
equivariance unitary on the line \(\Re\nu=\rho\), rather than \(-\rho\).
An opposite inducing-parameter convention could reverse the sign; it cannot
be changed in just the unitarity sentence.

Target: KV01.07. The sign-conflicted general unitarity assertion is withheld.

### E01.10. Compact orthogonal boundary model

**Normalization check.** §2.6, pp. 164–165, (26).
The prose combines homogeneous harmonic polynomials in \(n\) variables with
all degrees at most \(l\), while the compact degree-\(l\) irreducible lives
naturally in harmonics in \(n+1\) variables.
In (26), the multiplier contains \(\sin\varphi_{n-1}\), but the following
transformed coordinate formula uses \(\cos\varphi_{n-1}\).
Continuing the noncompact formula predicts the cosine in both places.

Target: KV01.10. The intrinsic harmonic model is specified separately.

### E01.11. Dilation multiplier

**Confirmed.** §2.8, p. 166, (32).
Equation (31) with \(b=0\) gives \(a^{-w}F(w)\), not \(e^{-w}F(w)\).
The latter is only the case \(a=e\).

Target: KV01.12.

### E01.12. Irreducibility of the full circle model

**Confirmed.** §2.10, p. 168, after (44).
The stated circle operators preserve the proper closed Hardy subspace:
rotation preserves nonnegative Fourier powers, and multiplication by
\(e^{-\alpha(rz^2+sz)}\) and its inverse preserve that subspace.
They therefore do not give an irreducible representation on all of \(L^2(S^1)\).

Target: KV01.13. No replacement irreducibility theorem is inferred.

## Chapter 2

### E02.01. Equivariant Fourier expansion dimension factors

**Confirmed.** §1.4, pp. 171–173, Theorems 3–4.
The function-space direction in the prose is opposite to that dictated by
\(F(h_1gh_2)=Q_r(h_1)F(g)Q_s(h_2)\): the operator maps \(V_s\) to \(V_r\).
More substantially, the displayed reciprocal dimension factors do not
recover Peter–Weyl when \(H=\{e\}\). For the unscaled matrix blocks,
\[
\|T^\pi_{ri,sj}\|_2^2=d_rd_s/d_\pi.
\]
Hence the Fourier coefficient multiplier and Parseval multiplier are
\(d_\pi/(d_rd_s)\), with \(d_\pi/d_r\) for vector columns.
Taking a single nontrivial matrix coefficient tests the reciprocal immediately.

Target: KV02.04.

### E02.02. Canonical-basis phase versus Jacobi coefficient

**Confirmed.** §2.2, p. 178, (19)–(19a), compared with Chapter 1, (25).
The canonical basis includes \((-i)^{l-k}\), while the real Jacobi formula
corresponds to unphased monomials. For \(l=1/2\) and a real rotation,
the coefficient from the input \(-ix\) to the constant vector is
\(-i\sin(\theta/2)\), whereas (19a) gives \(\sin(\theta/2)\).
The missing conversion factor is \((-i)^{m-n}\).
A consistent rephasing resolves it, but both conventions must not be used
interchangeably in addition or differential formulas.

Target: KV02.10.

### E02.03. Opposite discrete-series radial ordering

**Confirmed sign/index conflict.** §2.1, p. 178, (18a).
The printed reverse-order formula is positive for both neighboring off-diagonal
coefficients of a real boost near the identity. A differentiable unitary
one-parameter representation has a skew-adjoint generator; its opposite
off-diagonal entries must be negative conjugates.
The expression also retains \(m-n\) as a Jacobi parameter in the
opposite ordering. Obtain the reverse coefficient from the unitary inverse
relation after fixing the radial convention.

Related direct check: E06.02 below.

### E02.04. Euclidean Bessel dimension and a denominator

**Confirmed.** §2.5, p. 181, (28)–(29).
The model is functions on \(S^{n-1}\), so its zonal Bessel order is
\(n/2-1\), not \((n-1)/2\).
At \(n=2\), integrating over the circle gives \(J_0\); the printed formula
instead gives the half-order sinc expression.
Equation (29) also prints a denominator \(3\) in the scaled argument where
the corresponding Bessel series normalization would use \(2\).
Recompute the entire formula from the sphere integral, rather than changing
just that digit.

Target: KV02.11.

### E02.05. Quadratic-circle Hermite coefficients

**Confirmed.** §2.7, p. 182.
The multiplier \(e^{-\alpha(rz^2+sz)}\) fixes each coefficient by an elementary
finite expansion. The source's linear-translation sign and Hermite argument
do not match it: the displayed argument even contains an \(s\) which cancels.
For the basis \(z^{-n}\), the coefficient with \(q=n-m\ge0\) is
\[
\sum_{j=0}^{\lfloor q/2\rfloor}
 \frac{(-\alpha r)^j(-\alpha s)^{q-2j}}{j!(q-2j)!}.
\]
In physicists' Hermite notation the argument is
\(-\sqrt\alpha\,s/(2\sqrt r)\), with the combined polynomial interpretation
at \(r=0\). The opposite basis convention reverses the triangular indexing.

Target: KV02.13.

### E02.06. Last-coordinate phase and unspecified constants

**Confirmed omission; open formula check.** §2.8, pp. 182–183.
The diagonal phase display after (34) omits the angle \(\varphi\) from
\(\exp i(p+p'-m-m')\). At \(\varphi=0\), it must be the identity.
The constants \(A,B,C\) in (36)–(37) are not given in this chapter,
so those expressions are not fully evaluable formulas from this reference
alone. The constants in (34)–(35) also need an identity-element check.

Target: KV02.14. No guessed constants are supplied.

### E02.07. Second hypergeometric branch exponent

**Confirmed.** §2.1, p. 177, second display evaluating the coefficient integral.
For \(m\ge n\), the printed exponent of \(\bar\alpha\) is
\(\tau+m+\epsilon\); it should be \(\tau+n+\epsilon\).
For a real boost, \(\tau=1,\epsilon=0,m=1,n=0\), the defining integral
gives \(\cosh(t/2)\sinh(t/2)\), whereas the printed expression gives
\(\cosh^2(t/2)\sinh(t/2)\).
The corrected exponent also agrees with the following Jacobi radial formula.

Target: KV02.09.

## Chapter 3

### E03.01. Boost range and dimension inequality

**Confirmed.** §1.2, p. 185, after (6), bounds a noncompact boost by \(\pi\);
the boost parameter is unbounded.
Section 1.4, p. 187, says \(n<2\) for the higher-dimensional Bessel
addition theorem; the formula with \(p=(n-2)/2>0\) requires \(n>2\).

Targets: KV03.02, KV03.04.

### E03.02. Jacobi-function infinite addition constant

**Open check with a failed constant term.** §1.5, p. 188, (20).
Set both radial arguments to zero, so only the \(m=j=0\) term remains.
With the printed coefficient, its value reduces to
\(\Gamma(\beta+\nu+1)/\Gamma(\beta+1)\), although the normalized
Jacobi function at \(1\) equals \(1\).
This indicates a missing normalization or a coefficient error. A possible
alternative convention would need to change the definition of \(R\) too.
Convergence conditions for the infinite double series are also not stated.

Target: KV03.05. The coefficient is recorded as source data pending correction.

### E03.03. Sign in the scalar Legendre Mellin integral

**Confirmed.** §3.2, p. 197, (39).
For \(x>1\) and \(\tau=-1/2\), the integral is positive and
\(P_{-1/2}(x)>0\), but the printed \(\sin(\pi\tau)/\pi\) is negative.
The prefactor should be \(-\sin(\pi\tau)/\pi\) with the stated orientation.
The inverse Barnes formula on p. 198 already has the compatible sign.

Target: KV03.14.

### E03.04. Operator-domain qualifications

**Missing hypotheses.** §§1.1, 1.8–1.9, 4.1, pp. 184, 190–191, 200–201.
Differentiating an infinite coefficient sum requires smooth vectors or
a generator-domain argument. Schur's lemma for bounded operators does not
by itself make an unbounded central differential operator scalar.
Use an infinitesimal-character theorem in the relevant representation category.
These are hypothesis gaps in the informal presentation, not claims that
the rank-one differential equations are false.

Targets: KV02.01, KV03.08, KV03.16.

### E03.05. Degree in the Jacobi derivative

**Confirmed.** §1.5, p. 188, the derivative identity immediately above (19).
The right side must have \(P_{n-1}^{(\alpha+1,\beta+1)}\), not
\(P_n^{(\alpha+1,\beta+1)}\). Differentiation lowers the degree by one.
For \(n=1,\alpha=\beta=0\), the left side is \(1\), while the
printed right side is \(P_1^{(1,1)}(x)=2x\).

Target: KV03.05.

## Chapter 4

### E04.01. Affine gamma-kernel scale

**Confirmed.** §1.2, p. 204, (1).
The preceding integral has \(e^{\lambda bx/a}\), so the gamma evaluation is
\[
a^{-w}\Gamma(w-z)(-\lambda b/a)^{z-w}/(2\pi i)
 =a^{-z}\Gamma(w-z)(-\lambda b)^{z-w}/(2\pi i).
\]
The printed denominator \(2\) in \((-\lambda b/2)^{z-w}\) is not justified.

Target: KV04.02.

### E04.02. Signed Mellin factors and Whittaker channels

**Confirmed omissions; normalization check.** §1.4, pp. 206–207, (14)–(21).
All signed-Mellin channels use the same inverse Mellin measure.
Equations (15)–(16) omit \(1/(2\pi i)\), although (14) retains it.
Equation (19)'s denominator \(\Gamma(\lambda-\mu-1)\) conflicts with
the beta-channel factor \(\Gamma(\lambda-\mu+1)\).
Direct evaluation of the signed Mellin integral is the normalization test.
The \(W\)-channel constants in (18), (20) should be checked together with
the Gaussian and powers in the subgroup parametrizations.

Target: KV04.04.

### E04.03. Cylinder-kernel convergence conditions

**Confirmed missing hypotheses.** §1.5, p. 207, (22)–(23).
Nonzero \(r,s\) and \(\Re\lambda>0\) do not alone ensure convergence
of the defining quadratic Laplace integral. A sufficient domain is
\(\Re(\alpha r)>0,\Re\lambda>0\); for \(r=0\), it is
\(\Re(\alpha s)>0,\Re\lambda>0\).
The printed condition involving \(\Re(\lambda s)\) in (23) uses
the wrong parameter.

Target: KV04.05.

### E04.04. Discrete-series spectral measures and Gaussian

**Normalization check; confirmed conflicting powers.** §1.7, p. 211,
(44)–(49).
The generalized vector \(x^{2i\lambda-1/2}/\sqrt{2\pi}\) has
delta normalization \(\tfrac12\delta(\lambda-\mu)\) for Lebesgue
spectral measure, not \(\delta(\lambda-\mu)\).
Either the vector or the measure must be rescaled.
The parabolic vector also carries a nontrivial \(\lambda^{-1/2}\)
factor and therefore requires its own measure.
In (46), the Laguerre argument is \(\lambda^2e^{-t}\), while the printed
Gaussian uses \(\lambda e^{-t}\); a dilated normalized Laguerre function
requires the same squared variable in both.

Targets: KV04.07, KV05.04.

### E04.05. Meixner–Pollaczek norm

**Confirmed.** §1.8, p. 212, final display.
For the defined polynomial, the norm is
\[
2\pi\Gamma(n+2k)\big/(n!(2\sin\varphi)^{2k}).
\]
The printed \(\pi(2k-1)!/n!\) multiplier misses both the factor \(2\)
and the dependence of the gamma factor on \(n\).
For \(k=1,\varphi=\pi/2,n=0\),
\(\int_{\mathbb R}|\Gamma(1+ix)|^2dx=\pi/2\), not \(\pi/4\).

Targets: KV04.08, KV05.04.

### E04.06. Barnes representations: a Gaussian and unresolved contours

**Confirmed Gaussian error; open checks.** §2.2, p. 214.
The parabolic-cylinder representation prints \(e^{-x^2/2}\).
The integral definition of \(D_\nu\) gives \(e^{-x^2/4}\).
The remaining factors agree with that value after Mellin inversion
of \(e^{-xt}\).

The alternative Whittaker \(W\) formula (54) and the \(M\) formula (55)
need explicit vertical-contour and branch checks. The latter's
\(\kappa\)-sign is not resolved here. They are recorded as open checks,
not declared false on the basis of OCR alone.

Target: KV04.10.

### E04.07. Cylinder translation formula

**Confirmed.** §2.5, p. 217, (62)–(63).
For the stated convention,
\[
D_\nu(x+y)=e^{xy/2+y^2/4}
 \sum_{k=0}^\infty(-y)^kD_{\nu+k}(x)/k!.
\]
This follows by Taylor expansion of \(e^{-x^2/4}D_\nu(x)\).
The printed exponent, coefficient, and order shift do not give this
identity. The first derivative already tests the shift and sign through
\(D_\nu'=xD_\nu/2-D_{\nu+1}\).
For instance, the printed series at \(\nu=0\) has only its constant term
after its reciprocal-gamma coefficients are interpreted, and gives the
wrong Gaussian ratio.

Target: KV04.12.

### E04.08. Whittaker addition geometry

**Normalization check with a sign conflict.** §3.3, p. 220.
The first formula uses
\(r^2=t^2+2ts\cosh\tau+s^2\), but prints
\(e^{\tau_1}=(t-se^\tau)/r\). At \(t=s,\tau=0\), its right side
vanishes, impossible for an exponential, while the group product is regular.
The correct factor must be recovered from the triangular matrix product.
The neighboring second formula has different geometry and must be checked
separately.

Target: KV04.14.

### E04.09. Cylinder residue-series starting index

**Confirmed omission.** §3.4, p. 221, display after (68).
The sum starts at \(n=1\), losing the constant term in its residue expansion.
For an integral nonnegative order reduced to Hermite addition, the
degree-zero case already contradicts the displayed series.
The integral formula (68) and the product formula should be checked
independently; the missing constant term does not invalidate them.

Target: KV04.15.

### E04.10. Continuous Hahn weight and complex norm

**Confirmed.** §4.2, pp. 225–226.
The weight uses \(\Gamma(-a-ix)\) with \(a=-l_2>0\).
At positive integral \(a\), this has a pole at \(x=0\), so the claimed
degree-zero norm is infinite. The compatible positive weight uses
\(|\Gamma(a-ix)\Gamma(b+ix)|^2/(2\pi)\).
For complex \(b\), the printed \(\Gamma(a+b)^2\) factor in the norm
must also be an absolute square, as required by a nonnegative squared norm.

Target: KV04.18. The corrected full orthogonality theorem still needs
its parameter and conjugation conventions stated together.

### E04.11. Bessel–Jacobi product constant

**Confirmed missing scale.** §4.3, p. 227, penultimate long display.
For \(p=q=0\) and all \(x_i,y_i\) small, the left side starts with
\(J_1(R)\sim R/2\); the printed right side starts with \(R\).
Only the \(n=0\) term contributes at this order.
Thus a factor of \(2\) is missing between the two sides.
The synopsis records the printed expression as disputed rather than
choosing a corrected side without a full normalization derivation.

Target: KV04.19.

## Chapter 5

### E05.01. Haar scale and signs of discrete-series labels

**Normalization check.** §2.1–2.2, p. 231, (7)–(8).
The group inversion theorem has a fixed \(1/(4\pi^2)\) Plancherel scale.
Section 2.2 also normalizes the Euler-coordinate Haar density by
\(1/(4\pi^2)\). Rescaling Haar measure rescales the Fourier operators,
the Plancherel measure, and the discrete formal degrees; these constants
cannot be combined independently without the angular covering domain.
The positive series was earlier indexed by positive \(l\), but (7)
writes both signs at \(-l-1\). A common reindexing is possible, and
must be made explicit.

Targets: KV05.06–07.

### E05.02. Radial discrete summation range

**Normalization check.** §2.2, p. 232, (9)–(11).
For \(N=-\min(|m|,|n|)\), the displayed discrete sum often has a negative
upper label below its starting label. It must be read as a descending
weight-lattice sum. The half-integral starting label must also match
the lattice, and zero weights give no discrete summand.
Use occurrence of the fixed weights in the actual discrete representation
to define the finite index set before writing an ordinary integer sum.

Target: KV05.07.

### E05.03. Jacobi-function argument

**Confirmed.** §2.4, p. 233, below (16).
Comparing the definitions gives
\[
\varphi_\lambda^{(\alpha,\beta)}(t)
 =R_{(i\lambda-\alpha-\beta-1)/2}^{(\alpha,\beta)}(\cosh2t),
\]
not \(R_{\ldots}^{(\alpha,\beta)}(t)\).
The hypergeometric argument is \(-\sinh^2t=(1-\cosh2t)/2\).

Target: KV05.09.
The \(c\)-function constants themselves are consistent after gamma duplication;
they are not listed as an error.

### E05.04. Final Whittaker–Laguerre transform

**Confirmed internal mismatch; full correction open.** §2.5, p. 235.
The continuous kernel is \(W_{\kappa,i\rho}(x)\), but its displayed
discrete term has \(e^{-x^2/2}L_n^{2l+1}(x)\).
The Whittaker differential equation in variable \(x\) instead gives
Laguerre bound-state factors with \(e^{-x/2}\), not \(e^{-x^2/2}\).
For \(\kappa=-(n+\epsilon)\le1/2\), there are no such bound states,
while the printed sum does not impose the necessary finite condition.
The continuous gamma factor and constants also need rederivation.
No full repaired transform is claimed here.

Target: KV05.12.

## Chapter 6

### E06.01. Krawtchouk endpoint parameters

**Confirmed missing restriction.** §1.2, p. 236, after the orthogonality display.
The positive binomial-weight orthogonal basis requires \(0<p<1\).
At \(p=0\), the defining \(p^{-1}\) formula is undefined; at \(p=1\),
the measure has one-point support, so it cannot support \(N+1\)
nonzero orthogonal basis vectors for \(N>0\).
Endpoint degenerations require different statements.

Target: KV06.03.

### E06.02. Meixner radial coefficient sign

**Confirmed.** §1.3, p. 238, first two matrix-element displays.
With \(s=l-m,\ x=l-n,\ \gamma=-2l\), the hypergeometric coefficient
needs a factor \((-1)^s\) in the convention matching (18).
At \(s=x=1\), \(c=\tanh^2(t/2)\to0\),
\(M_1(1;\gamma,c)=\gamma+1-1/c\).
The printed diagonal matrix element tends to \(-1\) as \(t\to0\),
although the identity operator has diagonal \(1\).
The factor \((-1)^s\) repairs this test and the off-diagonal
skew-adjointness check. Orthogonality of the polynomial family is
unaffected by row phases.

Target: KV06.05; related E02.03.

### E06.03. Meixner degree recurrence

**Confirmed.** §1.3, p. 238, last display.
The coefficient \(s\gamma\) should be \(c\gamma\) in the source's
scaled normalization. At \(s=0,x=0\), \(M_0=1,M_1=\gamma\):
the printed left side is \(c\gamma\ne0\).
The corrected recurrence is in KV06.06.

### E06.04. Charlier matrix input index

**Confirmed.** §1.4, p. 239, (5).
The power of \(r^2\rho\) is printed \((m+k)/2\), but must be
\((n+k)/2\), with \(n\) the matrix input index.
The representation label \(m\) supplies a rotation phase and cannot
enter the displacement degree. Comparing Chapter 2, (33), fixes the index.

Target: KV06.07.

### E06.05. Krawtchouk–Meixner coefficient sum and complementary interval

**Confirmed typographical omissions.** §1.5, p. 241.
The expansion coefficient \(a_n\) must sum over the function variable \(x\),
not the fixed coefficient label \(n\).
The printed complementary-series interval \(1<\tau<1\) is empty.
A nonempty interval and an explicitly chosen invariant norm are required;
no corrected orthogonality statement for that series is guessed.

Target: KV06.08.

### E06.06. Hahn difference coefficient

**Confirmed.** §2.2, p. 244.
The factor \(x(N+\beta-n+1)\Delta\nabla\) must be
\(x(N+\beta-x+1)\Delta\nabla\).
For a quadratic \(Q_2\), substitution leaves a nonzero residual with
the printed coefficient; the corrected coefficient annihilates the
finite hypergeometric polynomial.

Target: KV06.12.

### E06.07. Hahn reflection prefactor

**Confirmed convention conflict.** §2.2, p. 244, first display.
The falling-factorial ratio does not yield the standard reflection
of the defined \(Q_n\). In rising-factorial notation the correct ratio is
\[
(-1)^n(\beta+1)_n/(\alpha+1)_n.
\]
The degree-one formula or evaluation at \(x=0,N\) checks it directly.
Falling-factorial notation must be converted before evaluating singular
gamma quotients.

Target: KV06.12.

### E06.08. Hahn-to-Meixner limit normalization

**Confirmed.** §2.2, p. 244, last limit formula.
The terminating series tends to the unscaled
\(\widetilde M_n=M_n/(\gamma)_n\), with \(\gamma=\beta\) in that display.
At \(x=0\), every Hahn polynomial equals \(1\), whereas the scaled
Meixner polynomial defined on p. 238 equals \((\gamma)_n\).

Target: KV06.12.

### E06.09. Meixner product and connection conventions

**Confirmed for the connection formula; product requires conversion.**
§2.4, p. 246.
The coefficient formulas use unscaled Meixner polynomials, whereas §1.3
defines \(M_n=(\gamma)_n\widetilde M_n\).
For the printed connection formula, set \(n=1\) and evaluate at \(x=0\);
the scaled convention does not give \(M_1(0)=\gamma\).
Converting both sides to the scaled convention gives KV06.15.
The preceding product coefficients must be converted with all three
degree-dependent factors, not only an overall constant.

Target: KV06.15.

### E06.10. Racah support condition

**Confirmed.** §2.5, p. 247.
Requiring all three negative denominator parameters to lie in
\(\{0,\ldots,n\}\) is not the usual finite-support condition and may
produce a zero denominator before degree \(n\).
Choose a support size \(N\), require at least one lower parameter
to be \(-N\), and take \(0\le n\le N\), excluding earlier
denominator zeros in the remaining parameters.
This preserves the finite terminating polynomial on \(\{0,\ldots,N\}\).

Target: KV06.16.

### E06.11. Final Charlier addition sign

**Confirmed.** §3.2, p. 248, final display.
Its prefactor \((-b)^{n+k}\) should be \((-1)^n b^{n+k}\).
It differs by \((-1)^k\). Multiply the valid product formula (25)
by the binomial Krawtchouk weight and use its orthogonality:
the inverse coefficient has exactly the latter sign.

An exact rational counterexample to the printed display is
\(a=2,b=3,n=k=1,x=2,y=1\).
The printed left side is \(2/5\); the right side is \(-2/5\).
The proposed corrected sign makes them agree.
Additional low-degree checks also agree with the orthogonality derivation.

Target: KV06.18.

## Verification scope

Page-image checks distinguish printed errors from OCR loss.
Exact finite-polynomial calculations check the corrected Meixner recurrence,
Hahn difference equation and norm, Hahn beta-integral identity, finite Jacobi
addition coefficients, Racah difference identities, and the Charlier product
and corrected addition examples. These checks supply evidence and detect
normalization errors; they do not replace proofs for the parameter families.

No Lean declarations or proofs are introduced by this inventory. Unresolved
kernel constants, contour conditions, and global normalization questions remain
explicitly identified above and in the corresponding synopsis entries.
