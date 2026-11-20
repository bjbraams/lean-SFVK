# Errata and source checks: Heckman–Schlichtkrull, Harmonic Analysis and Special Functions

Reference: G. Heckman and H. Schlichtkrull, *Harmonic Analysis and Special Functions on
Symmetric Spaces*, Perspectives in Mathematics 16, Academic Press (preface dated March 1994).
Part I (Heckman, *Hypergeometric and Spherical Functions*), Part II (Schlichtkrull,
*Semisimple Symmetric Spaces*), Part III (Heckman, *\(K\)-invariant Eisenstein Integrals*).
The local copy is in [References](References/).

Locators use printed page numbers. The pagination is continuous through the book, but the PDF
omits the title, contents and part-title pages. To get the one-based PDF page number, add 2 in
Part I (pp. 3–89), subtract 1 in Part II (pp. 93–188), and subtract 3 in Part III and the back
matter (pp. 191–226).

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

- the location, as part, chapter or lecture, section, printed page and equation (a line
  number, when given, is counted from the top of the page, negative from the bottom);
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries.

Synopsis entries cite errata by id. An erratum id \(\mathrm{HS}p\text{-}\mathrm Ecc.s.nn\) is the
\(nn\)-th erratum located in section \(s\) of chapter, lecture or section \(cc\) of part \(p\)
(\(s=0\) when the unit has no subdivisions or the item is at chapter level).

## Scope

These are observations about this edition, not an official publisher list; no published errata
list for this book is known to us. No claim is made that formulas without an erratum are free of
errors. Formulas that the synopsis marks "as printed" were transcribed from the page images
without an independent check. Corrected formulas in the synopsis are statements to be
formalized. They are not Lean proofs. Garbling of the PDF text layer is not an erratum; every
erratum was checked on the page image.

Each part ends with a list of conventions and notation that are not errata, for example a
normalization of an inner product that differs between parts.

## Summary by chapter

- Part I. Hypergeometric and Spherical Functions (G. Heckman): 171 entries, 10 errata (Confirmed 8, Normalization check 1, Open check 1).
- Part II. Semisimple Symmetric Spaces (H. Schlichtkrull): 125 entries, 8 errata (Confirmed 8).
- Part III. \(K\)-invariant Eisenstein Integrals (G. Heckman): 40 entries, 1 erratum (Confirmed 1).
- Total: 336 entries, 19 errata (Confirmed 17, Normalization check 1, Open check 1).

## Part I. Hypergeometric and Spherical Functions (G. Heckman)

### HS1-E01.2.01. Sign of the recurrence for the commutant of \(L(k)\)

Status: Confirmed.
Location: Part I, §1.2, p. 13, Lemma 1.2.7.
Printed: \([L(k),P]=0\) iff \((2\lambda+2\rho(k)+\mu,\mu)p_\mu(\lambda)=2\sum_{\alpha>0}k_\alpha
\sum_{j\ge1}\{(\lambda+\mu+j\alpha,\alpha)p_{\mu+j\alpha}(\lambda)-(\lambda,\alpha)
p_{\mu+j\alpha}(\lambda-j\alpha)\}\).
Correct: the right side has the opposite sign:
\((2\lambda+2\rho(k)+\mu,\mu)p_\mu(\lambda)=2\sum_{\alpha>0}k_\alpha\sum_{j\ge1}\{(\lambda,\alpha)
p_{\mu+j\alpha}(\lambda-j\alpha)-(\lambda+\mu+j\alpha,\alpha)p_{\mu+j\alpha}(\lambda)\}\).
Evidence: with \(P e^\lambda=\sum_\mu p_\mu(\lambda)e^{\lambda+\mu}\) and (1.2.16),
\(L(k)e^\nu=(\nu,\nu+2\rho(k))e^\nu+2\sum_{\alpha>0}k_\alpha\sum_{j\ge1}(\nu,\alpha)
e^{\nu-j\alpha}\),
the coefficient of \(e^{\lambda+\mu}\) in \([L(k),P]e^\lambda\) is
\((2\lambda+2\rho+\mu,\mu)p_\mu(\lambda)+2\sum k_\alpha\sum_j\{(\lambda+\mu+j\alpha,\alpha)
p_{\mu+j\alpha}(\lambda)-(\lambda,\alpha)p_{\mu+j\alpha}(\lambda-j\alpha)\}\), which must vanish.
Test case \(P=L(k)\) in rank one, \(R=\{\pm\alpha\}\), \(\rho=\frac k2\alpha\), \(\mu=-\alpha\):
\(p_0(\lambda)=(\lambda,\lambda+2\rho)\), \(p_{-\alpha}(\lambda)=2k(\lambda,\alpha)\). The left side
is \(-2k(\lambda,\alpha)\{2(\lambda,\alpha)+(k-1)(\alpha,\alpha)\}\); the corrected right side
gives \(2k(\lambda,\alpha)\{p_0(\lambda-\alpha)-p_0(\lambda)\}=-2k(\lambda,\alpha)\{2(\lambda,
\alpha)+(k-1)(\alpha,\alpha)\}\), equal to the left side, while the printed right side is its
negative.
Target: [HS1.01.2.11].

### HS1-E01.3.01. Normalization of the rank-one weight measure

Status: Normalization check.
Location: Part I, §1.3, p. 15, Example 1.3.2.
Printed: \(|\delta(k,t)|\,dt=\frac{2^{k_1+2k_2}}{2\pi}(1-x)^{k_1+k_2-\frac12}(1+x)^{k_2-\frac12}
dx\).
Correct: the image of \(|\delta(k,t)|\,dt\) (normalized Haar measure on \(T\)) under
\(t\mapsto x=\cos\theta\) is \(\frac{2^{k_1+2k_2}}{\pi}(1-x)^{k_1+k_2-\frac12}
(1+x)^{k_2-\frac12}dx\) on \([-1,1]\); the printed density is the image of the half-torus
\(0<\theta<\pi\) only.
Evidence: at \(k=0\) the printed density integrates to \(\frac1{2\pi}\int_{-1}^1(1-x^2)^{-1/2}dx
=\frac12\), whereas \(\int_T dt=1\). The map \(\theta\mapsto\cos\theta\) is two-to-one on
\(\mathbb R/2\pi\mathbb Z\). The identification with Jacobi polynomials "up to normalization" is
unaffected.
Target: [HS1.01.3.03].

### HS1-E02.1.01. Coupling constant of the Calogero–Moser operator

Status: Confirmed.
Location: Part I, §2.1, p. 23, (2.1.18), proof of Theorem 2.1.6.
Printed: \(g_\alpha^2=-\tfrac12k_\alpha(1-k_\alpha-k_{2\alpha})(\alpha,\alpha)\).
Correct: \(g_\alpha^2=-\tfrac12k_\alpha(1-k_\alpha-2k_{2\alpha})(\alpha,\alpha)\), so that
\(\delta(k)^{-\frac12}S(g)\delta(k)^{\frac12}=-\frac12\{L(k)+(\rho(k),\rho(k))\}\).
Evidence: Theorem 2.1.1 (2.1.9) has potential coefficient \(k_\alpha(1-k_\alpha-2k_{2\alpha})
(\alpha,\alpha)\); multiplying by \(-\frac12\) gives the corrected \(g_\alpha^2\). The factor 2 in
(2.1.9) was checked directly in type \(BC_1\) with \((\alpha,\alpha)=1\), coordinate \(t\),
\(\delta^{1/2}=(2\sinh\frac t2)^{k_1}(2\sinh t)^{k_2}\): \(\delta^{1/2}(L+(\frac{k_1}2+k_2)^2)
\delta^{-1/2}=\frac{d^2}{dt^2}+\frac{k_1(1-k_1-2k_2)}{4\sinh^2(t/2)}+\frac{k_2(1-k_2)}{\sinh^2t}\)
(symbolic simplification gives zero difference; numerically at \(t=0.7\), \(k_1=0.3\),
\(k_2=1.9\) on \(f=\cos3t\) the difference is \(<10^{-14}\)). The printed \(g_\alpha^2\) differs
when \(k_{2\alpha}\ne0\) (type \(BC_n\)), and then \(P\mapsto\delta^{-1/2}P\delta^{1/2}\) does not
carry the commutant of \(S(g)\) to \(\mathbb D(k)\).
Target: [HS1.02.1.05].

### HS1-E03.1.01. Sign of the recurrence for shift operators

Status: Confirmed.
Location: Part I, §3.1, p. 30, proof of Proposition 3.1.6.
Printed: \(D=\sum_{\mu\le0}e^{-\rho(l)+\mu}\partial_{p_\mu}\in\mathbb S(l,k)\) iff
\((2\lambda+2\rho(k)+\mu,\mu)p_\mu(\lambda)=2\sum_{\alpha>0}\sum_{j\ge1}\{(k_\alpha+l_\alpha)
(\lambda+\mu-\rho(l)+j\alpha,\alpha)p_{\mu+j\alpha}(\lambda)-k_\alpha(\lambda,\alpha)
p_{\mu+j\alpha}(\lambda-j\alpha)\}\).
Correct: the right side has the opposite sign,
\(2\sum_{\alpha>0}\sum_{j\ge1}\{k_\alpha(\lambda,\alpha)p_{\mu+j\alpha}(\lambda-j\alpha)-
(k_\alpha+l_\alpha)(\lambda+\mu-\rho(l)+j\alpha,\alpha)p_{\mu+j\alpha}(\lambda)\}\).
Evidence: comparing coefficients of \(e^{\lambda-\rho(l)+\mu}\) in
\(ML(k+l)De^\lambda\) and \(D\,ML(k)e^\lambda\), using \(ML(k)e^\nu=(\nu+\rho(k),\nu+\rho(k))e^\nu
+2\sum_{\alpha>0}k_\alpha\sum_{j\ge1}(\nu,\alpha)e^{\nu-j\alpha}\), gives
\(p_\mu(\lambda)(2\lambda+2\rho(k)+\mu,\mu)+2\sum\sum(k_\alpha+l_\alpha)(\lambda-\rho(l)+\mu+
j\alpha,\alpha)p_{\mu+j\alpha}(\lambda)=2\sum\sum k_\alpha(\lambda,\alpha)p_{\mu+j\alpha}
(\lambda-j\alpha)\). For \(l=0\) this is the corrected Lemma 1.2.7, and the rank-one test
\(D=ML(k)\), \(\mu=-\alpha\) of [HS1-E01.2.01] again shows that the printed sign gives the
negative of the left side.
Target: [HS1.03.1.09].

### HS1-E04.1.01. Definition of harmonic differential operators reversed

Status: Confirmed.
Location: Part I, §4.1, p. 51, definition before (4.1.2).
Printed: \(\partial_q\in U\mathfrak h\) is harmonic if \(\partial_q(p)=0\) for all \(W\)-invariant
polynomials \(p\) with \(p(0)=0\).
Correct: \(\partial_q\) is harmonic if \(\partial_p(q)=0\) for all \(W\)-invariant \(p\in
S\mathfrak h\)
with \(p(0)=0\) (the invariant operators annihilate \(q\)).
Evidence: under the printed condition no nonzero \(q\) is harmonic. For \(R\) of type \(A_1\),
\(\mathfrak h=\mathbb C\), \(W=\{\pm1\}\), the invariants of positive degree include
\(p=x^{2m}\) for all \(m\ge1\), and \(q(d/dx)x^{2m}\ne0\) for \(m\) large unless \(q=0\); so the
printed harmonics are \(\{0\}\), contradicting \(\dim H\mathfrak h=|W|=2\) and the choice
\(q_1\equiv1\) in Definition 4.1.4 (\(\partial_1(p)=p\ne0\)). With the corrected condition the
harmonics for \(A_1\) are \(\mathrm{span}\{1,x\}\).
Target: [HS1.04.1.02].

### HS1-E04.3.01. Braid exponents \(m_{ij}\)

Status: Confirmed.
Location: Part I, §4.3, p. 60, Theorem 4.3.2 (after (4.3.6)) and Remark 4.3.4 (after (4.3.11)).
Printed: "\(m_{ij}=(\alpha_i,\alpha_j^\vee)(\alpha_i^\vee,\alpha_j)\) is the order of
\(r_ir_j\in W\)", with \(m_{ij}\) factors on both sides of the braid relations.
Correct: \(m_{ij}\) is the order of \(r_ir_j\), which is \(2,3,4,6\) according as
\((\alpha_i,\alpha_j^\vee)(\alpha_i^\vee,\alpha_j)=0,1,2,3\) (and \(\infty\) for the affine
\(A_1\) case, product 4, in Remark 4.3.4).
Evidence: the product of Cartan integers and the order of \(r_ir_j\) differ in every case. For
type \(A_2\) the product is 1 while \(r_1r_2\) has order 3 and the braid relation is
\(g_1g_2g_1=g_2g_1g_2\); for orthogonal simple roots the product is 0 while the relation is
\(g_ig_j=g_jg_i\) (2 factors). With \(m_{ij}=0\) or 1 the printed relation would be empty or
\(g_i=g_j\).
Target: [HS1.04.3.02], [HS1.04.3.04].

### HS1-E04.3.02. Relations between \(g_j\) and the translations \(l_x\)

Status: Confirmed.
Location: Part I, §4.3, p. 60, (4.3.6) and (4.3.9).
Printed: \(g_il_j=l_jl_i^{r+1}g_il_i^{-r}\) if \(n_{ij}=-(2r+1)\) is odd (4.3.6), and
\(g_jl_{r_j(x)}=l_xg_j\) if \((x,\alpha_j)=1\) (4.3.9).
Correct: \(g_jl_{r_j(x)}g_j=l_x\) if \((x,\alpha_j)=1\), and correspondingly
\(g_il_j=l_jl_i^{r+1}g_i^{-1}l_i^{-r}\) for odd \(n_{ij}=-(2r+1)\) (take
\(x=\alpha_j^\vee+(r+1)\alpha_i^\vee\)). This is the form used in the proof of Proposition 4.3.5,
\(l_xg_jl_{-x}=l_xl_{-r_j(x)}g_j^{-1}\), and it is the braid-group form of the Bernstein–Lusztig
relation \(T_s\theta_{s(x)}T_s=\theta_x\).
Evidence: the printed relation is incompatible with the monodromy representation for generic
\(k\). Let \(\alpha_j(Q^\vee)=\mathbb Z\) (so \(k_{\frac12\alpha_j}=0\)), \((x,\alpha_j)=1\),
\(\lambda\) generic, and \(V_w=\mathrm{span}\{\Phi(w\lambda),\Phi(r_jw\lambda)\}\), which is
\(M(g_j)\)-stable (4.3.15). By (4.3.14), \(M(l_x)|_{V_w}=\mathrm{diag}(a,b)\) and
\(M(l_{r_j(x)})|_{V_w}=q\,\mathrm{diag}(b,a)\) with \(q=e^{2\pi i(\rho(k),\alpha_j^\vee)}=
e^{2\pi ik_{\alpha_j}}\) (since \(\rho(k)-r_j\rho(k)=k_{\alpha_j}\alpha_j\)). Taking determinants
in the printed \(Gq\,\mathrm{diag}(b,a)=\mathrm{diag}(a,b)G\) gives \(q^2=1\), false for generic
\(k\). The corrected relation gives \(\det(G)^2q^2=1\), i.e. \(\det M(g_j)|_{V_w}=-q^{-1}\),
which matches the eigenvalues \(1,-e^{-2\pi ik_{\alpha_j}}\) found for the orientation of
(4.3.1) in [HS1-E04.3.04]; with the printed eigenvalue \(-e^{2\pi ik_{\alpha_j}}\) the compatible
form would instead be \(g_j^{-1}l_{r_j(x)}g_j^{-1}=l_x\). Either way the printed relations are
impossible. Type \(A_2\) has such \(x\): \(x=-\alpha_2^\vee\), \((x,\alpha_1)=1\).
Target: [HS1.04.3.02], [HS1.04.3.03].

### HS1-E04.3.03. Quotient of the two weights in the proof of Corollary 4.3.7

Status: Confirmed.
Location: Part I, §4.3, p. 63, (4.3.21).
Printed: \(\delta(k';a)^{-\frac12}\delta(k;a)^{\frac12}=\Delta(a)\delta(k;a)\).
Correct: \(\delta(k';a)^{-\frac12}\delta(k;a)^{\frac12}=\Delta(a)^{-1}\delta(k;a)\).
Evidence: \(k-k'\) equals \(2k_\alpha-1\) on \(R^0\) and \(2k_\alpha\) on \(R\cap\frac12R\), so
\(\delta(k)^{1/2}/\delta(k')^{1/2}=\delta(2k)^{1/2}\prod_{\alpha\in R^0_+}(e^{\frac12\alpha}-
e^{-\frac12\alpha})^{-1}=\delta(k)\Delta^{-1}\). In type \(A_1\): \(\delta(k)^{1/2}=s^k\),
\(\delta(k')^{1/2}=s^{1-k}\) (\(s=e^{\frac12\alpha}-e^{-\frac12\alpha}\)), quotient \(s^{2k-1}=
\delta(k)\Delta^{-1}\), not \(s^{2k+1}\). The monodromy factor \(-e^{\mp2\pi i(\dots)}\) along
\(g_j\) is the same for both, so the conclusion of Corollary 4.3.7 is unaffected.
Target: [HS1.04.3.08].

### HS1-E04.3.04. Orientation of the loops \(g_j\) and the sign in the Hecke eigenvalue

Status: Open check.
Location: Part I, §4.3, pp. 62–63, Corollary 4.3.7, (4.3.22)–(4.3.23) and their proof.
Printed: \(M(\lambda,k)(g_j)\) has eigenvalues \(1\) and \(-e^{2\pi i(k_{\frac12\alpha_j}+
k_{\alpha_j})}\), and \((M(l_jg_j^{-1})-1)(M(l_jg_j^{-1})+e^{2\pi ik_{\alpha_j}})=0\); the proof
states that in the rank-one reduction \(g_j\) goes once around \(z=0\) in the negative direction.
Correct (conjectured): for the path (4.3.1) with \(\varepsilon\ge0\), \(g_j\) goes around
\(z=0\) in the positive direction, so the eigenvalue is \(-e^{-2\pi i(k_{\frac12\alpha_j}+
k_{\alpha_j})}\) and (4.3.22)–(4.3.23) hold with \(e^{-2\pi i(\cdot)}\) in place of
\(e^{2\pi i(\cdot)}\). The question is whether an unstated convention (orientation, or the branch
of \(z^{1-c}\)) reverses this.
Evidence: in rank one (\(R_+=\{\frac12\alpha,\alpha\}\)) with \(u=e^{\frac12\alpha}\) and
\(u(a_0)=e^s\), \(s>0\), the path \(G_j\) of (4.3.1) is \(u(t)=e^{(1-2t)s}e^{2\pi
i\varepsilon(t)}\). For \(s=1\),
\(\varepsilon(t)=\frac14\sin\pi t\), \(z=\frac12-\frac14(u+u^{-1})\) takes the values
\(-0.27\), \(0.25-0.23i\), \(0.5\), \(0.25+0.23i\), \(-0.27\) at \(t=0,\frac14,\frac12,\frac34,1\):
one counterclockwise turn about \(z=0\). With local exponents \(0,1-c\),
\(1-c=\frac12-k_{\frac12\alpha}-k_\alpha\), a positive turn multiplies \(z^{1-c}\) by
\(e^{2\pi i(1-c)}=-e^{-2\pi i(k_{\frac12\alpha}+k_\alpha)}\). This sign is also the one compatible
with (4.3.14) and the corrected relation of [HS1-E04.3.02] (\(\det M(g_j)|_{V_w}=-q^{-1}\)). The
conclusion that the monodromy factors through an affine Hecke algebra is unaffected.
Target: [HS1.04.3.08], [HS1.04.3.09].

### HS1-E05.3.01. Power of \(\sqrt2\) in the Cayley transform of \(v_0\)

Status: Confirmed.
Location: Part I, §5.3, p. 82, (5.3.4).
Printed: \(c(v_0)=\big(\tfrac1{\sqrt2}\big)^2\exp(iy)v_0=\big(\tfrac1{\sqrt2}\big)^l(v_0+iv_1+
\dots+i^lv_l)\).
Correct: \(c(v_0)=\big(\tfrac1{\sqrt2}\big)^l\exp(iy)v_0\).
Evidence: in the factorization \(c=\exp(iy)\,\mathrm{diag}(2^{-1/2},2^{1/2})\exp(ix)\),
\(\exp(ix)v_0=v_0\) and \(\mathrm{diag}(2^{-1/2},2^{1/2})=\exp(-\frac12\log2\cdot h)\) acts on
\(v_0\) (weight \(l\)) by \(2^{-l/2}\); \(\exp(iy)v_0=\sum_ji^jv_j\). For \(l=1\) (\(V(1)=
\mathbb C^2\), \(v_0=e_1\), \(v_1=e_2\)): \(ce_1=\frac1{\sqrt2}(e_1+ie_2)\), whereas the middle
expression gives \(\frac12(e_1+ie_2)\). Only the right-hand expression is used in (5.3.5).
Target: [HS1.05.3.03].

### Conventions and notation (not errata)

- Two multiplicity notations: the book's \(k\) is half the geometric multiplicity after
  replacing \(\Sigma\) by \(R=2\Sigma\): \(k_{2\alpha}=\frac12m(\alpha)\) (Notation 5.1.3).
- \(\overline F\) on \(\mathbb R[P]\) (1.1.9) is the involution \(e^\lambda\mapsto e^{-\lambda}\),
  which is complex conjugation of the function on \(T\); the inner product (1.1.11) uses it.
  Haar measure \(dt\) on \(T\) is normalized, so \(|P(\lambda,k)|_k^2\) carries the factor
  \(|W|\) in (3.5.7) and \(\int_T|\delta(0,t)|dt=1\).
- The Dunkl-type operators \(D_\xi\) use \(\Delta_\alpha\) (1.1.3), not \(A_\alpha\); the source
  sums over \(R_+\) with factor \(\frac12\).
- In the proof of Theorem 4.3.6 the symbols \(c(\lambda,k)\) and \(\Phi(\lambda,k;z)\) (rank one,
  with \(a=(\lambda+\rho(k),\alpha^\vee)\)) equal \(c(-\lambda,k)\) of (3.4.3) and
  \(\Phi(-\lambda,k;a)\) of (4.2.4): the term \(2^{-2a}(-z)^{-a}F(\cdots)\) has leading exponent
  \(-\lambda-\rho(k)\), and \(2^{2a}\Gamma(c)\Gamma(b-a)/(\Gamma(b)\Gamma(c-a))=\tilde c(-\lambda,
  k)/\tilde c(\rho(k),k)\) (checked via the duplication formula). Kummer's identity (4.3.17) is
  symmetric in \(\pm\lambda\), so it holds in either labelling.
- In the proof of Theorem 4.3.11 "Proposition (4.3.25)" refers to Proposition 4.3.10.
- The rank-one constants \(k_2-\frac12\) in \(E_+\) and \(k_1+k_2-\frac12\) in \(E_-\)
  (Proposition 3.3.1) are as printed and correct (checked symbolically); the PDF text layer
  garbles the fractions.
- §5.5: the outline assumes \(|l|\le k_s+1\) (p. 86), while Corollary 5.5.3 (standardness of
  \(m_-\)) and Conclusion 5.5.5 use \(|l|<k_s+1\). At \(|l|=k_s+1\) the long-root pole of
  \(1/c(-\lambda,m_-)\) at \((\lambda,\alpha^\vee)=0\) is cancelled by the zero of the short-root
  factor, so the boundary case may also be covered; the synopsis states the results for
  \(|l|<k_s+1\), as in Conclusion 5.5.5. For \(k_s=0\) (type \(C_n\) regarded as \(BC_n\)) the
  short roots carry multiplicity zero and are omitted from the standardness condition.
- In Corollary 5.5.6 the domain "\(C_c^\infty(C)\)" means the \(\chi_l\)-spherical functions with
  support in \(KCK\), and the target is the \(W\)-invariant part of \(\mathcal P_C(\mathfrak h^*)\).

## Part II. Semisimple Symmetric Spaces (H. Schlichtkrull)

### HS2-E03.0.01. Restrictions of an arbitrary positive system need not form a positive system

Status: Confirmed.
Location: Part II, Lecture 3, p. 114, proof of Lemma 3.1.
Printed: "Given a positive set \(\Sigma^+(\mathfrak a_0,\mathfrak g)\), the set of its nonzero
restrictions to \(\mathfrak a_q\) is a positive set."
Correct: this holds for positive systems \(\Sigma^+(\mathfrak a_0,\mathfrak g)\) compatible with
\(\mathfrak a_q\) (defined by an ordering in which \(\mathfrak a_q\) comes first, so that a root with
positive nonzero restriction is positive); for an arbitrary positive system it fails. The lemma
itself is unaffected when such a compatible system is used.
Evidence: for \(X_{p,q}=SO_e(p,q)/SO_e(p-1,q)\) with \(p\ge q=2\), take \(\mathfrak a_q=\mathbb RY\),
\(Y=E_{p+q,1}+E_{1,p+q}\), and \(\mathfrak a_0=\mathrm{span}(Y,Y_2)\) with
\(Y_2=E_{p+q-1,2}+E_{2,p+q-1}\); \(\mathfrak a_0\) is maximal abelian in \(\mathfrak p\), and \(\Sigma(\mathfrak a_0,\mathfrak g)\) is of type
\(B_2\) (\(p>2\)) or \(D_2\) (\(p=2\)), containing \(\pm e_1\pm e_2\) in the dual basis; and restriction to \(\mathfrak a_q\) is
\((x,y)\mapsto x\). The positive system defined by a regular element \((x_0,y_0)\) with
\(y_0>x_0>0\) contains \(e_2+e_1\) and \(e_2-e_1\), whose restrictions are \(e_1\) and \(-e_1\); a
positive set cannot contain both.
Target: [HS2.03.0.03].

### HS2-E05.0.01. Convergence condition for the standard intertwining integral

Status: Confirmed.
Location: Part II, Lecture 5, p. 144, Proposition 5.5.
Printed: the integral converges when \(\langle\mathrm{Re}\,\lambda,\alpha\rangle>0\) for all
\(\alpha\in\Sigma^+(\mathfrak a_q,\mathfrak g)\) "such that \(\mathfrak g^\alpha\subset\bar{\mathfrak n}
\cap\mathfrak n'\)".
Correct: the condition runs over the \(\alpha\in\Sigma^+(\mathfrak a_q,\mathfrak g)\) with
\(\mathfrak g_{-\alpha}\subset\bar{\mathfrak n}\cap\mathfrak n'\).
Evidence: for \(\alpha\in\Sigma^+(\mathfrak a_q,\mathfrak g)\), \(\mathfrak g_\alpha\subset\mathfrak n\),
and \(\mathfrak n\cap\bar{\mathfrak n}=0\), so the printed index set is empty and the proposition
would assert convergence for every \(\lambda\). In the case \(H=K\), \(P'=\bar P\), the integral
is Harish-Chandra's \(c\)-function integral \(\int_{\bar N}e^{(-\lambda-\rho)H(\bar n)}d\bar n\), which
converges exactly on a region of the form \(\langle\mathrm{Re}\,\lambda,\alpha\rangle>0\) for all
\(\alpha>0\) (p. 157), in accordance with the corrected condition (here \(\bar{\mathfrak n}\cap
\mathfrak n'=\bar{\mathfrak n}\) contains every \(\mathfrak g_{-\alpha}\)).
Target: [HS2.05.0.16].

### HS2-E06.0.01. Continuity of the functions \(f_\lambda\) on the hyperbolic space

Status: Confirmed.
Location: Part II, Lecture 6, p. 147, Example 6.2.
Printed: for \(p>1\), \(f_\lambda\) is continuous "iff \(\mathrm{Re}\,\lambda+\rho\le0\)".
Correct: \(f_\lambda\) is continuous iff \(\mathrm{Re}\,\lambda+\rho<0\), or \(\lambda+\rho=0\) and
\(i=0\).
Evidence: \(f_\lambda\) is homogeneous of the form \(|x_1|^{-\lambda-\rho}\) (times
\(\mathrm{sign}(x_1)^i\)) near \(x_1=0\). For \(\lambda=-\rho+i\tau\), \(\tau\ne0\), real, the factor
\(|x_1|^{-i\tau}\) has no limit at \(x_1=0\); for \(\lambda=-\rho\) and \(i=1\) the function is
\(\mathrm{sign}(x_1)\), discontinuous on \(x_1=0\).
Target: [HS2.06.0.03].

### HS2-E06.0.02. Homogeneity of \(H\)-fixed distributions supported on \(x_1=0\)

Status: Confirmed.
Location: Part II, Lecture 6, p. 151, Example 6.4 (proof of Theorem 6.3 in this case).
Printed: the homogeneity "forces \(P(v)=v^{-\lambda-\rho}\)", so "\(-\lambda-\rho\) has to be a
nonnegative integer" for such a distribution to exist.
Correct: a distribution of the form \(P(\partial)\delta(x_1)\) with \(\delta^{(m)}(x_1)\) has
homogeneity \(-1-m\); matching homogeneity \(-\lambda-\rho\) gives \(\lambda+\rho=m+1\in\{1,2,\dots\}\),
with \(m\equiv i\pmod 2\).
Evidence: by (6.2) the family \(f_\lambda\) has a pole at \(\lambda=1-\rho\) (pole of
\(B(\frac12(1-\lambda-\rho),\frac12(p-1))\)), and its residue is a nonzero multiple of
\(\delta(x_1)\), an \(H\)-fixed distribution supported on \(x_1=0\); here \(-\lambda-\rho=-1\), which
is not a nonnegative integer. Conversely at \(\lambda=-\rho\) (\(-\lambda-\rho=0\)) no nonzero
distribution supported on \(x_1=0\) has homogeneity \(0\).
Target: [HS2.06.0.08].

### HS2-E07.0.01. The potential term in (7.14)

Status: Confirmed.
Location: Part II, Lecture 7, p. 166, (7.14).
Printed: \(\tilde\Phi''-d''\tilde\Phi=(\lambda^2-\rho^2)\tilde\Phi\), with \(d=J^{-1/2}(J^{1/2})''\).
Correct: \(\tilde\Phi''-d\,\tilde\Phi=(\lambda^2-\rho^2)\tilde\Phi\).
Evidence: (7.13) gives \(J^{1/2}\Pi(L)\Phi=(J^{1/2}\Phi)''-(J^{1/2})''\Phi=\tilde\Phi''-d\tilde\Phi\);
\(d\) already contains the second derivative.
Target: [HS2.07.0.16].

### HS2-E07.0.02. Expansion of the potential \(d\)

Status: Confirmed.
Location: Part II, Lecture 7, p. 166, expansion of \(d\) after (7.14), and the recursion for
\(\tilde\Gamma_m\).
Printed: \(d(t)=\sum_{n=0}^\infty d_ne^{-nt}\), \(d_0=\rho^2\),
\(d_n=((q-1)(q-3)+(-1)^n(p-1)(p-3))n\); recursion \(m(m-2\lambda)\tilde\Gamma_m=\sum_{n=1}^m
d_n\tilde\Gamma_{m-n}\).
Correct: \(d(t)=\rho^2+\sum_{n\ge1}d_ne^{-2nt}\) with the printed \(d_n\), and
\(m(m-2\lambda)\tilde\Gamma_m=\sum_{1\le n\le m/2}d_n\tilde\Gamma_{m-2n}\); hence
\(\tilde\Gamma_m=0\) for odd \(m\). The bound \(|d_n|\le c_0n\) and the estimate (7.15) are unaffected.
Evidence: with \(a=\frac12(p-1)\), \(b=\frac12(q-1)\), \(J^{1/2}=\cosh^at\sinh^bt\),
\(d=(a+b)^2+(a-a^2)\,\mathrm{sech}^2t+(b^2-b)\,\mathrm{csch}^2t\). Expanding
\(\mathrm{sech}^2t=4\sum_{n\ge1}(-1)^{n-1}ne^{-2nt}\) and \(\mathrm{csch}^2t=4\sum_{n\ge1}ne^{-2nt}\)
gives \(d_n=4n\{(b^2-b)-(-1)^n(a-a^2)\}=n\{(q-1)(q-3)+(-1)^n(p-1)(p-3)\}\) as coefficient of
\(e^{-2nt}\). At \(p=5\), \(q=3\), \(t=3\): \(d(3)=8.980268\), the \(e^{-2nt}\) series gives
\(8.980268\), the printed \(e^{-nt}\) series gives \(8.638587\).
Target: [HS2.07.0.16].

### HS2-E08.0.01. Missing factor \(2^{2\lambda}\) in \(C^\circ_-(\lambda)\)

Status: Confirmed.
Location: Part II, Lecture 8, p. 172, Example 8.1, formula for \(C^\circ_-(\lambda)\).
Printed: \(C^\circ_-(\lambda)=\dfrac{\Gamma(\frac12(\rho+\lambda))\Gamma(-\lambda)\Gamma(\frac12(q-\rho+
\lambda))}{\Gamma(\frac12(\rho-\lambda))\Gamma(\lambda)\Gamma(\frac12(q-\rho-\lambda))}\).
Correct: \(C^\circ_-(\lambda)=2^{2\lambda}\dfrac{\Gamma(\frac12(\rho+\lambda))\Gamma(-\lambda)
\Gamma(\frac12(q-\rho+\lambda))}{\Gamma(\frac12(\rho-\lambda))\Gamma(\lambda)\Gamma(\frac12(q-\rho-
\lambda))}\).
Evidence: \(E^\circ(\lambda)=2^{\lambda-\rho}\frac{\Gamma(\frac12(\lambda+\rho))\Gamma(\frac12(\lambda-
\rho+q))}{\Gamma(\lambda)\Gamma(\frac12q)}F(a,b;c;-\sinh^2t)\); in (8.4) the \((-z)^{-a}\)-term is
\(\sinh^{-\lambda-\rho}t=2^{\lambda+\rho}(2\sinh t)^{-\lambda-\rho}\), and comparison with
\(\Phi_{-\lambda}=(2\sinh t)^{-\lambda-\rho}F(\dots)\) of (8.5) gives the coefficient
\(2^{\lambda-\rho}\cdot2^{\lambda+\rho}=2^{2\lambda}\) times the printed Gamma ratio. Numerically, at
\(p=5\), \(q=3\), \(\lambda=0.37+0.21i\), the coefficient of \(\Phi_{-\lambda}\) obtained from
\(E^\circ(\lambda)-\Phi_\lambda\) at \(t=1\) and at \(t=2.5\) is \(1.857143+0.952381i\), while the
printed formula gives \(1.228827+0.227076i\); \(2^{2\lambda}\) times the printed value agrees. The
factor has modulus one on \(i\mathbb R\) and cancels in (7.12), so the unitarity check in the source
does not detect it.
Target: [HS2.08.0.05].

### HS2-E08.0.02. Conjugation in the adjoint rule of Lemma 8.3

Status: Confirmed.
Location: Part II, Lecture 8, pp. 174–175, definition of \(v^*\) before (8.12), and the proof of
Lemma 8.3.
Printed: \(v^*(\lambda)=v(-\lambda)\) for \(v\in S(\mathfrak a_q)\), and \(D^*=r(\check u)\) for
\(D=r(u)\).
Correct: for the formal adjoint with respect to \(\langle f_1|f_2\rangle=\int f_1\bar f_2\),
\(v^*(\lambda)=\overline{v(-\bar\lambda)}\) and \(D^*=r(\overline{\check u})\), the bar being the
conjugation of \(U(\mathfrak g)\) with respect to the real form \(\mathfrak g\). With this \(v^*\),
\(\gamma_q(D^*)=\gamma_q(D)^*\) and (8.12) hold. The printed rules are correct for \(D\) with real
coefficients (or for the transpose with respect to the bilinear pairing).
Evidence: take \(D=iL\) (\(L\) the Laplace–Beltrami operator, formally self-adjoint). Then
\(D^*=-iL\) and \(\gamma_q(D^*)(\lambda)=-i(\langle\lambda,\lambda\rangle-\langle\rho,\rho\rangle)\),
whereas the printed rule gives \(\gamma_q(D)(-\lambda)=i(\langle\lambda,\lambda\rangle-
\langle\rho,\rho\rangle)\).
Target: [HS2.08.0.09].

### Conventions and notation (not errata)

- Throughout the OCR text of Part II, \(\rho\) is rendered as "p"; the page images have \(\rho\).
- Example 7.3 (p. 159) writes \(\mathfrak a_0^*\) for the integration domain of the
  spectral parameter where \(i\mathfrak a_0^*\) is meant; [HS2.07.0.06] uses \(i\mathfrak a_0^*\).
- Example 8.1 (p. 172) says "if \(p<q+2\) there are no poles" with positive real part; the poles
  with positive real part are \(\lambda_j=\rho-q-2j>0\), so there are none iff \(p\le q+2\)
  (at \(p=q+2\), \(\lambda_0=0\) is not of positive real part and is cancelled by
  \(1/\Gamma(\lambda)\)); [HS2.08.0.03] states this precise form.
- In (8.23) (p. 180) the residue term carries \(2\pi i|W|\), which corresponds to reading
  \(d\lambda\) as the complex line element on \(i\mathbb R\); with Lebesgue measure
  \(d(\mathrm{Im}\,\lambda)\) the factor is \(2\pi|W|\) up to orientation. The measure is only
  "suitably normalized" in the source; see [HS2.08.0.17].
- "Gauss summation formula" on p. 182 refers to the Gauss hypergeometric series, not to Gauss's
  evaluation of \(F(a,b;c;1)\).
- The notes to the lectures (pp. 183–188) are bibliographical and were not checked.

## Part III. \(K\)-invariant Eisenstein Integrals (G. Heckman)

### HS3-E04.0.01. Exponents at \(x=1\) in the rank one scheme

Status: Confirmed.
Location: Part III, Section 4, p. 205, table of exponents, \(x\)-variable, column \(1\).
Printed: exponents \(0,\ 1-k\) at \(x=1\).
Correct: exponents \(0,\ 1-2k\) at \(x=1\) (the same as at \(x=-1\)).
Evidence: \(2-4y=x+x^{-1}\) has critical points \(x=\pm1\), lying over \(y=0\) (\(x=1\)) and \(y=1\)
(\(x=-1\)), each with ramification index 2, so the exponents there are twice those at \(y=0\) and
\(y=1\), which are \(0,\frac12-k\) in the table; this gives \(0,1-2k\) at both points, as printed for
\(x=-1\). Fuchs' relation for a second-order equation with four singular points on
\(\mathbb P^1\) requires the exponents to sum to \(4-2=2\): the corrected \(x\)-row gives
\((1-2k)+2k+(1-2k)+2k=2\), the printed row gives \(2+k\). The \(y\)-row (three points, sum \(1\))
and the \(z\)-row (sum \(1\)) are consistent.
Target: [HS3.04.0.01].

### Conventions and notation (not errata)

- Section 4 (p. 207) refers to "Conjecture 3.9" and writes \(\mathcal H\) for the most continuous
  part; Conjecture 3.11 and \(L^2_{mc}\) are meant. [HS3.04.0.04] uses the latter.
- The header of the book lists Part III as pp. 191–207, but Question 5.4 ends on p. 208.
- In Section 3 the letter \(H\) is the complex torus and \(K\) the space of multiplicities, while
  in Section 2 they are subgroups of \(U\); see the Part III conventions of the synopsis.
- (2.13) is a product over all of \(R\) with exponent \(k_\alpha\), equivalent to a product over
  \(R_+\) with exponent \(2k_\alpha\) as in (3.10).
