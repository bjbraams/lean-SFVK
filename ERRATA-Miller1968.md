# Errata and source checks: Miller (1968), Lie Theory and Special Functions

Reference: Willard Miller, Jr., *Lie Theory and Special Functions*, Mathematics in Science and
Engineering 43, Academic Press, New York and London, 1968. The local copy is
[References/Miller1968LieTheorySpecialFunctions-ElsevierMSE43.pdf](References/Miller1968LieTheorySpecialFunctions-ElsevierMSE43.pdf).

Locators use printed page numbers. To get the one-based PDF page number, add 6 (throughout the
book). Line numbers, where given, count from the top of the page; negative line numbers count
from the bottom. Equation numbers \((c.n)\) are the source's chapter-wise numbers.

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

- the location, as chapter section, printed page, line and equation;
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries.

Synopsis entries cite errata by id. An erratum id \(\mathrm{M68\text{-}E}cc.s.nn\) is the
\(nn\)-th erratum located in section \(c\)-\(s\) of chapter \(cc\) (two-digit chapter number;
\(s=0\) for the chapter introduction).

## Scope

These are observations about this edition, not an official publisher list. No claim is made
that formulas without an erratum are free of errors. Formulas that the synopsis marks "as
printed" were transcribed from the page images without an independent check. Corrected
formulas in the synopsis are statements to be formalized. They are not Lean proofs.
Garbling of the PDF text layer is not an erratum; every printed formula quoted here was read
on the page image.

Each chapter section ends with a list of conventions and notation that are not errata, for
example a sign or normalization convention that differs from a modern reference.

## Summary by chapter

- Chapter 1. Résumé of Lie Theory: 24 entries, 7 errata (Confirmed 7).
- Chapter 2. Representations and Realizations of Lie Algebras: 27 entries, 6 errata (Confirmed 6).
- Chapter 3. Lie Theory and Bessel Functions: 31 entries, 4 errata (Confirmed 4).
- Chapter 4. Lie Theory and Confluent Hypergeometric Functions: 77 entries, 11 errata (Confirmed 11).
- Chapter 5. Lie Theory and Hypergeometric Functions: 75 entries, 11 errata (Confirmed 11).
- Chapter 6. Special Functions Related to the Euclidean Group in 3-Space: 16 entries, 4 errata (Confirmed 4).
- Chapter 7. The Factorization Method: 7 entries, 2 errata (Confirmed 2).
- Chapter 8. Generalized Lie Derivatives: 13 entries, 1 erratum (Confirmed 1).
- Chapter 9. Some Generalizations: 17 entries, 8 errata (Confirmed 8).
- Total: 287 entries, 54 errata (Confirmed 54).

## Chapter 1. Résumé of Lie Theory

### M68-E01.1.01. The commutator curve is not analytic in \(t=\tau^2\)

Status: Confirmed.
Location: §1-1, p. 3, (1.3)–(1.4).
Printed: the commutator \([\alpha,\beta]\) is "the tangent vector at \(e\) of the analytic curve
\(k(t)=g(\tau)h(\tau)g^{-1}(\tau)h^{-1}(\tau)\), \(t=\tau^2\)".
Correct: \(k\) is an analytic function of \(\tau\), with \(k(\tau)=e+\tau^2[\alpha,\beta]+O(\tau^3)\);
in general it is not an analytic (or even single-valued) function of \(t=\tau^2\). The bracket is
\([\alpha,\beta]=\lim_{\tau\to0}\tau^{-2}(k(\tau)-e)\), which is what (1.4) computes.
Evidence: in \(GL(2)\) take \(g(\tau)=e^{\tau X}\), \(h(\tau)=e^{\tau Y}\) with
\(X=\mathrm{diag}(1,0)\), \(Y=E_{12}\). Then \(e^{\tau X}Ye^{-\tau X}=e^\tau Y\) and
\(k(\tau)=I+\tau(e^\tau-1)Y=I+(\tau^2+\tfrac12\tau^3+\cdots)Y\), which contains the odd power
\(\tau^3\) and so is not a power series in \(\tau^2\).
Target: [M68.01.1.03].

### M68-E01.2.01. Entry of the adjoint action on \(\mathfrak{sl}(2)\)

Status: Confirmed.
Location: §1-2, p. 8, (1.25), entry (2,2).
Printed: \(\frac{-ad-bc}2x_3+bcx_2-acx_1\).
Correct: \(-\frac{ad+bc}2x_3+bdx_2-acx_1\) (the negative of the (1,1) entry, since
\(g\alpha g^{-1}\) has trace zero).
Evidence: direct computation of \(g\alpha g^{-1}\) with \(g^{-1}=\begin{pmatrix}d&-b\\-c&a
\end{pmatrix}\). For \(x_1=x_3=0\),
\(x_2=1\), \(g=\begin{pmatrix}1&1\\0&1\end{pmatrix}\): \(\alpha=\begin{pmatrix}0&0\\-1&0
\end{pmatrix}\), \(g\alpha g^{-1}=\begin{pmatrix}-1&1\\-1&1\end{pmatrix}\), whose (2,2) entry is
\(1=bd\), while the printed formula gives \(bc=0\). The other three printed entries agree with
the computation.
Target: [M68.01.2.03].

### M68-E01.2.02. The exponential map of \(G(0,1)\) is not a global diffeomorphism

Status: Confirmed.
Location: §1-2, p. 10, after (1.32).
Printed: \(\exp\alpha=e^\alpha\) "is an analytic diffeomorphism mapping all of \(L[G(0,1)]\) onto
\(G(0,1)\)".
Correct: \(\exp\) is an analytic diffeomorphism of a neighborhood of \(0\) onto a neighborhood
of \(e\) (Theorem 1.4); globally it is neither injective nor surjective.
Evidence: for \(\alpha=x_1\mathcal J^++x_2\mathcal J^-+x_3\mathcal J^3+x_4\mathcal E\),
\(e^\alpha=g(a,b,c,\tau)\) with \(\tau=x_3\), \(b=x_1(e^{x_3}-1)/x_3\),
\(ce^\tau=x_2(e^{x_3}-1)/x_3\), \(a=x_4+x_1x_2(e^{x_3}-1-x_3)/x_3^2\). Every \(\alpha\) with
\(x_3=2\pi i\) gives \(b=c=0\), so \(g(0,1,0,2\pi i)\) is not in the image, and
\(x_1\mathcal J^++2\pi i\mathcal J^3\) has the same exponential \(g(0,0,0,2\pi i)\) for all
\(x_1\).
Target: [M68.01.2.05].

### M68-E01.2.03. The exponential map of \(\mathcal T_3\) is not onto \(T_3\)

Status: Confirmed.
Location: §1-2, p. 12, l. 1.
Printed: "The mapping \(\alpha\to\exp\alpha\) of \(\mathcal T_3\) onto \(T_3\), Eq. (1.8), is
\(\exp\alpha=e^\alpha\)."
Correct: \(\exp\alpha=e^\alpha\) holds, but the map is not onto \(T_3\); it is a local
diffeomorphism near \(0\).
Evidence: for \(\alpha=x_1\mathcal J^++x_2\mathcal J^-+x_3\mathcal J^3\),
\(e^\alpha=g(x_1(e^{x_3}-1)/x_3,\ x_2(1-e^{-x_3})/x_3,\ x_3)\). The \(\tau\)-coordinate is \(x_3\),
and \(x_3=2\pi i\) forces \(b=c=0\); so \(g(1,0,2\pi i)\in T_3\) is not an exponential.
Target: [M68.01.2.06].

### M68-E01.3.01. Missing plus sign in the action defined by a multiplier

Status: Confirmed.
Location: §1-3, p. 17, l. 13.
Printed: \((x,w)\to(xg,\,w\ln[\nu(x,g)])\).
Correct: \((x,w)\to(xg,\,w+\ln\nu(x,g))\), as in (1.51) with \(q=\ln\nu\).
Evidence: the induced operator on \(e^wf(x)\) must be \(e^{w+\ln\nu(x,g)}f(xg)=e^w\nu(x,g)f(xg)\);
with the printed product the image of \(e^wf(x)\) is \(e^{w\ln\nu}f(xg)\), which is not of the
form \(e^w\cdot(\text{function of }x)\), and at \(g=e\) (\(\nu=1\)) the printed map sends \(w\) to
\(0\) instead of \(w\).
Target: [M68.01.3.05].

### M68-E01.3.02. Exponential series starts at \(n=0\)

Status: Confirmed.
Location: §1-3, p. 19, Theorem 1.11.
Printed: \([T^\nu(\exp\alpha t)f](x)=\sum_{n=1}^\infty\frac{t^n}{n!}[D^n_\alpha f](x)\).
Correct: the sum runs over \(n\ge0\) (the \(n=0\) term is \(f(x)\)).
Evidence: at \(t=0\) the left side is \(f(x)\) and the printed right side is \(0\); (1.60) for
\(n=0\) gives the constant Taylor coefficient \(f(x)\).
Target: [M68.01.3.08].

### M68-E01.4.01. Sign of the multiplier term in \(J^+\)

Status: Confirmed.
Location: §1-4, p. 20, (1.61).
Printed: \(J^+=2uz+z^2\frac{d}{dz}\) (with \(J^3=-u+z\frac{d}{dz}\), \(J^-=-\frac{d}{dz}\)).
Correct: \(J^+=-2uz+z^2\frac{d}{dz}\).
Evidence: with the printed operator, \([J^+,J^-]=[\frac d{dz},z^2\frac d{dz}+2uz]=2z\frac d{dz}+2u
\ne2J^3=2z\frac d{dz}-2u\). With \(-2uz\) the relation holds, and \(-2uz+z^2\frac{d}{dz}\) is the
derivative at \(b=0\) of the printed one-parameter group (1.65),
\(f\mapsto(1-bz)^{2u}f(z/(1-bz))\), and of (1.69) with \(g=\exp b\mathcal J^+\).
Target: [M68.01.4.01].

### Conventions and notation (not errata)

- Bold \(\mathbf g\) denotes points of a local group and lightface letters points of the space
  acted on, except the identity \(\mathbf e\) (p. 12); the synopsis does not distinguish them.
- §1-4, p. 20, Remark: the source does not specify the domains of the local formulas and states
  that they are "easily determined by inspection".
- The source writes \(\mathcal J^+\), \(\mathcal J^-\) with a minus sign in the matrices (1.13),
  (1.18), so that \(\exp b\mathcal J^+\) has upper right entry \(-b\); this is a choice of basis,
  not an error.

## Chapter 2. Representations and Realizations of Lie Algebras

### M68-E02.4.01. Spherical coordinates with \(\sin\theta\) and \(\cos\theta\) interchanged

Status: Confirmed.
Location: §2-4, p. 34, l. 5–7.
Printed: \(x_1=r\cos\theta\cos\varphi\), \(x_2=r\cos\theta\sin\varphi\), \(x_3=r\sin\theta\),
\(r\ge0\), \(0\le\theta\le\pi\), \(0\le\varphi<2\pi\).
Correct: \(x_1=r\sin\theta\cos\varphi\), \(x_2=r\sin\theta\sin\varphi\), \(x_3=r\cos\theta\).
Evidence: with the printed coordinates \(x_3\ge0\) only, and (2.13) fails: for
\(F=\sin^2\theta\cos\theta\,e^{2i\varphi}+\cos^3\theta\sin\varphi\) at \(\theta=0.7\),
\(\varphi=0.4\), \((-J_2+iJ_1)F\) computed from (2.12) equals \(-0.6929+0.0300i\), the value of the
right side of (2.13), in the corrected coordinates, but \(-0.0997-0.4605i\) in the printed ones.
The later formulas (\(P^l_l=c_l\sin^l\theta\), the measure \(\sin\theta\,d\theta\,d\varphi\)) also
use the corrected coordinates.
Target: [M68.02.4.01].

### M68-E02.4.02. Condition \(J^-Y_l^{-l}=0\): sign and exponent

Status: Confirmed.
Location: §2-4, p. 35, display after (2.15).
Printed: \(-\frac{dP^{-l}_l}{d\theta}-l\cot\theta\,P^{-l}_l=\frac{c_l}{(2l)!}(1-\cos^2\theta)^{-(l+1)/2}
\frac{d^{2l+1}}{d(\cos\theta)^{2l+1}}(1-\cos^2\theta)^l\equiv0\).
Correct: \(-\frac{dP^{-l}_l}{d\theta}+l\cot\theta\,P^{-l}_l=\frac{c_l}{(2l)!}(1-\cos^2\theta)^{(l+1)/2}
\frac{d^{2l+1}}{d(\cos\theta)^{2l+1}}(1-\cos^2\theta)^l\).
Evidence: \(J^-(P(\theta)e^{ik\varphi})=e^{i(k-1)\varphi}(-P'-k\cot\theta\,P)\) by (2.13), so
\(k=-l\) gives \(-P'+l\cot\theta\,P\) (consistent with the first equation (2.16)). For \(l=\frac32\),
\(c_l=1\), \(\theta=0.4\), with \(P^{-l}_l\) from (2.15): \(-P'+l\cot\theta P=15.8508\), equal to the
corrected right side \(15.8508\); the printed left side is \(-1.6747\) and the printed right side
\(1769.98\). The conclusion (vanishing iff \(l\) is an integer) is unaffected.
Target: [M68.02.4.02].

### M68-E02.4.03. Normalization constant of \(Y_l^l\)

Status: Confirmed.
Location: §2-4, p. 35, last display.
Printed: \(c_l=(-1)^l\bigl[(2l+1)!/(4\pi(l!)^2)\bigr]^{1/2}\).
Correct: \(c_l=(-1)^l\bigl[(2l+1)!/(4\pi)\bigr]^{1/2}/(2^l\,l!)\).
Evidence: \(P^l_l=c_l\sin^l\theta\) and \(\int_0^\pi\sin^{2l+1}\theta\,d\theta=
2\,(2^ll!)^2/(2l+1)!\), so \(\int_0^{2\pi}\!\int_0^\pi|Y^l_l|^2\sin\theta\,d\theta\,d\varphi=
4\pi c_l^2(2^ll!)^2/(2l+1)!\). With the printed \(c_l\) this equals \(4^l\) (\(4\) for \(l=1\),
\(16\) for \(l=2\)), not \(1\).
Target: [M68.02.4.03].

### M68-E02.7.01. Independence condition for the type A solutions

Status: Confirmed.
Location: §2-7, p. 47, l. 13–14.
Printed: "If \(m-q\) is not a positive integer there is a linearly independent solution of the
form \(g_m=w^{(q-m)/2}(1+w)^{-u}F(q-u,-m-u;q-m+1;-w)\)."
Correct: the two displayed solutions are both defined and linearly independent when
\(m-q\notin\mathbb Z\).
Evidence: for \(m=q\) (not a positive integer) the second displayed function equals the first,
\((1+w)^{-u}F(q-u,-q-u;1;-w)\); for \(m-q\) a negative integer the first displayed solution has
\(c=m-q+1\in\{0,-1,\dots\}\) and is undefined. Both functions do satisfy the type A equation
(checked numerically at \(p=0.2\), \(q=0.55\), \(m=0.3\), \(u=0.85\), \(x=0.37\): eigenvalue
\(1.5725=u(u+1)\)).
Target: [M68.02.7.04].

### M68-E02.7.02. Coefficient in the type B equation

Status: Confirmed.
Location: §2-7, p. 47, l. −8.
Printed: \(-e^{-ix}\frac{d}{dx}\bigl[e^{ix}\frac{d}{dx}g_m\bigr]+\bigl[-q^2e^{-2ix}+2mqe^{-ix}\bigr]g_m
=u(u+1)g_m\).
Correct: \(-e^{-ix}\frac{d}{dx}\bigl[e^{ix}\frac{d}{dx}g_m\bigr]+\bigl[q^2e^{-2ix}-2imqe^{-ix}\bigr]g_m
=u(u+1)g_m\).
Evidence: with \(k=i\), \(j=qe^{-ix}\) in (2.29), \(e^{-my}C_{1,0}(g_me^{my})=-g_m''-ig_m'+
(j^2+ij+j'-2imj)g_m\), and \(ij+j'=0\). The printed solutions \((2qz)^{u+1}e^{-qz}{}_1F_1(u-m+1;
2u+2;2qz)\) and \((2qz)^{-u}e^{-qz}{}_1F_1(-u-m;-2u;2qz)\), \(z=-ie^{-ix}\), satisfy the corrected
equation (at \(q=0.55\), \(m=0.3\), \(u=0.85\), \(x=0.37\) both give the eigenvalue \(1.5725\)) but
not the printed one (which gives \(1.5527+0.5963i\)).
Target: [M68.02.7.05].

### M68-E02.7.03. Type C′ solutions omit the parameter \(\mu\)

Status: Confirmed.
Location: §2-7, p. 48, l. 8–14.
Printed: \(g_m=(x^2/4)^{\pm\xi}\exp(-x^2/8)\,{}_1F_1(\pm\xi-\eta+\frac12;\pm2\xi+1;x^2/4)\) with
\(\xi=(m-q)/2\), \(\eta=(\mu/2)(m+q+2\omega+1)\).
Correct: \(g_m=(\mu x^2/4)^{\pm\xi}\exp(-\mu x^2/8)\,{}_1F_1(\pm\xi-\eta'+\frac12;\pm2\xi+1;
\mu x^2/4)\) with \(\eta'=\frac12(m+q+2\omega+1)\); the printed formulas are the case \(\mu=1\).
Evidence: the equation contains \(\mu^2x^2/16\), so for \(\mu\ne1\) the Gaussian factor must be
\(e^{-\mu x^2/8}\). Numerically (\(q=0.55\), \(m=0.3\), \(\omega=0.45\), \(x=0.37\)): for \(\mu=1\)
the printed functions give the eigenvalue \(0.45=\mu\omega\); for \(\mu=2\) they give
\(0.92567\ne\mu\omega=0.9\), while the corrected functions give \(0.9\).
Target: [M68.02.7.06].

### Conventions and notation (not errata)

- §2-1, p. 27: "irreducible" is defined by the absence of a "proper" invariant subspace; the
  intended meaning is the absence of invariant subspaces other than \(\{0\}\) and \(V\).
- §2-5, p. 38: "we get in the limit either \(\mathcal G(0,1)\) or \(\mathcal G(0,0)\) depending on
  whether or not \(b=0\)" means \(\mathcal G(0,1)\) for \(b\ne0\) and \(\mathcal G(0,0)\) for \(b=0\)
  ([M68.02.5.03]).
- §2-7, p. 46: the list of solutions of (2.30) for \(\mathcal G(1,0)\) omits \(k=-i\), \(j=qe^{ix}\),
  which is equivalent to type B under \((x,y)\mapsto(-x,-y)\) and the automorphism
  \(\mathcal J^\pm\mapsto\mathcal J^\mp\), \(\mathcal J^3\mapsto-\mathcal J^3\)
  ([M68.02.7.02]).
- §2-7, p. 48: the type C′ equation is written for \(p=0\), and the type D′, C″, D″ equations for
  \(q=0\) (and \(p=0\)) without saying so; for general \(q\) the type C″ potential is
  \((m-q)^2/x^2\) and the D″ equation is \(-g''+q^2g=\omega^2g\). These constants are removed by a
  translation in \(x\) and a gauge factor \(e^{qy}\) that shifts the spectrum
  ([M68.02.7.06], [M68.02.7.07]).

## Chapter 3. Lie Theory and Bessel Functions

### M68-E03.1.01. Abbreviated form of the coordinates \(r,v\)

Status: Confirmed.
Location: §3-1, p. 56, l. after (3.13).
Printed: "or briefly, \(r=(ibc)^{1/2}\) and \(v=(b/ic)^{1/2}\)".
Correct: \(r=2(-bc)^{1/2}\) and \(v=(-b/c)^{1/2}\), with the branches fixed by (3.13).
Evidence: (3.13) gives \(r^2=4|bc|e^{i(\arg b+\arg c+\pi)}=-4bc\) and
\(v^2=|b/c|e^{i(\arg b-\arg c-\pi)}=-b/c\), consistent with the next line \(b=rv/2\),
\(c=-rv^{-1}/2\) (then \(rv/2\cdot(-r/(2v))=-r^2/4=bc\)). The printed abbreviations give
\(r^2=ibc\) and \(v^2=b/(ic)\); for \(b=c=1\) (3.13) gives \(r=2i\), \(v=-i\), whereas
\((ibc)^{1/2}=e^{i\pi/4}\).
Target: [M68.03.1.04].

### M68-E03.3.01. \(J_{-m}\) does not satisfy the recursions (3.25)

Status: Confirmed.
Location: §3-3, p. 60, l. 14–15.
Printed: "for arbitrary complex values of \(m_0\) we can obtain the solutions \(Z_m(x)=J_m(x),
J_{-m}(x),H^{(1)}_m(x),H^{(2)}_m(x),N_m(x)\), for all \(m\in S\)" of (3.25) with \(\omega=-1\).
Correct: \(Z_m=J_m,H^{(1)}_m,H^{(2)}_m,N_m\) and \(Z_m=e^{i\pi m}J_{-m}\) (equivalently
\((-1)^{m-m_0}J_{-m}\)) are solutions; \(Z_m=J_{-m}\) is not.
Evidence: \(J_{-m}'-\frac mxJ_{-m}=J_{-m-1}\) (from \(J_\nu'+\frac\nu xJ_\nu=J_{\nu-1}\) with
\(\nu=-m\)), whereas (3.25) with \(\omega=-1\) requires \(Z_m'-\frac mxZ_m=-Z_{m+1}\). Numerically
at \(m=0.3\), \(x=1.1\): \(J_{-m}'(x)-\frac mxJ_{-m}(x)=-0.90648=J_{-1.3}(x)\), while
\(-J_{-1.3}(x)=0.90648\). For \(Y_m\) and \(H^{(1)}_m\) both sides agree.
Target: [M68.03.3.01].

### M68-E03.3.02. Sign in the one-parameter group \(\exp b\mathcal J^+\)

Status: Confirmed.
Location: §3-3, p. 61, l. 6.
Printed: \([T(\exp b\mathcal J^+)f](x,t)=f\bigl[x(1-2bt/x)^{1/2},\,t(1+2bt/x)^{-1/2}\bigr]\).
Correct: \(f\bigl[x(1+2bt/x)^{1/2},\,t(1+2bt/x)^{-1/2}\bigr]\).
Evidence: the system \(dx/db=t\), \(dt/db=-t^2/x\) (\(t=e^y\)) has the first integral \(xt\), so
\(x\,dx/db=x_0t_0\) and \(x(b)^2=x_0^2+2bx_0t_0\). The printed first component has derivative
\(-t\) at \(b=0\), not \(t\). The composite formula (3.26) uses the corrected factor
\((1+2bt/x)^{1/2}\).
Target: [M68.03.3.02].

### M68-E03.4.01. Missing first-order term in \(C_{0,0}\) in the variables \((x,t)\)

Status: Confirmed.
Location: §3-4, p. 63, (3.33).
Printed: \(\bigl(-\frac{\partial^2}{\partial x^2}-\frac1x\frac{\partial}{\partial x}+\frac{t^2}{x^2}
\frac{\partial^2}{\partial t^2}\bigr)f=\omega^2f\).
Correct: \(\bigl(-\frac{\partial^2}{\partial x^2}-\frac1x\frac{\partial}{\partial x}+\frac{t^2}{x^2}
\frac{\partial^2}{\partial t^2}+\frac t{x^2}\frac{\partial}{\partial t}\bigr)f=\omega^2f\).
Evidence: \(C_{0,0}=-\partial_x^2-\frac1x\partial_x+\frac1{x^2}\partial_y^2\) by (3.24), and
\(\partial_y^2=t^2\partial_t^2+t\partial_t\) for \(t=e^y\). For \(f=J_m(x)t^m\) (used in (3.36),
with \(C_{0,0}f=f\)) at \(m=0.4\), \(x=2.3\), \(t=1.2\), the printed operator gives \(0.92439f\), the
corrected one \(1.00000f\).
Target: [M68.03.4.01].

### Conventions and notation (not errata)

- §3-2, p. 59, (3.22): the recursions are written with argument \(r\), which corresponds to
  \(\omega=-1\) in (3.14); for general \(\omega\) the argument is \(-\omega r\) ([M68.03.2.02]).
- §3-3, p. 62, (3.31): the formula is (3.29) with \(b=0\), \(t=1\) and \(c\) replaced by \(-c\); the
  printed \(2c/xt\) is to be read with \(t=1\) ([M68.03.3.04]).
- §3-8, p. 75, proof of Lemma 3.2: "nonnegative integers \(m',m''\)" should read "integers"; the
  argument is unaffected ([M68.03.8.04]).
- §3-10, p. 77: "as the reader can verify for himself from Lemma 2.1" refers to Lemma 3.1
  ([M68.03.10.02]).
- §3-6, p. 67: the source's inner product is conjugate-linear in the first argument; the
  synopsis keeps this convention.

## Chapter 4. Lie Theory and Confluent Hypergeometric Functions

### M68-E04.2.01. Range of validity of a special case of (4.28)

Status: Confirmed.
Location: §4-2, p. 89, second display (special case \(c_1=-c_2=1\), \(b_1=x\), \(b_2=-y\) of (4.28)).
Printed: \(0=\sum_{j=0}^\infty(-1)^jL^{(j-l)}_l(x)L^{(l+n-j)}_j(y)\) "for all \(l,n\ge0\)".
Correct: the identity holds for \(l\ge0\), \(n\ge1\); for \(n=0\) the sum equals \((-1)^le^y\).
Evidence: (4.28) with \(c_1+c_2=0\) gives \(e^{y}\cdot0^n\cdot(\dots)\), which is \(0\) only for
\(n\ge1\); for \(n=0\), \(0^0L^{(0)}_l(0\cdot\dots)=1\). Numerically at \(l=1\), \(n=0\), \(x=0.7\),
\(y=0.4\) the sum is \(-1.49182=-e^{0.4}\); for \((l,n)=(2,1),(3,2),(0,1)\) it is \(0\).
Target: [M68.04.2.06].

### M68-E04.7.01. Scaling in the Hermite form (4.76)

Status: Confirmed.
Location: §4-7, p. 106, (4.76).
Printed: \(\exp(-t^2b^2-2xtb)H_k(x+bt-ct^{-1})t^k=\sum_l(-c)^{k-l}L^{(k-l)}_l(-bc)H_l(x)t^l\).
Correct: the right side is \(\sum_l(-2c)^{k-l}L^{(k-l)}_l(-2bc)H_l(x)t^l\).
Evidence: at \(x=0.3\), \(b=0.4\), \(c=-0.25\), \(t=1.3\): for \(k=1\) the left side is \(1.47012\),
the printed right side \(1.33048\), the corrected right side \(1.47012\); for \(k=3\): \(-4.72287\),
\(-5.94203\), \(-4.72287\). The conversion \(H_m(x)=e^{x^2/2}2^{m/2}D_m(2^{1/2}x)\) rescales \(b,c\)
by \(2^{-1/2}\) and contributes the factor \(2^{(k-l)/2}\) twice.
Target: [M68.04.7.03].

### M68-E04.7.02. Hermite addition formula (case \(b=0\), \(t=-1\))

Status: Confirmed.
Location: §4-7, p. 106, last display.
Printed: \(H_k(x-c)=\sum_{l=0}^k\binom klc^{k-l}H_l(x)\).
Correct: \(H_k(x+c)=\sum_{l=0}^k\binom kl(2c)^{k-l}H_l(x)\), equivalently
\(H_k(x-c)=\sum_l\binom kl(-2c)^{k-l}H_l(x)\).
Evidence: the corrected (4.76) at \(b=0\), \(t=-1\) with \(L^{(k-l)}_l(0)=\binom kl\) gives the
corrected form (the printed (4.76) would give \(H_k(x+c)=\sum\binom klc^{k-l}H_l\), also wrong).
At \(k=3\), \(x=0.3\), \(c=-0.25\): \(H_3(x-c)=-5.269\), printed sum \(-2.057\);
\(H_3(x+c)=-0.599=\sum\binom3l(2c)^{3-l}H_l(x)\).
Target: [M68.04.7.03].

### M68-E04.10.01. Exponent in the case \(c=0\), \(u=t\) of (4.94)

Status: Confirmed.
Location: §4-10, p. 112, display after (4.94).
Printed: \(e^{-bu}(1+b)^{q+k}L^{(q)}_k[u(1+b)]=\sum_{l\ge0}b^l\binom{l+k}lL^{(q-l)}_{l+k}(u)\).
Correct: \(e^{-bu}(1+b)^{q}L^{(q)}_k[u(1+b)]=\sum_{l\ge0}b^l\binom{l+k}lL^{(q-l)}_{l+k}(u)\).
Evidence: (4.94) at \(c=0\), \(t=u\) with (4.29) gives
\(e^{-bu}(1+b)^{q-k}L^{(q-k)}_k[u(1+b)]=\sum b^l\binom{l+k}lL^{(q-k-l)}_{l+k}(u)\); replace \(q\) by
\(q+k\). At \(q=0.6\), \(u=1.1\), \(b=0.2\): for \(k=1,2,3\) the right side is \(0.250681\), \(-0.430456\),
\(-0.831374\); the corrected left side agrees, the printed left side is \(0.300818\),
\(-0.619856\), \(-1.436614\). The case \(k=0\) (the next display) is unaffected.
Target: [M68.04.10.02].

### M68-E04.11.01. Corner entry of the matrix (4.95)

Status: Confirmed.
Location: §4-11, p. 113, (4.95).
Printed: the \((3,3)\) entry of \(g\{w,\alpha,\delta\}\) is \(0\).
Correct: the \((3,3)\) entry is \(1\).
Evidence: with \(0\) the matrices are singular, \(g\{0,0,0\}\) is not the identity, and the
product law (4.96) fails; with \(1\), (4.96) and (4.97) hold (numerical check of the matrix
product to \(10^{-16}\)). The matrix on p. 120 has entry \(1\).
Target: [M68.04.11.01].

### M68-E04.11.02. Sign in the basis element \(\mathcal J_1\) (4.98)

Status: Confirmed.
Location: §4-11, p. 113, (4.98).
Printed: \(\mathcal J_1=\begin{pmatrix}0&-i/2&0\\0&0&i/2\\0&0&0\end{pmatrix}\).
Correct: the \((2,3)\) entry is \(-i/2\).
Evidence: \(\mathcal J_1=\frac d{dy}g\{iy,0,0\}|_{y=0}\) has \((2,3)\) entry \(-\frac12\cdot i\). With the
printed matrix, \([\mathcal J_1,\mathcal J_2]=0\) instead of \(\frac12\mathcal Q\),
\([\mathcal J_3,\mathcal J_1]=\begin{pmatrix}0&\frac12&0\\0&0&\frac12\\0&0&0\end{pmatrix}\ne\mathcal J_2\),
and \(\exp y\mathcal J_1\) has \((1,3)\) entry \(+y^2/8\), while \(g\{iy,0,0\}\) has \(-y^2/8\)
(p. 116). With the corrected entry all of (4.99) and the exponentials on p. 116 hold, as do the
relations \([\mathcal J^+,\mathcal J^-]=-\mathcal E\), \([\mathcal J^3,\mathcal J^\pm]=\pm\mathcal J^\pm\).
Target: [M68.04.11.02].

### M68-E04.15.01. Normalization of the delta function

Status: Confirmed.
Location: §4-15, p. 124, line before Theorem 4.3.
Printed: \(\delta(l-l')=\frac1{2\pi i}\int_{-\infty}^\infty e^{ix(l-l')}dx\).
Correct: \(\delta(l-l')=\frac1{2\pi}\int_{-\infty}^\infty e^{ix(l-l')}dx\).
Evidence: \(\int e^{ix\xi}dx=2\pi\delta(\xi)\). With \(\frac1{2\pi}\) the constant
\(\delta(l-l')/(4l)\) of Theorem 4.3 follows: the \(\theta,\alpha\) integrals give \(4\pi^2\), the
\(\delta\) integral \(2\pi\delta(l-l')\), the \(r\) integral \(m!/(2l\,n!)\) by (4.126), and
\((n!/m!)\cdot4\pi^2\cdot2\pi\cdot m!/(2l\,n!)/(16\pi^3)=1/(4l)\). With \(\frac1{2\pi i}\) the constant
would be imaginary.
Target: [M68.04.15.05].

### M68-E04.18.01. Spurious factor \(l/(l-l')\) in (4.145) and before (4.148)

Status: Confirmed.
Location: §4-18, p. 132, (4.145), and p. 133, display before (4.148).
Printed: \(\langle G(u,v,\cdot,\cdot),\mathbf W(g)G(w,z,\cdot,\cdot)\rangle'=\frac l{l-l'}\sum
\frac{u^kv^nw^qz^m}{(k!n!q!m!)^{1/2}}\langle h^{(n)}_k,\mathbf W(g)h^{(m)}_q\rangle'\), and likewise
\(\langle G(\cdot,\cdot,u,v),G(\cdot,\cdot,t,p)\rangle'=\frac l{l-l'}\sum\overline{h^{(n)}_k(u,v)}
h^{(n)}_k(t,p)\).
Correct: the factor \(l/(l-l')\) is absent in both (it is \(1\)).
Evidence: (4.144) is the expansion of \(G\) in \(u^kv^n/(k!n!)^{1/2}\), which are orthonormal in
\(\mathcal F_2\), so no factor arises. Direct check with \(l'/l=0.35\): the explicit
\(h^{(n)}_k\) of p. 134 have Gram matrix the identity (\((k,n)\le(2,1)\), to \(10^{-17}\)), and
\(\langle G(u,v),G(w,z)\rangle'=0.965737-0.466504i=\exp(\bar uw+\bar vz)\) at \(u=0.3+0.2i\),
\(v=-0.4+0.1i\), \(w=0.5-0.3i\), \(z=0.2+0.6i\), whereas \(l/(l-l')=1.538\). (4.146) and (4.148),
which the source derives from these displays, carry no such factor.
Target: [M68.04.18.02].

### M68-E04.18.02. Sign in the generating function (4.146)

Status: Confirmed.
Location: §4-18, p. 132, (4.146).
Printed: \(\exp[vze^{i\alpha}-uwe^{-i\alpha}-u(l-l')^{1/2}re^{i\theta}-\dots]\).
Correct: \(\exp[\bar vze^{i\alpha}+\bar uwe^{-i\alpha}-\bar u(l-l')^{1/2}re^{i\theta}-\frac12(l-l')r^2
+i\alpha(\lambda+\lambda'+1)+i\delta(l-l')+w(l-l')^{1/2}re^{-i\theta-i\alpha}]\).
Evidence: at \(g=e\) the printed form gives \(\langle h^{(n)}_k,h^{(n)}_k\rangle'=(-1)^k\), impossible
for a norm, though the source uses (4.146) at \(g=e\) to prove orthonormality. Lemma 4.8 (4.147)
has \(+uwe^{-i\alpha}\). Numerically, \(l=1\), \(l'=0.35\), \(\lambda=1\), \(\lambda'=2\), \(r=0.4\),
\(\theta=0.7\), \(\alpha=0.3\), \(\delta=0.25\), and \(u,v,w,z\) as in [M68-E04.18.01]: the inner product
computed from (4.143), (4.144) is \(0.710605+0.597491i\); the corrected right side is
\(0.710605+0.597491i\), the printed one \(0.384714+0.785491i\).
Target: [M68.04.18.02].

### M68-E04.19.01. Missing phase in the second identity (4.166)

Status: Confirmed.
Location: §4-19, p. 142, (4.166), second display.
Printed: \(e^{-y^2/8}(y/2)^{m-n}L^{(m-n)}_n(y^2/4)=[\pi^{1/2}2^{(n+m)/2}n!]^{-1}\int
e^{-q^2-iqy/\sqrt2}H_n(q)H_m(q)dq\).
Correct: the left side is \(e^{-y^2/8}(-iy/2)^{m-n}L^{(m-n)}_n(y^2/4)\).
Evidence: at \(y=1.3\): \((n,m)=(1,2)\): left side \(0.830115\), integral \(-0.830115i\); \((2,0)\):
\(0.171022\) and \(-0.171022\); \((2,2)\): equal. The ratio is \((-i)^{m-n}\). The first identity of
(4.166) checks (\(x=0.9\)). For \(m\ne n\) the printed left side is real and the right side
is not.
Target: [M68.04.19.04].

### M68-E04.20.01. Arguments and phase in (4.190)

Status: Confirmed.
Location: §4-20, p. 150, (4.190).
Printed: right side \(\sum_n\frac{i^{s-w}k!}{(n+k-s)!}L^{(n-w)}_q(\rho)L^{(n-s)}_k(\rho)
L^{(k-q+w-s)}_{n+q-w}(r^2)(\rho)^{2n-w-s}\).
Correct: \(\sum_n\frac{k!}{(n+k-s)!}L^{(n-w)}_q(\rho^2)L^{(n-s)}_k(\rho^2)
L^{(k-q+w-s)}_{n+q-w}(r^2)\rho^{2n-w-s}\) (arguments \(\rho^2\), no factor \(i^{s-w}\)).
Evidence: (4.188) involves \(L(p^2/4l)\), i.e. a squared argument. At \(\rho=0.7\), \(r=0.5\),
\((q,w,s,k)=(1,1,0,1)\): left side \(0.805538\); printed right side \(-0.499470i\); corrected
\(0.805538\). Also checked \((1,0,0,0)\), \((0,1,0,0)\), \((2,1,2,1)\), \((1,2,0,1)\). For real
\(\rho,r\) the left side is real, so \(i^{s-w}\) cannot be right for \(s-w\) odd. The special case
\(q=w=s=k=0\) is correct.
Target: [M68.04.20.04].

### Conventions and notation (not errata)

- §4-1–§4-3: the chapter's page range is pp. 78–153; the Laguerre functions with integer
  \(\alpha\) and \(n+\alpha<0\) are understood as the terminating series, as in (4.26) and (4.36).
- §4-5, p. 95, Lemma 4.1: "If \(J^+,J^-,J^3,E\) are defined by (4.47)" refers to (4.46)
  ([M68.04.5.02]).
- §4-16, p. 126: "The matrix elements of \((\lambda,l)\)" in Theorem 4.4 and "The representation
  \((\lambda,l)\) is irreducible" in Lemma 4.6 refer to \((\lambda,-l)\) ([M68.04.16.01],
  [M68.04.16.02]).
- §4-15, p. 124: the generating function is written \(G^{\lambda,l}(g;u,s)\) with the arguments in
  the reverse order of (4.121); the result is unchanged ([M68.04.15.05]).
- §4-18: in (4.145)–(4.148) the variables in the first (antilinear) slot appear without bars;
  the synopsis writes \(\bar u,\bar v\) ([M68.04.18.02]).
- §4-21, p. 151: \(K_1=-ip\cos\alpha\), \(K_2=-ip\sin\alpha\) are the negatives of \(J_1,J_2\) in
  (3.64); \(K_{1,2}\mapsto-K_{1,2}\) is an automorphism of \(\mathcal E_3\) and the limit (4.197)
  matches this sign ([M68.04.21.01]).
- §4-19: Theorem 4.10 is a symbolic statement of (4.173), (4.176); the source does not prove
  completeness of the Hermite functions (it cites Courant–Hilbert and Bargmann).
- §4-21, p. 153: the source proves (4.201) only formally and says a direct proof from the power
  series is easy.

## Chapter 5. Lie Theory and Hypergeometric Functions

### M68-E05.5.01. Normalization of the 3-j symbol

Status: Confirmed.
Location: §5-5, p. 175, (5.57).
Printed: \(\begin{pmatrix}l_1&l_2&l_3\\m_1&m_2&m_3\end{pmatrix}=\frac{(-1)^{l_3-m_3}}{2l_3+1}
C(l_1,m_1;l_2,m_2\mid l_3,-m_3)\).
Correct: \(\begin{pmatrix}l_1&l_2&l_3\\m_1&m_2&m_3\end{pmatrix}=\frac{(-1)^{l_3-m_3}}{(2l_3+1)^{1/2}}
C(l_1,m_1;l_2,m_2\mid l_3,-m_3)\); with this definition (5.58) holds as printed.
Evidence: Take \(l_1=0\), \(l_2=l_3=\frac12\). The left side of (5.58) is \((x-w)/\sqrt2\), so the
coefficient of \(x\) (\(k_1=k_2=0\), \(k_3=1\)) requires
\(\begin{pmatrix}0&\frac12&\frac12\\0&-\frac12&\frac12\end{pmatrix}=\frac1{\sqrt2}\), while the printed (5.57) gives
\(\frac12C(0,0;\frac12,-\frac12\mid\frac12,-\frac12)=\frac12\). With the square root, (5.58) was verified
exactly for \((l_1,l_2,l_3)\in\{(1,1,1),(1,1,0),(1,\frac12,\frac12),(2,1,1),(\frac32,1,\frac12),(2,2,1),
(\frac12,\frac12,1),(\frac32,\frac32,1)\}\), using \(C=\) Condon–Shortley coefficients (which the
source's \(C\) equal).
Target: [M68.05.5.06].

### M68-E05.6.01. Missing hypothesis in the decomposition of \(\uparrow_u\otimes\uparrow_v\)

Status: Confirmed.
Location: §5-6, pp. 176–178, Lemma 5.6 and Theorem 5.2.
Printed: For \(2u,2v\) not nonnegative integers, \(\uparrow_u\otimes\uparrow_v\cong\sum_{s=0}^\infty\oplus\,\uparrow_{u+v-s}\),
with \(f_{s,k}=\frac{\Gamma(2s-2u-2v)}{\Gamma(2s-2u-2v+k)}(J^+)^kf_{s,0}\) a basis.
Correct: The decomposition, the normalization of \(f_{s,k}\) and Lemma 5.6 require in addition
\(2(u+v)\notin\mathbb Z_{\ge0}\) (equivalently \(2(u+v-s)\notin\mathbb Z_{\ge0}\) for all \(s\ge0\)).
Evidence: For \(u=v=\frac34\) (so \(2u=2v=\frac32\)), \(\Gamma(2s-2u-2v)=\Gamma(-3)\) is undefined at \(s=0\), and
\(\uparrow_{u+v}=\uparrow_{3/2}\) is not defined. The submodule generated by \(f_{0,0}=1\) is not
irreducible: with \(J^+=-\frac32z-\frac32w+z^2\partial_z+w^2\partial_w\) one computes
\((J^+)^4 1=\frac9{16}(z-w)^4=\frac9{16}f_{4,0}\), so the cyclic submodules generated by \(f_{0,0}\) and
\(f_{4,0}\) intersect and the sum over \(s\) is not direct.
Target: [M68.05.6.02].

### M68-E05.11.01. Sign of the exponent \(r/2\) in the type A multiplier representation

Status: Confirmed.
Location: §5-11, p. 196, the formulas for \(\mathbf T(\exp(-bJ^+))\), \(\mathbf T(\exp(-cJ^-))\) and (5.109).
Printed: the scalar multipliers are \(\big[\frac{(z^2-1)^{1/2}+bt(z+1)}{(z^2-1)^{1/2}+bt(z-1)}\big]^{r/2}\),
\(\big[\frac{(z^2-1)^{1/2}+ct^{-1}(z-1)}{(z^2-1)^{1/2}+ct^{-1}(z+1)}\big]^{r/2}\), and the product of the two
corresponding brackets raised to \(r/2\) in (5.109).
Correct: the exponent is \(-r/2\) in all three formulas (equivalently, \(z+1\) and \(z-1\) are interchanged in
each bracket).
Evidence: Differentiating the printed \(\mathbf T(\exp(-bJ^+))f\) at \(b=0\) gives
\(tR\,\partial_zf-\frac{t^2z}{R}\partial_tf+\frac{rt}{R}f\) (\(R=(z^2-1)^{1/2}\)), whereas
\(-J^+f=tR\,\partial_zf-\frac{t^2z}{R}\partial_tf-\frac{rt}{R}f\) for the operator (5.106) (whose sign of \(r\) is
confirmed by (5.108)(i)); likewise for \(J^-\). Numerically, with \(u=0.37\), \(r=0.23\), \(m_0=0.41\),
\(z=1.9\), \(t=1.1\), \(a=1.05\), \(b=0.03\), \(c=0.04\), \(f=f_{m_0}\): the printed (5.109) gives \(0.915400\), the
right side \(\sum_lA_{l0}(g)f_{m_0+l}\) of (5.110) gives \(0.915405\), and the corrected (5.109) agrees with it
to 30 digits (also for \(k=2\) and for \(c=0\) or \(b=0\)).
Target: [M68.05.11.02].

### M68-E05.11.02. Sign of \(r\) in the prefactors of the addition theorems for \(\mathfrak B_u^{r,m}\)

Status: Confirmed.
Location: §5-11, p. 197, the three displayed identities following (5.110).
Printed: the prefactors are \(\big(1+\frac{b(z+1)}R\big)^{(r-m)/2}\big(1+\frac{b(z-1)}R\big)^{(-r-m)/2}\);
\(\big(1+\frac{c(z-1)}R\big)^{(r+m)/2}\big(1+\frac{c(z+1)}R\big)^{(-r+m)/2}\); and
\((1+e^{-i\alpha}X)^{(r+m)/2}(1+e^{i\alpha}X)^{(-r-m)/2}(1+e^{-i\alpha}Y)^{(-r+m)/2}(1+e^{i\alpha}Y)^{(r-m)/2}\).
Correct: replace \(r\) by \(-r\) in each prefactor (the functions \(\mathfrak B_u^{r,m}\) are unchanged), as in
[M68.05.11.03]; this follows from the corrected (5.109).
Evidence: At \(u=0.37\), \(r=0.23\), \(m=-0.41\), \(z=1.9\), \(b=0.05\), the first identity gives \(1.20699\) (printed
left side) against \(1.19086\) (right side); with \(r\to-r\) in the prefactor both sides equal
\(1.190861452823517\). The second: \(1.13675\) against \(1.15214\), corrected both \(1.152141993037953\). The
third (\(\rho=1.15\), \(\alpha=0.7\)): printed \(1.25836+0.19846i\), right side \(1.26828+0.11969i\), corrected
left side equal to the right side to 22 digits.
Target: [M68.05.11.03].

### M68-E05.12.01. Sign of \(r\) in the prefactors of the \(\uparrow_u\) addition theorems

Status: Confirmed.
Location: §5-12, pp. 201–202, the three identities following (5.116).
Printed: prefactors \(\big(1+\frac{b(z+1)}R\big)^{(r-m)/2}\big(1+\frac{b(z-1)}R\big)^{(-r-m)/2}\);
\(\big(1+\frac{c(z-1)}R\big)^{(r+m)/2}\big(1+\frac{c(z+1)}R\big)^{(-r+m)/2}\); and
\((1+e^{-i\alpha}X)^{(r+m)/2}(1+e^{i\alpha}X)^{(-r-m)/2}(1+e^{-i\alpha}Y)^{(-r+m)/2}(1+e^{i\alpha}Y)^{(r-m)/2}\), multiplying
\(\mathfrak B_u^{-r,-m}\).
Correct: replace \(r\) by \(-r\) in each prefactor, as in [M68.05.12.01]. The identities are consequences of
(5.109), whose multiplier exponent has the wrong sign ([M68-E05.11.01]).
Evidence: At \(u=0.37\), \(m=-u+2\), \(r=0.23\), \(z=1.9\), \(b=c=0.05\): first identity, printed left side
\(-0.291029\) against right side \(-0.287141\), corrected left side \(-0.2871411224452209\); second, \(-0.345453\)
against \(-0.350130\), corrected equal; third (\(\rho=1.15\), \(\alpha=0.7\)), \(-0.22783+0.11482i\) against
\(-0.22023+0.12879i\), corrected equal to 14 digits.
Target: [M68.05.12.01].

### M68-E05.14.01. Phase of the normalization constant \(c_r\)

Status: Confirmed.
Location: §5-14, p. 208, the definition of \(c_r\) and the resulting \(W_m(z)\).
Printed: \(c_r=\frac{(-1)^{u-r}}{(u+r)!}\big[\frac{(u+r)!(2u)!}{(u-r)!}\big]^{1/2}\), "Thus"
\(W_m(z)=(-1)^{m+r}\big[\frac{(u+m)!(u+r)!}{(u-m)!(u-r)!}\big]^{1/2}\mathfrak B_u^{r,m}(z)\).
Correct: inserting the printed \(c_r\) into (5.126) gives \(W_m=(-1)^{2u-m-r}[\cdots]^{1/2}\mathfrak B_u^{r,m}\), which differs from the
printed \(W_m\) by the factor \((-1)^{2u}\); the printed \(W_m\) requires \(c_r=\frac{(-1)^{u+r}}{(u+r)!}\big[\frac{(u+r)!(2u)!}{(u-r)!}\big]^{1/2}\).
The synopsis keeps the printed \(W_m\). For integer \(u\) the two agree; the discrepancy is a constant factor and
does not affect (5.127).
Evidence: In (5.126) the coefficient of \(\mathfrak B_u^{r,m}\) is \(c_r(-1)^{u-m}\Gamma(u+r+1)[(u+m)!/((2u)!(u-m)!)]^{1/2}\) (checked
against the recursion \(W_{m-1}=[(u+m)(u-m+1)]^{-1/2}(-(z^2-1)^{1/2}\frac d{dz}-\frac{zm+r}{(z^2-1)^{1/2}})W_m\) and (5.83)). For
\(u=r=m=\frac12\): the printed \(c_r\) gives \(W_{1/2}=c_{1/2}\Gamma(2)\mathfrak B^{1/2,1/2}_{1/2}=\mathfrak B_{1/2}^{1/2,1/2}\), whereas the printed
\(W_m\) formula gives \((-1)^1\mathfrak B_{1/2}^{1/2,1/2}\).
Target: [M68.05.14.01].

### M68-E05.14.02. Sign of \(r\) in the prefactors of the \(D(2u)\) addition theorems

Status: Confirmed.
Location: §5-14, pp. 208–209, the four identities following (5.127).
Printed: prefactors \(\big(1+\frac{c(z-1)}R\big)^{(r-u+k)/2}\big(1+\frac{c(z+1)}R\big)^{(-r-u+k)/2}\);
\((1+e^{-i\alpha}X)^{(r+m)/2}(1+e^{i\alpha}X)^{(-r-m)/2}(1+e^{-i\alpha}Y)^{(-r+m)/2}(1+e^{i\alpha}Y)^{(r-m)/2}\);
\((1-\tau\tan\frac\theta2)^{(r-u+k)/2}(1+\tau\cot\frac\theta2)^{(-r-u+k)/2}\); and
\((1-e^{-i\alpha}T_1)^{(r+m)/2}(1+e^{-i\alpha}T_2)^{(-r+m)/2}(1+e^{i\alpha}T_2)^{(r-m)/2}(1-e^{i\alpha}T_1)^{(-r-m)/2}\) with
\(T_1=\tan\frac\varphi2\tan\frac\theta2\), \(T_2=\tan\frac\varphi2\cot\frac\theta2\).
Correct: replace \(r\) by \(-r\) in each prefactor, as in [M68.05.14.02] (consequence of [M68-E05.11.01]).
Evidence: For \(u=r=1\), \(z=1.9\), \(c=0.05\): first identity at \(k=0\), printed left side \(1.367639\), right side
\(1.45\), corrected left side \(1.45\); at \(k=1\): \(0.830275\) against \(0.880275\) (corrected equal). Third identity
(\(\theta=1.1\), \(\tau=0.1\), \(k=1\)): \(0.418283\) against \(0.518283\), corrected equal. Second and fourth
(\(\rho=1.15\), \(\varphi=0.6\), \(\alpha=0.7\)): the printed left sides are the complex conjugates of the right
sides for \(m=0\) and differ for \(m=1\) (\(0.24252+0.07076i\) against \(0.22629-0.11232i\)); corrected, both
agree to 20 digits.
Target: [M68.05.14.02].

### M68-E05.15.01. Confluent equation and solution for \(C_{1,0}f=u(u+1)f\), \(J^+f=-f\)

Status: Confirmed.
Location: §5-15, p. 212.
Printed: substituting \(f=t^u\exp(t^{-1})h(zt^{-1})\) into (i) gives \(x\frac{d^2h}{dx^2}+(2u-x)\frac{dh}{dx}+(q+u)h=0\), and
\(f(z,t)=t^u\exp(t^{-1})\,{}_1F_1(q+u;2u;zt^{-1})\).
Correct: \(x\frac{d^2h}{dx^2}+(x-2u)\frac{dh}{dx}-(q+u)h=0\), with regular solution \(h(x)={}_1F_1(-q-u;-2u;-x)\), so
\(f(z,t)=t^u\exp(t^{-1})\,{}_1F_1(-q-u;-2u;-zt^{-1})\) \(\big(=t^u\exp((1-z)t^{-1})\,{}_1F_1(q-u;-2u;zt^{-1})\big)\).
Evidence: Direct substitution (symbolic) of \(t^u e^{1/t}h(z/t)\) into (i) gives
\(t^{-1}[xh''+(x-2u)h'-(q+u)h]\). Numerically, at \(u=-0.31\), \(q=0.17\), \(z=0.3\), \(t=1.7\), the left side of
(i) applied to the printed \(f\) is \(0.4688\), and to the corrected \(f\) is \(0\) (to 32 digits). (The printed
solution does not even solve the printed equation, whose regular solution is \({}_1F_1(-q-u;2u;x)\).)
Target: [M68.05.15.03].

### M68-E05.15.02. Confluent function in (5.129)–(5.131)

Status: Confirmed.
Location: §5-15, pp. 213–214, (5.129), (5.130), the identity for \(a=c=w^{-1/2}\), \(b=0\), and (5.131).
Printed: \({}_1F_1\big[q+u;2u;\frac{z\tau}{(a-c(z-1)\tau)(a+c\tau)}\big]\) in (5.129); \(e^\tau{}_1F_1(-\mu;-\nu;z\tau)\) in (5.130);
\({}_1F_1\big[-\mu;-\nu;\frac{z\tau w}{(1-(z-1)\tau)(1+\tau)}\big]\); and \((1-z)^{-\mu}e^t{}_1F_1\big(-\mu;-\nu;\frac{zt}{1-z}\big)\) in (5.131).
Correct: \({}_1F_1\big[-q-u;-2u;\frac{-z\tau}{(a-c(z-1)\tau)(a+c\tau)}\big]\); \(e^\tau{}_1F_1(\mu;\nu;-z\tau)\);
\({}_1F_1\big[\mu;\nu;\frac{-z\tau w}{(1-(z-1)\tau)(1+\tau)}\big]\); \((1-z)^{-\mu}e^t{}_1F_1\big(\mu;\nu;\frac{zt}{1-z}\big)\). The right-hand
sides and the coefficients \(j_{u-n}(g)\) are correct as printed.
Evidence: (5.130) at \(\mu=0.29\), \(\nu=0.71\), \(z=0.3\), \(\tau=0.4\): printed left side \(1.576277\), right side
\(\sum\tau^nF(-n,\mu;\nu;z)/n!=1.421905\), corrected left side \(1.421904980313303\) (this is the classical
\(\sum_n\frac{\tau^n}{n!}F(-n,\mu;\nu;z)=e^\tau{}_1F_1(\mu;\nu;-z\tau)\)). (5.129) at \(u=-0.31\), \(q=0.17\), \(a=1.1\), \(b=0.2\), \(c=0.3\),
\(z=0.3\), \(\tau=0.05\) (factor \(\tau^{-u}\) removed): printed \(1.171670\), right side \(1.165247\), corrected equal to 24
digits. The \(w\)-identity (\(w=0.6\), \(\tau=0.2\)): printed \(0.996471\), corrected \(0.975044\) \(=\) right side. (5.131)
(\(t=0.5\)): printed \(2.034638\), corrected \(2.002174\) \(=\) right side. The errors stem from [M68-E05.15.01].
Target: [M68.05.15.03].

### M68-E05.18.01. Moduli of \(a\) and \(b\) in the coordinates on \(G_3\)

Status: Confirmed.
Location: §5-18, p. 227, line 9 (display after "case these parameters can be defined by").
Printed: \(|a|=\cosh\rho\), \(|b|=\sinh\rho\).
Correct: \(|a|=\cosh(\rho/2)\), \(|b|=\sinh(\rho/2)\).
Evidence: by (5.157), printed on p. 226, \(a=e^{-i(\mu+\nu)/2}\cosh(\rho/2)\) and \(b=e^{i(\nu-\mu)/2}\sinh(\rho/2)\). The printed
values are incompatible with (5.157) for every \(\rho>0\). The SU(2) analogue on p. 217 has the half angle (\(\cos(\theta/2)=|a|\)). The
argument \(\cosh\rho\) of \(\mathfrak B\) in (5.159), (5.164), (5.168), (5.171), (5.177) is correct, since
\(|a|^2+|b|^2=\cosh\rho\).
Target: [M68.05.18.01].

### M68-E05.18.02. Normalization of the orthonormal basis of \(D_n^-\)

Status: Confirmed.
Location: §5-18, p. 237, line 7 (definition of \(j_m\)), and p. 238, line 7 (definition of \(j_{-n-k}(z)\)).
Printed: \(j_m=\big[\frac{(n-m-1)!}{(2n+1)!\,(-n-m)!}\big]^{1/2}f_m\) and
\(j_{-n-k}(z)=\big[\frac{(2n+k-1)!}{(2n+1)!\,k!}\big]^{1/2}z^k\).
Correct: \(j_m=\big[\frac{(n-m-1)!}{(2n-1)!\,(-n-m)!}\big]^{1/2}f_m\) and \(j_{-n-k}(z)=\big[\frac{(2n+k-1)!}{(2n-1)!\,k!}\big]^{1/2}z^k\).
Evidence: by (5.175), \(\langle z^k,z^k\rangle_{2n}=k!(2n-1)!/(2n+k-1)!\), so the printed \(j_{-n-k}\) has squared norm
\((2n-1)!/(2n+1)!=1/(2n(2n+1))\ne1\). The analogous definitions for \(D_n^+\) on pp. 226 and 236 have \((2n-1)!\),
and the matrix elements \(C^n_{lk}\) of (5.177) (in which the factor cancels) agree with the corrected basis.
For the abstract basis on p. 237 a common constant factor does not affect (5.155) or (5.177), but it contradicts the
claim that \(\{j_m\}\) is orthonormal when \(|f_{-n}|=1\).
Target: [M68.05.18.06].

### Conventions and notation (not errata)

- §5-5, p. 175, (5.57): with the square root restored ([M68-E05.5.01]) the source's 3-j symbol
  carries the phase \((-1)^{l_3-m_3}\); Wigner's standard symbol has \((-1)^{l_1-l_2-m_3}\), so the two differ
  by the factor \((-1)^{l_2+l_3-l_1}\). The generating function (5.58) holds with the source's phase
  ([M68.05.5.06]). The source's Clebsch–Gordan coefficients \(C(u,l;v,j\mid r,k)\) of (5.53) coincide
  with the Condon–Shortley ones ([M68.05.5.04]).
- §5-2, p. 164, (5.22)–(5.23) (and (5.37)): the two displays are printed with the ranges
  \(k\ge l\ge0\) and \(l\ge k\ge0\); the text notes that both hold for all \(l,k\ge0\) with (A.5).
- §5-16–§5-19: inner products are conjugate-linear in the first argument and linear in the second (stated on
  p. 239), and matrix elements are \(U_{nm}(A)=\langle p_n,\mathbf U(A)p_m\rangle\) (column convention).
- §5-16, p. 219, (5.143): \(P_u^{n,m}(x)=e^{-i\pi(m+n)/2}\mathfrak B_u^{n,m}(x+i0)\) is the source's normalization of the
  Jacobi functions used in §5-16 and §5-19.
- §5-19, p. 241: the source labels its derivation of (5.186) as not rigorous; (5.187) itself is stated as following
  from power series and is numerically confirmed (synopsis M68.05.19.02).
- §5-16, p. 215: the source calls the rotation group \(O_3\); the image of \(R\) is \(SO(3)\) (the connected
  component), as is standard.

## Chapter 6. Special Functions Related to the Euclidean Group in 3-Space

### M68-E06.1.01. Factor \((u+m)\) in the \(P^+\) formula of (6.8)

Status: Confirmed.
Location: §6-1, p. 248, (6.8), third term of \(P^+f^{(u)}_m\).
Printed: \(-\frac{\zeta(u+m)(u-m-1)}{(2u+1)u}f^{(u-1)}_{m+1}\).
Correct: \(-\frac{\zeta(u-m)(u-m-1)}{(2u+1)u}f^{(u-1)}_{m+1}\).
Evidence: the corrected (6.8) is the limit of (6.5) (p. 246, whose \(P^+\) term is \(-\frac{\omega(u+q)(u-m)(u-m-1)}{(2u+1)u}\)) with
\(\omega q=\zeta\), \(\omega\to0\). A symbolic check with generic \(u,m,\zeta\) shows that the corrected operators satisfy all relations
(6.1) with \(\mathbf P\cdot\mathbf P=0\), \(\mathbf P\cdot\mathbf J=-\zeta\), whereas with the printed factor \([P^3,J^+]=P^+\), \([J^+,P^+]=0\),
\([P^+,J^-]=2P^3\), \([P^3,P^+]=0\), \([P^+,P^-]=0\) all fail and \(\mathbf P\cdot\mathbf P\) is not scalar. The same factor recurs in (6.18)
([M68-E06.3.01]).
Target: [M68.06.1.05].

### M68-E06.1.02. Sign of \(q\) in the limit from (6.5) to (6.8)

Status: Confirmed.
Location: §6-1, p. 248, lines 4–5 after (6.8): "by setting \(q=-\zeta/\omega\) and passing to the limit as \(\omega\to0\)".
Printed: \(q=-\zeta/\omega\).
Correct: \(q=\zeta/\omega\).
Evidence: (6.5) has \(\mathbf P\cdot\mathbf J=-\omega q\), and (6.8) has \(\mathbf P\cdot\mathbf J=-\zeta\); so \(\omega q=\zeta\). Term by term, the limits of
the coefficients in (6.5) with \(\omega q=\zeta\) are \(\omega(u-q+1)\to-\zeta\), \(m\omega q\to\zeta m\), \(\omega(u+q)\to\zeta\), which are the
coefficients printed in (6.8); with \(q=-\zeta/\omega\) every coefficient would change sign.
Target: [M68.06.1.05].

### M68-E06.3.01. Factor \((u+m)\) in the second relation of (6.18)

Status: Confirmed.
Location: §6-3, p. 253, (6.18), second relation, last term.
Printed: \(+\frac{(u+m)(u-m-1)}{(2u+1)u}Z^{(u-1)}_{m+1}(z)\).
Correct: \(+\frac{(u-m)(u-m-1)}{(2u+1)u}Z^{(u-1)}_{m+1}(z)\).
Evidence: the second relation of (6.18) is \(P^+f^{(u)}_m\) of (6.8) divided by \(-\zeta\), with \(P^+=2\zeta tz^{-1}\) from (6.16), so it
inherits [M68-E06.1.01]. With the printed factor the relations are inconsistent with (6.1) (see that erratum).
Target: [M68.06.3.01].

### M68-E06.4.01. Sign in \(\mathcal J^\pm\) for \(\mathcal E_6\)

Status: Confirmed.
Location: §6-4, p. 256, line 4 after (6.25).
Printed: \(\mathcal J^\pm=\pm\mathcal J_2+i\mathcal J_1\).
Correct: \(\mathcal J^\pm=\mp\mathcal J_2+i\mathcal J_1\).
Evidence: with (6.24), \([i\mathcal J_3,\mathcal J_2+i\mathcal J_1]=-(\mathcal J_2+i\mathcal J_1)\), so the printed \(\mathcal J^+\) would be lowering; a check in the
\(4\times4\) matrix model of \(\mathfrak e(3)\) shows that, together with \(\mathcal P^\pm=\mp\mathcal P_2+i\mathcal P_1\), only the sign \(\mp\) gives (6.1).
The source itself uses \(\mp\) for \(su(2)\) on p. 215 and for the operators (6.27) on p. 257.
Target: [M68.06.4.02].

### Conventions and notation (not errata)

- §5-16, p. 215 and §6-4, p. 255: the source's Pauli matrix is \(\sigma^3=\mathrm{diag}(-1,1)\), the negative of the usual one.
  The matrix \(R(A)\) of (6.23) is correct for this choice; with the usual \(\sigma^3\) one obtains \(DR(A)D\), \(D=\mathrm{diag}(1,1,-1)\).
- §6-1: the hypotheses (i)–(iv) of Theorems 6.1–6.2 concern algebraic direct sums of \(\mathfrak{sl}(2)\)-modules; the classification
  does not cover all \(\mathcal T_6\)-modules. Proofs of Theorems 6.1 and 6.2 are omitted in the source.
- §6-1: in (6.5), (6.8), (6.30) a term whose coefficient has a vanishing denominator (for example at \(u=0\)) is to be read
  as absent; the source does not say so.
- §6-5, p. 265: the inner product \(\langle\cdot,\cdot\rangle^*\) is linear in the second argument and conjugate-linear in the first.

## Chapter 7. The Factorization Method

### M68-E07.2.01. Exponent of the gauge factor \(\varphi_m^{-1}\) for type A

Status: Confirmed.
Location: §7-2, p. 274, lines 3–4.
Printed: \(Y'_{\lambda'}(m,x)=\varphi_m^{-1}(x)Y_\lambda(m,x)\) where \(\varphi_m^{-1}(x)=(\sin(x+p))^{1/2}\).
Correct: \(\varphi_m^{-1}(x)=(\sin(x+p))^{-1/2}\), i.e. \(Y'_{\lambda'}(m,x)=(\sin(x+p))^{-1/2}Y_\lambda(m,x)\).
Evidence: substituting \(Y'=(\sin x)^{-1/2}Y\) (\(p=0\)) with \(Y''=(V_m-\lambda)Y\) from (7.15) into the transformed equation gives 0
identically (symbolic check); with \(Y'=(\sin x)^{1/2}Y\) the residual is \((Y\sin x-2Y'\cos x)/\sqrt{\sin x}\ne0\). The direction is also forced
by §7-1: the operator \(-\frac1{\sin}\frac d{dx}\sin\frac d{dx}\) has \(D=-\cot x\), whose normal-form gauge is
\(\varphi=\exp\frac12\int D=(\sin x)^{-1/2}\), so the normal-form solution \(Y\) equals \(\varphi^{-1}Y'=(\sin x)^{1/2}Y'\).
Target: [M68.07.2.02].

### M68-E07.2.02. Transformed type E equation and (7.16)

Status: Confirmed.
Location: §7-2, p. 275, the display after "we obtain" and (7.16) with the line before it.
Printed: \(\big[-\frac{d^2}{dz^2}-\frac{2iq\cos z+\lambda+\frac14}{\sin^2z}\big]W(z)=-(m+\frac12)^2W(z)\); "in terms of the constants \(r,l\) given by
\(\lambda=-l^2-r^2\), \(q=irl\)": \(\big[-\frac{d^2}{dz^2}+\frac{2rl\cos z+r^2+(l+\frac12)(l-\frac12)}{\sin^2z}\big]W(z)=-(m+\frac12)^2W(z)\) (7.16).
Correct: \(\big[-\frac{d^2}{dz^2}+\frac{2iq\cos z+\lambda-\frac14}{\sin^2z}\big]W(z)=(m+\frac12)^2W(z)\); with \(\lambda=l^2+r^2\), \(q=-irl\):
\(\big[-\frac{d^2}{dz^2}+\frac{2rl\cos z+r^2+(l+\frac12)(l-\frac12)}{\sin^2z}\big]W(z)=(m+\frac12)^2W(z)\).
Evidence: with \(i(z+\frac\pi2)=\ln\tan\frac x2\) one has \(d/dz=i\sin x\,d/dx\), \(\sin z=-1/\sin x\), \(\cos z=i\cot x\); a symbolic computation
with \(W=\sin^{-1/2}x\,Y\) and \(Y''=(m(m+1)/\sin^2x+2q\cot x-\lambda)Y\) gives
\(-W_{zz}/W=(m+\frac12)^2+(\frac14-\lambda)\sin^2x+2q\sin x\cos x\), i.e. the corrected equation. Numerically, for a solution with
\(m=0.3\), \(q=0.7\), \(\lambda=1.9\) at \(x=1.2\), the corrected equation has residual \(0\) (30 digits) and the printed one \(-0.3958\). The
printed (7.16) does not follow from the printed parametrization either. The conclusion drawn (type E eigenfunctions are type A
eigenfunctions with the roles of \(l\) and \(m+\frac12\) exchanged) holds for the corrected form.
Target: [M68.07.2.03].

### Conventions and notation (not errata)

- §7-1: the source normalizes \(L^\pm_m=\mp\frac d{dx}+B_m\), so \(L^+\) is the raising operator. The "Riccati difference equation" is
  (7.10); the constants \(a_m\) are independent of \(x\).
- §7-2: the completeness of the types A–F for the ansatz (7.17) is asserted as "a straightforward exercise" without proof; the
  synopsis records it as stated without proof (M68.07.2.03).

## Chapter 8. Generalized Lie Derivatives

### M68-E08.2.01. Whitehead lemmas stated for all degrees

Status: Confirmed.
Location: §8-2, p. 288, paragraph before Theorem 8.4.
Printed: "we can apply the Whitehead lemmas (Jacobson [1], Chapter 3) which state \(H^i(\mathcal G',\mathcal O(\mathcal M))=0\), \(i=0,1,2,\dots\)."
Correct: for \(\mathcal G'\) semisimple and \(\mathcal O(\mathcal M)\) finite-dimensional (characteristic 0), \(H^1(\mathcal G',\mathcal O(\mathcal M))=H^2(\mathcal G',\mathcal O(\mathcal M))=0\). Only
\(H^2=0\) is needed for the conclusion that the extension splits.
Evidence: for the trivial module \(\mathbb C\), \(H^0(\mathcal G',\mathbb C)=\mathbb C\ne0\), and \(H^3(\mathfrak{sl}(2),\mathbb C)\cong\mathbb C\ne0\) (spanned by the cocycle
\((x,y,z)\mapsto\kappa([x,y],z)\), \(\kappa\) the Killing form). The trivial module occurs here, e.g. for \(\mathcal G(1,0)=\mathfrak{sl}(2)\oplus(\mathcal E)\) realized
by (8.30), where \(\mathcal M=(\mathcal E)\) and \(\mathcal O(\mathcal M)=\mathbb C1\). Theorem 8.4 itself is unaffected.
Target: [M68.08.2.05].

### Conventions and notation (not errata)

- §8-1: the source defines gd's on an associative algebra; the identity with \(h=1\) forces \(D(1)\) to be central, and the converse
  (\(\tilde D+h\) is a gd) needs \(h\) central. All applications are to the commutative algebra \(\mathcal O\).
- §8-2, p. 288, Theorem 8.4: \(\mathcal G'\oplus\mathcal M\) denotes the split extension (semidirect sum) \(\mathcal G'\ltimes\mathcal M\), not the direct sum; for the
  type E realization of \(\mathcal T_6\) the ideal \(\mathcal M\) of multiplication operators is not central.
- §8-2–§8-4: all cohomology is of germs at the base point; \(H^1(\mathcal G,\mathcal O)\) and Theorems 8.3, 8.5 are local statements.
- §8-4: the two-variable lists and Lie's one-variable classification are quoted without proof; the synopsis records them as
  stated without proof. In (8.26) the normalization \(a_1(a_1-1)=0\) is achieved by rescaling \(z\).

## Chapter 9. Some Generalizations

### M68-E09.2.01. Group law and inverse of \(K_5\)

Status: Confirmed.
Location: §9-2, p. 300, (9.3) and the inverse displayed below it.
Printed: \(g(q,a,b,c,\tau)g(q',a',b',c',\tau')=g(q+e^{2\tau}q',a+a'+e^\tau cb',b+e^\tau b'+2e^{2\tau}cq',c+e^{-\tau}c',\tau+\tau')\);
inverse \(g(-qe^{-2\tau},-a+bc-2c^2q,-be^{-\tau}+2cqe^{-\tau},-ce^\tau,-\tau)\).
Correct: second component \(a+a'+e^\tau cb'+e^{2\tau}c^2q'\); inverse second component \(-a+bc-c^2q\).
Evidence: the printed law is not associative: for three elements the second components of \((g_1g_2)g_3\) and \(g_1(g_2g_3)\) differ by
\(-2c_0c_1q_2e^{\tau_0+2\tau_1}\) (symbolic check). The matrix realization (9.4), whose entries are confirmed by (9.5) and (9.1), multiplies
according to the corrected law, and the corrected inverse is the matrix inverse. The printed inverse is the inverse for the printed law.
Target: [M68.09.2.01].

### M68-E09.4.01. Exponent of \(q'\) in (9.16)

Status: Confirmed.
Location: §9-4, p. 305, (9.16).
Printed: \(\cdot\frac{q'^m}{m!}H_m\big(\frac{b'}{2\sqrt{q'}}\big)\).
Correct: \(\cdot\frac{q'^{m/2}}{m!}H_m\big(\frac{b'}{2\sqrt{q'}}\big)\).
Evidence: \(\exp(bz-qz^2)=\sum_nq^{n/2}H_n(b/2\sqrt q)z^n/n!\), and (9.16) is the coefficient of \(z^n\) in the product of two such series. Numerically
(\(q=0.3\), \(q'=0.5\), \(b=0.7\), \(b'=-0.4\), \(n=2\)): left side \(-0.755\), corrected right side \(-0.755\), printed right side \(-0.46299\).
Target: [M68.09.4.02].

### M68-E09.4.02. The relation before (9.17) and the exponential factor in (9.17)

Status: Confirmed.
Location: §9-4, p. 305, the group relation before (9.17) and (9.17).
Printed: \(g(0,0,0,c,0)g(-b/2c,0,b,0,0)=g(-b/2c,bc,0,c,0)\); \(\exp(2bc^2)R^{\rho+k}_{l-k}(-b,c)=\sum_jc^{j-l}\binom{\rho+j}{j-l}\frac{b^{(j-k)/2}}{(j-k)!}H_{j-k}(\frac{bc}{\sqrt b})\).
Correct: \(g(0,0,0,c,0)g(-b/2c,0,b,0,0)=g(-b/2c,bc/2,0,c,0)\); \(\exp(bc^2)R^{\rho+k}_{l-k}(-b,c)=\) the same right side.
Evidence: the relation follows from the corrected law of [M68-E09.2.01] (the printed law gives \(bc\)). The identity (9.17) is the matrix element
form of the relation with \(\mu=1\) and \(b\) replaced by \(2bc\); the factor is then \(e^{bc^2}\). Numerically (\(\rho=0.37\), \(b=0.6\), \(c=0.45\)), for
\((l,k)=(0,0),(2,1),(1,3),(3,0)\): right side \(1.144840\), \(-0.418664\), \(0.908469\), \(0.033611\); corrected left side equal to 15 digits;
printed left side \(1.292742\), \(-0.472751\), \(1.025833\), \(0.037953\).
Target: [M68.09.4.02].

### M68-E09.4.03. Sign of \(t^{-1}\) in the \(h^m_n\) identity

Status: Confirmed.
Location: §9-4, p. 307, display after "If \(a=b=\tau=0\), \(q=-\frac12\), (9.22) simplifies to".
Printed: \(H_m\Big(\frac{x+c(t+t^{-1})}{(1-t^2)^{1/2}}\Big)\).
Correct: \(H_m\Big(\frac{x+c(t-t^{-1})}{(1-t^2)^{1/2}}\Big)\).
Evidence: in (9.21) the first argument is \((x+bt-ct^{-1}-2ctq)/(1+2t^2q)^{1/2}\), which for \(b=0\), \(q=-\frac12\) is \((x+ct-ct^{-1})/(1-t^2)^{1/2}\). Numerically
(\(m=0.37\), \(x=0.6\), \(c=0.05\), \(t=0.3\)): with \(h^m_n\) from \(\exp(-z^2/4)(1-2c/z)^m\), the series is \(1.132365\), the corrected left side \(1.132365\)
(15 digits), the printed left side \(1.307699\). The text also omits the condition \(|2c|<|t|\) needed for the Laurent series.
Target: [M68.09.4.04].

### M68-E09.5.01. Factor \(\mu\) in (9.32)

Status: Confirmed.
Location: §9-5, p. 310, (9.32).
Printed: \(e^{-bc}\frac{(q)^{l/2}}{l!}H_l\big(\frac{-b}{2\sqrt q}\big)=\sum_{k=0}^\infty\frac{(\mu b)^k}{k!}R^k_{l-k}(\mu q,c)\).
Correct: \(e^{\mu bc}\frac{(-\mu q)^{l/2}}{l!}H_l\big(\frac{\mu b}{2(-\mu q)^{1/2}}\big)=\sum_{k=0}^\infty\frac{(\mu b)^k}{k!}R^k_{l-k}(\mu q,c)\); the printed left side is the case
\(\mu=-1\).
Evidence: by (9.30), \(\sum_k\frac{(\mu b)^k}{k!}R^k_{l-k}(\mu q,c)\) is the coefficient of \(z^l\) in \(e^{\mu qz^2}e^{\mu b(z+c)}\). Numerically (\(q=0.3\), \(b=0.7\),
\(c=0.4\)): for \(\mu=0.6\), \(l=1,2,3\) the right side is \(0.496833\), \(0.317264\), \(0.104037\), the corrected left side agrees, the printed left side
is \(-0.529049\), \(-0.041568\), \(0.115509\); for \(\mu=-1\) all three agree.
Target: [M68.09.5.01].

### M68-E09.5.02. Sign of \(t^{-1}\) in (9.37)

Status: Confirmed.
Location: §9-5, p. 311, (9.37).
Printed: \(H_k\Big(\frac{x+c(t+t^{-1})}{(1-t^2)^{1/2}}\Big)\).
Correct: \(H_k\Big(\frac{x+c(t-t^{-1})}{(1-t^2)^{1/2}}\Big)\).
Evidence: as for [M68-E09.4.03]. Numerically (\(x=0.6\), \(t=0.3\), \(c=0.05\)): for \(k=2\) the right side is \(-1.241145\), the corrected left side
\(-1.241145\), the printed left side \(0.762300\); for \(k=3\): \(-5.604480\), \(-5.604480\), \(-6.329562\).
Target: [M68.09.5.02].

### M68-E09.6.01. Normalization condition excludes \(\mathcal G_{1,1}\)

Status: Confirmed.
Location: §9-6, p. 312, lines 7–9 after Lemma 9.1.
Printed: "(1) \(p\) and \(q\) are relatively prime positive integers; (2) \(p\) is odd; and (3) if \(q\) is odd then \(p>q\)."
Correct: (3) if \(q\) is odd then \(p\ge q\).
Evidence: \(\mathcal G_{1,1}\cong\mathcal T_3\) is not isomorphic to any \(\mathcal G_{p,q}\) with \(p>q\) (the ratio of the \(\mathrm{ad}\,\mathcal J^3\) eigenvalues on the
derived algebra is \(-1\) only for \(p=q\)), yet the source uses \(G_{1,1}\cong T_3\) and the case \(p=q=1\) throughout §§9-7–9-11.
Target: [M68.09.6.01].

### M68-E09.11.01. The expansion (9.76) omits terms for \(p\ge2\)

Status: Confirmed.
Location: §9-11, pp. 322–323, the Laurent expansion of \(h\) "in \(t^p\)" and (9.76).
Printed: \(h(x,t)=\sum_{n=-\infty}^\infty h_n(x)t^{np}\) and (9.76) with only the terms \(I^{p,q}_{np}(x)t^{np}\).
Correct: \(h(x,t)=\sum_{j\in\mathbb Z}c_jI^{p,q}_j(x)t^j\) with \(pc_{j+p}=(m-j)c_j\); the coefficients \(c_{np}\) are as printed, and the coefficients on the
chains \(j\not\equiv0\pmod p\) are in general nonzero (their normalization is not determined by \(x=0\)). For \(p=1\) the printed (9.76) is correct.
Evidence: by (9.70) and (9.75), \(h\) is a power series in \(X^{1/p}=x(xt^p+p+q)^{q/p}t^{-q}\) times \((xt^p+p+q)^{m/p}\), so all powers \(t^{-qk}\) occur. For
\(p=3\), \(q=1\), \(m=0.4\), \(x=0.7\) the Laurent coefficients computed on \(|t|=0.6\) are \(0.8304099\) (\(t^0\)), \(0.01937472\) (\(t^3\)),
\(6.543849\cdot10^{-4}\) (\(t^{-3}\)), matching the printed coefficients, but also \(-0.0629914\) (\(t^{-1}\)), \(0.00124141\) (\(t\)),
\(-0.00514420\) (\(t^2\)), \(0.00886728\) (\(t^{-2}\)). The ratio test with \(I^{3,1}_j(0.7)\) confirms \(pc_{j+p}=(m-j)c_j\) on these chains. The step that
fails is the tacit assumption that \(h\) contains only powers \(t^{np}\).
Target: [M68.09.11.02].

### Conventions and notation (not errata)

- §9-4–§9-5: \(H_m(x)=2^{m/2}\exp(x^2/2)D_m(\sqrt2x)\) for complex \(m\) (Hermite functions); \(R^\rho_n\) is defined by its generating function
  (9.15), (9.30).
- §9-4, (9.17): the identity is stated after the substitution \(b\to2bc\) in the preceding group relation, without saying so.
- §9-8: \(n_l,s_l\) in (9.53) are the nonnegative solutions of \(l=n_lp-s_lq\) with \(n_l+s_l\) minimal.
- §9-10: (9.68) and the analytic continuation of \(I^{p,q}_m\) to complex \(m\) assume \(p\) odd and \(\mathrm{Re}\,r>0\); the principal branch of \(z^{-m-1}\) on
  the plane cut along the negative axis is used.
