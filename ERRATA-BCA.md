# Errata and source checks: Bluman–Cheviakov–Anco (2010)

Reference: George W. Bluman, Alexei F. Cheviakov and Stephen C. Anco, *Applications of
Symmetry Methods to Partial Differential Equations*, Applied Mathematical Sciences 168,
Springer, New York, 2010. The local copy is in [References](References/).
Synopsis: [SYNOPSIS-BCA](SYNOPSIS-BCA.md).

Locators use printed page numbers. To get the one-based PDF page number, add 19.

## Status vocabulary

- **Confirmed.** A contradiction is exhibited. It may be a direct calculation, a special case
  or counterexample, a numerical evaluation, a standard definition fixed in the source, or a
  conflict between two displays of the source.
- **Normalization check.** Two displays cannot both hold under one stated convention. An
  unstated change of basis, coordinate, sign or normalization may explain the difference. The
  synopsis fixes one convention and states the conversion.
- **Open check.** A suspected problem that is not settled. The entry states the uncertainty
  and the conjectured correction. Formalization is expected to decide it.

Each erratum gives:

- the status;
- the location, as section, printed page, equation, and line where useful (negative line
  numbers count from the bottom of the page);
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries.

Synopsis entries cite errata by id. An erratum id \(\mathrm{BCA\text{-}E}cc.s.nn\) is the
\(nn\)-th erratum located in section \(s\) of chapter \(cc\).

## Scope

These are observations about this edition, not an official publisher list. No claim is made
that formulas without an erratum are free of errors. Formulas that a synopsis marks "as
printed" were transcribed from the page images without an independent check. Corrected
formulas in the synopses are statements to be formalized. They are not Lean proofs.
Garbling of the PDF text layer is not an erratum; every erratum was checked on the page image.

Each chapter section ends with a list of conventions and notation that are not errata, for
example a sign convention for characteristics that differs from a modern reference.

## Summary by chapter

- Chapter 1. Local Transformations and Conservation Laws: 104 entries, 24 errata (Confirmed 22, Normalization check 2).
- Chapter 2. Construction of Mappings Relating Differential Equations: 33 entries, 9 errata (Confirmed 9).
- Chapter 3. Nonlocally Related PDE Systems: 43 entries, 15 errata (Confirmed 14, Open check 1).
- Chapter 4. Applications of Nonlocally Related PDE Systems: 33 entries, 14 errata (Confirmed 14).
- Chapter 5. Further Applications of Symmetry Methods: Miscellaneous Extensions: 34 entries, 11 errata (Confirmed 11).
- Total: 247 entries, 73 errata (Confirmed 70, Normalization check 2, Open check 1).

## Chapter 1. Local Transformations and Conservation Laws

### BCA-E01.2.01. Missing \(\varepsilon\) in the extended contact infinitesimal

Status: Confirmed.
Location: §1.2.2, p. 9, (1.16c).
Printed: \(u^*_i=u_i+\eta^{(1)}_i(x,u,\partial u)+O(\varepsilon^2)\).
Correct: \(u^*_i=u_i+\varepsilon\eta^{(1)}_i(x,u,\partial u)+O(\varepsilon^2)\).
Evidence: at \(\varepsilon=0\) the group element is the identity, so \(u^*_i=u_i\); the printed
form gives \(u^*_i=u_i+\eta^{(1)}_i\) at \(\varepsilon=0\). The companion displays (1.16a),
(1.16b) carry the factor \(\varepsilon\).
Target: [BCA.01.2.04].

### BCA-E01.2.02. Sign of the contact generator built from a characteristic function

Status: Confirmed.
Location: §1.2.4, p. 15, Theorem 1.2.5, (1.43).
Printed: an evolutionary generator \(W(x,u,\partial u)\partial_u\) is equivalent to the contact
generator with \(\xi^j=\partial W/\partial u_j\), \(\eta=u_i\partial W/\partial u_i-W\),
\(\eta^{(1)}_j=-\partial_{x^j}W-u_j\partial_uW\).
Correct: the evolutionary component of the printed field is \(\eta-\xi^ju_j=-W\), so it is
equivalent to \(-W\partial_u\). The contact generator equivalent to \(W\partial_u\) in the
sense of (1.31) is \(\xi^j=-\partial W/\partial u_j\), \(\eta=W-u_i\partial W/\partial u_i\),
\(\eta^{(1)}_j=\partial_{x^j}W+u_j\partial_uW\).
Evidence: take \(W=-u_x\) (one independent variable). The printed formulas give
\(\xi=-1\), \(\eta=0\), i.e. the generator \(-\partial_x\), whose evolutionary form (1.31) is
\(\eta-\xi u_x=+u_x\), not \(W=-u_x\). The source's own use of the theorem in (2.119)
(p. 152) takes \(\xi=-F_{u_x}\), \(\tau=-F_{u_t}\), \(\eta=F-u_xF_{u_x}-u_tF_{u_t}\) for the
evolutionary generator \(F\partial_u\), which is the corrected form.
Target: [BCA.01.2.10].

### BCA-E01.2.03. Equivalence transformations of the potential nonlinear diffusion system

Status: Confirmed.
Location: §1.2.6, p. 24, (1.70).
Printed: \(\tilde v=a_5a_7v+a_3x+a_4\) and \(\tilde K(\tilde u)=(a_5^2/a_6)K(u)\), with
\(\tilde t=a_5t+a_1\), \(\tilde x=a_6x+a_2\), \(\tilde u=a_7u+a_3\).
Correct: \(\tilde v=a_6a_7v+a_3a_6x+a_4\) and
\(\tilde K(\tilde u)=(a_6^2/a_5)K((\tilde u-a_3)/a_7)\).
Evidence: the system is \(v_x=u\), \(v_t=K(u)u_x\). (1) Take \(a_5=2\), all other scale factors
1 and shifts 0, \(K\equiv1\), and the solution \(u\equiv1\), \(v=x\). The printed map gives
\(\tilde v=2\tilde x\) but \(\tilde u=1\), so \(\tilde v_{\tilde x}\ne\tilde u\). (2) Take
\(a_6=2\), \(a_3=1\), other scale factors 1. Then
\(\tilde v_{\tilde x}=\tfrac12v_x=(u+1)/2\) under the printed map, but \(\tilde u=u+1\). With
the corrected formulas both equations transform covariantly: \(\tilde v_{\tilde x}=a_7u+a_3
=\tilde u\) and \(\tilde v_{\tilde t}=(a_6a_7/a_5)Ku_x=\tilde K\tilde u_{\tilde x}\). The
companion (1.71) checks out.
Target: [BCA.01.2.20].

### BCA-E01.2.04. Order of the product defining \(\mathcal R_5\) for Burgers' equation

Status: Confirmed.
Location: §1.2.8, p. 31, statement after (1.107).
Printed: \(\mathcal R_5=\mathcal R_2\mathcal R_3\).
Correct: \(\mathcal R_5=\mathcal R_3\mathcal R_2=\mathcal R_2\mathcal R_3-\tfrac12\).
Evidence: with \(\mathcal R_2=D_x-\tfrac12u_x\) and
\(\mathcal R_3=tD_x+\tfrac12(x-tu_x)\), \([\mathcal R_2,\mathcal R_3]=\tfrac12\) (the only
nonzero contribution is \(D_x(\tfrac12x)\)). Expanding \(\mathcal R_3\mathcal R_2\) reproduces the
printed \(\mathcal R_5=\tfrac14(tu_x^2-xu_x-2tu_{xx})+(\tfrac12x-tu_x)D_x+tD_x^2\), while
\(\mathcal R_2\mathcal R_3\) differs from it by \(+\tfrac12\).
Target: [BCA.01.2.26].

### BCA-E01.2.05. Coefficient of the nonlocal term in the KdV recursion operator

Status: Confirmed.
Location: Exercise 1.2.15, p. 37, (1.129).
Printed: \(\mathcal R=D_x^2+\tfrac23u+u_xD_x^{-1}\) (coefficient 1 on \(u_xD_x^{-1}\)).
Correct: \(\mathcal R=D_x^2+\tfrac23u+\tfrac13u_xD_x^{-1}\).
Evidence: for \(u_t+uu_x+u_{xxx}=0\) and the printed operator,
\(\mathcal Ru_x=u_{xxx}+\tfrac53uu_x\). Its linearized-equation residual on solutions is
\(2u_xu_{xxx}+2u_{xx}^2\ne0\), so it is not a symmetry. With coefficient \(\tfrac13\),
\(\mathcal Ru_x=u_{xxx}+uu_x=-u_t\), and \(\mathcal R^2u_x\) is the fifth-order symmetry (1.45)
times \(\tfrac53\).
Target: [BCA.01.2.34].

### BCA-E01.3.01. Flux decay does not suffice for conservation of the integral

Status: Confirmed.
Location: §1.3.1, p. 39, Theorem 1.3.1.
Printed: if \(D_t\Psi+\mathrm{div}\,\Phi=0\) on \(\mathbb R^n\) and the flux \(\Phi\) vanishes as
\(|x|\to\infty\), then \(\frac{d}{dt}\int_{\mathbb R^n}\Psi\,dx=0\).
Correct: one needs the boundary flux \(\oint_{|x|=R}\Phi\cdot\mathbf n\,dS\) to tend to zero as
\(R\to\infty\) (e.g. \(|\Phi|=o(|x|^{1-n})\)), together with integrability of \(\Psi\) and
\(D_t\Psi\) to justify differentiating under the integral.
Evidence: on \(\mathbb R^2\), \(\Phi=(x,y)/(1+r^2)\), \(\Psi=-2t/(1+r^2)^2\). Then
\(\mathrm{div}\,\Phi=2/(1+r^2)^2=-D_t\Psi\), \(\Phi\to0\) at infinity, but
\(\int\Psi\,dx=-2\pi t\) is not constant; the flux through the circle of radius \(R\) is
\(2\pi R^2/(1+R^2)\to2\pi\).
Target: [BCA.01.3.02].

### BCA-E01.3.02. Multiplier for the momentum law of the Euler equations

Status: Confirmed.
Location: §1.3.1, pp. 40–41, (1.138).
Printed: the momentum law arises by multiplying (1.135b) by \(\rho v^i\).
Correct: the multipliers are \(v^i\) for (1.135a) and \(1\) for (1.135b) (in the source's form
(1.135b) already contains the factor \(\rho\)).
Evidence: \(v^i(D_t\rho+D_j(\rho v^j))+\rho(D_t+v^jD_j)v^i+D_ip=D_t(\rho v^i)+D_j(\rho v^iv^j+
p\delta^{ij})\) identically; with the factor \(\rho v^i\) on (1.135b) the pressure term becomes
\(\rho v^iD_ip\), which is not a divergence in general, and the sum is not the momentum law.
Target: [BCA.01.3.03].

### BCA-E01.3.03. Construction of the angular momentum law

Status: Confirmed.
Location: §1.3.1, p. 41, text after (1.139) (Exercise 1.3.1).
Printed: the angular momentum law is obtained from (1.135a) twice, using \(\mathbf v\).
Correct: multiply (1.135a) by \(\mathbf x\times\mathbf v\) and take the cross product of
\(\mathbf x\) with (1.135b).
Evidence: \((\mathbf x\times\mathbf v)\,(D_t\rho+\mathrm{div}(\rho\mathbf v))+\mathbf x\times
(\rho(D_t+\mathbf v\cdot\nabla)\mathbf v+\nabla p)=D_t\mathbf m+D_j(v^j\mathbf m)+\mathbf x
\times\nabla p\), with \(\mathbf m=\mathbf x\times\rho\mathbf v\), and \(\mathbf x\times\nabla p=
-\mathrm{curl}(p\mathbf x)\) is a divergence; (1.135b) does not enter the printed recipe.
Target: [BCA.01.3.03].

### BCA-E01.3.04. Flux of the fourth KdV conservation law

Status: Confirmed.
Location: §1.3.1, p. 42, (1.143).
Printed: the flux lacks the term \(\tfrac5{18}u^3u_{xx}\) and has \(-\tfrac5{12}u^2u_x^2\).
Correct: \(\Phi=\tfrac1{18}u^5+\tfrac5{18}u^3u_{xx}-\tfrac54u^2u_x^2+\tfrac56u_x^2u_{xx}
+\tfrac43uu_{xx}^2-\tfrac53uu_xu_{xxx}-\tfrac12u_{xxx}^2+u_{xx}u_{xxxx}\) for the density
\(\tfrac5{72}u^4-\tfrac56uu_x^2+\tfrac12u_{xx}^2\).
Evidence: on solutions of \(u_t=-uu_x-u_{xxx}\), \(D_t(\text{density})+D_x\Phi\) vanishes for
the corrected \(\Phi\); for the printed flux the residual is
\(\tfrac5{18}u(-u^2u_{xxx}+3uu_xu_{xx}+6u_x^3)\ne0\).
Target: [BCA.01.3.04].

### BCA-E01.3.05. Flux of the KdV centre-of-mass law

Status: Confirmed.
Location: §1.3.1, p. 42, (1.144).
Printed: the flux of the density \(\tfrac12tu^2-xu\) lacks the term \(\tfrac13tu^3\).
Correct: \(\Phi=\tfrac13tu^3-\tfrac12xu^2+tuu_{xx}-\tfrac12tu_x^2-xu_{xx}+u_x\).
Evidence: with the printed flux the residual \(D_t\Psi+D_x\Phi\) on solutions is
\(-tu^2u_x\), which is the \(x\)-derivative of the missing \(-\tfrac13tu^3\).
Target: [BCA.01.3.04].

### BCA-E01.3.06. Order of the fluxes of a divergence

Status: Confirmed.
Location: §1.3.3, p. 45, Theorem 1.3.2; also Exercise 1.3.3.
Printed: if \(F(x,U,\ldots,\partial^sU)\) is annihilated by the Euler operators, then
\(F=D_i\Psi^i\) with \(\Psi^i\) of order \(s-1\).
Correct: for \(n=1\) the order \(s-1\) holds; for \(n\ge2\) the fluxes can in general only be
chosen of order \(\le s\).
Evidence: for \(n=2\), \(F=U_{xx}U_{yy}-U_{xy}^2=D_x(U_xU_{yy})-D_y(U_xU_{xy})\) has order 2,
but \(D_i\Psi^i\) with first-order \(\Psi^i\) is affine in the second derivatives, while \(F\) is
quadratic in them.
Target: [BCA.01.3.08].

### BCA-E01.3.07. Sign of the fifth multiplier set of the telegraph system

Status: Confirmed.
Location: §1.3.5, p. 51, (1.164)–(1.167).
Printed: the fifth multiplier set \((\xi_5,\varphi_5)=(e^{x+\frac12U^2-V},-Ue^{x+\frac12U^2-V})\)
corresponds to the conservation law \(D_t[e^{x+\frac12u^2-v}]+D_x[ue^{x+\frac12u^2-v}]=0\).
Correct: with \(F=e^{x+\frac12U^2-V}\),
\(D_tF+D_x(UF)\equiv-(\xi_5R^1+\varphi_5R^2)\), so the displayed law is the characteristic form
of \((-\xi_5,-\varphi_5)\) (equivalently, flip both signs of the density and flux).
Evidence: (1.165)–(1.166) require \(\Psi_V=\xi\); for \(\Psi=F\) one has \(\Psi_V=-F=-\xi_5\).
Direct expansion with \(R^1=v_t-(u^2+1)u_x-u\), \(R^2=u_t-v_x\) gives the sign.
Target: [BCA.01.3.15].

### BCA-E01.3.08. Which KdV laws the multipliers \(\Lambda_1,\Lambda_2,\Lambda_3\) give

Status: Confirmed.
Location: §1.3.5, p. 53, text after (1.173).
Printed: \(\Lambda_1=1\), \(\Lambda_2=U\), \(\Lambda_3=tU-x\) yield (1.142a)–(1.142c).
Correct: \(\Lambda_1\) and \(\Lambda_2\) yield (1.142a), (1.142b); \(\Lambda_3=tU-x\) yields the
centre-of-mass law (1.144); the energy law (1.142c) comes from \(\Lambda_4=U_{xx}+\tfrac12U^2\).
Evidence: \((tU-x)(U_t+UU_x+U_{xxx})\) is the divergence of the density \(\tfrac12tU^2-xU\) of
(1.144) and its flux; the density of (1.142c) is cubic in \(U\), which a multiplier linear in
\(U\) cannot produce.
Target: [BCA.01.3.16].

### BCA-E01.3.09. Second multiplier determining equation of the wave-speed equation

Status: Confirmed.
Location: §1.3.8, p. 66, (1.228).
Printed: \(2\Lambda_U+\hat D_t\Lambda_{U_t}-D_x\Lambda_{U_t}=0\).
Correct: \(2\Lambda_U+\hat D_t\Lambda_{U_t}-D_x\Lambda_{U_x}=0\).
Evidence: decomposing \(E_U(\Lambda R)\) for \(R=U_{tt}-U^2U_{xx}-UU_x^2\) by direct computation
for \(\Lambda=U-xU_x\) and \(\Lambda=xU_tU_x+U^2U_t\) gives the corrected coefficient
\(\Lambda_{U_x}\) in the \(D_x\) term; for \(\Lambda=xU_tU_x+U^2U_t\) the printed and corrected
left sides differ by \(D_x(xU_x+U^2-xU_t)\ne0\). The source's conclusion is unaffected: for
the scaling \(\Lambda=U-xU_x\) the corrected left side equals 3.
Target: [BCA.01.3.29].

### BCA-E01.4.01. Flux in the proof of Theorem 1.4.6

Status: Confirmed.
Location: §1.4.3, p. 76, proof of Theorem 1.4.6, (1.261).
Printed: \(A^i=-D_i(L[U]\xi^i(x,U))\).
Correct: \(A^i=-L[U]\xi^i(x,U)\) (no sum over \(i\)).
Evidence: a point symmetry of the action satisfies \(LD_i\xi^i+X^{(k)}L\equiv0\), and by
Theorem 1.4.2 \(\hat X^{(k)}L=X^{(k)}L+LD_i\xi^i-D_i(L\xi^i)=-D_i(L\xi^i)\); hence
\(\hat X^\infty L=D_iA^i\) with \(A^i=-L\xi^i\). The printed \(A^i\) are scalars already
differentiated, and \(D_iA^i\) would be a second-order expression.
Target: [BCA.01.4.07].

### BCA-E01.4.02. Sign normalization of the Klein–Gordon example

Status: Normalization check.
Location: §1.4.5, pp. 79–82, (1.268)–(1.275).
Printed: \(R[u]=u_{tx}+g(u)\) (1.268) and \(L[U]=-\tfrac12U_tU_x+h(U)\) (1.270), \(h'=g\); but
(1.272a)–(1.273c), the \(A^i\), and the text ("\(u_{tx}-u^n=0\)", "\(U_{tx}-U^n\)") use the
opposite sign.
Correct: the synopsis fixes \(R[u]=u_{tx}-g(u)\) and \(L[U]=-\tfrac12U_tU_x-h(U)\), which is
consistent with (1.272)–(1.273) and the power case \(u_{tx}=u^n\). The conversion is
\(g\mapsto-g\), \(h\mapsto-h\). (1.275) as printed, \(E_U(\hat X_4L)=2(U_{xt}+U^n)\), belongs to
the \(+g\) convention; in the fixed convention it reads \(2(U_{xt}-U^n)\).
Evidence: with \(L=-\tfrac12U_tU_x-h\), \(E_U(L)=U_{tx}-g(U)\); the variational identities
\(\hat X_1^\infty L=-D_t(\tfrac12U_tU_x+h)\), etc., and the conservation laws
\(D_t(h)-D_x(\tfrac12u_t^2)=0\), etc., hold only in this convention. For \(g=U^n\),
\(E_U((U-(1-n)xU_x)(U_{tx}-U^n))=2(U_{tx}-U^n)\) by direct computation.
Target: [BCA.01.4.09], [BCA.01.4.10].

### BCA-E01.4.03. Table 1.1: the extra multiplier for \(n=1\)

Status: Confirmed.
Location: §1.4.5, p. 83, Table 1.1, row \(n=1\).
Printed: additional multiplier \(\Lambda_4[U]=\tfrac12U^2+U_{xx}\); the "Arbitrary" row also lists
\(\hat\eta_2\) twice.
Correct: for \(n=1\), \(\Lambda_3=U^2+2U_{xx}\), so \(\tfrac12U^2+U_{xx}=\tfrac12\Lambda_3\) is
not
additional. The additional multiplier is \(\Lambda_4=tU-x\) (the counterpart of the symmetry
\(\hat\eta_4=tu_x-1\)).
Evidence: \((tU-x)(U_t+UU_x+U_{xxx})=D_t(\tfrac12tU^2-xU)+D_x(\tfrac13tU^3-\tfrac12xU^2+tUU_{xx}
-\tfrac12tU_x^2-xU_{xx}+U_x)\) identically (BCA-E01.3.05); this multiplier is not in the span of
\(1,U,U^2+2U_{xx}\).
Target: [BCA.01.4.11].

### BCA-E01.4.04. Exponent in the Lagrangian of the potential generalized KdV equation

Status: Confirmed.
Location: §1.4.5, p. 83, (1.280).
Printed: \(L[V]=\tfrac12V_{xx}^2-\frac1{(n+1)(n+2)}V_x^{n+3}-\tfrac12V_xV_t\).
Correct: \(L[V]=\tfrac12V_{xx}^2-\frac1{(n+1)(n+2)}V_x^{n+2}-\tfrac12V_xV_t\).
Evidence: \(E_V\) of the corrected Lagrangian is \(v_{xxxx}+v_x^nv_{xx}+v_{xt}\) (checked for
\(n=1,2,3\)); for \(n=1\) it reduces to the KdV potential Lagrangian (1.267). With exponent
\(n+3\) the nonlinear term is \(\frac{n+3}{n+1}v_x^{n+1}v_{xx}\).
Target: [BCA.01.4.12].

### BCA-E01.4.05. Equivalence transformation of the potential variable of the telegraph system

Status: Confirmed.
Location: §1.4.5, p. 85, (1.287).
Printed: \(\tilde v=a_3v+a_2a_7t+a_8\).
Correct: \(\tilde v=a_1a_2^{-1}a_3v+a_2a_7t+a_8\).
Evidence: the system is \(u_t=v_x\), \(v_t=F(u)u_x+G(u)\). Take \(F=1\), \(G=0\), \(a_1=2\),
all other parameters trivial. Then \(\tilde x=2x\), and \(\tilde u_{\tilde t}=u_t\) while the
printed \(\tilde v=v\) gives \(\tilde v_{\tilde x}=v_x/2\), so the first equation is not
preserved. With the factor \(a_1a_3/a_2\) both equations transform covariantly, and the printed
\(\tilde F=(a_1^2/a_2^2)F\), \(\tilde G=(a_1a_3/a_2^2)G+a_7\) are consistent with it.
Target: [BCA.01.4.13].

### BCA-E01.4.06. Self-adjointness of the Boussinesq system as written

Status: Normalization check.
Location: Exercise 1.4.6(a), p. 88, (1.290).
Printed: "Show that the linearized system of (1.290) is self-adjoint."
Correct: for \(R^1=u_t-v_{xx}\), \(R^2=v_t-u_{xx}+u+u^2\) ordered as written, the linearization
has \((1,1)\) entry \(D_t\) and adjoint entry \(-D_t\), so it is not self-adjoint. It is
self-adjoint after pairing \(R^2\) with \(u\) and \(-R^1\) with \(v\), i.e. for the system
\((R^2,-R^1)\).
Evidence: the linearization of \((R^2,-R^1)\) is
\(\begin{pmatrix}-D_x^2+1+2u & D_t\\ -D_t & D_x^2\end{pmatrix}\), which equals its formal adjoint.
The multipliers \(\Lambda_1,\Lambda_2\) of part (c) refer to the source's ordering.
Target: [BCA.01.4.17].

### BCA-E01.5.01. Recursion for the iterated symmetry matrices

Status: Confirmed.
Location: §1.5.1, p. 98, (1.317).
Printed: \(a^\sigma_\tau[U]_{k+1}=Xa^\sigma_\tau[U]_k+a^\lambda_\tau[U]_ka^\sigma_\lambda[U]\),
i.e.
\(A_{k+1}=XA_k+AA_k\) in matrix form (rows \(\sigma\)).
Correct: \(A_{k+1}=XA_k+A_kA\), i.e.
\(a^\sigma_\tau[U]_{k+1}=Xa^\sigma_\tau[U]_k+a^\sigma_\lambda[U]_ka^\lambda_\tau[U]\).
Evidence: from \(X^kR=A_kR\), \(X^{k+1}R=(XA_k)R+A_kXR=(XA_k+A_kA)R\). The printed
\(A_3=XA_2+AA_2\) differs from the correct \(XA_2+A_2A\) by \([A,XA]\). Example: let
\(\tilde R\) be any system not depending explicitly on \(x\), \(X=\partial_x\), and
\(R=M(x)\tilde R\) with \(M=\begin{pmatrix}e^x&x\\0&1\end{pmatrix}\). Then \(XR=AR\) with
\(A=M'M^{-1}=\begin{pmatrix}1&1-x\\0&0\end{pmatrix}\), \(XA=\begin{pmatrix}0&-1\\0&0
\end{pmatrix}\) and \([A,XA]=\begin{pmatrix}0&-1\\0&0\end{pmatrix}\ne0\).
Target: [BCA.01.5.04].

### BCA-E01.5.02. Sign of a trivial density

Status: Confirmed.
Location: §1.5.2, p. 109, example after Theorem 1.5.4.
Printed: \(\Psi=-e^x[u^{\alpha+1}u_t+vv_t]=D_x(e^xu^{\alpha+1}v)\),
\(\Phi=e^xu^\alpha[(\alpha+1)vu_t+uv_t]=D_t(e^xu^{\alpha+1}v)\).
Correct: on solutions of \(u_t=v_x\), \(v_t=(\alpha+1)u^\alpha u_x+u^{\alpha+1}\),
\(\Psi=-D_x(e^xu^{\alpha+1}v)\) (and \(\Phi=D_t(e^xu^{\alpha+1}v)\)), so
\(D_t\Psi+D_x\Phi=0\) holds as a trivial law.
Evidence: \(D_x(e^xu^{\alpha+1}v)=e^x[u^{\alpha+1}v+(\alpha+1)u^\alpha u_xv+u^{\alpha+1}v_x]
=e^x[vv_t+u^{\alpha+1}u_t]\) on solutions; with the printed sign, \(D_t\Psi+D_x\Phi=
2D_tD_x(e^xu^{\alpha+1}v)\ne0\).
Target: [BCA.01.5.09].

### BCA-E01.5.03. Flux formula for noncritical scaling-homogeneous laws

Status: Confirmed.
Location: §1.5.2, p. 111, Theorem 1.5.5, (1.364).
Printed: \(\Psi^i[U]=(P-p_i)\Phi^i[U]\) modulo trivial fluxes.
Correct: \(\Psi^i[U]=\chi\,\Phi^i[U]\) modulo trivial fluxes, with
\(\chi=P+\sum_jp^{(j)}\), the same constant for all \(i\) (as the proof (1.372) shows).
Evidence: heat equation \(R=U_t-U_{xx}\), \(\Lambda=1\) (law \(D_t(u)+D_x(-u_x)=0\)), scaling
\(2t\partial_t+x\partial_x\), so \(p_t=2\), \(p_x=1\), \(r=-2\), \(s=0\), \(P=-2\), \(\chi=1\).
The printed factors give \((P-p_t)u=-4u\) and \((P-p_x)(-u_x)=3u_x\), whose divergence
\(-4u_t+3u_{xx}=-u_{xx}\ne0\) on solutions; the flux (1.179) with \(V=\hat\eta_s\),
\(W=1\) is \((u,-u_x)\) modulo trivial terms, i.e. factor \(\chi=1\).
Target: [BCA.01.5.11].

### BCA-E01.5.04. Point symmetries of the potential wave system with variable speed

Status: Confirmed.
Location: Exercise 1.5.6(c), p. 115, (1.381).
- Printed (with \(q=c/c'\)): \(X^\pm=\pm2e^{\pm t}q\partial_x+2e^{\pm t}(q'-1)\partial_t
\pm e^{\pm t}(2-q')u\partial_u-e^{\pm t}qv\partial_v\), for \(cc'q''=1\).
Correct: \(X^\pm=\pm2e^{\pm t}q\partial_x+2e^{\pm t}(q'-1)\partial_t+[\pm e^{\pm t}(2-q')u
-e^{\pm t}qv]\partial_u+[\mp e^{\pm t}q'v-e^{\pm t}(cc')^{-1}u]\partial_v\).
Evidence: for \(v_t-u_x=0\), \(v_x-c^{-2}u_t=0\), the linearized equations applied to the
characteristics of the corrected generators vanish on solutions after using \(cc'q''=1\)
(symbolic computation with \(c\) arbitrary). For the printed \(X^+\) the residual of the
first linearized equation \(D_tQ^v-D_xQ^u\) on solutions is
\(e^t[u/(cc')-qv+(1-q-cc''/c'^2)u_x]\ne0\).
Target: [BCA.01.5.15].

### Conventions and notation (not errata)

- Characteristic sign: the source's contact characteristic function \(W=\xi^iu_i-\eta\) (1.19)
  is the negative of the evolutionary component \(\hat\eta=\eta-\xi^iu_i\) (1.31); entries state
  which is meant.
- p. 27: "PDE (1.84)" in the statement on recursion operators for the heat equation should read
  (1.85).
- p. 58: "determining equations (1.150)" should read (1.151).
- p. 63: "PDE (1.141)" in the self-adjointness discussion should read (1.219).
- p. 83: "since \(\Lambda_1[V]=\hat\eta_i[V]\)" should read \(\Lambda_i[V]=\hat\eta_i[V]\).
- pp. 91–92, (1.294), (1.296): \(z=(z^1,\ldots,z^m)\) should read \(z=(z^1,\ldots,z^n)\).
- p. 106: "sgXR\(^2\)" is a typesetting slip for \(XR^2\).
- p. 98, (1.317)–(1.319): \(X\) denotes the infinitely prolonged generator.
- Throughout §1.3 the multiplier determining equations hold "for arbitrary \(U\)"; the source
  writes \(\Lambda[U]\) for multipliers and \(\Lambda[u]\) for their values on solutions.

## Chapter 2. Construction of Mappings Relating Differential Equations

### BCA-E02.3.01. Projective symmetry of Burgers' equation

Status: Confirmed.
Location: §2.3.1, p. 129, (2.20).
Printed: \(Z_4=xt\partial_x+t^2\partial_t-[x-tw]\partial_w\).
Correct: \(Z_4=xt\partial_x+t^2\partial_t+[x-tw]\partial_w\).
Evidence: for \(w_t=w_{xx}-ww_x\), the characteristic \(Q=\omega-xtw_x-t^2w_t\) must satisfy
\(D_tQ=D_x^2Q-wD_xQ-w_xQ\) on solutions. With \(\omega=-(x-tw)\) the residual is
\(2w_x(tw-x)\ne0\); with \(\omega=x-tw\) it vanishes. The mapping equation (2.23d) on p. 131
uses the corrected sign (right side \(x-t\psi\)).
Target: [BCA.02.3.01].

### BCA-E02.3.02. Mapping equation for the Galilean symmetry

Status: Confirmed.
Location: §2.3.1, p. 131, (2.23e).
Printed: \(t\psi_x-\tfrac12tu\psi_u-\tfrac12[u+xu_x]\psi_{u_x}-[u_x+\tfrac12xu_t]\psi_{u_t}=1\).
Correct: \(t\psi_x-\tfrac12xu\psi_u-\tfrac12[u+xu_x]\psi_{u_x}-[u_x+\tfrac12xu_t]\psi_{u_t}=1\).
Evidence: \(X_5=t\partial_x-\tfrac12xu\partial_u\) (2.19) and its prolongation on p. 131. The
third equation of (2.24), \(1+\tfrac12u\psi_{u_x}+u_x\psi_{u_t}=0\), follows from (2.23e) by
subtracting \(\tfrac12x\) times (2.23f) only with the coefficient \(\tfrac12xu\).
Target: [BCA.02.3.02].

### BCA-E02.3.03. Parameter value of Zal'mez's transformation

Status: Confirmed.
Location: §2.3.2, p. 137, sentence after (2.55).
Printed: "Zal'mez's transformation (2.33) corresponds to the special case \(\lambda=2\)."
Correct: (2.33) is the case \(\lambda=-2\) of (2.55). The case \(\lambda=2\) gives
\(\tilde z^1=-xt^{-1/2}\), \(\tilde z^2=2t^{-1/2}\), \(\tilde w=tu-\tfrac12x\), which differs from
(2.33) by the KdV symmetry \((z^1,z^2)\mapsto(-z^1,-z^2)\).
Evidence: substituting \(\lambda=-2\) in (2.55): \(\tilde z^1=t^{-1/2}x\),
\(\tilde z^2=\tfrac14(-8)t^{-1/2}=-2t^{-1/2}\), \(\tilde w=-\tfrac12(x-2tu)=tu-\tfrac12x\),
which is (2.33).
Target: [BCA.02.3.05].

### BCA-E02.4.01. Superposition symmetries do not determine the target equation

Status: Confirmed.
Location: §2.4.1, pp. 142–143, Theorem 2.4.2 and its proof; the same argument in Theorem 2.4.4
(pp. 150–151) and in the scalar use of Theorems 2.4.1–2.4.2 (p. 147).
Printed: if the hypotheses on (2.70)–(2.71) hold, the map \(z=X\), \(w=\psi\) transforms
\(\mathbf R\) to a linear system \(L[z]w=g(z)\), because "only a linear system of the form (2.73)
can be characterized as having a point symmetry of the form (2.74)".
Correct: the map is invertible and carries the symmetries to \(f^\gamma(z)\partial_{w^\gamma}\),
\(L[z]f=0\), but the transformed system need not be \(L[z]w=g\). An additional hypothesis is
needed, for example that the transformed system is equivalent to \(L[z]w=g\) (same number of
equations and orders, solved for corresponding leading derivatives); the precise sufficient
condition is an open item.
Evidence: the system \(u_{xx}=u_x^2\), \(v_{xx}=v_x^2\) (independent variables \(x,t\)) admits
\(f(t)\partial_u+g(t)\partial_v\) for all \(f,g\), i.e. \(F=(f,g)\) ranges over the solutions of
\(L F=0\) with \(L=D_xI_2\) in \(X=(x,t)\). Here \(\alpha=0\), \(\beta=I\); (2.70) has the
functionally independent solutions \(X^1=x\), \(X^2=t\), and (2.71) has the solution
\(\psi=(u,v)\). The resulting map is the identity, and the system is not of the form
\(w_x=g(z)\): the solutions \(u=-\log|a(t)x+b(t)|\) have non-constant \(u_x\). The scalar
equation \(u_{xx}=u_x^2\) with \(f(t)\partial_u\) is a counterexample for the \(m=1\) point
version and for Theorem 2.4.4.
Target: [BCA.02.4.03], [BCA.02.4.08].

### BCA-E02.4.02. Right-hand side of the system for the derivative components

Status: Confirmed.
Location: §2.4.2, p. 150, Theorem 2.4.4(iii), (2.111), first line.
Printed: \(\alpha^i\partial_{x^i}\Psi_j+\beta\partial_u\Psi_j+\lambda_i\partial_{u_i}\Psi_j=1\).
Correct: the right-hand side is \(0\).
Evidence: by (2.107c) and (2.108), \(X\psi_j=f(\alpha^i\partial_{x^i}\psi_j+\beta\partial_u\psi_j+
\lambda_i\partial_{u_i}\psi_j)+f_k(\alpha^{ik}\partial_{x^i}\psi_j+\cdots)\) must equal
\(\partial f/\partial z^j\) for every solution \(f\), so the coefficient of \(f\) vanishes. In the
Legendre example (\(\beta=1\), \(\alpha^i=\lambda_i=0\), \(\psi_1=-x\), \(\psi_2=-t\)) the first
line
reads \(\partial_u\psi_j=0\), not \(1\).
Target: [BCA.02.4.08].

### BCA-E02.4.03. Coefficients of the Legendre-linearized equation

Status: Confirmed.
Location: §2.4.2, pp. 152–153, (2.118) and (2.126).
Printed: \(aF_{pp}-2bF_{pq}+cF_{qq}=0\) and \(a w_{z^1z^1}-2bw_{z^1z^2}+cw_{z^2z^2}=0\), for
\(au_{xx}+2bu_{xt}+cu_{tt}=0\) with \(p=u_x\), \(q=u_t\).
Correct: \(cF_{pp}-2bF_{pq}+aF_{qq}=0\) and \(c\,w_{z^1z^1}-2b\,w_{z^1z^2}+a\,w_{z^2z^2}=0\)
(\(a\) and \(c\) interchanged).
Evidence: the Legendre transformation inverts Hessians:
\(w_{pp}=-u_{tt}/\Delta\), \(w_{pq}=u_{xt}/\Delta\), \(w_{qq}=-u_{xx}/\Delta\) with
\(\Delta=u_{xx}u_{tt}-u_{xt}^2\). Hence \(cw_{pp}-2bw_{pq}+aw_{qq}=-(au_{xx}+2bu_{xt}+cu_{tt})/
\Delta\), while the printed combination equals \(-(cu_{xx}+2bu_{xt}+au_{tt})/\Delta\). A symbolic
check of the symmetry condition for \(F(u_x,u_t)\partial_u\) with arbitrary \(a,b,c\) leaves a
nonzero residual for (2.118) as printed and none for the corrected equation.
Target: [BCA.02.4.09].

### BCA-E02.4.04. Exponential factor of the potential Burgers symmetries

Status: Confirmed.
Location: Exercise 2.4.4(a), p. 156.
Printed: \(X=e^{u^2/4}\{[2g_x+ug]\partial_u+4g\partial_v\}\).
Correct: \(X=e^{v/4}\{[2g_x+ug]\partial_u+4g\partial_v\}\), \(g_t=g_{xx}\).
Evidence: for \(v_x=2u\), \(v_t=2u_x-u^2\), \(\varphi=e^{-v/4}\) solves
\(\varphi_t=\varphi_{xx}\),
and \(v\mapsto v+4\varepsilon ge^{v/4}\) shifts \(\varphi\) by \(-\varepsilon g\); the
\(u\)-component
\(\tfrac12D_x(4ge^{v/4})=e^{v/4}(2g_x+ug)\). With \(g=1\) and the printed factor, the linearized
first equation gives \(D_x(4e^{u^2/4})-2ue^{u^2/4}=2u(u_x-1)e^{u^2/4}\ne0\).
Target: [BCA.02.4.11].

### BCA-E02.5.01. Linearization of the Riccati equation (2.190)

Status: Confirmed.
Location: §2.5.1, p. 166, lines 3–5.
Printed: "the Riccati transformation \(M=2Y'/Y\) maps any solution of \(Y''-4q_2(y)Y=0\) to a
solution of (2.190)".
Correct: \(M=-2Y'/Y\) with \(Y''+4q_2(y)Y=0\).
Evidence: for \(M=-2Y'/Y\), \(2M'-M^2=-4Y''/Y\), which equals \(16q_2\) iff
\(Y''+4q_2Y=0\). For \(q_2=0\) and \(Y=y\) the printed recipe gives \(M=2/y\), with
\(2M'=-4/y^2\ne M^2=4/y^2\).
Target: [BCA.02.5.03].

### BCA-E02.5.02. Conformal weight in the biharmonic symmetries and mappings

Status: Confirmed.
Location: §2.5.2, pp. 169–170, (2.203b) and (2.209b).
Printed: \(u^*=|dz^*/dz|^{-1}u\) and \(G(x,y)=|d\zeta/dz|^{-1}\).
Correct: \(u^*=|dz^*/dz|\,u\) and \(G(x,y)=|d\zeta/dz|\).
Evidence: (1) \(X_1\) generates \(z^*=z+\varepsilon z^2+O(\varepsilon^2)\), so
\(|dz^*/dz|=1+2\varepsilon x+O(\varepsilon^2)\), and its \(u\)-component \(2xu\) gives
\(u^*=(1+2\varepsilon x)u\). (2) For the inversion \(z^*=1/z\), the biharmonic Kelvin transform
is \(|z^*|^2u(1/z^*)=|dz^*/dz|u\); with the printed weight \(u\equiv1\) goes to \(|z^*|^{-2}\),
and \(\Delta^2(r^{-2})=64r^{-6}\ne0\). (3) For \(\zeta=A^{-1}\log(1+Az)\), numerical evaluation of
the left side of (2.211) at \((z^1,z^2)=(0.3,-1/7)\) with \(u=x^2+y^2\): zero for
\(G=|d\zeta/dz|\), about \(157.41\) (\(A=1\)) and \(483.28\) (\(A=1+i\)) for
\(G=|d\zeta/dz|^{-1}\). (2.211) itself is correct with the corrected \(G\).
Target: [BCA.02.5.05].

### Conventions and notation (not errata)

- p. 126: the mapping equations (2.13) presuppose that \(\mu\) intertwines \(g_\varepsilon\) with
  some \(h_\varepsilon\); they are not a consequence of \(\mu\) mapping solutions to solutions.
- p. 134, (2.40): "\([Z_3,Z_4]=2X_4\)" should read \(2Z_4\).
- pp. 154–155: "the nonlinear PDE (2.129)" (twice) should read (2.131).
- p. 153, (2.126), and p. 181, (2.249): derivatives with respect to \(z^1,z^2\) are written as
  \(\partial/\partial u_x\), \(\partial/\partial u_t\) or \(\partial/\partial X^1\); the synopsis
  uses
  \(z^j\).
- p. 166: "on a domain where \(q_2(y)\ge0\) … \(T'(y)\) is a monotone function": the Riccati
  equation gives \(M=T''/T'\) nondecreasing; \(T\) itself is strictly monotone wherever
  \(T'=\eta_2^{-1}\ne0\), independently of the sign of \(q_2\).
- p. 168, Theorem 2.5.2: the multiplier \(\exp(\int\alpha\,dy)\) must be taken with \(S_x=\beta\)
  (BCA.02.5.04).
- Theorems 2.4.1–2.4.4, 2.5.1, 2.6.1–2.6.2 are local statements; inequalities written "\(=0\)" in
  the PDF text layer (for Jacobians and determinants) are "\(\ne0\)" on the page images.

## Chapter 3. Nonlocally Related PDE Systems

Synopsis: [SYNOPSIS-BCA](SYNOPSIS-BCA.md), Chapter 3.

### BCA-E03.3.01. Factor \(L(u)\) for \(L'(u)\) in the system \(\mathbf{TA}\)

Status: Confirmed.
Location: §3.3.2, p. 204, (3.37), second equation.
Printed: \(\dfrac{\alpha_u}{t_u}=-L(u)-\dfrac{xL(u)t_x}{t_u}\).
Correct: \(\dfrac{\alpha_u}{t_u}=-L(u)-\dfrac{xL'(u)t_x}{t_u}\).
Evidence: In \((x,t)\) variables \(\alpha_t=x(L(u))_x-L(u)=xL'(u)u_x-L(u)\), and for the
hodograph \(t=t(x,u)\) one has \(u_x=-t_x/t_u\), \(\alpha_t=\alpha_u/t_u\). Special case
\(L(u)=u\) (\(K=1\)): \(u=x^2+2t\), \(\alpha=\frac14x^4+tx^2-t^2\) solves \(\mathbf{UA}\); in
\((x,u)\) variables \(t=(u-x^2)/2\), \(\alpha_u/t_u=2x^2-u\), the corrected right side is
\(-u+2x^2\), the printed one \(-u+2x^2u\). Eliminating \(t\) from the corrected system
reproduces the printed equation (3.38) exactly, so (3.38) is correct.
Target: [BCA.03.3.03].

### BCA-E03.4.01. Transformation of \(B\) under the equivalence group of (3.53)

Status: Confirmed.
Location: §3.4.2, p. 212, equivalence transformations of (3.53).
Printed: \(\tilde t=a_4t+a_1\), \(\tilde x=a_5x+a_7t+a_2\), \(\tilde u=a_6u+a_3\),
\(\tilde A=\frac{a_5^2}{a_4}A\), \(\tilde B=\frac{a_5^2}{a_4}B-a_7\).
Correct: \(\tilde B=\dfrac{a_5B-a_7}{a_4}\).
Evidence: With \(\partial_t=a_4\partial_{\tilde t}+a_7\partial_{\tilde x}\),
\(\partial_x=a_5\partial_{\tilde x}\), the equation \(u_t=(Au_x)_x+Bu_x\) becomes
\(\tilde u_{\tilde t}=\frac{a_5^2}{a_4}(A\tilde u_{\tilde x})_{\tilde x}+\frac{a_5B-a_7}{a_4}
\tilde u_{\tilde x}\). For \(a_7=0\), \(a_4=1\), \(a_5=2\) (pure scaling of \(x\)), \(B\) must
become \(2B\), not \(4B\).
Target: [BCA.03.4.04].

### BCA-E03.4.02. Extra factor \(u\) in the flux of (3.56)

Status: Confirmed.
Location: §3.4.2, p. 213, (3.56).
Printed: \(D_t\bigl((e^x+\varepsilon)u\bigr)-D_x\bigl(\varepsilon\int A(u)du+(e^x+\varepsilon)uA(u)
u_x\bigr)=0\) for \(B=A\).
Correct: \(D_t\bigl((e^x+\varepsilon)u\bigr)-D_x\bigl(\varepsilon\int A(u)du+(e^x+\varepsilon)
A(u)u_x\bigr)=0\).
Evidence: On solutions of \(u_t=(Au_x)_x+Au_x\), \(D_t((e^x+\varepsilon)u)=(e^x+\varepsilon)
((Au_x)_x+Au_x)\) and \(D_x(\varepsilon I_A+(e^x+\varepsilon)Au_x)=\varepsilon Au_x+e^xAu_x
+(e^x+\varepsilon)(Au_x)_x\), which agree. For \(A=B=1\), \(\varepsilon=0\) and the solution
\(u=x+t\), the printed divergence equals \(-e^x(x+t)\ne0\). The potential system (3.59) has
the correct flux.
Target: [BCA.03.4.04].

### BCA-E03.4.03. The case \(B=A\) has two, not four, independent local conservation laws

Status: Confirmed.
Location: §3.4.2, p. 213, item 3 and (3.56); p. 212, "classification of linearly independent
local conservation laws".
Printed: For arbitrary \(A\) and \(B=A\) there are four local conservation laws, (3.54) and
(3.56) with \(\varepsilon=0,\pm1\).
Correct: The space of local conservation laws is two-dimensional, spanned by (3.54) and
(3.56) with \(\varepsilon=0\); the laws with \(\varepsilon=\pm1\) are their sum and
difference. The values \(\varepsilon=0,\pm1\) are representatives modulo equivalence
transformations (translations and scalings of \(x\), which multiply \(e^x\) by a positive
constant) of the multipliers \(e^x+\varepsilon\), and they give inequivalent potential systems
(3.59).
Evidence: For \(B=A\), (3.54) reads \(D_tu-D_x(Au_x+I_A)=0\); (3.56) (corrected, see
[BCA-E03.4.02]) with parameter \(\varepsilon\) has density \(e^xu+\varepsilon u\) and flux
\(-(e^xAu_x)-\varepsilon(Au_x+I_A)\), i.e. it is the \(\varepsilon=0\) law plus \(\varepsilon\)
times (3.54).
Target: [BCA.03.4.04].

### BCA-E03.4.04. Sign of the potential flux in (3.58)

Status: Confirmed.
Location: §3.4.2, p. 213, (3.58).
Printed: \(v^2_x=xu\), \(v^2_t=\int A(u)du-xA(u)u_x\).
Correct: \(v^2_x=xu\), \(v^2_t=xA(u)u_x-\int A(u)du\) (the convention \(v_x=\) density,
\(v_t=-\)flux of (3.2) applied to (3.55)).
Evidence: Compatibility of the printed pair requires \((xu)_t=(I_A-xAu_x)_x=-x(Au_x)_x\), while
on solutions \((xu)_t=x(Au_x)_x\). For \(A=1\) and the solution \(u=x^2+2t\) the two mixed
derivatives are \(v_{xt}=2x\) and \(v_{tx}=-2x\).
Target: [BCA.03.4.05].

### BCA-E03.4.05. Duplicated term in a flux of Table 3.3(a)

Status: Confirmed.
Location: §3.4.3, p. 217, Table 3.3(a), system \(\mathbf{UV}^1\), subcase \(\alpha=\beta=-1\),
first conservation law.
Printed: flux part \(-D_x\bigl(\frac1{12}(v^1)^4+(x+u)(v^1)^2+tv^1+tv^1+\frac12u^2+2xu\bigr)\).
Correct: \(-D_x\bigl(\frac1{12}(v^1)^4+(x+u)(v^1)^2+tv^1+\frac12u^2+2xu\bigr)\) (one term
\(tv^1\)).
Evidence: With the printed density, the divergence on solutions of \(\mathbf{UV}^1\)
(\(F=G=u^{-1}\)) equals \(-tu_t\) for the printed flux and \(0\) for the corrected one; the
corrected flux also satisfies \(X_v=-\Lambda_1\) for the printed multiplier
\(\Lambda_1=t+\frac13v^3+2(x+u)v\).
Target: [BCA.03.4.09].

### BCA-E03.4.06. Density and multiplier of the second law for \(\alpha=\beta=-1\)

Status: Confirmed.
Location: §3.4.3, p. 217, Table 3.3(a), system \(\mathbf{UV}^1\), subcase \(\alpha=\beta=-1\),
second conservation law.
Printed: density \(2x-\frac12t^2+\frac12(\frac13u+(v^1)^2)u^2+\frac1{12}u(v^1)^4+(t+xv^1)uv^1
+x^2u\); \(\Lambda_2=(t+(2x+u)v^1)u+\frac13(v^1)^3\).
Correct: density \(xu^2-\frac12t^2+\frac12(\frac13u+(v^1)^2)u^2+\frac1{12}u(v^1)^4+(t+xv^1)uv^1
+x^2u\); \(\Lambda_2=\bigl(t+(2x+u)v^1+\frac13(v^1)^3\bigr)u\).
Evidence: With the printed flux, the divergence of the printed density on solutions of
\(\mathbf{UV}^1\) (\(F=G=u^{-1}\)) is \(-2xuu_t\); replacing \(2x\) by \(xu^2\) gives \(0\). For a
law whose density and flux depend only on \(x,t,u,v\), the multiplier of \(v_t-Fu_x-G\) is
\(\partial(\text{density})/\partial v=u\bigl(t+(2x+u)v+\frac13v^3\bigr)\), which differs from the
printed \(\Lambda_2\) by \((u-1)\frac13v^3\); the printed \(\Lambda_1\) agrees with the flux.
Target: [BCA.03.4.09].

### BCA-E03.4.07. Missing factor 2 in the flux of the \(\mathbf{UV}^2\) law of Table 3.3(b)

Status: Confirmed.
Location: §3.4.3, p. 218, Table 3.3(b), system \(\mathbf{UV}^2\), \(\alpha=-4\).
Printed: \(D_t\bigl(e^x(\frac{t^2}{u^2}-(v^2)^2)\bigr)+D_x\bigl(e^x\frac{tv^2}{u^3}\bigr)=0\).
Correct: \(D_t\bigl(e^x(\frac{t^2}{u^2}-(v^2)^2)\bigr)+D_x\bigl(2e^x\frac{tv^2}{u^3}\bigr)=0\),
equivalently \(D_t\bigl(e^x(\frac12(v^2)^2-\frac{t^2}{2u^2})\bigr)-D_x\bigl(e^x\frac{tv^2}{u^3}
\bigr)=0\), as for \(\mathbf{UB}^4\).
Evidence: With \(G=u^{-3}\), \(F=G'=-3u^{-4}\), the printed multipliers \((-e^xt/u^3,e^xv^2)\)
satisfy the Euler-operator criterion for the equations \(v^2_x-tu_t+u=0\),
\(v^2_t-t(Fu_x+G)=0\); integrating them gives the corrected law. The printed pair has
divergence \(-te^x(tuu_t-u^2+uv^2-3u_xv^2)/u^4\ne0\) on solutions.
Target: [BCA.03.4.10].

### BCA-E03.4.08. Coefficient of \(t(v^1)^2\) in a flux of Table 3.3(c)

Status: Confirmed.
Location: §3.4.3, p. 218, Table 3.3(c), system \(\mathbf{UV}^1\), \(\alpha=1\), first law.
Printed: flux \(\bigl(-tx+\frac12v^1+\frac16(t^3-2tu)\bigr)u^2-\bigl(tv^1+\frac1{12}t^4-t^2x+x^2
\bigr)v^1\).
Correct: \(\bigl(-tx+\frac12v^1+\frac16(t^3-2tu)\bigr)u^2-\bigl(\frac12tv^1+\frac1{12}t^4-t^2x
+x^2\bigr)v^1\).
Evidence: For \(F=G=u\), the printed density and flux have divergence \(-tu_tv^1\) on solutions;
with the corrected flux it is \(0\). The printed multipliers are valid (Euler-operator check)
and the corrected flux satisfies \(\partial(\text{flux})/\partial v^1=-\Lambda_1\).
Target: [BCA.03.4.11].

### BCA-E03.4.09. Multipliers of the second \(\mathbf{UV}^1\) law of Table 3.3(c)

Status: Confirmed.
Location: §3.4.3, p. 218, Table 3.3(c), system \(\mathbf{UV}^1\), \(\alpha=1\), second law.
Printed: \(\Lambda_1=\frac16t^3-tx+v^1\), \(\Lambda_2=-\frac12t^2+x+u\), with the law
\(D_t\bigl((\frac13t^3-2tx)u+(-t^2+2x+u)v^1\bigr)+D_x\bigl((\frac12t^2-x-\frac13u)u^2-(\frac13t^3
-2tx+\frac12v^1)v^1\bigr)=0\).
Correct: The law is correct; its multipliers are \(\Lambda_1=\frac13t^3-2tx+v^1\),
\(\Lambda_2=-t^2+2x+u\).
Evidence: The divergence of the printed law vanishes on solutions (\(F=G=u\)). The printed
multipliers fail the Euler-operator test: from \(\Lambda_1=T_u\), \(\Lambda_2=T_v\),
\(X_v=-\Lambda_1\), \(X_u=-u\Lambda_2\) one would need \(T_t+X_x=-u\Lambda_2\), but integration
gives \(T_t+X_x=(\frac12t^2-x)u-\frac12u^2\ne(\frac12t^2-x)u-u^2\). The density gives
\(T_u=\frac13t^3-2tx+v^1\), \(T_v=-t^2+2x+u\), which pass the test.
Target: [BCA.03.4.11].

### BCA-E03.4.10. The \(\mathbf{UC}^3\) row of Table 3.3(c)

Status: Open check.
Location: §3.4.3, p. 218, Table 3.3(c), system \(\mathbf{UC}^3\), \(\alpha=1\).
Printed: \(\Lambda_1=-\frac1{80}(t^2-2x)+\frac{2xt^2+5u^2}{40(t^2-2x)}+\frac{4x^3+5tc^3}{10(t^2-2x)^2}\),
\(\Lambda_2=\frac{3t^5-20c^3}{40(t^2-2x)^2}-\frac{t(2x+u)}{4(t^2-2x)}\), and a law with density
\(\frac1{64}(t^4-4x^2)u+\frac1{96}(u^3-3t^4u-6tc^3)+\frac{t(t^5+10c^3)u}{80(t^2-2x)}
+\frac{(t^5+5c^3)c^3}{40(t^2-2x)^2}\) and flux \(-\frac1{64}(t^2-2x)(tu^2+2c^3)+\frac1{48}t(u^3+3tc^3)
+\frac{t^4(tu^2-10c^3)+20u^2c^3}{160(t^2-2x)}+\frac{t(t^5+5c^3)c^3}{40(t^2-2x)^2}\)
(reading \(c^3\) as the potential of (3.66), not a cube).
Correct: Not determined. The row is not a conservation law of \(\mathbf{UC}^3\) as read.
Evidence: With \(F=G=u\) and (3.66), neither the multipliers (for either sign of the first
equation, and with the roles of \(\Lambda_1,\Lambda_2\) interchanged) satisfy the
Euler-operator criterion, nor does the density–flux pair have zero divergence on solutions;
the density does not satisfy \(T_{c}=\Lambda_2\) either. Since the row is set in small type,
a misreading of an exponent or a superscript index cannot be excluded; the question is to
recompute the multipliers of \(\mathbf{UC}^3\) of the form \(\Lambda_i(x,t,U,C)\).
Target: [BCA.03.4.11].

### BCA-E03.5.01. The \(\alpha\)-equations of \(\mathbf{XTA}\)

Status: Confirmed.
Location: §3.5.2, p. 227, (3.74), third and fourth equations.
Printed: \(\alpha_u=-K(u)t_u\), \(\alpha_v=x-L'(u)x-\dfrac{L(u)}{L'(u)}x_u\).
Correct: \(\alpha_u=-L(u)t_u\), \(\alpha_v=x-\dfrac{L(u)}{L'(u)}x_u\).
Evidence: From \(\alpha_x=xu\), \(\alpha_t=xL'(u)u_x-L(u)\), \(v_x=u\) and the inverse-function
relations \(u_x=-ut_v/t_u\), one gets \(\alpha_u=xux_u+(xL'u_x-L)t_u=-Lt_u\) and
\(\alpha_v=xux_v+(xL'u_x-L)t_v=x-(L/L')x_u\) using the first two equations of (3.74). Special
case \(L(u)=u\): the solution \(u=x\), \(v=\frac12x^2+t\), \(\alpha=\frac13x^3\) of
\(\mathbf{UVA}\) gives \(x=u\), \(t=v-\frac12u^2\), \(\alpha=\frac13u^3\), so \(\alpha_u=u^2\),
\(\alpha_v=0\); the corrected right sides give \(u^2\) and \(0\), the printed ones \(u\) and
\(-u\). The first two equations of (3.74) hold (\(t_u=-u\), \(t_v=1\)).
Target: [BCA.03.5.04].

### BCA-E03.5.02. Equation references for the tree \(\mathcal T_b\) of the wave equation

Status: Confirmed.
Location: §3.5.3, p. 231, lines 1–2 and the second bullet.
Printed: "the extended tree \(\mathcal T_b\) that arises from the conservation laws
(3.77)–(3.80) of the linear wave equation (3.87)"; the couplets \(\mathbf{TPQ}\),
\(\mathbf{TPR}\), \(\mathbf{TQR}\) "given by \([(3.82),(3.83)]\), \([(3.82),(3.84)]\) and
\([(3.83),(3.84)]\)".
Correct: the conservation laws (3.88)–(3.91) of (3.87); \(\mathbf{TPQ}\), \(\mathbf{TPR}\),
\(\mathbf{TQR}\) are given by \([(3.92),(3.93)]\), \([(3.92),(3.94)]\), \([(3.93),(3.94)]\).
Evidence: (3.77)–(3.80) are laws of the nonlinear equation (3.76) in \((x,t)\); (3.82)–(3.84)
define \(w,\alpha,\beta\), not \(p,q,r\). The triplets and quadruplet in the next bullets are
correctly referenced to (3.92)–(3.94).
Target: [BCA.03.5.07].

### BCA-E03.5.03. System labels in Exercise 3.5.4

Status: Confirmed.
Location: Exercise 3.5.4, pp. 241–242.
Printed: "the potential system \(\mathbf{XTQ}\{u,v;x,t,p\}\) [(3.85), (3.93)] is locally
related to the potential system \(\mathbf{UWB}\{x,t;u,w,\beta\}\) [(3.81), (3.84)]".
Correct: \(\mathbf{XTQ}\{u,v;x,t,q\}\) is locally related to \(\mathbf{UVB}\{x,t;u,v,\beta\}\)
[(3.81), (3.84)], as stated in the text on p. 231.
Evidence: (3.81) and (3.84) define \(v\) and \(\beta\). On solutions
\(q=xv-\beta-t\int c^2du+\)const, which involves \(v\), not \(w\).
Target: [BCA.03.5.07].

### BCA-E03.5.04. Chaplygin gas: \(p=w^4(y)q\)

Status: Confirmed.
Location: §3.5.4, p. 241, last display.
Printed: \(p=w^4(y)q\), \(q_{ss}+(w^4(y)q)_{yy}=0\), with \(w^4=w^4(y)\) arbitrary.
Correct: \(p=w^4_y(y)\,q\), \(q_{ss}+(w^4_y(y)q)_{yy}=0\); equivalently \(p=W(y)q\) with an
arbitrary function \(W=w^4_y\).
Evidence: For \(\gamma=-1\), (3.123) gives \(w^4_y=pq^{-1}\) and \(w^4_s=0\), so
\(p=w^4_y(y)q\); the printed relation with \(w^4\) itself contradicts \(w^4_y=p/q\) unless
\(w^4=w^4_y\).
Target: [BCA.03.5.12].

### Conventions and notation (not errata)

- (3.2) uses \(v_x=\) density, \(v_t=-\)flux. (3.45) introduces \(\alpha^3\) with
  \(\alpha^3_x=-\alpha^1\), \(\alpha^3_t=\alpha^2\), the negative of that convention for the
  law \(D_t\alpha^1+D_x\alpha^2=0\); this is a relabelling ([BCA.03.3.05]).
- In (3.37)–(3.38) the potential \(\alpha\) is typeset as \(a\) ([BCA.03.3.03]).
- (3.49) names \(\Phi\) the density and \(\Psi\) the flux, while Theorem 3.4.2 calls \(\Phi\) the
  flux and \(\Psi\) the density ([BCA.03.4.03]).
- In Tables 3.3(a)–(c), \(v^2\), \(b^3\), \(c^3\), \(b^4\) are potentials (superscript
  indices); \((v^2)^2\) is the square of \(v^2\). In the \(\mathbf{UV}^2\) rows, "\(uv^2\)" means
  \(u\cdot v^2\) with the potential \(v^2\) ([BCA.03.4.09]–[BCA.03.4.11]).
- Multiplier signs in Tables 3.1–3.3 and (3.69) correspond to different ways of writing the
  first equation (\(u_t-v_x\) or \(v_x-u_t\)), and some rows give the multipliers of the negative
  of the displayed law; the synopsis states the form used.
- Table 3.3(b) is stated for \(F=G'\), \(G=u^{\alpha+1}\), so \(F=(\alpha+1)u^\alpha\), while
  the table caption says \(F=u^\alpha\); the two normalizations are related by an equivalence
  transformation, and the printed laws hold with \(F=G'\) ([BCA.03.4.10]).
- In (3.99)–(3.103), "\(vs+qy\)" and "\(-sp+vy\)" are products \(v\cdot s\), \(q\cdot y\), as in
  Table 3.5 ([BCA.03.5.08]).
- The conservation laws of Table 3.1 hold only for the specific antiderivative \(\int B\,du\)
  stated in the synopsis (\(uI_A\), \(0\), \(-u^{-1}\), \(u^2\)); the source leaves the
  integration constant implicit ([BCA.03.4.06]).

## Chapter 4. Applications of Nonlocally Related PDE Systems

Synopsis: [SYNOPSIS-BCA](SYNOPSIS-BCA.md), Chapter 4.

### BCA-E04.2.01. \(K\) for \(L\) in the equivalence transformation of \(L\)

Status: Confirmed.
Location: §4.2.1, p. 252, (4.6).
Printed: \(\tilde L(\tilde u)=\dfrac{a_5^2a_6}{a_4}K(u)+a_7\).
Correct: \(\tilde L(\tilde u)=\dfrac{a_5^2a_6}{a_4}L(u)+a_7\).
Evidence: \(\tilde L\) must satisfy \(\tilde L'(\tilde u)=\tilde K(\tilde u)=\frac{a_5^2}{a_4}K(u)\);
since \(d\tilde u=a_6\,du\), \(\frac{d}{du}\tilde L=\frac{a_5^2a_6}{a_4}K(u)=\frac{d}{du}\bigl(
\frac{a_5^2a_6}{a_4}L(u)\bigr)\). For \(K=1\), \(L=u\) and \(a_4=a_5=a_6=1\), \(a_7=0\), the
printed formula gives \(\tilde L=1\), which is not an antiderivative of \(\tilde K=1\).
Target: [BCA.04.2.03].

### BCA-E04.2.02. Coefficient of \(\partial_\alpha\) in \(Z_{15}\)

Status: Confirmed.
Location: §4.2.1, p. 255, Table 4.3, row \(K=u^{-4/3}(1+bu)^{-2/3}\).
Printed: \(Z_{15}=\dots+(b^2v+2b\alpha)v\,\partial_\alpha\).
Correct: \(Z_{15}=\dots+(b^2v^2+2b\alpha)v\,\partial_\alpha\).
Evidence: With \(L=-3(u/(1+bu))^{-1/3}\) (so \(L'=K\)), the corrected generator satisfies all
determining equations of \(\mathbf{UVA}\) (\(v_x=u\), \(v_t=Ku_x\), \(\alpha_x=xu\),
\(\alpha_t=xKu_x-L\)) identically in \(b\). The two candidates differ by
\(\delta=b^2v^2(v-1)\) in the \(\alpha\)-component; in the determining equation from
\(\alpha_x=xu\) this contributes \(D_x\delta=b^2(3v^2-2v)u\), which no other term cancels, so
the printed generator is not a symmetry for \(b\ne0\). The corrected form is also homogeneous
under the scaling \(x,v,\alpha\) of weights \(1,1,2\) used by the other terms of \(Z_{15}\).
Target: [BCA.04.2.05].

### BCA-E04.2.03. The generator \(W_8\) for \(c(u)=e^u\)

Status: Confirmed.
Location: §4.2.2(2), p. 260, Table 4.6, row \(c=e^u\).
Printed: \(W_8=-(2vt+x)\partial_t-2e^ut\partial_x+4v\partial_u+(4e^u+v^2)\partial_v\).
Correct: \(W_8=-(2tv+x)\partial_t-e^{2u}t\partial_x+2v\partial_u+(e^{2u}+v^2)\partial_v\).
Evidence: For \(\mathbf{UV}\) with \(c=e^u\) (\(v_x=u_t\), \(v_t=e^{2u}u_x\)) the corrected
generator satisfies the determining equations, and a search over generators with these
monomials gives it uniquely up to adding \(W_1,\dots,W_4,W_7\). The printed generator fails
for \(c=e^u\) and also for \(c=e^{u/2}\) (the reading \(c^2=e^u\)). The corrected form parallels
the generators \(K_7\) (Table 4.10) and \(J^{(b)}_6\) (Table 4.9) for the same \(c=e^u\), whose
\(\partial_v\)-coefficients contain \(e^{2u}+v^2\).
Target: [BCA.04.2.08].

### BCA-E04.2.04. Sign of the \(\partial_p\)-coefficient of \(L_7\)

Status: Confirmed.
Location: §4.2.2(4), p. 264, Case 3b(1).
Printed: \(L_7=\dots+(tu^{2+2\nu}-vp)\partial_p\).
Correct: \(L_7=\dots+(vp-tu^{2+2\nu})\partial_p\), the other components as printed.
Evidence: For \(\mathbf{TP}\) (\(p_v=ut_u-t\), \(p_u=uc^2t_v\)) with \(c=u^2\), the general
point symmetry with components in the span of \(1,t,p,v,u,tv,pv,v^2,uv,tu^6,u^6,\dots\) was
computed; the solution with \(\partial_t\)-component \(-(5tv+p)\) has
\(\partial_p\)-component \(pv-tu^6\). With the printed sign the determining equation from
\(p_v=ut_u-t\) leaves the residual \(-2p+2tv-2t_uuv+2t_vu^6\) (\(\nu=2\)); the same failure
occurs for \(\nu=\frac12\), \(-3\). The corrected sign is also the one in \(L_8\)
(\(\nu=-1\)), whose \(\partial_p\)-coefficient \(-(t-pv)\) checks.
Target: [BCA.04.2.10].

### BCA-E04.2.05. Cross-reference \(W_7\) for \(W_9\)

Status: Confirmed.
Location: §4.2.2(4), p. 264, Case 3b(2), last sentence.
Printed: "These symmetries correspond to \(W_5\) (\(\nu=-1\)) and \(W_7\), respectively, in
Table 4.6."
Correct: \(W_5\) (\(\nu=-1\)) and \(W_9\).
Evidence: In Table 4.6, \(W_7\) belongs to \(c=e^u\) and \(W_9\) to \(c=u^{-1}\), the case of
\(L_8\); \(L_8\) and \(W_9\) have the same \(\partial_u\)- and \(\partial_v\)-components
\(2uv\), \(2\log u\).
Target: [BCA.04.2.10].

### BCA-E04.2.06. \(u^2\) for \(v^2\) in \(L_9\)

Status: Confirmed.
Location: §4.2.2(4), p. 264, Case 3b(3).
Printed: \(L_9=(pu-2tv(u+1))\partial_t-2u^2v\partial_u+(u^2+e^{2/u})\partial_v+t\frac{e^{2/u}}u
\partial_p\).
Correct: \(\partial_v\)-coefficient \(v^2+e^{2/u}\).
Evidence: For \(\mathbf{TP}\) with \(c=u^{-2}e^{1/u}\), the linear ansatz over monomials in
\(t,p,v,u,e^{2/u}\) gives, besides \(L_1\)–\(L_3\), \(L_{10}\) and the trivial ones, exactly
\((pu-2tv(u+1))\partial_t-2u^2v\partial_u+(v^2+e^{2/u})\partial_v+te^{2/u}u^{-1}\partial_p\).
The printed generator leaves the residual \(-2tv+2t_uuv+2t_vu^2\) in the first determining
equation.
Target: [BCA.04.2.10].

### BCA-E04.2.07. "\(v^*\)" for \(v\) in (4.25)

Status: Confirmed.
Location: §4.2.2(6), p. 266, (4.25).
Printed: \(\tilde t=a_2^{-2}a_3t+a_5uv+a_6v^*\).
Correct: \(\tilde t=a_2^{-2}a_3t+a_5uv+a_6v\).
Evidence: The accompanying term \(-\frac13a_2^2a_6v^3\) in \(\tilde r\) is exactly what
\(t\mapsto t+a_6v\) requires: with \(t=v\), \(r_v=v(ut_u-t)=-v^2\) and
\(r_u=uc^2(vt_v-t)=0\), so \(r=-\frac13v^3\). No other meaning of \(v^*\) is defined.
Target: [BCA.04.2.12].

### BCA-E04.2.08. Sign of the \(\partial_t\)-coefficient of \(N_8\)

Status: Confirmed.
Location: §4.2.2(6), p. 267, Table 4.8, row \(c=u^{-2}\).
Printed: \(N_8=\frac1u\bigl[(tu^2v^2+2t-u^2r)\partial_t+2v\partial_v+(tv^2+r)\partial_r\bigr]
-(1+u^2v^2)\partial_u\).
Correct: \(N_8=\frac1u\bigl[-(tu^2v^2+2t-u^2r)\partial_t+2v\partial_v+(tv^2+r)\partial_r\bigr]
-(1+u^2v^2)\partial_u\).
Evidence: For \(\mathbf{TR}\) with \(c=u^{-2}\) (\(r_v=v(ut_u-t)\), \(r_u=u^{-3}(vt_v-t)\)) the
corrected generator satisfies the determining equations, and a linear ansatz over monomials
in \(t,r,v,u,u^{-1}\) yields it (besides \(N_1,N_2,N_3,N_7\)) with \(\partial_t\)-coefficient
\((u^2r-tu^2v^2-2t)/u\). The printed generator leaves a nonzero residual in both determining
equations. No overall sign change reconciles the printed one, since its
\(\partial_v\), \(\partial_r\), \(\partial_u\) components agree with the corrected ones.
Target: [BCA.04.2.12].

### BCA-E04.2.09. Factor \(\frac12\) in \(K_5\)

Status: Confirmed.
Location: §4.2.2(8), p. 270, Table 4.10, row \(c=u^\nu\) (written with \(C=\nu\)).
Printed: \(K_5=-\frac12Ctv\partial_t+uv\partial_u+\Bigl[\dfrac{u^{2+2C}}{1+C}+\frac12(1+C)v^2
\Bigr]\partial_v\).
Correct: \(K_5=-\frac12Ctv\partial_t+uv\partial_u+\frac12\Bigl[\dfrac{u^{2+2C}}{1+C}+(1+C)v^2
\Bigr]\partial_v\).
Evidence: For \(t_{uu}=u^{2C}t_{vv}\), the ansatz \(atv\partial_t+uv\partial_u+(\alpha u^{2+2C}+
\beta v^2)\partial_v\) gives \(a=-\frac C2\), \(\beta=\frac{1+C}2\), \(\alpha=\frac1{2(1+C)}\):
\(\alpha=\frac16\) for \(C=2\) and \(\alpha=\frac13\) for \(C=\frac12\), not \(\frac13\) and
\(\frac23\). The corrected form parallels \(K_7=-\frac12tv\partial_t+v\partial_u+\frac12
[e^{2u}+v^2]\partial_v\) and \(W_6\) (Table 4.6, with \(2uv\partial_u\)).
Target: [BCA.04.2.14].

### BCA-E04.2.10. Factor 2 on \(\int F\,du\) in \(Y_4\), \(Y_5\), \(Y_6\)

Status: Confirmed.
Location: §4.2.3, p. 272, Table 4.12, rows \(\tan u\), \(\tanh u\), \(\coth u\), \(u^{-1}\).
Printed: \(\partial_x\)-coefficients \(2[\beta x-\int F(u)du]\) (\(Y_4\)) and
\(2[\beta x+\int F(u)du]\) (\(Y_5\), \(Y_6\)).
Correct: \(2\beta x-\int F(u)du\) (\(Y_4\)) and \(2\beta x+\int F(u)du\) (\(Y_5\), \(Y_6\));
the other components as printed.
Evidence: For \(\mathbf{UV}^1\) (\(v_x=u_t\), \(v_t=Fu_x+G\)) with \(\tau=\beta t\mp v\) and
\(\xi=2\beta x+kW\), \(W=\int F\,du\), the terms quadratic in first derivatives in the
second determining equation are \(-(k\pm1)F(u_t^2-Fu_x^2)\) up to sign, so \(k=\mp1\); the
printed \(k=\mp2\) leaves \(\mp F(u_t^2-Fu_x^2)\). A numerical null-space computation of the
determining equations (\(\beta=\frac53\)) for \(F=e^{2\beta u}\sec^2u\), \(G=\tan u\);
\(F=e^{2\beta u}\operatorname{sech}^2u\), \(G=\tanh u\); \(F=-u^{-2}e^{2\beta u}\), \(G=u^{-1}\)
returns exactly the corrected generators (plus translations). In \(Y_1\)–\(Y_3\) the ratio of
the \(v\)-coefficient in \(\tau\) to the \(W\)-coefficient in \(\xi\) is 1, as in the corrected
\(Y_4\)–\(Y_6\); \(Y_3\) was checked in the same way and is correct as printed.
Target: [BCA.04.2.16].

### BCA-E04.2.11. \(x^2\) for \(x^4\) in (4.35)

Status: Confirmed.
Location: Exercise 4.2.6, p. 282, (4.35).
Printed: \(q_{tt}=x^2q_{xx}\).
Correct: \(q_{tt}=x^4q_{xx}\).
Evidence: (4.35) is to be the equation \(\mathbf T\) (3.87), \(t_{uu}=c^2(u)t_{vv}\), for
\(c=u^{-2}\) after renaming; \(t_{vv}=u^4t_{uu}\) becomes \(q_{tt}=x^4q_{xx}\). With
\(Q=f(X)+g(T)\), \(X=1/x+t\), \(T=1/x-t\), the function \(q=x(Q-t)\) satisfies
\(q_{tt}-x^4q_{xx}=0\) identically, while \(q_{tt}-x^2q_{xx}=(x-x^{-1})(f''+g'')\ne0\).
Target: [BCA.04.2.14].

### BCA-E04.3.01. Signs in the linearizing map (4.50) of the Thomas equations

Status: Confirmed.
Location: §4.3.1(3), p. 287, (4.50).
Printed: \(w^1=e^{-w}\), \(w^2=e^{-w}v\), \(w^3=e^{-v}u\).
Correct: \(w^1=e^{-w}\), \(w^2=-e^{-w}v\), \(w^3=-e^{-w}u\).
Evidence: On solutions of (4.47), \(\partial_xe^{-w}=-ve^{-w}\) and \(\partial_te^{-w}=-ue^{-w}\),
so (4.51) \(\partial_{z^1}w^1=w^2\), \(\partial_{z^2}w^1=w^3\) require the minus signs (and
\(e^{-w}\) in \(w^3\)). Then \(\partial_{z^2}w^2=-e^{-w}(v_t-uv)=-e^{-w}(u+v)=w^2+w^3\), and
the inverse formula \((u,v)=-(w^3/w^1,\,w^2/w^1)\) printed after (4.51) holds; with the printed
signs it would give \((u,v)\mapsto(-u,-v)\).
Target: [BCA.04.3.04].

### BCA-E04.3.02. Factor 4 for \(c(y)\) in the equation for \(\lambda'\)

Status: Confirmed.
Location: §4.3.2, p. 291, (4.66), third equation.
Printed: \(\lambda'=\sigma^{-2}(\rho'^2-2\sigma\sigma')+c(y)\).
Correct: \(\lambda'=\sigma^{-2}(\rho'^2-2\sigma\sigma')+4c(y)\).
Evidence: Substituting \(u=W(z^1,z^2)e^{-g}\), \(g=\frac14[\sigma^{-1}\sigma'x^2+2\sigma^{-1}
\rho'x+\lambda]\), into \(u_{xx}+u_y+(ax^2+bx+c)u\) gives \(\sigma^2e^{-g}(W_{z^1z^1}+W_{z^2})\)
plus \(e^{-g}W\) times a quadratic polynomial in \(x\) whose coefficients are
\(-\frac14\sigma^{-2}(\sigma\sigma''-2\sigma'^2-4a\sigma^2)\),
\(-\frac12\sigma^{-2}(\sigma\rho''-2\sigma'\rho'-2b\sigma^2)\) and
\(-\frac14\sigma^{-2}(\sigma^2\lambda'+2\sigma\sigma'-\rho'^2-4c\sigma^2)\). The first two
reproduce the printed first two equations of (4.66); the third forces the factor 4. Example:
\(\sigma=1\), \(\rho=0\), \(a=b=0\), \(c=1\): \(w=ue^{\lambda/4}\) solves the backward heat
equation when \(u_{xx}+u_y+u=0\) iff \(\lambda=4y\), not \(\lambda=y\).
Target: [BCA.04.3.07].

### BCA-E04.3.03. Sign of \(\psi^{-1}\psi_x\) in the map (4.73)

Status: Confirmed.
Location: §4.3.2, p. 292, (4.73), third equation.
Printed: \(w^1=\sigma^{-1}e^{g}\bigl\{u+\bigl(\frac12\sigma^{-1}(\sigma'x+\rho')-\psi^{-1}
\psi_x\bigr)\psi v\bigr\}\).
Correct: \(w^1=\sigma^{-1}e^{g}\bigl\{u+\bigl(\frac12\sigma^{-1}(\sigma'x+\rho')+\psi^{-1}
\psi_x\bigr)\psi v\bigr\}\).
Evidence: Simplest case \(\sigma=1\), \(\rho=\lambda=0\), \(a=b=c=0\), \(g=0\): then
\(w^2=\psi v\) and, on solutions of \(v_x=\psi^{-1}u\), \(\partial_{z^1}w^2=\psi_xv+u\), which is
\(w^1\) only with the plus sign; the second equation of (4.72) then also holds, using
\(\psi_y=-\psi_{xx}\). For general data (e.g. \(\sigma=e^y\), \(\rho=y\), \(\lambda=y^2\),
\(\hat\psi=z^1\); \(\sigma=1+y^2\), \(\rho=\sin y\), \(\lambda=y\),
\(\hat\psi=(z^1)^2-2z^2\)), with \(a,b,c\) from the corrected (4.66) and
\(\psi=\hat\psi e^{-g}\), both equations of (4.72) were evaluated at a sample point and vanish
with the plus sign and not with the printed minus sign.
Target: [BCA.04.3.09].

### Conventions and notation (not errata)

- In Table 4.10 the exponent \(\nu\) of \(c=u^\nu\) is written \(C\) in the generators
  ([BCA.04.2.14]).
- Table 4.14 uses the normalization \(F=(\alpha+1)u^\alpha\), \(G=u^{\alpha+1}\) of case (b),
  equivalent to \(F=u^\alpha\), \(G=u^{\alpha+1}\) by (3.61) ([BCA.04.2.18]).
- In §4.3.2 the independent variables of (4.62) are \((x,y)\); the sentence after (4.73)
  speaks of \((x,t,u,v)\)- and \((x,t,u)\)-space, meaning \((x,y,u,v)\) and \((x,y,u)\)
  ([BCA.04.3.09]).
- In (4.72), \(\partial w^1/\partial z_1\) has a subscript index; it means
  \(\partial w^1/\partial z^1\) ([BCA.04.3.09]).
- The condition \(\partial_x^5\log|\phi|\not\equiv0\) after (4.73) and Theorem 4.3.3 are stated
  without proof (Exercise 4.3.3); the synopsis records them as stated ([BCA.04.3.10]).

## Chapter 5. Further Applications of Symmetry Methods: Miscellaneous Extensions

Synopsis: [SYNOPSIS-BCA](SYNOPSIS-BCA.md), Chapter 5.

### BCA-E05.2.01. Constant \(q_0\) for \(\gamma\) in the potential \(w\) of (5.60)

Status: Confirmed.
Location: §5.2.3(2), p. 319, (5.60), last formula.
Printed: \(w(y,s)=-\dfrac{q_0\beta}{\alpha^2}\dfrac{y^2}{y+\alpha}\tan(\beta s)\).
Correct: \(w(y,s)=-\dfrac{\gamma\beta}{\alpha^2}\dfrac{y^2}{y+\alpha}\tan(\beta s)\).
Evidence: \(w\) is the potential of \(\mathbf{LW}^2\), \(w_y=v\), \(w_s=-p\). With the printed
\(v\) and \(p\) of (5.60), \(\partial_y\bigl[y^2/(y+\alpha)\bigr]=y(y+2\alpha)/(y+\alpha)^2\)
gives \(w_y=v\) and \(\partial_s\tan\beta s=\beta(1+\tan^2\beta s)\) gives \(w_s=-p\) exactly
for the coefficient \(\gamma\); \(q_0\) does not occur elsewhere in (5.60) (it enters only in
(5.61)). The functions \(p,q,v\) of (5.60) do solve \(\mathbf L\) with \(M(p)=-p\ln p\).
Target: [BCA.05.2.10].

### BCA-E05.2.02. Sign of the constitutive function after (5.61)

Status: Confirmed.
Location: §5.2.3(2), p. 320, display after (5.61).
Printed: \(B(p',q')=\dfrac{(p_0-p')\ln(p_0-p')}{q_0-q'}\).
Correct: \(B(p',q')=-\dfrac{(p_0-p')\ln(p_0-p')}{q_0-q'}\).
Evidence: The constitutive function of (5.60) is \(B=M(p)/q=-p\ln p/q\), and the stated
equivalence transformation (3.96) with \(a_3=-1\) does not change its sign. Directly: for (5.61),
\(q'_s=v'_y\) and \(v'_s+p'_y=0\) hold, and \(p'_s+Bv'_y=0\) holds with the corrected \(B\); with
the printed \(B\) the residual is \(8y^2\sinh s/\bigl((y+1)\cosh^3s\bigr)\ne0\).
Target: [BCA.05.2.10].

### BCA-E05.3.01. The Lorentz gauge in \((2+1)\) dimensions contains \(z\)

Status: Confirmed.
Location: §5.3.1, p. 335, Lorentz-gauge bullet and (5.118) (fourth equation and system name).
Printed: Lorentz gauge \(\Psi^1_t-\Psi^2_y-\Psi^3_z=0\); in (5.118)
\(\Psi^1_t-\Psi^2_y-\Psi^3_z=0\); system name \(\mathbf S\{x,y,t;u,\Psi^1,\Psi^1,\Psi^3\}\).
Correct: with independent variables ordered \((t,x,y)\), \(\Psi^1_t-\Psi^2_x-\Psi^3_y=0\); in
(5.118), whose curl is taken in the order \((x,y,t)\) so that \(\Psi^3\) is the time
component, \(\Psi^3_t-\Psi^1_x-\Psi^2_y=0\); system name
\(\mathbf S\{x,y,t;u,\Psi^1,\Psi^2,\Psi^3\}\).
Evidence: \(z\) is not an independent variable in \((2+1)\) dimensions. The first three
equations of (5.118) state \(\operatorname{curl}_{(x,y,t)}\Psi=(Ku_x,Ku_y,-u_t)\). For
\(K=1\) the substitution \(\Psi^1=-v^1\), \(\Psi^2=-v^2\), \(\Psi^3=-v^0\) carries them to the
first three equations of (5.145), and the Lorentz gauge \(v^0_t-v^1_x-v^2_y=0\) of (5.145)
becomes \(\Psi^3_t-\Psi^1_x-\Psi^2_y=0\). The Cronstrom gauge \(t\Psi^1-x\Psi^2-y\Psi^3=0\) in
the same bullet list uses the ordering \((t,x,y)\).
Target: [BCA.05.3.01].

### BCA-E05.3.02. Sign of the \(h\)-components in (5.143)

Status: Confirmed.
Location: §5.3.5, p. 344, (5.143).
Printed: \(X_\infty=F(w)\bigl(\partial_w+h^1\partial_{h^1}+h^2\partial_{h^2}+h^3\partial_{h^3}
\bigr)\).
Correct: \(X_\infty=F(w)\bigl(\partial_w-h^1\partial_{h^1}-h^2\partial_{h^2}-h^3\partial_{h^3}
\bigr)\).
Evidence: For \(K=|h|^{-2}\) and any function \(g(w)\), on solutions of (5.141) one has
\(\operatorname{grad}w\perp h\), \(\operatorname{curl}(gh)=g\operatorname{curl}h+g'
\operatorname{grad}w\times h\) and \((\operatorname{grad}w\times h)\times h=-|h|^2
\operatorname{grad}w\), hence
\(K(|gh|)\,\operatorname{curl}(gh)\times(gh)=(1-g'/g)\operatorname{grad}w\). The generator
\(F(w)(\partial_w+\sigma h^i\partial_{h^i})\) corresponds to \(g=1+\varepsilon\sigma F\),
\(w\mapsto w+\varepsilon F\); to first order the left side becomes
\((1-\varepsilon\sigma F')\operatorname{grad}w\) and the right side
\((1+\varepsilon F')\operatorname{grad}w\), so the residual is
\(-\varepsilon(\sigma+1)F'(w)\operatorname{grad}w\), zero for all \(F\) only when
\(\sigma=-1\). \(\operatorname{div}h=0\) is preserved since \(\operatorname{div}(gh)=g'\,h\cdot
\operatorname{grad}w=0\).
Target: [BCA.05.3.10].

### BCA-E05.3.03. Conformal symmetries \(Y_8\)–\(Y_{10}\) of the wave potential system

Status: Confirmed.
Location: §5.3.5, p. 346, (5.146).
Printed: \(Y_8=X_8-(yv^1-xv^2+tu)\partial_u-(2tv^0+xv^1+yv^2)\partial_{v^0}-(xv^0+2tv^1+yu)
\partial_{v^1}+(yv^0+2tv^2-xu)\partial_{v^2}\);
\(Y_9=X_9-(-yv^0-tv^2+xu)\partial_u-(2xv^0+tv^1+yu)\partial_{v^0}-(xv^0+2tv^1+yu)
\partial_{v^1}+(yv^0+2tv^2-xu)\partial_{v^2}\);
\(Y_{10}=X_{10}-(xv^0+tv^1+yu)\partial_u-(2yv^0+tv^2-xu)\partial_{v^0}-(2yv^1-xv^2+tu)
\partial_{v^1}+(tv^0+xv^1+2yv^2)\partial_{v^2}\).
Correct: with the \((t,x,y)\)-components of \(X_8,X_9,X_{10}\),
\[
\begin{aligned}
Y_8&:\ u:\,-2tu+yv^1-xv^2;\ v^0:\,-2tv^0-xv^1-yv^2;\ v^1:\,-2tv^1-xv^0+yu;\
v^2:\,-2tv^2-yv^0-xu;\\
Y_9&:\ u:\,-2xu-tv^2-yv^0;\ v^0:\,-2xv^0-tv^1+yu;\ v^1:\,-2xv^1-tv^0-yv^2;\
v^2:\,-2xv^2-tu+yv^1;\\
Y_{10}&:\ u:\,-2yu+tv^1+xv^0;\ v^0:\,-2yv^0-tv^2-xu;\ v^1:\,-2yv^1+tu+xv^2;\
v^2:\,-2yv^2-tv^0-xv^1
\end{aligned}
\]
(total coefficients of \(\partial_u,\partial_{v^0},\partial_{v^1},\partial_{v^2}\), including
the \(-tu\), \(-xu\), \(-yu\) of \(X_8,X_9,X_{10}\)).
Evidence: The first-order prolongation test of each generator on (5.145) (all four equations
in solved form for \(u_t,v^2_t,v^1_t,v^0_t\)) leaves nonzero residuals for the three printed
generators and vanishes identically for the corrected ones; a linear ansatz (\(u\)- and
\(v\)-components linear in \(u,v^0,v^1,v^2\) with coefficients linear in \(t,x,y\)) with the
\((t,x,y)\)-components of \(X_8,X_9,X_{10}\) fixed returns exactly these generators, up to
adding multiples of \(u\partial_u+v^i\partial_{v^i}\) and of (5.147). The printed \(Y_9\)
repeats the \(v^1\)- and \(v^2\)-components of \(Y_8\).
Target: [BCA.05.3.11].

### BCA-E05.3.04. Duality symmetries (5.147)

Status: Confirmed.
Location: §5.3.5, p. 346, (5.147).
Printed: \(Y_{11}=v^0\partial_u-u\partial_{v^0}+v^2\partial_{v^1}-v^1\partial_{v^2}\),
\(Y_{12}=v^1\partial_u-v^2\partial_{v^0}+u\partial_{v^1}-v^0\partial_{v^2}\),
\(Y_{13}=v^2\partial_u+v^1u\partial_{v^0}+v^0\partial_{v^1}+u\partial_{v^2}\).
Correct: \(Y_{11}=v^0\partial_u-u\partial_{v^0}-v^2\partial_{v^1}+v^1\partial_{v^2}\),
\(Y_{12}=v^1\partial_u+v^2\partial_{v^0}+u\partial_{v^1}+v^0\partial_{v^2}\),
\(Y_{13}=v^2\partial_u-v^1\partial_{v^0}-v^0\partial_{v^1}+u\partial_{v^2}\).
Evidence: For a generator with constant-coefficient linear components and no
\((t,x,y)\)-components, invariance of (5.145) is a linear condition on the \(4\times4\)
coefficient matrix. Its solution space is spanned by the identity scaling and the three
corrected generators; the printed \(Y_{11}\) leaves the residuals \(2(v^1_x+v^2_y)\),
\(2(u_y-v^0_x)\), \(2(u_x+v^0_y)\), \(2(v^1_y-v^2_x)\), the printed \(Y_{12}\) leaves
\(2v^0_x\), \(-2v^1_x\), \(2v^2_x\), \(-2u_x\), and the printed \(Y_{13}\) is not linear
(\(v^1u\)). The statement that \(\mathbf{MAW}\) (5.156) inherits these symmetries holds for the
corrected forms.
Target: [BCA.05.3.11], [BCA.05.3.12].

### BCA-E05.3.05. Index in the cyclic identity (5.151a)

Status: Confirmed.
Location: §5.3.5, p. 348, (5.151a).
Printed: \(\partial_pF_{ij}+\partial_jF_{pi}+\partial_iF_{ip}=0\).
Correct: \(\partial_pF_{ij}+\partial_jF_{pi}+\partial_iF_{jp}=0\).
Evidence: The identity is the cyclic sum over \((p,i,j)\); the printed third term repeats the
index \(i\) (a contraction) and has free indices \(p\) only, so it is not a term of a
three-index identity. With the corrected term and \(F\) from (5.150), the single independent
component \((p,i,j)=(0,1,2)\) gives \(B_t+E^2_x-E^1_y=0\), i.e. (5.149d), and agrees with
\(\eta^{ij}\partial_i{}^*F_j=0\) for \({}^*F=(B,-E^2,E^1)\), as the text states.
Target: [BCA.05.3.12].

### BCA-E05.4.01. Missing \(p\)- and \(\rho\)-components of \(X_7\) in §5.4.1

Status: Confirmed.
Location: §5.4.1, p. 359, generator \(X_7\).
Printed: \(X_7=xt\partial_x+t^2\partial_t+(x-vt)\partial_v\).
Correct: \(X_7=xt\partial_x+t^2\partial_t+(x-vt)\partial_v-3tp\partial_p-t\rho\partial_\rho\).
Evidence: The first-order prolongation test on (5.173) with \(\gamma=3\) leaves the residuals
\(\rho\), \(2tp_x/\rho\), \(3p\) (in the three equations) for the printed generator and vanishes
for the corrected one; the missing terms depend on \(t\) and cannot be supplied by the
constant combinations of \(X_5\), \(X_6\). The corrected form is the \(X_7\) of Table 4.17
(\(\gamma=3\)).
Target: [BCA.05.4.01].

### BCA-E05.4.02. Sign of \(U_{xx}\) in the KdV multiplier \(\Lambda_4\)

Status: Confirmed.
Location: §5.4.3, p. 364, \(\Lambda_4\).
Printed: \(\Lambda_4[U]=\frac12U^2-U_{xx}\).
Correct: \(\Lambda_4[U]=\frac12U^2+U_{xx}\).
Evidence: The reduced determining equations printed just above require
\(\partial^2\Lambda/\partial U^2=\partial\Lambda/\partial U_{xx}\), which the printed
\(\Lambda_4\) violates (\(1\ne-1\)). For \(R=u_t+uu_x+u_{xxx}\) the Euler operator gives
\(E_u[(\frac12u^2+u_{xx})R]=0\), while \(E_u[(\frac12u^2-u_{xx})R]=-6u_xu_{xx}\). The
corresponding fourth conservation law printed afterwards has density
\(\frac13u^3+uu_{xx}\), consistent with \(\frac12u^2+u_{xx}\).
Target: [BCA.05.4.01].

### BCA-E05.4.03. Missing term in the Galilean flux of KdV

Status: Confirmed.
Location: §5.4.3, p. 364, third conservation law.
Printed: \(D_t\bigl(\frac12tu^2-xu\bigr)+D_x\bigl(-\frac12xu^2+tuu_{xx}-\frac12tu_x^2-xu_{xx}
+u_x\bigr)=0\).
Correct: \(D_t\bigl(\frac12tu^2-xu\bigr)+D_x\bigl(-\frac12xu^2+\frac13tu^3+tuu_{xx}
-\frac12tu_x^2-xu_{xx}+u_x\bigr)=0\).
Evidence: On solutions of \(u_t=-uu_x-u_{xxx}\) the printed divergence equals
\(-tu^2u_x\ne0\); adding \(\frac13tu^3\) to the flux makes it vanish identically. The
corrected flux is \(t\) times the flux of the second law plus \(-x\) times the flux of the
first law plus \(u_x\), as the multiplier \(tU-x\) requires.
Target: [BCA.05.4.01].

### BCA-E05.4.04. Missing plus sign in the fourth KdV flux

Status: Confirmed.
Location: §5.4.3, p. 364, fourth conservation law.
Printed: \(D_x\bigl(\frac14u^4u^2u_{xx}+u_{xx}^2-uu_{xt}+u_xu_t\bigr)\).
Correct: \(D_x\bigl(\frac14u^4+u^2u_{xx}+u_{xx}^2-uu_{xt}+u_xu_t\bigr)\).
Evidence: With the density \(\frac13u^3+uu_{xx}\) and the corrected flux, the divergence
vanishes identically on solutions of (5.181); the printed product \(\frac14u^6u_{xx}\) has the
wrong degree in \(u\) for this scaling-homogeneous law.
Target: [BCA.05.4.01].

### Conventions and notation (not errata)

- In §5.2, "assume that \(\xi(x,u)\equiv0\)" (p. 301) means \(\xi\not\equiv0\); "Exercise
  5.2-1", "5.2-7" mean Exercises 5.2.1, 5.2.7 ([BCA.05.2.01], [BCA.05.2.04]).
- In (5.49) the "\(=0\)" is omitted: the Fitzhugh–Nagumo equation is
  \(u_t-u_{xx}+u(u-1)(u-a)=0\) ([BCA.05.2.07]).
- The sentence after (5.98) says "direct application of the nonclassical method to the PDE
  (5.97)"; (5.97) are the determining equations and the PDE is (5.92) ([BCA.05.2.15]).
- In (5.137)–(5.138) the constant \(m\) is not defined; invariance of (5.126) and (5.127) with
  \(K=|v|^{2k}\) requires \(m=k\) ([BCA.05.3.09]).
- In §5.3.5 (p. 344) "For \(k=-1\), the potential system ... has nine point symmetries" is read
  as \(k\ne-1\) (the second occurrence is \(k=-1\)); likewise "with respect to the
  constitutive parameter \(k=0\)" (p. 343) means \(k\ne0\) ([BCA.05.3.09], [BCA.05.3.10]).
- In (5.160c), (5.167d) "curl V × B" denotes \(\operatorname{curl}(V\times B)\)
  ([BCA.05.3.13]).
- In (5.183) the code declares \(U_t=UU_x+U_{xxx}\), the opposite sign convention to (5.181);
  the multipliers and conservation laws printed afterwards refer to (5.181) (software code is
  outside the synopsis) ([BCA.05.4.01]).
- (5.57), (5.99), (5.105)–(5.106), (5.112), (5.171)–(5.172), Exercise 5.2.3(b) and the
  conformal symmetries \(Y_2\), \(Y_3\) of \(\mathbf{MW}\) beyond \(Y_1\) are recorded as
  printed where not stated otherwise in the synopsis.

[BCA.01.2.04]: SYNOPSIS-BCA.md#bca01204-one-parameter-contact-groups
[BCA.01.2.10]: SYNOPSIS-BCA.md#bca01210-first-order-generators-are-contact-generators
[BCA.01.2.20]: SYNOPSIS-BCA.md#bca01220-equivalence-group-of-the-nonlinear-diffusion-potential-system
[BCA.01.2.26]: SYNOPSIS-BCA.md#bca01226-recursion-operators-of-the-integrated-burgers-equation
[BCA.01.2.34]: SYNOPSIS-BCA.md#bca01234-recursion-operator-of-the-kdv-equation
[BCA.01.3.02]: SYNOPSIS-BCA.md#bca01302-constants-of-motion
[BCA.01.3.03]: SYNOPSIS-BCA.md#bca01303-conservation-laws-of-the-euler-equations-of-gas-dynamics
[BCA.01.3.04]: SYNOPSIS-BCA.md#bca01304-conservation-laws-of-the-kdv-equation
[BCA.01.3.08]: SYNOPSIS-BCA.md#bca01308-euler-operators-detect-divergences
[BCA.01.3.15]: SYNOPSIS-BCA.md#bca01315-zeroth-order-conservation-laws-of-a-nonlinear-telegraph-system
[BCA.01.3.16]: SYNOPSIS-BCA.md#bca01316-low-order-multipliers-of-the-kdv-equation
[BCA.01.3.29]: SYNOPSIS-BCA.md#bca01329-a-symmetry-that-is-not-a-multiplier-the-nonlinear-wave-speed-equation
[BCA.01.4.07]: SYNOPSIS-BCA.md#bca01407-noethers-formulation-is-a-special-case-of-boyers
[BCA.01.4.09]: SYNOPSIS-BCA.md#bca01409-variational-symmetries-and-conservation-laws-of-kleingordon-equations
[BCA.01.4.10]: SYNOPSIS-BCA.md#bca01410-the-scaling-symmetry-of-power-kleingordon-equations-is-not-variational
[BCA.01.4.11]: SYNOPSIS-BCA.md#bca01411-symmetries-versus-multipliers-of-generalized-kdv-equations
[BCA.01.4.12]: SYNOPSIS-BCA.md#bca01412-the-potential-form-of-generalized-kdv-equations
[BCA.01.4.13]: SYNOPSIS-BCA.md#bca01413-nonlinear-telegraph-systems-are-not-variational-equivalence-group
[BCA.01.4.17]: SYNOPSIS-BCA.md#bca01417-conservation-laws-of-a-boussinesq-system
[BCA.01.5.04]: SYNOPSIS-BCA.md#bca01504-higher-order-conservation-laws-from-a-one-parameter-symmetry-group
[BCA.01.5.09]: SYNOPSIS-BCA.md#bca01509-example-power-nonlinear-telegraph-system
[BCA.01.5.11]: SYNOPSIS-BCA.md#bca01511-fluxes-of-noncritical-scaling-homogeneous-conservation-laws
[BCA.01.5.15]: SYNOPSIS-BCA.md#bca01515-wave-equation-with-variable-speed-and-its-potential-system
[BCA.02.3.01]: SYNOPSIS-BCA.md#bca02301-point-symmetries-of-the-heat-and-burgers-equations
[BCA.02.3.02]: SYNOPSIS-BCA.md#bca02302-derivation-of-the-hopfcole-transformation
[BCA.02.3.05]: SYNOPSIS-BCA.md#bca02305-point-transformations-from-cylindrical-kdv-to-kdv
[BCA.02.4.03]: SYNOPSIS-BCA.md#bca02403-sufficient-conditions-for-invertible-linearization-of-systems
[BCA.02.4.08]: SYNOPSIS-BCA.md#bca02408-sufficient-conditions-for-contact-linearization-of-scalar-pdes
[BCA.02.4.09]: SYNOPSIS-BCA.md#bca02409-legendre-linearization-of-second-order-quasilinear-pdes
[BCA.02.4.11]: SYNOPSIS-BCA.md#bca02411-exercises-linearizations-through-infinite-symmetry-families
[BCA.02.5.03]: SYNOPSIS-BCA.md#bca02503-parabolic-equations-reducible-to-constant-coefficients
[BCA.02.5.05]: SYNOPSIS-BCA.md#bca02505-constant-coefficient-targets-of-the-biharmonic-equation
[BCA.03.3.03]: SYNOPSIS-BCA.md#bca03303-tree-for-the-nonlinear-diffusion-equation-hodograph-subsystems
[BCA.03.3.05]: SYNOPSIS-BCA.md#bca03305-further-potential-systems-and-a-subsystem-for-pgd
[BCA.03.4.03]: SYNOPSIS-BCA.md#bca03403-density-order-for-even-order-scalar-evolution-equations
[BCA.03.4.04]: SYNOPSIS-BCA.md#bca03404-diffusionconvection-equations-equivalence-group-and-local-conservation-laws
[BCA.03.4.05]: SYNOPSIS-BCA.md#bca03405-potential-systems-of-diffusionconvection-equations
[BCA.03.4.06]: SYNOPSIS-BCA.md#bca03406-nonlocal-conservation-laws-of-diffusionconvection-equations
[BCA.03.4.09]: SYNOPSIS-BCA.md#bca03409-additional-conservation-laws-for-power-nonlinearities-case-a
[BCA.03.4.10]: SYNOPSIS-BCA.md#bca03410-additional-conservation-laws-for-power-nonlinearities-case-b
[BCA.03.4.11]: SYNOPSIS-BCA.md#bca03411-additional-conservation-laws-for-power-nonlinearities-case-c
[BCA.03.5.04]: SYNOPSIS-BCA.md#bca03504-extended-tree-for-the-nonlinear-diffusion-equation
[BCA.03.5.07]: SYNOPSIS-BCA.md#bca03507-conservation-laws-of-the-linearized-wave-equation-and-redundancies
[BCA.03.5.08]: SYNOPSIS-BCA.md#bca03508-lagrange-pgd-system-equivalence-group-and-conservation-laws
[BCA.03.5.12]: SYNOPSIS-BCA.md#bca03512-polytropic-gas
[BCA.04.2.03]: SYNOPSIS-BCA.md#bca04203-nonlinear-diffusion-equation-equivalence-and-point-symmetries
[BCA.04.2.05]: SYNOPSIS-BCA.md#bca04205-couplet-potential-system-mathbfuva
[BCA.04.2.08]: SYNOPSIS-BCA.md#bca04208-the-potential-system-mathbfuv
[BCA.04.2.10]: SYNOPSIS-BCA.md#bca04210-the-potential-system-mathbftp
[BCA.04.2.12]: SYNOPSIS-BCA.md#bca04212-the-potential-system-mathbftr
[BCA.04.2.14]: SYNOPSIS-BCA.md#bca04214-the-subsystem-mathbf-tuvt
[BCA.04.2.16]: SYNOPSIS-BCA.md#bca04216-nonlocal-symmetries-of-telegraph-equations-from-mathbfuv1
[BCA.04.2.18]: SYNOPSIS-BCA.md#bca04218-power-nonlinearities-cases-b-and-c
[BCA.04.3.04]: SYNOPSIS-BCA.md#bca04304-thomas-equations
[BCA.04.3.07]: SYNOPSIS-BCA.md#bca04307-linear-parabolic-equations-mappable-to-the-backward-heat-equation
[BCA.04.3.09]: SYNOPSIS-BCA.md#bca04309-nonlocal-maps-to-the-backward-heat-equation
[BCA.04.3.10]: SYNOPSIS-BCA.md#bca04310-the-class-of-coefficients-obtained-theorem-433
[BCA.05.2.01]: SYNOPSIS-BCA.md#bca05201-invariant-solutions
[BCA.05.2.04]: SYNOPSIS-BCA.md#bca05204-the-nonclassical-method
[BCA.05.2.07]: SYNOPSIS-BCA.md#bca05207-nonclassical-solutions-of-the-boussinesq-equation
[BCA.05.2.10]: SYNOPSIS-BCA.md#bca05210-a-solution-of-generalized-polytropic-gas-dynamics-from-a-nonlocal-symmetry
[BCA.05.2.15]: SYNOPSIS-BCA.md#bca05215-nonclassical-determining-equations-for-nonlinear-heat-conduction
[BCA.05.3.01]: SYNOPSIS-BCA.md#bca05301-vector-potentials-and-gauges-in-three-dimensions
[BCA.05.3.09]: SYNOPSIS-BCA.md#bca05309-a-nonlocal-symmetry-from-a-nonlocally-related-subsystem
[BCA.05.3.10]: SYNOPSIS-BCA.md#bca05310-nonlocal-symmetries-from-a-curl-type-conservation-law
[BCA.05.3.11]: SYNOPSIS-BCA.md#bca05311-nonlocal-symmetries-of-the-21-dimensional-wave-equation
[BCA.05.3.12]: SYNOPSIS-BCA.md#bca05312-maxwells-equations-in-21-dimensions
[BCA.05.3.13]: SYNOPSIS-BCA.md#bca05313-incompressible-mhd-equilibria
[BCA.05.4.01]: SYNOPSIS-BCA.md#bca05401-mathematical-results-of-the-symbolic-software-examples
