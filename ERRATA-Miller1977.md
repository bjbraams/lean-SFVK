# Errata and source checks: Miller (1977), Symmetry and Separation of Variables

Reference: Willard Miller, Jr., *Symmetry and Separation of Variables*, Encyclopedia of
Mathematics and its Applications 4, Addison-Wesley, Reading, Mass., 1977; reissued by Cambridge
University Press, 1984. The local copy is
[References/Miller1977SymmetrySeparationVariables-CambridgeUP.EMA04.pdf](References/Miller1977SymmetrySeparationVariables-CambridgeUP.EMA04.pdf).

Locators use printed page numbers. To get the one-based PDF page number, add 30 (throughout the
book). Line numbers, where given, count from the top of the page; negative line numbers count
from the bottom.

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

- the location, as chapter, section, printed page and equation;
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries.

Synopsis entries cite errata by id. An erratum id \(\mathrm{M77\text{-}E}cc.s.nn\) is the
\(nn\)-th erratum located in section \(s\) of chapter \(cc\) (two-digit chapter number; \(s=0\)
for the chapter introduction; \(cc=\mathrm A,\mathrm B,\mathrm C\) for the appendices).

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

- Chapter 1. The Helmholtz Equation: 73 entries, 21 errata (Confirmed 21).
- Chapter 2. The Schrödinger and Heat Equations: 78 entries, 25 errata (Confirmed 23, Open check 2).
- Chapter 3. The Three-Variable Helmholtz and Laplace Equations: 83 entries, 20 errata (Confirmed 19, Normalization check 1).
- Chapter 4. The Wave Equation: 24 entries, 2 errata (Confirmed 2).
- Chapter 5. The Hypergeometric Function and Its Generalizations: 16 entries, 5 errata (Confirmed 5).
- Appendix A. Lie Groups and Algebras: 5 entries, 0 errata.
- Appendix B. Basic Properties of Special Functions: 11 entries, 2 errata (Confirmed 2).
- Appendix C. Elliptic Functions: 2 entries, 0 errata.
- Total: 292 entries, 75 errata (Confirmed 72, Normalization check 1, Open check 2).

## Chapter 1. The Helmholtz Equation

### M77-E01.2.01. Rectification of a first-order symmetry needs a nonvanishing vector field

Status: Confirmed.
Location: §1.2, p. 11, lines 13–16.
Printed: If \(L=A(\mathbf x)\partial_x+B(\mathbf x)\partial_y\) is a nonzero operator, it is always
possible to find coordinates \(u,v\) valid in a neighbourhood of any fixed point
\(\mathbf x_0\in\mathcal D\) such that \(L=\partial_u\).
Correct: This holds near \(\mathbf x_0\) when \((A(\mathbf x_0),B(\mathbf x_0))\ne(0,0)\).
Evidence: \(L=M=y\partial_x-x\partial_y\) is a nonzero operator whose vector field vanishes at
\(\mathbf x_0=0\); a change of coordinates maps a zero of a vector field to a zero, while
\(\partial_u\) has none. (Polar coordinates rectify \(M=-\partial_\theta\) only away from the
origin.)
Target: [M77.01.2.03].

### M77-E01.3.01. Gamma factor in the Bessel–parabolic overlap

Status: Confirmed.
Location: §1.3, p. 37, (3.50).
Printed: the first bracketed term is \(\dfrac{(-1)^n\Gamma(\frac12+i\mu)}{\Gamma(\frac12+i\mu-n)}
{}_2F_1\Big(\begin{matrix}\frac12+i\mu,\frac12-n\\1+i\mu-n\end{matrix}\Big|-1\Big)\).
Correct: the denominator is \(\Gamma(1+i\mu-n)\) (matching \(\Gamma(1-i\mu-n)\) in the second term
and the lower parameter \(1+i\mu-n\)).
Evidence: Direct quadrature of the integral in (3.50) (substitution \(t=\tan(\varphi/2)\)) for
\(n\in\{-1,0,1,2,3\}\), \(\mu\in\{0.3,1.1\}\) agrees with the corrected formula to \(10^{-12}\); the
printed formula fails, e.g. for \(n=0\), \(\mu=0.3\) the integral is \(0.59745\) (which equals the
Beta-function value \(2^{-3/2}\pi^{-1}\Gamma(\frac14+\frac{i\mu}2)\Gamma(\frac14-\frac{i\mu}2)/\Gamma(\frac12)\))
while the printed right side is \(0.45059+0.02076i\).
Target: [M77.01.3.14].

### M77-E01.3.02. Missing factor \(2^{-1/2}\) in the Mathieu–Bessel overlap

Status: Confirmed.
Location: §1.3, p. 37, (3.52).
Printed: \(\langle f^{(4)}_{2n+1,c},f^{(2)}_p\rangle=A^{(2n+1)}_{2m+1}\) if \(|p|=2m+1\), \(0\) otherwise.
Correct: \(\langle f^{(4)}_{2n+1,c},f^{(2)}_p\rangle=2^{-1/2}A^{(2n+1)}_{2m+1}\) if \(|p|=2m+1\).
Evidence: With \(f^{(4)}_{2n+1,c}=\pi^{-1/2}\mathrm{ce}_{2n+1}\), \(f^{(2)}_p=(2\pi)^{-1/2}e^{ip\varphi}\)
and \(\mathrm{ce}_{2n+1}=\frac12\sum_mA_{2m+1}(e^{i(2m+1)\varphi}+e^{-i(2m+1)\varphi}\)),
\(\int_{-\pi}^{\pi}\mathrm{ce}_{2n+1}e^{-ip\varphi}d\varphi=\pi A_{|p|}\), so the overlap is
\(\pi A_{|p|}/(\pi\sqrt2)\). Parseval check: (B.27) gives \(\sum_mA_{2m+1}^2=1\), and the printed
values would give \(\sum_p|\langle f^{(4)},f^{(2)}_p\rangle|^2=2\) for a unit vector.
Target: [M77.01.3.15].

### M77-E01.4.01. Klein–Gordon system 2: radial equation and solutions

Status: Confirmed.
Location: §1.4, p. 43, (4.23)–(4.24).
Printed: \(\big(\frac{d^2}{du^2}+\frac{\tau^2}{u^2}+\omega^2\big)U=0\); \(\Phi_\tau=\sqrt u\,J_\nu(\omega u)
e^{i\tau v}\), \(\nu^2=\frac14-\tau^2\).
Correct: \(U''+u^{-1}U'+(\tau^2u^{-2}+\omega^2)U=0\) and \(\Phi_\tau=J_{\pm i\tau}(\omega u)e^{i\tau v}\).
Evidence: For \(t=u\cosh v\), \(x=u\sinh v\), \(dt^2-dx^2=du^2-u^2dv^2\), so
\(\partial_{tt}-\partial_{xx}=\partial_{uu}+u^{-1}\partial_u-u^{-2}\partial_{vv}\). Substituting the
printed separated equations into the Klein–Gordon operator at random points leaves a residual of
order 1, while the corrected equations give 0 (to \(10^{-16}\)). The printed \(\sqrt u J_\nu\) solves
the printed equation (Liouville normal form) but \(\sqrt uJ_\nu(\omega u)e^{i\tau v}\) is not a
Klein–Gordon solution. The eigenvalue \(S_{\mathrm M}\Phi_\tau=-\tau^2\Phi_\tau\) is correct
(\(M=-\partial_v\)).
Target: [M77.01.4.05].

### M77-E01.4.02. Klein–Gordon systems 3 and 4: the operator \(\{M,P_2\}\) in parabolic coordinates

Status: Confirmed.
Location: §1.4, pp. 43–44, System 3 heading and System 4 heading.
Printed: \(S_{\mathrm D'}=\{M,P_2\}=u^2\partial_{vv}-v^2\partial_{uu}\), \(S_{\mathrm D'}\Phi_\lambda=
-\omega\lambda\Phi_\lambda\); System 4: \(S_{\mathrm D}=\{M,P_1\}=u^2\partial_{vv}-v^2\partial_{uu}\).
Correct: On solutions, \(\{M,P_2\}=(u^2-v^2)^{-1}(v^2\partial_{uu}-u^2\partial_{vv})\) and
\(\{M,P_2\}\Phi_\lambda=\omega\lambda\Phi_\lambda\) for the separated equations (4.26); in System 4
(\(t=uv\), \(x=\frac12(u^2+v^2)\)), \(\{M,P_1\}=(u^2-v^2)^{-1}(v^2\partial_{uu}-u^2\partial_{vv})\) on
solutions and \(\{M,P_1\}\Phi_\lambda=i\omega\lambda\Phi_\lambda\).
Evidence: The printed operator lacks the denominator (it is not homogeneous of degree 0 in the
coordinates). Computing \(\{M,P_2\}\) with \(M=-t\partial_x-x\partial_t\) (4.2) on \(UV\), where \(U,V\)
satisfy (4.26), gives the ratio \(\{M,P_2\}(UV)/(UV)=\omega\lambda\) at random points
(\(\omega=1.37\), \(\lambda=0.61\): \(0.8357=\omega\lambda\)), whereas
\((u^2-v^2)^{-1}(u^2\partial_{vv}-v^2\partial_{uu})(UV)=-\omega\lambda\,UV\); likewise for System 4
the ratio is \(+i\omega\lambda\).
Target: [M77.01.4.06].

### M77-E01.4.03. Klein–Gordon system 3: argument of the parabolic cylinder functions

Status: Confirmed.
Location: §1.4, p. 43, (4.27).
Printed: \(\Phi_\lambda=D_{(i\lambda-1)/2}(\varepsilon_1(1+i)\sqrt\omega\,u)D_{(i\lambda-1)/2}(\varepsilon_2
(1+i)\sqrt\omega\,v)\).
Correct: \(\Phi_\lambda=D_{(i\lambda-1)/2}(\varepsilon_1(1-i)\sqrt\omega\,u)D_{(i\lambda-1)/2}(\varepsilon_2
(1-i)\sqrt\omega\,v)\) (equivalently, keep \((1+i)\) and use the index \((-i\lambda-1)/2\)).
Evidence: \(D_\nu(cu)\) solves \(U''+c^2(\nu+\frac12-\frac{c^2u^2}4)U=0\). For \(c=(1+i)\sqrt\omega\)
(\(c^2=2i\omega\)) this is \(U''+(\omega^2u^2-2i\omega(\nu+\frac12))U=0\), which matches (4.26) only for
\(\nu=(-i\lambda-1)/2\). Numerically (\(\omega=1.3\), \(\lambda=0.7\), \(u=0.6\)) the printed function
leaves the residual \(1.35-0.51i\) in (4.26); the corrected ones leave \(<10^{-15}\).
Target: [M77.01.4.06].

### M77-E01.4.04. Klein–Gordon system 5: operator, separated solutions and eigenvalue

Status: Confirmed.
Location: §1.4, p. 44, System 5, after (4.29).
Printed: \(S_{\mathrm A}=(u+v)^{-1}(u\partial_{vv}-v\partial_{uu})\);
\(\varphi_\varepsilon(z)=(z+\lambda/\omega)^{1/2}J_{\varepsilon/3}[\frac{2\omega}3(z+\lambda/\omega)^{3/2}]\),
\(S_{\mathrm A}\Phi_\lambda=\lambda\Phi_\lambda\).
Correct: With the printed coordinates (4.29): \(S_{\mathrm A}=(u-v)^{-1}(u\partial_{vv}-v\partial_{uu})\)
on solutions; the separated equations are \(\varphi''+(4\omega^2z-\lambda)\varphi=0\), solved by
\(\varphi_\varepsilon(z)=(z-\lambda/4\omega^2)^{1/2}J_{\varepsilon/3}[\frac{4\omega}3(z-\lambda/4\omega^2)^{3/2}]\),
and \(S_{\mathrm A}\Phi_\lambda=\lambda\Phi_\lambda\).
Evidence: \(t+x=2(u+v)\), \(t-x=(u-v)^2\) give \(dt^2-dx^2=4(u-v)(du^2-dv^2)\), so the equation is
\((\partial_{uu}-\partial_{vv})\Phi+4\omega^2(u-v)\Phi=0\). The printed \(\varphi\) solves
\(\varphi''+(\omega^2z+\omega\lambda)\varphi=0\), a different equation. Numerically, with
\(U''+(4\omega^2u+c)U=0\), \(V''+(4\omega^2v+c)V=0\), the Klein–Gordon residual vanishes and
\(S_{\mathrm A}(UV)/(UV)=-c\) at random points.
Target: [M77.01.4.07].

### M77-E01.4.05. Klein–Gordon system 6: scale of the separated equation and sign of the eigenvalue

Status: Confirmed.
Location: §1.4, p. 44, (4.30)–(4.31) and the following line.
Printed: \(\big(\frac{d^2}{dz^2}+\omega^2\sinh z+\lambda\big)\varphi=0\); \(S\Phi_\lambda=4\lambda\Phi_\lambda\).
Correct: \(\varphi''+(\frac{\omega^2}8\sinh z+\lambda)\varphi=0\) for the printed coordinates (4.30), and
\(S\Phi_\lambda=-4\lambda\Phi_\lambda\).
Evidence: From (4.30), \(t+x=\cosh\frac{u-v}2\), \(t-x=\sinh\frac{u+v}2\), so
\(dt^2-dx^2=\frac14\sinh\frac{u-v}2\cosh\frac{u+v}2(du^2-dv^2)=\frac18(\sinh u-\sinh v)(du^2-dv^2)\).
With the printed equation the Klein–Gordon residual at random points is of order 10; with the
corrected one it vanishes. The printed operator form \(4(\sinh u-\sinh v)^{-1}(\sinh u\,\partial_{vv}
-\sinh v\,\partial_{uu})\) applied to \(\varphi(u)\varphi(v)\) gives \(-4\lambda\) (for either form of the
separated equation), and direct computation of \(M^2-P_1P_2\) gives the same.
Target: [M77.01.4.08].

### M77-E01.4.06. Klein–Gordon system 8: sign of the eigenvalue

Status: Confirmed.
Location: §1.4, p. 45, (4.36).
Printed: \(S_{\mathrm B}\Phi_{\nu^2}=-\nu^2\Phi_{\nu^2}\).
Correct: \(S_{\mathrm B}\Phi_{\nu^2}=\nu^2\Phi_{\nu^2}\).
Evidence: \(J_{\pm\nu}(\omega e^z)\) satisfies \(\varphi''=(\nu^2-\omega^2e^{2z})\varphi\); the printed
operator form \((e^{2v}-e^{2u})^{-1}(e^{2v}\partial_{uu}-e^{2u}\partial_{vv})\) then gives
\([e^{2v}(\nu^2-\omega^2e^{2u})-e^{2u}(\nu^2-\omega^2e^{2v})]/(e^{2v}-e^{2u})=\nu^2\). Direct computation
of \(M^2-(P_1+P_2)^2\) in the coordinates (4.35) gives the ratio \(\nu^2\) at random points, with zero
Klein–Gordon residual.
Target: [M77.01.4.09].

### M77-E01.4.07. Klein–Gordon system 9: sign of the eigenvalue

Status: Confirmed.
Location: §1.4, p. 45, line after (4.38).
Printed: \(S\Phi_\lambda=(\lambda-\omega^2/2)\Phi_\lambda\), with (4.38)
\(\big(\frac{d^2}{du^2}+\frac{\omega^2}2\cosh2u+\lambda\big)U=0\),
\(\big(\frac{d^2}{dv^2}-\frac{\omega^2}2\cosh2v+\lambda\big)V=0\).
Correct: \(S\Phi_\lambda=(\omega^2/2-\lambda)\Phi_\lambda\) (the separated equations (4.38) are correct).
Evidence: For \(t=\sinh u\cosh v\), \(x=\cosh u\sinh v\), \(dt^2-dx^2=(\cosh^2u+\sinh^2v)(du^2-dv^2)\),
and (4.38) reads \(U''=-(\omega^2\cosh^2u-\frac{\omega^2}2+\lambda)U\),
\(V''=(\omega^2\sinh^2v+\frac{\omega^2}2-\lambda)V\). The printed operator form
\((\cosh^2u+\sinh^2v)^{-1}(\cosh^2u\,\partial_{vv}+\sinh^2v\,\partial_{uu})\) then gives
\(\frac{\omega^2}2-\lambda\). Direct computation of \(M^2+P_2^2\) at random points gives the ratio
\(0.32845=\omega^2/2-\lambda\) (\(\omega=1.37\), \(\lambda=0.61\)), with zero Klein–Gordon residual.
Target: [M77.01.4.10].

### M77-E01.4.08. Klein–Gordon system 10(i): sign of the eigenvalue

Status: Confirmed.
Location: §1.4, p. 46, after (4.40).
Printed: \(L\Phi_\lambda=\lambda\Phi_\lambda\) for the coordinates (4.39) and equations (4.40).
Correct: \(L\Phi_\lambda=-\lambda\Phi_\lambda\) (for (4.41)–(4.42), \(L\Phi_\lambda=\lambda\Phi_\lambda\) is
correct).
Evidence: (4.40) is \(\varphi''=-(\omega^2\sinh^2z+\lambda)\varphi\); the printed form
\(L=(\sinh^2a-\sinh^2b)^{-1}(\sinh^2a\,\partial_{bb}-\sinh^2b\,\partial_{aa})\) gives
\([\sinh^2a(-\omega^2\sinh^2b-\lambda)-\sinh^2b(-\omega^2\sinh^2a-\lambda)]/(\sinh^2a-\sinh^2b)=-\lambda\).
Direct computation of \(M^2-P_2^2\) gives \(-\lambda\) for (i) and \(+\lambda\) for (ii) at random points,
with zero Klein–Gordon residual in both.
Target: [M77.01.4.11].

### M77-E01.5.01. Normalization of the Klein–Gordon inner product

Status: Confirmed.
Location: §1.5, p. 49, (5.5′).
Printed: \((\Phi_1,\Phi_2)=i\int_{-\infty}^{\infty}\Phi_1\partial_t\bar\Phi_2\,dx=-i\int(\partial_t\Phi_1)
\bar\Phi_2\,dx\) at \(t=t_0\), with \((\Phi_1,\Phi_2)=\langle h_1,h_2\rangle\) by (5.5).
Correct: both integrals must be multiplied by \((2\pi)^{-1}\).
Evidence: For \(\Phi_j=I(h_j)\), \(\int e^{i\omega x(\sinh y-\sinh y')}dx=2\pi\delta(\omega(\sinh y-\sinh y'))
=2\pi\delta(y-y')/(\omega\cosh y)\), and \(\partial_t\bar\Phi_2\) brings \(-i\omega\cosh y'\); hence
\(i\int\Phi_1\partial_t\bar\Phi_2dx=2\pi\langle h_1,h_2\rangle\).
Target: [M77.01.5.02].

### M77-E01.5.02. Evaluation of the System 2 eigenfunctions in \(\mathcal H\)

Status: Confirmed.
Location: §1.5, p. 51, (5.13).
Printed: \(\Phi^{\mathrm M}_\lambda=\frac{\sqrt2}\pi e^{-i\lambda v}K_{i\lambda}(i\omega u)\).
Correct: \(\Phi^{\mathrm M}_\lambda=\big(\frac2\pi\big)^{1/2}e^{-i\lambda v}K_{i\lambda}(-i\omega u)\) for
\(\mathrm{Im}\,u>0\) (boundary values for \(u>0\)).
Evidence: \(\int_{-\infty}^\infty e^{-z\cosh s+i\lambda s}ds=2K_{i\lambda}(z)\) for \(\mathrm{Re}\,z>0\);
convergence of (5.13) requires \(\mathrm{Im}(t\pm x)>0\), i.e. \(\mathrm{Im}\,u>0\), so \(z=-i\omega u\).
Numerically (\(\omega=1.3\), \(\lambda=0.7\), \(u=1+0.4i\), \(v=0.2\)) the integral is
\(0.000579+0.444262i\), equal to the corrected value; the printed value is \(-0.4543-0.6767i\).
Target: [M77.01.5.04].

### M77-E01.5.03. Overlaps between the \((\mathrm D,\alpha)\) and \((\mathrm D,\alpha')\) bases are conjugated

Status: Confirmed.
Location: §1.5, p. 52, display after (5.15).
Printed: \(\langle f^{\mathrm D,\alpha'}_m,f^{\mathrm D,\alpha}_n\rangle=\dfrac{e^{i\beta\pi}-1}{i\beta\pi}\),
\(\beta=\alpha'-\alpha+2(m-n)\).
Correct: \(\langle f^{\mathrm D,\alpha'}_m,f^{\mathrm D,\alpha}_n\rangle=\dfrac{1-e^{-i\beta\pi}}{i\beta\pi}\)
(the printed value is \(\langle f^{\mathrm D,\alpha}_n,f^{\mathrm D,\alpha'}_m\rangle\)).
Evidence: In \(L_2[0,\pi]\), \(f_n=\pi^{-1/2}e^{-i(\alpha+2n)u}\), so the overlap is
\(\pi^{-1}\int_0^\pi e^{-i\beta u}du=(1-e^{-i\beta\pi})/(i\beta\pi)\). Quadrature in \(L_2(\mathbb R)\)
with (5.15) (\(\alpha=0.6\), \(\alpha'=1.1\), \(m=n=0\)) gives \(0.63662-0.63662i\), the corrected value;
the printed value is \(0.63662+0.63662i\).
Target: [M77.01.5.05].

### M77-E01.5.04. Sign in the action of \(M\) on the \((\mathrm D,\alpha)\) basis

Status: Confirmed.
Location: §1.5, p. 52, (5.16).
Printed: \(Mf^{\mathrm D,\alpha}_n=-\sum_m\frac{2i}\pi\frac{\alpha+m+n}{4(n-m)^2-1}f^{\mathrm D,\alpha}_m\).
Correct: \(Mf^{\mathrm D,\alpha}_n=+\sum_m\frac{2i}\pi\frac{\alpha+m+n}{4(n-m)^2-1}f^{\mathrm D,\alpha}_m\).
Evidence: \(VMV^{-1}=\sin u\frac d{du}+\frac12\cos u\) on \(L_2[0,\pi]\) (\(M=d/dy\), \(e^y=\tan(u/2)\),
\(\tanh y=-\cos u\)); with \(\int_0^\pi\sin u\,e^{-2iju}du=2/(1-4j^2)\) and
\(\int_0^\pi\cos u\,e^{-2iju}du=4ij/(1-4j^2)\) one gets \(\langle Mf_n,f_m\rangle=\frac{2i}\pi\frac{\alpha+m+n}
{4(n-m)^2-1}\). Quadrature in \(L_2(\mathbb R)\) (\(\alpha=0.6\)): \(\langle Mf_0,f_0\rangle=-0.381972i\),
\(\langle Mf_0,f_1\rangle=0.339531i\), \(\langle Mf_1,f_{-1}\rangle=0.025465i\), matching the corrected
coefficients (\(-0.381972i\), \(0.339531i\), \(0.025465i\)).
Target: [M77.01.5.06].

### M77-E01.5.05. The parabolic-cylinder form of \(\Phi^{\mathrm D,\alpha}_n\)

Status: Confirmed.
Location: §1.5, p. 53, (5.17).
Printed: \(\Phi^{\mathrm D,\alpha}_n(u,v)=2\exp[3i\pi(\alpha+2n)/2]D_{-\alpha-2n-1/2}((2\omega)^{1/2}u)
D_{\alpha+2n-1/2}(i(2\omega)^{1/2}v)\).
Correct: \(\Phi^{\mathrm D,\alpha}_n(u,v)=2\exp[-i\pi(\alpha+2n)/2]D_{\alpha+2n-1/2}((2\omega)^{1/2}u)
D_{-\alpha-2n-1/2}(-i(2\omega)^{1/2}v)\), for \(t=uv\), \(x=\frac12(u^2+v^2)\) with
\(\mathrm{Re}\,u,\mathrm{Re}\,v>0\), \(\mathrm{Im}(t\pm x)>0\), and as boundary values for real
\(u,v>0\).
Evidence: In System 4 the eigenvalue \(2\omega k\) of \(S_{\mathrm D}\) (\(k=\alpha+2n\)) gives
\(U''+(2\omega k-\omega^2u^2)U=0\), solved by \(D_{k-1/2}(\pm(2\omega)^{1/2}u)\), while the printed
\(D_{-k-1/2}((2\omega)^{1/2}u)\) solves \(U''+(-2\omega k-\omega^2u^2)U=0\). Quadrature of
\(I(f^{\mathrm D,\alpha}_n)\) at complex points (e.g. \(\omega=0.9\), \(u+v=1.3e^{0.3i}\),
\(u-v=0.6e^{-0.4i}\); \((\alpha,n)=(0.25,1),(1.4,-1),(0.6,0)\)) agrees with the corrected formula to
\(10^{-10}\); a fit shows the printed product is not proportional to the integral.
Target: [M77.01.5.06].

### M77-E01.5.06. Kontorovich–Lebedev normalization and the System 7 solutions

Status: Confirmed.
Location: §1.5, p. 53, (5.18)–(5.19).
Printed: \(f^{\mathrm K}_\lambda=\pi^{-1}(2\lambda\sinh\lambda)^{1/2}K_{i\lambda}(\omega e^y)\);
\(\Phi^{\mathrm K}_\lambda(u,v)=2\pi^{-1}(\lambda\sinh\lambda)^{1/2}K_{i\lambda}(\omega u)K_{i\lambda}(-i\omega v)\).
Correct: \(f^{\mathrm K}_\lambda=\pi^{-1}(2\lambda\sinh\pi\lambda)^{1/2}K_{i\lambda}(\omega e^y)\);
\(\Phi^{\mathrm K}_\lambda(u,v)=2\pi^{-1}(2\lambda\sinh\pi\lambda)^{1/2}K_{i\lambda}(\omega u)K_{i\lambda}(i\omega v)\)
for \(u,v>0\), \(u>v\) (boundary values from \(\mathrm{Im}(t\pm x)>0\)).
Evidence: \(\int_0^\infty K_{i\lambda}(x)K_{i\lambda'}(x)\frac{dx}x=\frac{\pi^2\delta(\lambda-\lambda')}{2\lambda\sinh\pi
\lambda}\) (Kontorovich–Lebedev), and the source itself uses \(\sinh\mu\pi\) in (5.29), which checks
numerically with the corrected \(f^{\mathrm K}\) (\(\alpha=0.7\), \(n=1\), \(\mu=0.9\): both sides
\(0.0726675\)). For (5.19), quadrature of \(I(K_{i\lambda}(\omega e^y))\) at three complex points near
\(u,v>0\) with \(\mathrm{Im}(t\pm x)>0\) gives exactly \(2K_{i\lambda}(\omega u)K_{i\lambda}(i\omega v)\)
(ratio \(2.000\)); the printed \(K_{i\lambda}(-i\omega v)\) is not proportional.
Target: [M77.01.5.07].

### M77-E01.5.07. Closed form of \(\Phi^{\mathrm E}_\lambda\)

Status: Confirmed.
Location: §1.5, p. 55, (5.25).
Printed: \(\Phi^{\mathrm E}_\lambda=[-2i\omega^2(t+x)-2i\lambda]^{-1/2}\exp\{-[\omega^2(x^2-t^2)-\lambda(x-t)/
\omega]^{1/2}\}\).
Correct: \(\Phi^{\mathrm E}_\lambda=[2i\lambda-2i\omega^2(t+x)]^{-1/2}\exp\{-[\omega^2(x^2-t^2)-\lambda(x-t)]^{1/2}\}\).
Evidence: With \(s=e^y\), \(I(f^{\mathrm E}_\lambda)=(4\pi\omega)^{-1/2}\int_0^\infty s^{-1/2}e^{-As-B/s}ds\),
\(A=-\frac{i\omega}2(t+x)+\frac{i\lambda}{2\omega}\), \(B=-\frac{i\omega}2(t-x)\), and
\(\int_0^\infty s^{-1/2}e^{-As-B/s}ds=(\pi/A)^{1/2}e^{-2\sqrt{AB}}\), \(4AB=\omega^2(x^2-t^2)-\lambda(x-t)\). The
printed \(\lambda(x-t)/\omega\) is also dimensionally inconsistent. Numerically (\(\omega=1.3\),
\(\lambda=0.7\), \(t=0.4+0.9i\), \(x=0.2+0.3i\)): quadrature \(0.153509+0.055175i\) = corrected value;
printed value \(0.113294+0.088595i\).
Target: [M77.01.5.09].

### M77-E01.5.08. Reflection relation for the \((\mathrm D,\alpha)\)–\(M\) overlaps

Status: Confirmed.
Location: §1.5, p. 56, (5.27), last line.
Printed: \(\langle f^{\mathrm D,\alpha}_{-n},f^{\mathrm M}_\lambda\rangle=\overline{\langle f^{\mathrm D,\alpha}_n,
f^{\mathrm M}_{-\lambda}\rangle}\), \(\delta=\alpha+2n<0\).
Correct: The first display of (5.27) holds for every \(n\in\mathbb Z\) (no restriction on
\(\delta\)); the reflection relation holds for \(\alpha=0\) (where \(\overline{f^{\mathrm D,0}_n}=f^{\mathrm D,0}
_{-n}\)) but not for general \(\alpha\).
Evidence: \(\overline{f^{\mathrm D,\alpha}_n}=f^{\mathrm D,-\alpha}_{-n}\), not \(f^{\mathrm D,\alpha}_{-n}\).
Quadrature (\(\alpha=0.6\), \(\lambda=0.5\), \(n=1\)): left side \(-0.54301+0.74739i\), right side
\(0.05558+0.07650i\). The first display agrees with quadrature for \(n=-2,-1,0,1\) (e.g. \(n=1\):
\(-0.0146157+0.0201168i\) both).
Target: [M77.01.5.10].

### M77-E01.5.09. A matrix element with a stray group parameter

Status: Confirmed.
Location: §1.5, p. 57, (5.32), third line.
Printed: \(T_{\mu\lambda}(\theta,-a,0)=(-i/2)\exp[(\mu-\lambda)\pi/2]H^{(2)}_{i(\mu-\lambda)}(\omega a)\).
Correct: \(T_{\mu\lambda}(0,-a,0)=(-i/2)\exp[(\mu-\lambda)\pi/2]H^{(2)}_{i(\mu-\lambda)}(\omega a)\)
(for general \(\theta\) multiply by \(e^{i\mu\theta}\)).
Evidence: By (5.30), \(T_{\mu\lambda}(\theta,a,b)=e^{i\mu\theta}T_{\mu\lambda}(0,a,b)\), and the right side has no
\(\theta\). The value itself follows from \(H^{(2)}_\nu(x)=-\frac{e^{i\nu\pi/2}}{\pi i}\int e^{-ix\cosh t-\nu t}dt\)
with \(\nu=i(\mu-\lambda)\).
Target: [M77.01.5.11].

### M77-E01.7.01. Exponential factor in the Bessel form of the matrix elements

Status: Confirmed.
Location: §1.7, p. 66, (7.24).
Printed: \(T_{lj}(g)=\exp[(m_0+j)\tau](-\omega)^{l-j}J_{l-j}(\rho)\).
Correct: \(T_{lj}(g)=\exp[(m_0+l)\tau](-\omega)^{l-j}J_{l-j}(\rho)\), as in (7.22).
Evidence: The coefficient of \(z^l\) in \(\exp[-\alpha e^\tau z-\beta e^{-\tau}/z+(m_0+j)\tau]z^j\) carries
\(e^{(m_0+j)\tau}e^{(l-j)\tau}=e^{(m_0+l)\tau}\); for \(\alpha=\beta=0\), \(T_{ll}(g)=e^{(m_0+l)\tau}\) is
the eigenvalue of \(\exp(\tau P^0)\) on \(z^{m_0+l}\).
Target: [M77.01.7.05].

### Conventions and notation (not errata)

- §1.3, (3.1): the plane-wave transform uses Lebesgue measure \(d\varphi\) on \([-\pi,\pi)\) without
  the factor \(1/2\pi\); the inner product (3.3) is the matching unnormalized one.
- §1.3, (3.33): \(\cos(i\mu\pi)\) is written for \(\cosh\mu\pi\).
- §1.3, (3.41): \(\mathrm{Se}_n(\alpha,q)=i\,\mathrm{se}_n(i\alpha,q)\) differs in sign from the Bateman
  convention \(-i\,\mathrm{se}_n(i\alpha,q)\); the difference is absorbed in the undetermined constant
  \(S_n\) ([M77.01.3.11]).
- §1.4: the adjoint action is written \(L^g\) and the Lie algebra symbols \(P_1,P_2,M\) are reused
  for the Klein–Gordon generators (4.2), with \(M=-t\partial_x-x\partial_t\); the sign of \(M\) fixes
  the sign of \(\{M,P_j\}\) ([M77-E01.4.02]).
- §1.4, System 3: the operator is labelled \(S_{\mathrm D'}\) in the text but listed without a label in
  Table 2; Table 2 gives the coordinates of Systems 6–8 through \(t\pm x\) where the text gives
  \(t\), \(x\) separately (they agree).
- §1.5: (5.5′) is printed after (5.5) with a prime; locators keep the source's numbering.
- §1.7, (7.23): the symbol \(\omega\) is reused for a complex group parameter after \(\omega\) has
  been set to 1.

## Chapter 2. The Schrödinger and Heat Equations

### M77-E02.1.01. Sign of the oscillator term in \(\mathcal L_2\)

Status: Confirmed.
Location: §2.1, p. 82, line 6.
Printed: \(\mathcal L_2=\mathcal K_{-2}+\mathcal K_2=i\partial_{xx}-ix^2/4\in\mathcal G_2\).
Correct: \(\mathcal L_2=\mathcal K_{-2}+\mathcal K_2=i\partial_{xx}+ix^2/4\).
Evidence: \(\mathcal K_2=ix^2/4\) and \(\mathcal K_{-2}=i\partial_{xx}\) by (1.24); the printed value is \(\mathcal L_3\) (p. 81). The
equation stated next, \(i\partial_t\Psi=-\partial_{xx}\Psi-x^2\Psi/4\) (repulsive oscillator), and the kernel (1.43) both
correspond to \(\partial_t\Psi=(i\partial_{xx}+ix^2/4)\Psi\).
Target: [M77.02.1.11].

### M77-E02.1.02. The Airy solutions \(F^{(2)}_\lambda\)

Status: Confirmed.
Location: §2.1, p. 89, (1.51).
Printed: \(F_\lambda^{(2)}(t,x)=\exp[-\frac i4(\pi+\frac1{8v^2}-u^2v+\frac uv+\frac{4\lambda}v)]2^{1/6}\mathrm{Ai}[2^{2/3}(\frac u2+\lambda)]\),
\(x=uv+(2v)^{-1}\), \(t=v\).
Correct: \(F_\lambda^{(2)}(t,x)=v^{-1/2}\exp[-\frac i4(\pi+\frac1{12v^3}-u^2v+\frac uv+\frac{4\lambda}v)]2^{1/6}\mathrm{Ai}[2^{2/3}(\frac u2+\lambda)]\).
Evidence: Substituting \(\Psi=e^{iP(t,x)}\mathrm{Ai}(\alpha(t)x+\beta(t))\) with the printed Airy argument into
\(i\Psi_t+\Psi_{xx}=0\) and using \(\mathrm{Ai}''=z\mathrm{Ai}\) forces \(P=x^2/4t-x/2t^2-\lambda/t+1/6t^3+\frac i2\ln t\), i.e. the
factor \(t^{-1/2}\) and the term \(1/(12v^3)\) in the bracket. The printed function fails the equation (relative
residual \(0.63\) at \(t=0.8\), \(x=0.3\), \(\lambda=0.37\)). The corrected function satisfies it and the eigenvalue
equation \(i(K_2+K_{-1})F=\lambda F\), and it agrees with \(\exp(t\mathcal K_{-2})f^{(2)}_\lambda\) computed by Fourier
quadrature at complex \(t\) (\(t=0.8-0.5i\), \(1.1-0.7i\)) to 20 digits, including the constant \(e^{-i\pi/4}2^{1/6}\).
Target: [M77.02.1.20].

### M77-E02.1.03. Sign of the time phase of the plane waves

Status: Confirmed.
Location: §2.1, p. 89, (1.54).
Printed: \(F_\lambda^{(1)}(t,x)=(2\pi)^{-1/2}\exp[i(\lambda^2t-\lambda x)]\).
Correct: \(F_\lambda^{(1)}(t,x)=(2\pi)^{-1/2}\exp[-i(\lambda^2t+\lambda x)]\).
Evidence: \(\mathcal K_{-2}=i\partial_{xx}\) gives \(\mathcal K_{-2}e^{-i\lambda x}=-i\lambda^2e^{-i\lambda x}\). The printed function gives
\(i\Psi_t+\Psi_{xx}=-2\lambda^2\Psi\ne0\).
Target: [M77.02.1.21].

### M77-E02.1.04. Normalization of the Hermite–Mellin overlap

Status: Confirmed.
Location: §2.1, p. 90, (1.56).
Printed: the denominator is \(2\pi(2^nn!)^{1/2}\).
Correct: the denominator is \((2\pi)^{3/4}(2^nn!)^{1/2}\), i.e. the printed value times \((2\pi)^{1/4}\).
Evidence: Quadrature of \((2\pi)^{-1/2}\int_0^\infty f_n^{(4)}(\pm x)x^{i\lambda-1/2}dx\) with \(f_n^{(4)}\) from (1.34), for
\(n=0,\dots,3\) and both signs, gives the printed value times \(1.5832335=(2\pi)^{1/4}\) in every case. Also, (1.60) at
\(t=0\) has the denominator \((2\pi)^{3/4}(2^nn!)^{1/2}\).
Target: [M77.02.1.23].

### M77-E02.1.05. The Hermite–Airy generating function

Status: Confirmed.
Location: §2.1, p. 90, (1.57).
Printed: \(2^{2/3}\exp\{-i[\frac16+\lambda+(2y)^{1/2}]\}\mathrm{Ai}\{2^{2/3}[\frac14-i\lambda-i(2y)^{1/2}]\}=\sum_n\frac{(\sqrt2iy)^n}{(n!)^{1/2}}
\langle f_n^{(4)},f_\lambda^{(2)}\rangle\).
Correct: the left side is \((2\pi)^{1/4}2^{2/3}\exp(y^2+\sqrt2y+\lambda+\frac16)\,\mathrm{Ai}[2^{2/3}(\frac14+\lambda+\sqrt2y)]\).
Evidence: By the Hermite generating function (2.32), \(\sum_n\frac{a^n}{\sqrt{n!}}f_n^{(4)}(x)=(2\pi)^{-1/4}
\exp(ax-a^2/2-x^2/4)\). With \(a=\sqrt2iy\), the sum equals
\((2\pi)^{-3/4}e^{y^2}\int\exp(ix^3/12-x^2/4+ibx)\,dx\), \(b=\lambda+\sqrt2y\). The shift \(x=w-i\) removes the quadratic term and
gives \(e^{b+1/6}4^{1/3}2\pi\mathrm{Ai}(4^{1/3}(b+\frac14))\). At \(\lambda=0.4\), \(y=0.3\), direct quadrature of 25 terms gives
\(0.3993917\), which matches the corrected form; the printed form gives \(0.7374+0.4254i\).
Target: [M77.02.1.23].

### M77-E02.1.06. The Hermite–Fourier overlap

Status: Confirmed.
Location: §2.1, p. 90, (1.58).
Printed: \(\langle f_n^{(4)},f_\lambda^{(1)}\rangle=[n!(-2)^n\pi]^{-1/2}\exp(-\lambda^2)H_n[(2\lambda)^{1/2}]\).
Correct: \(\langle f_n^{(4)},f_\lambda^{(1)}\rangle=i^n[n!\,2^{n-1}(2\pi)^{1/2}]^{-1/2}\exp(-\lambda^2)H_n(\sqrt2\,\lambda)\).
Evidence: \(\int e^{-y^2/2}H_n(y)e^{iky}dy=\sqrt{2\pi}\,i^nH_n(k)e^{-k^2/2}\) with \(x=\sqrt2y\), \(k=\sqrt2\lambda\). The argument
must be \(\sqrt2\lambda\) (the printed \((2\lambda)^{1/2}\) is not even real for \(\lambda<0\)), and the modulus differs from the
printed one by \((2\pi)^{1/4}\), as in [M77-E02.1.04]. Quadrature at \(\lambda=0.6\), \(n=0,\dots,3\) agrees with the
corrected form (\(n=0\): \(0.623195\); printed \(0.393622\)).
Target: [M77.02.1.23].

### M77-E02.1.07. Sign in the Airy–Fourier overlap

Status: Confirmed.
Location: §2.1, p. 90, (1.59).
Printed: \(\langle f_\lambda^{(2)},f_\mu^{(1)}\rangle=2^{2/3}\mathrm{Ai}[2^{2/3}(\mu-\lambda)]\).
Correct: \(\langle f_\lambda^{(2)},f_\mu^{(1)}\rangle=2^{2/3}\mathrm{Ai}[2^{2/3}(\lambda-\mu)]\).
Evidence: \((2\pi)^{-1}\int e^{-i((\lambda-\mu)x+x^3/12)}dx\) with \(x=4^{1/3}s\) is
\((2\pi)^{-1}4^{1/3}\cdot2\pi\mathrm{Ai}(4^{1/3}(\lambda-\mu))\), using \(\mathrm{Ai}(z)=(2\pi)^{-1}\int e^{i(s^3/3+zs)}ds\). Numerically, at
\(\lambda=0.4\), \(\mu=-0.2\), Gaussian-damped quadrature gives \(0.2276\); the corrected form gives \(0.2270\) and the printed
form \(0.8484\).
Target: [M77.02.1.23].

### M77-E02.2.01. Spatial argument of \(\mathbf T(A_0)\)

Status: Confirmed.
Location: §2.2, p. 94, (2.11), first line.
Printed: \(\Psi\big(\frac{t-1}{t+1},\frac{(2x)^{1/2}}{t+1}\big)\).
Correct: \(\Psi\big(\frac{t-1}{t+1},\frac{\sqrt2\,x}{t+1}\big)\).
Evidence: (2.6) with \(\alpha=\delta=\beta=-\gamma=2^{-1/2}\) gives the argument \(x/(\delta+t\beta)=\sqrt2x/(1+t)\). The
two-variable analogue (7.7) and the Schrödinger analogue (1.21) both print \(\sqrt2x\).
Target: [M77.02.2.04].

### M77-E02.2.02. Sign of the multiplier in Table 7, system 4

Status: Confirmed.
Location: §2.2, p. 94, Table 7, row 4.
Printed: \(H_2+H_{-2}\), \(x=u(1+v^2)^{1/2}\), \(\mathcal R=u^2v/4\).
Correct: \(\mathcal R=-u^2v/4\).
Evidence: Substituting \(\Phi=e^{\mathcal R}U(u)V(v)\), \(t=v\), into \(\Phi_t-\Phi_{xx}=0\). With \(\mathcal R=-u^2v/4\) the equation divided by
\(UV\) becomes \(U''/U+u^2/4-(1+v^2)V'/V-v/2=0\), which separates. With the printed sign, mixed terms
\(u^2v^2/2\) and \(2uvU'/U\) remain. The two-variable Table 13, row 7 (\(H_{-2}+H_2\),
\(x=u(1+w^2)^{1/2}\)) has \(\mathcal R=-(u^2+v^2)w/4\).
Target: [M77.02.2.03].

### M77-E02.2.03. Factor 2 in the \(R_{nm}\) Hermite identities

Status: Confirmed.
Location: §2.2, p. 102, (2.40b) and (2.43); p. 104, (2.51).
Printed: (2.40b) \(\exp(-s^2\alpha^2-2zs\alpha)H_m(z+s\alpha-\beta/s)s^m=\sum_n(-\beta)^{m-n}L_n^{(m-n)}(-\alpha\beta)H_n(z)s^n\);
(2.43) \(H_m(z-\beta)=\sum_n\binom mn\beta^{m-n}H_n(z)\); (2.51) the same as (2.40b) with \(H_{\lambda+m}\),
\(L^{(m-n)}_{\lambda+n}\), \(H_{\lambda+n}\).
Correct: replace \((-\beta)^{m-n}L(\cdot)(-\alpha\beta)\) by \((-2\beta)^{m-n}L(\cdot)(-2\alpha\beta)\) in (2.40b) and (2.51), and
\(\beta^{m-n}\) by \((-2\beta)^{m-n}\) in (2.43).
Evidence: \(\exp(\alpha H_1)\exp(\beta H_{-1})\Phi_m=\exp(2\alpha zs-\alpha^2s^2)H_m(z-\alpha s+\beta/4s)s^m=\sum_nR_{nm}(\alpha,\beta)\Phi_n\) by
(2.39), with \(R_{nm}=(\beta/2)^{m-n}L_n^{(m-n)}(-\alpha\beta/2)\) (2.38). The substitution \(\alpha\to-\alpha\), \(\beta\to-4\beta\) gives the
corrected (2.40b). Numerically, at \(z=0.3\), \(\alpha=0.7\), \(s=0.4\), \(\beta=0.5\), \(m=1,2\), the printed (2.40b) is off by
\(0.39\) and \(0.22\); the corrected form agrees to \(10^{-26}\). For \(\lambda=0.37\), \(\beta=0.05\), \(m=0,\pm1\) the corrected (2.51)
agrees to all digits and the printed one does not. The corrected (2.43) is the binomial theorem for
\(H_m(z-\beta)\) (\(H_n'=2nH_{n-1}\)). With \(\beta=-v\), the corrected (2.51) reproduces the printed (2.56), which
has \((2v)^j\).
Target: [M77.02.2.11], [M77.02.2.12], [M77.02.2.13].

### M77-E02.3.01. Sign pairing in Table 9, system 2b

Status: Confirmed.
Location: §2.3, p. 107, Table 9, row 2b.
Printed: \(x=u[\pm(1-v^2)]^{1/2}\), \(\mathcal R=\pm u^2v/4\).
Correct: \(x=u[\pm(v^2-1)]^{1/2}\), \(\mathcal R=\pm u^2v/4\). Equivalently, \(\mathcal R=-u^2v/4\) when
\(x=u(1-v^2)^{1/2}\), \(|v|<1\), as in Table 6, system 3b.
Evidence: Substitution of \(e^{i\mathcal R}U(u)V(v)\) into \(i\Psi_t+\Psi_{xx}-a\Psi/x^2=0\). The pairs \(x=u(v^2-1)^{1/2}\),
\(\mathcal R=u^2v/4\) and \(x=u(1-v^2)^{1/2}\), \(\mathcal R=-u^2v/4\) separate. The pair \(x=u(1-v^2)^{1/2}\), \(\mathcal R=+u^2v/4\) leaves the
mixed terms \(-u^2v^2/2\) and \(2iuvU'/U\) (the same computation as for Table 6).
Target: [M77.02.3.01].

### M77-E02.3.02. Sign of the radial oscillator eigenvalues

Status: Confirmed.
Location: §2.3, p. 109, (3.10).
Printed: \(\lambda=\lambda_n=-2n-\frac\mu2-1\).
Correct: \(\lambda_n=2n+\frac\mu2+1\).
Evidence: \(i\mathcal L_3=-\partial_{xx}+a/x^2+x^2/4\) is a positive operator, and direct differentiation of \(f_n^{(3)}\) gives
\((-\partial_{xx}+a/x^2+x^2/4)f_n^{(3)}=(2n+\mu/2+1)f_n^{(3)}\) (checked at \(\mu=2.6\), \(n=0,1,2\)). The text on p. 110 uses
\(\exp(\beta\mathcal L_3)f_n^{(3)}=\exp[-i\beta(2n+\mu/2+1)]f_n^{(3)}\), which requires the positive sign.
Target: [M77.02.3.03].

### M77-E02.3.03. Normalization and phase of \(\Psi_n^{(3)}\)

Status: Confirmed.
Location: §2.3, p. 111, (3.14).
Printed: \(\Psi_n^{(3)}(t,x)=(-2)^n\exp[\pm i\pi(\mu+2)/4](\cdots)\), with no normalization constant.
Correct: \(\Psi_n^{(3)}(t,x)=\big(\frac{n!2^{-\mu/2}}{\Gamma(n+1+\mu/2)}\big)^{1/2}(-2)^n\exp[-i\pi(\mu+2)/4](\cdots)\) for all \(t\), with the
remaining factors as printed (principal powers of \(t\pm i\)).
Evidence: The printed function satisfies (3.1) (relative residual \(<10^{-20}\)). But as \(t\to0\) its ratio to
\(f_n^{(3)}\) is \(N_n^{-1}e^{i\pi(\mu+2)/2}\), where \(N_n\) is the constant of (3.10). For example, at \(\mu=2.6\), \(n=0\) the ratio is
\(0.99625+1.37123i\), of modulus \(1/N_0=1.695\) and argument \(0.3\pi\). The factor \((t-i)^{-\mu/4-3/4-n}(t+i)^{\mu/4+1/4+n}\) is
continuous through \(t=0\), so no sign change in \(t\) is possible. With the corrected constant and phase,
\(\Psi_n^{(3)}(0,x)=f_n^{(3)}(x)\).
Target: [M77.02.3.04].

### M77-E02.3.04. Factor in the Laguerre–Mellin overlap

Status: Confirmed.
Location: §2.3, p. 112, (3.20).
Printed: \(\langle f_n^{(3)},f_\lambda^{(2)}\rangle=\frac12[\cdots]^{1/2}\frac{\Gamma(-i\lambda/2+\mu/4+1/2)}{\Gamma(1+\mu/2)}{}_2F_1(-n,i\lambda/2+\mu/4+1/2;1+\mu/2;2)\).
Correct: drop the factor \(\frac12\) and put \(-i\lambda/2+\mu/4+\frac12\) as the second numerator parameter of \({}_2F_1\).
Equivalently, by Pfaff's transformation at argument 2, multiply the printed expression by \(2(-1)^n\).
Evidence: Quadrature of \((2\pi)^{-1/2}\int_0^\infty f_n^{(3)}(x)x^{-i\lambda-1/2}dx\) at \(\mu=2.6\), \(\lambda=0.8\) gives exactly
\(2.0\), \(-2.0\), \(2.0\) times the printed value for \(n=0,1,2\).
Target: [M77.02.3.05].

### M77-E02.4.01. Relation between \(a\) and \(l\) in the Laguerre form of the radial equation

Status: Confirmed.
Location: §2.4, p. 114, (4.5).
Printed: \(\beta=l+\frac14\), \(a=4(\frac1{16}-l^2)\).
Correct: \(a=4(l+\frac14)(l+\frac34)=4l^2+4l+\frac34\), with \(\beta=l+\frac14\).
Evidence: With \(s=\tau\), \(z=-x^2/4\tau\), \(\Psi=s^{-1/4}z^{-\beta}\Psi'\), symbolic substitution into
\((\partial_\tau-\partial_{xx}+a/x^2)\Psi\) yields \(z\partial_{zz}-(2l+z)\partial_z+s\partial_s+l\) only for \(a=4l^2+4l+\frac34\). Check: the
solution \(\Psi'=s^{-l}\) of (4.6) (\(n=0\) in (4.10)) corresponds to \(\Psi\propto x^{-2l-1/2}\), which solves
\(-\Psi_{xx}+a\Psi/x^2=0\) iff \(a=(2l+\frac12)(2l+\frac32)\). The printed operators \(J'^\pm,J'^0\) and the equation (4.6) are
consistent with this \(a\).
Target: [M77.02.4.02].

### M77-E02.5.01. Multipliers in Table 12

Status: Confirmed.
Location: §2.5, pp. 126–127, Table 12, rows 10b, 11b, 12b, 15, 17, and the definition of \(\varepsilon\) on p. 127.
Printed: \(\varepsilon=\pm1\) is the sign of \(1-w^2\); multipliers \(\varepsilon(u^2+v^2)w/4\) (10b), \(\varepsilon u^2w/4\) (11b),
\(\varepsilon(\sinh^2u+\cos^2v)/4\) (12b), \(wu^2/4\) (15), \(\varepsilon v^2w/4\) (17).
Correct: with \(\varepsilon=\operatorname{sign}(1-w^2)\), the multipliers are \(-\varepsilon(u^2+v^2)w/4\), \(-\varepsilon u^2w/4\),
\(-\varepsilon(\sinh^2u+\cos^2v)w/4\), \(wv^2/4\), \(-\varepsilon v^2w/4\). Equivalently, keep the printed signs with
\(\varepsilon=\operatorname{sign}(w^2-1)\) and add the factor \(w\) in 12b and replace \(u\) by \(v\) in 15.
Evidence: For \(x=s(w)X(u,v)\), the dilation term \(-i(s'/s)X\cdot\nabla_X\) from \(i\partial_t\) cancels against \(2i\nabla\mathcal R\cdot\nabla\) only for
\(\mathcal R=(s'/4s)|\mathbf x|^2\). For \(s=|1-w^2|^{1/2}\) this is \(-w|\mathbf x|^2/4(1-w^2)\). The one-variable case is Table 6, system
3b (\(\mathcal R=-u^2v/4\) for \(|v|<1\)), checked by direct substitution. The same rule gives row 7
(\(s=(1+w^2)^{1/2}\), \(\mathcal R=+(u^2+v^2)w/4\)) as printed. It gives row 9 \((\sinh^2u+\cos^2v)w/4\), which contains \(w\),
because \(|\mathbf x|^2=s^2(\sinh^2u+\cos^2v)\). Row 15 is Table 6, system 4 in the variable \(y=v(1+w^2)^{1/2}\); a multiplier
\(wu^2/4\) would destroy the exponential \(u\)-factor. The heat analogue, Table 13, prints \(w\) in 12b and \(-v^2w/4\)
in 15.
Target: [M77.02.5.05].

### M77-E02.5.02. Operator labels of systems 5a and 13 in Table 12

Status: Open check.
Location: §2.5, p. 126, Table 12, row 5a (\(K_2-2aP_1-2bP_2\), \(x=uw+a/w\), \(y=vw+b/w\)); p. 127, row 13.
Printed: \(K=K_2-2aP_1-2bP_2\) for the coordinates \(x=uw+a/w\), \(y=vw+b/w\).
Question: the coordinates suggest \(K=K_2+2aP_1+2bP_2\).
Evidence: In one variable, Table 6, system 2b pairs \(K_2+K_{-1}\) with \(x=uv+1/2v\). This was confirmed through
(1.51), corrected per [M77-E02.1.02]. By scaling, \(K_2+cP_1\) pairs with \(x_1=uw+c/2w\); see also [M77-E02.6.04],
where \(i(\mathcal K_2+a\mathcal P_1)\) leads to \(x_1=uw+a/2w\). So \(x=uw+a/w\) goes with \(K_2+2aP_1\), not \(K_2-2aP_1\).
The second-order operators \(S\) of rows 5a and 13, and the corresponding entries of Table 13, were not checked.
Target: [M77.02.5.05].

### M77-E02.5.03. The two-dimensional Hermite basis

Status: Confirmed.
Location: §2.5, p. 131, (5.27).
Printed: \(oc_{n,m}(\mathbf x)=(2^{m+n}\pi n!m!)^{-1/2}\exp(-\mathbf x\cdot\mathbf x/4)H_n(x_1/\sqrt2)H_n(x_2/\sqrt2)\).
Correct: \(oc_{n,m}(\mathbf x)=(2^{m+n+1}\pi n!m!)^{-1/2}\exp(-\mathbf x\cdot\mathbf x/4)H_n(x_1/\sqrt2)H_m(x_2/\sqrt2)\).
Evidence: \(\int e^{-x^2/2}H_n(x/\sqrt2)^2dx=\sqrt{2\pi}\,2^nn!\), so the squared norm of the product is \(2\pi2^{n+m}n!m!\)
(the product of two copies of (1.34)). The stated eigenvalues \(\mu=-n-\frac12\), \(\lambda+\mu=m+\frac12\) require \(H_m\) in
\(x_2\). The time-dependent form (6.1) has the constant \(2^{m+n+1}\pi n!m!\).
Target: [M77.02.5.09].

### M77-E02.6.01. The Oc basis functions

Status: Confirmed.
Location: §2.6, p. 133, (6.1).
Printed: \(\exp[\frac{i\pi(m+n-1)}2-\cdots](\frac{w+i}{w-i})^{(m+n)/2}(w-i)^{-1}H_m(u/\sqrt2)H_n(v/\sqrt2)\).
Correct: \(\exp[-\frac{i\pi(m+n+1)}2-\cdots]\frac{(w+i)^{m+n}}{(1+w^2)^{(m+n)/2}}(w-i)^{-1}H_n(u/\sqrt2)H_m(v/\sqrt2)\).
Evidence: Free evolution of each factor (as in (1.45)) gives the phase \(e^{-i(n+m+1)\tan^{-1}w}(1+w^2)^{-1/2}\). With
\(w\pm i=(1+w^2)^{1/2}e^{\pm i(\pi/2-\tan^{-1}w)}\), the printed phase equals this times \((-1)^{m+n}\), so at \(t=0\) it
gives \((-1)^{m+n}oc_{n,m}\). The corrected function satisfies the Schrödinger equation and equals \(oc_{n,m}\) at
\(t=0\) (numerical check for \((n,m)=(1,2)\)). The order \(H_n(u)H_m(v)\) follows [M77-E02.5.03].
Target: [M77.02.6.01].

### M77-E02.6.02. Normalization of the polar oscillator basis

Status: Confirmed.
Location: §2.6, pp. 133–134, (6.2)–(6.3); consequences in (6.31)–(6.33), (6.37).
Printed: \(or^+_{n,m}=[m!/2^m\pi(n+m)!]^{1/2}\cdots\cos m\theta\), \(or^-_{n,m}=\tan(n\theta)or^+_{n,m}\);
\(or^+_{\lambda,0}=(2/\pi n!)^{1/2}\exp(-r^2/4)L_n^{(0)}(r^2/2)\).
Correct: \(or^+_{n,m}=[n!/2^m\pi(n+m)!]^{1/2}\exp(-r^2/4)r^mL_n^{(m)}(r^2/2)\cos m\theta\), \(or^-_{n,m}=\tan(m\theta)or^+_{n,m}\);
\(or^+_{n,0}=(2\pi)^{-1/2}\exp(-r^2/4)L_n^{(0)}(r^2/2)\).
Evidence: \(\iint|or^+_{n,m}|^2=\pi\cdot2^m\int_0^\infty y^me^{-y}L_n^{(m)}(y)^2dy\) with \(y=r^2/2\), which is
\(\pi2^m(n+m)!/n!\) (for \(m=0\) the angular factor is \(2\pi\)). Numerical quadrature of the corrected functions gives
norm \(1.0\) for \((n,m)=(1,2),(0,1),(2,3)\). With the printed constant the squared norm is \(m!/n!\). The
time-dependent (6.4) has \(\tan(mv)\). The overlaps (6.31) (case \(p=m=0\): printed \((4\gamma/n!)^{1/2}\), correct
\(\gamma^{1/2}\)), (6.32), (6.33), (6.37) inherit the printed constants.
Target: [M77.02.6.02], [M77.02.6.09].

### M77-E02.6.03. The Or basis functions

Status: Confirmed.
Location: §2.6, p. 134, (6.4).
Printed: \(Or^+_{n,m}=K\big(\frac{m!}{\pi^32^m(n+m)!}\big)^{1/2}\frac{(-1)^{m+n}}{2^{2m}}\frac{(w+i)^{m/2+n}}{(w-i)^{m/2+n+1}}
\exp[\frac{u^2(iw-1)}4]L_n^{(m)}(\frac{u^2}2)\cos mv\), \(K=\sqrt2\) for \(m=0\), else \(K=1\).
Correct: \(Or^+_{n,m}=K[\frac{n!}{2^m\pi(n+m)!}]^{1/2}e^{-i\pi(2n+m+1)/2}\frac{(w+i)^{m/2+n}}{(w-i)^{m/2+n+1}}u^m
\exp[\frac{u^2(iw-1)}4]L_n^{(m)}(\frac{u^2}2)\cos mv\), with \(K=2^{-1/2}\) for \(m=0\), else \(K=1\).
Evidence: The lens transformation \(\Psi(t,\mathbf x)=(1+t^2)^{-1/2}e^{-i\lambda\tan^{-1}t}e^{i|\mathbf x|^2t/4(1+t^2)}f(\mathbf x/(1+t^2)^{1/2})\)
for an eigenfunction \(f\) of \(-\Delta_2+|\mathbf x|^2/4\) with eigenvalue \(\lambda=2n+m+1\) (the two-dimensional form of
(1.45)), together with \((w+i)^{a}(w-i)^{-a-1}=(1+w^2)^{-1/2}e^{i\pi\lambda/2}e^{-i\lambda\tan^{-1}w}\), \(a=m/2+n\). The factor \(u^m\)
is missing in print. The corrected function satisfies the equation (residual \(<10^{-20}\)) and equals
\(or^+_{n,m}\) at \(t=0\) for \((n,m)=(1,2),(0,1),(2,3)\).
Target: [M77.02.6.02].

### M77-E02.6.04. The Lc basis functions

Status: Confirmed.
Location: §2.6, p. 138, (6.17) and the coordinates below it.
Printed: \(Lc_{\lambda,\rho}=\frac{(9a)^{-1/3}}{8iw(2\pi|a|)^{1/2}}\exp[i((u^2+v^2)\frac w4-\frac{au}w-\frac{\rho v}2-\frac a{3w^3}-\frac\lambda w)]
\mathrm{Ai}[(36a)^{-1/3}(\frac ua+\frac\lambda a+\frac{\rho^2}{4a})]\), \(x_1=uw+a/w\), \(x_2=vw\), \(t=w\).
Correct (\(a>0\)): \(x_1=uw+a/2w\), \(x_2=vw\), and
\(Lc_{\lambda,\rho}=\frac{e^{-i\pi/4}2^{1/6}a^{-1/6}}{(4\pi i)^{1/2}w}\exp[i((u^2+v^2)\frac w4-\frac{au}{4w}-\frac{\rho v}2-\frac{a^2}{48w^3}-\frac\lambda w)]
\mathrm{Ai}[(\frac a2)^{1/3}(u+\frac{2\lambda}a+\frac{\rho^2}{2a})]\).
Evidence: The printed function fails the Schrödinger equation (relative residual \(3.9\) at \(t=0.6\),
\(\mathbf x=(0.7,0.4)\), \(a=0.8\)). The \(x_1\)-factor is the evolution of
\(\exp[-i(\Lambda x_1+x_1^3/12)/a]\), \(\Lambda=\lambda+\rho^2/4\). It follows from the corrected (1.51) by the scaling
\(x\to a^{1/3}x\), \(t\to a^{2/3}t\). The Airy argument is independent of \(w\) only for \(x_1=uw+a/2w\). The \(x_2\)-factor is the
free evolution of \(\delta(x_2-\rho)\). The corrected function satisfies the equation (residual \(10^{-21}\)).
Target: [M77.02.6.06].

### M77-E02.6.05. Airy generating function for the Lc–Oc overlaps

Status: Open check.
Location: §2.6, p. 143, (6.34).
Printed: \(2^{2/3}\exp[-i(1/6+\lambda+\rho^2/4+\sqrt{2y})]\mathrm{Ai}[2^{2/3}(1/4-i\lambda-i\rho^2/4-i(2y)^{1/2})]=\sum_n[((2i)^{1/2}y)^n/n!]C_n\)
(with \(a=-1\)).
Question: This has the same structure as (1.57), which is wrong ([M77-E02.1.05]). The one-variable computation
suggests a left side of the form \(c\,e^{y^2}\exp(\cdots+\sqrt2y)\mathrm{Ai}[2^{2/3}(\frac14+\cdots+\sqrt2y)]\) with real shifts. The
convention \(a=-1\) and the normalization of the \(C_n\) were not reconstructed.
Target: [M77.02.6.09].

### M77-E02.7.01. Sign convention for \(\varepsilon\) in Table 13

Status: Confirmed.
Location: §2.7, p. 149, Table 13, rows 10b, 11b, 12b, 17.
Printed: \(\varepsilon=\operatorname{sign}(1-w^2)\); multipliers \(-\varepsilon(u^2+v^2)w/4\), \(-\varepsilon u^2w/4\), \(-\varepsilon(\sinh^2u+\cos^2v)w/4\),
\(-\varepsilon v^2w/4\).
Correct: with \(\varepsilon=\operatorname{sign}(1-w^2)\), the multipliers are \(+\varepsilon(u^2+v^2)w/4\), \(+\varepsilon u^2w/4\),
\(+\varepsilon(\sinh^2u+\cos^2v)w/4\), \(+\varepsilon v^2w/4\). Equivalently, the printed signs hold with
\(\varepsilon=\operatorname{sign}(w^2-1)\).
Evidence: For \(\Phi=e^{\mathcal R}\phi\), \(x=s(w)X\), the dilation term from \(\partial_t\) cancels against \(-2\nabla\mathcal R\cdot\nabla\) only for
\(\mathcal R=-(s'/4s)|\mathbf x|^2\). This gives row 7 as printed (\(s=(1+w^2)^{1/2}\), \(\mathcal R=-(u^2+v^2)w/4\)) and
\(\mathcal R=+w|\mathbf x|^2/4(1-w^2)\) for \(s=|1-w^2|^{1/2}\). The same computation for the one-variable heat equation
confirms Table 7, row 4 corrected ([M77-E02.2.02]). This is the same convention slip as [M77-E02.5.01].
Target: [M77.02.7.02].

### M77-E02.9.01. Coefficient in Exercise 7

Status: Confirmed.
Location: Exercises, p. 159, Exercise 7.
Printed: \(H_{-2}\Phi_n=\frac12n(n-1)\Phi_{n-2}\).
Correct: \(H_{-2}\Phi_n=\frac14n(n-1)\Phi_{n-2}\).
Evidence: On solutions \(H_{-2}=H_{-1}^2\), and \(H_{-1}\Phi_n=(n/2)\Phi_{n-1}\) (stated in the same exercise) gives
\(\frac n2\cdot\frac{n-1}2\). This agrees with (2.33) and (2.46).
Target: [M77.02.9.01].

### Conventions and notation (not errata)

- §2.1, Table 6, row 4: the operator is printed \(K_2-K_{-2}\), the negative of \(L_3=K_{-2}-K_2\) used in (1.20) and the
  text; the orbit and the coordinates are the same.
- §2.1, (1.4): the basis element \(K_0=i\) is distinct from \(K^0=x\partial_x+2t\partial_t+\frac12\); the script versions follow
  the same convention.
- §2.2: the heat group acts on the left through \(\mathbf T(A)\) with \(\mathbf T\begin{pmatrix}1&\beta\\0&1\end{pmatrix}=\exp(-\beta H_2)\), a sign
  that differs from (1.17).
- §2.2, (2.26) and Exercise 7: \(H_\nu(z)=2^{\nu/2}e^{z^2/2}D_\nu(\sqrt2z)\) extends the physicists' Hermite polynomials to complex
  order; Mathlib's `Polynomial.hermite` is the probabilists' family.
- §2.3: the range "\(a\ge3/4\)" (\(\mu\ge2\)) is the limit-point range for \(-\partial_{xx}+a/x^2\) at \(0\); the endpoint \(a=3/4\) is included.
- §2.3, (3.12), (3.18), (3.19): the phase \(\exp[\mp i\pi(\mu+2)/4]\) uses "upper sign for \(t>0\)" conventions; (3.19) prints
  \(\pm\) where (3.12) has \(\mp\).
- §2.4, (4.22) and (4.24): \({}_2F_1(\alpha,\beta;\gamma;z)/\Gamma(\gamma)\) and \({}_1F_1/\Gamma(\nu+1)\) are understood as entire in the lower
  parameter.
- §2.5, Table 12: system names \(Ab^j\) (\(F,L,O,R\); \(c,r,p,e\)); \(w=t\) throughout.
- §2.6, (6.13): \(\cos(i\mu\pi)\) is written for \(\cosh\mu\pi\).

## Chapter 3. The Three-Variable Helmholtz and Laplace Equations

### M77-E03.1.01. Euler-angle degeneracy at \(\theta=\pi\)

Status: Confirmed.
Location: §3.1, p. 161, after (1.6).
Printed: the Euler angles are one to one except where \(\theta=0,\pi\), "in which cases only the sum
\(\varphi+\psi\) is uniquely determined".
Correct: at \(\theta=0\) only \(\varphi+\psi\) is determined; at \(\theta=\pi\) only \(\varphi-\psi\) is
determined.
Evidence: \(\exp(\pi\mathcal J_1)=\mathrm{diag}(1,-1,-1)\) conjugates \(\mathcal J_3\) to \(-\mathcal J_3\), so
\(A(\varphi,\pi,\psi)=\exp((\varphi-\psi)\mathcal J_3)\exp(\pi\mathcal J_1)\).
Target: [M77.03.1.02].

### M77-E03.1.02. Dimension of the space of second-order symmetries

Status: Confirmed.
Location: §3.1, pp. 162–163.
Printed: the factor space \(\mathcal S/\mathfrak q\) is 41-dimensional, with basis \(E\), the six
first-order operators and 34 purely second-order symmetrized operators; it is spanned by
\(\{J_l,J_m\},\{J_l,P_m\},\{P_l,P_m\}\) subject only to \(\mathbf J\cdot\mathbf P\equiv0\) and
\(\mathbf P\cdot\mathbf P=-\omega^2\).
Correct: \(\dim\mathcal S/\mathfrak q=26\): \(E\), six first-order operators and nineteen purely
second-order classes.
Evidence: there are only \(\binom{7}{2}=21\) symmetrized products of the six generators. As
differential operators, the 28 operators \(E,J_l,P_l\) and the 21 symmetrized products have rank 27
(computed from their coefficient vectors in the monomials \(x^\alpha\partial^\beta\)); the only relation
is \(\mathbf J\cdot\mathbf P=0\). Modulo \(Q=\mathbf P\cdot\mathbf P+\omega^2\) one more dimension drops,
giving \(1+6+19=26\). The printed counts contradict the printed spanning statement.
Target: [M77.03.1.04].

### M77-E03.1.03. Second sign choice in the parabolic separated solutions

Status: Confirmed.
Location: §3.1, p. 167, (1.25).
Printed: \(\Xi(\xi)=\xi^m\exp(\pm i\omega\xi^2/2)\,{}_1F_1(i\lambda/4\omega+(m+1)/2;m+1;\mp i\omega\xi^2)\),
\(H(\eta)=\eta^m\exp(\pm i\omega\eta^2/2)\,{}_1F_1(-i\lambda/4\omega+(m+1)/2;m+1;\mp i\omega\eta^2)\).
Correct: \(\Xi=\xi^m\exp(\pm i\omega\xi^2/2)\,{}_1F_1(\pm i\lambda/4\omega+(m+1)/2;m+1;\mp i\omega\xi^2)\) and
\(H=\eta^m\exp(\pm i\omega\eta^2/2)\,{}_1F_1(\mp i\lambda/4\omega+(m+1)/2;m+1;\mp i\omega\eta^2)\); by Kummer's
transformation both sign choices give the same functions.
Evidence: substituting into (1.24) at \(\omega=1.3\), \(\lambda=0.8\), \(\xi=0.9\), \(m=0,1,2\) gives residual
\(<10^{-15}\) for the upper signs and residual \(\approx1.2\)–\(1.8\) for the printed lower signs.
Target: [M77.03.1.13].

### M77-E03.1.04. Sign of \(c^2P_3^2\) in the paraboloidal operator

Status: Confirmed.
Location: §3.1, p. 164, Table 14, system 9; p. 167, (1.27); §3.2, p. 181, (2.55).
Printed: \(S_1=J_3^2-c^2P_3^2+c(\{J_2,P_1\}+\{J_1,P_2\})\).
Correct: \(S_1=J_3^2+c^2P_3^2+c(\{J_2,P_1\}+\{J_1,P_2\})\) (equivalently, modulo
\(\mathbf P\cdot\mathbf P=-\omega^2\), \(J_3^2-c^2(P_1^2+P_2^2)+c(\cdots)+c^2\omega^2\)). With this \(S_1\),
\(S_1\Psi=-\mu\Psi\) and \(q=\mu-c^2\omega^2/2\) in (1.26) are correct.
Evidence: on plane waves \(e^{i\mathbf k\cdot\mathbf x}\), \(|\mathbf k|=\omega\), the printed operators give
\([S_1,S_2]=-8ic^2\omega^3\sin^2\theta\cos\theta\ne0\) (i.e. \(8c^2P_3(P_1^2+P_2^2)\)), so they do not commute;
the general \(J_3^2+c^2(a_1P_1^2+a_2P_2^2+a_3P_3^2)+c(\cdots)\) commutes with \(S_2\) iff \(a_1=a_2\),
\(a_3=a_1+1\). In paraboloidal coordinates, for \(\Psi=A(\alpha)B(\beta)\Gamma(\gamma)\) satisfying (1.26),
the Helmholtz equation and \(S_2\Psi=\lambda\Psi\) hold, \(S_1\Psi/\Psi\) is not constant for the printed
\(S_1\), and equals \(-\mu\) for the corrected one (numerical evaluation at random points).
Target: [M77.03.1.07], [M77.03.1.14], [M77.03.2.21].

### M77-E03.1.05. Sign of the separation constant in the conical (Lamé) equations

Status: Confirmed.
Location: §3.1, p. 169, (1.35); §3.3, p. 184, (3.1) with p. 186, (3.8); p. 188, (3.19).
Printed: with \((J_1^2+bJ_2^2)\Psi=\lambda\Psi\), \(A''+(\lambda-l(l+1)k^2\mathrm{sn}^2\alpha)A=0\) (and
likewise for \(B\), \(E_j\), \(\mathcal G\)).
Correct: \(A''+(-\lambda-l(l+1)k^2\mathrm{sn}^2\alpha)A=0\); equivalently the Lamé parameter is \(h=-\lambda\),
where \(\lambda\) is the eigenvalue of \(J_1^2+bJ_2^2\).
Evidence: for \(l=1\) the harmonic \(z=rk\,\mathrm{sn}\,\alpha\,\mathrm{sn}\,\beta\) has \(A=\mathrm{sn}\,\alpha\), which
solves \(A''+(h-2k^2\mathrm{sn}^2)A=0\) with \(h=1+k^2\), while \(J_1z=-y\), \(J_1^2z=-z\), \(J_2^2z=-z\), so
\((J_1^2+bJ_2^2)z=-(1+k^2)z\). Likewise \(1+z^2\) and \(1-z^2\) in \(W_l\) (types \(\mathrm{cn}\), \(\mathrm{dn}\)) have
\(S'\)-eigenvalues \(-1,-k^2\) and Lamé parameters \(1,k^2\). A symbolic–numerical check of (1.35) in
conical coordinates confirms the Helmholtz and \(\mathbf J\cdot\mathbf J\) equations and fails for the printed
\(S_2\) equation.
Target: [M77.03.1.16], [M77.03.3.03], [M77.03.3.06].

### M77-E03.1.06. Sign of the second separation constant in the ellipsoidal system

Status: Confirmed.
Location: §3.1, p. 168, (1.29)–(1.30).
Printed: the separated equations \(\big(4h^{1/2}\frac d{d\xi}h^{1/2}\frac d{d\xi}+\lambda_1\xi+\lambda_2
+\omega^2\xi^2\big)E=0\) hold with \((\mathbf J\cdot\mathbf J+P_1^2+aP_2^2+(a+1)P_3^2)\Psi=\lambda_1\Psi\) and
\((J_2^2+aJ_1^2+aP_3^2)\Psi=\lambda_2\Psi\).
Correct: with (1.29) as printed, \((J_2^2+aJ_1^2+aP_3^2)\Psi=-\lambda_2\Psi\) (equivalently, keep
\(+\lambda_2\) in (1.30) and write \(-\lambda_2\) in (1.29)).
Evidence: in the coordinates of Table 14, row 10, for \(\Psi=E(\mu)E(\nu)E(\rho)\) with each factor satisfying
(1.29), symbolic differentiation followed by numerical evaluation at random points and random values of
\(E,E'\) gives residual \(<10^{-9}\) for the Helmholtz equation and the \(\lambda_1\) equation, residual
\(0.42\) for the printed \(\lambda_2\) equation, and \(10^{-13}\) when \(\lambda_2\) is replaced by \(-\lambda_2\).
Target: [M77.03.1.15].

### M77-E03.2.01. Phase convention of the Wigner \(D\)-functions

Status: Confirmed.
Location: §3.2, p. 173, (2.13) (and (2.16)).
Printed: \(\mathbf D(A)=\exp(\varphi J_3)\exp(\theta J_1)\exp(\psi J_3)\) has, in the basis (2.12), the matrix
elements \(D^l_{nm}(A)=i^{n-m}[\cdots]^{1/2}\exp[i(n\varphi+m\psi)]P_l^{-n,m}(\cos\theta)\).
Correct: the matrix elements are
\(i^{n-m}[\cdots]^{1/2}\exp[-i(n\varphi+m\psi)]P_l^{-n,m}(\cos\theta)\); the printed formula gives the matrix
of \(\exp(-\varphi J_3)\exp(\theta J_1)\exp(-\psi J_3)\). Correspondingly (2.16) reads
\(D^l_{0m}(\varphi,\theta,\psi)=i^m(4\pi/(2l+1))^{1/2}Y_l^m(\theta,-\psi)\).
Evidence: (2.12) gives \(J_3f_m^{(l)}=-imf_m^{(l)}\), so \(\exp(\psi J_3)f_m^{(l)}=e^{-im\psi}f_m^{(l)}\). Building
\(J_1,J_2,J_3\) from (2.12) and exponentiating, for \(l=1,2,3\) at \((\varphi,\theta,\psi)=(0.3,0.7,1.1)\) the
printed (2.13) differs from \(\exp(\varphi J_3)\exp(\theta J_1)\exp(\psi J_3)\) by up to 1.7 and agrees with
\(\exp(-\varphi J_3)\exp(\theta J_1)\exp(-\psi J_3)\) to \(10^{-15}\). The same sign is fixed on \(L_2(S_2)\)
by \(J_3=-\partial_\varphi\), \(J^0=-i\partial_\varphi\) in (2.6), (2.21).
Target: [M77.03.2.07], [M77.03.2.08].

### M77-E03.2.02. Constant in the parabolic Helmholtz solutions

Status: Confirmed.
Location: §3.2, p. 181, (2.53).
Printed: \(\Psi^{(8)}_{\lambda,m}=\frac{i^m\sqrt2}{\xi\eta\omega}\Gamma(\frac{1-m+i\lambda}2)
\Gamma(\frac{1-m-i\lambda}2)\mathcal M_{i\lambda/2,-m/2}\big[\frac{\exp(-i\pi/2)\omega\xi^2}{\sqrt2}\big]
\mathcal M_{i\lambda/2,-m/2}\big[\frac{\exp(i\pi/2)\omega\eta^2}{\sqrt2}\big]e^{im\varphi}\).
Correct: \(\Psi^{(8)}_{\lambda,m}=\frac{(-i)^m}{\xi\eta\omega}\Gamma(\frac{1-m+i\lambda}2)\Gamma(\frac{1-m-i\lambda}2)
\mathcal M_{i\lambda/2,-m/2}(e^{-i\pi/2}\omega\xi^2)\mathcal M_{i\lambda/2,-m/2}(e^{i\pi/2}\omega\eta^2)e^{im\varphi}\).
Evidence: with the arguments divided by \(\sqrt2\) the factors do not satisfy (1.24) (which requires the
arguments \(\mp i\omega\xi^2\)). Reading the \(\sqrt2\) as dividing each factor, numerical quadrature of
\(I(f^{(8)}_{\lambda,m})=i^me^{im\varphi}\int_0^\pi\tan^{-i\lambda}(\theta/2)e^{i\omega z\cos\theta}
J_m(\omega\xi\eta\sin\theta)\,d\theta\) at \(\omega=1.3\), \(\xi=0.8\), \(\eta=0.6\) gives the ratio (computed/printed)
\(=(-1)^m\sqrt2\) for \((\lambda,m)=(0.7,0),(0.7,1),(-0.4,2),(0.7,-1),(0.3,3)\).
Target: [M77.03.2.20].

### M77-E03.2.03. Sign of the exponential factor in the paraboloidal eigenfunctions

Status: Confirmed.
Location: §3.2, p. 181, (2.56).
Printed: \(f^{(9)}_{nt\lambda}=(2\pi)^{-1/2}\frac{[\tan(\theta/2)]^{i\lambda}}{\sin\theta}
\exp(-\frac{ic\omega}2\cos\theta\cos2\varphi)\,gt_n(\varphi;2c\omega,\lambda)\).
Correct: the factor is \(\exp(+\frac{ic\omega}2\cos\theta\cos2\varphi)\).
Evidence: on \(L_2(S_2)\), \(S_2=c(P_2^2-P_1^2)+\{J_2,P_1\}-\{J_1,P_2\}=c\omega^2\sin^2\theta\cos2\varphi
-2i\omega(\cos\theta+\sin\theta\partial_\theta)\). Applied to the printed \(f^{(9)}\) it gives
\(S_2f=(2\omega\lambda+2c\omega^2\sin^2\theta\cos2\varphi)f\); with the corrected sign
\(S_2f=2\omega\lambda f\) exactly (numerically, at \(\theta=0.7\), \(\varphi=0.4\), \(c=0.6\), \(\omega=1.3\),
\(\lambda=0.45\): \(1.1700\) versus \(2\omega\lambda=1.17\), and \(1.756\) for the printed sign).
Target: [M77.03.2.21].

### M77-E03.3.01. Normalization of the scalar product on \(W_l\)

Status: Confirmed.
Location: §3.3, p. 187, (3.11).
Printed: \((2l+1)!(g_1,g_2)=\pi^{-1}\iint(1+|z|^2)^{-2l-2}g_1\bar g_2\,dx\,dy\).
Correct: \((g_1,g_2)=(2l+1)!\,\pi^{-1}\iint(1+|z|^2)^{-2l-2}g_1\bar g_2\,dx\,dy\), which is consistent with
(3.10).
Evidence: \(\pi^{-1}\iint(1+|z|^2)^{-2l-2}|z|^{2(l-m)}dx\,dy=B(l-m+1,l+m+1)=\frac{(l-m)!(l+m)!}{(2l+1)!}\), so
the printed formula gives \((z^{l-m},z^{l-m})=(l-m)!(l+m)!/((2l+1)!)^2\) instead of \((l-m)!(l+m)!\); e.g.
\(l=1\), \(m=0\): \(1/36\) instead of \(1\).
Target: [M77.03.3.04].

### M77-E03.3.02. The operator \(S'\) on \(W_l\)

Status: Confirmed.
Location: §3.3, p. 188, display before (3.18).
Printed: \(S'=[(1-k)z^2-(1+k)][(1+k)z^2-(1-k)]\frac{d^2}{dz^2}+2(2l-1)z[1+k^2-z^2(1-k^2)]\frac d{dz}
+2l[1+k^2+(1-k^2)(2l-1)z^2]\).
Correct: \(S'=J_1^2+bJ_2^2\) equals \(-\frac14\) times the printed expression.
Evidence: computing \(J_1^2+k^2J_2^2\) from (3.12) symbolically gives the leading coefficient
\(\frac14(kz^2+k-z^2+1)(kz^2+k+z^2-1)=-\frac14[(1-k)z^2-(1+k)][(1+k)z^2-(1-k)]\), and the sum of
\(J_1^2+k^2J_2^2\) and \(\frac14\)(printed) vanishes identically. Check: \((J_1^2+bJ_2^2)z=-(1+b)z\).
Target: [M77.03.3.06].

### M77-E03.4.01. Spherical–prolate spheroidal overlaps

Status: Confirmed.
Location: §3.4, p. 192, (4.5).
Printed: for \(m'\ge0\): \(\delta_{mm'}(-1)^{(2m+l-n)/2}[\frac{(n-m)!(l+m)!(2n+1)}{(n+m)!(l-m)!(2l+1)}]^{1/2}
a^m_{n,l-n}\); for \(m'<0\): \(\delta_{mm'}(-1)^{(l-n)/2}[\frac{(n+m)!(2n+1)}{(n-m)!(2l+1)}]^{1/2}a^{|m|}_{n,l-n}\).
Correct: \(\delta_{mm'}\epsilon_m(-1)^{(l-n)/2}[\frac{(n-|m|)!(l+|m|)!(2n+1)}{(n+|m|)!(l-|m|)!(2l+1)}]^{1/2}
a^{|m|}_{n,l-n}(a^2\omega^2)\), \(\epsilon_m=1\) (\(m\ge0\)), \((-1)^m\) (\(m<0\)).
Evidence: inserting (2.46) into \(\int Y_l^m\overline{f^{(6)}_{n,m}}\,d\Omega\) and using
\(\int_{-1}^1P_l^{-|m|}P_l^{|m|}dx=(-1)^m\frac2{2l+1}\). At \(a=0\), where \(Ps_n^{|m|}=P_n^{|m|}\) and
\(a^{|m|}_{n,2k}=\delta_{k0}\): \(f^{(6)}_{1,1}=Y_1^1\) and \(f^{(6)}_{1,-1}=-Y_1^{-1}\), so the overlaps are
\(+1\) and \(-1\), whereas the printed formulas give \(-1\) and \(1/\sqrt2\).
Target: [M77.03.4.03].

### M77-E03.4.02. Spheroidal parameter in the cylindrical overlap

Status: Confirmed.
Location: §3.4, p. 192, (4.6).
Printed: \(Ps_n^{|m|}(\cos\gamma,a\omega^2)\).
Correct: \(Ps_n^{|m|}(\cos\gamma,a^2\omega^2)\).
Evidence: \(f^{(6)}_{n,m}\) in (2.45) has parameter \(a^2\omega^2\), and the overlap is
\(\int f^{(6)}_{n,m}\overline{f^{(2)}_{m',\gamma}}\,d\Omega\), which evaluates \(f^{(6)}\) at \(\theta=\gamma\); (4.7),
(4.8) print \(a^2\omega^2\).
Target: [M77.03.4.03].

### M77-E03.4.03. Complex conjugate of the Fourier coefficient in the elliptic-cylindrical overlap

Status: Confirmed.
Location: §3.4, p. 192, (4.8)–(4.9).
Printed: \(\langle f^{(6)}_{n,m},f^{(4)}_{n'p,\gamma}\rangle=[\cdots]^{1/2}Ps_n^{|m|}(\cos\gamma,a^2\omega^2)A_{n'}^m\).
Correct: the last factor is \(\overline{A^m_{n'}}=A^{-m}_{n'}\).
Evidence: \(\int_0^{2\pi}e^{im\varphi}\overline{\mathrm{pe}_{n'}(\varphi)}\,d\varphi=2\pi\overline{A^m_{n'}}\). For
\(p=s\), \(\mathrm{se}_{n'}\) is real and odd, so \(A^m_{n'}\) is purely imaginary with \(A^{-m}=-A^m\), and the
printed formula has the wrong sign (e.g. \(\mathrm{se}_1\to\sin\varphi\) as \(q\to0\): \(A^1_1=-i/2\)).
Target: [M77.03.4.03].

### M77-E03.5.01. Normalization of the traveling spherical waves

Status: Confirmed.
Location: §3.5, p. 196, (5.8).
Printed: \(\Psi_m^{(l)}=I(f_m^{(l)})=-i^l(\omega\rho)^{-1/2}H^{(1)}_{l+\frac12}(\omega\rho)Y_l^m(\theta,\varphi)\).
Correct: \(\Psi_m^{(l)}=-(2\pi^3)^{1/2}i^l(\omega\rho)^{-1/2}H^{(1)}_{l+\frac12}(\omega\rho)Y_l^m(\theta,\varphi)\).
Evidence: (5.5) is \(I((2\pi^3)^{-1/2})=-(\omega\rho)^{-1/2}H^{(1)}_{1/2}(\omega\rho)\) (consistent with the stated
value \(\Psi(0,0,z)=(i/\omega z)(2/\pi)^{1/2}e^{i\omega z}=(2\pi^3)^{-1/2}\cdot2\pi i\int_{-i}^\infty e^{-\omega\beta z}
d\beta\)), and \(f_0^{(0)}=(4\pi)^{-1/2}\) by (5.7). Hence
\(\Psi_0^{(0)}=(2\pi^3)^{1/2}(4\pi)^{-1/2}\cdot(5.5)\), while (5.8) gives \((4\pi)^{-1/2}\cdot(5.5)\); the
recurrences fix the same constant for all \(l\).
Target: [M77.03.5.02].

### M77-E03.5.02. Missing \(\omega\) in the expansion of \(\exp(\alpha P^0)f_l^{(l)}\)

Status: Normalization check.
Location: §3.5, p. 201, (5.27′).
Printed: \(\exp(\alpha P^0)f_l^{(l)}=(2/\alpha)^{l+\frac12}\Gamma(l+\frac12)\sum_n\frac{l+n+\frac12}{n!}
I_{l+n+\frac12}(\alpha)f_l^{(l+n)}\).
Correct: with \(P^0=\omega\rho\) as in (5.18), \(\alpha\) must be replaced by \(\alpha\omega\) on the right; the
printed form holds for \(\omega=1\).
Evidence: \(\exp(\alpha P^0)f_l^{(l)}=e^{\alpha\omega\rho}\Gamma(l+\frac12)(2\tau)^l\); expanding by (5.27) with
\(\nu=l+\frac12\) and argument \(\alpha\omega\), and \(f_l^{(l+n)}=n!\Gamma(l+\frac12)C_n^{l+\frac12}(\rho)(2\tau)^l\) by
(5.23), gives the corrected form. The source sets \(\omega=1\) explicitly only later, in (5.35) and (5.37).
Target: [M77.03.5.06].

### M77-E03.5.03. Missing factor in the Gegenbauer addition theorem

Status: Confirmed.
Location: §3.5, p. 202, (5.33).
Printed: \(I_{l+\frac12}(sS)(2S)^{-l-\frac12}=\Gamma(l+\frac12)\sum_n(l+n+\frac12)I_{l+n+\frac12}(s)
I_{l+n+\frac12}(\gamma)C_n^{l+\frac12}(\rho)\).
Correct: the right side carries the additional factor \(\gamma^{-l-\frac12}\).
Evidence: at \(l=0.3\), \(s=1.3\), \(\gamma=0.4\), \(\rho=0.3\), the left side is \(0.581366\), the printed right
side \(0.279317\); their ratio \(2.081383\) equals \(\gamma^{-l-1/2}\). (Compare the classical
\(w^{-\nu}I_\nu(w)=2^\nu\Gamma(\nu)\sum_k(\nu+k)s^{-\nu}I_{\nu+k}(s)\gamma^{-\nu}I_{\nu+k}(\gamma)C_k^\nu(\rho)\),
\(w=sS\).)
Target: [M77.03.5.07].

### M77-E03.5.04. Argument of the Bessel function in (5.35)

Status: Confirmed.
Location: §3.5, p. 202, (5.35).
Printed: \(C^{m+\frac12}_{l-m}(\rho\partial_s+\frac{1-\rho^2}s\partial_\rho-\frac{\rho m}s)I_{m+\frac12}(\omega)s^{-1/2}
=I_{l+\frac12}(s)C^{m+\frac12}_{l-m}(\rho)s^{-1/2}\).
Correct: \(I_{m+\frac12}(s)\) on the left (with \(\omega=1\)).
Evidence: for \(l=m\) (\(C_0=1\)) the printed identity reads \(I_{m+\frac12}(\omega)s^{-1/2}=I_{m+\frac12}(s)s^{-1/2}\),
false for \(s\ne\omega\); (5.34) with (5.32) gives the corrected form.
Target: [M77.03.5.08].

### M77-E03.6.01. Second-order relation (6.13 iii)

Status: Confirmed.
Location: §3.6, p. 206, (6.13)(iii).
Printed: \(\Gamma_{45}^2+\Gamma_{41}^2-\Gamma_{51}^2=\frac14+\Gamma_{23}^2\).
Correct: \(\Gamma_{41}^2-\Gamma_{45}^2-\Gamma_{51}^2=\frac14+\Gamma_{23}^2\) on the solution space.
Evidence: with the identifications (6.7), on harmonic exponentials \(e^{px_1+qx_2+i\sqrt{p^2+q^2}x_3}\) the
printed difference is a nonzero polynomial, while a numerical fit of
\(a\Gamma_{45}^2+b\Gamma_{41}^2+c\Gamma_{51}^2+d\Gamma_{23}^2+e=0\) at random points has the one-dimensional
solution \((a,b,c,d,e)=(4,-4,4,4,1)\). Relations (i), (ii), (iv) check exactly.
Target: [M77.03.6.04], [M77.03.6.11].

### M77-E03.7.01. Missing power of 2 in the cylindrical-wave generating function

Status: Confirmed.
Location: §3.7, p. 221, (7.29).
Printed: \(\Gamma(m+1)[\rho(w^2-1)^{1/2}]^{-m}e^{\rho w}I_m[\rho(w^2-1)^{1/2}]=\sum_n\frac{\Gamma(2m+1)}
{\Gamma(2m+n+1)}C_n^{m+\frac12}(w)\rho^n\).
Correct: \(\Gamma(m+1)[\rho(w^2-1)^{1/2}/2]^{-m}e^{\rho w}I_m[\rho(w^2-1)^{1/2}]=\sum_n\cdots\).
Evidence: as \(\rho\to0\) the printed left side tends to \(2^{-m}\) and the right side to \(1\); numerically
(right/left printed) \(=2^m\) for \(m=0,1,2,3\) at \((\rho,w)=(0.6,1.7)\) and \((0.2,0.4)\).
Target: [M77.03.7.09].

### Conventions and notation (not errata)

- The associated Legendre functions \(P_l^m\) of the source include the factor \((-1)^m\) (Ferrers
  functions with the Condon–Shortley phase); \(P_l^m=P_l^{0,-m}\) from (2.14) agrees with this.
- The source's \(J_l\) are \(-\) the usual angular-momentum vector fields:
  \(J_3=x_2\partial_1-x_1\partial_2\); \(J^0=iJ_3\) is the usual \(L_z=-i\partial_\varphi\).
- p. 166: the stated range \(0\le\alpha<2\pi\) for prolate spheroidal coordinates covers \(\mathbb R^3\)
  twice together with \(0\le\varphi<2\pi\); \(0\le\alpha\le\pi\) suffices (M77.03.1.11).
- p. 168: in Table 14, rows 10–11, and in (2.58), the coordinates are given as square roots; signs are
  fixed by the octant (or by the elliptic-function parametrizations (1.32), (1.34), (2.63)).
- p. 218: the source refers to a "Section 3.9" for Hilbert space expansions of the wave equation; the
  material is in Chapter 4.
- (2.53): the placement of \(\sqrt2\) in the printed formula is typographically ambiguous (as divisor of
  the argument or of the factor); see [M77-E03.2.02].

## Chapter 4. The Wave Equation

### M77-E04.1.01. Normalization and argument of the kernel \(\Delta_+\)

Status: Confirmed.
Location: §4.1, pp. 227–228, (1.25)–(1.27).
Printed: \(\sum_\alpha\bar\Psi_\alpha(x)\Psi_\alpha(x')=\Delta_+(x-x')=(16\pi^2)^{-1}\iint\exp[ik\cdot(x'-x)]\,
d\mu(\mathbf k)\), with \(\Delta_+(x)=2\pi i(t^2-r^2)^{-1/2}\) (\(t>r\)), \(-2\pi i(t^2-r^2)^{-1/2}\)
(\(t<-r\)), \(2\pi(r^2-t^2)^{-1/2}\) (\(-r<t<r\)), and \(\Psi(x)=\langle\Psi,\Delta_+(x'-x)\rangle\).
Correct: \(\sum_\alpha\bar\Psi_\alpha(x)\Psi_\alpha(x')=\Delta_+(x'-x)\) with
\(\Delta_+(y)=(16\pi^2)^{-1}\iint\exp(ik\cdot y)\,d\mu(\mathbf k)\), i.e. \((16\pi^2)^{-1}\) times the
printed three-case expression; then \(\Psi(x)=\langle\Psi,\Delta_+(x'-x)\rangle\) holds as printed.
Evidence: from (1.20) and completeness \(\sum_\alpha\bar f_\alpha(\mathbf k)f_\alpha(\mathbf l)=
\delta_\mu(\mathbf k,\mathbf l)\), the sum equals \((16\pi^2)^{-1}\iint e^{ik\cdot(x'-x)}d\mu\), a function
of \(x'-x\), not of \(x-x'\) (the two differ by complex conjugation). The reproducing property requires
the positive-energy function \(G(x')\) with \(\langle f,g\rangle=\Psi(x)\), i.e.
\(g(\mathbf k)=(4\pi)^{-1}e^{-ik\cdot x}\), so \(G(x')=(16\pi^2)^{-1}\iint e^{ik\cdot(x'-x)}d\mu\). Finally
\(\iint e^{ik\cdot y}d\mu=2\pi\int_0^\infty e^{ikt}J_0(kr)\,dk\), which equals the printed three-case
expression without any \((16\pi^2)^{-1}\) factor (checked numerically with an \(e^{-\epsilon k}\) damping
at \((t,r)=(2,1),(-2,1),(0.5,1)\): \(3.6276i\), \(-3.6276i\), \(7.2552\)).
Target: [M77.04.1.08].

### M77-E04.2.01. Phase in the Bargmann–Segal intertwining kernel

Status: Confirmed.
Location: §4.2, p. 233, (2.13).
Printed: \(U(\mathbf k,\mathbf z)=\pi^{-1/2}\exp(-k+z_1z_2)\cosh\{\sqrt{2k}\,[z_1\exp(i\theta/2)-z_2
\exp(i\theta/2)]\}\).
Correct: \(U(\mathbf k,\mathbf z)=\pi^{-1/2}\exp(-k+z_1z_2)\cosh\{\sqrt{2k}\,[z_1e^{-i\theta/2}-
z_2e^{i\theta/2}]\}\).
Evidence: \(U=\sum_{l,m}\bar f_m^{(l)}(\mathbf k)f_m^{(l)}(\mathbf z)\) with (2.2) and (2.10); the term with
\(z_1^{l+m}z_2^{l-m}\) carries \(e^{-im\theta}\), so \(z_1\) must be paired with \(e^{-i\theta/2}\) and
\(z_2\) with \(e^{i\theta/2}\). Numerically, at a sample point the truncated bilinear series sums to
\(0.36168+0.01972i\); the corrected closed form gives the same value, the printed one
\(0.32849+0.05021i\).
Target: [M77.04.2.04].

### Conventions and notation (not errata)

- p. 234: in §4.3 the source writes \(L_2(S_2)\) for the space on which \(E(2)\) acts via
  \(P_1=-i\omega\cos\theta\), \(P_2=-i\omega\sin\theta\), \(M_{12}=\partial_\theta\), and again on p. 236 for
  the \(SO(2,1)\) model (3.8); in both places the circle \(L_2(S_1)\) (functions of \(\theta\)) is meant.
- The running heads of pp. 225–236 read "4.1" although §§4.2–4.3 begin on pp. 230 and 234.
- (1.18): \(\partial_{ij}\) denotes \(\partial_{k_i}\partial_{k_j}\) on \(\mathcal H_\pm\).
- The integral kernels (1.30)–(1.32), (1.34), (1.35) (cited from [60]) are recorded as printed and were not
  independently checked.

## Chapter 5. The Hypergeometric Function and Its Generalizations

### M77-E05.1.01. Signs in the identification with \(sl(n+3,\mathbb C)\)

Status: Confirmed.
Location: §5.1, p. 248, (1.7).
Printed: \(E^{\beta_k\gamma}=-\mathcal E_{k+3,1}\), \(E_{\beta_k\gamma}=-\mathcal E_{1,k+3}\) (other identifications as in
M77.05.1.03).
Correct: \(E^{\beta_k\gamma}=\mathcal E_{k+3,1}\), \(E_{\beta_k\gamma}=\mathcal E_{1,k+3}\) (equivalently, keep the
printed signs and reverse those of \(E^\alpha,E_\alpha,E^\gamma,E_\gamma\)).
Evidence: from the action (1.4), \([E^\alpha,E^{\beta_k\gamma}]\Psi_c^{a,b}=b_k\Psi_{c+1}^{a+1,\hat b_k}=
E^{\alpha\beta_k\gamma}\Psi_c^{a,b}\), so \([E^\alpha,E^{\beta_k\gamma}]=E^{\alpha\beta_k\gamma}\); but
\([\mathcal E_{12},-\mathcal E_{k+3,1}]=\mathcal E_{k+3,2}\), the image of \(-E^{\alpha\beta_k\gamma}\). For
\(n=2\), all 276 commutators of the 24 operators (1.3) were computed symbolically: with the printed
identification 24 fail (each by a sign), and solving the resulting sign constraints over
\(\mathbb Z/2\) shows that the corrected identification above makes all 276 hold.
Target: [M77.05.1.03].

### M77-E05.1.02. Sign in the \(\gamma\) triplet

Status: Confirmed.
Location: §5.1, p. 250, (1.17); p. 251, before (1.21).
Printed: \(\{J^+,J^-,J^0\}=\{E^\gamma,E_\gamma,J_\gamma\}\) satisfies \([J^0,J^\pm]=\pm J^\pm\),
\([J^+,J^-]=2J^0\), and generates the action (1.21).
Correct: the triplet is \(\{E^\gamma,-E_\gamma,J_\gamma\}\); (1.21) is the action it generates.
Evidence: by (1.4), \(E^\gamma E_\gamma\Psi_c^{a,b}=(c-1-\sum b_j)(c-a-1)\Psi\) and
\(E_\gamma E^\gamma\Psi_c^{a,b}=(c-\sum b_j)(c-a)\Psi\), so \([E^\gamma,E_\gamma]=-(2c-a-\sum b_j-1)=
-2J_\gamma\) on the basis; also \([\mathcal E_{31},-\mathcal E_{13}]=-(\mathcal E_{33}-\mathcal E_{11})\) under (1.7).
For \(n=2\), the derivative of (1.21) at the identity in the direction \(\mathcal E_{21}\) equals \(+E_\gamma\),
whereas for the other six formulas (1.19), (1.20), (1.22)–(1.25) it equals \(-J^-\) (and \(\mathcal E_{12}\)
gives \(-J^+\) throughout), consistent with \(J^-=-E_\gamma\).
Target: [M77.05.1.06].

### M77-E05.2.01. Prefactor of \(B_h\) in the \(F_D\) generating function

Status: Confirmed.
Location: §5.2, p. 255, (2.14).
Printed: \(B_h=(b/a)^\alpha a^{-\gamma-h}c^h\binom{-\gamma}h{}_2F_1(-h,\alpha;\gamma;-1/bc)\).
Correct: \(B_h=(a/b)^\alpha a^{-\gamma-h}c^h\binom{-\gamma}h{}_2F_1(-h,\alpha;\gamma;-1/bc)\).
Evidence: at \(\mathbf z=0\) the left side of (2.13) is \((a+c\tau)^{\alpha-\gamma}(b+d\tau)^{-\alpha}\), whose
constant term is \(a^{\alpha-\gamma}b^{-\alpha}\), while the printed \(B_0=b^\alpha a^{-\alpha-\gamma}\). The
left-side prefactor is confirmed by deriving it from (1.19). Numerically
(\(a=1.2\), \(b=0.7\), \(c=0.4\), \(\alpha=0.37\), \(\gamma=1.91\)) the Taylor coefficients are
\(0.86174,-0.92821,0.94381,\dots\) and the printed \(B_h\) are \(0.57830,-0.62291,0.63338,\dots\), a constant
ratio \((b/a)^{2\alpha}=0.6711\); the full identity (2.13) with the corrected \(B_h\) holds for \(n=2\) to
\(10^{-22}\). The special cases (2.15) (\(a=b\)) and (2.16) (where the factor \((-w)^\alpha\) cancels) are
correct as printed.
Target: [M77.05.2.05].

### M77-E05.2.02. Laguerre coefficients \(B_h\)

Status: Confirmed.
Location: §5.2, p. 257, (2.20).
Printed: \(B_h=a^{-\gamma}e^{-b/a}(c/a)^hL_h^{(\gamma-1)}((ac)^{-1})\).
Correct: \(B_h=a^{-\gamma}e^{-b/a}(-c/a)^hL_h^{(\gamma-1)}(-(ac)^{-1})\).
Evidence: at \(\mathbf z=0\) the left side of (2.19) is \(e^{-(d\tau+b)/(a+c\tau)}(a+c\tau)^{-\gamma}\). With
\(ad-bc=1\), \((d\tau+b)/(a+c\tau)=b/a+(\tau/a^2)/(1-x)\), \(x=-c\tau/a\), so the left side is
\(a^{-\gamma}e^{-b/a}(1-x)^{-\gamma}\exp[-yx/(1-x)]\) with \(y=-1/(ac)\); the Laguerre generating function
\(\sum L_h^{(\gamma-1)}(y)x^h=(1-x)^{-\gamma}e^{-yx/(1-x)}\) gives the corrected \(B_h\). Numerically (\(n=2\),
\(a=1.2\), \(b=0.7\), \(c=0.4\), \(\tau=0.07\)) the printed version is off by \(0.031\) on a value \(0.361\); the
corrected one agrees to \(10^{-26}\). The case (2.21) (\(c\to0\)) is unaffected.
Target: [M77.05.2.07].

### M77-E05.2.03. Laguerre generating function for \(F_D\)

Status: Confirmed.
Location: §5.2, p. 257, (2.22).
Printed: right side \(\sum_hL_h^{(\gamma-1)}(w)F_D(-h;\beta_j;\gamma;z_j)\tau^h\).
Correct: \(\sum_hL_h^{(\gamma-1)}(-w)F_D(-h;\beta_j;\gamma;z_j)(-\tau)^h\).
Evidence: this is (2.19) with \(a=c=d^{-1}=w^{-1/2}\), \(b=0\), for which the corrected (2.20) gives
\(B_h=w^{\gamma/2}(-1)^hL_h^{(\gamma-1)}(-w)\) (the factor \(w^{\gamma/2}\) cancels against the left side).
Numerically (\(n=2\), \(w=0.4\), \(\tau=0.1\)) the printed right side differs from the left side by \(0.344\) on
a value \(0.814\); the corrected one agrees to \(10^{-26}\).
Target: [M77.05.2.07].

### Conventions and notation (not errata)

- (1.18) uses the ordering \(\mathbf T(A)=\exp(-bd^{-1}J^+)\exp(-cdJ^-)\exp(\tau J^0)\) of §2.4; with it
  \(J^+\leftrightarrow-\mathcal E_{12}\), \(J^-\leftrightarrow-\mathcal E_{21}\), \(J^0\leftrightarrow
  \mathrm{diag}(\frac12,-\frac12)\), and \(\mathbf T(A)\mathbf T(B)=\mathbf T(AB)\).
- (2.5): the variables \(z_j\) (\(j\ne k\)) and the variable \(z_k\) are written as two groups
  "\(\frac{z_k-z_j}{z_k-1},\frac{z_k}{z_k-1}\)" with parameters "\(b_j,b_k\)"; the formula is to be read with the
  \(k\)-th pair in its own position.
- Exercise 7 writes \({}_pF_q\) for a series whose upper parameters are \(\sigma\) (or \(-n\)) together
  with \(a_1,\dots,a_p\).

## Appendix A. Lie Groups and Algebras

No errata.

### Conventions and notation (not errata)

- Appendix A has no numbered sections; synopsis entries use \(s=0\) (M77.A.0.nn).
- The local group is real (\(W\subset\mathbb R^n\)) unless stated complex; Theorem A.3 requires real
  structure constants \(c^l_{jk}\), but the same construction applies verbatim to complex constants and
  complex local groups, which is how it is used in Chapter 5.

## Appendix B. Basic Properties of Special Functions

### M77-EB.2.01. Sign in Euler's integral for \({}_2F_1\)

Status: Confirmed.
Location: Appendix B.2, p. 266, integral representation of \({}_2F_1\).
Printed: \({}_2F_1(a,b;c;z)=\frac{\Gamma(c)}{\Gamma(b)\Gamma(c-b)}\int_0^1t^{b-1}(1-t)^{c-b-1}(1+tz)^{-a}dt\).
Correct: the integrand factor is \((1-tz)^{-a}\).
Evidence: expanding \((1-tz)^{-a}\) and integrating termwise with the beta integral gives
\(\sum(a)_n(b)_nz^n/(c)_nn!\); the printed factor gives \({}_2F_1(a,b;c;-z)\). Numerically (\(a=0.37\),
\(b=0.6\), \(c=1.9\), \(z=0.31\)) the printed integral differs from \({}_2F_1\) by \(-0.0739\), the corrected
one agrees to \(10^{-20}\). The stated condition \(|\arg(1-z)|<\pi\) fits the corrected form.
Target: [M77.B.2.01].

### M77-EB.3.01. Prefactor in the \({}_1F_1\) representation of \(D_\nu\)

Status: Confirmed.
Location: Appendix B.3, p. 269, (B.9iii).
Printed: \(D_\nu(x)=2^{1/2}\exp(-x^2/4)[\cdots]\).
Correct: \(D_\nu(x)=2^{\nu/2}\exp(-x^2/4)[\cdots]\), the bracket unchanged.
Evidence: at \(x=0\) the bracket is \(\sqrt\pi/\Gamma(\frac12-\frac\nu2)\) and
\(D_\nu(0)=2^{\nu/2}\sqrt\pi/\Gamma(\frac12-\frac\nu2)\) (Bateman, Whittaker–Watson); with \(2^{1/2}\) the
printed formula contradicts (B.11) for \(\nu=n\ne1\) (e.g. \(D_0(x)=e^{-x^2/4}\)). Numerically at
\(\nu=0.8\), \(x=1.7\) the printed form differs from \(D_\nu\) by \(0.0545\); with \(2^{\nu/2}\) it agrees to
\(10^{-16}\).
Target: [M77.B.3.02].

### Conventions and notation (not errata)

- (B.6) \(P_\nu^\mu,Q_\nu^\mu\) are the Legendre functions on \(\mathbb C\setminus(-\infty,1]\) (type 3), not the
  Ferrers functions on \((-1,1)\) used for spherical harmonics in Chapter 3.
- (B.10), (B.11) mix the variables \(x\) and \(z\) for \(D_\nu\).
- (B.12) \(H_n\) is the physicists' Hermite polynomial.
- (B.14): \((z/2)^\nu\) is the principal branch, \(|\arg z|<\pi\).
- (B.27): the normalization \(\int_{-\pi}^\pi u^2dx=\pi\) is Ince's (Bateman) normalization.

## Appendix C. Elliptic Functions

No errata.

### Conventions and notation (not errata)

- Appendix C has no numbered sections; synopsis entries use \(s=0\) (M77.C.0.nn).
- p. 275 carries the running head "References" although (C.3)–(C.6) belong to Appendix C.
- The source allows \(0\le k\le1\); \(K\) and the stated limits require \(k<1\) for \(K\), \(k>0\) for \(1/k\).
