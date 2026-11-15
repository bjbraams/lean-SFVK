# Errata and source checks: Xu (2017), Representations of Lie Algebras and Partial Differential Equations

Reference: Xiaoping Xu, *Representations of Lie Algebras and Partial Differential Equations*,
Springer Nature Singapore, 2017 (DOI 10.1007/978-981-10-6391-6). The local copy is
[References/Xu2017RepresentationsLieAlgebrasPartialDifferentialEquations-Springer.pdf](References/Xu2017RepresentationsLieAlgebrasPartialDifferentialEquations-Springer.pdf).
Synopsis: [SYNOPSIS-Xu2017](SYNOPSIS-Xu2017.md).

Locators use printed page numbers. The PDF omits blank pages, so the offset to the one-based PDF
page number changes between chapters: add 32 in Chapters 1–2, 31 in Chapter 3, 30 in Chapter 4,
29 in Chapter 5; for Chapters 6–15 see the chapter headings of the synopsis, which give the
printed and PDF page ranges. Line numbers, where given, count from the top of the page; negative
line numbers count from the bottom. Equation numbers \((c.s.n)\) are the source's.

## Status vocabulary

- **Confirmed.** A contradiction is exhibited. It may be a direct calculation, a special case
  or counterexample, a numerical evaluation, a standard definition fixed in the source, or a
  conflict between two displays of the source.
- **Normalization check.** Two displays cannot both hold under one stated convention. An
  unstated change of basis, coordinate, branch or normalization may explain the difference. The
  synopsis fixes one convention and states the conversion.
- **Open check.** A suspected problem that is not settled. The entry states the uncertainty
  and the conjectured correction. Formalization is expected to decide it.

Each erratum gives:

- the location, as chapter section, printed page, line and equation;
- the printed statement;
- the correct statement, or the open question;
- the evidence;
- the target synopsis entries.

Synopsis entries cite errata by id. An erratum id \(\mathrm{X17\text{-}E}cc.s.nn\) is the
\(nn\)-th erratum located in Section \(c.s\) of Chapter \(cc\) (two-digit chapter number;
\(s=0\) for the chapter introduction).

## Scope

These are observations about this edition, not an official publisher list. No claim is made
that formulas without an erratum are free of errors. Formulas that the synopsis marks "as
printed" were transcribed from the page images without an independent check. Corrected
formulas in the synopsis are statements to be formalized. They are not Lean proofs.
Garbling of the PDF text layer (for example lost slashes in \(\ne\), \(\notin\), \(\not\subset\),
or lost overlines) is not an erratum; every printed formula quoted here was read on the page
image. Slips confined to derivation steps of a proof, when the stated result is correct, are not
listed.

Each chapter section ends with a list of conventions and notation that are not errata, for
example a sign or normalization convention that differs from a modern reference.

## Summary by chapter

- Chapter 1. Preliminary of Lie Algebras: 46 entries, 3 errata (Confirmed 3).
- Chapter 2. Semisimple Lie Algebras: 31 entries, 1 erratum (Confirmed 1).
- Chapter 3. Root Systems: 34 entries, 7 errata (Confirmed 6, Normalization check 1).
- Chapter 4. Isomorphisms, Conjugacy and Exceptional Types: 23 entries, 2 errata (Confirmed 2).
- Chapter 5. Highest-Weight Representation Theory: 21 entries, 3 errata (Confirmed 3).
- Chapter 6. Representations of Special Linear Algebras: 66 entries, 12 errata (Confirmed 12).
- Chapter 7. Representations of Even Orthogonal Lie Algebras: 27 entries, 3 errata (Confirmed 3).
- Chapter 8. Representations of Odd Orthogonal Lie Algebras: 25 entries, 10 errata (Confirmed 9, Normalization check 1).
- Chapter 9. Representations of Symplectic Lie Algebras: 18 entries, 5 errata (Confirmed 4, Normalization check 1).
- Chapter 10. Representations of \(G_2\) and \(F_4\): 19 entries, 4 errata (Confirmed 4).
- Chapter 11. Representations of \(E_6\): 29 entries, 5 errata (Confirmed 4, Open check 1).
- Chapter 12. Representations of \(E_7\): 22 entries, 2 errata (Confirmed 1, Open check 1).
- Chapter 13. Oscillator Representations of gl(n|m) and osp(n|2m): 37 entries, 4 errata (Confirmed 4).
- Chapter 14. Representation Theoretic Codes: 22 entries, 5 errata (Confirmed 5).
- Chapter 15. Path Hypergeometric Functions: 41 entries, 10 errata (Confirmed 9, Open check 1).
- Total: 461 entries, 76 errata (Confirmed 70, Normalization check 3, Open check 3).

## Chapter 1. Preliminary of Lie Algebras

Source: Chapter 1, printed pp. 3–32 (PDF pp. 35–64).

### X17-E01.1.01. Bilinearity of an algebra product

Status: Confirmed.
Location: §1.1, p. 3, (1.1.1).
Printed: \(m(au+bv,w)=a\,m(u,v)+b\,m(v,w)\).
Correct: \(m(au+bv,w)=a\,m(u,w)+b\,m(v,w)\).
Evidence: Linearity in the first argument with \(w\) fixed: the printed first term
\(a\,m(u,v)\) does not involve \(w\); for \(b=0\) the printed identity would give
\(m(au,w)=a\,m(u,v)\) for all \(v\).
Target: [X17.01.1.01].

### X17-E01.1.02. Associativity of a group product

Status: Confirmed.
Location: §1.1, p. 4, (1.1.5).
Printed: \((g_1\cdot g_2)\cdot g_3=(g_1\cdot g_2)\cdot g_3\).
Correct: \((g_1\cdot g_2)\cdot g_3=g_1\cdot(g_2\cdot g_3)\).
Evidence: The printed equation is a tautology; the definition of a group requires
associativity.
Target: [X17.01.1.02].

### X17-E01.5.01. Last terms of the lower central series of \(\mathcal N_n\)

Status: Confirmed.
Location: §1.5, p. 23, (1.5.11).
Printed: \(\mathcal N_n^{n-1}=\mathbb FE_{1,n}\), \(\mathcal N_n^n=\{0\}\).
Correct: \(\mathcal N_n^{n-2}=\mathbb FE_{1,n}\) and \(\mathcal N_n^{n-1}=\{0\}\) (\(n\ge2\)).
Evidence: By (1.5.9)–(1.5.10), \(\mathcal N_n^r=\mathcal E_r=\sum_{j-i>r}\mathbb FE_{i,j}\) with
the source's indexing \(\mathcal G^0=\mathcal G\), \(\mathcal G^1=[\mathcal G,\mathcal G]\)
(1.5.1). Only \((i,j)=(1,n)\) has \(j-i>n-2\), and no pair has \(j-i>n-1\). For \(n=2\),
\(\mathcal N_2=\mathbb FE_{1,2}\) is abelian, so \(\mathcal N_2^1=[\mathcal N_2,\mathcal N_2]=0\),
while the printed formula gives \(\mathcal N_2^1=\mathbb FE_{1,2}\). Nilpotency of
\(\mathcal N_n\) is unaffected.
Target: [X17.01.5.03].

### Conventions and notation (not errata)

- The lower central series is indexed from \(0\) (\(\mathcal G^0=\mathcal G\)), as in Mathlib's
  `LieModule.lowerCentralSeries`; some texts start at \(\mathcal G^1=\mathcal G\).
- "Up-triangular" means upper triangular. A semisimple endomorphism means a diagonalizable one
  (over \(\mathbb C\)).
- A simple Lie algebra is required to have \(\dim>1\), which excludes the one-dimensional
  algebra; Mathlib's `LieAlgebra.IsSimple` requires instead non-abelian, which is equivalent.
- The exercise on the bracket \([u,v]_\xi=u\xi v-v\xi u\) (p. 5) asks for \(\xi\ne0\); the
  bracket is a Lie bracket for every \(\xi\).
- §1.4 introduces the split orthogonal models \(o'(n,\mathbb F)\); from Chapter 3 on the source
  writes \(o(n,\mathbb C)\) for these models.

## Chapter 2. Semisimple Lie Algebras

Source: Chapter 2, printed pp. 33–59 (PDF pp. 65–91).

### X17-E02.2.01. Invariant equations of the polynomial module

Status: Confirmed.
Location: §2.2, p. 40, (2.2.21).
Printed: \(\sum_{i,j\in I}\nu_{i,j}(\xi)\,x_i\,\partial_{x_j}(f)=0\), \(\xi\in\mathcal G\).
Correct: \(\sum_{i,j\in I}\nu_{i,j}(\xi)\,x_j\,\partial_{x_i}(f)=0\), \(\xi\in\mathcal G\), i.e.
\(\xi(f)=0\) for the action (2.2.18).
Evidence: The action defined in (2.2.18) is \(\xi(f)=\sum\nu_{i,j}(\xi)x_j\partial_{x_i}(f)\),
and the invariants (one-dimensional trivial submodules) are the \(f\) with \(\xi(f)=0\). The
printed operator is the transpose. Example: \(\mathfrak{sl}(2)\) on \(V=\mathbb F^2\) with
\(e(u_2)=u_1\), \(e(u_1)=0\), so \(\nu_{2,1}(e)=1\) and the other \(\nu_{i,j}(e)=0\). By (2.2.18),
\(e\) acts as \(x_1\partial_{x_2}\), which kills \(f=x_1\) (the image of the \(e\)-fixed vector
\(u_1\)); the printed operator \(x_2\partial_{x_1}\) does not kill \(x_1\).
Target: [X17.02.2.03].

### Conventions and notation (not errata)

- Invariance of a bilinear form on a module is \(\beta(\xi(u),v)=-\beta(u,\xi(v))\) (2.2.14); for
  the Killing form on the adjoint module this is \(\kappa([u,v],w)=\kappa(u,[v,w])\) (2.1.2).
- The Casimir operator (2.4.4) is defined only for a faithful representation and uses the trace
  form \(\beta(\xi,\zeta)=\mathrm{Tr}\,\phi(\xi)\phi(\zeta)\), not the Killing form; the
  "orthonormal basis" exists because \(\beta\) is a nondegenerate symmetric form over
  \(\mathbb C\).
- Lemma 2.2.1 is proved for finite-dimensional modules (minimal submodules, induction on the
  number of summands).
- Mathlib develops root space theory for Cartan subalgebras (`LieSubalgebra.IsCartanSubalgebra`)
  of Killing Lie algebras, where the source uses maximal toral subalgebras; Corollary 4.2.4
  identifies the two for semisimple algebras over \(\mathbb C\).

## Chapter 3. Root Systems

Source: Chapter 3, printed pp. 61–93 (PDF pp. 92–124).

### X17-E03.1.01. Normalization \((\varepsilon_i,\varepsilon_j)=\delta_{i,j}\) for \(\mathfrak{sl}(n)\)

Status: Normalization check.
Location: §3.1, p. 65, (3.1.31), with (3.1.10)–(3.1.12).
Printed: Replacing \(\kappa\) by \(\zeta(A,B)=\mathrm{Tr}\,AB\) in Example 3.1.1 (and by
\(\zeta/2\) in Examples 3.1.2–3.1.4), \((\varepsilon_i,\varepsilon_j)=\delta_{i,j}\) for
\(i,j\in\overline{1,n}\).
Correct: For \(\mathfrak{sl}(n,\mathbb C)\), the \(\varepsilon_i\in H^*\) of (3.1.11) satisfy
\(\sum_i\varepsilon_i=0\) and the form induced by \(\mathrm{Tr}\) gives \((\varepsilon_i,
\varepsilon_j)=\delta_{i,j}-1/n\). The values \((\alpha,\beta)\) for roots
\(\alpha,\beta\in\Phi_{A_{n-1}}\) coincide with those computed from \((\varepsilon_i,
\varepsilon_j)=\delta_{i,j}\) in \(\mathbb R^n\). For \(B_n,C_n,D_n\) with \(\zeta/2\), (3.1.31)
holds as printed.
Evidence: On \(H=\{\mathrm{diag}(a)\mid\sum a_i=0\}\), \(\varepsilon_1+\cdots+\varepsilon_n=0\), so
\((\sum\varepsilon_i,\sum\varepsilon_i)=0\), whereas the printed values give \(n\). The
\(\mathrm{Tr}\)-dual of \(\varepsilon_i\) is \(t_{\varepsilon_i}=E_{i,i}-\frac1nI\), so
\((\varepsilon_i,\varepsilon_j)=\mathrm{Tr}(t_{\varepsilon_i}t_{\varepsilon_j})=\delta_{i,j}-
\frac1n\). The source itself switches to the realization of \(A_{n-1}\) in the hyperplane
\(\sum a_i=0\) of \(\mathbb R^n\) with orthonormal \(\varepsilon_i\) in (3.2.64) and (3.4.11);
the synopsis uses that realization.
Target: [X17.03.1.03].

### X17-E03.2.01. The isomorphism \(S_n\ltimes\mathbb Z_2^n\cong W_{B_n}\)

Status: Confirmed.
Location: §3.2, p. 79, (3.2.72).
Printed: \(\nu[(\iota,\sum_ia_i\varepsilon_i)](\varepsilon_r)=(-1)^{a_r}\varepsilon_{\iota(r)}\).
Correct: \(\nu[(\iota,\sum_ia_i\varepsilon_i)](\varepsilon_r)=(-1)^{a_{\iota(r)}}
\varepsilon_{\iota(r)}\), i.e. \(\nu(\iota,\varsigma)=D_\varsigma P_\iota\) with
\(P_\iota\varepsilon_r=\varepsilon_{\iota(r)}\) and \(D_\varsigma\varepsilon_s=(-1)^{a_s}
\varepsilon_s\). With this \(\nu\), (3.2.73) and (3.2.75) hold.
Evidence: With the product (3.2.71), \((\iota_1,\varsigma_1)(\iota_2,\varsigma_2)=(\iota_1\iota_2,
\varsigma_1+\iota_1(\varsigma_2))\). Take \(n=2\): \((\mathrm{id},\varepsilon_1)\cdot((12),0)=
((12),\varepsilon_1)\). The printed \(\nu\) gives \(\nu((12),\varepsilon_1)(\varepsilon_1)=
-\varepsilon_2\), but \(\nu(\mathrm{id},\varepsilon_1)\nu((12),0)(\varepsilon_1)=
\nu(\mathrm{id},\varepsilon_1)(\varepsilon_2)=\varepsilon_2\), so the printed \(\nu\) is not a
homomorphism. The corrected \(\nu\) satisfies \(P_\iota D_\varsigma P_\iota^{-1}=
D_{\iota(\varsigma)}\), hence \(\nu(g_1)\nu(g_2)=D_{\varsigma_1+\iota_1(\varsigma_2)}
P_{\iota_1\iota_2}=\nu(g_1g_2)\).
Target: [X17.03.2.12].

### X17-E03.4.01. Fundamental weights of \(C_n\) and \(D_n\): summation index

Status: Confirmed.
Location: §3.4, p. 88, (3.4.23), and p. 89, (3.4.28).
Printed: \(\lambda_i=\sum_{r=1}^i\varepsilon_i\) (\(i\in\overline{1,n-1}\) for \(C_n\),
\(i\in\overline{1,n-2}\) for \(D_n\)).
Correct: \(\lambda_i=\sum_{r=1}^i\varepsilon_r\).
Evidence: Read literally, \(\lambda_2=2\varepsilon_2\), and \(\langle2\varepsilon_2,
\varepsilon_1-\varepsilon_2\rangle=-2\ne0\), contradicting \(\langle\lambda_i,\alpha_j\rangle=
\delta_{i,j}\) (3.4.3). The same weights for \(B_n\) in (3.4.18) are printed with
\(\varepsilon_r\), and \(\sum_{r=1}^i\varepsilon_r\) satisfies (3.4.3) for the bases (3.4.21),
(3.4.26).
Target: [X17.03.4.02].

### X17-E03.4.02. The \(E_8\) lattice is not \(\Lambda(D_8)\)

Status: Confirmed.
Location: §3.4, p. 89, (3.4.31).
Printed: \(\Lambda_r(E_8)=\Lambda(D_8)=\Lambda(E_8)\), "a self-dual integral even lattice".
Correct: \(\Lambda_r(E_8)=\Lambda(E_8)=\Lambda_r(D_8)\cup\big(\tfrac12(1,\dots,1,-1)+\Lambda_r(D_8)
\big)\) (with the root system of [X17-E03.4.03]); this is an index-2 sublattice of
\(\Lambda(D_8)=Q\cup(\frac12(1,\dots,1)+Q)\), \(Q=\mathbb Z^8\), and it is even and self-dual.
Evidence: \(\Lambda(D_8)\supset Q\ni\varepsilon_1\) with \((\varepsilon_1,\varepsilon_1)=1\), so
\(\Lambda(D_8)\) is not even, while (4.4.15) shows \((\alpha,\alpha)\in2\mathbb Z\) on
\(\Lambda_r(E_8)\). Also \(|\Lambda(D_8)/\Lambda_r(D_8)|=4\) by (3.4.30), while
\(\Lambda_r(E_8)\supset\Lambda_r(D_8)\) with index 2 (determinants \(\det CM(E_8)=1\),
\(\det CM(D_8)=4\) from (3.3.41)).
Target: [X17.03.4.03].

### X17-E03.4.03. Parity of the half-integral roots of \(E_8\)

Status: Confirmed.
Location: §3.4, p. 89, (3.4.32)–(3.4.33); the same root system is recalled in §4.4, p. 118,
(4.4.41).
Printed: \(\Phi_{E_8}=\{\frac12\sum_{i=1}^8(-1)^{\iota_i}\varepsilon_i\mid\iota_i\in\mathbb Z_2,
\sum_r\iota_r=0\text{ in }\mathbb Z_2\}\cup\Phi_{D_8}\) with base containing
\(\alpha_2=\frac12(\sum_{s=4}^8\varepsilon_s-\sum_{r=1}^3\varepsilon_r)\).
Correct: \(\sum_r\iota_r=1\) in \(\mathbb Z_2\) (an odd number of minus signs). With this
choice, (3.4.33) is a base, (3.4.34)–(3.4.36) are its fundamental weights, and (4.4.45)–(4.4.52)
list its positive roots.
Evidence: \(\alpha_2\) has three minus signs, so \(\alpha_2\notin\Phi_{E_8}\) as printed. The
half-integral root \(\frac12(\sum_{r=2}^8\varepsilon_r-\varepsilon_1)=\alpha_{(1,3,3,5,4,3,2,1)}\)
in (4.4.48) also has one minus sign. A direct computation with the odd convention gives: the
eight vectors of (3.4.33) have Cartan matrix of \(E_8\) in the numbering of Theorem 3.3.1,
\(\langle\lambda_i,\alpha_j\rangle=\delta_{i,j}\) for (3.4.34)–(3.4.36), and the vectors of
(4.4.45)–(4.4.52) are 120 distinct positive roots. (Both parity conventions give root systems
of type \(E_8\); they differ by the reflection \(\varepsilon_8\mapsto-\varepsilon_8\).)
Target: [X17.03.4.03], [X17.04.4.04].

### X17-E03.4.04. Second simple root of \(E_7\) and \(E_6\)

Status: Confirmed.
Location: §3.4, p. 90, (3.4.37)–(3.4.38).
Printed: \(\Pi_{E_7}\) and \(\Pi_{E_6}\) contain \(\frac12(\sum_{r=1}^3\varepsilon_r-
\sum_{s=4}^8\varepsilon_s)\).
Correct: \(\frac12(\sum_{s=4}^8\varepsilon_s-\sum_{r=1}^3\varepsilon_r)\), the \(\alpha_2\) of
(3.4.33); then \(\Pi_{E_7}=\{\alpha_1,\dots,\alpha_7\}\) and \(\Pi_{E_6}=\{\alpha_1,\dots,
\alpha_6\}\) are subsets of \(\Pi_{E_8}\), as used in (4.4.54)–(4.4.61).
Evidence: The printed vector is \(-\alpha_2\). With \(\alpha_4=\varepsilon_3-\varepsilon_4\),
\((-\alpha_2,\alpha_4)=\frac12(1+1)=1>0\), so the Cartan integer is \(+1\), contradicting
(3.1.51) for a base; the printed sets are not bases.
Target: [X17.03.4.04].

### X17-E03.4.05. \(\mathrm{Aut}\,\Phi/W\) for \(A_1\)

Status: Confirmed.
Location: §3.4, p. 93, Theorem 3.4.5, (3.4.64).
Printed: \(\mathrm{Aut}\,\Phi_{A_n}/W\cong\mathbb Z_2\) (no restriction on \(n\)).
Correct: \(\mathrm{Aut}\,\Phi_{A_n}/W\cong\mathbb Z_2\) for \(n\ge2\); \(\mathrm{Aut}\,
\Phi_{A_1}/W=\{1\}\).
Evidence: \(\Phi_{A_1}=\{\pm\alpha\}\) in \(\mathbb R\alpha\): \(\mathrm{Aut}\,\Phi=\{\pm1\}=
\{1,\sigma_\alpha\}=W\). The proof identifies \(\mathrm{Aut}\,\Phi/W\) with the diagram
automorphisms, and the one-node diagram has none.
Target: [X17.03.4.09].

### Conventions and notation (not errata)

- \(\langle\beta,\alpha\rangle=2(\beta,\alpha)/(\alpha,\alpha)\) is linear in \(\beta\) only. The
  Cartan matrix \(CM(\Pi)=(\langle\alpha_i,\alpha_j\rangle)\) agrees with Mathlib's
  `RootPairing.Base.cartanMatrix` and `CartanMatrix.*` (entry \((i,j)\) pairs root \(i\) with
  coroot \(j\)).
- The \(G_2\) numbering of Theorem 3.3.1 takes \(\alpha_1\) long and \(\alpha_2\) short (Bourbaki
  reverses it); \(\Pi_{G_2}\) in (3.4.46) and the construction in §4.4 follow the source's
  numbering, and so does Mathlib's `CartanMatrix.G₂`.
- The partial orders \(\prec\) (3.2.18) and \(\preceq\) (3.4.49) include equality.
  \(\Lambda^+=\Lambda\cap\overline{\mathcal C(\Pi)}\) uses the closed chamber; "strong dominant"
  means in the open chamber.
- The Weyl group of \(G_2\) is called \(D_6\) in the exercise on p. 93: the dihedral group of
  order 12.
- The \(E_8\) root system uses the half-integral vectors with an odd number of minus signs (after
  [X17-E03.4.03]); Bourbaki uses an even number with a different base.

## Chapter 4. Isomorphisms, Conjugacy and Exceptional Types

Source: Chapter 4, printed pp. 95–123 (PDF pp. 125–153).

### X17-E04.2.01. Bracket of generalized eigenspaces

Status: Confirmed.
Location: §4.2, p. 99, (4.2.3).
Printed: \([\mathcal G_a(\mathrm{ad}\,\xi),\mathcal G_b(\mathrm{ad}\,\xi)]=\mathcal G_{a+b}(\mathrm{ad}
\,\xi)\) for \(a,b\in\mathbb C\).
Correct: \([\mathcal G_a(\mathrm{ad}\,\xi),\mathcal G_b(\mathrm{ad}\,\xi)]\subset\mathcal
G_{a+b}(\mathrm{ad}\,\xi)\).
Evidence: The cited (1.5.60) gives only the inclusion. For \(\xi=0\) in a non-perfect
\(\mathcal G\) (e.g. \(\mathcal G\) abelian, nonzero), \(\mathcal G_0(\mathrm{ad}\,0)=\mathcal G\)
and \([\mathcal G,\mathcal G]\ne\mathcal G\). Only the inclusion is used later (Engel
subalgebras are subalgebras).
Target: [X17.04.2.01].

### X17-E04.3.01. Sign of the exponent in \(\sigma(a)\)

Status: Confirmed.
Location: §4.3, p. 111, (4.3.57), (4.3.58) and Lemma 4.3.8; p. 112, (4.3.64).
Printed: \(\sigma(a)(f(x_1,x_2))=f(-a^{-1}x_1,-ax_2)\);
\(\sigma(a)(x_1^{\ell_1}x_2^{\ell_2})=(-a)^{\ell_2-\ell_1}x_1^{\ell_1}x_2^{\ell_2}\); Lemma 4.3.8:
\(\sigma(a)(u)=(-a)^{-k}u\); (4.3.64): \(\sigma_i(a_i)|_{\mathcal G_{\alpha_j}}=
(-a_i)^{-\langle\alpha_j,\alpha_i\rangle}\mathrm{Id}\).
Correct: \(\sigma(a)(f(x_1,x_2))=f(-ax_1,-a^{-1}x_2)\); \(\sigma(a)(x_1^{\ell_1}x_2^{\ell_2})=
(-a)^{\ell_1-\ell_2}x_1^{\ell_1}x_2^{\ell_2}\); \(\sigma(a)(u)=(-a)^ku\);
\(\sigma_i(a_i)|_{\mathcal G_{\alpha_j}}=(-a_i)^{\langle\alpha_j,\alpha_i\rangle}\mathrm{Id}\).
Evidence: The printed intermediate step is correct:
\(T(a)=e^{aE_{1,2}}e^{-a^{-1}E_{2,1}}e^{aE_{1,2}}\) acts by \(T(a)f=f(-a^{-1}x_2,ax_1)\). Then
\(\sigma(a)f=T(a)(T(1)f)\) with \(T(1)f=f(-x_2,x_1)\) gives \(f(-ax_1,-a^{-1}x_2)\). On
\(x_1^{\ell_1}x_2^{\ell_2}\), of weight \(k=\ell_1-\ell_2\) for \(E_{1,1}-E_{2,2}=x_1\partial_{x_1}
-x_2\partial_{x_2}\), this is \((-1)^{\ell_1+\ell_2}a^{\ell_1-\ell_2}=(-a)^k\). Matrix check in
\(SL_2\) (the defining module, \(e_1\) of weight \(1\)): \(\exp(aE)\exp(-a^{-1}F)\exp(aE)\cdot
\exp(E)\exp(-F)\exp(E)=\mathrm{diag}(-a,-a^{-1})\). The conclusions (4.3.65)–(4.3.69) are
unaffected, since the \(a_i\) can be chosen for either sign of the exponents.
Target: [X17.04.3.07], [X17.04.3.08].

### Conventions and notation (not errata)

- The simply-laced construction (4.4.24) uses \([E_\alpha,E_{-\alpha}]=-\alpha\) and
  \([h,E_\alpha]=(h,\alpha)E_\alpha\) with \(H=\mathbb C\otimes\Lambda_r\); other sources take
  \([E_\alpha,E_{-\alpha}]=\alpha\) with a different cocycle.
- The case "\([E_\alpha,E_\beta]=0\) if \(\alpha+\beta\notin\Phi\)" in (4.4.25) is meant for
  \(\beta\ne-\alpha\).
- \(\mathcal E(\mathcal G)\) is generated by \(e^{\mathrm{ad}\,u}\) for strongly nilpotent \(u\);
  the opening sentence of §4.3 refers to the group \(\mathrm{Int}\,\mathcal G\) of inner
  automorphisms, but all statements are proved for \(\mathcal E(\mathcal G)\).
- The rank of a semisimple algebra is the dimension of a CSA; Mathlib's `LieAlgebra.rank` is
  defined differently (nil-rank).
- In §4.4 the root vectors of \(F_4\) are labelled by coefficient strings of the \(E_6\) simple
  roots, \(E_{(k_1,\dots,k_r)}=E_{\sum k_s\alpha_s}\), and bars denote both the negative-root
  vectors (4.4.44) and the roots of \(F_4\).

## Chapter 5. Highest-Weight Representation Theory

Source: Chapter 5, printed pp. 125–151 (PDF pp. 154–180).

### X17-E05.1.01. Multilinear expansion in the tensor algebra

Status: Confirmed.
Location: §5.1, p. 126, (5.1.5).
Printed: \(v_1\otimes v_2\otimes\cdots\otimes v_r=\sum a_{1,j_1}a_{2,j_2}\cdots a_{r,j_r}
u_{j_1}\otimes u_{j_1}\otimes\cdots\otimes u_{j_r}\).
Correct: \(\sum a_{1,j_1}a_{2,j_2}\cdots a_{r,j_r}\,u_{j_1}\otimes u_{j_2}\otimes\cdots\otimes
u_{j_r}\).
Evidence: Multilinearity of \(\otimes\) with \(v_i=\sum_ja_{i,j}u_j\) (5.1.4); the summation index
\(j_2\) otherwise does not appear in the tensor.
Target: [X17.05.1.01].

### X17-E05.2.01. Summation range in the maximal submodule of a tensor Verma module

Status: Confirmed.
Location: §5.2, p. 137, (5.2.61).
Printed: \(N(\lambda)\cong\sum_{i=1}^kM(\lambda_1)\otimes\cdots\otimes N(\lambda_i)\otimes\cdots
\otimes M(\lambda_s)\).
Correct: the sum runs over \(i=1,\dots,s\).
Evidence: There are \(s\) simple ideals in (5.2.50) and \(s\) tensor factors in (5.2.58);
\(k\) is not defined in this context.
Target: [X17.05.2.06].

### X17-E05.4.01. Image of the Casimir element in a representation

Status: Confirmed.
Location: §5.4, p. 141, sentence after (5.4.2).
Printed: "Indeed, for any representation \(\phi\) of \(\mathcal G\), \(\phi(\omega)=\omega_\phi\)
the Casimir operator defined in (2.4.4)."
Correct: \(\phi(\omega)=\Omega_\phi\) holds for \(\phi=\mathrm{ad}\) (and whenever the trace form of
\(\phi\) equals \(\kappa\)). In general, for faithful \(\phi\), on each simple ideal
\(\mathcal G_i\) the trace form of \(\phi\) is \(c_i\kappa\) with \(c_i>0\), and
\(\Omega_\phi=\sum_ic_i^{-1}\phi(\omega_i)\), where \(\omega=\sum_i\omega_i\) is the
decomposition of \(\omega\) over the simple ideals. \(\Omega_\phi\) is defined only for faithful
\(\phi\).
Evidence: (2.4.4) is built from a basis orthonormal for \(\beta(\xi,\zeta)=\mathrm{Tr}\,\phi(\xi)
\phi(\zeta)\), (5.4.1) from a basis orthonormal for \(\kappa\). For \(\mathfrak{sl}(2,\mathbb C)\)
in its defining representation, \(\kappa=4\beta\); \(\omega=\frac18h^2+\frac14(ef+fe)\), so
\(\phi(\omega)=\frac38I\), whereas \(\Omega_\phi=\frac32I=(\dim\mathcal G/\dim V)I\) by (2.4.10).
Target: [X17.05.4.01].

### Conventions and notation (not errata)

- Products of formal characters are the convolution \(*\) of (5.3.5); the source also writes
  \(\mathrm{ch}_U\cdot\mathrm{ch}_V\) (5.3.21) and juxtaposition in products such as \(q\).
- \(\mathrm{sn}(\sigma)=\det\sigma=(-1)^{\ell(\sigma)}\); \(\bar\mu\) denotes the dominant element
  of \(W\mu\) (5.4.54).
- In Example 5.4.1 dominant weights of \(\mathfrak{sl}(n)\) are written \(\mu-|\mu|\mathbf 1/n\)
  in the hyperplane \(\sum a_i=0\); \(x_i=\varepsilon_{\varepsilon_i}\) is a formal exponential.
- The source writes \(\omega_\phi\) in §5.4 for the Casimir operator called \(\Omega_\phi\) here
  (2.4.4).
- Remark 5.2.4 assumes \([\mathcal G_-,\mathcal G_+]\subset\mathcal G_0\); the construction of
  generalized Verma modules does not need it.

## Chapter 6. Representations of Special Linear Algebras

### X17-E06.1.01. Factor in the characteristic-coordinate wave equation

Status: Confirmed.
Location: §6.1, p. 160, (6.1.26)–(6.1.29), Theorem 6.1.2.
Printed: with \(z_0=x_1+t\), \(z_1=x_1-t\), (6.1.23) becomes \(2u_{z_0z_1}+\sum_{i,j\ge2}
g_{i,j}(z_1)u_{x_ix_j}=0\); \(T_1=2\partial_{z_0}\partial_{z_1}\), \(T_1^-=\frac12\int_{(z_0)}
\int_{(z_1)}\); the solution space (6.1.29) carries the factor \((-2)^{-m}\).
Correct: \(\partial_t^2-\partial_{x_1}^2=(\partial_{z_0}-\partial_{z_1})^2-(\partial_{z_0}+
\partial_{z_1})^2=-4\partial_{z_0}\partial_{z_1}\), so the transformed equation is
\(4u_{z_0z_1}+\sum g_{i,j}(z_1)u_{x_ix_j}=0\), \(T_1=4\partial_{z_0}\partial_{z_1}\),
\(T_1^-=\frac14\int_{(z_0)}\int_{(z_1)}\), and the factor in (6.1.29) is \((-4)^{-m}\).
Evidence: \(n=2\), \(g_{2,2}=1\): \(u=x_2^2-\frac12z_0z_1=x_2^2-\frac12(x_1^2-t^2)\) satisfies
\(u_{tt}-u_{x_1x_1}-u_{x_2x_2}=1+1-2=0\), but \(2u_{z_0z_1}+u_{x_2x_2}=-1+2\ne0\).
The printed (6.1.29) with \(f_0=1\), \(g_0=x_2^2\) gives
\(x_2^2+(-2)^{-1}\int_{(z_0)}\int_{(z_1)}\partial_{x_2}^2(x_2^2)=x_2^2-z_0z_1\),
for which \(u_{tt}-u_{x_1x_1}-u_{x_2x_2}=2+2-2\ne0\); with \((-4)^{-1}\) one
gets the solution \(x_2^2-\frac12z_0z_1\).
Target: [X17.06.1.03].

### X17-E06.2.01. Index in the definition of \(|\alpha|\)

Status: Confirmed.
Location: §6.2, p. 163, (6.2.11).
Printed: \(|\alpha|=\sum_{i=1}^n\alpha_n\).
Correct: \(|\alpha|=\sum_{i=1}^n\alpha_i\).
Evidence: the printed sum equals \(n\alpha_n\); all later uses ((6.2.13), (6.2.30), (6.2.42))
need the total degree, e.g. \(\mathcal A_m\) is spanned by the monomials of degree \(m\).
Target: [X17.06.2.01].

### X17-E06.2.02. Eigenvalue of \(\Delta\) on \(\eta^ig\)

Status: Confirmed.
Location: §6.2, p. 166, (6.2.39).
Printed: \(\Delta(\eta^ig)=\sum_{r=1}^i(n+\ell_1+\ell_2-2r)(\eta^{i-1}g)=i(n+\ell_1+\ell_2-i+1)
\eta^{i-1}g\) for \(g\in V_{\ell_1-i,\ell_2-i}\).
Correct: \(\sum_{r=1}^i(n+\ell_1+\ell_2-2r)=i(n+\ell_1+\ell_2-i-1)\), so
\(\Delta(\eta^ig)=i(n+\ell_1+\ell_2-i-1)\eta^{i-1}g\).
Evidence: \(i=1\): the middle sum is \(n+\ell_1+\ell_2-2\), the right side printed gives
\(n+\ell_1+\ell_2\). Direct check \(n=2\), \(\ell_1=\ell_2=1\), \(g=1\):
\(\Delta(x_1y_1+x_2y_2)=2=n+\ell_1+\ell_2-2\). The conclusion (6.2.40) is unaffected, since the
corrected factor is still positive for \(i\le\min(\ell_1,\ell_2)\) and \(n\ge2\).
Target: [X17.06.2.06].

### X17-E06.2.03. Denominator in the harmonic basis

Status: Confirmed.
Location: §6.2, p. 167, Theorem 6.2.4, (6.2.42).
Printed: denominator \(\prod_{r=1}^i(\alpha_1+i)(\beta_1+i)\).
Correct: \(\prod_{r=1}^i(\alpha_1+r)(\beta_1+r)\), the coefficient produced by
\((\int_{(x_1)}\int_{(y_1)})^i(x_1^{\alpha_1}y_1^{\beta_1})\) in Lemma 6.1.1 (the correct form
appears in the analogous basis (6.4.70)).
Evidence: \(n=2\), \(\alpha=\beta=(0,2)\): the corrected element is
\(x_2^2y_2^2-4x_1y_1x_2y_2+x_1^2y_1^2\), which is harmonic (\(\Delta\) gives
\(4x_2y_2-4(x_2y_2+x_1y_1)+4x_1y_1=0\)); the printed denominator at \(i=2\) is \((2\cdot2)^2=16\)
instead of \(1\cdot2\cdot1\cdot2=4\), giving \(x_2^2y_2^2-4x_1y_1x_2y_2+\frac14x_1^2y_1^2\),
with \(\Delta=-3x_1y_1\ne0\).
Target: [X17.06.2.07].

### X17-E06.3.01. Commutation of \(\widetilde D\) with \(E_{i,j}\)

Status: Confirmed.
Location: §6.3, p. 170, (6.3.7).
Printed: \(\widetilde DE_{i,j}=E_{j,i}\widetilde D\) on \(\mathcal A\) for \(i,j\in\overline{1,n}\).
Correct: \(\widetilde DE_{i,j}=E_{i,j}\widetilde D\); this is what is needed for
\(\mathcal A_{\langle k\rangle}\) to be a submodule.
Evidence: \(n=2\), \(n_1=1\), \(f=x_2\) (\(\widetilde Df=f\)): \(E_{1,2}=\partial_{x_1}
\partial_{x_2}\) gives \(\widetilde DE_{1,2}x_2=0\), while \(E_{2,1}=-x_1x_2\) gives
\(E_{2,1}\widetilde Dx_2=-x_1x_2^2\ne0\). Each \(E_{i,j}\) of (6.3.2) changes the signed degree
by \(0\), so it commutes with \(\widetilde D\).
Target: [X17.06.3.02].

### X17-E06.5.01. Irreducibility range for \(n_1+1=n_2=n\)

Status: Confirmed.
Location: §6.5, p. 192, Theorem 6.5.1 (second paragraph, case \(n_2=n\)).
Printed: "For \(m_1,m_2\in\mathbb N\) with \(m_1<m_2\), \(\mathcal H_{\langle m_1,m_2\rangle}\)
and \(\mathcal H_{\langle-m_2-m_1-1,m_1+1\rangle}\) are also infinite-dimensional irreducible
highest-weight \(\mathfrak{sl}(n,\mathbb F)\)-modules. All submodules
\(\mathcal H_{\langle-m_1,m_1+m_2+1\rangle}\) with \(m_1,m_2\in\mathbb N\) have exactly two
singular vectors."
Correct: the first family requires \(m_1\in\mathbb N+1\): \(\mathcal H_{\langle0,m\rangle}\)
(\(m\ge1\)) has the two singular vectors \(y_n^m\) and \(\eta^m(x_{n-1}^m)\) (the second from
the family \(\eta^{m_1+1}(x_{n-1}^{m_1+m_2+1}y_n^{m_2})\) of (6.5.62) with \(m_2=0\)), as the
last printed sentence with \(m_1=0\) also says; so it is not irreducible.
Evidence: \(n=3\), \(n_1=2\), \(\mathcal H_{\langle0,1\rangle}\) contains the singular vectors
\(y_3\) (weight \(0\)) and \(\eta(x_2)=y_2+x_2x_3y_3\) (weight \(\lambda_1-2\lambda_2\)); both
are harmonic and killed by \(E_{1,2},E_{2,3}\) (direct computation). The printed sentence
with \(m_1=0\), \(m_2=1\) asserts irreducibility of \(\mathcal H_{\langle0,1\rangle}\), and the
last printed sentence with \(m_1=0\), \(m_2=0\) asserts two singular vectors in the same space.
Target: [X17.06.5.03].

### X17-E06.5.02. Highest-weight data for \(n_1+1=n_2=n\)

Status: Confirmed.
Location: §6.5, p. 192, paragraph after Theorem 6.5.1 (case \(n_2=n\)).
Printed: "\(\mathcal H_{\langle m,0\rangle}\) has a highest-weight vector \(x_{n-1}^m\) of weight
\(m\lambda_{n-2}-(m+1)\lambda_{n-1}\) for \(m\in\mathbb Z\)"; "\(\mathcal H_{\langle m_1,m_2
\rangle}\) has a highest-weight vector \(\eta^{m_1+m_2}(x_{n-1}^{m_2}y_n^{-m_1})\) of weight
\(m_2\lambda_{n-2}+(m_1-m_2-1)\lambda_{n-1}\)".
Correct: \(x_{n-1}^m\in\mathcal H_{\langle-m,0\rangle}\), \(m\in\mathbb N\) (it has signed degree
\(-m\)); the weight of \(\eta^{m_1+m_2}(x_{n-1}^{m_2}y_n^{-m_1})\) is
\(m_2\lambda_{n-2}-(m_1+m_2+1)\lambda_{n-1}\).
Evidence: \(\widetilde D(x_{n-1}^m)=-mx_{n-1}^m\) since \(x_{n-1}\) is swapped. For the second
vector, \(\eta\) commutes with \(H\); on \(x_{n-1}^{m_2}y_n^{-m_1}\),
\(E_{n-2,n-2}=-1\), \(E_{n-1,n-1}=-m_2-1\), \(E_{n,n}=m_1\), so \(h_{n-2}=m_2\),
\(h_{n-1}=-m_1-m_2-1\). Example \(n=3\), \(m_1=1\), \(m_2=2\): computed weight
\((h_1,h_2)=(2,-4)\); printed \((2,-2)\).
Target: [X17.06.5.04].

### X17-E06.6.01. Norm of \(x_{n_1}^{m_1}\zeta_1^{m_2}\)

Status: Confirmed.
Location: §6.6, pp. 195–196, (6.6.27)–(6.6.28).
Printed: \(\sum_{i=0}^{m_1}(-1)^{m_1-i}i!(m_2+i)!>0\) for \(m_1,m_2\in\mathbb N\), and
\((x_{n_1}^{m_1}\zeta_1^{m_2}|x_{n_1}^{m_1}\zeta_1^{m_2})=(-1)^{m_1}m_2!\sum_{i=0}^{m_2}
(-1)^{m_2-i}(m_1+i)!(m_2-i)!\ne0\).
Correct: \((x_{n_1}^{m_1}\zeta_1^{m_2}|x_{n_1}^{m_1}\zeta_1^{m_2})=(-1)^{m_1+m_2}(m_2!)^2
\sum_{i=0}^{m_2}(m_1+i)!/i!\), which is nonzero; the conclusion \(\ne0\) holds.
Evidence: in the expansion \(\zeta_1^{m_2}=\sum_i\binom{m_2}i(-1)^ix_{n_1-1}^{m_2-i}x_{n_1}^i
y_{n_1-1}^iy_{n_1}^{m_2-i}\) every monomial has total \(x\)-degree \(m_1+m_2\) in swapped
variables, so all terms have the sign \((-1)^{m_1+m_2}\); there is no alternation. Values
\((m_1,m_2)=(0,1)\): actual norm \(-2\), printed formula \(0\); \((1,1)\): actual \(3\),
printed \(-1\). The inequality (6.6.27) fails at \((m_1,m_2)=(1,0)\) (sum \(-1+1=0\)).
Target: [X17.06.6.03].

### X17-E06.6.02. Missing condition for \(n_1=n_2=n\)

Status: Confirmed.
Location: §6.6, p. 197, Theorem 6.6.3.
Printed: "Let \(\ell_1,\ell_2\in\mathbb Z\) such that \(\ell_2\ge0\) when \(n_1=n\) … Then
\(\mathcal H_{\langle\ell_1,\ell_2\rangle}\) is an irreducible highest-weight module …"
Correct: for \(n_1=n\) the hypothesis must be \(\ell_2\ge0\) and \(\ell_1+\ell_2\le0\).
Evidence: for \(n_1=n_2=n\), \(\widetilde D=-\sum_ix_i\partial_{x_i}\le0\) on monomials, so
\(\mathcal B_{\langle\ell_1,\ell_2\rangle}=0\) for \(\ell_1>0\); e.g. \(\mathcal H_{\langle1,0
\rangle}=0\) although \(\ell_2=0\ge0\), and the zero module is not irreducible. More generally
the highest-weight vectors \(x_n^{m_1}\zeta_1^{m_2}\) lie in \(\mathcal H_{\langle-m_1-m_2,m_2
\rangle}\), and (6.6.40) gives \(\mathcal H_{\langle\ell_1,\ell_2\rangle}=0\) for
\(\ell_1+\ell_2>0\).
Target: [X17.06.6.04].

### X17-E06.6.03. Signs in the highest weights for \(n_1=n_2\)

Status: Confirmed.
Location: §6.6, p. 197, paragraph after Theorem 6.6.3.
Printed: \(x_{n_1}^{m_1}\zeta_1^{m_2+1}\) has weight \((m_2+1)\lambda_{n_1-2}-m_1
\lambda_{n_1-1}-(m_1+m_2+3)\lambda_{n_1}\) (and for \(n_1=n-1\):
\((m_2+1)(1-\delta_{n,3})\lambda_{n-3}-m_1\lambda_{n-2}-(m_1+m_2+3)\lambda_{n-1}\));
\(y_{n_1+1}^{m_2}\zeta_2^{m_1+1}\) has weight \(-(m_1+m_2+3)\lambda_{n_1}+m_2\lambda_{n_1+1}-
(m_1+1)(1-\delta_{n_1,n-2})\lambda_{n_1+2}\).
Correct: the coefficient of \(\lambda_{n_1-1}\) (resp. \(\lambda_{n-2}\)) is \(+m_1\), and the
coefficient of \(\lambda_{n_1+2}\) is \(+(m_1+1)(1-\delta_{n_1,n-2})\).
Evidence: \(\zeta_1\) has weight \(\lambda_{n_1-2}-\lambda_{n_1}\) and \(x_{n_1}\) (swapped)
contributes \(E_{n_1,n_1}=-1\) per factor, so \(h_{n_1-1}\) acts on
\(x_{n_1}^{m_1}\zeta_1^{m_2+1}\) by \(+m_1\). Direct computation \(n=5\), \(n_1=n_2=2\),
\(m_1=1\), \(m_2=2\): \(x_2\zeta_1^3\) has \((h_1,\dots,h_4)=(1,-6,0,0)\) and \(y_3^2\zeta_2^2\)
has \((0,-6,2,2)\); the printed formulas give \((-1,-6,0,0)\) and \((0,-6,2,-2)\).
Target: [X17.06.6.05].

### X17-E06.7.01. Irreducibility hypothesis for \(\mathfrak{gl}(n)\)-modules

Status: Confirmed.
Location: §6.7, p. 206, after (6.7.47).
Printed: "any finite-dimensional \(gl(n,\mathbb F)\)-module is a highest-weight irreducible
module \(V(\mu)\) for some \(\mu\in\Lambda^+\) when \(\mathbb F\) is algebraically closed."
Correct: any finite-dimensional irreducible \(\mathfrak{gl}(n,\mathbb F)\)-module is
\(V(\mu)\) for some \(\mu\in\Lambda^+\).
Evidence: the direct sum of two copies of the trivial module is finite-dimensional and not
irreducible; the two-dimensional module on which \(\sum_rE_{r,r}\) acts by a nonzero nilpotent
Jordan block (and \(\mathfrak{sl}(n)\) by \(0\)) is not even completely reducible.
Target: [X17.06.7.07].

### X17-E06.8.01. Sign in the definition of \(\mathcal A_{\langle k\rangle}\) in §6.8

Status: Confirmed.
Location: §6.8, p. 212, (6.8.8).
Printed: \(\mathcal A_{\langle k\rangle}=\mathrm{Span}\{x^\alpha\mid\sum_{i=1}^{n_1}\alpha_i-
\sum_{r=n_1+1}^n\alpha_r=k\}\).
Correct: \(\sum_{r=n_1+1}^n\alpha_r-\sum_{i=1}^{n_1}\alpha_i=k\), as in (6.3.3).
Evidence: the next display (6.8.9) states \(\mathcal A_{\langle k\rangle}=\{f\mid\widetilde Df=
kf\}\) with \(\widetilde D=\sum_{r>n_1}x_r\partial_{x_r}-\sum_{i\le n_1}x_i\partial_{x_i}\)
(6.8.3), and the proof of Lemma 6.8.2 uses \(x_1f\in\mathcal A_{\langle k-1\rangle}\),
\(x_nf\in\mathcal A_{\langle k+1\rangle}\) for \(f\in\mathcal A_{\langle k\rangle}\) (6.8.11)–
(6.8.12); both hold only with the corrected sign.
Target: [X17.06.8.03].

### Conventions and notation (not errata)

- The heading of §6.6 reads "Noncanonical Representations VI" (the sequence is I, II, III,
  VI); the synopsis keeps the printed heading.
- (6.2.42) uses \(i\) both as the summation index of the outer sum and as the index of
  \(\sum_{i=2}^n\partial_{x_i}\partial_{y_i}\); the synopsis renames the inner index \(r\).
- In §§6.3–6.6 the source writes \(\eta\) (no tilde) for the operator (6.3.41), and
  \(\widetilde\Delta\) has the sign of (6.3.40) (\(+x_i\partial_{y_i}\) on swapped \(x\),
  \(-\partial_{x_r}\partial_{y_r}\) on the unswapped middle block). The synopsis keeps this sign.
- Theorem 6.3.3 states only \(\lambda_0=0\); the source also uses \(\lambda_n=0\)
  (e.g. \(n_1=n-1\) in Theorem 6.3.3, the factors \(1-\delta\) in §§6.4–6.6).
- "Exactly two (three) singular vectors" means two (three) singular vectors up to scalar
  multiples.
- In (6.7.71) the term \(\mu_{i_r}-\mu_s\) is a misprint for \(\mu_{i_r}-\mu_{i_s}\) in a
  derivation step.
- In §6.7 after Theorem 6.7.6, the fundamental weights of \(\mathfrak{sl}(n+1)\) are taken for
  the reordered index set \(n+1,1,2,\dots,n\).
- Lemma 6.8.5: the statement is recorded as printed; its proof is incomplete (an orthogonal
  normalization of an isotropic \(a\), and a restriction to a subspace not preserved by the
  operators used). This is a gap in the proof, not an erratum of the statement; see
  [X17.06.8.07].

## Chapter 7. Representations of Even Orthogonal Lie Algebras

### X17-E07.1.01. Denominator in the \(o(2n)\)-harmonic basis

Status: Confirmed.
Location: §7.1, p. 220, Theorem 7.1.1, (7.1.16).
Printed: denominator \(\prod_{r=1}^i(\alpha_1+i)(\beta_1+i)\).
Correct: \(\prod_{r=1}^i(\alpha_1+r)(\beta_1+r)\).
Evidence: (7.1.16) repeats (6.2.42) (see [X17-E06.2.03]); for \(n=2\), \(\alpha=\beta=(0,2)\)
(\(k=4\)) the printed element \(x_2^2y_2^2-4x_1y_1x_2y_2+\frac14x_1^2y_1^2\) has
\(\Delta=-3x_1y_1\ne0\), while the corrected coefficient \(1\) gives a harmonic polynomial.
Target: [X17.07.1.03].

### X17-E07.3.01. The operator \(C_{i,j}\) in the conformal representation

Status: Confirmed.
Location: §7.3, p. 234, (7.3.24).
Printed: \(C_{i,j}|_{\mathcal A}=x_{n+i}\partial_{x_j}-x_j\partial_{x_{n+i}}\).
Correct: \(C_{i,j}|_{\mathcal A}=x_{n+i}\partial_{x_j}-x_{n+j}\partial_{x_i}\).
Evidence: \(C_{i,i}=0\) in \(o(2n+2)\), but the printed operator for \(i=j\) is
\(x_{n+i}\partial_{x_i}-x_i\partial_{x_{n+i}}\ne0\). The corrected form agrees with the
differential-operator part of \(\nu(C_{i,j})\) in (7.3.33) and with \(\pi_c(C_{i,j})=y_i
\partial_{x_j}-y_j\partial_{x_i}\) in (7.4.3), and with it all brackets of the representation
check (\(n=2,3\)).
Target: [X17.07.3.05].

### X17-E07.4.01. Reducibility of the conformal representation \(\pi_c\)

Status: Confirmed.
Location: §7.4, p. 242, Theorem 7.4.1, with the proof on pp. 243–245.
Printed: "The representation \(\pi_c\) of \(o(2n+2,\mathbb C)\) on \(\mathcal B\) is irreducible
with highest weight \(-c\lambda_1\) if \(c\notin-\mathbb N\). When \(c=-k\) with
\(k\in\mathbb N\), … \(\mathcal B/\mathcal B_{[k]}\) is an irreducible highest-weight
\(o(2n+2,\mathbb C)\)-module with highest weight \(-(k+2)\lambda_1+(k+1)\lambda_2\)."
Correct: with \(\Delta=\sum_i\partial_{x_i}\partial_{y_i}\), \(\ker\Delta^m\) is a nonzero proper
submodule when \(c=n-m\), \(m\in\mathbb N+1\). Hence \(\pi_c\) is reducible for
\(c\in\{1,\dots,n-1\}\), and for \(c=-k\) the quotient \(\mathcal B/\mathcal B_{[k]}\) is
reducible (it contains \(\ker\Delta^{n+k}/\mathcal B_{[k]}\), which is neither \(0\) nor the
whole quotient). The finite-dimensional statement for \(\mathcal B_{[k]}\) stands. Open: the
conjectured sharp form is that \(\pi_c\) is irreducible iff \(c\notin n-1-\mathbb N\).
Evidence: direct commutation gives \([\Delta^m,\pi_c(A_{i,n+1})]=m(n-m-c)\partial_{y_i}
\Delta^{m-1}-2mx_i\Delta^m\) (checked symbolically for \(m=1,2,3\), \(n=2,3\)), the analogous
identity for \(C_{n+1,i}\), and \(\Delta^m\) commutes with \(\pi_c(o(2n))\), \(\partial_{x_i}\),
\(\partial_{y_i}\), and satisfies \([D,\Delta^m]=-2m\Delta^m\), so all of \(\pi_c\) preserves
\(\ker\Delta^m\) at \(c=n-m\). For \(n=2\),
\(c=1\) the submodule generated by \(1\) has dimensions \(4,9,16,25\) in degrees \(1,2,3,4\)
(the harmonic polynomials) against \(\dim\mathcal B_d=4,10,20,35\); for \(n=3\), \(c=2\) the
dimensions are \(6,20,50,105\) against \(6,21,56,126\), and for \(n=3\), \(c=1\) the module
generated by \(1\) misses one dimension in degree \(4\) (\(125<126\)). The proof fails at (7.4.21):
\(\Delta^r(x_1^{\ell-r-1}x_2y_1^r)\) needs \(\ell-2r-1\ge0\), so for even \(\ell\) the summand
\(\eta^{\ell/2}\mathsf H_0=\mathbb C\eta^{\ell/2}\) of \(\mathcal B_\ell\) is never reached.
Target: [X17.07.4.02].

### Conventions and notation (not errata)

- \(o(2n,\mathbb F)\) and \(o(2n+2,\mathbb C)\) are the split models (7.1.1), (7.3.20); the source
  writes \(E_{i,n+j}|_{\mathcal B}\), \(E_{n+i,j}|_{\mathcal B}\) in (7.2.4)–(7.2.5) and
  (7.4.41)–(7.4.42) for the images of the antisymmetrized elements.
- In (7.1.16) the summation index \(i\) is reused inside \(\sum_{i=2}^n\); the synopsis renames
  it.
- In the proof of Theorem 7.4.2, (7.4.33)–(7.4.34) drop a factor: substituting (7.4.30)–(7.4.31)
  gives \(\frac2{a_1}(\sum_ia_ib_i)y_1ge^{\cdots}\equiv0\); the conclusion is unaffected.

## Chapter 8. Representations of Odd Orthogonal Lie Algebras

### X17-E08.2.01. Sign of \(\widetilde\Delta\) in \(\widetilde\Delta'\) and in \(T_\iota\)

Status: Normalization check.
Location: §8.2, p. 260, (8.2.14)–(8.2.16); used in (8.2.36)–(8.2.97).
Printed: "We take \(\widetilde\Delta\) in (7.2.6) and \(\eta\) in (7.2.7). Then
\(\widetilde\Delta'=\partial_{x_0}^2+2\widetilde\Delta\), \(\eta'=x_0^2+2\eta\)", and
\(T_\iota=\sum_i\frac{(-2)^ix_0^{2i+\iota}}{(2i+\iota)!}\widetilde\Delta^i\) from Lemma 6.1.1 with
\(T_2=2\widetilde\Delta\).
Correct: with \(\widetilde\Delta\) of (7.2.6), (8.2.8) gives \(\widetilde\Delta'=
\partial_{x_0}^2-2\widetilde\Delta\), so \(T_2=-2\widetilde\Delta\) and
\(T_\iota=\sum_i\frac{2^ix_0^{2i+\iota}}{(2i+\iota)!}\widetilde\Delta^i\). Equivalently, the
printed (8.2.14)–(8.2.15) hold if \(\widetilde\Delta\) is replaced by its negative, and the source
does this silently from (8.2.36) on (for \(n_1=n_2\) it writes \(\widetilde\Delta=-\sum_{i\le
n_1}x_i\partial_{y_i}-\sum_{s>n_1}y_s\partial_{x_s}\), the negative of (6.6.1)). The synopsis
keeps \(\widetilde\Delta\) of (6.3.40) and the corrected \(T_\iota\).
Evidence: (8.2.8) prints \(\widetilde\Delta'=\partial_{x_0}^2-2\sum_{i\le n_1}x_i\partial_{y_i}+
2\sum\partial_{x_r}\partial_{y_r}-2\sum_{s>n_2}y_s\partial_{x_s}=\partial_{x_0}^2-2\widetilde
\Delta\). Only this operator is invariant: for \(n=n_1=n_2=1\),
\([\partial_{x_0}^2+2x_1\partial_{y_1},\pi(E_{0,1}-E_{2,0})]\ne0\) with
\(\pi(E_{0,1}-E_{2,0})=-x_0x_1-y_1\partial_{x_0}\), while \(\partial_{x_0}^2-2x_1\partial_{y_1}\)
commutes with it.
Target: [X17.08.2.02].

### X17-E08.2.02. Range of the signed degree in the decomposition of \(\mathcal B'\)

Status: Confirmed.
Location: §8.2, p. 267, Theorem 8.2.3.
Printed: "\(\mathcal B'=\bigoplus_{i,k=0}^\infty\eta'^i(\mathsf H'_{\langle k\rangle})\) is a
decomposition of irreducible submodules."
Correct: \(\mathcal B'=\bigoplus_{i\in\mathbb N,\ k\in\mathbb Z}\eta'^i(\mathsf
H'_{\langle k\rangle})\), as the proof concludes (\(\mathcal B'=\bigoplus_{k\in\mathbb Z}
\mathcal B'_{\langle k\rangle}\)).
Evidence: for \(n_1\ge1\), \(x_1\in\mathcal B'_{\langle-1\rangle}\) (\(x_1\) is swapped), while
\(\eta'^i\) raises the signed degree by \(2i\ge0\); so \(x_1\) is not in the printed sum over
\(k\ge0\).
Target: [X17.08.2.04].

### X17-E08.2.03. Factor in \(\widetilde\Delta'^r(\eta'^rv)\)

Status: Confirmed.
Location: §8.2, p. 272, (8.2.97)–(8.2.100).
Printed: \((\widetilde\Delta')^r[\eta'^r(v)]=2^rr!\prod_{i=1}^r[1+2(n_1-n_2-k+r+i)]v\).
Correct: \(2^rr!\prod_{i=1}^r[1-2(n_1-n_2-k+r+i)]v\) (with \(\widetilde\Delta'\) of (8.2.8)).
Evidence: \(n=n_1=n_2=1\), \(v=x_1\in\mathsf H'_{\langle-1\rangle}\), \(k=1\), \(r=1\): with
\(\widetilde\Delta'=\partial_{x_0}^2-2x_1\partial_{y_1}\) and \(\eta'=x_0^2+2y_1\partial_{x_1}\),
\(\eta'(x_1)=x_0^2x_1+2y_1\) and \(\widetilde\Delta'(x_0^2x_1+2y_1)=2x_1-4x_1=-2x_1\); the
printed factor gives \(2\cdot[1+2\cdot1]x_1=6x_1\). With the other sign convention of
[X17-E08.2.01] (\(\partial_{x_0}^2+2x_1\partial_{y_1}\) and \(x_0^2-2y_1\partial_{x_1}\)) the
value is again \(-2x_1\). The factors are odd integers, hence nonzero, so the conclusion
(8.2.98)–(8.2.100) is unaffected.
Target: [X17.08.2.04].

### X17-E08.3.01. Upper limit in \(\rho\) for \(B_n\)

Status: Confirmed.
Location: §8.3, p. 273, (8.3.8).
Printed: \(\rho=\sum_{i=1}^{n-1}(n-i+1/2)\varepsilon_i\).
Correct: \(\rho=\sum_{i=1}^n(n-i+\frac12)\varepsilon_i\) (so \(\rho_n=\frac12\)).
Evidence: (8.3.7) requires \(2(\rho,\nu)/(\nu,\nu)=1\) for the simple root \(\nu=\varepsilon_n\),
i.e. \(2\rho_n=1\); the printed \(\rho\) gives \(0\). (8.3.10) at \(i=n\) and
\((\varepsilon_1+2\rho,\varepsilon_1)=2n\) in (8.3.9) need the corrected \(\rho\) (for \(n=1\) the
printed \(\rho\) is \(0\) and \((\varepsilon_1+2\rho,\varepsilon_1)=1\ne2\)).
Target: [X17.08.3.02].

### X17-E08.3.02. Roots of the characteristic polynomial for \(o(2n+1)\)

Status: Confirmed.
Location: §8.3, p. 274, Lemma 8.3.2, (8.3.13); p. 280, (8.3.69); p. 281, (8.3.70)–(8.3.71).
Printed: factor \((t+\mu_{i_\iota}+2n-i_{\iota+1})^{\iota^-_{i_{\iota+1}-1}(\mu)}\) and the second
product \(\prod_{r=1}^{s-1}(t-\mu_{i_r}+i_r-1)^{\iota^+_{i_r}(\mu)}\); in (8.3.69) the eigenvalue
\(c-\mu_{i_r}-2n+i_{r+1}\); in (8.3.70) "\(\mu_{\iota+1}-\mu_\iota\in\mathbb N\)".
Correct: \((t+\mu_{i_\iota}+2n+1-i_{\iota+1})\); product over \(r=1,\dots,s\); eigenvalue
\(c-\mu_{i_r}-2n-1+i_{r+1}\); \(\mu_\iota-\mu_{\iota+1}\in\mathbb N\).
Evidence: by (8.3.11) with \(i=i_{\iota+1}-1\) and \(\mu_{i_{\iota+1}-1}=\mu_{i_\iota}\), the root
on \(V(\mu-\varepsilon_{i_{\iota+1}-1})\) is \(i_{\iota+1}-1-2n-\mu_{i_\iota}\). By Lemma 8.3.1 all
\(s\) summands \(V(\mu+\varepsilon_{i_r})\) occur. For \(n=1\), \(\mu=\mu_1\varepsilon_1\)
(\(\mu_1\ge1\)): \(\widetilde\omega\) acts on \(V(\mu-\varepsilon_1)\subset V(\varepsilon_1)
\otimes V(\mu)\) by \(\frac12[(\mu_1-1)\mu_1-\mu_1(\mu_1+1)-2]=-\mu_1-1\) (with \((\mu,\mu+2\rho)=
\mu_1(\mu_1+1)\)), while the printed factor gives \(-\mu_1\); and \(V(\mu+\varepsilon_1)\) (root
\(\mu_1\)) is missing from the printed product, which is empty for \(s=1\).
Target: [X17.08.3.03], [X17.08.3.09].

### X17-E08.3.03. The operator \(C_{i,j}\) in the odd conformal representation

Status: Confirmed.
Location: §8.3, p. 275, (8.3.21).
Printed: \(C_{i,j}|_{\mathcal A}=x_{n+i}\partial_{x_j}-x_j\partial_{x_{n+i}}\).
Correct: \(C_{i,j}|_{\mathcal A}=x_{n+i}\partial_{x_j}-x_{n+j}\partial_{x_i}\).
Evidence: as for (7.3.24) ([X17-E07.3.01]): \(C_{i,i}=0\), but the printed operator for
\(i=j\) is nonzero; the corrected form agrees with (8.3.33) and (8.4.5).
Target: [X17.08.3.04].

### X17-E08.3.04. Sign of \(K_{n+1}\)

Status: Confirmed.
Location: §8.3, p. 275, (8.3.25); p. 276, (8.3.38); §8.4, p. 284, (8.4.9); p. 290, (8.4.51).
Printed: \(K_{n+1}|_{\mathcal A}=x_0D-\eta\partial_{x_0}\) (and \(\nu(K_{n+1})\) with the
corresponding sign); \(\pi_c(K_{n+1})=x_0(D'+c)-\eta'\partial_{x_0}\);
\(\pi_c^{n_1,n_2}(K_{n+1})=x_0(\widetilde D'+\tilde c)-\widetilde\eta'\partial_{x_0}\).
Correct: \(K_{n+1}|_{\mathcal A}=\eta\partial_{x_0}-x_0D\), \(\pi_c(K_{n+1})=\eta'\partial_{x_0}-
x_0(D'+c)\), \(\pi_c^{n_1,n_2}(K_{n+1})=\widetilde\eta'\partial_{x_0}-x_0(\widetilde D'+\tilde c)\),
and \(\nu(K_{n+1})\) with the opposite overall sign.
Evidence: in \(o(2n+3)\), \([K_{n+1},K_{2n+2}]=[E_{0,n+1}-E_{2n+2,0},E_{0,2n+2}-E_{n+1,0}]=
E_{n+1,n+1}-E_{2n+2,2n+2}=A_{n+1,n+1}\), which acts by \(-D\) (resp. \(-D'-c\)). With the printed
operators, \([x_0D-\eta\partial_{x_0},-\partial_{x_0}]=D\) (resp. \(D'+c\)), the wrong sign; with
the corrected sign all brackets of the representation hold (checked for \(n=1,2\), and for
\(\pi_c^{n_1,n_2}\) with \(n=1,2\), all \(n_1\le n_2\)). The theorems of §§8.3–8.4 are unaffected:
\(\mathcal G_-\) and the submodules generated are the same, and \(\varphi\) and \(T\) change only
by signs absorbed in the definitions.
Target: [X17.08.3.04], [X17.08.3.05], [X17.08.4.01], [X17.08.4.04].

### X17-E08.3.05. Constant in Lemma 8.3.5

Status: Confirmed.
Location: §8.3, p. 279, Lemma 8.3.5; p. 280, (8.3.74).
Printed: \(T|_{\widetilde M_k}=(2c-2n+k+2)\eta\); (8.3.74) uses \(2c+2-2n+\ell\) for
\(u\in\widetilde{V(\mu)}_{\ell-1}\).
Correct: \(T|_{\widetilde M_k}=(2c-2n+k+1)\eta\); in (8.3.74) the factor is \(2c+1-2n+\ell\).
Evidence: summing the scalar terms of (8.3.64)–(8.3.66) gives \((k+1+c)(x_0^2+2\sum_ix_ix_{n+i})-
(2n+1)\eta-k\eta=(2c+k+1-2n)\eta\), since \(x_0^2+2\sum x_ix_{n+i}=2\eta\). Direct check with
\(M\) trivial: for \(n=1\), \(T\) acts on \(1,x_1,x_0y_1\) and a cubic by \(2c-1,2c,2c+1,
2c+2\) times \(\eta\); for \(n=2\) by \(2c-3,2c-2,2c-1,2c\). The analogous \(o(2n+2)\) Lemma 7.3.5
(\(2c+2-2n+k\)) corresponds to dimension \(2n\); for dimension \(2n+1\) the constant drops by
one. Theorem 8.3.6 is unaffected, since its excluded set \(n-\mathbb N/2\) contains all zeros
\(c=n-\ell/2\), \(\ell\ge1\), of the corrected factor.
Target: [X17.08.3.08].

### X17-E08.3.06. Exceptional set in Theorem 8.3.6

Status: Confirmed.
Location: §8.3, p. 280, (8.3.67), Theorem 8.3.6.
Printed: \(\Theta(\mu)=\mu_1+2n-i_2-\mathbb N\) (for \(\mu\ne\frac12\sum\varepsilon_i\)).
Correct: \(\Theta(\mu)=\mu_1+2n+1-i_2-\mathbb N\).
Evidence: by [X17-E08.3.02] the eigenvalue of \(\varphi\) on the summand
\(V(\mu-\varepsilon_{i_2-1})\) of \(\widetilde{V(\mu)}_1\) is \(c-\mu_1-2n-1+i_2\), which vanishes
at \(c=\mu_1+2n+1-i_2\). Example \(n=1\), \(\mu=\varepsilon_1\) (\(i_2=2\)), \(c=2\): \(c\) is not
in the printed exceptional set \(\{1-\mathbb N/2\}\cup(1-\mathbb N)\), but the span of
\(U(\mathcal G_-)(1\otimes V(\varepsilon_1))\) in degree one has dimension \(8<9=
\dim\widetilde{V(\mu)}_1\), so \(\varphi\) is not injective and \(\widetilde{V(\mu)}\) is
reducible. Likewise \(n=2\), \(\mu=\varepsilon_1\), \(c=4\): rank \(24<25\).
Target: [X17.08.3.09].

### X17-E08.4.01. Reducibility of the odd conformal representation \(\pi_c\)

Status: Confirmed.
Location: §8.4, p. 285, Theorem 8.4.1.
Printed: "The representation \(\pi_c\) of \(o(2n+3,\mathbb C)\) on \(\mathcal B'\) is irreducible
with highest weight \(-c\lambda_1\) if \(c\notin-\mathbb N\)."
Correct: for \(c=n+\frac12-m\), \(m\in\mathbb N+1\), \(\ker\Delta'^m\) is a nonzero proper
submodule; so \(\pi_c\) is reducible for \(c\in n-\frac12-\mathbb N\). Open: whether \(\pi_c\) is
irreducible for all \(c\notin(-\mathbb N)\cup(n-\frac12-\mathbb N)\), and whether the quotient
statement for \(c=-k\) holds.
Evidence: with \(\Delta'=\partial_{x_0}^2+2\sum\partial_{x_i}\partial_{y_i}\) and \(\eta'=
\frac12x_0^2+\sum x_iy_i\), \([\Delta',\pi_c(A_{i,n+1})]=(2n-1-2c)\partial_{y_i}-2x_i\Delta'\) and
similarly for \(C_{n+1,i}\) and for \(K_{n+1}\) (corrected sign), with \(\partial_{x_0}\) and
\(x_0\) (checked symbolically for \(n=2\); this is \([\Delta,K_i]=2z_i\Delta+(2c+2-d)\partial_i\)
for \(d=2n+1\)); for \(m=1\) and \(c=n-\frac12\), harmonic polynomials form an invariant subspace
containing \(1\) but not \(\eta'\). Computation for \(n=1\): \(c=\frac12\) and \(c=-\frac12\) give
proper submodules generated by \(1\) ; \(c=\frac32,
1,2,\frac52\) give none up to degree \(5\).
Target: [X17.08.4.02].

### Conventions and notation (not errata)

- The invariant quadratic form is \(\eta'=x_0^2+2\sum x_iy_i\) in (8.1.11), (8.2.9) and
  \(\eta'=\frac12x_0^2+\sum x_iy_i\) in (8.3.16), (8.4.2); the factor \(2\) is harmless.
- (8.1.27) reads "for \(k\in\overline{0,2k}\)"; read \(\overline{0,2n}\).
- (8.1.39) prints \((E_{r,n+s},E_{s,n+r})|\) and \((E_{n+r,s},E_{n+s,r})|\) for the differences
  \(E_{r,n+s}-E_{s,n+r}\), \(E_{n+r,s}-E_{n+s,r}\), as in (7.1.35).
- (8.3.42) writes \(f_2I_{2n}\) for \(f_2I_{2n+1}\); \(\nu(K_{n+1+i})\) in (8.3.37) has the
  subscript "\(n+i+i\)" for \(n+1+i\).
- Theorem 8.4.1 says "\(\mathcal B'_{[k]}\) is an irreducible \(o(2n+2,\mathbb C)\)-submodule";
  read \(o(2n+3,\mathbb C)\). Theorem 8.4.3 writes \(\mathcal A\) for \(\mathcal B'\).
- Theorem 8.3.6's proof cites "Lemma 8.3.3" for Proposition 8.3.3, and (8.3.70)–(8.3.71) and the
  sentence before (8.3.72) contain the misprints "\(\mu_1+2n-n_1-\mathbb N\)" and
  "\(c=n\)" for \(\mu_1+2n-i_2-\mathbb N\) and \(c\ne n\) (derivation steps).
- Mathlib's `LieAlgebra.Orthogonal.typeB` uses the Gram matrix \(2\oplus\begin{pmatrix}0&I\\I&0
  \end{pmatrix}\); the source's \(o(2n+1)\) uses \(1\oplus\begin{pmatrix}0&I\\I&0\end{pmatrix}\).

## Chapter 9. Representations of Symplectic Lie Algebras

### X17-E09.1.01. Range of the Lefschetz index in the exterior decomposition

Status: Confirmed.
Location: §9.1, p. 296, Theorem 9.1.2, (9.1.22).
Printed: \(\check{\mathcal A}=\bigoplus_{k=0}^n\bigoplus_{\ell=0}^{\lfloor n-k/2\rfloor}
\check\eta^\ell\check{\mathcal H}_k\), "a direct sum of irreducible submodules".
Correct: \(\check{\mathcal A}=\bigoplus_{k=0}^n\bigoplus_{\ell=0}^{n-k}\check\eta^\ell
\check{\mathcal H}_k\); the terms with \(n-k<\ell\le\lfloor n-k/2\rfloor\) are zero, and the zero
module is not irreducible.
Evidence: For \(n=2\), \(k=2\), \(\ell=1\le\lfloor 2-1\rfloor\): \(\check\eta\check{\mathcal H}_2
\subset\Lambda^4\), which is the one-dimensional trivial module; multiplication by the invariant
\(\check\eta\) is a module map from the irreducible 5-dimensional \(\check{\mathcal H}_2\) to it,
hence zero, so \(\check\eta\check{\mathcal H}_2=0\). Dimension count
with the corrected range: \(\sum_k(n-k+1)\bigl(\binom{2n}{k}-\binom{2n}{k-2}\bigr)=3\cdot1+2\cdot4+
1\cdot5=16=2^4\); with the printed range, counting each printed summand as a copy of
\(\check{\mathcal H}_k\), one gets \(3+8+10=21\).
Target: [X17.09.1.05].

### X17-E09.1.02. Highest weight vectors of the Weil modules

Status: Normalization check.
Location: §9.1, p. 297, Theorem 9.1.3 (with the positive roots (9.1.4)).
Printed: "the identity element \(1_{\mathcal A}\) is a highest-weight vector with weight
\((1/2)\sum_{i=1}^n\varepsilon_i\)"; "\(x_1\) … is a highest-weight vector with weight
\(\varepsilon_1+(1/2)\sum\varepsilon_i\)".
Correct: These hold for the positive system \(\{\varepsilon_i-\varepsilon_j\ (i<j),
-\varepsilon_i-\varepsilon_j,-2\varepsilon_r\}\). For the positive roots \(C_n^+\) fixed in
(9.1.4), \(1\) and \(x_n\) are lowest-weight vectors (weights \(\frac12\sum\varepsilon_i\) and
\(\varepsilon_n+\frac12\sum\varepsilon_i\)) and the modules have no highest-weight vector.
Evidence: \(2E_{1,n+1}\) is a positive root vector for \(2\varepsilon_1\in C_n^+\), and by
(9.1.24) it acts by \(x_1^2\), so \(2E_{1,n+1}(1)=x_1^2\ne0\). The weights
\(\frac12\sum\varepsilon_i+\sum_i\alpha_i\varepsilon_i\) of \(x^\alpha\) are unbounded above
for \(C_n^+\). On the other hand \(1\) is killed by \(x_i\partial_{x_j}\) (\(i<j\)) and by all
\(-\partial_{x_i}\partial_{x_j}\), the root vectors of \(\varepsilon_i-\varepsilon_j\) and
\(-\varepsilon_i-\varepsilon_j\).
Target: [X17.09.1.07].

### X17-E09.2.01. Weight of the highest-weight vector \(x_{n_1}^m\)

Status: Confirmed.
Location: §9.2.1, p. 298, Theorem 9.2.1.
Printed: "\(x_{n_1}^m\) is a highest-weight vector of \(\mathcal B_{\langle-m\rangle}\) with weight
\(m\varepsilon_{n_1}-\sum_{i=1}^{n_1}\varepsilon_i\)".
Correct: the weight is \(-m\varepsilon_{n_1}-\sum_{i=1}^{n_1}\varepsilon_i\).
Evidence: By (9.2.10), \(E_{i,i}-E_{n+i,n+i}\) acts as \(-x_i\partial_{x_i}-y_i\partial_{y_i}-1\) for
\(i\le n_1\) and as \(x_i\partial_{x_i}\mp y_i\partial_{y_i}(+1)\) for \(i>n_1\); on \(x_{n_1}^m\)
the eigenvalues are \(-m-1\) at \(i=n_1\), \(-1\) at \(i<n_1\) and \(0\) at \(i>n_1\). Direct
computation for \(n=3\), \(n_2=3\), \(m=2\): weights \((-3,0,0)\), \((-1,-3,0)\), \((-1,-1,-3)\)
for \(n_1=1,2,3\). The other weights of the theorem are correct as printed (e.g.
\(x_{n_1+1}^{3}\) has weight \((-1,3,0)\) for \(n_1=1\)).
Target: [X17.09.2.03].

### X17-E09.3.01. Simple roots for the projective oscillator module

Status: Confirmed.
Location: §9.3, p. 319, (9.3.20); used in Theorem 9.3.1, p. 318, and p. 321.
Printed: highest weights are taken "with respect to the following simple positive roots
\(\{\varepsilon_{n+1}-\varepsilon_n,\varepsilon_n-\varepsilon_{n-1},\dots,\varepsilon_2-
\varepsilon_1,2\varepsilon_1\}\)" (with \(n\) for \(m\)).
Correct: a positive system for which the statements of Theorem 9.3.1 hold has simple roots
\(-\varepsilon_{m+1}-\varepsilon_1,\varepsilon_1-\varepsilon_2,\dots,\varepsilon_{m-1}-
\varepsilon_m,2\varepsilon_m\) (i.e. \(\varepsilon'_1=-\varepsilon_{m+1}\), \(\varepsilon'_{i+1}=
\varepsilon_i\) in standard \(C_{m+1}\) order); then \(\lambda_1=-\varepsilon_{m+1}\),
\(\lambda_2=\varepsilon_1-\varepsilon_{m+1}\).
Evidence: In the printed system \(2\varepsilon_{m+1}\) and \(\varepsilon_{m+1}-\varepsilon_i\)
are positive, but \(\pi_\kappa(B^s_{m+1,m+1})(1)=2\kappa x_0\) and \(\pi_\kappa(A_{m+1,i})(1)=
-\kappa y_i\) are nonzero, so \(1\) is not a highest-weight vector; its weight
\(\kappa\varepsilon_{m+1}\) would be \(+\kappa\lambda_1\) there. In the corrected system \(1\) is
killed by \(\pi(A_{i,m+1})\), \(\pi(C^s_{m+1,i})\), \(\pi(C^s_{m+1,m+1})\) and by
\(\pi(\mathcal K)\), and has weight \(\kappa\varepsilon_{m+1}=-\kappa\lambda_1\); for
\(\kappa=-\ell\) the class of \(x_1^{\ell+1}\) has weight \((\ell+1)\varepsilon_1+\varepsilon_{m+1}
=-(\ell+2)\lambda_1+(\ell+1)\lambda_2\) (using \(\pi(A_{m+1,m+1})x_1^{\ell+1}=(\ell+1-\ell)
x_1^{\ell+1}\)), as stated.
Target: [X17.09.3.02].

### X17-E09.3.02. Highest-weight vector of the quotient module

Status: Confirmed.
Location: §9.3, p. 321, line 3 (end of the proof of Theorem 9.3.1).
Printed: "\(x_n^{\ell+1}\) is a highest-weight vector of weight \(-(\ell+2)\lambda_1+(\ell+1)
\lambda_2\)".
Correct: \(x_1^{\ell+1}\) (modulo \(\mathcal B'_{(\ell)}\)), as in (9.3.26).
Evidence: With \(n=2m+1\) and (9.3.3), \(x_n=y_m\); \(\pi_\kappa(B^s_{m,m})(y_m^{\ell+1})=
2(\ell+1)x_my_m^{\ell}\ne0\) modulo \(\mathcal B'_{(\ell)}\), and \(B^s_{m,m}\) is a positive root
vector in every positive system for which the theorem holds. The class of \(x_1^{\ell+1}\) is
annihilated by all positive root vectors of the system of [X17-E09.3.01].
Target: [X17.09.3.02].

### Conventions and notation (not errata)

- §9.3 uses \(n=2m+1\) from §6.8 and \(m\) for the rank of \(\mathcal K\); several displays mix
  them (e.g. "\(s\in\overline{n_2+1,n}\)" for \(\overline{m_2+1,m}\) on p. 323, "\(sp(2m+m,
  \mathbb F)\)" on p. 321, \(m_1,m_2\in\overline{1,n}\) in Remark 9.3.4). The synopsis uses
  \(m\) throughout.
- In (9.3.59)–(9.3.60) the source writes \(\tilde c\) for \(\tilde\kappa\), and in the proof of
  Theorem 9.3.1 \(c\) for \(\kappa\). In (9.3.72) the operator raising the \(x_0\)-degree is
  \(B^s_{m+1,m+1}\) (printed \(C^s_{m+1,m+1}\)); this is inside a proof.
- \(\lambda_i\) in §9.3 are fundamental weights for the positive system of (9.3.20) as
  corrected in [X17-E09.3.01], not for \(C^+_{m+1}\) of (9.1.4).
- The canonical bosonic (9.1.8)–(9.1.9), fermionic (9.1.14)–(9.1.15), Weil (9.1.23)–(9.1.24),
  noncanonical (9.2.1)–(9.2.5), projective (9.3.5)–(9.3.8) and noncanonical projective
  (9.3.51)–(9.3.61) operators were checked to satisfy the \(sp\) commutation relations for small
  ranks; no misprint was found in them.

## Chapter 10. Representations of \(G_2\) and \(F_4\)

### X17-E10.1.01. Exterior square of the 7-dimensional \(G_2\)-module is reducible

Status: Confirmed.
Location: §10.1, p. 333, Theorem 10.1.3, with (10.1.28)–(10.1.29) on p. 332.
Printed: "The subspace \(\check{\mathcal A}'_2\) is an irreducible \(\mathcal G^{G_2}\)-module of
highest weight \(\lambda_1\)"; (10.1.29): \(C_3(a\theta_0\theta_3+b\theta_{1'}\theta_{2'})=
-\sqrt2a\theta_{1'}\theta_3+b\theta_3\theta_{1'}\); "\(\theta_3\theta_{2'}\) is the only
singular vector in \(\check{\mathcal A}'_2\)".
Correct: \(\Lambda^2\Theta=V(\lambda_1)\oplus V(\lambda_2)\) (dimensions \(14+7\)); (10.1.29)
reads \(C_3(a\theta_0\theta_3+b\theta_{1'}\theta_{2'})=(b-\sqrt2a)\theta_{1'}\theta_3\), and
\(\theta_0\theta_3+\sqrt2\theta_{1'}\theta_{2'}\) is a second singular vector, of weight
\(\lambda_2\).
Evidence: \(\dim\Lambda^2\mathbb F^7=21\ne14=\dim V(\lambda_1)\). By (10.1.22) with \(r=3\),
\(C_3=\theta_3\partial_{\theta_{2'}}-\theta_1\partial_{\theta_{3'}}+\sqrt2(\theta_0
\partial_{\theta_1}-\theta_{1'}\partial_{\theta_0})\), so \(C_3(\theta_0\theta_3)=
-\sqrt2\theta_{1'}\theta_3\) and \(C_3(\theta_{1'}\theta_{2'})=\theta_{1'}\theta_3\). Direct
computation of the joint kernel of the six positive root vectors on \(\Lambda^2\Theta\) gives
a 2-dimensional space spanned by \(\theta_3\theta_{2'}\) (weight \((h_1,h_2)=(1,0)\)) and
\(\frac1{\sqrt2}\theta_0\theta_3+\theta_{1'}\theta_{2'}\) (weight \((0,1)\)). The \(\Lambda^3\)
statement is correct (singular weights \(0,\lambda_2,2\lambda_2\), \(1+7+27=35\)).
Target: [X17.10.1.06].

### X17-E10.2.01. Sign in the conformal operator \(\pi_c(C_2)\)

Status: Confirmed.
Location: §10.2, p. 334, (10.2.8); also (10.2.25) and (10.2.34), p. 335–336.
Printed: \(\pi_c(C_2)=x_2\partial_{y_1}-x_1\partial_{y_2}+\sqrt2(x_0(D'+c)-\eta'\partial_{x_0})\).
Correct: \(\pi_c(C_2)=x_2\partial_{y_1}-x_1\partial_{y_2}-\sqrt2(x_0(D'+c)-\eta'\partial_{x_0})\)
(only the relative sign of the two parts matters for the commutation relations); accordingly
\(\pi_c(C_2)(1)=-\sqrt2c\,x_0\) in (10.2.25) and \(-\sqrt2(1+c)\) in (10.2.34).
Evidence: With the printed operators, \([\pi_c(A_{3,1}),\pi_c(C_2)]=[\partial_{x_1},\pi_c(C_2)]=
-\partial_{y_2}+\sqrt2(x_0\partial_{x_1}-y_1\partial_{x_0})\), which is not in the span of the
fourteen operators (10.2.3)–(10.2.12) (the only operator containing \(\partial_{y_2}\) and
\(x_0\partial_{x_1}\) is \(\pi_c(C_3)=\partial_{y_2}+\sqrt2(x_0\partial_{x_1}-y_1\partial_{x_0})\));
the pairs \((A_{3,2},C_2)\), \((A_{1,3},C_3)\), \((A_{2,3},C_1)\), \((C_1,C_2)\), \((C_2,C_3)\),
\((C_2,C'_2)\), \((C'_1,C'_3)\) also fail to close. With the corrected sign all 91 brackets lie
in the span, for symbolic \(c\). The corrected sign is also what (10.1.6) gives under the
substitution that produces (10.2.5): there \(x_j\partial_{x_3}\mapsto-x_j(D'+c)\) and
\(x_{3'}\partial_{x_{j'}}\mapsto-\eta'\partial_{y_j}\), so \(\sqrt2(x_0\partial_{x_3}-x_{3'}
\partial_{x_0})\mapsto-\sqrt2(x_0(D'+c)-\eta'\partial_{x_0})\).
Target: [X17.10.2.01].

### X17-E10.2.02. Harmonic exception in the conformal \(G_2\) irreducibility criterion

Status: Confirmed.
Location: §10.2, p. 334, Theorem 10.2.1.
Printed: "The representation \(\pi_c\) of \(\mathcal G^{G_2}\) on \(\mathcal B'\) is irreducible
if and only if \(c\notin-\mathbb N\)."
Correct: \(\pi_c\) is reducible for \(c\in-\mathbb N\) and also for \(c=\frac32\); the "if"
direction fails. Open question: the complete set of reducibility parameters (the source's
argument establishes irreducibility only away from additional exceptional values, which it does
not identify).
Evidence: Let \(\Delta'=\partial_{x_0}^2+2\partial_{x_1}\partial_{y_1}+2\partial_{x_2}
\partial_{y_2}\). The operators \(\pi_c(\xi)\) are the restriction of the conformal action of
\(o(7)\) in 5 variables; for a special conformal operator \(K_i=z_i(D'+c)-\eta'\partial_i\)
(orthonormal coordinates \(z\)), \([\Delta',K_i]=2z_i\Delta'+(2c+2-5)\partial_i\), and
translations, rotations and \(D'+c\) preserve \(\ker\Delta'\); so at \(c=\frac32\) every
\(\pi_c(\xi)\) maps \(\ker\Delta'\) into itself. Direct check with the operators of [X17.10.2.01] (printed or corrected sign of
\(C_2\)): for the harmonic test polynomials \(x_1x_2,x_0x_1,x_0^2-x_1y_1,x_1^3,x_0x_1x_2,
x_0^3-3x_0x_2y_2,x_0y_1,x_0y_1y_2\), \(\Delta'\pi_{3/2}(\xi)f=0\) for all fourteen \(\xi\), while
at \(c=1\), e.g. \(\Delta'\pi_1(A_{1,3})(x_1x_2)\ne0\). The harmonic subspace contains \(1\) but not
\(\eta'\) (\(\Delta'\eta'=5\)), so it is a proper nonzero submodule.
Target: [X17.10.2.02].

### X17-E10.4.01. Index range of the \(\tau\)-images of \(\zeta_r\)

Status: Confirmed.
Location: §10.4, p. 344, (10.4.28).
Printed: \(\zeta_r=\tau(\zeta_{\bar r})\) for \(r\in\overline{15,27}\).
Correct: \(r\in\overline{15,26}\).
Evidence: \(\bar r=27-r\), so \(r=27\) would require \(\zeta_0\), which is not defined; the copy
of \(V\) has the 26 basis vectors \(\zeta_1,\dots,\zeta_{26}\).
Target: [X17.10.4.02].

### Conventions and notation (not errata)

- \(G_2\): the source's \(\lambda_1\) (adjoint) and \(\lambda_2\) (7-dimensional) are Bourbaki's
  \(\omega_2\) and \(\omega_1\). In (10.1.28)–(10.1.36), (10.2.13)–(10.2.15) the primes on
  \(C'_r\) and on indices are essential; the text layer drops them.
- The highest weight \(-c\lambda_2\) of the conformal module (p. 337) refers to the positive
  root vectors (10.1.8); the vector \(1\) is annihilated by \(\pi_c(C_1),\pi_c(C'_2),\pi_c(C_3),
  \pi_c(A_{1,2}),\pi_c(A_{3,1}),\pi_c(A_{3,2})\) and has \((h_1,h_2)\)-eigenvalues \((0,-c)\).
- The \(F_4\) raising and lowering operators satisfy \([F_{\alpha_i},F'_{\alpha_i}]=-h_i\) (not
  \(+h_i\)); this is the sign convention of the construction (4.4.68)–(4.4.80), not an error.
- In (10.4.70) \(L(m_1,1,m_2,0,0,0)\) has one argument too many; it is \(L(m_1,1,m_2,0,0)\).
- Theorem 10.3.1 and Corollaries 10.3.2–10.3.4 carry §10.3 numbers but appear in §10.4.


## Chapter 11. Representations of \(E_6\)

### X17-E11.2.01. Sign in the cubic identity for Dickson's invariant

Status: Confirmed.
Location: §11.2, p. 358, (11.2.41).
Printed: \(\sum_{14\ne i\in\overline{1,26}}x_i\zeta_{28-i}-x_{14}\zeta_{14}-x_{27}\zeta_1=-3\eta\),
with \(\eta\) given by (11.2.42).
Correct: the left-hand side equals \(+3\eta\) for \(\eta\) as printed in (11.2.42).
Evidence: Expanding both sides with \(\zeta_r\) from (11.2.1), (11.2.3)–(11.2.28) gives
\(3\eta\) exactly. Single-term check: the only monomial of \(\eta\) containing \(x_1x_{14}\) is
\(-x_1x_{14}x_{27}\) (from \(-x_{14}(x_1x_{27}-\cdots)\)), coefficient \(-1\). On the left,
\(x_1x_{14}x_{27}\) occurs in \(x_1\zeta_{27}\), \(-x_{14}\zeta_{14}\) and \(-x_{27}\zeta_1\), with
coefficients \(-1,-1,-1\), total \(-3\); this equals \(+3\cdot(-1)\). The sign of (11.2.42) is
fixed independently by (12.6.42), which holds as printed with this \(\eta\). The error
propagates to Lemmas 12.6.4–12.6.5 (see [X17-E12.6.01]).
Target: [X17.11.2.02].

### X17-E11.2.02. Highest weight of \(L(m_1,m_2,m_3)\)

Status: Confirmed.
Location: §11.2, p. 361, sentence before (11.2.80).
Printed: \(L(m_1,m_2,m_3)\) "is a finite-dimensional irreducible submodule of highest weight
\(m_1\lambda_1+m_2\lambda_6\)".
Correct: highest weight \(m_1\lambda_6+m_2\lambda_1\).
Evidence: By Table 11.1, \(x_1\) has weight \((0,0,0,0,0,1)=\lambda_6\), and \(\zeta_1\) has
weight \(\lambda_1\) (stated on p. 355 and in Table 11.2, row 1); \(\eta\) is invariant. The
source itself uses \(m_1\lambda_6+m_2\lambda_1\) in (11.2.81) and on p. 362. The dimension
identities (11.2.82), (11.2.108) are unaffected because the diagram automorphism exchanges
\(\lambda_1\) and \(\lambda_6\).
Target: [X17.11.2.04].

### X17-E11.2.03. The commutator \([\mathcal D_2,\eta]\) and formula (11.2.104)

Status: Confirmed.
Location: §11.2, pp. 363–364, Lemma 11.2.5, (11.2.98)–(11.2.104).
Printed: \([\mathcal D_2,\eta]=\eta(3+\mathcal D_1)\) (the constants are found as \(c_1=3\),
\(c_2=1\)), and
\(\mathcal D(\eta^mx_1^{m_1}\zeta_1^{m_2})=[m(45+5m_1+m_2(m_1+m_2+4))+\sum_{s=1}^{m-1}
s(3+3(s+1)/2+m_1+2m_2)]\eta^{m-1}x_1^{m_1}\zeta_1^{m_2}\).
Correct: \([\mathcal D_2,\eta]=\eta(15+2\mathcal D_1)\), and
\(\mathcal D(\eta^mx_1^{m_1}\zeta_1^{m_2})=[m(45+5(m_1+2m_2)+m_2(m_1+m_2+4))+(15+m_1+2m_2)
m(m-1)+m(m-1)(m-2)]\eta^{m-1}x_1^{m_1}\zeta_1^{m_2}\).
Evidence: Direct computation with \(\mathcal D_2=\sum_i\zeta_i\Im(\zeta_i)\): \(\mathcal D_2(\eta f)
-\eta\mathcal D_2(f)=(15+2k)\eta f\) for \(f\) of degree \(k=0,1,2,3\) (values \(15,17,19,21\)),
e.g. \(\mathcal D_2(\eta)=15\eta\), \(\mathcal D_2(\eta x_1)=17\eta x_1\). The corrected formula
follows from Lemmas 11.2.3–11.2.4 by induction on \(m\), using \(\mathcal D_1=\) degree
\(=m_1+2m_2+3j\) on \(\eta^jx_1^{m_1}\zeta_1^{m_2}\). Direct checks: \(\mathcal D(\eta^2)=120\eta\)
(printed formula: \(96\eta\)); \(\mathcal D(\eta\zeta_1)=60\zeta_1\) (printed: \(50\zeta_1\)); both
agree with the corrected formula. The printed term \(5m_1\) also omits the contribution
\(10m_2\) of \(\zeta_1^{m_2}\) to \(5\mathcal D_1\). The corrected coefficient is positive, so
Lemma 11.2.6 and Theorem 11.2.7 are unaffected.
Target: [X17.11.2.08].

### X17-E11.2.04. Singular vectors need a homogeneity qualification

Status: Confirmed.
Location: §11.2, p. 364, Theorem 11.2.7, first sentence.
Printed: "The set \(\{x_1^{m_1}\zeta_1^{m_2}\eta^{m_3}\mid m_1,m_2,m_3\in\mathbb N\}\) is the set
of all singular vectors in \(\mathcal A\) up to a scalar multiple."
Correct: every homogeneous singular weight vector is a scalar multiple of such a monomial;
in general the singular vectors (together with \(0\)) form the algebra
\(\mathbb F[x_1,\zeta_1,\eta]\), and a singular weight vector is a linear combination of
monomials of that weight.
Evidence: \(1+\eta\) has weight \(0\) and is annihilated by every positive root vector (both
\(1\) and \(\eta\) are invariant), but is not a multiple of a monomial. Lemma 11.2.1, on which
the theorem rests, is stated for homogeneous vectors.
Target: [X17.11.2.10].

### X17-E11.6.01. Second exclusion sets in Corollary 11.6.7(c),(d)

Status: Open check.
Location: §11.6, p. 395, Corollary 11.6.7(c),(d).
Printed: (c) \(\widehat{V(k\lambda_4)}\) is irreducible if \(c\notin\{\mathbb N-10-k/2,\
2\mathbb N+k-12\}\); (d) \(\widehat{V(k\lambda_5)}\) is irreducible if
\(c\notin\{\mathbb N-10-k/2,\ 2\mathbb N-k-20\}\).
Correct: not determined. Theorem 11.6.4 gives second exclusion set \(2\ell_\omega(\lambda)+2\mathbb N\);
direct computation of (11.6.28) gives \(\ell_\omega(k\lambda_4)=-6-\frac{3k}4\) and
\(\ell_\omega(k\lambda_5)=-10-\frac{5k}4\), i.e. sets \(2\mathbb N-12-\frac{3k}2\) and
\(2\mathbb N-20-\frac{5k}2\), not the printed ones.
Evidence: With the \(D_5\) form \((\varepsilon_i,\varepsilon_j)=\delta_{ij}\),
\(2\rho=(8,6,4,2,0)\) and \(\Pi(\mathcal B_1)=\{\frac12\sum\pm\varepsilon_i\text{ with an odd number of
minus signs}\}\) (11.6.22), the minimum over \(H(k\lambda_4)\) of the bracket in (11.6.28) is
attained at \(\lambda'=(k-1)\lambda_4+\lambda_1\) and equals \(-6-\frac{3k}4\) (with
\((\lambda_4+2\rho,\lambda_4)=\frac{45}4\)); for \(k\lambda_5\) the minimum is attained at
\(\lambda'=(k-1)\lambda_5\) and equals \(-10-\frac{5k}4\) (checked for \(k=1,\dots,4\)). The same computation
reproduces the source's values for \(k\lambda_1\) (\(-4-\frac k2\)), \(\lambda_2\) (\(-8\)) and
\(\lambda_3\) (\(-\frac{21}2\)). The printed sets would require
\(\ell_\omega=\frac k2-6\) and \(-\frac k2-10\). The first exclusion sets (from \(\ell(\lambda)\))
were not recomputed; the source gives no derivation for (c)–(d), so whether the printed
statements were obtained by a different (valid) argument is unresolved.
Target: [X17.11.6.06].

### Conventions and notation (not errata)

- In §11.7, \(c=2\mathfrak c\) relates the functor parameter \(c\) to the parameter
  \(\mathfrak c\) of \(\pi_{\mathfrak c}\); the text layer renders both as "c".
- In (11.6.11), \(U(o(2n,\mathbb F))\) means \(U(o(10,\mathbb F))\) (\(n=5\)); in the proof of
  Lemma 11.6.2, \(\mathcal A_1\) means \(\mathcal B_1\).
- In Theorem 11.2.7 the index set is written "\(n_1,m_2,m_3\in\mathbb N\)" for
  \(m_1,m_2,m_3\); in (11.2.80) the summation index "\(m_2\)" is repeated for \(m_3\).
- The relations (11.2.104)–(11.2.105) assert \(\ne0\); the text layer renders "\(\ne\)" as "=".
- \(\overline{E_\alpha}=E_{-\alpha}\) and \(b_i=E_{-\beta_i}\) are fixed by (11.1.4)–(11.1.17) and
  (11.3.14); positive-root and lowering conventions follow those definitions.

## Chapter 12. Representations of \(E_7\)

### X17-E12.6.01. Right-hand side of Lemmas 12.6.4 and 12.6.5

Status: Confirmed.
Location: §12.6, p. 452, Lemma 12.6.4, (12.6.41), (12.6.43); Lemma 12.6.5, (12.6.45), (12.6.48).
Printed: \(\sum_{14\ne i\in\overline{1,26}}P_i\zeta_{28-i}-P_{14}\zeta_{14}-P_{27}\zeta_1=
\eta(24-5D)\); and on \(\widehat M\) the corresponding \(\iota(b_i)\)-expression equals
\(\eta(24-5D+3c)\).
Correct: with \(\eta\) as in (11.2.42), \(\sum_{14\ne i\in\overline{1,26}}P_i\zeta_{28-i}-
P_{14}\zeta_{14}-P_{27}\zeta_1=\eta(D-24)\). Consequently the \(c\)-term of Lemma 12.6.5 is
\(-3c\eta\), and the lemma reads \(\eta(D-24-3c)\) (granted the source's argument that the
\(\mathcal G^{E_6}\)-valued terms vanish).
Evidence: Direct computation from (12.4.20), (12.4.39)–(12.4.64) and (11.2.1)–(11.2.28): the
first-order part of the operator is \(\eta D\) and the zero-order part is
\(\sum\pm P_i(\zeta_{28-i})=-24\eta\); applied to \(f=1,x_1,x_5x_{27},\zeta_1\) the operator gives
\(-24\eta,\ -23\eta x_1,\ -22\eta x_5x_{27},\ -22\eta\zeta_1\). In the source's own proof the
coefficient of \(\partial_{x_i}\) besides the \(D\)-term is \(-2\eta x_i\) (12.6.42)–(12.6.43),
which holds; the \(D\)-term has coefficient \(\sum\pm x_i\zeta_{28-i}=+3\eta\)
(see [X17-E11.2.01]), so the total is \((3-2)\eta D=\eta D\), not \(-5\eta D\). In Lemma 12.6.5 the
\(c\)-term is \(-c\sum\pm x_i\zeta_{28-i}=-3c\eta\). The operators used are consistent:
\([P_i,P_j]=0\) for all \(i,j\), and Lemma 12.6.3 holds exactly.
Target: [X17.12.6.04], [X17.12.6.05].

### X17-E12.6.02. First exclusion set in Theorem 12.6.6 and Corollaries 12.6.7–12.6.8

Status: Open check.
Location: §12.6, pp. 459–463, Theorem 12.6.6, (12.6.86), (12.6.92); Corollary 12.6.7;
Corollary 12.6.8, (12.6.119).
Printed: irreducibility for \(c\notin\{-8+\frac53\mathbb N\}\cup\cdots\), the first set coming
from the invertibility of \(\eta(24-5(|\alpha|-1)+3c)\) in (12.6.92).
Correct: not determined. With [X17-E12.6.01] the scalar in (12.6.92) is
\(-(24-(|\alpha|-1)+3c)\), which vanishes for \(c\in-8+\frac13\mathbb N\). The proof as written
therefore establishes irreducibility only for \(c\notin(-8+\frac13\mathbb N)\cup\{\frac12(\ell(\lambda)
+\mathbb N)-4\}\cup\{\ell_\omega(\lambda)+\mathbb N\}\). Whether the printed, smaller exclusion
set suffices is not settled.
Evidence: (12.6.92) applies Lemma 12.6.5 to \(\partial_{x_{28-r}}(x^\alpha)v\), of degree
\(|\alpha|-1\); the condition from the corrected lemma is \(3c\ne(|\alpha|-1)-24\). The other two
sets are unaffected: the values \(\ell_\omega(k\lambda_1)=-16-\frac{4k}3\) (12.6.103) and the
bracket values \(\frac{2k}3,-\frac k3-5,-\frac{4k}3-16\) on \(\Upsilon(k\lambda_1)\) were checked
directly.
Target: [X17.12.6.06], [X17.12.6.07].

### Conventions and notation (not errata)

- §12.1 introduction (p. 403) says the representation is lifted from the "27-dimensional"
  module; the module of §12.1 is the 56-dimensional \(V(\lambda_7)\).
- In (12.4.7) \(\mathcal G^{D_6}\) means \(\mathcal G^{E_6}\); on p. 432 the sum
  \(c\sum_{i=1}^{16}x_i\partial_{x_i}\) runs to 27; after (12.6.37), \(\Phi^+_{D_6}\) means
  \(\Phi^+_{E_6}\); in (12.6.90) \(\alpha\in\mathbb N^{16}\) means \(\mathbb N^{27}\).
- After Theorem 12.5.1, "generalized module" means "generalized Verma module" (compare the
  parallel remark after Theorem 11.5.1).
- Theorem 12.8.1 writes \(\pi_c\) for the representation \(r_c\) defined in (12.8.3)–(12.8.31).
- In Lemma 12.6.1 the shift is \(\tilde\omega-c\) (not \(c/2\) as in Lemma 11.6.1) because
  \(\kappa\) is normalized differently in (12.5.42).

## Chapter 13. Oscillator Representations of gl(n|m) and osp(n|2m)

Source: Chapter 13, printed pp. 481–521 (PDF pp. 504–544; PDF page \(=p+23\)).

Throughout, \(N=m+1-n\).

### X17-E13.1.01. Range of non-complete reducibility of the bigraded spaces

Status: Confirmed.
Location: §13.1.3, p. 494, Remark 13.1.7 (lines 3–4 of the remark).
Printed: "This also shows that \(\mathscr A_{\ell,\ell'}\) is not completely reducible when
\(|\ell-\ell'|\le m+1-n\) and \(\ell+\ell'>m+1-n\)."
Correct: \(\mathscr A_{\ell,\ell'}\) contains a reducible (indecomposable) summand
\(\eta^i\mathcal H_{\ell-i,\ell'-i}\), hence is not completely reducible, iff \(|\ell-\ell'|<N\) and
\(\ell+\ell'>N\). For \(|\ell-\ell'|=N\) the decomposition \(\mathscr A_{\ell,\ell'}=\bigoplus_i
\eta^i\mathcal H_{\ell-i,\ell'-i}\) of Theorem 13.1.6 holds with all summands irreducible.
Evidence: By Theorem 13.1.6, \(\eta^i\mathcal H_{\ell-i,\ell'-i}\) is reducible iff
\(\ell-i,\ell'-i\le N\) and \(\ell+\ell'-2i>N\). If \(\ell=\ell'+N\), then \(\ell-i\le N\) forces
\(i=\ell'\), and then \(\ell+\ell'-2i=N\); so no summand is reducible. Computation of the
singular vectors and of the submodule generated by the highest vector in each summand:
\(\mathfrak{gl}(2|1)\) (\(N=0\)), \(\mathscr A_{1,1}\) (dimension \(9\)) \(=\mathcal H_{1,1}\)
(\(8\), irreducible) \(\oplus\ \eta\mathcal H_{0,0}\) (\(1\)); \(\mathfrak{gl}(2|2)\) (\(N=1\)),
\(\mathscr A_{2,1}\) (\(32\)) \(=\mathcal H_{2,1}\) (\(28\), irreducible) \(\oplus\ \eta\mathcal
H_{1,0}\) (\(4\)), and \(\mathscr A_{3,2}\) (\(96\)) \(=64+28+4\), all three summands irreducible.
Target: [X17.13.1.15], [X17.13.1.13].

### X17-E13.3.01. Indecomposability and complete reducibility for osp(2n|2m)

Status: Confirmed.
Location: §13.3, p. 507, remark after the proof of Theorem 13.3.1, lines 1–3.
Printed: "if \(m+1-n<k\le2(m+1-n)\), then \(\mathcal H_k\) is an indecomposable
\(\mathfrak{gl}(n|m)\)-module. … This also shows that \(\mathscr A_k\) is not completely
reducible when \(k>m+1-n\)."
Correct: \(\mathcal H_k\) is an indecomposable \(\mathfrak{osp}(2n|2m)\)-module for
\(N<k\le2N\). \(\mathscr A_k=\bigoplus_i\eta^i\mathcal H_{k-2i}\) is not completely reducible iff
some \(k-2i\in\overline{N+1,2N}\), i.e. iff \(N\ge2\) and \(k>N\), or \(N=1\) and \(k\ge2\) is even.
Evidence: As a module over \(\mathcal K\cong\mathfrak{gl}(n|m)\), \(\mathcal H_k=\bigoplus_{i}
\mathcal H_{i,k-i}\) is a direct sum of nonzero submodules, hence decomposable. For
\(\mathfrak{osp}(4|4)\) (\(n=m=2\), \(N=1\)), computation of singular vectors and generated
submodules gives \(\dim\mathcal H_k=1,8,31,80,160\) for \(k=0,\dots,4\), only \(\mathcal H_2\)
reducible, and \(\mathscr A_3=\mathcal H_3\oplus\eta\mathcal H_1\) (\(80+8\)) with both summands
irreducible, although \(3>N\). For \(n=m+1\) (\(N=0\)) every \(\mathcal H_k\) is irreducible and
\(\mathscr A_1=\mathcal H_1\).
Target: [X17.13.3.05].

### X17-E13.3.02. Degree condition in the noncanonical graded space

Status: Confirmed.
Location: §13.3, p. 508, (13.3.51).
Printed: \(\mathscr A_{\langle k\rangle}=\mathrm{Span}\{x^\alpha y^\beta\Theta_1^{\ell_1}
\Theta_2^{\ell_2}:\sum_{r>n_1}\alpha_r-\sum_{i\le n_1}\alpha_i+\sum_{i\le n_2}\beta_i-
\sum_{r>n_2}\beta_r+\ell_1+\ell_2=\ell_2\}\) for \(k\in\mathbb Z\).
Correct: the right-hand side of the degree condition is \(k\).
Evidence: The printed condition does not involve \(k\) and would make
\(\mathscr A_{\langle k\rangle}\) independent of \(k\); the subsequent use
\(\mathscr A_{\langle k\rangle}=\sum_\ell\mathscr A_{\langle\ell,k-\ell\rangle}\) and Claim 1
(\(x_{n_1+1}^k\in\mathcal H_{\langle k\rangle}\)) require total signed degree \(k\).
Target: [X17.13.3.06].

### X17-E13.4.01. Graded pieces in the noncanonical osp(2n+1|2m) theorem

Status: Confirmed.
Location: §13.4, p. 516, (13.4.30)–(13.4.31).
Printed: \(\mathscr B_k=\sum_{i\ge0}\mathscr A_{k-i}x_0^i\), \(\mathcal H_k=\{f\in\mathscr B_k:
\Delta'_{n_1,n_2}(f)=0\}\) (13.4.30), and \(\mathscr B=\bigoplus_{\ell,k=0}^\infty\eta'^\ell
(\mathcal H'_{\langle k\rangle})\) (13.4.31).
Correct: \(\mathscr B_{\langle k\rangle}=\sum_{i\ge0}\mathscr A_{\langle k-i\rangle}x_0^i\),
\(\mathcal H'_{\langle k\rangle}=\{f\in\mathscr B_{\langle k\rangle}:\Delta'_{n_1,n_2}(f)=0\}\)
(the noncanonical grading of (13.3.51)), and \(\mathscr B=\bigoplus_{\ell\in\mathbb N,\,k\in
\mathbb Z}\eta'^\ell(\mathcal H'_{\langle k\rangle})\).
Evidence: (13.4.30) itself says "We take the notation in (13.3.51)", and Theorem 13.4.2 is
stated for \(\mathcal H'_{\langle k\rangle}\), \(k\in\mathbb Z\). The canonical \(\mathscr A_{k}\) is
not invariant under the noncanonical representation (e.g. \(E_{i,j}|=\partial_{x_i}\partial_{x_j}\)
for \(i\le n_1<j\) lowers the total degree by \(2\)). With \(k\ge0\) only, (13.4.31) misses
\(\mathcal H'_{\langle-1\rangle}\ni x_{n_1}\), so the sum is not all of \(\mathscr B\).
Target: [X17.13.4.04], [X17.13.4.05].

### Conventions and notation (not errata)

- \(\mathbb N\) contains \(0\); \(\overline{m_1,m_2}=\{m_1,\dots,m_2\}\).
- "Irreducible" for modules of a Lie superalgebra refers to \(\mathbb Z_2\)-graded submodules.
- In §13.2 the parameters satisfy \(1\le n_1\), \(n_1+1<n_2\le n\); in §§13.3–13.4,
  \(n_1,n_2\in\overline{1,n}\) with \(n_1+1<n_2\).
- p. 501: "Lemma 12.2.3" means Lemma 13.2.3.
- (13.3.68): \(V\) is written where \(U\) is meant.
- (13.4.10), (13.4.26): "\(2n++m\)" is a typographical slip for \(2n+m\).
- The proof of Lemma 13.1.5 refers to the Lie algebra \(\mathcal G\) of (13.1.42); it is the
  even subalgebra \(\bar{\mathcal G}+\check{\mathcal G}\) of (13.1.13)–(13.1.17).
- Theorems 13.1.6, 13.2.5, 13.3.2 and 13.4.2 for the infinite-dimensional noncanonical modules
  use algebraic direct sums (each element has finitely many nonzero components).

## Chapter 14. Representation Theoretic Codes

Source: Chapter 14, printed pp. 523–554 (PDF pp. 545–576; PDF page \(=p+22\)).

### X17-E14.2.01. Weight table of the binary code of the exterior cube, n = 15

Status: Confirmed.
Location: §14.2, p. 531, Table 14.4 (column \(t=3\)).
Printed: \(\mathrm{wt}\,u(3)=216\) for \(C_2(\Lambda^3)\), \(n=15\).
Correct: \(\mathrm{wt}\,u(3)=236\).
Evidence: \(u(t)\) has difference vector supported on \(2t\) indices, and its weight is the number
of \(3\)-subsets of \(\overline{1,15}\) meeting that support in an odd number of points:
\(2t\binom{15-2t}2+\binom{2t}3\). For \(t=1,2\) this gives \(156\), \(224\), matching the table;
for \(t=3\), \(6\binom92+\binom63=216+20=236\). The minimum distance \(156\) of Theorem 14.2.2 is
unaffected.
Target: [X17.14.2.03].

### X17-E14.2.02. Length of the ternary code of the exterior cube for n = 6

Status: Confirmed.
Location: §14.2, p. 535, remark after the proof of Theorem 14.2.3, line 4.
Printed: "\(C_3(\Lambda^3)\) is a ternary orthogonal … \([15,4,12]\)-code if \(n=6\)".
Correct: \([20,4,12]\).
Evidence: The length of \(C_3(\Lambda^3)\) is \(\binom63=20\); Theorem 14.2.3 for \(n\equiv0
\pmod3\) gives \([\binom n3,n-2,(n-2)(n-3)]=[20,4,12]\), confirmed by enumeration.
Target: [X17.14.2.04].

### X17-E14.2.03. Minimal distance of the ternary weight code of the adjoint module of sl(3m)

Status: Confirmed.
Location: §14.2, p. 536, Theorem 14.2.4 (second sentence).
Printed: for \(n=3m\), \(m>1\), \(\mathcal C_K\) is an orthogonal \([\binom{3m}2,3m-2,3(m-1)]\)-code.
Correct: \(\mathcal C_K\) is an orthogonal \([\binom{3m}2,3m-2,3(2m-1)]\)-code
(minimal distance \(2n-3\)).
Evidence: A codeword of \(\mathcal C_K\) is \((d_i-d_j)_{i<j}\) with \(d\in\mathbb F_3^n\),
\(\sum d_i=0\). The choice \(d=e_s-e_t\) (from \(E_{s,s}-E_{t,t}\)) has weight \(2(n-2)+1=2n-3\).
Enumeration: \(n=6\) gives \([15,4,9]\) and \(n=9\) gives \([36,7,15]\), both orthogonal; the
printed distances would be \(3\) and \(6\).
Target: [X17.14.2.05].

### X17-E14.3.01. Minimal distance of the spin-module code

Status: Confirmed.
Location: §14.3, p. 544, Theorem 14.3.3.
Printed: for \(m>3\), \(C_3(V)\) is of type \([2^{m-1},m,2^{m-2}]\) if \(m\ne6\), and \([32,6,12]\)
when \(m=6\).
Correct: the type \([2^{m-1},m,2^{m-2}]\) holds for \(m=5,7,9\) and \([32,6,12]\) for \(m=6\); for
\(m=4\) the code is \([8,4,2]\) and for \(m=8\) it is \([128,8,58]\). The general minimal distance
must include the codeword \(u(m)=\sum_r\xi_r\), which is not Weyl-conjugate to the codewords
treated in (14.3.45)–(14.3.47) (those formulas need \(t<m\)).
Evidence: For \(u(m)\), the coordinate at the weight \(\frac12\sum_r(-1)^{[r\in J]}\varepsilon_r\)
(\(|J|\) even) is \(\equiv\frac12(m-2|J|)\pmod3\) up to sign. For \(m=4\) it vanishes unless
\(|J|-2\not\equiv0\pmod3\), i.e. only for \(J=\emptyset\) and \(J=\overline{1,4}\): weight \(2\).
For \(m=8\) the nonzero coordinates are those with \(|J|\in\{0,2,6,8\}\): weight
\(1+28+28+1=58<64\). Enumeration of all \(3^m\) codewords gives these minima, and the stated
values for \(m=5,6,7,9\).
Target: [X17.14.3.04].

### X17-E14.3.02. Dimensions in the examples after Corollary 14.3.4

Status: Confirmed.
Location: §14.3, p. 546, paragraph after the proof of Corollary 14.3.4.
Printed: "\([400,8,186]\)-code" (\(m=9\)) and "\([1134,8,549]\)-code" (\(m=11\)).
Correct: \([400,9,186]\) and \([1134,11,549]\).
Evidence: Corollary 14.3.4 gives dimension \(m\) in every case; enumeration of the generated
ternary codes gives rank \(9\) and \(11\), with the stated lengths and distances and
orthogonality.
Target: [X17.14.3.05].

### Conventions and notation (not errata)

- "Theorem 2.2" on p. 528 means Theorem 14.2.2; "(cf. (14.2.18))" before Theorem 14.2.3 refers
  to the matrix (14.2.13).
- "when \(n=6\)" in Theorem 14.3.3 means \(m=6\).
- For a self-dual module the ternary weight code is generated by the half matrix \(A\) of
  \(C(V)=(-A,A)\), so its length is half the number of nonzero weights.
- In \(\mathbb F_3\), \(1/2\equiv-1\); weights with half-integer coordinates are reduced this way.
- In Corollary 14.3.4, "\(\mathcal C_2\oplus C_3(V)\)" is the code generated by the juxtaposed
  generator matrices (dimension \(m\)), not a direct sum of codes.
- The F4 and E6–E8 matrices (14.4.6), (14.4.8), (14.4.16), … agree with the root-system weight
  matrices up to signs and order of columns, which do not change the code parameters.

## Chapter 15. Path Hypergeometric Functions

Source: Chapter 15, printed pp. 555–616 (PDF pp. 577–638; PDF page \(=p+22\)).

### X17-E15.1.01. Kinetic term of the Olshanetsky–Perelomov equation

Status: Confirmed.
Location: §15.1, p. 557, (15.1.5).
Printed: \(\sum_{i=1}^n\partial^2_{z_i}(\Psi)+[\cdots]\Psi=\nu\Psi\).
Correct: \(\sum_{i=1}^n(z_i\partial_{z_i})^2(\Psi)+[\cdots]\Psi=\nu\Psi\).
Evidence: Under \(z_i=e^{2x_i}\), \(\partial_{x_i}=2z_i\partial_{z_i}\), so
\(\partial^2_{x_i}=4(z_i\partial_{z_i})^2\), exactly as in (15.1.4). Theorems 15.1.3–15.1.5 and
15.2.2 are stated and verified with \((z_r\partial_{z_r})^2\); e.g. for \(n=1\),
\(\varphi^B_{\mu,0}=(z^{1/2}-z^{-1/2})^\mu\) satisfies \((z\partial_z)^2\varphi+\mu(1-\mu)
\frac z{(z-1)^2}\varphi=\frac{\mu^2}4\varphi\), but not the equation with \(\partial_z^2\).
Target: [X17.15.1.01].

### X17-E15.1.02. Sign in the type C one-variable identity

Status: Confirmed.
Location: §15.1, p. 564, (15.1.29).
Printed: \((z_r\partial_{z_r})^2[(z_r-z_r^{-1})(z_r+z_r^{-1})^k]=(k+1)^2(z_r-z_r^{-1})(z_r+z_r^{-1})^k
+4k(k-1)(z_r-z_r^{-1})(z_r+z_r^{-1})^{k-2}\).
Correct: the last term is \(-4k(k-1)(z_r-z_r^{-1})(z_r+z_r^{-1})^{k-2}\).
Evidence: With \(u=z+z^{-1}\), \(v=z-z^{-1}\): \(z\partial u=v\), \(z\partial v=u\), \(v^2=u^2-4\).
Then \(z\partial(vu^k)=u^{k+1}+kv^2u^{k-1}=(k+1)u^{k+1}-4ku^{k-1}\), and applying \(z\partial\)
again gives \((k+1)^2vu^k-4k(k-1)vu^{k-2}\). Symbolic check for \(k=3\). The eigenvalue (15.1.30)
is unaffected (Lemma 15.1.1 is applied to the leading terms of the determinant (15.1.28)).
Target: [X17.15.1.06].

### X17-E15.1.03. Sign in the type B one-variable identity

Status: Confirmed.
Location: §15.1, p. 565, (15.1.38).
Printed: \((z\partial_z)^2[(z^{1/2}-z^{-1/2})(z^{1/2}+z^{-1/2})^{2k}]=\frac{(2k+1)^2}4(\cdots)^{2k}
+2k(2k-1)(z^{1/2}-z^{-1/2})(z^{1/2}+z^{-1/2})^{2(k-1)}\).
Correct: the last term has coefficient \(-2k(2k-1)\).
Evidence: With \(u=z^{1/2}+z^{-1/2}\), \(v=z^{1/2}-z^{-1/2}\): \(z\partial u=v/2\),
\(z\partial v=u/2\), \(v^2=u^2-4\); \(z\partial(vu^{2k})=(k+\frac12)u^{2k+1}-4ku^{2k-1}\) and then
\((z\partial)^2(vu^{2k})=\frac{(2k+1)^2}4vu^{2k}-2k(2k-1)vu^{2k-2}\). Symbolic check for \(k=3\). The
eigenvalue (15.1.39) is unaffected.
Target: [X17.15.1.07].

### X17-E15.2.01. Eigenvalue constant for the type A Etingof trace

Status: Confirmed.
Location: §15.2, pp. 571–572, (15.2.27)–(15.2.30).
Printed: \(\sum_r(z_r\partial_{z_r})^2W_{A_{n-1}}=\big(\frac12+2\binom n3\big)W_{A_{n-1}}\), and
\(\nu=b+\frac12+2\binom n3\) in (15.2.29)–(15.2.30).
Correct: \(\sum_r(z_r\partial_{z_r})^2W_{A_{n-1}}=\frac{n(n^2-1)}{12}W_{A_{n-1}}\) and
\(\nu=b+\frac{n(n^2-1)}{12}\).
Evidence: (15.1.17) with \(\mu_1=\frac{1-n}2\), \(\mu_2=1\) gives \(n\mu_1^2+n(n-1)(\mu_1+\frac12)+
2\binom n3=\frac{n(n-1)(n+1)}{12}\) (and \(2\mu_2(1-\mu_2)=0\)); this is \(|\rho|^2\) for
\(A_{n-1}\). For \(n=3\) the correct constant is \(2\), the printed one \(\frac52\); they agree only
for \(n=2\). Numerical check for \(n=3\), \(\kappa=2/7\), \(\sigma=-5/3\), \(\lambda_3=1/5\), at
\(z=(1,0.12,0.013)\) using the series of Theorem 15.3.3: \(\big(\sum(z_i\partial_{z_i})^2-2\kappa
(\kappa+1)\sum_{i<j}\frac{z_iz_j}{(z_i-z_j)^2}\big)\Psi_A/\Psi_A=2.82385487528\ldots=b+2\), where
\(b\) is the Casimir value of \(M(\lambda)\).
Target: [X17.15.2.02].

### X17-E15.4.01. The arguments ξ^C on the diagonal

Status: Open check.
Location: §15.4, pp. 598–602, (15.4.73)–(15.4.98).
Printed: \(\xi^C_{n+i,i}=-\frac14y_{i,i}\cdots y_{n,n}\prod_{k=i}^{n-1}(1+w^{(2k)}_{k,k+1})\)
(15.4.98), with the \(w^{(j)}\) defined recursively in (15.4.77)–(15.4.95) starting from
\(w_{k,n}=y_{n,k}\) (15.4.73).
Correct: for \(n=2\), \(\xi^C_{3,1}=-\frac14y_{1,1}y_{2,2}(1+2y_{2,1})\), i.e. the factor
\(1+w^{(2)}_{1,2}\) must be \(1+2y_{2,1}\); the recursion does not define \(w^{(2)}_{1,2}\), and
taking \(w_{1,2}=y_{2,1}\) from (15.4.73) gives a wrong result. Question: what is the correct
general-\(n\) definition (conjecturally the recursion should start from \(w_{k,n}=2y_{n,k}\))?
Evidence: For \(n=2\), \(\lambda_2=3/7\), the trace \(\mathcal E_C\) was computed by brute force in
the Verma module (singular vector (15.4.30) and intertwiner) and expanded in \(A=z_2/z_1\),
\(C=z_2^{-2}\). With \(\xi^A_{2,1}=\frac{z_2}{z_2-z_1}\), \(\xi^C_{4,1}=\frac12y_{2,1}y_{2,2}\),
\(\xi^C_{4,2}=-\frac14y_{2,2}\) and the corrected prefactor of [X17-E15.4.02]: with
\(\xi^C_{3,1}=-\frac14y_{1,1}y_{2,2}(1+y_{2,1})\) the first discrepancy is at \(A^3C^3\)
(\(76700023/17301504\) against \(69130615/17301504\), difference \(7/16\)); with the factor
\(1+2y_{2,1}\) all coefficients agree through \(A^5C^5\). The alternatives \((1+y_{2,1})^2\) and
\((1-y_{2,1})^{-2}\) fail at \(A^4C^4\). General \(n\) was not checked.
Target: [X17.15.4.03], [X17.15.4.06].

### X17-E15.4.02. Prefactor of the type C Etingof trace

Status: Confirmed.
Location: §15.4, p. 603, Theorem 15.4.1, (15.4.107).
Printed: numerator \(x^*z_n^{n+\lambda_n+1}\prod_{i=1}^{n-1}z_i^{2n-i+1/2}\).
Correct: numerator \(x^*\prod_{i=1}^nz_i^{\lambda_i+2n-i+1}\), \(\lambda_i=\lambda(C_{i,i})=
\lambda_n-\frac{n-i}2\); i.e. \(z_i^{\lambda_n+(3n-i)/2+1}\) (the printed exponent for \(i=n\)).
Evidence: The term of \(\mathcal E_C\) from \(v_\lambda\) is \(z^\lambda x^*=x^*\prod_iz_i^{\lambda_i}\)
times \(1\). The denominator \(\prod_{r_1<r_2}(z_{r_1}-z_{r_2})\prod_{s_1\le s_2}(z_{s_1}z_{s_2}-1)\)
has leading monomial \(\prod_iz_i^{2n-i+1}\) (for \(|z_1|\gg\dots\gg|z_n|\gg1\)), and \(X_C=1+\dots\),
so the numerator must be \(x^*\prod_iz_i^{\lambda_i+2n-i+1}\); the printed one has leading term
\(z_n^{\lambda_n}\prod_{i<n}z_i^{-1/2}\), which is independent of \(\lambda_n\) in \(z_1,\dots,
z_{n-1}\). For \(n=2\), \(\lambda_2=3/7\), the corrected prefactor \(z_1^{\lambda_2+7/2}z_2^{\lambda_2+3}\)
reproduces the brute-force trace through \(A^5C^5\) (with [X17-E15.4.01]); the printed
\(z_1^{7/2}z_2^{\lambda_2+3}\) does not. For \(n=1\) both agree.
Target: [X17.15.4.06].

### X17-E15.4.03. Prefactor of the type C eigenfunction

Status: Confirmed.
Location: §15.4, p. 603, (15.4.108).
Printed: \(\Psi_C=z_n^{\lambda_n+2-n}\prod_{i=1}^{n-1}z_i^{-i-1/2}X_C(\frac12,\dots,\frac12;-\lambda_n)
\{\cdots\}\).
Correct: \(\Psi_C=\prod_{r=1}^nz_r^{\lambda_r+n-r+1}X_C(\frac12,\dots,\frac12;-\lambda_n)\{\cdots\}\),
\(\lambda_r=\lambda_n-\frac{n-r}2\).
Evidence: \(\Psi_C=(x^*)^{-1}W_{C_n}\mathcal E_C\) (15.2.49) and \(W_{C_n}=\prod_{r_1<r_2}(z_{r_1}-
z_{r_2})\prod_{s_1\le s_2}(z_{s_1}z_{s_2}-1)\big/\prod_rz_r^n\) (from \(z+z^{-1}-w-w^{-1}=
(z-w)(zw-1)/(zw)\) and \(z-z^{-1}=(z^2-1)/z\)). Even from the printed (15.4.107) this gives
\(z_n^{\lambda_n+1}\prod_{i<n}z_i^{n-i+1/2}\), not the printed (15.4.108); for \(n=2\) the printed
form is \(z_2^{\lambda_2}z_1^{-3/2}\), the correct one \(z_1^{\lambda_2+3/2}z_2^{\lambda_2+1}\). For
\(n=1\), \(\Psi_C=z^{\lambda+1}{}_2F_1(\frac14,\frac34;-\lambda;-\frac1{z^2-1})\) satisfies the
equation of Theorem 15.2.2.
Target: [X17.15.4.06].

### X17-E15.5.01. Diagonal coefficient in the differentiation formulas of types C, B, D

Status: Confirmed.
Location: §15.5, p. 611, (15.5.53); p. 613, (15.5.71); p. 614, (15.5.74).
Printed: the first sum in \(\partial_{z_{n+r_2,r_1}}X\) is \(\frac1\vartheta\sum_{i=1}^{r_1}\tau_i^2
P_{[i,r_1]}P_{[i,r_2]}X[i(2)]\) (\(X=X_C,X_B,X_D\)).
Correct: \(\frac1\vartheta\sum_{i=1}^{r_1}\tau_i(\tau_i+1)P_{[i,r_1]}P_{[i,r_2]}X[i(2)]\).
Evidence: For \(n=2\), \(r_1=1\), \(r_2=2\), type C: the coefficient of \(z_{2,1}\) in
\(\partial_{z_{4,1}}X_C\) is \(\tau_1(\tau_1+1)(\tau_2-1)/\vartheta\) (from (15.4.106)), while the
printed right side gives \(\tau_1(\tau_1+1)\tau_2/\vartheta-\tau_1^2/\vartheta\), which differs by
\(\tau_1/\vartheta\). The shift \(X[i(2)]\) arises from \((\tau_i)(\tau_i+1)\) in (15.5.45)/(15.5.51),
as in the third formula for \(s=1\). The corrected formulas agree with the series for \(n=3\)
through total degree \(2\) in all three types.
Target: [X17.15.5.11], [X17.15.5.15].

### X17-E15.5.02. Differentiation of X_C in the diagonal variables

Status: Confirmed.
Location: §15.5, p. 611, (15.5.54).
Printed: \(\partial_{z_{n+s,s}}X_C=\frac1\vartheta\big[\sum_{i=1}^s\tau_i^2P_{[i,s]}^2X_C[i(2)]+
\tau_sX_C[s(2)]+\sum_{i=1}^{s-1}\tau_iP_{[i,s]}X_C[i,s;1]+2\sum_{r_1<r_2\le s}\tau_{r_1}\tau_{r_2}
P_{[r_1,s]}P_{[r_2,s]}X_C[r_1,r_2;1]\big]\).
Correct: \(\partial_{z_{n+s,s}}X_C=\frac1\vartheta\big[\sum_{i=1}^s\tau_i(\tau_i+1)P_{[i,s]}^2X_C[i(2)]+
2\sum_{1\le r_1<r_2\le s}\tau_{r_1}\tau_{r_2}P_{[r_1,s]}P_{[r_2,s]}X_C[r_1,r_2;1]\big]\).
Evidence: For \(n=2\), \(s=2\): the coefficient of \(z_{2,1}\) in \(\partial_{z_{4,2}}X_C\) is
\(\tau_1(\tau_2^2-\tau_2)/\vartheta\), while the printed right side gives
\(\tau_1(\tau_2^2-\tau_2-1)/\vartheta\). The corrected formula agrees with the series for \(n=3\),
\(s=1,2,3\), through total degree \(2\). For \(s=1\) the printed and corrected forms coincide.
Target: [X17.15.5.11].

### X17-E15.5.03. Differentiation of X_B in the diagonal variables

Status: Confirmed.
Location: §15.5, p. 614, (15.5.72).
Printed: \(\partial_{z_{n+s,s}}X_B=\sum_{r=1}^s\tau_rP_{[s,r]}X_B[s]\).
Correct: \(\partial_{z_{n+s,s}}X_B=\frac1\vartheta\sum_{r=1}^s\tau_rP_{[r,s]}X_B[r]\).
Evidence: For \(n=1\), \(X_B(\tau;\vartheta)\{u\}={}_1F_1(\tau;\vartheta;u)\) and
\(\frac d{du}{}_1F_1(\tau;\vartheta;u)=\frac\tau\vartheta{}_1F_1(\tau+1;\vartheta+1;u)\), while the
printed formula gives \(\tau\,{}_1F_1(\tau+1;\vartheta+1;u)\). Also \(P_{[s,r]}\) is defined only for
\(s\le r\). The corrected formula agrees with the series for \(n=3\) through total degree \(2\).
Target: [X17.15.5.15].

### Conventions and notation (not errata)

- Rising factorial \((c)_i\) (15.3.18), falling factorial \(\langle c\rangle_i\) (15.3.11).
- The sign of \(K\) in (15.1.4): with \(+K\), the trace function of Theorem 15.2.1 gives
  \(K=-2\kappa(\kappa+1)\), and \(\varphi^A_{\mu_1,\mu_2}\) gives \(K=2\mu_2(1-\mu_2)\).
- (15.3.4): "Under the assumption (15.4.1)" means (15.3.1). Before Theorem 15.3.1,
  "(15.3.17)–(15.4.20)" means (15.3.17)–(15.3.20).
- (15.3.38): the operator is \(x_{j_1}\partial_{x_{j_2}}-\kappa\delta_{j_1,j_2}\), as in (15.2.12).
- (15.4.4): the negative root vectors "\(C_{i,n+j}\)" are \(C_{n+i,j}\) (\(j\le i\)).
- (15.4.18): "\(E^\alpha v_\lambda\)" means \(C^\alpha v_\lambda\).
- (15.1.44): the left side reads \(\varphi^C_{\mu_1,\mu_2}\) where \(\varphi^B_{\mu_1,\mu_2}\) is meant
  (Theorem 15.1.5).
- (15.2.62): the range "\(1<i_1<i_2\le n\)" means \(1\le i_1<i_2\le n\).
- (15.5.12): \(\partial_{z_{r,1}}X_A=\tau_1X_A[1,r]\) is for \(r\in\overline{2,n-1}\).
- (15.5.49)–(15.5.50): \(X_C[i_1,i_2]\), \(X_C[i_1,i_2;1]\) mean \(X_C[r_1,r_2]\), \(X_C[r_1,r_2;1]\).
- (15.5.69): "\(X_N\)" means \(X_B\).
- Formal power series identities in §§15.3–15.5 hold coefficientwise; complex powers in the
  prefactors and in Theorem 15.5.2 need a branch choice, which the source does not specify.

[X17.01.1.01]: SYNOPSIS-Xu2017.md#x1701101-algebras-and-associative-algebras
[X17.01.1.02]: SYNOPSIS-Xu2017.md#x1701102-groups-and-group-algebras
[X17.01.5.03]: SYNOPSIS-Xu2017.md#x1701503-nilpotency-of-mathcal-k_n-and-of-strictly-upper-triangular-matrices
[X17.02.2.03]: SYNOPSIS-Xu2017.md#x1702203-lifting-to-an-oscillator-polynomial-representation
[X17.03.1.03]: SYNOPSIS-Xu2017.md#x1703103-root-data-of-the-classical-lie-algebras
[X17.03.2.12]: SYNOPSIS-Xu2017.md#x1703212-weyl-groups-of-the-classical-root-systems
[X17.03.4.02]: SYNOPSIS-Xu2017.md#x1703402-lattices-and-fundamental-weights-of-a_n-1-b_n-c_n-d_n
[X17.03.4.03]: SYNOPSIS-Xu2017.md#x1703403-the-root-system-and-lattices-of-e_8
[X17.03.4.04]: SYNOPSIS-Xu2017.md#x1703404-bases-of-e_7-and-e_6
[X17.03.4.09]: SYNOPSIS-Xu2017.md#x1703409-automorphism-groups-modulo-the-weyl-group
[X17.04.2.01]: SYNOPSIS-Xu2017.md#x1704201-engel-subalgebras-and-normalizers
[X17.04.3.07]: SYNOPSIS-Xu2017.md#x1704307-the-torus-elements-sigmaa-on-mathfraksl_2-modules
[X17.04.3.08]: SYNOPSIS-Xu2017.md#x1704308-automorphism-group-modulo-mathcal-emathcal-g
[X17.04.4.04]: SYNOPSIS-Xu2017.md#x1704404-positive-roots-of-e_8-e_7-e_6
[X17.05.1.01]: SYNOPSIS-Xu2017.md#x1705101-free-associative-tensor-and-symmetric-algebras
[X17.05.2.06]: SYNOPSIS-Xu2017.md#x1705206-semisimple-algebras-tensor-decomposition-of-verma-and-irreducible-modules
[X17.05.4.01]: SYNOPSIS-Xu2017.md#x1705401-the-casimir-element-and-its-eigenvalue
[X17.06.1.03]: SYNOPSIS-Xu2017.md#x1706103-polynomial-solutions-of-a-wave-equation-in-riemannian-space
[X17.06.2.01]: SYNOPSIS-Xu2017.md#x1706201-root-data-of-mathfrakslnmathbb-f
[X17.06.2.06]: SYNOPSIS-Xu2017.md#x1706206-the-laplace-operator-and-the-mathfraksl2-relations
[X17.06.2.07]: SYNOPSIS-Xu2017.md#x1706207-harmonic-polynomials-for-mathfraksln
[X17.06.3.02]: SYNOPSIS-Xu2017.md#x1706302-signed-degree-grading
[X17.06.5.03]: SYNOPSIS-Xu2017.md#x1706503-structure-theorem-for-n_11n_2
[X17.06.5.04]: SYNOPSIS-Xu2017.md#x1706504-highest-weights-for-n_11n_2
[X17.06.6.03]: SYNOPSIS-Xu2017.md#x1706603-norms-of-the-singular-vectors-boundary-cases
[X17.06.6.04]: SYNOPSIS-Xu2017.md#x1706604-structure-theorem-for-n_1n_2
[X17.06.6.05]: SYNOPSIS-Xu2017.md#x1706605-highest-weights-for-n_1n_2
[X17.06.7.07]: SYNOPSIS-Xu2017.md#x1706707-finite-dimensional-mathfrakgln-modules-and-the-casimir
[X17.06.8.03]: SYNOPSIS-Xu2017.md#x1706803-explicit-form-of-pi_kappan_1
[X17.06.8.07]: SYNOPSIS-Xu2017.md#x1706807-case-n_11-twist-confined-to-swapped-variables
[X17.07.1.03]: SYNOPSIS-Xu2017.md#x1707103-harmonic-polynomials-for-o2n
[X17.07.3.05]: SYNOPSIS-Xu2017.md#x1707305-the-conformal-representation-of-o2n2
[X17.07.4.02]: SYNOPSIS-Xu2017.md#x1707402-structure-of-pi_c-on-polynomials
[X17.08.2.02]: SYNOPSIS-Xu2017.md#x1708202-invariant-operators-and-grading
[X17.08.2.04]: SYNOPSIS-Xu2017.md#x1708204-structure-of-the-noncanonical-o2n1-modules
[X17.08.3.02]: SYNOPSIS-Xu2017.md#x1708302-casimir-data-for-o2n1
[X17.08.3.03]: SYNOPSIS-Xu2017.md#x1708303-characteristic-polynomial-of-widetildeomega-for-o2n1
[X17.08.3.04]: SYNOPSIS-Xu2017.md#x1708304-the-conformal-representation-of-o2n3
[X17.08.3.05]: SYNOPSIS-Xu2017.md#x1708305-shens-extension-for-o2n3
[X17.08.3.08]: SYNOPSIS-Xu2017.md#x1708308-an-invariant-operator-for-o2n3
[X17.08.3.09]: SYNOPSIS-Xu2017.md#x1708309-irreducibility-of-the-odd-conformal-extension
[X17.08.4.01]: SYNOPSIS-Xu2017.md#x1708401-the-one-parameter-conformal-representation-of-o2n3
[X17.08.4.02]: SYNOPSIS-Xu2017.md#x1708402-structure-of-pi_c-for-o2n3
[X17.08.4.04]: SYNOPSIS-Xu2017.md#x1708404-odd-conformal-oscillator-representations
[X17.09.1.05]: SYNOPSIS-Xu2017.md#x1709105-primitive-exterior-forms
[X17.09.1.07]: SYNOPSIS-Xu2017.md#x1709107-irreducibility-of-the-weil-modules
[X17.09.2.03]: SYNOPSIS-Xu2017.md#x1709203-main-theorem-irreducibility-of-the-graded-pieces
[X17.09.3.02]: SYNOPSIS-Xu2017.md#x1709302-structure-of-the-projective-oscillator-module
[X17.10.1.06]: SYNOPSIS-Xu2017.md#x1710106-exterior-square-and-cube-of-the-7-dimensional-module
[X17.10.2.01]: SYNOPSIS-Xu2017.md#x1710201-the-five-variable-conformal-representation-of-g_2
[X17.10.2.02]: SYNOPSIS-Xu2017.md#x1710202-irreducibility-of-the-conformal-g_2-module
[X17.10.4.02]: SYNOPSIS-Xu2017.md#x1710402-the-quadratic-covariant-zeta
[X17.11.2.02]: SYNOPSIS-Xu2017.md#x1711202-dicksons-cubic-invariant
[X17.11.2.04]: SYNOPSIS-Xu2017.md#x1711204-decomposition-of-mathcal-a-and-dimension-identity
[X17.11.2.08]: SYNOPSIS-Xu2017.md#x1711208-the-commutator-mathcal-d_2eta-and-mathcal-d-on-etam-multiples
[X17.11.2.10]: SYNOPSIS-Xu2017.md#x1711210-main-theorem-dicksons-cubic-equation
[X17.11.6.06]: SYNOPSIS-Xu2017.md#x1711606-further-explicit-cases
[X17.12.6.04]: SYNOPSIS-Xu2017.md#x1712604-second-quadratic-identity-for-the-p_i
[X17.12.6.05]: SYNOPSIS-Xu2017.md#x1712605-the-corresponding-identity-on-widehat-m
[X17.12.6.06]: SYNOPSIS-Xu2017.md#x1712606-irreducibility-theorem-for-the-e_7-functor
[X17.12.6.07]: SYNOPSIS-Xu2017.md#x1712607-scalar-and-vector-cases
[X17.13.1.13]: SYNOPSIS-Xu2017.md#x1713113-super-analogue-of-the-theorem-on-harmonic-polynomials-for-glnm
[X17.13.1.15]: SYNOPSIS-Xu2017.md#x1713115-indecomposability-and-super-howe-duality
[X17.13.3.05]: SYNOPSIS-Xu2017.md#x1713305-indecomposability-for-osp2n2m
[X17.13.3.06]: SYNOPSIS-Xu2017.md#x1713306-the-noncanonical-oscillator-representation-of-osp2n2m
[X17.13.4.04]: SYNOPSIS-Xu2017.md#x1713404-noncanonical-representation-of-osp2n12m
[X17.13.4.05]: SYNOPSIS-Xu2017.md#x1713405-noncanonical-harmonic-theorem-for-osp2n12m
[X17.14.2.03]: SYNOPSIS-Xu2017.md#x1714203-binary-weight-code-of-the-exterior-cube
[X17.14.2.04]: SYNOPSIS-Xu2017.md#x1714204-ternary-codes-of-the-exterior-square-and-cube
[X17.14.2.05]: SYNOPSIS-Xu2017.md#x1714205-ternary-codes-from-the-adjoint-module-of-sln
[X17.14.3.04]: SYNOPSIS-Xu2017.md#x1714304-spin-modules-and-their-weight-codes
[X17.14.3.05]: SYNOPSIS-Xu2017.md#x1714305-weight-codes-of-the-adjoint-plus-spin-module
[X17.15.1.01]: SYNOPSIS-Xu2017.md#x1715101-calogerosutherland-and-olshanetskyperelomov-hamiltonians
[X17.15.1.06]: SYNOPSIS-Xu2017.md#x1715106-type-c-weyl-function-and-eigenfunctions
[X17.15.1.07]: SYNOPSIS-Xu2017.md#x1715107-type-b-weyl-function-and-eigenfunctions
[X17.15.2.02]: SYNOPSIS-Xu2017.md#x1715202-etingof-trace-function-of-type-a-and-the-sutherland-equation
[X17.15.4.03]: SYNOPSIS-Xu2017.md#x1715403-auxiliary-variables-y-w-and-the-arguments-ξc
[X17.15.4.06]: SYNOPSIS-Xu2017.md#x1715406-etingof-trace-of-sp2n-as-a-path-hypergeometric-function
[X17.15.5.11]: SYNOPSIS-Xu2017.md#x1715511-differential-property-of-x_c
[X17.15.5.15]: SYNOPSIS-Xu2017.md#x1715515-differential-properties-of-x_b-and-x_d
