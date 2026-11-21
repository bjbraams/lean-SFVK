/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.RankOne.JacobiIdentities
public import SFVK.RankOne.JacobiAsymptotics
public import SFVK.RankOne.JacobiEstimates

/-!
# Jacobi functions

The Jacobi function `φ_λ^{(α,β)}(t) = F((ρ + iλ)/2, (ρ − iλ)/2; α + 1; −sinh² t)`,
`ρ = α + β + 1`, is lean-DLMF's `DLMF.Legendre.jacobiFunction α β λ t`, written there as
`Γ(α + 1) 𝐅(…)` with the principal-branch regularized Gauss function (DLMF 15.9.11), and used
here at real `t`. This file states its theory as a function of the radius: the value at the
origin, evenness, the Jacobi equation, uniqueness, the polynomial and elementary cases, the
quadratic transformation, the Harish-Chandra series `Φ_λ` and the connection formula with the
`c`-function, the asymptotics, the bounds, and Koornwinder's Laplace-type representation and
product formula.

Sources: DLMF 15.9.11–15.9.14; Klimyk–Vilenkin, *Representations of Lie Groups and Special
Functions* (Kirillov (ed.), EMS 59), Part II Ch. 5 §2.4, (12)–(14), p. 233; Vilenkin–Klimyk,
*Representation of Lie Groups and Special Functions*, Vol. 2, §11.4.6, (4)–(10), pp. 348–350;
Wawrzyńczyk, *Group Representations and Special Functions*, §18.5, (18.5.1)–(18.5.2),
pp. 627–628. lean-DLMF supplies `DLMF.Legendre.jacobiFunction` and the regularized Gauss
function.

## Main results

* `SFVK.RankOne.jacobiFunction_zero`, `SFVK.RankOne.jacobiFunction_even`,
  `SFVK.RankOne.jacobiFunction_neg_spectral`, `SFVK.RankOne.jacobiFunction_I_mul_rho`.
* `SFVK.RankOne.differentiable_jacobiFunction`: holomorphy in the spectral parameter.
* `SFVK.RankOne.jacobiOperator_jacobiFunction`: the Jacobi equation.
* `SFVK.RankOne.jacobiFunction_eq_jacobiPolynomialP`: the terminating polynomial case.
-/
