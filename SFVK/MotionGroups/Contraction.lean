/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import SFVK.SU2.Basic.WignerSmallD

/-!
# Contraction of `SO(3)` and `SO(n+1)` to the motion groups

As the radius of the sphere grows, the matrix elements of `SO(3)` tend to those of `M(2)` and
the zonal functions of `SO(n+1)` to those of `M(n)`: `d^l_{pq}(x/l) → J_{p-q}(x)` for the
Wigner functions `SFVK.SU2.wignerSmallD` of spin `l`, and
`l!/Γ(2p+l) C^p_l(cos(r/l)) → √π J_{p-1/2}(r) / ((2r)^{p-1/2} Γ(p))` for lean-DLMF's Gegenbauer
polynomials. Vilenkin–Klimyk, *Representation of Lie Groups and Special Functions*, Vol. 2,
§9.3.4 (3)–(4), p. 51.
-/

public noncomputable section

open Complex Filter Topology
open scoped Real

namespace SFVK.MotionGroups

/-- Contraction of Wigner's `d`-functions (Vilenkin–Klimyk Vol. 2 §9.3.4, p. 51): for fixed
`p, q ∈ ℤ` and real `x`, `d^l_{pq}(x/l) → J_{p-q}(x)` as `l → ∞`, with `d^l_{pq}` the
spin-`l` function `SFVK.SU2.wignerSmallD (2l) (l+p) (l+q)`. -/
theorem tendsto_wignerSmallD_besselJ (p q : ℤ) (x : ℝ) :
    Tendsto (fun l : ℕ =>
        (SFVK.SU2.wignerSmallD (2 * l) ((l : ℤ) + p).toNat ((l : ℤ) + q).toNat (x / l) : ℂ))
      atTop (𝓝 (besselJ (p - q : ℤ) x)) := by
  sorry

/-- Contraction of zonal functions (Vilenkin–Klimyk Vol. 2 §9.3.4 (3), p. 51): for `Re p > 0`
and `r > 0`, `l!/Γ(2p+l) C^p_l(cos(r/l)) → √π / ((2r)^{p-1/2} Γ(p)) J_{p-1/2}(r)`. -/
theorem tendsto_ultrasphericalPolynomial_besselJ {p : ℂ} (hp : 0 < p.re) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun l : ℕ => (l.factorial : ℂ) / Complex.Gamma (2 * p + l) *
        DLMF.OrthogonalPolynomials.ultrasphericalPolynomial p l (Real.cos (r / l)))
      atTop (𝓝 (Real.sqrt π / ((2 * r : ℂ) ^ (p - 1 / 2) * Complex.Gamma p) *
        besselJ (p - 1 / 2) r)) := by
  sorry

end SFVK.MotionGroups
