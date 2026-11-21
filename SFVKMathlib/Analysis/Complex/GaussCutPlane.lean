/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Basic.PrincipalBranch

/-!
# Nonpositive real arguments of the Gauss function

The nonpositive real axis lies in lean-DLMF's principal Gauss cut plane `ℂ \ [1, ∞)`.
In particular this gives the branch condition for the radial argument `−sinh² t`.
-/

public section

namespace Complex

/-- The negative square of the hyperbolic sine of a real radius lies in the Gauss cut plane. -/
theorem neg_sinh_sq_mem_gaussCutPlane (t : ℝ) :
    -(Complex.sinh t) ^ 2 ∈ DLMF.Hypergeometric.cutPlane := by
  rw [DLMF.Hypergeometric.mem_cutPlane, sub_neg_eq_add, ← ofReal_sinh, ← ofReal_pow,
    ← ofReal_one, ← ofReal_add, ofReal_mem_slitPlane]
  positivity

end Complex
