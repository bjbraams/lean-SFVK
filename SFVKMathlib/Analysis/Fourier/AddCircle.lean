/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier characters of an additive circle

For every real period `T`, the character of `AddCircle T` at integer index `k` is the
`k`th power of the first character. This uses Mathlib's normalization of `AddCircle.fourier`.
-/

public section

namespace AddCircle

/-- The Fourier character at index `k` is the `k`th power of the first character. -/
theorem fourier_eq_zpow {T : ℝ} (k : ℤ) (x : AddCircle T) :
    fourier k x = fourier 1 x ^ k := by
  rw [fourier_apply, fourier_one, AddCircle.toCircle_zsmul, Circle.coe_zpow]

end AddCircle
