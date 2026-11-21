/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import SFVK.MotionGroups.Addition
public import SFVK.MotionGroups.Basic
public import SFVK.MotionGroups.CircleModel
public import SFVK.MotionGroups.Contraction
public import SFVK.MotionGroups.Hankel
public import SFVK.MotionGroups.Hyperbola
public import SFVK.MotionGroups.MatrixElements
public import SFVK.MotionGroups.Miller
public import SFVK.MotionGroups.Polar
public import SFVK.MotionGroups.Spherical

/-!
# Euclidean motion groups and Bessel functions

The plane motion group `M(2)` in polar coordinates; its circle models `T_R`, `R ∈ ℂ`, with
their matrix elements `i^{n-m} e^{i(n-m)φ} e^{-inα} J_{n-m}(R r)` and infinitesimal operators;
the addition theorem and the multiplication formula for `Jₙ`; Miller's complex group `T₃`; the
hyperbola model of `ISO(1,1)` and the Macdonald kernel; the quasi-regular representation of
`M(n)` and the Hankel transform; the Gel'fand pair `(M(n), SO(n))`; and the contraction of
`SO(3)` and `SO(n+1)` to the motion groups.
-/
