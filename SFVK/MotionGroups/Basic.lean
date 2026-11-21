/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import SFVK.MotionGroups.Basic.CircleModel
public import SFVK.MotionGroups.Basic.Group
public import SFVK.MotionGroups.Basic.Hyperbola
public import SFVK.MotionGroups.Basic.Miller
public import SFVK.MotionGroups.Basic.Zonal

/-!
# Motion groups: foundational definitions

The motion groups `M(n)` and `ISO(1,1)` with polar coordinates on `M(2)`, the circle models of
`M(2)` and the hyperbola model of `ISO(1,1)` with their realizations on `L²`, Miller's group
`T₃` with its multiplier representation and matrix elements, the Hankel transform, the zonal
Bessel functions and the spherical functions of `(M(n), SO(n))`. Everything here is fully
proved.
-/
