/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU2.Basic.Coordinates
public import SFVK.SU2.Basic.MatrixElements
public import SFVK.SU2.Basic.SO3
public import SFVK.SU2.Basic.UnitaryModel
public import SFVK.SU2.Basic.WignerSmallD

/-!
# `SU(2)`: foundational definitions

Edmonds's Euler coordinates and the Euler-angle measure, the rotations about the coordinate axes,
the spin `d/2` representation in the normalized monomial basis, its matrix elements and the
entry polynomial, and Wigner's small `d`-functions with their elementary values. Everything here
is fully proved.
-/
