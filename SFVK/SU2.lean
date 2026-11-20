/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import SFVK.SU2.Basic
public import SFVK.SU2.Coordinates
public import SFVK.SU2.MatrixElements
public import SFVK.SU2.SO3
public import SFVK.SU2.SpecialFunctions
public import SFVK.SU2.UnitaryModel

/-!
# `SU(2)` and its matrix elements

The foundational layer `SFVK.SU2.Basic` together with the theorem layer: the Euler covering and
Haar measure, unitarity, the entry polynomial, the double cover of `SO(3)` in Euler angles, and
the Jacobi and Legendre forms of the small `d`-functions.
-/
