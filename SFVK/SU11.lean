/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import SFVK.SU11.Basic
public import SFVK.SU11.CircleModel
public import SFVK.SU11.Coordinates
public import SFVK.SU11.HaarShell
public import SFVK.SU11.MatrixElementKernels
public import SFVK.SU11.MatrixElementRecurrences
public import SFVK.SU11.MatrixElementSpecialFunctions
public import SFVK.SU11.MatrixElements
public import SFVK.SU11.Transforms

/-!
# `SU(1,1)` and the circle model of its principal series

The foundational layer `SFVK.SU11.Basic` together with the theorem layer: the Euler bijection
and Haar measure, the ambient shell construction of Haar measure, and the `L²` theory of the
circle model, together with boost matrix elements and the Mehler–Fock transform.
-/
