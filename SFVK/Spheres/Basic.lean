/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.Spheres.Basic.Disk
public import SFVKMathlib.MeasureTheory.Group.GelfandPair
public import SFVK.Spheres.Basic.Sphere
public import SFVK.Spheres.Basic.Zonal

/-!
# Spheres in higher dimension, `SO(n)` and `U(n)`: foundational definitions

The rotation and unitary groups with their actions and the stabilizers of a unit vector; the
normalized measures on the real and complex unit spheres; Gel'fand pairs and spherical
functions; the normalized zonal polynomials, zonal harmonics and branching harmonics of `SO(n)`;
the harmonics of bidegree `(p, q)`, the disk polynomials and the zonal harmonics of `U(n)`.
Everything here is fully proved.
-/
