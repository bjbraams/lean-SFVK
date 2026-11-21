/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import SFVKMathlib.Analysis.Complex.EulerPhases
public import SFVKMathlib.MeasureTheory.Group.GelfandPair
public import SFVKMathlib.MeasureTheory.Group.MatrixGroups
public import SFVKMathlib.MeasureTheory.Group.Multiplier
public import SFVKMathlib.MeasureTheory.Group.MultiplierRepresentation
public import SFVKMathlib.RepresentationTheory.Continuous.MatrixElement

/-!
# General auxiliary results for SFVK

These modules extend Mathlib and Tau Ceti APIs and are not specific to special functions.
They use the namespaces of the APIs they extend.

* `SFVKMathlib.Analysis.Complex.EulerPhases`: half-sum and half-difference coordinates on
  the product of two unit circles.
* `SFVKMathlib.MeasureTheory.Group.GelfandPair`: bi-invariant functions, Gel'fand pairs and
  spherical functions of a subgroup.
* `SFVKMathlib.MeasureTheory.Group.MatrixGroups`: Borel structures on `SO(n)` and `U(n)`.
* `SFVKMathlib.MeasureTheory.Group.Multiplier`: multiplier actions of a group on functions and
  measures quasi-invariant with a given density.
* `SFVKMathlib.MeasureTheory.Group.MultiplierRepresentation`: the multiplier representation on
  `L²`, defined by choice.
* `SFVKMathlib.RepresentationTheory.Continuous.MatrixElement`: matrix elements of a continuous
  representation in a Hilbert basis.
-/
