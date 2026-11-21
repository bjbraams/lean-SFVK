/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# Borel structures on the classical matrix groups

The special orthogonal group `SO(n)` and the unitary group `U(n)`, as subtypes of the matrices
with the subspace topology, carry the Borel σ-algebra, so that Haar measures on them are Borel
measures.
-/

public noncomputable section

variable (n : Type*) [Fintype n] [DecidableEq n]

instance Matrix.specialOrthogonalGroup.instMeasurableSpace :
    MeasurableSpace (Matrix.specialOrthogonalGroup n ℝ) :=
  borel _

instance Matrix.specialOrthogonalGroup.instBorelSpace :
    BorelSpace (Matrix.specialOrthogonalGroup n ℝ) :=
  ⟨rfl⟩

instance Matrix.unitaryGroup.instMeasurableSpace : MeasurableSpace (Matrix.unitaryGroup n ℂ) :=
  borel _

instance Matrix.unitaryGroup.instBorelSpace : BorelSpace (Matrix.unitaryGroup n ℂ) :=
  ⟨rfl⟩
