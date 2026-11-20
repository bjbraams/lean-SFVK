/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module -- shake: keep-all

public import SFVK.SU11.Basic
public import SFVK.SU2.Basic

/-!
# Special functions and group representations: foundational layer

The foundational entry point. It collects the `Basic` layer of each area; these modules import
only Mathlib, Tau Ceti, `SFVKMathlib` and other foundational modules, and contain no `sorry`.
-/
