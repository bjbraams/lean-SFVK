# Credits

- The initial statements are guided by the `SU2MatrixElements` and `FunctionSpaceModels` roadmaps.
  They use the Euler and matrix-element conventions of Edmonds and the invariant measures and
  function-space construction of Vilenkin and Klimyk, with source locators in the Lean files.
- `SFVK.SU2.UnitaryModel` reuses Tau Ceti's `SU2.symPowerModel` and
  `ContinuousLinearEquiv.congr`. The Euler parametrization uses `SU2.torusExp` and the
  projection to `SO(3)` uses `SU2.toSO3`.
- `SFVK.RepresentationTheory.MatrixElements` uses Mathlib's
  `HilbertBasis.hasSum_inner_mul_inner` and relates its convention to Tau Ceti's
  `ContRepresentation.matrixCoeff`. The `SU(1,1)` circle model uses Mathlib's
  `AddCircle.haarAddCircle` and `fourierLp`.
- `SFVK.SU2.SpecialFunctions` uses lean-DLMF's
  `DLMF.OrthogonalPolynomials.jacobiPolynomialP`,
  `DLMF.OrthogonalPolynomials.legendrePolynomialP` and `DLMF.Legendre.ferrersPNat`.
