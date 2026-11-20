# Credits

- The initial statements are guided by the `SU2MatrixElements` and `FunctionSpaceModels` roadmaps.
  They use the Euler and matrix-element conventions of Edmonds and the invariant measures and
  function-space construction of Vilenkin and Klimyk, with source locators in the Lean files.
- `SFVK.SU2.UnitaryModel` reuses Tau Ceti's `SU2.symPowerModel` and
  `ContinuousLinearEquiv.congr`. The Euler parametrization uses `SU2.torusExp` and the
  projection to `SO(3)` uses `SU2.toSO3`.
- The entry formula in `SFVK.SU2.Basic.MatrixElements` uses Tau Ceti's
  `SymmetricPower.lift` and `coeff_C_add_C_mul_X_pow`.
- The Euler Haar measure proof in `SFVK.SU2.Coordinates` uses Tau Ceti's
  `ContRepresentation.schur_orthogonality_basis` and Mathlib's
  measure extensionality for separating star subalgebras.
- `SFVK.RepresentationTheory.MatrixElements` uses Mathlib's
  `HilbertBasis.hasSum_inner_mul_inner` and relates its convention to Tau Ceti's
  `ContRepresentation.matrixCoeff`. The `SU(1,1)` circle model uses Mathlib's
  `AddCircle.haarAddCircle` and `fourierLp`.
- `SFVK.SU2.SpecialFunctions` uses lean-DLMF's
  `DLMF.OrthogonalPolynomials.jacobiPolynomialP`,
  `DLMF.OrthogonalPolynomials.legendrePolynomialP` and `DLMF.Legendre.ferrersPNat`.
- The Poisson density in `SFVK.SU11.CircleModel` uses Mathlib's
  `DiffContOnCl.circleAverage`, `DiffContOnCl.circleAverage_poissonKernel_smul`,
  and `span_fourier_closure_eq_top`.
- `SFVK.SU11.HaarShell` uses Mathlib's `Measure.map_linearMap_addHaar_eq_smul_addHaar`
  and `LinearMap.det_restrictScalars` for invariance of ambient Lebesgue measure.
- The Euler normalization in `SFVK.SU11.Coordinates` uses Mathlib's
  `Complex.lintegral_comp_pi_polarCoord_symm` and
  `lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn` to integrate the ambient shell.
- `SFVKMathlib.Analysis.Complex.EulerPhases` uses Mathlib's
  `AddCircle.measurePreserving_mk` and `MeasurePreserving.skew_product` for the distribution of
  the two phases.
- `SFVKMathlib.MeasureTheory.Group.Multiplier` uses Mathlib's
  `withDensity_eq_iff_of_sigmaFinite` to identify the quasi-invariance and unitarity densities.
