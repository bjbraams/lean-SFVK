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
- `SFVK.ClebschGordan` uses Tau Ceti's fixed-sum parity reindexing, character transport and
  the weight-string formula on the maximal torus. Its comparisons with Wigner symbols,
  special values and permutation identities use lean-DLMF's Wigner-symbol library. Hahn
  reflection and the Racah-to-Hahn limit use lean-DLMF's cleared Sheppard transformation
  and its complex Racah limit.
- The Gel'fand criterion in `SFVKMathlib.MeasureTheory.Group.GelfandPair` uses Mathlib's Haar
  translation and inversion formulas. `SFVK.Spheres.Unitary` uses Tau Ceti's Gram rigidity
  and unitary matrix isometries for the orbit and double-coset arguments.
  `SFVK.Spheres.DiskPolynomials`
  uses lean-DLMF's Jacobi binomial expansion, disk orthogonality and Jacobi norm. The complex
  sphere marginal uses Tau Ceti's
  `map_sum_sq_uniformSphereMeasure` for the two real coordinates and Mathlib's complex polar
  coordinates. The branching dimension formula in `SFVK.Spheres.Branching` uses Tau Ceti's
  Fischer decomposition. Branch harmonicity and spanning use its
  `MvPolynomial.laplacian_normSq_mul` and `finrank_iSup_eq_sum_finrank_of_iSupIndep`.
- The motion-group circle model uses Mathlib's continuous-function density in `L²` and its
  Fourier coefficients on the additive circle. The Bessel formulas use lean-DLMF's Jacobi–Anger
  expansion, Graf addition theorem, and regularized hypergeometric series. The Fourier
  translation and rotation laws use Mathlib's `fourierIntegral_comp_add_right` and
  `fourier_comp_linearIsometry`.
- `SFVK.Spheres.SphereMeasure` uses Tau Ceti's special orthogonal orbit theorem,
  `LinearIsometryEquiv.map_toSphere`, and the symmetric beta density for sphere projections.
- The sphere zonal polynomials use Tau Ceti's harmonic dimension and Euclidean Laplacian formulas.
  Their product, bound, and orthogonality use lean-DLMF's Gegenbauer formulas and Mathlib's
  Chebyshev orthogonality.
- The radial Fourier transform uses Tau Ceti's polar integration and unit sphere area formulas.
  The angular transform uses Tau Ceti's complex-plane isometry and Mathlib's
  `Complex.integral_comp_polarCoord_symm`. The zonal Bessel sphere mean uses Tau Ceti's
  von Mises–Fisher normalizer, holomorphy of parameter
  integrals, and the Rademacher law for the two-point sphere. The zonal Bessel boundedness
  criterion uses lean-DLMF's `besselI_isEquivalent_sector`, and the Laguerre eigenfunction
  proof uses its `integral_laguerreExtended_hankel`.
- The hyperbola model uses Mathlib's continuous measure-preserving composition on `L²`, Tau Ceti's
  dominated convergence on `L²` and Fourier integrability for smooth compactly supported functions,
  and lean-DLMF's Bessel kernel integrability. The Bessel circle mean and matrix addition in
  `SFVK.MotionGroups.Miller` use Mathlib's `fourierCoeff_eq_of_hasSum`. The radial Bessel product
  uses its `integral_Icc_deriv_smul_of_deriv_nonpos`.
- The affine Mellin formulas use lean-DLMF's beta integral, Mellin–Barnes inversion,
  `integral_mul_eq_mellin_parseval`, and the vertical integrability of the Gamma kernel.
  The Charlier identities use its terminating series, duality, Laguerre finite sum, and
  discrete orthogonality. The signed Mellin kernel uses Tau Ceti's Mellin inversion and vertical
  decay, and its evaluations use lean-DLMF's Tricomi, Kummer and exponential Mellin integrals.
- The Schrödinger matrix elements use lean-DLMF's Hermite translation, product and Laplace
  transform formulas. The matrix addition theorem uses Mathlib's Hilbert-basis expansion.
  Matrix-element orthogonality uses Tau Ceti's Hermite Schwartz functions and Mathlib's
  Schwartz-space Plancherel identity.
- The `SU(1,1)` matrix-element proofs use lean-DLMF's Laplace formula for Legendre functions,
  binomial series, Gauss argument continuation, and compact-parameter holomorphy.
- `SFVK.RankOne.Jacobi` and `HarishChandra` use lean-DLMF's Gauss differential equation,
  transformations, boundary limits, and parameter holomorphy. The Jacobi transform uses
  DLMFMathlib's theorem for differentiating a locally dominated parameter integral.
  Hyperbolic polar integration and Laplacians use Mathlib's Haar-to-sphere and second-order
  chain-rule APIs. Horospherical integration uses its monotone change of variables and
  Haar measure scaling. Lorentz invariance uses Mathlib's
  `Measure.map_linearMap_addHaar_eq_smul_addHaar` and `iteratedDeriv_vcomp_two`.
  The Jacobi density bound uses Mathlib's Gamma duplication formula,
  lean-DLMF's vertical Stirling limit and Tau Ceti's derivative of reciprocal Gamma at its zeros.
