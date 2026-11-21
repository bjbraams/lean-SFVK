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
  Fischer decomposition.
- The motion-group circle model uses Mathlib's continuous-function density in `L²` and its
  Fourier coefficients on the additive circle. The Bessel formulas use lean-DLMF's Jacobi–Anger
  expansion, Graf addition theorem, and regularized hypergeometric series. The Fourier
  translation and rotation laws use Mathlib's `fourierIntegral_comp_add_right` and
  `fourier_comp_linearIsometry`.
- `SFVK.Spheres.SphereMeasure` uses Tau Ceti's special orthogonal orbit theorem,
  `LinearIsometryEquiv.map_toSphere`, and the symmetric beta density for sphere projections.
- The affine Mellin formulas use lean-DLMF's beta integral and Mellin–Barnes inversion. The
  Charlier identities use its terminating series, duality, and Laguerre finite sum.
- The `SU(1,1)` matrix-element proofs use lean-DLMF's Laplace formula for Legendre functions,
  binomial series, Gauss argument continuation, and compact-parameter holomorphy.
- `SFVK.RankOne.Jacobi` and `HarishChandra` use lean-DLMF's Gauss differential equation,
  transformations, boundary limits, and parameter holomorphy. The Jacobi transform uses
  DLMFMathlib's theorem for differentiating a locally dominated parameter integral.
  Hyperbolic polar integration and Laplacians use Mathlib's Haar-to-sphere and second-order
  chain-rule APIs.
