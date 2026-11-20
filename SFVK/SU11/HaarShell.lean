/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.SU11.Basic.Coordinates
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.RingTheory.Norm.Transitivity

/-!
# A Haar measure on SU(1,1) from ambient Lebesgue measure

The first column of a complex matrix with conjugate-symmetric rows determines the other column.
Its determinant is the difference of the squared norms of its entries. Left multiplication by an
element of SU(1,1) preserves ambient Lebesgue measure and the determinant. Radial normalization of
the open determinant shell between zero and one gives a left Haar measure on the group.
The invariance calculation uses Mathlib's determinant formula for linear changes of variables
and its restriction-of-scalars formula for determinants.
-/

public noncomputable section

open Complex Matrix MeasureTheory Set
open scoped ComplexConjugate

namespace SFVK.SU11.HaarShell

/-- The determinant of the conjugate-symmetric matrix with first column z. -/
@[expose]
def ambientDeterminant (z : Fin 2 → ℂ) : ℝ := normSq (z 0) - normSq (z 1)

/-- The determinant of a first column is the difference of its squared norms. -/
theorem ambientDeterminant_def (z : Fin 2 → ℂ) :
    ambientDeterminant z = normSq (z 0) - normSq (z 1) := rfl

/-- The determinant of the conjugate-symmetric matrix varies continuously with its column. -/
theorem continuous_ambientDeterminant : Continuous ambientDeterminant := by
  unfold ambientDeterminant
  exact (continuous_normSq.comp (continuous_apply 0)).sub
    (continuous_normSq.comp (continuous_apply 1))

/-- The open determinant shell used for ambient Lebesgue disintegration. -/
@[expose]
def ambientShell : Set (Fin 2 → ℂ) := ambientDeterminant ⁻¹' Ioo 0 1

/-- A column belongs to the shell when its determinant lies strictly between zero and one. -/
theorem mem_ambientShell {z : Fin 2 → ℂ} :
    z ∈ ambientShell ↔ 0 < ambientDeterminant z ∧ ambientDeterminant z < 1 := Iff.rfl

/-- The open determinant shell is open in the space of complex columns. -/
theorem isOpen_ambientShell : IsOpen ambientShell :=
  isOpen_Ioo.preimage continuous_ambientDeterminant

/-- Normalization of a positive-determinant column yields determinant one. -/
private theorem ambientDeterminant_normalize (z : Fin 2 → ℂ) (h : 0 < ambientDeterminant z) :
    normSq (z 0 / (Real.sqrt (ambientDeterminant z) : ℂ)) -
      normSq (conj (z 1) / (Real.sqrt (ambientDeterminant z) : ℂ)) = 1 := by
  rw [Complex.normSq_div, Complex.normSq_div, Complex.normSq_conj, ← sub_div,
    Complex.normSq_ofReal, ← sq, Real.sq_sqrt h.le, ← ambientDeterminant_def, div_self h.ne']

/-- Divide the two coordinates by the positive square root of their determinant. The projection
outside the positive-determinant region is the identity element. -/
def ambientProject (z : Fin 2 → ℂ) : SU11 :=
  if h : 0 < ambientDeterminant z then
    ofPair (z 0 / (Real.sqrt (ambientDeterminant z) : ℂ))
      (conj (z 1) / (Real.sqrt (ambientDeterminant z) : ℂ))
      (ambientDeterminant_normalize z h)
  else 1

/-- On positive-determinant columns, the projection uses radial normalization. -/
private theorem ambientProject_of_pos (z : Fin 2 → ℂ) (h : 0 < ambientDeterminant z) :
    ambientProject z =
      ofPair (z 0 / (Real.sqrt (ambientDeterminant z) : ℂ))
        (conj (z 1) / (Real.sqrt (ambientDeterminant z) : ℂ))
        (ambientDeterminant_normalize z h) := by
  rw [ambientProject, dite_eq_left h]

/-- The diagonal entry of the normalized positive column. -/
theorem entryA_ambientProject (z : Fin 2 → ℂ) (h : 0 < ambientDeterminant z) :
    entryA (ambientProject z) = z 0 / (Real.sqrt (ambientDeterminant z) : ℂ) := by
  rw [ambientProject_of_pos z h, entryA_ofPair]

/-- The second upper entry of the normalized positive column. -/
theorem entryB_ambientProject (z : Fin 2 → ℂ) (h : 0 < ambientDeterminant z) :
    entryB (ambientProject z) = conj (z 1) / (Real.sqrt (ambientDeterminant z) : ℂ) := by
  rw [ambientProject_of_pos z h, entryB_ofPair]

/-- The pushforward of Lebesgue measure on the ambient shell under radial normalization. -/
@[expose]
def ambientShellMeasure : Measure SU11 := (volume.restrict ambientShell).map ambientProject

/-- The shell measure is a pushforward of restricted Lebesgue measure. -/
theorem ambientShellMeasure_def :
    ambientShellMeasure = (volume.restrict ambientShell).map ambientProject := rfl

/-- A column fills a matrix by conjugating and exchanging its entries for the second column. -/
private def columnMatrix (z : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z 0, conj (z 1); z 1, conj (z 0)]

/-- Reconstructing the conjugate-symmetric matrix is continuous. -/
private theorem continuous_columnMatrix : Continuous columnMatrix := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [columnMatrix] <;> fun_prop

/-- The reconstructed ambient matrix has the designated determinant. -/
private theorem det_columnMatrix (z : Fin 2 → ℂ) :
    (columnMatrix z).det = (ambientDeterminant z : ℂ) := by
  rw [columnMatrix, Matrix.det_fin_two_of, Complex.mul_conj,
    mul_comm (conj (z 1)), Complex.mul_conj, ambientDeterminant_def, Complex.ofReal_sub]

/-- The projected matrix is the radial multiple of the reconstructed ambient matrix. -/
private theorem coe_ambientProject (z : Fin 2 → ℂ) (h : 0 < ambientDeterminant z) :
    (ambientProject z).1.1 = ((Real.sqrt (ambientDeterminant z) : ℂ)⁻¹) • columnMatrix z := by
  rw [coe_eq_matrix, entryA_ambientProject z h, entryB_ambientProject z h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [columnMatrix, div_eq_mul_inv, mul_comm, Complex.conj_ofReal]

/-- The projection is continuous on the positive-determinant region. -/
private theorem continuousOn_ambientProject :
    ContinuousOn ambientProject {z | 0 < ambientDeterminant z} := by
  apply Topology.IsEmbedding.continuousOn_iff Topology.IsEmbedding.subtypeVal |>.mpr
  apply Topology.IsEmbedding.continuousOn_iff
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isEmbedding |>.mpr
  have hroot : Continuous fun z : Fin 2 → ℂ => (Real.sqrt (ambientDeterminant z) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_ambientDeterminant)
  have hinv : ContinuousOn (fun z : Fin 2 → ℂ => (Real.sqrt (ambientDeterminant z) : ℂ)⁻¹)
      {z | 0 < ambientDeterminant z} := by
    apply hroot.continuousOn.inv₀
    intro z hz
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos hz).ne'
  refine (hinv.smul continuous_columnMatrix.continuousOn).congr ?_
  intro z hz
  exact coe_ambientProject z hz

/-- Radial normalization is measurable on the ambient column space. -/
theorem measurable_ambientProject : Measurable ambientProject := by
  have hs : MeasurableSet {z | 0 < ambientDeterminant z} :=
    measurableSet_lt measurable_const continuous_ambientDeterminant.measurable
  refine measurable_of_restrict_of_restrict_compl hs
    (continuousOn_iff_continuous_domRestrict.mp continuousOn_ambientProject).measurable ?_
  have heq : ({z | 0 < ambientDeterminant z}ᶜ : Set (Fin 2 → ℂ)).domRestrict ambientProject =
      fun _ => (1 : SU11) := by
    funext z
    exact dite_eq_right (fun h => z.2 h)
  rw [heq]
  exact measurable_const

/-- Left multiplication on an ambient column is complex-linear. -/
private def ambientLeftMul (g : SU11) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  Matrix.toLin' g.1.1

/-- The matrix of the resulting column is the left-multiplied ambient matrix. -/
private theorem columnMatrix_ambientLeftMul (g : SU11) (z : Fin 2 → ℂ) :
    columnMatrix (ambientLeftMul g z) = g.1.1 * columnMatrix z := by
  rw [coe_eq_matrix g]
  simp only [ambientLeftMul, Matrix.toLin'_apply, coe_eq_matrix g]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [columnMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  all_goals ring

/-- Left multiplication preserves the ambient determinant. -/
private theorem ambientDeterminant_ambientLeftMul (g : SU11) (z : Fin 2 → ℂ) :
    ambientDeterminant (ambientLeftMul g z) = ambientDeterminant z := by
  apply Complex.ofReal_injective
  rw [← det_columnMatrix, ← det_columnMatrix, columnMatrix_ambientLeftMul,
    Matrix.det_mul, g.1.2, one_mul]

/-- Left multiplication has determinant one also as a real linear map. -/
private theorem det_ambientLeftMul_restrictScalars (g : SU11) :
    LinearMap.det ((ambientLeftMul g).restrictScalars ℝ) = 1 := by
  rw [LinearMap.det_restrictScalars, ambientLeftMul, LinearMap.det_toLin', g.1.2, map_one]

/-- The ambient complex-linear left multiplication preserves Lebesgue measure. -/
private theorem measurePreserving_ambientLeftMul (g : SU11) :
    MeasurePreserving (ambientLeftMul g) volume volume := by
  refine ⟨(ambientLeftMul g).continuous_of_finiteDimensional.measurable, ?_⟩
  have hdet := det_ambientLeftMul_restrictScalars g
  have hne := hdet ▸ (one_ne_zero : (1 : ℝ) ≠ 0)
  simpa only [hdet, inv_one, abs_one, ENNReal.ofReal_one, one_smul,
    LinearMap.coe_restrictScalars] using
    Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (Fin 2 → ℂ)) (f := (ambientLeftMul g).restrictScalars ℝ) hne

/-- The determinant shell is invariant under left multiplication. -/
private theorem preimage_ambientShell_ambientLeftMul (g : SU11) :
    (ambientLeftMul g) ⁻¹' ambientShell = ambientShell := by
  ext z
  simp only [mem_preimage, mem_ambientShell, ambientDeterminant_ambientLeftMul]

/-- On admissible columns, normalization intertwines ambient and group left multiplication. -/
private theorem ambientProject_ambientLeftMul (g : SU11) {z : Fin 2 → ℂ}
    (h : 0 < ambientDeterminant z) :
    ambientProject (ambientLeftMul g z) = g * ambientProject z := by
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_ambientProject _ ((ambientDeterminant_ambientLeftMul g z).symm ▸ h),
    ambientDeterminant_ambientLeftMul, columnMatrix_ambientLeftMul, coe_ambientProject z h,
    Matrix.mul_smul]

/-- The shell pushforward is left invariant. -/
private theorem map_mul_left_ambientShellMeasure (g : SU11) :
    Measure.map (g * ·) ambientShellMeasure = ambientShellMeasure := by
  rw [ambientShellMeasure_def, Measure.map_map (by fun_prop) measurable_ambientProject]
  have h := measurePreserving_ambientLeftMul g
  have hrestr := Measure.restrict_map h.measurable isOpen_ambientShell.measurableSet
    (μ := (volume : Measure (Fin 2 → ℂ)))
  rw [h.map_eq, preimage_ambientShell_ambientLeftMul] at hrestr
  nth_rw 2 [hrestr]
  rw [Measure.map_map measurable_ambientProject h.measurable]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem isOpen_ambientShell.measurableSet] with z hz
  exact (ambientProject_ambientLeftMul g (mem_ambientShell.mp hz).1).symm

/-- The first column of a group matrix, viewed as an ambient vector. -/
private def groupColumn (g : SU11) : Fin 2 → ℂ := fun i => g.1.1 i 0

/-- The group first column depends continuously on the matrix. -/
private theorem continuous_groupColumn : Continuous groupColumn := by
  have hg : Continuous (fun g : SU11 => g.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  unfold groupColumn
  exact continuous_pi fun i => (continuous_apply_apply i 0).comp hg

/-- The first coordinate of the group column is the diagonal entry. -/
private theorem groupColumn_first (g : SU11) : groupColumn g 0 = entryA g := rfl

/-- The second coordinate of the group column is the conjugate of the other upper entry. -/
private theorem groupColumn_second (g : SU11) : groupColumn g 1 = conj (entryB g) :=
  (mem_su11.mp g.2).1

/-- The group first column has ambient determinant one. -/
private theorem ambientDeterminant_groupColumn (g : SU11) :
    ambientDeterminant (groupColumn g) = 1 := by
  rw [ambientDeterminant_def, groupColumn_first, groupColumn_second, Complex.normSq_conj,
    normSq_entryA_sub_normSq_entryB]

/-- Rescaling a column multiplies its determinant by the square of the real scale. -/
private theorem ambientDeterminant_smul (r : ℝ) (z : Fin 2 → ℂ) :
    ambientDeterminant (r • z) = r ^ 2 * ambientDeterminant z := by
  simp only [ambientDeterminant_def, Pi.smul_apply, Complex.real_smul, Complex.normSq_mul,
    Complex.normSq_ofReal]
  ring

/-- The positive square root of the determinant recovers the scale of a projected column. -/
private theorem smul_groupColumn_ambientProject (z : Fin 2 → ℂ) (h : 0 < ambientDeterminant z) :
    Real.sqrt (ambientDeterminant z) • groupColumn (ambientProject z) = z := by
  have hr : ((Real.sqrt (ambientDeterminant z) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos_of_pos h).ne'
  apply funext
  rw [Fin.forall_fin_two]
  constructor
  · simp only [Pi.smul_apply, Complex.real_smul, groupColumn_first, entryA_ambientProject z h]
    field_simp
  · simp only [Pi.smul_apply, Complex.real_smul, groupColumn_second, entryB_ambientProject z h,
      map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    field_simp

/-- Positive scaling of a group column leaves its projection unchanged. -/
private theorem ambientProject_smul_groupColumn (g : SU11) {r : ℝ} (hr : 0 < r) :
    ambientProject (r • groupColumn g) = g := by
  have hrz : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hd : ambientDeterminant (r • groupColumn g) = r ^ 2 := by
    rw [ambientDeterminant_smul, ambientDeterminant_groupColumn, mul_one]
  have hpos : 0 < ambientDeterminant (r • groupColumn g) := hd ▸ sq_pos_of_pos hr
  have ha : entryA (ambientProject (r • groupColumn g)) = entryA g := by
    rw [entryA_ambientProject _ hpos, hd, Real.sqrt_sq hr.le]
    simp only [Pi.smul_apply, Complex.real_smul, groupColumn_first]
    field_simp
  have hb : entryB (ambientProject (r • groupColumn g)) = entryB g := by
    rw [entryB_ambientProject _ hpos, hd, Real.sqrt_sq hr.le]
    simp only [Pi.smul_apply, Complex.real_smul, groupColumn_second, map_mul, Complex.conj_ofReal,
      Complex.conj_conj]
    field_simp
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_eq_matrix (ambientProject (r • groupColumn g)), coe_eq_matrix g, ha, hb]

/-- The shell over a compact set is contained in the compact set of columns with bounded scale. -/
private theorem ambientShellMeasure_lt_top_of_isCompact {K : Set SU11} (hK : IsCompact K) :
    ambientShellMeasure K < ⊤ := by
  let scaled : ℝ × SU11 → (Fin 2 → ℂ) := fun p => p.1 • groupColumn p.2
  have hs : Continuous scaled :=
    continuous_fst.smul (continuous_groupColumn.comp continuous_snd)
  have hcompact : IsCompact (scaled '' (Icc 0 1 ×ˢ K)) :=
    (isCompact_Icc.prod hK).image hs
  rw [ambientShellMeasure_def,
    Measure.map_apply measurable_ambientProject hK.isClosed.measurableSet,
    Measure.restrict_apply (measurable_ambientProject hK.isClosed.measurableSet)]
  refine (measure_mono ?_).trans_lt hcompact.measure_lt_top
  rintro z ⟨hz, hzs⟩
  obtain ⟨hpos, hlt⟩ := mem_ambientShell.mp hzs
  exact ⟨(Real.sqrt (ambientDeterminant z), ambientProject z),
    ⟨⟨Real.sqrt_nonneg _, (Real.sqrt_le_one).mpr hlt.le⟩, hz⟩,
    smul_groupColumn_ambientProject z hpos⟩

/-- A nonempty open set contains the projection of some point in the open determinant shell. -/
private theorem ambientShellMeasure_ne_zero_of_isOpen {U : Set SU11} (hU : IsOpen U)
    (hne : U.Nonempty) : ambientShellMeasure U ≠ 0 := by
  obtain ⟨g, hg⟩ := hne
  let z := (1 / 2 : ℝ) • groupColumn g
  have hz : z ∈ ambientShell := by
    rw [mem_ambientShell, ambientDeterminant_smul, ambientDeterminant_groupColumn, mul_one]
    norm_num
  have hproj : ambientProject z = g := ambientProject_smul_groupColumn g (by norm_num)
  have hcont : ContinuousOn ambientProject ambientShell :=
    continuousOn_ambientProject.mono fun _ hz => (mem_ambientShell.mp hz).1
  rw [ambientShellMeasure_def, Measure.map_apply measurable_ambientProject hU.measurableSet,
    Measure.restrict_apply (measurable_ambientProject hU.measurableSet), inter_comm]
  exact (hcont.isOpen_inter_preimage isOpen_ambientShell hU).measure_ne_zero
    (volume : Measure (Fin 2 → ℂ)) ⟨z, hz, by rwa [mem_preimage, hproj]⟩

/-- Projecting the open determinant shell yields a left Haar measure on SU(1,1). -/
theorem isHaarMeasure_ambientShellMeasure : ambientShellMeasure.IsHaarMeasure where
  lt_top_of_isCompact _ hK := ambientShellMeasure_lt_top_of_isCompact hK
  map_mul_left_eq_self := map_mul_left_ambientShellMeasure
  open_pos _ := ambientShellMeasure_ne_zero_of_isOpen

/-- Complex conjugation preserves Lebesgue measure by reflecting the imaginary coordinate. -/
private theorem measurePreserving_conj : MeasurePreserving (conj : ℂ → ℂ) volume volume := by
  have hprod := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hcomp := Complex.volume_preserving_equiv_real_prod.symm.comp
    (hprod.comp Complex.volume_preserving_equiv_real_prod)
  convert hcomp using 1
  funext z
  apply Complex.ext <;> rfl

/-- The ambient inverse operation conjugates the first entry and negates the second. -/
private def ambientInversion (z : Fin 2 → ℂ) (i : Fin 2) : ℂ :=
  if i = 0 then conj (z i) else -z i

/-- The ambient inverse operation preserves Lebesgue measure coordinatewise. -/
private theorem measurePreserving_ambientInversion :
    MeasurePreserving ambientInversion volume volume := by
  apply volume_preserving_pi (f := fun (i : Fin 2) (w : ℂ) => if i = 0 then conj w else -w)
  intro i
  by_cases hi : i = 0
  · simpa only [ite_eq_left hi] using measurePreserving_conj
  · simpa only [ite_eq_right hi] using Measure.measurePreserving_neg (volume : Measure ℂ)

/-- The ambient inverse operation preserves the determinant. -/
private theorem ambientDeterminant_ambientInversion (z : Fin 2 → ℂ) :
    ambientDeterminant (ambientInversion z) = ambientDeterminant z := by
  simp [ambientDeterminant_def, ambientInversion, Complex.normSq_conj, Complex.normSq_neg]

/-- The determinant shell is invariant under the ambient inverse operation. -/
private theorem preimage_ambientShell_ambientInversion :
    ambientInversion ⁻¹' ambientShell = ambientShell := by
  ext z
  simp only [mem_preimage, mem_ambientShell, ambientDeterminant_ambientInversion]

/-- Projection intertwines the ambient inverse operation with inversion in SU(1,1). -/
private theorem ambientProject_ambientInversion (z : Fin 2 → ℂ) (h : 0 < ambientDeterminant z) :
    ambientProject (ambientInversion z) = (ambientProject z)⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  rw [Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv,
    coe_ambientProject _ (ambientDeterminant_ambientInversion z ▸ h), coe_ambientProject z h,
    ambientDeterminant_ambientInversion, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [columnMatrix, ambientInversion]

/-- The shell pushforward is inversion invariant. -/
theorem inv_ambientShellMeasure : ambientShellMeasure.inv = ambientShellMeasure := by
  rw [Measure.inv_def, ambientShellMeasure_def, Measure.map_map measurable_inv
    measurable_ambientProject]
  have hrestr := Measure.restrict_map measurePreserving_ambientInversion.measurable
    isOpen_ambientShell.measurableSet (μ := (volume : Measure (Fin 2 → ℂ)))
  rw [measurePreserving_ambientInversion.map_eq, preimage_ambientShell_ambientInversion] at hrestr
  nth_rw 2 [hrestr]
  rw [Measure.map_map measurable_ambientProject measurePreserving_ambientInversion.measurable]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem isOpen_ambientShell.measurableSet] with z hz
  exact (ambientProject_ambientInversion z (mem_ambientShell.mp hz).1).symm

/-- The shell pushforward is right invariant by left invariance and inversion. -/
theorem isMulRightInvariant_ambientShellMeasure : ambientShellMeasure.IsMulRightInvariant := by
  have := isHaarMeasure_ambientShellMeasure
  rw [← inv_ambientShellMeasure]
  infer_instance

end SFVK.SU11.HaarShell
