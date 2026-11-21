/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SFVK.ClebschGordan.Basic.Coupling
public import SFVK.ClebschGordan.Basic.SixJ
public import SFVK.SU2.Basic.MatrixElements
public import TauCeti.RepresentationTheory.Continuous.TensorProduct
public import TauCeti.RepresentationTheory.Compact.SchurOrthogonality
import TauCeti.RepresentationTheory.SU2.TorusConjugacy

/-!
# The coupled basis and products of matrix elements

Layers 1.3 and 2 of the roadmap ClebschGordan. The spin `d/2` representation is the unitary
model `SFVK.SU2.unitaryModel d`, with matrix elements `SFVK.SU2.matrixElement`; the tensor
product is Tau Ceti's `ContRepresentation.tprod`. The character identity uses Tau Ceti's
character transport, torus conjugacy, and symmetric-power torus weight formula.

Locators: Edmonds, *Angular Momentum in Quantum Mechanics*, (3.4.1)–(3.4.2), pp. 36–37;
(3.5.1)–(3.5.3), pp. 37–38; (4.3.1), p. 60; (4.6.2), p. 62. Wawrzyńczyk, *Group Representations
and Special Functions*, (8.7.2), p. 305; (8.7.7), p. 306. Vilenkin–Klimyk, *Representation of
Lie Groups and Special Functions*, Vol. 1, §8.1.3, pp. 501–503.
-/

public noncomputable section

open scoped TensorProduct InnerProductSpace ComplexOrder
open TauCeti SFVK.SU2 MeasureTheory

namespace SFVK.ClebschGordan

/-! ### The coupled basis -/

/-- **The coupled vectors transform as the standard basis of spin `j`:**
`(T^{j₁} ⊗ T^{j₂})(g) w_{jm} = Σ_{m'} D^j_{m'm}(g) w_{jm'}`. -/
theorem tprod_coupledVector {d₁ d₂ d : ℕ} (h : IsTriad d₁ d₂ d) (g : TauCeti.SU2)
    (i : Fin (d + 1)) :
    ContRepresentation.tprod (unitaryModel d₁) (unitaryModel d₂) g (coupledVector d₁ d₂ d i) =
      ∑ k : Fin (d + 1), matrixElement d k i g • coupledVector d₁ d₂ d k := by
  sorry

/-- **The coupled vectors are orthonormal** (Edmonds (3.5.3), p. 38). -/
theorem inner_coupledVector {d₁ d₂ d d' : ℕ} (h : IsTriad d₁ d₂ d) (h' : IsTriad d₁ d₂ d')
    (i : Fin (d + 1)) (i' : Fin (d' + 1)) :
    ⟪coupledVector d₁ d₂ d i, coupledVector d₁ d₂ d' i'⟫_ℂ =
      if d = d' ∧ (i : ℕ) = i' then 1 else 0 := by
  sorry

/-- **The coupled vectors span the tensor product** (Edmonds (3.5.2), p. 37). -/
theorem span_coupledVector (d₁ d₂ : ℕ) :
    Submodule.span ℂ {v | ∃ (d : ℕ) (i : Fin (d + 1)), IsTriad d₁ d₂ d ∧
      v = coupledVector d₁ d₂ d i} = ⊤ := by
  sorry

/-- **Uniqueness of the coupled basis** (the phase conventions (3.4.1)–(3.4.2) of Edmonds,
pp. 36–37). A family transforming as the standard basis of spin `j`, whose top vector is a unit
vector with a positive component along `e_{j₁} ⊗ e_{j - j₁}`, is the coupled basis. -/
theorem eq_coupledVector_of_tprod {d₁ d₂ d : ℕ} (h : IsTriad d₁ d₂ d)
    (v : Fin (d + 1) → EuclideanSpace ℂ (Fin (d₁ + 1)) ⊗[ℂ] EuclideanSpace ℂ (Fin (d₂ + 1)))
    (hv : ∀ (g : TauCeti.SU2) (k : Fin (d + 1)),
      ContRepresentation.tprod (unitaryModel d₁) (unitaryModel d₂) g (v k) =
        ∑ k' : Fin (d + 1), matrixElement d k' k g • v k')
    (hn : ‖v (Fin.last d)‖ = 1)
    (hp : 0 < ⟪EuclideanSpace.single (Fin.last d₁) (1 : ℂ) ⊗ₜ[ℂ]
        EuclideanSpace.single (⟨(d + d₂ - d₁) / 2, by have := h.1; omega⟩ : Fin (d₂ + 1)) 1,
      v (Fin.last d)⟫_ℂ) (k : Fin (d + 1)) :
    v k = coupledVector d₁ d₂ d k := by
  sorry

/-! ### Products of matrix elements -/

/-- **The product of two matrix elements** (Edmonds (4.3.1), p. 60; Wawrzyńczyk (8.7.7),
p. 306). -/
theorem matrixElement_mul_matrixElement (d₁ d₂ : ℕ) (a₁ b₁ : Fin (d₁ + 1))
    (a₂ b₂ : Fin (d₂ + 1)) (g : TauCeti.SU2) :
    matrixElement d₁ a₁ b₁ g * matrixElement d₂ a₂ b₂ g =
      ∑ d ∈ Finset.range (d₁ + d₂ + 1), ∑ k : Fin (d + 1), ∑ l : Fin (d + 1),
        (clebschGordan d₁ d₂ d a₁ a₂ k * clebschGordan d₁ d₂ d b₁ b₂ l : ℝ) *
          matrixElement d k l g := by
  sorry

namespace Characters

/-- The diagonal matrix-element sum is the symmetric-power character. -/
private theorem sum_matrixElement_diagonal (d : ℕ) (g : SU2) :
    ∑ i, matrixElement d i i g = (TauCeti.SU2.symPower d).character g := by
  calc
    _ = ContRepresentation.character (unitaryModel d) (continuous_unitaryModel d) g := by
      rw [ContRepresentation.character_apply_eq_sum_inner _ _
        (EuclideanSpace.basisFun (Fin (d + 1)) ℂ)]
      simp only [EuclideanSpace.basisFun_apply, matrixElement_def]
    _ = _ := by
      have h := ContinuousLinearEquiv.character_congr (monomialScale d)
        (π := TauCeti.SU2.symPowerModel d) (continuous_unitaryModel d)
      rw [← TauCeti.SU2.symPowerCharacter_apply]
      exact congrFun (congrArg DFunLike.coe (h.trans (TauCeti.SU2.character_symPowerModel d))) g

/-- Reindex a pair of weights by the amount of spin removed and its new weight index. -/
private theorem sum_torus_weights (d₁ d₂ : ℕ) (z : ℂ) (hz : z ≠ 0) :
    (∑ i ∈ Finset.range (d₁ + 1), z ^ (2 * (i : ℤ) - d₁)) *
        (∑ j ∈ Finset.range (d₂ + 1), z ^ (2 * (j : ℤ) - d₂)) =
      ∑ d ∈ (Finset.range (d₁ + d₂ + 1)).filter (IsTriad d₁ d₂),
        ∑ i ∈ Finset.range (d + 1), z ^ (2 * (i : ℤ) - d) := by
  let F : ℕ × ℕ → (Σ _ : ℕ, ℕ) := fun p =>
    let k := min p.2 (d₁ - p.1)
    ⟨d₁ + d₂ - 2 * k, p.1 + p.2 - k⟩
  let G : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun q =>
    let k := (d₁ + d₂ - q.1) / 2
    let i := min q.2 (d₁ - k)
    (i, q.2 + k - i)
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_product', Finset.sum_sigma']
  refine Finset.sum_nbij' F G ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    simp only [F, Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, isTriad_def]
    refine ⟨⟨by omega, by omega, by omega, by omega, ?_⟩, by omega⟩
    exact ⟨d₁ + d₂ - min p.2 (d₁ - p.1), by omega⟩
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, isTriad_def] at hq
    simp only [G, Finset.mem_product, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    dsimp only [F, G]
    apply Prod.ext
    · omega
    · omega
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, isTriad_def] at hq
    obtain ⟨⟨_, hd, ha, hb, ⟨t, ht⟩⟩, hi⟩ := hq
    dsimp only [F, G]
    apply Sigma.ext
    · dsimp only
      omega
    · apply heq_of_eq
      dsimp only
      omega
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp
    rw [← zpow_add₀ hz]
    congr 1
    dsimp only [F]
    omega

end Characters

open Characters in
/-- **The Clebsch–Gordan series of characters** (Wawrzyńczyk (8.7.2), p. 305). -/
theorem character_mul_character (d₁ d₂ : ℕ) (g : TauCeti.SU2) :
    (∑ i, matrixElement d₁ i i g) * (∑ i, matrixElement d₂ i i g) =
      ∑ d ∈ (Finset.range (d₁ + d₂ + 1)).filter (IsTriad d₁ d₂), ∑ i : Fin (d + 1),
        matrixElement d i i g := by
  simp_rw [sum_matrixElement_diagonal]
  obtain ⟨z, hz⟩ := TauCeti.SU2.exists_isConj_torusHom g
  obtain ⟨u, hu⟩ := isConj_iff.mp hz
  have hc (d : ℕ) : (TauCeti.SU2.symPower d).character g =
      (TauCeti.SU2.symPower d).character (TauCeti.SU2.torusHom z) := by
    rw [← hu, Representation.char_conj]
  simp_rw [hc, TauCeti.SU2.character_symPower_torusHom_zpow]
  exact sum_torus_weights d₁ d₂ z z.coe_ne_zero

/-- **The integral of three matrix elements** (Edmonds (4.6.2), p. 62), for the Haar
probability measure. -/
theorem integral_matrixElement_mul_mul (d₁ d₂ d₃ : ℕ) (a₁ b₁ : Fin (d₁ + 1))
    (a₂ b₂ : Fin (d₂ + 1)) (a₃ b₃ : Fin (d₃ + 1)) :
    ∫ g, matrixElement d₁ a₁ b₁ g * matrixElement d₂ a₂ b₂ g * matrixElement d₃ a₃ b₃ g
        ∂haarProb TauCeti.SU2 =
      ((threeJ d₁ d₂ d₃ a₁ a₂ a₃ * threeJ d₁ d₂ d₃ b₁ b₂ b₃ : ℝ) : ℂ) := by
  sorry

/-! ### Recoupling -/

/-- **The recoupling coefficient does not depend on `M`** (Edmonds, §6.1): both coupled vectors
of three spins transform as `e_M`. -/
theorem recouplingCoefficient_eq_of_le {d₁ d₂ d₃ d₁₂ d₂₃ D I I' : ℕ} (h₁₂ : IsTriad d₁ d₂ d₁₂)
    (h₁₂₃ : IsTriad d₁₂ d₃ D) (h₂₃ : IsTriad d₂ d₃ d₂₃) (h₁₂₃' : IsTriad d₁ d₂₃ D)
    (hI : I ≤ D) (hI' : I' ≤ D) :
    recouplingCoefficient d₁ d₂ d₃ d₁₂ d₂₃ D I = recouplingCoefficient d₁ d₂ d₃ d₁₂ d₂₃ D I' := by
  sorry

end SFVK.ClebschGordan
