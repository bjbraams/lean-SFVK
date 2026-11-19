/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SFVK.SU2.Coordinates
public import SFVK.SU2.MatrixElements
public import DLMF.OrthogonalPolynomials.Basic.Definitions
public import DLMF.Legendre.Basic.Harmonics

/-!
# Wigner's small `d`-functions

The finite sum and Euler factorization follow Edmonds (4.1.12), p. 55, and (4.1.15),
p. 57. The Jacobi and Legendre forms are (4.1.23)–(4.1.26), pp. 58–59.
The Jacobi and Legendre functions use lean-DLMF's normalizations. In particular,
the associated Legendre form compensates for the Condon–Shortley phase of the Ferrers
function in lean-DLMF.
-/

public noncomputable section

open scoped Real

namespace SFVK.SU2

/-- Edmonds's finite binomial sum for the small `d`-function of spin `d/2`.
The totalized value for an index beyond `d` is zero. -/
def smallD (d i k : ℕ) (β : ℝ) : ℝ :=
  if i ≤ d ∧ k ≤ d then
    Real.sqrt ((i.factorial * (d - i).factorial : ℕ) / (k.factorial * (d - k).factorial : ℕ)) *
      ∑ s ∈ Finset.range (d - i + 1),
        ((k.choose (d - i - s) * (d - k).choose s : ℕ) : ℝ) * (-1) ^ (d - i - s) *
          Real.cos (β / 2) ^ (2 * s + i + k - d) * Real.sin (β / 2) ^ (2 * d - i - k - 2 * s)
  else 0

/-- The small `d`-function is zero when either weight index is out of range. -/
theorem smallD_eq_zero_of_out_of_range {d i k : ℕ} (h : d < i ∨ d < k) (β : ℝ) :
    smallD d i k β = 0 := by
  rcases h with h | h
  · simp [smallD, not_le.mpr h]
  · simp [smallD, not_le.mpr h]

/-- At spin zero the small `d`-function is constant. -/
@[simp]
theorem smallD_zero_zero_zero (β : ℝ) : smallD 0 0 0 β = 1 := by
  norm_num [smallD, Finset.sum_range_succ]

/-- The top-right entry of the spin one half middle factor is `sin (β/2)`. -/
theorem smallD_one_one_zero (β : ℝ) : smallD 1 1 0 β = Real.sin (β / 2) := by
  norm_num [smallD, Finset.sum_range_succ, Nat.factorial]

/-- The bottom-left entry of the spin one half middle factor is `-sin (β/2)`. -/
theorem smallD_one_zero_one (β : ℝ) : smallD 1 0 1 β = -Real.sin (β / 2) := by
  norm_num [smallD, Finset.sum_range_succ, Nat.factorial, Nat.choose]

/-- The zero-weight entry of spin one is the cosine of the middle angle. -/
theorem smallD_two_one_one (β : ℝ) : smallD 2 1 1 β = Real.cos β := by
  have h := Real.cos_two_mul' (β / 2)
  have hβ : 2 * (β / 2) = β := by ring
  rw [hβ] at h
  rw [h]
  norm_num [smallD, Finset.sum_range_succ, Nat.factorial, Nat.choose]
  ring

/-- The diagonal weight phases multiply the real small `d`-function in Euler coordinates. -/
theorem matrixElement_eulerD (d : ℕ) (i k : Fin (d + 1)) (α β γ : ℝ) :
    matrixElement d i k (eulerD α β γ) =
      Complex.exp (Complex.I * (edWeight d i * α)) * smallD d i k β *
        Complex.exp (Complex.I * (edWeight d k * γ)) := by
  sorry

/-- The Jacobi form at all real angles, with degree `r` and parameters `a, b`
determined by the two magnetic weights. -/
theorem smallD_eq_jacobi (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) (β : ℝ) :
    let a := Int.natAbs ((i : ℤ) - k)
    let b := Int.natAbs ((d : ℤ) - i - k)
    let r := min (min i k) (min (d - i) (d - k))
    (smallD d i k β : ℂ) =
      ((-1 : ℝ) ^ (k - i) *
        Real.sqrt ((r.factorial * (d - r).factorial : ℕ) /
          ((r + a).factorial * (r + b).factorial : ℕ)) *
        Real.sin (β / 2) ^ a * Real.cos (β / 2) ^ b : ℝ) *
        DLMF.OrthogonalPolynomials.jacobiPolynomialP a b r (Real.cos β) := by
  sorry

/-- At angles zero and π the entries reduce to the identity and signed reversal, respectively. -/
theorem smallD_zero_pi (d i k : ℕ) (hi : i ≤ d) (hk : k ≤ d) :
    smallD d i k 0 = (if i = k then 1 else 0) ∧
    smallD d i k π = (if i + k = d then (-1) ^ k else 0) := by
  sorry

/-- The zero-weight coefficient of integral spin is the Legendre polynomial of the cosine. -/
theorem smallD_two_mul_self (l : ℕ) (β : ℝ) :
    (smallD (2 * l) l l β : ℂ) = DLMF.OrthogonalPolynomials.legendrePolynomialP l (Real.cos β) := by
  sorry

/-- The column of weight zero in integral spin is given by the integer Ferrers function,
with the Condon–Shortley phase removed, on the polar-angle interval. -/
theorem smallD_eq_ferrers (l n : ℕ) (hn : n ≤ l) {β : ℝ} (hβ : β ∈ Set.Icc 0 π) :
    (smallD (2 * l) (l + n) l β : ℂ) =
      ((-1 : ℝ) ^ n * Real.sqrt ((l - n).factorial / (l + n).factorial) : ℝ) *
        DLMF.Legendre.ferrersPNat l n (Real.cos β) := by
  sorry

end SFVK.SU2
