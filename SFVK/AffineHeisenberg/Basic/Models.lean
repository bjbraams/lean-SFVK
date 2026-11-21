/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.RepresentationTheory.Continuous.Unitary.Basic
public import SFVKMathlib.MeasureTheory.Group.MultiplierRepresentation
public import SFVK.AffineHeisenberg.Basic.Groups

/-!
# Models of the affine, triangular, Heisenberg and oscillator groups

Pointwise operators, multipliers, kernels and the `L²` representations of the roadmap
`Roadmaps/AffineHeisenbergGroups/README.md` (section numbers `§x.y`):

* `affineAction`: Vilenkin–Klimyk's `R_λ(a, b) f(x) = e^{λbx} f(ax)` (Vol. 1, §3.4.1 (1), p. 128),
  and `affineGammaKernel` its Mellin kernel (§3.4.3 (2), p. 131);
* `triangularAction`, `triangularRep`: the representations `T_χ` of the triangular group
  (Vol. 1, §5.1.2, pp. 208–209), `signedMellin` and `triangularKernel` (§5.1.3 (1)–(5),
  pp. 209–210);
* `schrodinger`: the Schrödinger representation `(U(g) f)(u) = e^{i(z + yu)} f(u + x)` of Tau
  Ceti's Heisenberg group, with its action on the line as a scoped instance;
* `fockMeasure`, `fockMonomial`, `fockSpace`, `bargmannKernel`: the Fock model (Miller, *Lie
  Theory and Special Functions*, §4-13, pp. 117–118; Vilenkin–Klimyk Vol. 2, §12.1.7,
  pp. 418–420);
* `oscillatorFock`: the oscillator representations on the Fock space (Miller §4-14 (4.119),
  p. 121);
* `millerAction`, `millerMatrixElement`: Miller's representations of `G(0, 1)` on entire
  functions and their matrix elements as finite sums (§4-2 (4.19), (4.24), pp. 86–87);
* `charlier`: the Charlier polynomials as `₂F₀(-n, -x; ; -1/a)`.

Representations on `L²` are the continuous representation agreeing almost everywhere with the
pointwise formula when one exists, and the trivial representation otherwise
(`MulAction.multiplierRepresentation`); their existence is a theorem-layer target. Everything here is fully proved.
-/

@[expose] public section

noncomputable section

namespace SFVK.AffineHeisenberg

open MeasureTheory Set Complex MulAction
open scoped Real ComplexConjugate InnerProductSpace ENNReal

/-- The invariant measure `dx / x`. -/
def halfLineMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity fun x => ENNReal.ofReal x⁻¹

/-- The multiplier `e^{i λ b x}`. -/
def axbCocycle (lam : ℝ) (g : AxB) (x : ℝ) : ℂ := Complex.exp ((lam * g.b * x : ℝ) * Complex.I)

/-- `g • x = x - g.x`. -/
scoped instance : MulAction (TauCeti.HeisenbergGroup ℝ) ℝ where
  smul g x := x - g.x
  one_smul x := sub_zero x
  mul_smul g h x := by
    show x - (g.x + h.x) = x - h.x - g.x
    ring

/-- The Schrödinger multiplier `e^{i(z + y x)}`. -/
def schrodingerCocycle (g : TauCeti.HeisenbergGroup ℝ) (x : ℝ) : ℂ :=
  Complex.exp ((g.z + g.y * x : ℝ) * Complex.I)

/-- The Schrödinger representation. -/
def schrodinger :
    ContRepresentation ℂ (TauCeti.HeisenbergGroup ℝ) (Lp ℂ 2 (volume : Measure ℝ)) :=
  multiplierRepresentation volume schrodingerCocycle

/-- §1.1. Vilenkin–Klimyk's `R_λ(a, b) f(x) = e^{λ b x} f(a x)` for complex `λ`. -/
def affineAction (lam : ℂ) (g : AxB) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  Complex.exp (lam * g.b * x) * f (g.a * x)

/-- §1.2. The Gamma kernel `Γ(w - z) a^{-w} (-λb/a)^{z-w} / (2πi)`. -/
def affineGammaKernel (lam : ℂ) (a b : ℝ) (w z : ℂ) : ℂ :=
  Gamma (w - z) * (a : ℂ) ^ (-w) * (-lam * b / a) ^ (z - w) / (2 * π * Complex.I)

/-- §2.1. The multiplier `e^{ωτ + σ(dx + b)}`. -/
def triangularCocycle (σ ω : ℂ) (g : TriangularGroup) (x : ℝ) : ℂ :=
  Complex.exp (ω * g.τ + σ * (g.d * x + g.b))

/-- §2.1. `(T_χ(g) f)(x) = e^{ωτ + σ(dx + b)} f(e^τ x + a)`. -/
def triangularAction (σ ω : ℂ) (g : TriangularGroup) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  triangularCocycle σ ω g x * f (Real.exp g.τ * x + g.a)

/-- §2.1. The unitary representation at `σ = iγ`, `ω = 1/2 + iρ`. -/
def triangularRep (γ ρ : ℝ) : ContRepresentation ℂ TriangularGroup (Lp ℂ 2 (volume : Measure ℝ)) :=
  multiplierRepresentation volume (triangularCocycle (γ * Complex.I) (1 / 2 + ρ * Complex.I))

/-- §2.3. The signed Mellin transforms `F_±(λ) = ∫_0^∞ x^{λ-1} f(±x) dx`. -/
def signedMellin (f : ℝ → ℂ) (ε : ℤˣ) (lam : ℂ) : ℂ :=
  mellin (fun x => f (((ε : ℤ) : ℝ) * x)) lam

/-- §2.3. The matrix kernel `K_{εη}(λ, μ; χ, g)`: `e^{ωτ + σb}/(2πi)` times the integral of
`x^{λ-1} e^{σ d ε x} |e^τ ε x + a|^{-μ}` over the `x > 0` with `η(e^τ ε x + a) > 0`. -/
def triangularKernel (σ ω : ℂ) (ε η : ℤˣ) (lam μ : ℂ) (g : TriangularGroup) : ℂ :=
  Complex.exp (ω * g.τ + σ * g.b) / (2 * π * Complex.I) *
    ∫ x in Ioi (0 : ℝ) ∩ {x | 0 < ((η : ℤ) : ℝ) * (Real.exp g.τ * ((ε : ℤ) : ℝ) * x + g.a)},
      (x : ℂ) ^ (lam - 1) * Complex.exp (σ * g.d * ((ε : ℤ) : ℂ) * x) *
        ((|Real.exp g.τ * ((ε : ℤ) : ℝ) * x + g.a| : ℝ) : ℂ) ^ (-μ)

/-- §3.3. The Charlier polynomial `cₙ(x; a) = ∑_{j ≤ n} C(n, j) (-1/a)^j x(x-1)⋯(x-j+1)`,
the `₂F₀(-n, -x; ; -1/a)` of DLMF 18.20.8; the junk value at `a = 0` is `1`. -/
def charlier (a : ℝ) (n : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    Polynomial.C ((n.choose j : ℝ) * (-a⁻¹) ^ j) * descPochhammer ℝ j

/-- §3.4. The Fock measure `π⁻¹ e^{-|ζ|²} dζ`. -/
def fockMeasure : Measure ℂ :=
  volume.withDensity fun ζ => ENNReal.ofReal (π⁻¹ * Real.exp (-‖ζ‖ ^ 2))

open scoped Classical in
/-- §3.4. The Fock basis vector `ζⁿ / √n!`, and `0` if it is not square integrable. -/
def fockMonomial (n : ℕ) : Lp ℂ 2 fockMeasure :=
  if h : MemLp (fun ζ : ℂ => ζ ^ n / (Real.sqrt n.factorial : ℂ)) 2 fockMeasure then h.toLp _
  else 0

/-- §3.4. The Fock space: the closed span of the `fockMonomial n`. -/
def fockSpace : Submodule ℂ (Lp ℂ 2 fockMeasure) :=
  (Submodule.span ℂ (Set.range fockMonomial)).topologicalClosure

/-- §3.4. The Bargmann kernel `π^{-1/4} exp(-ζ²/2 + √2 ζ u - u²/2)`. -/
def bargmannKernel (ζ : ℂ) (u : ℝ) : ℂ :=
  ((π ^ (-(1 / 4 : ℝ)) : ℝ) : ℂ) *
    Complex.exp (-ζ ^ 2 / 2 + (Real.sqrt 2 : ℂ) * ζ * u - (u : ℂ) ^ 2 / 2)

/-- §3.4. The Heisenberg group on functions on `ℂ`:
`e^{i(z - xy/2)} e^{-|w|²/4 - conj w ζ/√2} F(ζ + w/√2)` with `w = x + iy`. -/
def fockHeisenbergAction (p : TauCeti.HeisenbergGroup ℝ) (F : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  let w : ℂ := ⟨p.x, p.y⟩
  Complex.exp ((p.z - p.x * p.y / 2 : ℝ) * Complex.I) *
    Complex.exp (-(‖w‖ ^ 2 / 4 : ℝ) - conj w * ζ / (Real.sqrt 2 : ℂ)) *
      F (ζ + w / (Real.sqrt 2 : ℂ))

/-- §4.1. The multiplier `e^{iλα - 2iδ} e^{-|w|²/4 - conj w ζ/√2}`. -/
def oscillatorCocycle (lam : ℝ) (g : Oscillator) (ζ : ℂ) : ℂ :=
  Complex.exp ((lam * g.α - 2 * g.δ : ℝ) * Complex.I) *
    Complex.exp (-(‖g.w‖ ^ 2 / 4 : ℝ) - conj g.w * ζ / (Real.sqrt 2 : ℂ))

/-- §4.1. The oscillator representation on `L²(fockMeasure)`. -/
def oscillatorFock (lam : ℝ) : ContRepresentation ℂ Oscillator (Lp ℂ 2 fockMeasure) :=
  multiplierRepresentation fockMeasure (oscillatorCocycle lam)

/-- §5.1. Miller's operators `e^{μ(bz + a) - ωτ} f(e^τ z + e^τ c)` (Miller (4.19)). -/
def millerAction (μ ω : ℂ) (g : MillerGroup) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (μ * (g.b * z + g.a) - ω * g.τ) * f (Complex.exp g.τ * z + Complex.exp g.τ * g.c)

/-- §5.1. Miller's matrix element `B_{lk}(g)` as the finite sum (4.24). -/
def millerMatrixElement (μ ω : ℂ) (l k : ℕ) (g : MillerGroup) : ℂ :=
  Complex.exp (μ * g.a + (k - ω) * g.τ) *
    ∑ s ∈ Finset.range (min k l + 1),
      (k.choose s : ℂ) * g.c ^ (k - s) * (μ * g.b) ^ (l - s) / (l - s).factorial

end SFVK.AffineHeisenberg
