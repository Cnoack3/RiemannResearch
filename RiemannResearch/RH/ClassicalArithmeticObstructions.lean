import RiemannResearch.RH.ChebyshevEnergyHardy
import RiemannResearch.RH.ChebyshevMellinRH
import RiemannResearch.RH.DyadicFourierAnalyticTargets
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Concrete classical consequences of an off-line zero: formalization targets

Source: user-provided 2026-09-21 catalogue, groups 28 and 33--35. The Mellin
pole order and finite-energy monotonicity have existing proved providers.
The prime/Mertens oscillation, boundary residue, endpoint-energy divergence,
Robin, and Lagarias propositions below are OPEN proof obligations, not axioms.

The Robin/Lagarias targets follow the statements discussed by J. C. Lagarias,
An Elementary Problem Equivalent to the Riemann Hypothesis,
https://arxiv.org/abs/math/0008177 (Theorem 1.1 and Proposition 3.2).
This citation supports the intended mathematical statements, not a Lean proof.

All arithmetic functions are concrete. Nonintegrability is expressed using
IntegrableOn: the default Bochner integral of a nonintegrable function is not
mistaken for an infinite real value. Every tail cutoff is explicitly quantified.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.ClassicalObstruction

def RightZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ (1 / 2 : ℝ) < ρ.re ∧ ρ.re < 1

def primeCountingError (x : ℝ) : ℝ :=
  (Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹

/-- The normalized ratio is unbounded on every tail, without Big-O notation. -/
def PowerLogTailUnbounded (f : ℝ → ℝ) (c B : ℝ) : Prop :=
  ∀ C X : ℝ, 0 < C → 1 < X →
    ∃ x : ℝ, X < x ∧ C * x ^ c * (Real.log x) ^ B < |f x|

/-- Group 33: all four concrete errors exceed every smaller power/log envelope. -/
def ArithmeticEnvelopeFailureTarget : Prop :=
  ∀ ρ : ℂ, RightZero ρ → ∀ c B : ℝ, (1 / 2 : ℝ) < c → c < ρ.re →
    PowerLogTailUnbounded Pareto.classicalMertensFunction c B ∧
    PowerLogTailUnbounded (fun x => Chebyshev.psi x - x) c B ∧
    PowerLogTailUnbounded (fun x => Chebyshev.theta x - x) c B ∧
    PowerLogTailUnbounded primeCountingError c B

/-- Group 33: failure of square integrability including the boundary c = Re ρ. -/
def ArithmeticBoundaryEnergyDivergenceTarget : Prop :=
  ∀ ρ : ℂ, RightZero ρ → ∀ c X : ℝ, c ≤ ρ.re → 1 < X →
    (¬ IntegrableOn (fun x : ℝ =>
      Pareto.classicalMertensFunction x ^ 2 * x ^ (-2 * c - 1)) (Ioi X)) ∧
    (¬ IntegrableOn (fun x : ℝ =>
      (Chebyshev.psi x - x) ^ 2 * x ^ (-2 * c - 1)) (Ioi X))

/-- The claimed residue coefficient, beyond the already proved pole order. -/
def ChebyshevZeroResidueTarget : Prop :=
  ∀ ρ : ℂ, RightZero ρ → ∀ m : ℕ, 0 < m →
    analyticOrderAt riemannZeta ρ = (m : ℕ∞) →
    Tendsto (fun z : ℂ => (z - ρ) * ChebyshevMellin.meromorphicError z)
      (𝓝[≠] ρ) (𝓝 (-(m : ℂ) / ρ))

/-- Endpoint lower excursions with the actual multiplicity and zeta derivative. -/
def ArithmeticBoundaryExcursionTarget : Prop :=
  ∀ ρ : ℂ, RightZero ρ → ∀ m : ℕ, 0 < m →
    analyticOrderAt riemannZeta ρ = (m : ℕ∞) →
    (∀ L X : ℝ, L < (m : ℝ) / ‖ρ‖ → 1 < X →
      ∃ x : ℝ, X < x ∧ L * x ^ ρ.re < |Chebyshev.psi x - x|) ∧
    (∀ L X : ℝ, L < (m : ℝ) / (‖ρ‖ * ‖iteratedDeriv m riemannZeta ρ‖) →
      1 < X → ∃ x : ℝ, X < x ∧
        L * x ^ ρ.re * (Real.log x) ^ (m - 1) < |Pareto.classicalMertensFunction x|)

/-- Increasing damping preserves actual Chebyshev square integrability. -/
theorem errorFiniteEnergy_mono {s t : ℝ}
    (hs : ChebyshevMellin.ErrorFiniteEnergy s) (hst : s ≤ t) :
    ChebyshevMellin.ErrorFiniteEnergy t := by
  have h := (MeasureTheory.WeightedMellin.finiteEnergy_mono
    (ChebyshevMellin.error_finiteEnergy hs) hst).2
  simpa only [ChebyshevMellin.ErrorFiniteEnergy, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

/-- An endpoint obstruction propagates to every smaller damping; the endpoint
itself still needs a provider and is not inferred from open-half-plane holomorphy. -/
theorem not_errorFiniteEnergy_of_le {s t : ℝ}
    (ht : ¬ ChebyshevMellin.ErrorFiniteEnergy t) (hst : s ≤ t) :
    ¬ ChebyshevMellin.ErrorFiniteEnergy s := by
  intro hs
  exact ht (errorFiniteEnergy_mono hs hst)

def divisorSum (n : ℕ) : ℝ := ∑ d ∈ n.divisors, (d : ℝ)

def robinBaseline (n : ℕ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)

def lagariasBaseline (n : ℕ) : ℝ :=
  (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

/-- Quantitative Robin violations at arbitrarily large integers. -/
def RobinQuantitativeViolationsTarget : Prop :=
  ∀ ρ : ℂ, RightZero ρ → ∀ b : ℝ, 1 - ρ.re < b → b < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N < n ∧ 3 ≤ n ∧
      robinBaseline n + c * n * Real.log (Real.log n) / (Real.log n) ^ b ≤
        divisorSum n

/-- Infinitely many, not merely one, actual Lagarias violations. -/
def LagariasInfiniteViolationsTarget : Prop :=
  ¬ RiemannHypothesis → ∀ N : ℕ, ∃ n : ℕ,
    N < n ∧ 1 ≤ n ∧ lagariasBaseline n < divisorSum n

end RiemannResearch.RH.ClassicalObstruction
