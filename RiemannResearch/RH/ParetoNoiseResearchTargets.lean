import RiemannResearch.RH.ParetoArithmeticRepair
import RiemannResearch.RH.ParetoNoiseSignal
import RiemannResearch.RH.ParetoHiddenNoise
import RiemannResearch.RH.ParetoGeometricTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Unproved analytic statements from the noise-to-signal report

Source: user-provided argument,
`RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, §§4–6 and 8.

Every declaration below is a proposition DEFINITION, not a proved theorem and
not an axiom. These statements preserve the principal remaining translation
obligations in a form that can be used in later proof work. No theorem in the
verified repair modules imports or assumes one of these propositions.

The smooth-gap input is a published theorem, but its Lean proof is absent.
The Bessel estimate is an open mathematical suggestion in the report itself.
These two statuses must not be conflated.
-/

open scoped BigOperators
open Filter MeasureTheory
namespace RiemannResearch.RH.Pareto.ResearchTargets
noncomputable section

/-- The published smooth-number input and the resulting analytic estimates
must be supplied before this existence statement is established in Lean. -/
def SummablePrimeRepairs : Prop :=
  ∃ E : ℕ → ℕ,
    (∀ p, p.Prime → 7 ≤ p →
      p < E p ∧ ∃ a b : ℕ, E p = 3^a * 5^b) ∧
    Tendsto (fun p : ℕ => (E p : ℝ) / (p : ℝ))
      (atTop ⊓ Filter.principal {p : ℕ | p.Prime}) (nhds 1) ∧
    Summable (fun p : {p : ℕ // p.Prime ∧ 7 ≤ p} =>
      paretoVariance (arithmeticRepair 2 p.val (E p.val)))

/-- Missing evaluation of the exact residue-four second moment. -/
def ResidueFourMoment : Prop :=
  paretoInner (residue 4) (residue 4) = 6 * Real.log 2 - Real.pi / 2

/-- The complete logarithmic growth claim; indices are actual odd integers. -/
def HiddenNoiseSecondMoment : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → n % 2 = 1 →
    |paretoInner (hiddenNoise n) (hiddenNoise n) - 2 * Real.log (n : ℝ)| ≤ C

/-- The first-moment estimate needed for the fixed-space gain calculation. -/
def HiddenNoiseFirstMoment : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n → n % 2 = 1 →
    |(n : ℝ) * paretoMean (fun k => |hiddenNoise n k|) -
      2 * Real.log (n : ℝ)| ≤ C

/-- Exact conditional-variance limit. `geometricTransform` is indexed from
zero, so the sequence is shifted to positive coordinates by `k+1`. -/
def HiddenNoiseConditionedLimit : Prop :=
  Tendsto (fun n : ℕ => (n : ℝ) *
    (∫ t : ℝ in Set.Ioc 0 1,
      (geometricTransform (fun k => hiddenNoise n (k+1)) t)^2))
    (atTop ⊓ Filter.principal {n : ℕ | n % 2 = 1})
    (nhds ((Real.pi^2 - 6) / 9))

/-- The suggested all-coefficient covariance bound is not proved in the PDF
and is deliberately not included in the established results. -/
def RepairBesselBound (E : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (a : ℕ → ℝ),
    (∀ p ∈ s, p.Prime ∧ 7 ≤ p) →
    paretoInner
      (fun k => ∑ p ∈ s, a p * arithmeticRepair 2 p (E p) k)
      (fun k => ∑ p ∈ s, a p * arithmeticRepair 2 p (E p) k) ≤
    C * ∑ p ∈ s, (a p)^2 *
      paretoInner (arithmeticRepair 2 p (E p)) (arithmeticRepair 2 p (E p))

end
end RiemannResearch.RH.Pareto.ResearchTargets
