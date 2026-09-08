import RiemannResearch.RH.ParetoResidueMoments
import RiemannResearch.RH.ParetoHiddenNoiseAsymptotics
import RiemannResearch.RH.ParetoArithmeticRepair
import RiemannResearch.RH.ParetoNoiseSignal
import RiemannResearch.RH.ParetoHiddenNoise
import RiemannResearch.RH.ParetoGeometricTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Analytic statements and proved providers from the noise-to-signal report

Source: user-provided argument,
`RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, §§4–6 and 8.

The proposition definitions record the original targets. The residue-four and
both hidden-noise moment targets have unconditional proved providers below.
The conditioned limit is proved in ParetoHiddenConditioningVerified. The
summability target is reduced to the quantitative smooth-gap theorem in
Smooth35RepairCompletion. None of these propositions is a project axiom.

The smooth-gap input is a published theorem, but its Lean proof is absent.
The Bessel estimate was an open suggestion in the report. It is now disproved
for the actual least-smooth scale choice in ParetoBesselSmoothObstruction,
without the quantitative gap input. This negative result does not contradict
any theorem claimed proved in the report.
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

/-- The exact residue-four second moment, with its proved provider below. -/
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

/-- The original suggested all-coefficient covariance bound. Its negation for
the actual least-smooth scale choice is proved in ParetoBesselSmoothObstruction.
The parameterized proposition remains useful for stating that precise result. -/
def RepairBesselBound (E : ℕ → ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ) (a : ℕ → ℝ),
    (∀ p ∈ s, p.Prime ∧ 7 ≤ p) →
    paretoInner
      (fun k => ∑ p ∈ s, a p * arithmeticRepair 2 p (E p) k)
      (fun k => ∑ p ∈ s, a p * arithmeticRepair 2 p (E p) k) ≤
    C * ∑ p ∈ s, (a p)^2 *
      paretoInner (arithmeticRepair 2 p (E p)) (arithmeticRepair 2 p (E p))

/-- Complete infinite-sum evaluation, including the digamma-series proof. -/
theorem residueFourMoment : ResidueFourMoment :=
  paretoInner_residue_four

/-- A uniform constant of 18 works; the provider also covers even n ≥ 3. -/
theorem hiddenNoiseSecondMoment : HiddenNoiseSecondMoment := by
  exact ⟨18, fun n hn _ => hiddenNoise_secondMoment_log_bound n hn⟩

/-- The actual first absolute moment, with all infinite tails included. -/
theorem hiddenNoiseFirstMoment : HiddenNoiseFirstMoment := by
  exact ⟨18, fun n hn _ => hiddenNoise_firstMoment_log_bound n hn⟩

end
end RiemannResearch.RH.Pareto.ResearchTargets
