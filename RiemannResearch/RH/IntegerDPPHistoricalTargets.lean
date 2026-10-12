import RiemannResearch.RH.IntegerDPPDampedConvergence

/-!
# Explicit open DPP targets from the historical not-RH catalogue

Source: user-provided catalogue, groups 24--27, 2026-09-21.

Every capitalized declaration in this module is a proposition *definition*,
not a theorem and not an axiom. PositiveFiniteHead is proved in
IntegerDPPWindowPositivity. Other providers remain separate. The events,
finite determinants, laws, and kernels are the actual arithmetic objects.
This records precise remaining obligations instead of assuming conclusions
in a purported proof.  In particular, finite determinant generating formulas
do not yet identify an operator-theoretic Fredholm determinant.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology Classical BigOperators

namespace RiemannResearch.RH.Pareto.IntegerDPP.HistoricalTargets

/-- Probability that all physical sites 1,...,m are occupied. -/
def headOccupationProbability (m : ℕ) : ℝ :=
  limitingLaw.real {x | ∀ n < m, x n = true}

/-- Probability that physical sites 2,...,m are occupied. -/
def surroundingOccupationProbability (m : ℕ) : ℝ :=
  limitingLaw.real {x | ∀ n < m, 0 < n → x n = true}

def firstConditionalOccupation (m : ℕ) : ℝ :=
  headOccupationProbability m / surroundingOccupationProbability m

/-- Open: the actual hole process has at least two points almost surely. -/
def AtLeastTwoHoles : Prop :=
  ¬ RiemannHypothesis →
    ∀ᵐ x ∂limitingLaw, ∃ i j : ℕ, i ≠ j ∧ x i = false ∧ x j = false

/-- Positivity of every finite head event; proved by IntegerDPPWindowPositivity.positiveFiniteHead. -/
def PositiveFiniteHead : Prop :=
  ∀ m : ℕ, 0 < headOccupationProbability m

/-- Open: the conjugate zero pair gives exponent 4 Re(s)-2. -/
def HeadOccupationPairExponent : Prop :=
  ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s.re < 1 → riemannZeta s = 0 →
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ,
      headOccupationProbability (m + 1) ≤
        C * ((m : ℝ) + 1) ^ (-(4 * s.re - 2))

/-- Open: conditional inclusion decreases to zero along growing heads. -/
def ConditionalOccupationDecay : Prop :=
  ¬ RiemannHypothesis →
    Antitone firstConditionalOccupation ∧
      Tendsto firstConditionalOccupation atTop (𝓝 0)

/-- An actual finite determinant of the exponentially damped hole kernel. -/
def holePrefixDeterminant (t : ℝ) (m : ℕ) : ℝ :=
  (1 - Matrix.diagonal (fun i : Fin m => Real.exp (-t * ((i.val : ℝ) + 1))) *
    (1 - Matrix.of (fun i j : Fin m => limitingKernel i.val j.val))).det

/-- The infimum of the finite determinant values. Convergence, positivity,
and Fredholm identification remain separate proof obligations below. -/
def holeDampedValue (t : ℝ) : ℝ :=
  sInf (Set.range (holePrefixDeterminant t))

def HolePrefixConvergence : Prop :=
  ∀ t : ℝ, 0 < t →
    Tendsto (holePrefixDeterminant t) atTop (𝓝 (holeDampedValue t)) ∧
      0 < holeDampedValue t ∧ holeDampedValue t ≤ 1

/-- Open: exact zero-one limit for this precisely defined numerical object. -/
def HoleDampingZeroOne : Prop :=
  Tendsto holeDampedValue (𝓝[>] (0 : ℝ))
    (𝓝 (if limitingVacancy = 0 then 1 else 0))

/-- Open: pair exponent for an actual off-line zero. -/
def HoleDampingPairExponent : Prop :=
  ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s.re < 1 → riemannZeta s = 0 →
    ∃ C : ℝ, 0 < C ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ℝ, 0 < t → t < ε →
        holeDampedValue t ≤ C * t ^ (4 * s.re - 2)

def weightedVacancyMass : ℝ :=
  ∑' n : ℕ, paretoWeight n * (1 - limitingKernel n n)

/-- Open: sharp log comparison with the fixed Pareto occupied benchmark.
The limit is the actual unconditionally convergent value. This concerns a
separate determinant from the exponentially damped hole determinant. -/
def OccupiedDampingLogComparison : Prop :=
  weightedVacancyMass ≤ Real.log (dampedPrefixLimit / paretoProductBenchmark) ∧
    Real.log (dampedPrefixLimit / paretoProductBenchmark) ≤
      2 * weightedVacancyMass

/-- Open: actual occupied points are infinite in every fixed progression. -/
def InfiniteArithmeticProgressionOccupation : Prop :=
  ∀ a d : ℕ, 0 < d →
    ∀ᵐ x ∂limitingLaw,
      Set.Infinite {n : ℕ | x n = true ∧ (n + 1) % d = a % d}

/-- Probability that the first-site congruence class contains an occupied
physical point at finite rank N. -/
def residueClassOccupationProbability (N M : ℕ) : ℝ :=
  (integerLaw N).real {x | ∃ k : ℕ, x (M * k) = true}

/-- Open: the two rank/class iterated limits disagree under not RH.
The increasing class moduli are positive and each divides its successor. -/
def ShrinkingClassNoncommutation : Prop :=
  ∀ M : ℕ → ℕ, (∀ j, 0 < M j) → (∀ j, M j ∣ M (j + 1)) →
    Tendsto M atTop atTop →
    (∀ j, Tendsto (fun N => residueClassOccupationProbability N (M j))
      atTop (𝓝 1)) ∧
    (∀ N, Tendsto (fun j => residueClassOccupationProbability N (M j))
      atTop (𝓝 (integerKernel N 0 0)))

end RiemannResearch.RH.Pareto.IntegerDPP.HistoricalTargets
