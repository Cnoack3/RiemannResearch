import RiemannResearch.Analysis.LaguerreMomentTransform
import RiemannResearch.RH.FiniteTwoSeedHeadMean
import RiemannResearch.RH.ParetoPrimePackets
import RiemannResearch.RH.ParetoNoiseSignal
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Concrete Ramanujan--Laguerre research obligations

Source: user-provided RH_Ramanujan_Laguerre_Schur_Continuation_20260911.md,
Sections 3--7. These definitions record exact specifications on actual
two-seed arithmetic packets and the continuous Pareto realization.
The companion modules ParetoExponentialRealization, ParetoDyadicCoefficientPolynomial,
ParetoMomentOptimizer and RamanujanOrdinaryMomentsProof now supply the realization,
finite-budget feasibility and optimizer, ordinary-moment and cancellation targets.
ActualParsevalTarget and the uniform-in-budget bounds remain open.
No proposition definition is an axiom, and no uniform bound or RH is asserted.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.RamanujanLaguerre

/-- The actual discrete packet viewed in the exponential coordinate. -/
def exponentialLift (F : ℕ → ℝ) (t : ℝ) : ℝ :=
  F ⌊Real.exp t⌋₊

/-- Ordinary log moment for the continuous Pareto realization. -/
def ordinaryMoment (F : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ),
    exponentialLift F t * t ^ j * Real.exp (-t)

/-- The actual Laguerre coefficient, not an abstract coordinate functional. -/
def coefficient (F : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ),
    exponentialLift F t * RiemannResearch.Analysis.laguerreValue k t *
      Real.exp (-t)

/-- Integrability of every actual ordinary moment prevents totalized
nonintegrable integrals from making moment constraints vacuous. -/
def AllMomentsIntegrable (F : ℕ → ℝ) : Prop :=
  ∀ j : ℕ, IntegrableOn
    (fun t => exponentialLift F t * t ^ j * Real.exp (-t)) (Set.Ici 0)

/-- The exact diagonal constraints at the prescribed dilation budget 2^K. -/
def MomentConstraints (K : ℕ) (F : ℕ → ℝ) : Prop :=
  F ∈ FiniteTwoSeedCompletion.budgetSpan (2 ^ K) ∧
  AllMomentsIntegrable F ∧ paretoMean F = 1 ∧
  ∀ j : ℕ, 0 < j → j ≤ K → coefficient F j = 0

/-- Full-error minimization over actual legal packets with the moment
constraints, rather than minimization over independently assigned moments. -/
def IsMomentOptimizer (K : ℕ) (F : ℕ → ℝ) : Prop :=
  MomentConstraints K F ∧
  ∀ G : ℕ → ℝ, MomentConstraints K G → paretoError F ≤ paretoError G

/-- Open formalization obligation: exact feasibility at every dyadic budget.
The supplied informal argument uses a concrete polynomial evaluation matrix. -/
def EveryBudgetFeasibleTarget : Prop :=
  ∀ K : ℕ, ∃ F : ℕ → ℝ, MomentConstraints K F

/-- Open formalization obligation: existence of the actual constrained
finite-dimensional optimizer, for each prescribed budget. -/
def EveryBudgetOptimizerTarget : Prop :=
  ∀ K : ℕ, ∃ F : ℕ → ℝ, IsMomentOptimizer K F

/-- Open analytic research target: uniformly bounded cost of actual legal
moment matching. This is the substantive estimate required by the note. -/
def UniformMomentBoundTarget : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ K : ℕ, ∃ F : ℕ → ℝ,
    MomentConstraints K F ∧ paretoError F ≤ B

/-- The specific optimizer version includes existence, so it cannot become
vacuously true merely because no optimizer has been supplied. -/
def UniformOptimizerBoundTarget : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ K : ℕ, ∃ F : ℕ → ℝ,
    IsMomentOptimizer K F ∧ paretoError F ≤ B

/-- Exact continuous exponential realization, supplied by
`continuousParetoRealizationTarget` in `ParetoExponentialRealization`. -/
def ContinuousParetoRealizationTarget : Prop :=
  ∀ F : ℕ → ℝ, F ∈ legalSeedSpan ({2, 3} : Set ℕ) →
    AllMomentsIntegrable F ∧
    ordinaryMoment F 0 = paretoMean F ∧
    (∫ t in Set.Ici (0 : ℝ),
      (exponentialLift F t - 1) ^ 2 * Real.exp (-t)) = paretoError F

/-- Open formalization obligation: Parseval for the actual Laguerre
coefficients of each mean-one legal packet. Summability is part of the target. -/
def ActualParsevalTarget : Prop :=
  ∀ F : ℕ → ℝ, F ∈ legalSeedSpan ({2, 3} : Set ℕ) →
    paretoMean F = 1 →
    Summable (fun k : ℕ => coefficient F (k + 1) ^ 2) ∧
    paretoError F = ∑' k : ℕ, coefficient F (k + 1) ^ 2

/-- Exact ordinary moments of actual Ramanujan packets, supplied by
`ramanujanOrdinaryMomentsTarget` in `RamanujanOrdinaryMomentsProof`.
The first surviving order is omega(d)-1. -/
def RamanujanOrdinaryMomentsTarget : Prop :=
  ∀ d : ℕ, 1 < d →
    AllMomentsIntegrable (ramanujanPacket d) ∧
    (∀ j : ℕ, j < d.primeFactors.card - 1 →
      ordinaryMoment (ramanujanPacket d) j = 0) ∧
    ordinaryMoment (ramanujanPacket d) (d.primeFactors.card - 1) =
      ((d.primeFactors.card - 1).factorial : ℝ) *
        ∏ p ∈ d.primeFactors, Real.log (p : ℝ)

/-- Exact arithmetic Laguerre cancellation on actual coefficient integrals,
supplied by `ramanujanLaguerreCancellationTarget` in `RamanujanOrdinaryMomentsProof`. -/
def RamanujanLaguerreCancellationTarget : Prop :=
  ∀ d : ℕ, 1 < d →
    (∀ k : ℕ, k < d.primeFactors.card - 1 →
      coefficient (ramanujanPacket d) k = 0) ∧
    coefficient (ramanujanPacket d) (d.primeFactors.card - 1) =
      (-1 : ℝ) ^ (d.primeFactors.card - 1) *
        ∏ p ∈ d.primeFactors, Real.log (p : ℝ)

/-- The actual exponential-Pareto integral is the finite transform of its
actual ordinary log moments, once their integrability is supplied. -/
theorem coefficient_eq_momentTransform (F : ℕ → ℝ)
    (hF : AllMomentsIntegrable F) (k : ℕ) :
    coefficient F k =
      RiemannResearch.Analysis.laguerreMomentTransform (ordinaryMoment F) k := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  have hint : ∀ j ≤ k, Integrable
      (fun t => (exponentialLift F t * Real.exp (-t)) * t ^ j) μ := by
    intro j hj
    have hi := hF j
    change Integrable
      (fun t => exponentialLift F t * t ^ j * Real.exp (-t)) μ at hi
    have heq : (fun t => (exponentialLift F t * Real.exp (-t)) * t ^ j) =
        (fun t => exponentialLift F t * t ^ j * Real.exp (-t)) := by
      funext t
      ring
    rw [heq]
    exact hi
  have hcoeff : coefficient F k =
      ∫ t, (exponentialLift F t * Real.exp (-t)) *
        RiemannResearch.Analysis.laguerreValue k t ∂μ := by
    unfold coefficient
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by ring)
  have hmom : (fun j : ℕ =>
      ∫ t, (exponentialLift F t * Real.exp (-t)) * t ^ j ∂μ) =
        ordinaryMoment F := by
    funext j
    unfold ordinaryMoment
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by ring)
  rw [hcoeff,
    RiemannResearch.Analysis.integral_mul_laguerreValue μ
      (fun t => exponentialLift F t * Real.exp (-t)) k hint,
    hmom]

/-- The arithmetic ordinary-moment specification implies Laguerre cancellation.
`RamanujanOrdinaryMomentsProof` supplies the ordinary-moment hypothesis and
exports the resulting unconditional cancellation provider. -/
theorem cancellationTarget_of_ordinaryMomentsTarget
    (h : RamanujanOrdinaryMomentsTarget) : RamanujanLaguerreCancellationTarget := by
  intro d hd
  obtain ⟨hI, hzero, hlead⟩ := h d hd
  constructor
  · intro k hk
    rw [coefficient_eq_momentTransform _ hI]
    exact RiemannResearch.Analysis.laguerreMomentTransform_eq_zero_of_moments
      _ hzero hk
  · rw [coefficient_eq_momentTransform _ hI]
    exact RiemannResearch.Analysis.laguerreMomentTransform_leading
      _ _ _ hzero hlead

end RiemannResearch.RH.Pareto.RamanujanLaguerre
