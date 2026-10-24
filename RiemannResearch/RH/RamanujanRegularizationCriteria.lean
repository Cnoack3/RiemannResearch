import RiemannResearch.Analysis.RegularizationBudget
import RiemannResearch.Analysis.NonnegativeErrorConvergence
import RiemannResearch.RH.QRamanujanRegularizedConstraints
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.QRamanujanSaturationCriteria

/-!
# Moving soft Ramanujan constraints and RH equivalence chains

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
Stages, penalties, requested values, conductor locations and the number of
observations may all vary. The full cost is retained before the budget
criterion is imposed. Every RH converse states the Baez-Duarte provider.
The positive residue-atom convention gives the target negative Moebius.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanRegularizationCriteria
open Pareto ZetaTwoHilbert
open RamanujanRegularizedConstraints (constraintMatrix coordinateMismatch observe_eq)
open RamanujanCanonicalOptimizer (packetMultipleTransform)
open RiemannResearch.Analysis.FiniteRegularizedConstraints
open RiemannResearch.Analysis.RegularizationBudget
open RiemannResearch.Analysis.NonnegativeErrorConvergence

section Pareto
variable {κ : Type*} [Fintype κ]

def paretoSoftCost (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) : ℝ :=
  softCost (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ

def paretoCanonicalBudget (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) : ℝ :=
  ρ ^ 2 * coordinateMismatch n m t (RamanujanCanonicalOptimizer.packetCoefficients n)

theorem pareto_minimum_decomposition (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    RamanujanRegularizedConstraints.penalizedError n m t ρ (RamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) =
      1 - RamanujanCanonicalOptimizer.packetMass n + paretoSoftCost n m t ρ := by
  have h := minimum_decomposition (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ
  change _ = ‖hilbertOne - RamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 + _ at h
  rw [RamanujanCanonicalOptimizer.packet_error n] at h
  simpa only [RamanujanRegularizedConstraints.objective_eq, RamanujanRegularizedConstraints.regularizedCoefficients, paretoSoftCost] using h

/-- Uniform quarter-budget control of physical regularization bias, without rank assumptions. -/
theorem pareto_bias_quarter_bound (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    ‖RamanujanRegularizedConstraints.regularizedCandidate n m t ρ - RamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 ≤
      paretoCanonicalBudget n m t ρ / 4 := by
  simpa only [biasEnergy, canonicalBudget, mismatchEnergy, observe_eq, coordinateMismatch,
    paretoCanonicalBudget, RamanujanCanonicalOptimizer.packetCandidate, RamanujanCanonicalOptimizer.packetCoefficients,
    RamanujanRegularizedConstraints.regularizedCandidate, RamanujanRegularizedConstraints.regularizedCoefficients, map_sub] using
      bias_le_quarter_budget (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ

theorem pareto_softCost_nonneg (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    0 ≤ paretoSoftCost n m t ρ := softCost_nonneg (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ

theorem pareto_softCost_le_budget (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    paretoSoftCost n m t ρ ≤ paretoCanonicalBudget n m t ρ := by
  simpa only [paretoSoftCost, canonicalBudget, mismatchEnergy, observe_eq, coordinateMismatch,
    paretoCanonicalBudget, RamanujanCanonicalOptimizer.packetCoefficients] using
      softCost_le_budget (finitePacket_independent n) (constraintMatrix n m) hilbertOne t ρ

end Pareto

section ParetoMoving
variable {α : Type*} {l : Filter α} [NeBot l]
  {J : α → Type*} [∀ i, Fintype (J i)]

/-- No growing-head uniformity is hidden: the exact soft cost remains a separate necessary condition. -/
theorem pareto_moving_penalized_iff (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ) :
    Tendsto (fun i => RamanujanRegularizedConstraints.penalizedError (N i) (m i) (t i) (ρ i)
      (RamanujanRegularizedConstraints.regularizedCoefficients (N i) (m i) (t i) (ρ i))) l (𝓝 0) ↔
      CoefficientStabilization.limitEnergy = 0 ∧ Tendsto (fun i => paretoSoftCost (N i) (m i) (t i) (ρ i)) l (𝓝 0) := by
  have hb : Tendsto (fun i => 1 - RamanujanCanonicalOptimizer.packetMass (N i)) l (𝓝 CoefficientStabilization.limitEnergy) := by
    simpa only [Function.comp_def, RamanujanCanonicalOptimizer.packet_energy_eq_original] using
      CoefficientStabilization.energy_tendsto.comp hN
  have he : Tendsto (fun i => 1 - RamanujanCanonicalOptimizer.packetMass (N i)) l (𝓝 0) ↔ CoefficientStabilization.limitEnergy = 0 := by
    constructor
    · exact fun hz => tendsto_nhds_unique hb hz
    · intro hz
      simpa only [hz] using hb
  simp_rw [pareto_minimum_decomposition]
  rw [nonnegative_add_zero_iff
    (fun i => 1 - RamanujanCanonicalOptimizer.packetMass (N i))
    (fun i => paretoSoftCost (N i) (m i) (t i) (ρ i))
    (fun i => by rw [← RamanujanCanonicalOptimizer.packet_error]; exact sq_nonneg _)
    (fun i => pareto_softCost_nonneg (N i) (m i) (t i) (ρ i)), he]

theorem pareto_moving_penalized_rh_iff
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ) :
    Tendsto (fun i => RamanujanRegularizedConstraints.penalizedError (N i) (m i) (t i) (ρ i)
      (RamanujanRegularizedConstraints.regularizedCoefficients (N i) (m i) (t i) (ρ i))) l (𝓝 0) ↔
      RiemannHypothesis ∧ Tendsto (fun i => paretoSoftCost (N i) (m i) (t i) (ρ i)) l (𝓝 0) := by
  rw [pareto_moving_penalized_iff N hN m t ρ]
  have he : CoefficientStabilization.limitEnergy = 0 ↔ RiemannHypothesis :=
    (RamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
      (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1
  rw [he]

/-- A concrete vanishing canonical coefficient-defect budget absorbs all growing soft constraints. -/
theorem pareto_moving_budget_rh_iff
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ)
    (hbudget : Tendsto (fun i => paretoCanonicalBudget (N i) (m i) (t i) (ρ i)) l (𝓝 0)) :
    Tendsto (fun i => RamanujanRegularizedConstraints.penalizedError (N i) (m i) (t i) (ρ i)
      (RamanujanRegularizedConstraints.regularizedCoefficients (N i) (m i) (t i) (ρ i))) l (𝓝 0) ↔ RiemannHypothesis := by
  have hc : Tendsto (fun i => paretoSoftCost (N i) (m i) (t i) (ρ i)) l (𝓝 0) :=
    squeeze_zero (fun i => pareto_softCost_nonneg (N i) (m i) (t i) (ρ i))
      (fun i => pareto_softCost_le_budget (N i) (m i) (t i) (ρ i)) hbudget
  rw [pareto_moving_penalized_rh_iff hBaezDuarte N hN m t ρ]
  exact and_iff_left hc

/-- Bias control also yields unconditional convergence to the same actual closed-space projection. -/
theorem pareto_moving_budget_displacement
    (N : α → ℕ) (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ)
    (hbudget : Tendsto (fun i => paretoCanonicalBudget (N i) (m i) (t i) (ρ i)) l (𝓝 0)) :
    Tendsto (fun i => RamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i) -
      RamanujanCanonicalOptimizer.packetCandidate (N i)) l (𝓝 (0 : ThresholdHilbert)) := by
  have hb : Tendsto (fun i => ‖RamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i) -
      RamanujanCanonicalOptimizer.packetCandidate (N i)‖ ^ 2) l (𝓝 0) := by
    apply squeeze_zero (fun i => sq_nonneg _) (fun i =>
      pareto_bias_quarter_bound (N i) (m i) (t i) (ρ i))
    simpa only [zero_div] using hbudget.div_const 4
  have hn := (norm_zero_iff_square _).mpr hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hn

theorem pareto_moving_budget_norm_rh_iff
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ)
    (hbudget : Tendsto (fun i => paretoCanonicalBudget (N i) (m i) (t i) (ρ i)) l (𝓝 0)) :
    Tendsto (fun i => ‖hilbertOne - RamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i)‖ ^ 2)
      l (𝓝 0) ↔ RiemannHypothesis := by
  have hd := pareto_moving_budget_displacement N m t ρ hbudget
  have he : Tendsto (fun i => hilbertOne - RamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i)) l (𝓝 0) ↔
      Tendsto (fun i => hilbertOne - RamanujanCanonicalOptimizer.packetCandidate (N i)) l (𝓝 0) := by
    constructor
    · intro hs
      simpa only [sub_add_sub_cancel, add_zero] using hs.add hd
    · intro hc
      have ht := hc.sub hd
      convert ht using 1
      · funext i
        abel
      · simp
  have hbase : Tendsto (fun i => hilbertOne - RamanujanCanonicalOptimizer.packetCandidate (N i)) l (𝓝 0) ↔
      RiemannHypothesis := by
    have hb : Tendsto (fun i => ‖hilbertOne - RamanujanCanonicalOptimizer.packetCandidate (N i)‖ ^ 2) l (𝓝 0) ↔
        CoefficientStabilization.limitEnergy = 0 := by
      have ht : Tendsto (fun i => ‖hilbertOne - RamanujanCanonicalOptimizer.packetCandidate (N i)‖ ^ 2) l (𝓝 CoefficientStabilization.limitEnergy) := by
        simpa only [RamanujanCanonicalOptimizer.packet_error, Function.comp_def,
          RamanujanCanonicalOptimizer.packet_energy_eq_original] using CoefficientStabilization.energy_tendsto.comp hN
      constructor
      · exact fun hz => tendsto_nhds_unique ht hz
      · intro hz
        simpa only [hz] using ht
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    rw [norm_zero_iff_square, hb]
    exact (RamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
      (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1
  rw [← norm_zero_iff_square]
  have hs : Tendsto (fun i => ‖hilbertOne - RamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i)‖)
      l (𝓝 0) ↔ Tendsto (fun i => hilbertOne - RamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i)) l (𝓝 0) := by
    constructor
    · intro h
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simpa only [sub_zero] using h
    · intro h
      have hh := tendsto_iff_norm_sub_tendsto_zero.mp h
      simpa only [sub_zero] using hh
  exact hs.trans (he.trans hbase)

/-- The complete regularized original-coordinate criterion remains equivalent to RH.
These are residue coordinates of legal Ramanujan approximants, with target negative Moebius. -/
theorem pareto_moving_budget_coordinates_rh_iff
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ)
    (hbudget : Tendsto (fun i => paretoCanonicalBudget (N i) (m i) (t i) (ρ i)) l (𝓝 0)) :
    (∀ d : ℕ, 1 < d → Tendsto (fun i => CoefficientStabilization.coefficientCLM d
      (RamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i))) l
        (𝓝 (-(ArithmeticFunction.moebius d : ℝ)))) ↔ RiemannHypothesis := by
  have hd := pareto_moving_budget_displacement N m t ρ hbudget
  have hdiff (d : ℕ) (hd' : 1 < d) :
      Tendsto (fun i => CoefficientStabilization.coefficientCLM d (RamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i)) -
        RamanujanCanonicalOptimizer.packetMultipleCoefficient (N i) d) l (𝓝 0) := by
    have ht := (CoefficientStabilization.coefficientCLM d).continuous.continuousAt.tendsto.comp hd
    have hc (i : α) : CoefficientStabilization.coefficientCLM d (RamanujanCanonicalOptimizer.packetCandidate (N i)) =
        RamanujanCanonicalOptimizer.packetMultipleCoefficient (N i) d := by
      exact RamanujanCanonicalOptimizer.coefficient_packet_synthesis
        (N i) (RamanujanCanonicalOptimizer.packetCoefficients (N i)) d hd'
    simpa only [Function.comp_def, map_sub, map_zero, hc] using ht
  have he : (∀ d : ℕ, 1 < d → Tendsto (fun i => CoefficientStabilization.coefficientCLM d
      (RamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i))) l
        (𝓝 (-(ArithmeticFunction.moebius d : ℝ)))) ↔
      (∀ d : ℕ, 1 < d → Tendsto (fun i => RamanujanCanonicalOptimizer.packetMultipleCoefficient (N i) d) l
        (𝓝 (-(ArithmeticFunction.moebius d : ℝ)))) := by
    constructor
    · intro hs d hd'
      have ht := (hs d hd').sub (hdiff d hd')
      convert ht using 1
      · funext i
        ring
      · simp
    · intro hc d hd'
      have ht := (hc d hd').add (hdiff d hd')
      convert ht using 1
      · funext i
        ring
      · simp
  exact he.trans (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).2.2.1

end ParetoMoving

section Q
variable {κ : Type*} [Fintype κ]

def qSoftCost (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) : ℝ :=
  softCost (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t ρ

def qCanonicalBudget (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) : ℝ :=
  ρ ^ 2 * coordinateMismatch n m t (QRamanujanCanonicalOptimizer.packetCoefficients n)

theorem q_minimum_decomposition (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    QRamanujanRegularizedConstraints.penalizedError n m t ρ (QRamanujanRegularizedConstraints.regularizedCoefficients n m t ρ) =
      1 - QRamanujanCanonicalOptimizer.packetMass n + qSoftCost n m t ρ := by
  have h := minimum_decomposition (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t ρ
  change _ = ‖qOne - QRamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 + _ at h
  rw [QRamanujanCanonicalOptimizer.packet_error n] at h
  simpa only [QRamanujanRegularizedConstraints.objective_eq, QRamanujanRegularizedConstraints.regularizedCoefficients, qSoftCost] using h

/-- Uniform quarter-budget control of physical regularization bias, without rank assumptions. -/
theorem q_bias_quarter_bound (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    ‖QRamanujanRegularizedConstraints.regularizedCandidate n m t ρ - QRamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 ≤
      qCanonicalBudget n m t ρ / 4 := by
  simpa only [biasEnergy, canonicalBudget, mismatchEnergy, observe_eq, coordinateMismatch,
    qCanonicalBudget, QRamanujanCanonicalOptimizer.packetCandidate, QRamanujanCanonicalOptimizer.packetCoefficients,
    QRamanujanRegularizedConstraints.regularizedCandidate, QRamanujanRegularizedConstraints.regularizedCoefficients, map_sub] using
      bias_le_quarter_budget (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t ρ

theorem q_softCost_nonneg (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    0 ≤ qSoftCost n m t ρ := softCost_nonneg (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t ρ

theorem q_softCost_le_budget (n : ℕ) (m : κ → ℕ) (t : κ → ℝ) (ρ : ℝ) :
    qSoftCost n m t ρ ≤ qCanonicalBudget n m t ρ := by
  simpa only [qSoftCost, canonicalBudget, mismatchEnergy, observe_eq, coordinateMismatch,
    qCanonicalBudget, QRamanujanCanonicalOptimizer.packetCoefficients] using
      softCost_le_budget (QRamanujanCanonicalOptimizer.packet_independent n) (constraintMatrix n m) qOne t ρ

end Q

section QMoving
variable {α : Type*} {l : Filter α} [NeBot l]
  {J : α → Type*} [∀ i, Fintype (J i)]

/-- No growing-head uniformity is hidden: the exact soft cost remains a separate necessary condition. -/
theorem q_moving_penalized_iff (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ) :
    Tendsto (fun i => QRamanujanRegularizedConstraints.penalizedError (N i) (m i) (t i) (ρ i)
      (QRamanujanRegularizedConstraints.regularizedCoefficients (N i) (m i) (t i) (ρ i))) l (𝓝 0) ↔
      QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 ∧ Tendsto (fun i => qSoftCost (N i) (m i) (t i) (ρ i)) l (𝓝 0) := by
  have hb : Tendsto (fun i => 1 - QRamanujanCanonicalOptimizer.packetMass (N i)) l (𝓝 QRamanujanCanonicalOptimizer.packetLimitEnergy) := by
    simpa only [Function.comp_def, QRamanujanCanonicalOptimizer.packetError] using
      QRamanujanCanonicalOptimizer.packetError_tendsto.comp hN
  have he : Tendsto (fun i => 1 - QRamanujanCanonicalOptimizer.packetMass (N i)) l (𝓝 0) ↔ QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
    constructor
    · exact fun hz => tendsto_nhds_unique hb hz
    · intro hz
      simpa only [hz] using hb
  simp_rw [q_minimum_decomposition]
  rw [nonnegative_add_zero_iff
    (fun i => 1 - QRamanujanCanonicalOptimizer.packetMass (N i))
    (fun i => qSoftCost (N i) (m i) (t i) (ρ i))
    (fun i => by rw [← QRamanujanCanonicalOptimizer.packet_error]; exact sq_nonneg _)
    (fun i => q_softCost_nonneg (N i) (m i) (t i) (ρ i)), he]

theorem q_moving_penalized_rh_iff
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ) :
    Tendsto (fun i => QRamanujanRegularizedConstraints.penalizedError (N i) (m i) (t i) (ρ i)
      (QRamanujanRegularizedConstraints.regularizedCoefficients (N i) (m i) (t i) (ρ i))) l (𝓝 0) ↔
      RiemannHypothesis ∧ Tendsto (fun i => qSoftCost (N i) (m i) (t i) (ρ i)) l (𝓝 0) := by
  rw [q_moving_penalized_iff N hN m t ρ]
  have he : QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 ↔ RiemannHypothesis :=
    (QRamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
      (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1
  rw [he]

/-- A concrete vanishing canonical coefficient-defect budget absorbs all growing soft constraints. -/
theorem q_moving_budget_rh_iff
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ)
    (hbudget : Tendsto (fun i => qCanonicalBudget (N i) (m i) (t i) (ρ i)) l (𝓝 0)) :
    Tendsto (fun i => QRamanujanRegularizedConstraints.penalizedError (N i) (m i) (t i) (ρ i)
      (QRamanujanRegularizedConstraints.regularizedCoefficients (N i) (m i) (t i) (ρ i))) l (𝓝 0) ↔ RiemannHypothesis := by
  have hc : Tendsto (fun i => qSoftCost (N i) (m i) (t i) (ρ i)) l (𝓝 0) :=
    squeeze_zero (fun i => q_softCost_nonneg (N i) (m i) (t i) (ρ i))
      (fun i => q_softCost_le_budget (N i) (m i) (t i) (ρ i)) hbudget
  rw [q_moving_penalized_rh_iff hBaezDuarte N hN m t ρ]
  exact and_iff_left hc

/-- Bias control also yields unconditional convergence to the same actual closed-space projection. -/
theorem q_moving_budget_displacement
    (N : α → ℕ) (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ)
    (hbudget : Tendsto (fun i => qCanonicalBudget (N i) (m i) (t i) (ρ i)) l (𝓝 0)) :
    Tendsto (fun i => QRamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i) -
      QRamanujanCanonicalOptimizer.packetCandidate (N i)) l (𝓝 (0 : QHilbert)) := by
  have hb : Tendsto (fun i => ‖QRamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i) -
      QRamanujanCanonicalOptimizer.packetCandidate (N i)‖ ^ 2) l (𝓝 0) := by
    apply squeeze_zero (fun i => sq_nonneg _) (fun i =>
      q_bias_quarter_bound (N i) (m i) (t i) (ρ i))
    simpa only [zero_div] using hbudget.div_const 4
  have hn := (norm_zero_iff_square _).mpr hb
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hn

theorem q_moving_budget_norm_rh_iff
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ)
    (hbudget : Tendsto (fun i => qCanonicalBudget (N i) (m i) (t i) (ρ i)) l (𝓝 0)) :
    Tendsto (fun i => ‖qOne - QRamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i)‖ ^ 2)
      l (𝓝 0) ↔ RiemannHypothesis := by
  have hd := q_moving_budget_displacement N m t ρ hbudget
  have he : Tendsto (fun i => qOne - QRamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i)) l (𝓝 0) ↔
      Tendsto (fun i => qOne - QRamanujanCanonicalOptimizer.packetCandidate (N i)) l (𝓝 0) := by
    constructor
    · intro hs
      simpa only [sub_add_sub_cancel, add_zero] using hs.add hd
    · intro hc
      have ht := hc.sub hd
      convert ht using 1
      · funext i
        abel
      · simp
  have hbase : Tendsto (fun i => qOne - QRamanujanCanonicalOptimizer.packetCandidate (N i)) l (𝓝 0) ↔
      RiemannHypothesis := by
    have hb : Tendsto (fun i => ‖qOne - QRamanujanCanonicalOptimizer.packetCandidate (N i)‖ ^ 2) l (𝓝 0) ↔
        QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
      have ht : Tendsto (fun i => ‖qOne - QRamanujanCanonicalOptimizer.packetCandidate (N i)‖ ^ 2) l (𝓝 QRamanujanCanonicalOptimizer.packetLimitEnergy) := by
        simpa only [QRamanujanCanonicalOptimizer.packet_error, Function.comp_def,
          QRamanujanCanonicalOptimizer.packetError] using QRamanujanCanonicalOptimizer.packetError_tendsto.comp hN
      constructor
      · exact fun hz => tendsto_nhds_unique ht hz
      · intro hz
        simpa only [hz] using ht
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    rw [norm_zero_iff_square, hb]
    exact (QRamanujanCanonicalOptimizer.packet_cofinal_mass_iff N hN).symm.trans
      (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).1
  rw [← norm_zero_iff_square]
  have hs : Tendsto (fun i => ‖qOne - QRamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i)‖)
      l (𝓝 0) ↔ Tendsto (fun i => qOne - QRamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i)) l (𝓝 0) := by
    constructor
    · intro h
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simpa only [sub_zero] using h
    · intro h
      have hh := tendsto_iff_norm_sub_tendsto_zero.mp h
      simpa only [sub_zero] using hh
  exact hs.trans (he.trans hbase)

/-- The complete regularized original-coordinate criterion remains equivalent to RH.
These are residue coordinates of legal Ramanujan approximants, with target negative Moebius. -/
theorem q_moving_budget_coordinates_rh_iff
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (m : ∀ i, J i → ℕ) (t : ∀ i, J i → ℝ) (ρ : α → ℝ)
    (hbudget : Tendsto (fun i => qCanonicalBudget (N i) (m i) (t i) (ρ i)) l (𝓝 0)) :
    (∀ d : ℕ, 1 < d → Tendsto (fun i => SquarefreeMobiusProjection.qCoefficientCLM d
      (QRamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i))) l
        (𝓝 (-(ArithmeticFunction.moebius d : ℝ)))) ↔ RiemannHypothesis := by
  have hd := q_moving_budget_displacement N m t ρ hbudget
  have hdiff (d : ℕ) (hd' : 1 < d) :
      Tendsto (fun i => SquarefreeMobiusProjection.qCoefficientCLM d (QRamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i)) -
        QRamanujanCanonicalOptimizer.packetCoordinate (N i) d) l (𝓝 0) := by
    have ht := (SquarefreeMobiusProjection.qCoefficientCLM d).continuous.continuousAt.tendsto.comp hd
    have hc (i : α) : SquarefreeMobiusProjection.qCoefficientCLM d (QRamanujanCanonicalOptimizer.packetCandidate (N i)) =
        QRamanujanCanonicalOptimizer.packetCoordinate (N i) d := by
      exact (QRamanujanCanonicalOptimizer.packetCoordinate_eq (N i) d hd').symm
    simpa only [Function.comp_def, map_sub, map_zero, hc] using ht
  have he : (∀ d : ℕ, 1 < d → Tendsto (fun i => SquarefreeMobiusProjection.qCoefficientCLM d
      (QRamanujanRegularizedConstraints.regularizedCandidate (N i) (m i) (t i) (ρ i))) l
        (𝓝 (-(ArithmeticFunction.moebius d : ℝ)))) ↔
      (∀ d : ℕ, 1 < d → Tendsto (fun i => QRamanujanCanonicalOptimizer.packetCoordinate (N i) d) l
        (𝓝 (-(ArithmeticFunction.moebius d : ℝ)))) := by
    constructor
    · intro hs d hd'
      have ht := (hs d hd').sub (hdiff d hd')
      convert ht using 1
      · funext i
        ring
      · simp
    · intro hc d hd'
      have ht := (hc d hd').add (hdiff d hd')
      convert ht using 1
      · funext i
        ring
      · simp
  exact he.trans (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte N hN).2.1

end QMoving

end RiemannResearch.RH.RamanujanRegularizationCriteria
