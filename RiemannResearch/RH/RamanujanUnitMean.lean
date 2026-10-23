import RiemannResearch.Analysis.ProjectionMeanOne
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.MeanOneResidualFloor
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
/-!
# Actual normalized mean-one Ramanujan optimizers
Source: user-requested continuation, 23 October 2026.
The arithmetic signal is proved positive. Finite and closed-space exact
minimum-energy identities strengthen the original variance lower bound.
Convergence to the normalized limiting projection is unconditional; energy
tending to one is a saturation test. The RH converse stays explicit.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.RamanujanCanonicalOptimizer
open Pareto Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionMeanOne

theorem packetMass_pos (n : ℕ) (hn : 0 < n) : 0 < packetMass n := by
  have hne : packetCandidate n ≠ 0 := by
    intro hz
    have h := packet_normal n ⟨0, hn⟩
    simp only [Nat.zero_add, hz, inner_zero_right] at h
    have hp : 0 < ArithmeticFunction.vonMangoldt 2 := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact Real.log_pos (by norm_num)
    linarith
  rw [← packet_energy]
  exact sq_pos_of_pos (norm_pos_iff.mpr hne)

theorem packetLimitMass_pos : 0 < 1 - limitEnergy := by
  have ht := packetMass_tendsto.comp (tendsto_add_atTop_nat 1)
  have hle : packetMass 1 ≤ 1 - limitEnergy :=
    ge_of_tendsto' ht (fun n => packetMass_monotone (by omega : 1 ≤ n + 1))
  exact lt_of_lt_of_le (packetMass_pos 1 (by omega)) hle

/-- Shift by one so every stage has a nonzero arithmetic signal. -/
def packetUnitMean (n : ℕ) : ThresholdHilbert :=
  (packetMass (n + 1))⁻¹ • packetCandidate (n + 1)

def packetUnitMeanLimit : ThresholdHilbert :=
  (1 - limitEnergy)⁻¹ • limitProjection

theorem packetUnitMean_eq_normalized (n : ℕ) :
    packetUnitMean n = normalized (finiteSpace (n + 1)) hilbertOne := by
  unfold normalized
  change packetUnitMean n = (‖projection (n + 1)‖ ^ 2)⁻¹ • projection (n + 1)
  rw [← packetCandidate_eq_projection, packet_energy]
  rfl

theorem packet_projection_ne_zero (n : ℕ) :
    (finiteSpace (n+1)).starProjection hilbertOne ≠ 0 := by
  intro h
  have he := packet_energy (n+1)
  rw [packetCandidate_eq_projection] at he
  change ‖(finiteSpace (n+1)).starProjection hilbertOne‖ ^ 2 = _ at he
  rw [h, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
  exact (ne_of_gt (packetMass_pos (n+1) (by omega))) he.symm

theorem packetUnitMean_legal (n : ℕ) : packetUnitMean n ∈ finiteSpace (n+1) := by
  rw [packetUnitMean_eq_normalized]
  exact normalized_mem _ _

theorem packetUnitMean_signal (n : ℕ) :
    inner ℝ hilbertOne (packetUnitMean n) = 1 := by
  rw [packetUnitMean_eq_normalized]
  exact normalized_signal _ _ (packet_projection_ne_zero n)

theorem packetUnitMean_energy (n : ℕ) :
    ‖packetUnitMean n‖ ^ 2 = (packetMass (n+1))⁻¹ := by
  rw [packetUnitMean_eq_normalized, normalized_energy _ _ (packet_projection_ne_zero n)]
  change (‖projection (n+1)‖ ^ 2)⁻¹ = _
  rw [← packetCandidate_eq_projection, packet_energy]

theorem packetUnitMean_completion (n : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace (n+1)) (hm : inner ℝ hilbertOne f = 1) :
    ‖f‖ ^ 2 = (packetMass (n+1))⁻¹ + ‖f - packetUnitMean n‖ ^ 2 := by
  have h := completion (finiteSpace (n+1)) hilbertOne f
    (packet_projection_ne_zero n) hf hm
  rw [← packetUnitMean_eq_normalized] at h
  change ‖f‖ ^ 2 = (‖projection (n+1)‖ ^ 2)⁻¹ + _ at h
  simpa only [← packetCandidate_eq_projection, packet_energy] using h

theorem packetUnitMean_variance (n : ℕ) :
    ‖packetUnitMean n - hilbertOne‖ ^ 2 =
      (1 - packetMass (n+1)) / packetMass (n+1) := by
  have hm : inner ℝ (packetUnitMean n) hilbertOne = 1 := by
    rw [real_inner_comm]
    exact packetUnitMean_signal n
  rw [norm_sub_sq_real, packetUnitMean_energy, hilbertOne_norm_sq, hm]
  field_simp [ne_of_gt (packetMass_pos (n+1) (by omega))]
  <;> ring

theorem packetUnitMean_nested_distance (m n : ℕ) (hmn : m ≤ n) :
    ‖packetUnitMean m - packetUnitMean n‖ ^ 2 =
      (packetMass (m+1))⁻¹ - (packetMass (n+1))⁻¹ := by
  have h := nested_distance (finiteSpace (m+1)) (finiteSpace (n+1))
    (walkSpan_mono residueAtom id (Nat.add_le_add_right hmn 1)) hilbertOne
    (packet_projection_ne_zero m) (packet_projection_ne_zero n)
  rw [← packetUnitMean_eq_normalized, ← packetUnitMean_eq_normalized] at h
  change _ = (‖projection (m+1)‖ ^ 2)⁻¹ - (‖projection (n+1)‖ ^ 2)⁻¹ at h
  simpa only [← packetCandidate_eq_projection, packet_energy] using h

theorem packetUnitMean_tendsto :
    Tendsto packetUnitMean atTop (𝓝 packetUnitMeanLimit) := by
  have hm := packetMass_tendsto.comp (tendsto_add_atTop_nat 1)
  have hp : Tendsto (fun n => packetCandidate (n+1)) atTop (𝓝 limitProjection) := by
    simpa only [Function.comp_def, packetCandidate_eq_projection] using
      projection_tendsto.comp (tendsto_add_atTop_nat 1)
  exact (hm.inv₀ (ne_of_gt packetLimitMass_pos)).smul hp

theorem packetUnitMeanLimit_energy :
    ‖packetUnitMeanLimit‖ ^ 2 = (1 - limitEnergy)⁻¹ := by
  have h := ((packetMass_tendsto.comp (tendsto_add_atTop_nat 1)).inv₀
    (ne_of_gt packetLimitMass_pos))
  have hnorm := packetUnitMean_tendsto.norm.pow 2
  simp_rw [packetUnitMean_energy] at hnorm
  exact tendsto_nhds_unique hnorm h


theorem packetUnitMeanLimit_eq_normalized :
    packetUnitMeanLimit = normalized closedSpace hilbertOne := by
  unfold normalized
  change packetUnitMeanLimit = (‖limitProjection‖ ^ 2)⁻¹ • limitProjection
  rw [limitProjection_norm_sq]
  rfl

theorem packetUnitMeanLimit_projection_ne_zero :
    closedSpace.starProjection hilbertOne ≠ 0 := by
  intro hz
  have he := limitProjection_norm_sq
  change ‖closedSpace.starProjection hilbertOne‖ ^ 2 = _ at he
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
  exact (ne_of_gt packetLimitMass_pos) he.symm

/-- The sharp original closed-space lower bound has an attained exact remainder. -/
theorem packetUnitMeanLimit_completion (f : ThresholdHilbert)
    (hf : f ∈ closedSpace) (hm : inner ℝ hilbertOne f = 1) :
    ‖f‖ ^ 2 = (1 - limitEnergy)⁻¹ + ‖f - packetUnitMeanLimit‖ ^ 2 := by
  have h := completion closedSpace hilbertOne f
    packetUnitMeanLimit_projection_ne_zero hf hm
  rw [← packetUnitMeanLimit_eq_normalized] at h
  change ‖f‖ ^ 2 = (‖limitProjection‖ ^ 2)⁻¹ + _ at h
  simpa only [limitProjection_norm_sq] using h

theorem packetUnitMeanLimit_variance_completion (f : ThresholdHilbert)
    (hf : f ∈ closedSpace) (hm : inner ℝ hilbertOne f = 1) :
    ‖f - hilbertOne‖ ^ 2 = limitEnergy / (1 - limitEnergy) +
      ‖f - packetUnitMeanLimit‖ ^ 2 := by
  have hm' : inner ℝ f hilbertOne = 1 := by
    rw [real_inner_comm]
    exact hm
  rw [norm_sub_sq_real, hilbertOne_norm_sq, hm',
    packetUnitMeanLimit_completion f hf hm]
  field_simp [ne_of_gt packetLimitMass_pos]
  <;> ring

theorem packetUnitMean_energy_tendsto_one_iff :
    Tendsto (fun n => ‖packetUnitMean n‖ ^ 2) atTop (𝓝 1) ↔ limitEnergy = 0 := by
  have ht := packetUnitMean_tendsto.norm.pow 2
  rw [packetUnitMeanLimit_energy] at ht
  constructor
  · intro h
    have he := tendsto_nhds_unique ht h
    have hi : 1 - limitEnergy = 1 := inv_eq_one.mp he
    linarith
  · intro h
    simpa only [h, sub_zero, inv_one] using ht

theorem packetUnitMean_energy_iff_rh
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    Tendsto (fun n => ‖packetUnitMean n‖ ^ 2) atTop (𝓝 1) ↔ RiemannHypothesis :=
  packetUnitMean_energy_tendsto_one_iff.trans
    ((packet_cofinal_mass_iff id tendsto_id).symm.trans
      (packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1)

end RiemannResearch.RH.RamanujanCanonicalOptimizer
