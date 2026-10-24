import RiemannResearch.RH.ApproximateHeadResidualTail
import RiemannResearch.RH.RamanujanTrialConvergence
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ParetoCoordinateEvaluation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Pointwise legal approximation and frequently bounded complete error

Source: user-requested fourth Ramanujan transfer program, 23 October 2026.
Exact growing heads and uniform boundedness are unnecessary. Along every
nontrivial filter, pointwise physical approximation together with merely
frequently bounded full error forces canonical saturation and hence RH.
Conversely, positive canonical residual energy forces every such pointwise
legal family's complete errors to tend to infinity. All P/Q packet trials
are covered, independently of their coefficient construction.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.SequenceHeadTail

theorem physical_residual_coordinate (f : ThresholdHilbert) (n : ℕ) :
    (hilbertOne - f : ThresholdHilbert) n =
      (1 - hilbertSequence f (n + 1)) * Real.sqrt (paretoWeight n) := by
  have hn : Real.sqrt (paretoWeight n) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    unfold paretoWeight
    positivity
  have h : hilbertSequence (hilbertOne - f) (n + 1) =
      1 - hilbertSequence f (n + 1) := by
    change hilbertSequenceLinear (hilbertOne - f) (n + 1) = _
    rw [map_sub]
    change hilbertSequence hilbertOne (n + 1) - hilbertSequence f (n + 1) = _
    rw [hilbertOne_sequence]
    simp [zeroAnchor]
  rw [hilbertSequence_succ] at h
  exact (div_eq_iff hn).mp h

theorem residualErrorHeadPairing_tendsto_zero {α : Type*} {l : Filter α}
    (F : α → ThresholdHilbert)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (F i) k) l (𝓝 1)) (N : ℕ) :
    Tendsto (fun i => residualErrorHeadPairing N (F i)) l (𝓝 0) := by
  apply headPair_tendsto_zero N limitResidual
    (fun i n => (hilbertOne - F i : ThresholdHilbert) n)
  intro n
  have hOne : Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1) := tendsto_const_nhds
  have h := (hOne.sub (hpoint (n + 1) (by omega))).mul_const
    (Real.sqrt (paretoWeight n))
  simpa only [physical_residual_coordinate, sub_self, zero_mul] using h

/-- Positive canonical residual energy forces divergence under pointwise physical approximation. -/
theorem pointwise_errors_diverge_of_limitEnergy_pos {α : Type*} {l : Filter α}
    (hE : 0 < limitEnergy) (F : α → ThresholdHilbert)
    (hlegal : ∀ i, F i ∈ closedSpace)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (F i) k) l (𝓝 1)) :
    Tendsto (fun i => ‖hilbertOne - F i‖ ^ 2) l atTop := by
  apply tendsto_atTop.mpr
  intro B
  let D : ℝ := max B 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hsmall := residualTailEnergy_tendsto_zero.eventually_lt_const
    (show 0 < limitEnergy ^ 2 / (4 * D) by positivity)
  obtain ⟨N, hN⟩ := hsmall.exists
  have hhead := (residualErrorHeadPairing_tendsto_zero F hpoint N).eventually_lt_const
    (show 0 < limitEnergy / 2 by positivity)
  filter_upwards [hhead] with i hi
  by_contra hn
  have herr : ‖hilbertOne - F i‖ ^ 2 ≤ D := by
    dsimp [D]
    linarith [lt_of_not_ge hn, le_max_left B 0]
  have hprod := mul_le_mul_of_nonneg_left herr (residualTailEnergy_nonneg N)
  have htail := residual_approximate_head_full_bound N (hlegal i)
  have hsmall' : residualTailEnergy N * (4 * D) < limitEnergy ^ 2 :=
    (lt_div_iff₀ (by positivity : 0 < 4 * D)).mp hN
  have hgap : limitEnergy / 2 < limitEnergy - residualErrorHeadPairing N (F i) := by linarith
  have hgap' : (limitEnergy / 2) ^ 2 <
      (limitEnergy - residualErrorHeadPairing N (F i)) ^ 2 :=
    (sq_lt_sq₀ (by positivity : 0 ≤ limitEnergy / 2) (by linarith)).mpr hgap
  nlinarith

theorem not_RH_pointwise_errors_diverge {α : Type*} {l : Filter α}
    (hRH : ¬ RiemannHypothesis) (F : α → ThresholdHilbert)
    (hlegal : ∀ i, F i ∈ closedSpace)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (F i) k) l (𝓝 1)) :
    Tendsto (fun i => ‖hilbertOne - F i‖ ^ 2) l atTop :=
  pointwise_errors_diverge_of_limitEnergy_pos (not_RH_limitEnergy_pos hRH) F hlegal hpoint

/-- A bounded cofinal subnet is enough; no eventual uniform bound is assumed. -/
theorem limitEnergy_zero_of_pointwise_frequently_bounded
    {α : Type*} {l : Filter α} [NeBot l]
    (F : α → ThresholdHilbert) (hlegal : ∀ i, F i ∈ closedSpace)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (F i) k) l (𝓝 1))
    (C : ℝ) (hbounded : ∃ᶠ i in l, ‖hilbertOne - F i‖ ^ 2 ≤ C) :
    limitEnergy = 0 := by
  by_contra hne
  have hE : 0 < limitEnergy := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
  have hd := pointwise_errors_diverge_of_limitEnergy_pos hE F hlegal hpoint
  have hgt : ∀ᶠ i in l, C < ‖hilbertOne - F i‖ ^ 2 :=
    hd.eventually (eventually_gt_atTop C)
  obtain ⟨i, hi, hlt⟩ := (hbounded.and_eventually hgt).exists
  exact (not_lt_of_ge hi) hlt

theorem riemannHypothesis_of_pointwise_frequently_bounded
    {α : Type*} {l : Filter α} [NeBot l]
    (F : α → ThresholdHilbert) (hlegal : ∀ i, F i ∈ closedSpace)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (F i) k) l (𝓝 1))
    (C : ℝ) (hbounded : ∃ᶠ i in l, ‖hilbertOne - F i‖ ^ 2 ≤ C) :
    RiemannHypothesis := by
  have he := limitEnergy_zero_of_pointwise_frequently_bounded F hlegal hpoint C hbounded
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (limitEnergy_zero_iff_mem.mp he))

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.RamanujanPointwiseCriterion
open Pareto Pareto.CoefficientStabilization
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open RamanujanTrialConvergence
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.FiniteHilbertGram

theorem toPareto_mem_full_closedSpace (f : QHilbert)
    (hf : f ∈ QFullResidueProjection.closure) : toPareto f ∈ closedSpace := by
  have he : f ∈ QFullResidueProjection.closure ↔ toPareto f ∈ closedSpace := by
    simpa only [toPareto_residueAtom, QFullResidueProjection.closure,
      QFullResidueProjection.legalSpan, closedSpace, dictionaryClosure] using
      mem_closure_span_iff (fun i : ℕ => qResidue (i + 2)) f
  exact he.mp hf

theorem qResidual_toPareto (f : QHilbert) :
    toPareto (qOne - f) = hilbertOne - toPareto f := by
  change toParetoLinear (qOne - f) = _
  rw [map_sub]
  exact congrArg (fun x => x - toPareto f) toPareto_qOne

/-- The same obstruction holds in the actual Q metric and physical coordinates. -/
theorem q_not_RH_pointwise_errors_diverge {α : Type*} {l : Filter α}
    (hRH : ¬ RiemannHypothesis) (F : α → QHilbert)
    (hlegal : ∀ i, F i ∈ QFullResidueProjection.closure)
    (hpoint : ∀ k : ℕ, 0 < k → Tendsto (fun i => qSequence (F i) k) l (𝓝 1)) :
    Tendsto (fun i => ‖qOne - F i‖ ^ 2) l atTop := by
  have hp := not_RH_pointwise_errors_diverge hRH (fun i => toPareto (F i))
    (fun i => toPareto_mem_full_closedSpace (F i) (hlegal i))
    (by simpa only [toPareto_sequence] using hpoint)
  apply tendsto_atTop.mpr
  intro B
  have hb : ∀ᶠ i in l, zetaTwo * B ≤ ‖hilbertOne - toPareto (F i)‖ ^ 2 :=
    hp.eventually (eventually_ge_atTop (zetaTwo * B))
  filter_upwards [hb] with i hi
  have hn := toPareto_norm_sq_le (qOne - F i)
  rw [qResidual_toPareto] at hn
  nlinarith [zetaTwo_pos]

theorem q_riemannHypothesis_of_pointwise_frequently_bounded
    {α : Type*} {l : Filter α} [NeBot l]
    (F : α → QHilbert) (hlegal : ∀ i, F i ∈ QFullResidueProjection.closure)
    (hpoint : ∀ k : ℕ, 0 < k → Tendsto (fun i => qSequence (F i) k) l (𝓝 1))
    (C : ℝ) (hbounded : ∃ᶠ i in l, ‖qOne - F i‖ ^ 2 ≤ C) :
    RiemannHypothesis := by
  by_contra hRH
  have hd := q_not_RH_pointwise_errors_diverge hRH F hlegal hpoint
  have hgt : ∀ᶠ i in l, C < ‖qOne - F i‖ ^ 2 := hd.eventually (eventually_gt_atTop C)
  obtain ⟨i, hi, hlt⟩ := (hbounded.and_eventually hgt).exists
  exact (not_lt_of_ge hi) hlt

theorem paretoTrial_mem_closedSpace (n : ℕ) (a : Fin n → ℝ) :
    paretoTrial n a ∈ closedSpace := by
  have h := synthesis_mem (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a
  change paretoTrial n a ∈ Submodule.span ℝ
    (Set.range (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))) at h
  rw [finitePacket_span_eq] at h
  exact ((walkSpan_le residueAtom id n).trans
    (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure) h

theorem qTrial_mem_closedSpace (n : ℕ) (a : Fin n → ℝ) :
    qTrial n a ∈ QFullResidueProjection.closure := by
  have h := synthesis_mem (QRamanujanCanonicalOptimizer.packetFamily n) a
  rw [QRamanujanCanonicalOptimizer.packet_span_eq_stage] at h
  exact ((walkSpan_le (fun i => qResidue (i + 2)) id n).trans
    (Submodule.span ℝ (Set.range (fun i : ℕ => qResidue (i + 2)))).le_topologicalClosure) h

/-- Actual Ramanujan trial arrays need neither normal equations nor exact head interpolation. -/
theorem pareto_packet_pointwise_bounded_criterion
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (a : ∀ i, Fin (N i) → ℝ)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => hilbertSequence (paretoTrial (N i) (a i)) k) l (𝓝 1))
    (C : ℝ) (hbounded : ∃ᶠ i in l, ‖hilbertOne - paretoTrial (N i) (a i)‖ ^ 2 ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_pointwise_frequently_bounded _
    (fun i => paretoTrial_mem_closedSpace (N i) (a i)) hpoint C hbounded

theorem q_packet_pointwise_bounded_criterion
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (a : ∀ i, Fin (N i) → ℝ)
    (hpoint : ∀ k : ℕ, 0 < k →
      Tendsto (fun i => qSequence (qTrial (N i) (a i)) k) l (𝓝 1))
    (C : ℝ) (hbounded : ∃ᶠ i in l, ‖qOne - qTrial (N i) (a i)‖ ^ 2 ≤ C) :
    RiemannHypothesis :=
  q_riemannHypothesis_of_pointwise_frequently_bounded _
    (fun i => qTrial_mem_closedSpace (N i) (a i)) hpoint C hbounded

def HasPointwiseBoundedParetoPackets : Prop :=
  ∃ a : (n : ℕ) → Fin n → ℝ,
    (∀ k : ℕ, 0 < k →
      Tendsto (fun n => hilbertSequence (paretoTrial n (a n)) k) atTop (𝓝 1)) ∧
    ∃ C : ℝ, ∃ᶠ n in atTop, ‖hilbertOne - paretoTrial n (a n)‖ ^ 2 ≤ C

def HasPointwiseBoundedQPackets : Prop :=
  ∃ a : (n : ℕ) → Fin n → ℝ,
    (∀ k : ℕ, 0 < k →
      Tendsto (fun n => qSequence (qTrial n (a n)) k) atTop (𝓝 1)) ∧
    ∃ C : ℝ, ∃ᶠ n in atTop, ‖qOne - qTrial n (a n)‖ ^ 2 ≤ C

theorem qTrial_physical (n : ℕ) (a : Fin n → ℝ) :
    qSequence (qTrial n a) = hilbertSequence (paretoTrial n a) := by
  rw [← toPareto_sequence, toPareto_qTrial]

/-- A single arithmetic coefficient family works in both measures. -/
theorem pointwise_bounded_packets_pareto_iff_q :
    HasPointwiseBoundedParetoPackets ↔ HasPointwiseBoundedQPackets := by
  constructor
  · rintro ⟨a, hpoint, C, hbound⟩
    refine ⟨a, ?_, (2 / zetaTwo) * C, ?_⟩
    · simpa only [qTrial_physical] using hpoint
    · apply hbound.mono
      intro n hn
      have hb := toQ_norm_sq_le (toPareto (qOne - qTrial n (a n)))
      rw [toQ_toPareto, toPareto_trial_residual] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left hn (by positivity [zetaTwo_pos]))
  · rintro ⟨a, hpoint, C, hbound⟩
    refine ⟨a, ?_, zetaTwo * C, ?_⟩
    · simpa only [qTrial_physical] using hpoint
    · apply hbound.mono
      intro n hn
      have hb := toPareto_norm_sq_le (qOne - qTrial n (a n))
      rw [toPareto_trial_residual] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left hn zetaTwo_pos.le)

/-- The existential pointwise/bounded criterion is exactly canonical saturation. -/
theorem pointwise_bounded_pareto_packets_iff_saturation :
    HasPointwiseBoundedParetoPackets ↔ limitEnergy = 0 := by
  constructor
  · rintro ⟨a, hpoint, C, hbound⟩
    exact limitEnergy_zero_of_pointwise_frequently_bounded
      (fun n => paretoTrial n (a n)) (fun n => paretoTrial_mem_closedSpace n (a n))
      hpoint C hbound
  · intro he
    have hlim : limitProjection = hilbertOne :=
      Submodule.starProjection_eq_self_iff.mpr (limitEnergy_zero_iff_mem.mp he)
    have ht : Tendsto (fun n => RamanujanCanonicalOptimizer.packetCandidate n)
        atTop (𝓝 hilbertOne) := by
      simpa only [RamanujanCanonicalOptimizer.packetCandidate_eq_projection, hlim] using
        projection_tendsto
    refine ⟨RamanujanCanonicalOptimizer.packetCoefficients, ?_, 1, ?_⟩
    · intro k hk
      have h := ((physicalEvaluationCLM (k - 1)).continuous.tendsto hilbertOne).comp ht
      have hk' : k - 1 + 1 = k := by omega
      simpa only [paretoTrial, RamanujanCanonicalOptimizer.packetCandidate,
        Function.comp_def, physicalEvaluationCLM_apply, hk', hilbertOne_sequence,
        zeroAnchor, if_neg (ne_of_gt hk)] using h
    · have hb : ∀ n : ℕ,
          ‖hilbertOne - paretoTrial n (RamanujanCanonicalOptimizer.packetCoefficients n)‖ ^ 2 ≤ 1 := by
        intro n
        change ‖hilbertOne - RamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 ≤ 1
        rw [RamanujanCanonicalOptimizer.packet_error]
        linarith [(RamanujanCanonicalOptimizer.packetMass_bounds n).1]
      exact (Eventually.of_forall hb).frequently

theorem pointwise_bounded_q_packets_iff_saturation :
    HasPointwiseBoundedQPackets ↔ limitEnergy = 0 :=
  pointwise_bounded_packets_pareto_iff_q.symm.trans
    pointwise_bounded_pareto_packets_iff_saturation

/-- Both new existence tests join the exact RH chain under the explicit classical converse. -/
theorem pointwise_bounded_packet_rh_equivalences
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    (HasPointwiseBoundedParetoPackets ↔ RiemannHypothesis) ∧
      (HasPointwiseBoundedQPackets ↔ RiemannHypothesis) := by
  have he := (RamanujanCanonicalOptimizer.packet_cofinal_mass_iff id tendsto_id).symm.trans
    (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1
  exact ⟨pointwise_bounded_pareto_packets_iff_saturation.trans he,
    pointwise_bounded_q_packets_iff_saturation.trans he⟩

end RiemannResearch.RH.RamanujanPointwiseCriterion
