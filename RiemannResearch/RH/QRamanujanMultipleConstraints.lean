import RiemannResearch.RH.RamanujanMultipleConstraints
import RiemannResearch.RH.QRamanujanCanonicalOptimizer
import RiemannResearch.RH.QParetoGramComparison
import RiemannResearch.Analysis.FiniteConstrainedMetricComparison
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual Q optimizers with several prescribed legal coefficients

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
Every finite selection of legal residue coordinates has an automatically
invertible source Gram in Q as well as Pareto. The actual Q moments and Q
inverse Gram are retained. The two constrained minima satisfy exact metric
identities, a two-displacement correction balance, and uniform comparison.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QRamanujanMultipleConstraints
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoMetric QRamanujanCanonicalOptimizer
open RamanujanCoefficientConstraints (coordinateSource coordinateSource_pairing)
open RamanujanCanonicalOptimizer (packetMultipleTransform coefficient_packet_synthesis)
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteGramMultipleConstraint

variable {κ : Type*} [Fintype κ]

def rows (n : ℕ) (e : κ ↪ Fin n) : κ → QHilbert :=
  sourceRows (packet_independent n) (RamanujanMultipleConstraints.sources n e)

/-- Legal residue-unit interpolants prove rank in the actual Q metric. -/
theorem rows_independent (n : ℕ) (e : κ ↪ Fin n) :
    LinearIndependent ℝ (rows n e) := by
  classical
  apply sourceRows_independent_of_interpolants
  intro j
  refine ⟨RamanujanMultipleConstraints.constrainedCoefficients n e
    (fun i => if i = j then 1 else 0), ?_⟩
  intro i
  change (∑ k, RamanujanMultipleConstraints.constrainedCoefficients n e
    (fun i => if i = j then 1 else 0) k * coordinateSource n ((e i).val + 2) k) = _
  rw [← coordinateSource_pairing]
  exact RamanujanMultipleConstraints.prescribed_coordinates n e
    (fun i => if i = j then 1 else 0) i

def constraintGram (n : ℕ) (e : κ ↪ Fin n) : Matrix κ κ ℝ :=
  gramMatrix (rows n e)

theorem constraintGram_entry (n : ℕ) (e : κ ↪ Fin n) (i j : κ) :
    constraintGram n e i j = ∑ k,
      inverseSource (packet_independent n) (coordinateSource n ((e j).val + 2)) k *
        coordinateSource n ((e i).val + 2) k :=
  sourceRows_gram (packet_independent n) (RamanujanMultipleConstraints.sources n e) i j

theorem constraintGram_det_pos [DecidableEq κ] (n : ℕ) (e : κ ↪ Fin n) :
    0 < (constraintGram n e).det := gramMatrix_det_pos (rows_independent n e)

def defect (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (j : κ) : ℝ :=
  t j - packetMultipleTransform n (packetCoefficients n) ((e j).val + 2)

theorem mismatch_eq (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    mismatch (packet_independent n) (RamanujanMultipleConstraints.sources n e)
      qOne t = defect n e t := by
  funext j
  unfold mismatch defect
  rw [coordinateSource_pairing]
  rfl

def constrainedCoefficients (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) : Fin n → ℝ :=
  RiemannResearch.Analysis.FiniteGramMultipleConstraint.coefficients (packet_independent n) (RamanujanMultipleConstraints.sources n e)
    (rows_independent n e) qOne t

def constrainedCandidate (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) : QHilbert :=
  Fintype.linearCombination ℝ (packetFamily n) (constrainedCoefficients n e t)

def constraintCost (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) : ℝ :=
  capacity (rows_independent n e) (defect n e t)

theorem coefficients_exact (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    constrainedCoefficients n e t = packetCoefficients n +
      ∑ j, inverseSource (rows_independent n e) (defect n e t) j •
        inverseSource (packet_independent n) (coordinateSource n ((e j).val + 2)) := by
  change inverseCoeff (packet_independent n) qOne +
    rowLift (packet_independent n) (RamanujanMultipleConstraints.sources n e)
      (inverseSource (rows_independent n e)
        (mismatch (packet_independent n) (RamanujanMultipleConstraints.sources n e) qOne t)) = _
  rw [mismatch_eq]
  rfl

theorem prescribed_coordinates (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (j : κ) :
    packetMultipleTransform n (constrainedCoefficients n e t) ((e j).val + 2) = t j := by
  rw [coordinateSource_pairing]
  exact coefficients_source (packet_independent n) (RamanujanMultipleConstraints.sources n e)
    (rows_independent n e) qOne t j

theorem toPareto_packetSynthesis (n : ℕ) (a : Fin n → ℝ) :
    toPareto (Fintype.linearCombination ℝ (packetFamily n) a) =
      Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a := by
  change toParetoLinear (∑ i, a i • QRamanujanPackets.qRamanujanPacket (i.val + 2)) = _
  simp only [map_sum, map_smul]
  change (∑ i : Fin n, a i • toPareto
    (QRamanujanPackets.qRamanujanPacket (i.val + 2))) = _
  simp only [RamanujanPrimeCoordinates.toPareto_packet]
  rfl

theorem toPareto_packetResidual (n : ℕ) (a : Fin n → ℝ) :
    toPareto (qOne - Fintype.linearCombination ℝ (packetFamily n) a) =
      hilbertOne - Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a := by
  change toParetoLinear (qOne - Fintype.linearCombination ℝ (packetFamily n) a) = _
  rw [map_sub]
  change toPareto qOne - toPareto
    (Fintype.linearCombination ℝ (packetFamily n) a) = _
  rw [toPareto_qOne, toPareto_packetSynthesis]

theorem candidate_coordinates (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) (j : κ) :
    SquarefreeMobiusProjection.qCoefficientCLM ((e j).val + 2)
      (constrainedCandidate n e t) = t j := by
  change CoefficientStabilization.coefficientCLM ((e j).val + 2)
    (toPareto (Fintype.linearCombination ℝ (packetFamily n)
      (constrainedCoefficients n e t))) = _
  rw [toPareto_packetSynthesis, coefficient_packet_synthesis _ _ _ (by omega)]
  exact prescribed_coordinates n e t j

theorem candidate_error_exact (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    ‖qOne - constrainedCandidate n e t‖ ^ 2 =
      1 - packetMass n + constraintCost n e t := by
  have h := coefficients_energy (packet_independent n)
    (RamanujanMultipleConstraints.sources n e) (rows_independent n e) qOne t
  rw [mismatch_eq] at h
  change ‖qOne - constrainedCandidate n e t‖ ^ 2 =
    ‖qOne - packetCandidate n‖ ^ 2 + constraintCost n e t at h
  rw [packet_error] at h
  exact h

theorem cost_inverseGram [DecidableEq κ] (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    constraintCost n e t = dotProduct (defect n e t)
      ((constraintGram n e)⁻¹.mulVec (defect n e t)) := by
  rw [constraintGram, gramMatrix_inverseSource (rows_independent n e)]
  unfold constraintCost capacity dotProduct
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem constrained_completion (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ)
    (a : Fin n → ℝ)
    (ha : ∀ j, packetMultipleTransform n a ((e j).val + 2) = t j) :
    ‖qOne - Fintype.linearCombination ℝ (packetFamily n) a‖ ^ 2 =
      1 - packetMass n + constraintCost n e t +
        ‖Fintype.linearCombination ℝ (packetFamily n)
          (a - constrainedCoefficients n e t)‖ ^ 2 := by
  have hc : ∀ j, (∑ i, a i * RamanujanMultipleConstraints.sources n e j i) = t j := by
    intro j
    exact (coordinateSource_pairing n ((e j).val + 2) a).symm.trans (ha j)
  have h := coefficients_completion (packet_independent n)
    (RamanujanMultipleConstraints.sources n e) (rows_independent n e) qOne t a hc
  change _ = ‖qOne - constrainedCandidate n e t‖ ^ 2 + _ at h
  rw [candidate_error_exact] at h
  exact h

theorem constrained_optimal_iff (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ)
    (a : Fin n → ℝ)
    (ha : ∀ j, packetMultipleTransform n a ((e j).val + 2) = t j) :
    ‖qOne - Fintype.linearCombination ℝ (packetFamily n) a‖ ^ 2 =
      1 - packetMass n + constraintCost n e t ↔ a = constrainedCoefficients n e t := by
  constructor
  · intro he
    apply coefficients_unique (packet_independent n)
      (RamanujanMultipleConstraints.sources n e) (rows_independent n e) qOne t a
    · intro j
      exact (coordinateSource_pairing n ((e j).val + 2) a).symm.trans (ha j)
    · change _ = ‖qOne - constrainedCandidate n e t‖ ^ 2
      rwa [candidate_error_exact]
  · rintro rfl
    exact candidate_error_exact n e t

/-- The Pareto constrained coefficient array interpreted in the Q dictionary. -/
def paretoCandidateLift (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) : QHilbert :=
  Fintype.linearCombination ℝ (packetFamily n)
    (RamanujanMultipleConstraints.constrainedCoefficients n e t)

theorem packet_metric_identity (n : ℕ) (a : Fin n → ℝ) :
    zetaTwo * ‖qOne - Fintype.linearCombination ℝ (packetFamily n) a‖ ^ 2 =
      ‖hilbertOne - Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 +
      metricCorrection (qOne - Fintype.linearCombination ℝ (packetFamily n) a) := by
  rw [norm_identity, toPareto_packetResidual]

/-- Neither the Q correction nor the Pareto displacement is discarded. -/
theorem metric_lower_identity (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    zetaTwo * ‖qOne - constrainedCandidate n e t‖ ^ 2 =
      ‖hilbertOne - RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 +
      ‖toPareto (constrainedCandidate n e t) -
        RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 +
      metricCorrection (qOne - constrainedCandidate n e t) := by
  have h := RiemannResearch.Analysis.FiniteConstrainedMetricComparison.lower_identity
    (finitePacket_independent n) (packet_independent n)
    (RamanujanMultipleConstraints.sources n e)
    (RamanujanMultipleConstraints.rows_independent n e) (rows_independent n e)
    hilbertOne qOne t zetaTwo
    (fun a => metricCorrection (qOne - Fintype.linearCombination ℝ (packetFamily n) a))
    (packet_metric_identity n)
  simpa only [constrainedCandidate, constrainedCoefficients,
    RamanujanMultipleConstraints.constrainedCandidate,
    RamanujanMultipleConstraints.constrainedCoefficients,
    toPareto_packetSynthesis, map_sub] using h

theorem metric_upper_identity (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    ‖hilbertOne - RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 +
      metricCorrection (qOne - paretoCandidateLift n e t) =
      zetaTwo * ‖qOne - constrainedCandidate n e t‖ ^ 2 +
        zetaTwo * ‖paretoCandidateLift n e t - constrainedCandidate n e t‖ ^ 2 := by
  have h := RiemannResearch.Analysis.FiniteConstrainedMetricComparison.upper_identity
    (finitePacket_independent n) (packet_independent n)
    (RamanujanMultipleConstraints.sources n e)
    (RamanujanMultipleConstraints.rows_independent n e) (rows_independent n e)
    hilbertOne qOne t zetaTwo
    (fun a => metricCorrection (qOne - Fintype.linearCombination ℝ (packetFamily n) a))
    (packet_metric_identity n)
  simpa only [constrainedCandidate, constrainedCoefficients, paretoCandidateLift,
    RamanujanMultipleConstraints.constrainedCandidate,
    RamanujanMultipleConstraints.constrainedCoefficients, map_sub] using h

theorem correction_balance (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    metricCorrection (qOne - paretoCandidateLift n e t) =
      metricCorrection (qOne - constrainedCandidate n e t) +
      ‖toPareto (constrainedCandidate n e t) -
        RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 +
      zetaTwo * ‖paretoCandidateLift n e t - constrainedCandidate n e t‖ ^ 2 := by
  linarith [metric_lower_identity n e t, metric_upper_identity n e t]

theorem correction_equal_iff (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    metricCorrection (qOne - paretoCandidateLift n e t) =
      metricCorrection (qOne - constrainedCandidate n e t) ↔
    RamanujanMultipleConstraints.constrainedCoefficients n e t =
      constrainedCoefficients n e t := by
  exact RiemannResearch.Analysis.FiniteConstrainedMetricComparison.correction_equal_iff
    (finitePacket_independent n) (packet_independent n)
    (RamanujanMultipleConstraints.sources n e)
    (RamanujanMultipleConstraints.rows_independent n e) (rows_independent n e)
    hilbertOne qOne t zetaTwo
    (fun a => metricCorrection (qOne - Fintype.linearCombination ℝ (packetFamily n) a))
    (packet_metric_identity n) zetaTwo_pos.le

/-- The comparison constants hold for every finite set and every prescribed vector. -/
theorem error_bounds (n : ℕ) (e : κ ↪ Fin n) (t : κ → ℝ) :
    ‖hilbertOne - RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 ≤
      zetaTwo * ‖qOne - constrainedCandidate n e t‖ ^ 2 ∧
    zetaTwo * ‖qOne - constrainedCandidate n e t‖ ^ 2 ≤
      2 * ‖hilbertOne - RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 := by
  constructor
  · have h := metric_lower_identity n e t
    have hc := metricCorrection_nonneg (qOne - constrainedCandidate n e t)
    have hs := sq_nonneg ‖toPareto (constrainedCandidate n e t) -
      RamanujanMultipleConstraints.constrainedCandidate n e t‖
    linarith
  · have hu := metric_upper_identity n e t
    have hn := mul_nonneg zetaTwo_pos.le
      (sq_nonneg ‖paretoCandidateLift n e t - constrainedCandidate n e t‖)
    have hm := packet_metric_identity n
      (RamanujanMultipleConstraints.constrainedCoefficients n e t)
    have hb := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq
      (qOne - paretoCandidateLift n e t)
    unfold paretoCandidateLift at hb
    rw [toPareto_packetResidual] at hb
    change zetaTwo * ‖qOne - paretoCandidateLift n e t‖ ^ 2 ≤
      2 * ‖hilbertOne - RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 at hb
    change zetaTwo * ‖qOne - paretoCandidateLift n e t‖ ^ 2 =
      ‖hilbertOne - RamanujanMultipleConstraints.constrainedCandidate n e t‖ ^ 2 +
        metricCorrection (qOne - paretoCandidateLift n e t) at hm
    linarith

/-- Constraints and target values may move arbitrarily: vanishing constrained
minimum error is equivalent in the actual two metrics. No cofinality is needed. -/
theorem moving_error_tendsto_zero_iff {α : Type*} {l : Filter α}
    (N : α → ℕ) (e : ∀ i, κ ↪ Fin (N i)) (t : α → κ → ℝ) :
    Tendsto (fun i => ‖qOne - constrainedCandidate (N i) (e i) (t i)‖ ^ 2) l (𝓝 0) ↔
    Tendsto (fun i => ‖hilbertOne -
      RamanujanMultipleConstraints.constrainedCandidate (N i) (e i) (t i)‖ ^ 2)
      l (𝓝 0) := by
  constructor
  · intro h
    have hupper : Tendsto (fun i => zetaTwo *
        ‖qOne - constrainedCandidate (N i) (e i) (t i)‖ ^ 2) l (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul h
    exact squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall (fun i => (error_bounds (N i) (e i) (t i)).1)) hupper
  · intro h
    have hupper : Tendsto (fun i => (2 / zetaTwo) *
        ‖hilbertOne - RamanujanMultipleConstraints.constrainedCandidate
          (N i) (e i) (t i)‖ ^ 2) l (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul h
    have hbound : ∀ i, ‖qOne - constrainedCandidate (N i) (e i) (t i)‖ ^ 2 ≤
        (2 / zetaTwo) * ‖hilbertOne -
          RamanujanMultipleConstraints.constrainedCandidate (N i) (e i) (t i)‖ ^ 2 := by
      intro i
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ zetaTwo_pos).mpr
      simpa only [mul_comm] using (error_bounds (N i) (e i) (t i)).2
    exact squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _))
      (Eventually.of_forall hbound) hupper

end RiemannResearch.RH.QRamanujanMultipleConstraints
