import RiemannResearch.RH.QParetoOptimizerError
import RiemannResearch.RH.QRamanujanCanonicalOptimizer
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.RamanujanPrimeCoordinates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Exact metric error identity for the actual P and Q arithmetic optimizers.
Source: user-requested Ramanujan transfers, 23 October 2026. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanMetricOptimizer
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open QParetoGramComparison QParetoMetric
open RiemannResearch.Analysis.FiniteHilbertGram

theorem packet_pFit (n : ℕ) :
    toPareto (pFit (QRamanujanCanonicalOptimizer.packet_independent n) qOne) =
      RamanujanCanonicalOptimizer.packetCandidate n := by
  let v := QRamanujanCanonicalOptimizer.packetFamily n
  let hv := QRamanujanCanonicalOptimizer.packet_independent n
  let c := inverseCoeff (paretoFamily_independent hv) (toPareto qOne)
  have hf : paretoFamily v = (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) := by
    funext i
    exact RamanujanPrimeCoordinates.toPareto_packet _
  have hfit : toPareto (pFit hv qOne) =
      Fintype.linearCombination ℝ (paretoFamily v) c := by
    exact toPareto_synthesis v c
  have hm : toPareto (pFit hv qOne) ∈ CoefficientStabilization.finiteSpace n := by
    have h := synthesis_mem (paretoFamily v) c
    rw [← hfit] at h
    change toPareto (pFit hv qOne) ∈ Submodule.span ℝ (Set.range (paretoFamily v)) at h
    rw [hf, finitePacket_span_eq] at h
    exact h
  rw [RamanujanCanonicalOptimizer.packetCandidate_eq_projection]
  change toPareto (pFit hv qOne) = (CoefficientStabilization.finiteSpace n).starProjection hilbertOne
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hm
  intro w hw
  have hp : w ∈ synthesisSpan (paretoFamily v) := by
    change w ∈ Submodule.span ℝ (Set.range (paretoFamily v))
    rw [hf, finitePacket_span_eq]
    exact hw
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hp
  obtain ⟨a, rfl⟩ := hp
  have ho := residual_orthogonal (paretoFamily_independent hv) (toPareto qOne) a
  change inner ℝ (toPareto qOne - Fintype.linearCombination ℝ (paretoFamily v) c)
    (Fintype.linearCombination ℝ (paretoFamily v) a) = 0 at ho
  rw [← hfit, toPareto_qOne] at ho
  exact ho

theorem packet_qFit (n : ℕ) :
    qFit (QRamanujanCanonicalOptimizer.packet_independent n) qOne =
      QRamanujanCanonicalOptimizer.packetCandidate n := rfl

/-- Exact difference between the actual Q and P optimal errors. -/
theorem packet_error_metric_identity (n : ℕ) :
    zetaTwo * (1 - QRamanujanCanonicalOptimizer.packetMass n) =
      1 - RamanujanCanonicalOptimizer.packetMass n +
      ‖toPareto (QRamanujanCanonicalOptimizer.packetCandidate n) -
        RamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 +
      metricCorrection (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) := by
  have h := optimizer_error_lower_identity
    (QRamanujanCanonicalOptimizer.packet_independent n) qOne
  have hp : toPareto (qOne -
      pFit (QRamanujanCanonicalOptimizer.packet_independent n) qOne) =
      hilbertOne - RamanujanCanonicalOptimizer.packetCandidate n := by
    change toParetoLinear (qOne - _) = _
    rw [map_sub]
    exact congrArg₂ HSub.hSub toPareto_qOne (packet_pFit n)
  have hd : toPareto
      (qFit (QRamanujanCanonicalOptimizer.packet_independent n) qOne -
        pFit (QRamanujanCanonicalOptimizer.packet_independent n) qOne) =
      toPareto (QRamanujanCanonicalOptimizer.packetCandidate n) -
        RamanujanCanonicalOptimizer.packetCandidate n := by
    change toParetoLinear (_ - _) = _
    rw [map_sub]
    exact congrArg₂ HSub.hSub (congrArg toPareto (packet_qFit n)) (packet_pFit n)
  rw [hp, hd, packet_qFit, QRamanujanCanonicalOptimizer.packet_error,
    RamanujanCanonicalOptimizer.packet_error] at h
  exact h

/-- Finite optimizers cannot coincide with the target, so the lower comparison is strict. -/
theorem packet_error_strict (n : ℕ) :
    1 - RamanujanCanonicalOptimizer.packetMass n <
      zetaTwo * (1 - QRamanujanCanonicalOptimizer.packetMass n) := by
  have hnon : qOne ≠ qFit (QRamanujanCanonicalOptimizer.packet_independent n) qOne := by
    intro he
    have h := packet_error_metric_identity n
    have hz : qOne - QRamanujanCanonicalOptimizer.packetCandidate n = 0 :=
      sub_eq_zero.mpr he
    have hq : 1 - QRamanujanCanonicalOptimizer.packetMass n = 0 := by
      rw [← QRamanujanCanonicalOptimizer.packet_error, hz, norm_zero]
      norm_num
    rw [hq, mul_zero] at h
    have hc := metricCorrection_nonneg
      (qOne - QRamanujanCanonicalOptimizer.packetCandidate n)
    have hs := sq_nonneg ‖toPareto (QRamanujanCanonicalOptimizer.packetCandidate n) -
      RamanujanCanonicalOptimizer.packetCandidate n‖
    have hp := (RamanujanCanonicalOptimizer.packetMass_bounds n).2
    linarith
  have h := optimizer_error_strict
    (QRamanujanCanonicalOptimizer.packet_independent n) qOne hnon
  have hp : toPareto (qOne -
      pFit (QRamanujanCanonicalOptimizer.packet_independent n) qOne) =
      hilbertOne - RamanujanCanonicalOptimizer.packetCandidate n := by
    change toParetoLinear (qOne - _) = _
    rw [map_sub]
    exact congrArg₂ HSub.hSub toPareto_qOne (packet_pFit n)
  rw [hp, packet_qFit, QRamanujanCanonicalOptimizer.packet_error,
    RamanujanCanonicalOptimizer.packet_error] at h
  exact h

end RiemannResearch.RH.RamanujanMetricOptimizer
