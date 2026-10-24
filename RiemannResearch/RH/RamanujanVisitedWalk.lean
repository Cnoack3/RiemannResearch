import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.RamanujanCanonicalOptimizer
import RiemannResearch.RH.QRamanujanCanonicalOptimizer
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.QRamanujanSaturationCriteria
import Mathlib.Tactic.Linarith

/-!
# Arbitrary visited Pareto and Q Ramanujan dictionaries

Source: sixth Ramanujan transfer program, 24 October 2026.
A draw may repeat conductors and omit arbitrarily many conductors. Its actual
orthogonal fits always converge, with the precise missed-span defect exposed.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.RamanujanVisitedWalk
open Pareto ZetaTwoHilbert
open RiemannResearch.Analysis.ExhaustiveWalk

def paretoPacket (j : ℕ) : ThresholdHilbert := ramanujanPacketHilbert (j + 2)
def qPacket (j : ℕ) : QHilbert := QRamanujanPackets.qRamanujanPacket (j + 2)

def paretoCandidate (draw : ℕ → ℕ) (n : ℕ) : ThresholdHilbert :=
  (walkSpan paretoPacket draw n).starProjection hilbertOne

def qCandidate (draw : ℕ → ℕ) (n : ℕ) : QHilbert :=
  (walkSpan qPacket draw n).starProjection qOne

theorem pareto_dictionaryClosure :
    dictionaryClosure paretoPacket = CoefficientStabilization.closedSpace := by
  change (Submodule.span ℝ (Set.range paretoPacket)).topologicalClosure =
    (Submodule.span ℝ (Set.range CoefficientStabilization.residueAtom)).topologicalClosure
  congr 1
  calc
    _ = ⨆ n, walkSpan paretoPacket id n := (iSup_walkSpan _ _ Function.surjective_id).symm
    _ = ⨆ n, walkSpan CoefficientStabilization.residueAtom id n := by
      congr 1
      funext n
      simpa only [walkSpan, paretoPacket, id_eq] using finitePacket_span_eq n
    _ = _ := iSup_walkSpan _ _ Function.surjective_id

theorem q_dictionaryClosure : dictionaryClosure qPacket = QFullResidueProjection.closure := by
  unfold dictionaryClosure QFullResidueProjection.closure QFullResidueProjection.legalSpan
  congr 1
  calc
    _ = ⨆ n, walkSpan qPacket id n := (iSup_walkSpan _ _ Function.surjective_id).symm
    _ = ⨆ n, walkSpan (fun i : ℕ => qResidue (i + 2)) id n := by
      congr 1
      funext n
      have hs := QRamanujanCanonicalOptimizer.packet_span_eq n
      unfold QRamanujanCanonicalOptimizer.packetFamily at hs
      simpa only [walkSpan, qPacket, id_eq] using hs
    _ = _ := iSup_walkSpan _ _ Function.surjective_id

theorem paretoCandidate_tendsto (draw : ℕ → ℕ) :
    Tendsto (paretoCandidate draw) atTop (𝓝 (visitedProjection paretoPacket draw hilbertOne)) :=
  walkProjection_tendsto_visited paretoPacket draw hilbertOne

theorem qCandidate_tendsto (draw : ℕ → ℕ) :
    Tendsto (qCandidate draw) atTop (𝓝 (visitedProjection qPacket draw qOne)) :=
  walkProjection_tendsto_visited qPacket draw qOne

theorem pareto_visited_error_exact (draw : ℕ → ℕ) :
    visitedError paretoPacket draw hilbertOne = CoefficientStabilization.limitEnergy +
      ‖CoefficientStabilization.limitProjection - visitedProjection paretoPacket draw hilbertOne‖ ^ 2 := by
  have h := visitedError_eq_full_add paretoPacket draw hilbertOne
  simpa only [limitingError, pareto_dictionaryClosure,
    CoefficientStabilization.limitEnergy, CoefficientStabilization.limitProjection] using h

theorem q_visited_error_exact (draw : ℕ → ℕ) :
    visitedError qPacket draw qOne = QRamanujanCanonicalOptimizer.packetLimitEnergy +
      ‖QFullResidueProjection.closure.starProjection qOne - visitedProjection qPacket draw qOne‖ ^ 2 := by
  have h := visitedError_eq_full_add qPacket draw qOne
  simpa only [limitingError, q_dictionaryClosure,
    QRamanujanCanonicalOptimizer.packetLimitEnergy] using h

/-- Norm saturation of any selected family implies saturation of the full dictionary. -/
theorem pareto_full_saturation_of_visited (draw : ℕ → ℕ)
    (h : visitedError paretoPacket draw hilbertOne = 0) :
    CoefficientStabilization.limitEnergy = 0 := by
  have he := pareto_visited_error_exact draw
  have hn : 0 ≤ CoefficientStabilization.limitEnergy := sq_nonneg _
  nlinarith [sq_nonneg ‖CoefficientStabilization.limitProjection -
    visitedProjection paretoPacket draw hilbertOne‖]

theorem q_full_saturation_of_visited (draw : ℕ → ℕ)
    (h : visitedError qPacket draw qOne = 0) :
    QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 := by
  have he := q_visited_error_exact draw
  have hn : 0 ≤ QRamanujanCanonicalOptimizer.packetLimitEnergy := sq_nonneg _
  nlinarith [sq_nonneg ‖QFullResidueProjection.closure.starProjection qOne -
    visitedProjection qPacket draw qOne‖]

end RiemannResearch.RH.RamanujanVisitedWalk
