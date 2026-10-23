import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ParetoResidueMean
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-!
# Canonical legal approximants in the integrated Ramanujan basis

Source: user-requested duality program, 23 October 2026.
The finite packet Gram matrix is the actual complete Pareto Gram matrix.
The target source is von Mangoldt, and every mixed conductor is retained.
The unique packet minimizer is proved equal to the residue minimizer.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanCanonicalOptimizer
open Pareto Pareto.CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram

def packetCoefficients (n : ℕ) : Fin n → ℝ :=
  inverseCoeff (finitePacket_independent n) hilbertOne

def packetCandidate (n : ℕ) : ThresholdHilbert :=
  Fintype.linearCombination ℝ
    (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
    (packetCoefficients n)

def packetMass (n : ℕ) : ℝ :=
  ∑ i : Fin n, packetCoefficients n i * ArithmeticFunction.vonMangoldt (i.val + 2)

theorem packetCandidate_eq_projection (n : ℕ) :
    packetCandidate n = CoefficientStabilization.projection n := by
  have hmem : packetCandidate n ∈ finiteSpace n := by
    have h := synthesis_mem
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) (packetCoefficients n)
    change packetCandidate n ∈ Submodule.span ℝ
      (Set.range (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))) at h
    rw [finitePacket_span_eq] at h
    exact h
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  intro w hw
  have hp : w ∈ synthesisSpan
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) := by
    change w ∈ Submodule.span ℝ
      (Set.range (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)))
    rw [finitePacket_span_eq]
    exact hw
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hp
  obtain ⟨a, rfl⟩ := hp
  exact residual_orthogonal (finitePacket_independent n) hilbertOne a

theorem packet_inner_one (q : ℕ) :
    inner ℝ (ramanujanPacketHilbert q) hilbertOne =
      ArithmeticFunction.vonMangoldt q := by
  rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
    paretoMean_ramanujanPacket]

theorem packetCoefficients_eq_inverseGram (n : ℕ) :
    packetCoefficients n = (finitePacketGram n)⁻¹.mulVec
      (fun i : Fin n => ArithmeticFunction.vonMangoldt (i.val + 2)) := by
  have hs : cross (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      hilbertOne = (fun i : Fin n => ArithmeticFunction.vonMangoldt (i.val + 2)) := by
    funext i
    exact packet_inner_one (i.val + 2)
  rw [finitePacketGram, gramMatrix_inverseSource (finitePacket_independent n)]
  change (gramEquiv (finitePacket_independent n)).symm
      (cross (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) hilbertOne) = _
  rw [hs]
  rfl

theorem packet_normal (n : ℕ) (i : Fin n) :
    inner ℝ (ramanujanPacketHilbert (i.val + 2)) (packetCandidate n) =
      ArithmeticFunction.vonMangoldt (i.val + 2) := by
  have h := inverseCoeff_normal (finitePacket_independent n) hilbertOne i
  change inner ℝ (ramanujanPacketHilbert (i.val + 2)) (packetCandidate n) =
    inner ℝ (ramanujanPacketHilbert (i.val + 2)) hilbertOne at h
  exact h.trans (packet_inner_one _)

theorem packetMass_eq_inverseGram (n : ℕ) :
    packetMass n = dotProduct
      (fun i : Fin n => ArithmeticFunction.vonMangoldt (i.val + 2))
      ((finitePacketGram n)⁻¹.mulVec
        (fun i : Fin n => ArithmeticFunction.vonMangoldt (i.val + 2))) := by
  unfold packetMass dotProduct
  rw [packetCoefficients_eq_inverseGram]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem packet_energy (n : ℕ) : ‖packetCandidate n‖ ^ 2 = packetMass n := by
  rw [packetCandidate, gram_quadratic]
  apply Finset.sum_congr rfl
  intro i _
  change packetCoefficients n i *
    inner ℝ (ramanujanPacketHilbert (i.val + 2)) (packetCandidate n) = _
  rw [packet_normal]

theorem packet_error (n : ℕ) :
    ‖hilbertOne - packetCandidate n‖ ^ 2 = 1 - packetMass n := by
  have h := residual_schur_value (finitePacket_independent n) hilbertOne
  simpa only [hilbertOne_norm_sq, cross, packet_inner_one,
    packetCandidate, packetCoefficients, packetMass] using h

theorem packet_completion (n : ℕ) (a : Fin n → ℝ) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
    1 - packetMass n + ‖Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (a - packetCoefficients n)‖ ^ 2 := by
  have h := residual_completion (finitePacket_independent n) hilbertOne a
  change _ = ‖hilbertOne - packetCandidate n‖ ^ 2 + _ at h
  rw [packet_error] at h
  exact h

theorem packet_optimal_iff (n : ℕ) (a : Fin n → ℝ) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
      1 - packetMass n ↔ a = packetCoefficients n := by
  constructor
  · intro h
    apply residual_minimizer_unique (finitePacket_independent n) hilbertOne a
    simpa only [hilbertOne_norm_sq, cross, packet_inner_one,
      packetCoefficients, packetMass] using h
  · rintro rfl
    exact packet_error n
end RiemannResearch.RH.RamanujanCanonicalOptimizer
