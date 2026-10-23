import RiemannResearch.RH.QParetoInverseMetricDefect
import RiemannResearch.RH.QRamanujanCanonicalOptimizer
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.RamanujanPrimeCoordinates
import Mathlib.Tactic.Ring

/-! Strict comparison of the actual arithmetic inverse Gram matrices.
Source: user-requested Ramanujan transfers, 23 October 2026. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanInverseMetric
open Pareto ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer
open QRamanujanCanonicalOptimizer QParetoGramComparison RamanujanPrimeCoordinates
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity

theorem packet_paretoGram_eq (n : ℕ) :
    gramMatrix (paretoFamily (packetFamily n)) = finitePacketGram n := by
  ext i j
  simp only [gramMatrix, paretoFamily, packetFamily, toPareto_packet, finitePacketGram]

/-- Strict inverse-metric comparison for every actual finite Ramanujan source. -/
theorem packet_inverse_quadratic_strict_iff (n : ℕ) (b : Fin n → ℝ) :
    dotProduct b ((gramMatrix (packetFamily n))⁻¹.mulVec b) <
      zetaTwo * dotProduct b ((finitePacketGram n)⁻¹.mulVec b) ↔ b ≠ 0 := by
  have h := capacity_upper_strict_iff (packet_independent n) b
  rw [capacity_eq_matrix] at h
  have hp : capacity (paretoFamily_independent (packet_independent n)) b =
      dotProduct b ((finitePacketGram n)⁻¹.mulVec b) := by
    rw [← packet_paretoGram_eq]
    rw [gramMatrix_inverseSource (paretoFamily_independent (packet_independent n))]
    unfold capacity dotProduct
    apply Finset.sum_congr rfl
    intro i _
    ring
  rwa [hp] at h

end RiemannResearch.RH.RamanujanInverseMetric
