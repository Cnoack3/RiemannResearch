import RiemannResearch.Analysis.FiniteGramNormalDefect
import RiemannResearch.RH.RamanujanCoefficientLimits
import RiemannResearch.RH.QRamanujanCanonicalOptimizer

/-! Exact actual Pareto and Q inverse-Gram normal-defect certificates. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanNormalDefect
open Pareto ZetaTwoHilbert
open RiemannResearch.Analysis.FiniteHilbertGram

def paretoDefect (n : ℕ) (a : Fin n → ℝ) : Fin n → ℝ :=
  normalDefect (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) hilbertOne a

def qDefect (n : ℕ) (a : Fin n → ℝ) : Fin n → ℝ :=
  normalDefect (QRamanujanCanonicalOptimizer.packetFamily n) qOne a

def paretoDefectEnergy (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  defectEnergy (finitePacket_independent n) hilbertOne a

def qDefectEnergy (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  defectEnergy (QRamanujanCanonicalOptimizer.packet_independent n) qOne a

theorem paretoDefect_arithmetic (n : ℕ) (a : Fin n → ℝ) (i : Fin n) :
    paretoDefect n a i =
      (∑ j, finitePacketGram n i j * a j) - ArithmeticFunction.vonMangoldt (i.val + 2) := by
  rw [paretoDefect, normalDefect_apply, RamanujanCanonicalOptimizer.packet_inner_one]
  rfl

theorem qDefect_arithmetic (n : ℕ) (a : Fin n → ℝ) (i : Fin n) :
    qDefect n a i =
      (∑ j, QRamanujanCanonicalOptimizer.packetGram n i j * a j) -
        QRamanujanCanonicalOptimizer.packetSource n i := by
  rw [qDefect, normalDefect_apply]
  rfl

theorem pareto_trial_error (n : ℕ) (a : Fin n → ℝ) :
    ‖hilbertOne - Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a‖ ^ 2 =
      1 - RamanujanCanonicalOptimizer.packetMass n + paretoDefectEnergy n a := by
  have h := residual_error_defect_identity (finitePacket_independent n) hilbertOne a
  change _ = ‖hilbertOne - RamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 + _ at h
  rw [RamanujanCanonicalOptimizer.packet_error] at h
  exact h

theorem q_trial_error (n : ℕ) (a : Fin n → ℝ) :
    ‖qOne - Fintype.linearCombination ℝ
      (QRamanujanCanonicalOptimizer.packetFamily n) a‖ ^ 2 =
      1 - QRamanujanCanonicalOptimizer.packetMass n + qDefectEnergy n a := by
  have h := residual_error_defect_identity
    (QRamanujanCanonicalOptimizer.packet_independent n) qOne a
  change _ = ‖qOne - QRamanujanCanonicalOptimizer.packetCandidate n‖ ^ 2 + _ at h
  rw [QRamanujanCanonicalOptimizer.packet_error] at h
  exact h

theorem pareto_trial_optimal_iff (n : ℕ) (a : Fin n → ℝ) :
    paretoDefectEnergy n a = 0 ↔ a = RamanujanCanonicalOptimizer.packetCoefficients n :=
  defectEnergy_zero_iff (finitePacket_independent n) hilbertOne a

theorem q_trial_optimal_iff (n : ℕ) (a : Fin n → ℝ) :
    qDefectEnergy n a = 0 ↔ a = QRamanujanCanonicalOptimizer.packetCoefficients n :=
  defectEnergy_zero_iff (QRamanujanCanonicalOptimizer.packet_independent n) qOne a

end RiemannResearch.RH.RamanujanNormalDefect
