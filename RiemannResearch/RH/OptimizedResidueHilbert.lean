import RiemannResearch.RH.ThresholdHilbertLegal
import RiemannResearch.RH.OptimizedResiduePackets
import RiemannResearch.RH.GibbsLegalSeed

/-!
# The optimized residue corrections in the actual Pareto Hilbert space

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md, §§5–6.
The sequence-to-Hilbert identification, finite legality, zero means, coordinate
support, and nonzero free direction are discharged for the concrete packets.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem hilbertSequence_sub_packets (f g : ThresholdHilbert) :
    hilbertSequence (f - g) = hilbertSequence f - hilbertSequence g :=
  hilbertSequenceLinear.map_sub f g

def optimizedResidueHilbert : ThresholdHilbert :=
  (3 / 4 : ℝ) • digitHilbert 2 1 (by norm_num) (by omega) +
  (1 / 2 : ℝ) • digitHilbert 3 1 (by norm_num) (by omega) -
  (1 / 4 : ℝ) • digitHilbert 6 1 (by norm_num) (by omega)

def complementaryResidueHilbert : ThresholdHilbert :=
  digitHilbert 2 1 (by norm_num) (by omega) - optimizedResidueHilbert

@[simp] theorem optimizedResidueHilbert_sequence :
    hilbertSequence optimizedResidueHilbert = optimizedResidueSeed := by
  unfold optimizedResidueHilbert
  rw [hilbertSequence_sub_packets, hilbertSequence_add]
  simp only [hilbertSequence_smul, hilbertSequence_digitHilbert]
  funext k
  simp [optimizedResidueSeed, digitSequence, residue]

@[simp] theorem complementaryResidueHilbert_sequence :
    hilbertSequence complementaryResidueHilbert = complementaryResidueSeed := by
  rw [complementaryResidueHilbert, hilbertSequence_sub_packets,
    optimizedResidueHilbert_sequence, hilbertSequence_digitHilbert]
  funext k
  simp [complementaryResidueSeed, digitSequence, residue]

theorem optimizedResidueHilbert_legal :
    optimizedResidueHilbert ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  change hilbertSequence optimizedResidueHilbert ∈ legalSeedSpan ({2, 3} : Set ℕ)
  simpa only [optimizedResidueHilbert_sequence] using optimizedResidueSeed_legal

theorem complementaryResidueHilbert_legal :
    complementaryResidueHilbert ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  change hilbertSequence complementaryResidueHilbert ∈ legalSeedSpan ({2, 3} : Set ℕ)
  simpa only [complementaryResidueHilbert_sequence] using complementaryResidueSeed_legal

def optimizedCorrectionHilbert (n : ℕ) (hn : 0 < n) : ThresholdHilbert :=
  (1 / (n : ℝ)) • (hilbertDilation n hn optimizedResidueHilbert -
    hilbertDilation (n + 1) (by omega) optimizedResidueHilbert)

def complementaryCorrectionHilbert (n : ℕ) (hn : 0 < n) : ThresholdHilbert :=
  (1 / (n : ℝ)) • (hilbertDilation n hn complementaryResidueHilbert -
    hilbertDilation (n + 1) (by omega) complementaryResidueHilbert)

@[simp] theorem optimizedCorrectionHilbert_sequence (n : ℕ) (hn : 0 < n) :
    hilbertSequence (optimizedCorrectionHilbert n hn) = optimizedCorrectionSequence n := by
  rw [optimizedCorrectionHilbert, hilbertSequence_smul, hilbertSequence_sub_packets]
  simp only [hilbertDilation_sequence, optimizedResidueHilbert_sequence]
  funext k
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, optimizedCorrectionSequence,
    nearbyDilationPacket, dilation, Nat.cast_add, Nat.cast_one]
  ring

@[simp] theorem complementaryCorrectionHilbert_sequence (n : ℕ) (hn : 0 < n) :
    hilbertSequence (complementaryCorrectionHilbert n hn) = complementaryCorrectionSequence n := by
  rw [complementaryCorrectionHilbert, hilbertSequence_smul, hilbertSequence_sub_packets]
  simp only [hilbertDilation_sequence, complementaryResidueHilbert_sequence]
  funext k
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, complementaryCorrectionSequence,
    nearbyDilationPacket, dilation, Nat.cast_add, Nat.cast_one]
  ring

theorem optimizedCorrectionHilbert_legal (n : ℕ) (hn : 0 < n) :
    optimizedCorrectionHilbert n hn ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  exact (hilbertLegalSubspace ({2, 3} : Set ℕ)).smul_mem _
    ((hilbertLegalSubspace ({2, 3} : Set ℕ)).sub_mem
      (hilbertLegal_dilation _ optimizedResidueHilbert_legal n hn)
      (hilbertLegal_dilation _ optimizedResidueHilbert_legal (n + 1) (by omega)))

theorem complementaryCorrectionHilbert_legal (n : ℕ) (hn : 0 < n) :
    complementaryCorrectionHilbert n hn ∈ hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  exact (hilbertLegalSubspace ({2, 3} : Set ℕ)).smul_mem _
    ((hilbertLegalSubspace ({2, 3} : Set ℕ)).sub_mem
      (hilbertLegal_dilation _ complementaryResidueHilbert_legal n hn)
      (hilbertLegal_dilation _ complementaryResidueHilbert_legal (n + 1) (by omega)))

theorem optimizedCorrectionHilbert_mean (n : ℕ) (hn : 0 < n) :
    inner ℝ (optimizedCorrectionHilbert n hn) hilbertOne = 0 := by
  rw [optimizedCorrectionHilbert, real_inner_smul_left, inner_sub_left,
    hilbert_inner_one, hilbert_inner_one,
    hilbertDilation_mean, hilbertDilation_mean]
  ring

theorem complementaryCorrectionHilbert_mean (n : ℕ) (hn : 0 < n) :
    inner ℝ (complementaryCorrectionHilbert n hn) hilbertOne = 0 := by
  rw [complementaryCorrectionHilbert, real_inner_smul_left, inner_sub_left,
    hilbert_inner_one, hilbert_inner_one,
    hilbertDilation_mean, hilbertDilation_mean]
  ring

theorem optimizedCorrectionHilbert_below (n k : ℕ) (hn : 0 < n) (hk : k < n) :
    hilbertSequence (optimizedCorrectionHilbert n hn) k = 0 := by
  rw [optimizedCorrectionHilbert_sequence]
  exact optimizedCorrectionSequence_below n k hk

theorem optimizedCorrectionHilbert_at (n : ℕ) (hn : 0 < n) :
    hilbertSequence (optimizedCorrectionHilbert n hn) n = 1 := by
  rw [optimizedCorrectionHilbert_sequence]
  exact optimizedCorrectionSequence_at n hn

theorem complementaryCorrectionHilbert_through (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    hilbertSequence (complementaryCorrectionHilbert n hn) k = 0 := by
  rw [complementaryCorrectionHilbert_sequence]
  exact complementaryCorrectionSequence_through n k hn hk

theorem complementaryCorrectionHilbert_twice (n : ℕ) (hn : 0 < n) :
    hilbertSequence (complementaryCorrectionHilbert n hn) (2 * n) = -(1 / 2) := by
  rw [complementaryCorrectionHilbert_sequence]
  exact complementaryCorrectionSequence_twice n hn

theorem complementaryCorrectionHilbert_ne_zero (n : ℕ) (hn : 0 < n) :
    complementaryCorrectionHilbert n hn ≠ 0 := by
  intro h
  have hv := complementaryCorrectionHilbert_twice n hn
  rw [h] at hv
  have hz : hilbertSequence (0 : ThresholdHilbert) = 0 := hilbertSequenceLinear.map_zero
  rw [hz] at hv
  norm_num at hv

end
end RiemannResearch.RH.Pareto
