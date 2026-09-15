/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.TwoThreeCanonicalBasis
import RiemannResearch.RH.TwoThreePacketRelations
import RiemannResearch.RH.ParetoMomentOptimizer

/-!
# The canonical basis and resonance cell in the actual finite Hilbert budget

The arithmetic canonical basis is realized by the existing Pareto Hilbert
vectors. The finite Hilbert budget is the existing `budgetHilbert` from the
moment optimizer module, not a newly defined approximation space.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
open AdjacentPacket RamanujanLaguerre
noncomputable section

/-- The canonical generators as actual vectors in the Pareto Hilbert space. -/
def canonicalHilbertFamily (M : ℕ) (i : canonicalIndices M) : ThresholdHilbert :=
  generator i.val.1 i.val.2
    (by
      obtain ⟨hpos, hupp, h3 | ⟨h2, hn⟩⟩ :=
        (mem_canonicalIndices M i.val).mp i.property
      · omega
      · omega)
    ((mem_canonicalIndices M i.val).mp i.property).1

/-- The Hilbert realization has exactly the original arithmetic coordinates. -/
theorem canonicalHilbertFamily_sequence (M : ℕ) (i : canonicalIndices M) :
    hilbertSequenceLinear (canonicalHilbertFamily M i) = canonicalFamily M i := by
  funext n
  change hilbertSequence (canonicalHilbertFamily M i) n = canonicalFamily M i n
  simp only [canonicalHilbertFamily, canonicalFamily, generator_sequence_apply,
    residue_mul_floor, Nat.mul_comm]

/-- No canonical arithmetic independence is lost in the Hilbert realization. -/
theorem canonicalHilbertFamily_linearIndependent (M : ℕ) :
    LinearIndependent ℝ (canonicalHilbertFamily M) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s c hz i hi
  apply (linearIndependent_iff'.mp (canonicalFamily_linearIndependent M)) s c ?_ i hi
  have h := congrArg hilbertSequenceLinear hz
  simpa only [map_sum, map_smul, map_zero, canonicalHilbertFamily_sequence] using h

/-- The actual Hilbert canonical family spans the existing finite budget. -/
theorem canonicalHilbertFamily_span (M : ℕ) :
    Submodule.span ℝ (Set.range (canonicalHilbertFamily M)) = budgetHilbert M := by
  classical
  let S := Submodule.span ℝ (Set.range (canonicalHilbertFamily M))
  have himage : hilbertSequenceLinear '' Set.range (canonicalHilbertFamily M) =
      Set.range (canonicalFamily M) := by
    ext f
    constructor
    · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (canonicalHilbertFamily_sequence M i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨canonicalHilbertFamily M i, ⟨i, rfl⟩, canonicalHilbertFamily_sequence M i⟩
  have hmap : S.map hilbertSequenceLinear = budgetSpan M := by
    dsimp only [S]
    rw [Submodule.map_span, himage, canonicalFamily_span, canonicalSpan_eq_budgetSpan]
  change S = budgetHilbert M
  apply le_antisymm
  · intro f hf
    change hilbertSequenceLinear f ∈ budgetSpan M
    rw [← hmap]
    exact ⟨f, hf, rfl⟩
  · intro f hf
    change hilbertSequenceLinear f ∈ budgetSpan M at hf
    rw [← hmap] at hf
    obtain ⟨g, hg, hgf⟩ := hf
    have hgf' : g = f := hilbertSequence_injective hgf
    rw [hgf'] at hg
    exact hg

/-- Exact dimension, now in the actual weighted Hilbert budget. -/
theorem finrank_budgetHilbert (M : ℕ) :
    Module.finrank ℝ (budgetHilbert M) = 2*M-M/3 := by
  rw [← canonicalHilbertFamily_span M,
    finrank_span_eq_card (canonicalHilbertFamily_linearIndependent M),
    Fintype.card_coe, card_canonicalIndices]

/-- Ordinary budget enlargement is a genuine inclusion of Hilbert subspaces. -/
theorem budgetHilbert_mono {M N : ℕ} (hMN : M ≤ N) :
    budgetHilbert M ≤ budgetHilbert N := by
  intro f hf
  exact budgetSpan_mono hMN hf

/-- Every permitted original generator belongs to its ordinary Hilbert budget. -/
theorem generator_mem_budgetHilbert (M p m : ℕ) (hp : 0 < p) (hm : 0 < m)
    (hseed : p = 2 ∨ p = 3) (hmM : m ≤ M) :
    generator p m hp hm ∈ budgetHilbert M := by
  change hilbertSequenceLinear (generator p m hp hm) ∈ budgetSpan M
  have heq : hilbertSequenceLinear (generator p m hp hm) = dilation m (residue p) := by
    funext n
    change hilbertSequence (generator p m hp hm) n = dilation m (residue p) n
    simp only [generator_sequence_apply, residue_mul_floor, Nat.mul_comm]
  rw [heq]
  exact generator_mem M p m hseed hm hmM

/-- An adjacent packet is in the ordinary budget once both endpoint indices are. -/
theorem packet_mem_budgetHilbert (M p m : ℕ) (hp : 0 < p) (hm : 0 < m)
    (hseed : p = 2 ∨ p = 3) (hmM : m+1 ≤ M) :
    packet p m hp hm ∈ budgetHilbert M := by
  exact (budgetHilbert M).sub_mem
    (generator_mem_budgetHilbert M p (m+1) hp (by omega) hseed hmM)
    (generator_mem_budgetHilbert M p m hp hm hseed (by omega))

/-- Both packets used for screening are in the old budget. -/
theorem old_cell_packets_mem (M k : ℕ) (hk : 0 < k) (hkM : k+1 ≤ M) :
    packet 2 k (by omega) hk ∈ budgetHilbert M ∧
      packet 3 k (by omega) hk ∈ budgetHilbert M :=
  ⟨packet_mem_budgetHilbert M 2 k (by omega) hk (Or.inl rfl) hkM,
   packet_mem_budgetHilbert M 3 k (by omega) hk (Or.inr rfl) hkM⟩

/-- All five members of the resonance cell lie in the doubled ordinary budget. -/
theorem new_cell_packets_mem (M k : ℕ) (hk : 0 < k) (hcell : 3*k+3 ≤ 2*M) :
    packet 2 (3*k) (by omega) (by omega) ∈ budgetHilbert (2*M) ∧
    packet 2 (3*k+1) (by omega) (by omega) ∈ budgetHilbert (2*M) ∧
    packet 2 (3*k+2) (by omega) (by omega) ∈ budgetHilbert (2*M) ∧
    packet 3 (2*k) (by omega) (by omega) ∈ budgetHilbert (2*M) ∧
    packet 3 (2*k+1) (by omega) (by omega) ∈ budgetHilbert (2*M) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact packet_mem_budgetHilbert (2*M) 2 (3*k) (by omega) (by omega) (Or.inl rfl) (by omega)
  · exact packet_mem_budgetHilbert (2*M) 2 (3*k+1) (by omega) (by omega) (Or.inl rfl) (by omega)
  · exact packet_mem_budgetHilbert (2*M) 2 (3*k+2) (by omega) (by omega) (Or.inl rfl) (by omega)
  · exact packet_mem_budgetHilbert (2*M) 3 (2*k) (by omega) (by omega) (Or.inr rfl) (by omega)
  · exact packet_mem_budgetHilbert (2*M) 3 (2*k+1) (by omega) (by omega) (Or.inr rfl) (by omega)

/-- The actual finite-budget residual automatically satisfies the cell relation. -/
theorem ordinary_budget_cellSource_compatible (M k : ℕ) (hk : 0 < k)
    (hkM : k+1 ≤ M) :
    RiemannResearch.LinearAlgebra.TwoThreeResonanceCell.Compatible
      (cellSource (hilbertOne-(budgetHilbert M).starProjection hilbertOne) k hk) := by
  obtain ⟨h2, h3⟩ := old_cell_packets_mem M k hk hkM
  exact projection_cellSource_compatible (budgetHilbert M) k hk h2 h3

end
end RiemannResearch.RH.Pareto.FiniteTwoSeedCompletion
