import RiemannResearch.RH.ParetoGibbsTailBasis
import RiemannResearch.RH.ThresholdHilbertLegal
import RiemannResearch.LinearAlgebra.OrthogonalSchurRepair

/-!
# Exact tail coordinates and the Pareto Schur repair

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Sections 6–7. The existing `tailBasisHilbert n` is the paper's h_(n+1):
its physical coordinate at n+1 is n+1, and its later coordinates are -1.
The complete orthonormal mean-zero basis was proved in ParetoGibbsTailBasis.
This module supplies the finite coefficient formula and exact repair update.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Exact finite formula for a full infinite-Hilbert-space pairing. -/
theorem tailBasis_coefficient_formula (f : ThresholdHilbert) (n : ℕ) :
    inner ℝ f (tailBasisHilbert n) =
      (∑ k ∈ Finset.range n, paretoWeight k * hilbertGibbsPhysical f k) +
        hilbertGibbsPhysical f n / ((n : ℝ) + 1) - inner ℝ f hilbertOne := by
  unfold tailBasisHilbert
  rw [inner_sub_right, inner_add_right, inner_smul_right, inner_sum]
  simp only [inner_paretoPoint]
  have hw : ((n : ℝ) + 2) * paretoWeight n = 1 / ((n : ℝ) + 1) := by
    unfold paretoWeight
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
  rw [← mul_assoc, hw]
  ring

/-- Mean-zero coefficient formula: all apparent infinite-tail terms have
been evaluated exactly through the mean, rather than discarded. -/
theorem tailBasis_coefficient_of_mean_zero (f : ThresholdHilbert) (n : ℕ)
    (hmean : inner ℝ f hilbertOne = 0) :
    inner ℝ f (tailBasisHilbert n) =
      (∑ k ∈ Finset.range n, paretoWeight k * hilbertGibbsPhysical f k) +
        hilbertGibbsPhysical f n / ((n : ℝ) + 1) := by
  rw [tailBasis_coefficient_formula, hmean, sub_zero]

theorem tailBasis_coefficient_at_first (f : ThresholdHilbert) (n : ℕ)
    (hmean : inner ℝ f hilbertOne = 0)
    (hhead : ∀ k < n, hilbertGibbsPhysical f k = 0) :
    inner ℝ f (tailBasisHilbert n) =
      hilbertGibbsPhysical f n / ((n : ℝ) + 1) := by
  rw [tailBasis_coefficient_of_mean_zero f n hmean]
  have hz : (∑ k ∈ Finset.range n, paretoWeight k * hilbertGibbsPhysical f k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hhead k (Finset.mem_range.mp hk), mul_zero]
  rw [hz, zero_add]

theorem tailBasis_coefficient_before_head (f : ThresholdHilbert) (n j : ℕ)
    (hmean : inner ℝ f hilbertOne = 0)
    (hhead : ∀ k < n, hilbertGibbsPhysical f k = 0) (hj : j < n) :
    inner ℝ f (tailBasisHilbert j) = 0 := by
  rw [tailBasis_coefficient_at_first f j hmean
    (fun k hk => hhead k (lt_trans hk hj)), hhead j hj, zero_div]

/-- At its first nonzero coordinate, the normalized repair has exactly the
expected Haar coefficient. The physical coordinate convention starts at zero. -/
theorem tailBasis_coefficient_normalized_repair (u : ThresholdHilbert) (n : ℕ)
    (hmean : inner ℝ u hilbertOne = 0)
    (hhead : ∀ k < n, hilbertGibbsPhysical u k = 0)
    (hat : hilbertGibbsPhysical u n = 1) :
    inner ℝ (((n : ℝ) + 1) • u) (tailBasisHilbert n) = 1 := by
  rw [inner_smul_left, RCLike.conj_to_real,
    tailBasis_coefficient_at_first u n hmean hhead, hat]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- One step of the actual Hilbert recursion, indexed by positive physical k. -/
def paretoPacketStep (F u d : ThresholdHilbert) (n : ℕ) : ThresholdHilbert :=
  LinearAlgebra.schurRepair F u d (1 - hilbertSequence F n)

theorem paretoPacketStep_sequence (F u d : ThresholdHilbert) (n k : ℕ) :
    hilbertSequence (paretoPacketStep F u d n) k =
      hilbertSequence F k + (1 - hilbertSequence F n) * hilbertSequence u k -
        ((inner ℝ F d + (1 - hilbertSequence F n) * inner ℝ u d) / ‖d‖ ^ 2) *
          hilbertSequence d k := by
  unfold paretoPacketStep LinearAlgebra.schurRepair LinearAlgebra.schurRemove
  change hilbertSequenceLinear
    (F + (1 - hilbertSequence F n) • u -
      (inner ℝ (F + (1 - hilbertSequence F n) • u) d / ‖d‖ ^ 2) • d) k = _
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, inner_add_left, inner_smul_left,
    RCLike.conj_to_real]
  rfl

theorem paretoPacketStep_head (F u d : ThresholdHilbert) (n : ℕ)
    (hF : ∀ k, 0 < k → k < n → hilbertSequence F k = 1)
    (hu : ∀ k, 0 < k → k < n → hilbertSequence u k = 0)
    (hun : hilbertSequence u n = 1)
    (hd : ∀ k, 0 < k → k ≤ n → hilbertSequence d k = 0) :
    ∀ k, 0 < k → k ≤ n → hilbertSequence (paretoPacketStep F u d n) k = 1 := by
  intro k hk hkn
  rw [paretoPacketStep_sequence, hd k hk hkn, mul_zero, sub_zero]
  by_cases he : k = n
  · subst k
    rw [hun]
    ring
  · have hlt : k < n := lt_of_le_of_ne hkn he
    rw [hF k hk hlt, hu k hk hlt]
    ring

theorem paretoPacketStep_mean (F u d : ThresholdHilbert) (n : ℕ)
    (hu : inner ℝ u hilbertOne = 0) (hd : inner ℝ d hilbertOne = 0) :
    inner ℝ (paretoPacketStep F u d n) hilbertOne = inner ℝ F hilbertOne :=
  LinearAlgebra.schurRepair_preserves_inner F u d hilbertOne _ hu hd

theorem paretoPacketStep_legal (A : Set ℕ) (F u d : ThresholdHilbert) (n : ℕ)
    (hF : F ∈ hilbertLegalSubspace A) (hu : u ∈ hilbertLegalSubspace A)
    (hd : d ∈ hilbertLegalSubspace A) :
    paretoPacketStep F u d n ∈ hilbertLegalSubspace A :=
  LinearAlgebra.schurRepair_mem (hilbertLegalSubspace A) F u d _ hF hu hd

/-- Formula (25) in the actual full Pareto Hilbert norm. -/
theorem paretoPacketStep_energy (F u d : ThresholdHilbert) (n : ℕ) (hd : d ≠ 0) :
    ‖paretoPacketStep F u d n‖ ^ 2 =
      ‖F‖ ^ 2 + 2 * (1 - hilbertSequence F n) * inner ℝ F u +
        (1 - hilbertSequence F n) ^ 2 * ‖u‖ ^ 2 -
        (inner ℝ F d + (1 - hilbertSequence F n) * inner ℝ u d) ^ 2 / ‖d‖ ^ 2 :=
  LinearAlgebra.schurRepair_norm_sq F u d _ hd

/-- Every Haar coefficient updates with all correlations retained. -/
theorem paretoPacketStep_tail_coefficient (F u d : ThresholdHilbert) (n j : ℕ) :
    inner ℝ (paretoPacketStep F u d n) (tailBasisHilbert j) =
      inner ℝ F (tailBasisHilbert j) +
        (1 - hilbertSequence F n) * inner ℝ u (tailBasisHilbert j) -
        ((inner ℝ F d + (1 - hilbertSequence F n) * inner ℝ u d) / ‖d‖ ^ 2) *
          inner ℝ d (tailBasisHilbert j) :=
  LinearAlgebra.schurRepair_inner F u d (tailBasisHilbert j) _

theorem pareto_mean_one_norm_sq (F : ThresholdHilbert)
    (hmean : inner ℝ F hilbertOne = 1) :
    ‖F‖ ^ 2 = 1 + ‖F - hilbertOne‖ ^ 2 :=
  LinearAlgebra.norm_sq_eq_one_add_error F hilbertOne hilbertOne_norm_sq hmean

end
end RiemannResearch.RH.Pareto
