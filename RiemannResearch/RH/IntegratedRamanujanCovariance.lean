import RiemannResearch.RH.IntegratedRamanujanGram
import RiemannResearch.RH.ParetoFiniteErrorObstruction
/-!
# Strict centered covariance for the actual Ramanujan packets

Source: Christian Noack, user-provided signal_to_noise_RH_program (2)(1).pdf,
Lemma 4.1. This proves the finite nonsingularity claim for the full Pareto
law using a common-period zero and actual packet independence. It supplies
no uniform lower eigenvalue estimate.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto

theorem packetCombination_variance_pos (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, 1 < q) (hc : ∃ q ∈ s, c q ≠ 0) :
    0 < paretoVariance (fun k => ∑ q ∈ s, c q * ramanujanPacket q k) := by
  let f : ℕ → ℝ := fun k => ∑ q ∈ s, c q * ramanujanPacket q k
  obtain ⟨C, hC⟩ := packetCombination_bounded s c
  have hb : ∀ k, |f k - paretoMean f| ≤ C + |paretoMean f| := by
    intro k
    exact (abs_sub (f k) (paretoMean f)).trans (add_le_add (hC k) (le_refl _))
  by_contra hp
  have hz : paretoVariance f = 0 :=
    le_antisymm (le_of_not_gt hp) (paretoVariance_nonneg f)
  have hvalues := (paretoInner_self_zero_iff_positive hb).mp hz
  let Q : ℕ := ∏ q ∈ s, q
  have hQ : 0 < Q := Finset.prod_pos (fun q hq => lt_trans Nat.zero_lt_one (hs q hq))
  have hfQ : f Q = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hqQ : q ∣ Q := Finset.dvd_prod_of_mem id hq
    rw [ramanujanPacket_eq_zero_of_dvd hqQ, mul_zero]
  have hmean : paretoMean f = 0 := by
    have h := hvalues Q hQ
    rw [hfQ] at h
    linarith
  have hall : ∀ k, ∑ q ∈ s, c q * ramanujanPacket q k = 0 := by
    intro k
    by_cases hk : k = 0
    · subst k
      simp [ramanujanPacket, residue]
    · have h := hvalues k (Nat.pos_of_ne_zero hk)
      simpa only [hmean, sub_zero] using h
  obtain ⟨q, hqs, hcq⟩ := hc
  exact hcq (ramanujanPacket_finite_independent s c hs hall q hqs)
end RiemannResearch.RH.Pareto
