import RiemannResearch.RH.ParetoNewPacketPeriodicity
import RiemannResearch.RH.ParetoTailOrthogonalization
import RiemannResearch.RH.ParetoFiniteGram
import RiemannResearch.RH.ParetoPeriodicRegrouping

/-!
# Strict covariance for prime conductor innovations

Source: user-provided `RH_Controlled_Conductor_Schur_2026-09-10.md`, §3.
All norms are the complete infinite Pareto norms.  The arithmetic independence
theorem allows subtraction of arbitrary old-periodic means, not only old legal
packet combinations.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Every nonzero new packet combination has strictly positive full Pareto
distance from every bounded old-periodic sequence.  There is no uniform lower
bound here, and no approximation claim is inferred from strict positivity. -/
theorem new_packet_minus_periodic_paretoInner_pos (p Q : ℕ)
    (hp : p.Prime) (hQ : 0 < Q) (s : Finset ℕ) (b : ℕ → ℝ)
    (hs : ∀ q ∈ s, q ∣ p * Q ∧ ¬ q ∣ Q)
    (hb : ∃ q ∈ s, b q ≠ 0) (g : ℕ → ℝ) {C : ℝ}
    (hg : ∀ k, |g k| ≤ C) (hgper : ∀ k, g (k + Q) = g k) :
    0 < paretoInner
      (fun k => (∑ q ∈ s, b q * ramanujanPacket q k) - g k)
      (fun k => (∑ q ∈ s, b q * ramanujanPacket q k) - g k) := by
  classical
  let f : ℕ → ℝ := fun k => ∑ q ∈ s, b q * ramanujanPacket q k
  have hL : 0 < p * Q := Nat.mul_pos hp.pos hQ
  have hfper (k : ℕ) : f (k + p * Q) = f k := by
    dsimp [f]
    apply Finset.sum_congr rfl
    intro q hqs
    rw [ramanujanPacket_period_of_dvd q (p * Q) (hs q hqs).1 k]
  have hexists : ∃ k : ℕ, 0 < k ∧ f k - g k ≠ 0 := by
    by_contra h
    push Not at h
    have heq (k : ℕ) (hk : 0 < k) : f k = g k := sub_eq_zero.mp (h k hk)
    have hper (k : ℕ) : f (k + Q) = f k := by
      calc
        f (k + Q) = f (k + Q + p * Q) := (hfper (k + Q)).symm
        _ = g (k + Q + p * Q) := heq _ (by omega)
        _ = g ((k + p * Q) + Q) := by congr 1; omega
        _ = g (k + p * Q) := hgper _
        _ = f (k + p * Q) := (heq _ (by omega)).symm
        _ = f k := hfper k
    have hzero := ramanujanPacket_new_independent_mod_periodic p Q hp hQ s b hs hper
    obtain ⟨q, hqs, hbq⟩ := hb
    exact hbq (hzero q hqs)
  obtain ⟨k, hk, hkg⟩ := hexists
  obtain ⟨B, hf⟩ := packetCombination_bounded s b
  exact paretoInner_pos_of_anchor (bounded_sub hf hg) k hk hkg

/-- Subtracting any bounded old-periodic means produces a strictly positive
innovation covariance matrix on the distinct new divisor packets.  The complete
double sum retains every signed off-diagonal entry. -/
theorem new_packet_periodic_mean_covariance_pos (p Q : ℕ)
    (hp : p.Prime) (hQ : 0 < Q) (s : Finset ℕ) (b : ℕ → ℝ)
    (hs : ∀ q ∈ s, q ∣ p * Q ∧ ¬ q ∣ Q)
    (hb : ∃ q ∈ s, b q ≠ 0) (M : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (hM : ∀ q k, |M q k| ≤ C q)
    (hMper : ∀ q k, M q (k + Q) = M q k) :
    0 < ∑ q ∈ s, ∑ r ∈ s, b q * b r *
      paretoInner (fun k => ramanujanPacket q k - M q k)
        (fun k => ramanujanPacket r k - M r k) := by
  let U : ℕ → ℕ → ℝ := fun q k => ramanujanPacket q k - M q k
  let B : ℕ → ℝ := fun q =>
    (∑ d ∈ q.divisors, |(ArithmeticFunction.moebius (q / d) : ℝ)| * (d : ℝ)) + C q
  have hU : ∀ q k, |U q k| ≤ B q := by
    intro q
    exact bounded_sub (ramanujanPacket_abs_le q) (hM q)
  have hgper (k : ℕ) :
      (∑ q ∈ s, b q * M q (k + Q)) = ∑ q ∈ s, b q * M q k := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hMper]
  have hpos := new_packet_minus_periodic_paretoInner_pos p Q hp hQ s b hs hb
    (fun k => ∑ q ∈ s, b q * M q k) (bounded_finsetCombination s b hM) hgper
  have heq :
      (fun k => (∑ q ∈ s, b q * ramanujanPacket q k) - ∑ q ∈ s, b q * M q k) =
      (fun k => ∑ q ∈ s, b q * U q k) := by
    funext k
    simp only [U, mul_sub, Finset.sum_sub_distrib]
  rw [heq, paretoInner_finsetCombination s b hU] at hpos
  exact hpos

end
end RiemannResearch.RH.Pareto
