import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ParetoFiniteCertificates
import RiemannResearch.RH.ParetoNoiseSignal

/-!
Source: user-provided Pareto CRT research note §§5-6. This module lifts finite
certificates to the complete Pareto error and noise-to-signal ratio. General
packet bounds live in `ParetoResidueDuality`; weighted summability and exclusion
of nonzero linear sequences live in `ParetoDilation`.
-/
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The previously finite certificate now bounds the genuine infinite Pareto norm. -/
theorem primePowerCombination_full_error_floor (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, ∃ p a, p.Prime ∧ q = p^a) :
    (3562158 : ℝ) / 256250081 ≤
      ∑' k, positiveWeight k * (1-∑ q ∈ s, c q*ramanujanPacket q k)^2 := by
  have h := primePowerCombination_error_floor s c hs
  have hfinite : (∑ k : Fin 15,
      (1-∑ q ∈ s, c q*ramanujanPacket q (k+1))^2 / (coordinateWeight k : ℝ)) =
      ∑ k ∈ Finset.Ico 1 16, positiveWeight k *
        (1-∑ q ∈ s, c q*ramanujanPacket q k)^2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    norm_num only [Nat.reduceSub]
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    unfold coordinateWeight positiveWeight
    push_cast
    simp only [Nat.add_comm 1]
    ring
  rw [hfinite] at h
  exact le_trans h ((packetCombination_error_summable s c).sum_le_tsum
    (Finset.Ico 1 16) (fun k hk => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _)))


theorem primePowerCombination_noiseSignal_floor (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, ∃ p a, p.Prime ∧ q = p^a)
    (hm : paretoMean (fun k => ∑ q ∈ s, c q * ramanujanPacket q k) ≠ 0) :
    (1 : ℝ)/91 ≤ noiseSignalRatio (fun k => ∑ q ∈ s, c q * ramanujanPacket q k) := by
  let f : ℕ → ℝ := fun k => ∑ q ∈ s, c q * ramanujanPacket q k
  obtain ⟨C, hC⟩ := packetCombination_bounded s c
  let a : ℝ := paretoMean f / (paretoVariance f + (paretoMean f)^2)
  have hbound := primePowerCombination_full_error_floor s (fun q => a * c q) hs
  have heq : (fun k => ∑ q ∈ s, (a * c q) * ramanujanPacket q k) =
      (fun k => a * f k) := by
    funext k
    simp only [f, Finset.mul_sum, mul_assoc]
  simp_rw [congrFun heq] at hbound
  have herr : (1 : ℝ)/92 ≤ paretoError (fun k => a * f k) := by
    change (1 : ℝ)/92 ≤ ∑' k, positiveWeight k * ((1 - a*f k)*(1 - a*f k))
    simp only [← sq]
    linarith
  have hop := paretoError_scale_completion (f := f) hC hm a
  change paretoError (fun k => a * f k) = _ at hop
  simp only [a, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hop
  rw [hop] at herr
  have hmpos : 0 < (paretoMean f)^2 := sq_pos_of_ne_zero hm
  have hdpos : 0 < paretoVariance f + (paretoMean f)^2 :=
    add_pos_of_nonneg_of_pos (paretoVariance_nonneg f) hmpos
  have hb := (le_div_iff₀ hdpos).mp herr
  change (1 : ℝ)/91 ≤ paretoVariance f / (paretoMean f)^2
  apply (le_div_iff₀ hmpos).mpr
  nlinarith

end
end RiemannResearch.RH.Pareto
