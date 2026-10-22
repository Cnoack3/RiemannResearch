import RiemannResearch.RH.ParetoUniformJordanIdentification
import RiemannResearch.RH.ParetoJordanMeanCoordinates
import RiemannResearch.RH.ParetoResidueMean

/-!
# Genuine legal packets in the reflection/Jordan objective

Source: Christian Noack, September 11, 2026, law of total variance discussion.
All coefficients may be signed. All positive integer dilation scales remain
available. The complete Pareto mean and variance are used throughout.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem divisorLegalPacket_mem {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (a m : ι → ℕ) (A : Set ℕ) (ha : ∀ i ∈ s, a i ∈ A)
    (hm : ∀ i ∈ s, 0 < m i) : divisorLegalPacket s c a m ∈ legalSeedSpan A := by
  classical
  have he : divisorLegalPacket s c a m =
      ∑ i ∈ s, c i • dilation (m i) (residue (a i)) := by
    ext n
    simp [divisorLegalPacket, Finset.sum_apply]
  rw [he]
  exact (legalSeedSpan A).sum_mem (fun i hi =>
    (legalSeedSpan A).smul_mem (c i) (dilation_generator_mem A (ha i hi) (hm i hi)))

theorem divisorLegalPacket_period {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (a m : ι → ℕ) (Q : ℕ) (hperiod : ∀ i ∈ s, a i * m i ∣ Q)
    (hscale : ∀ i ∈ s, m i ∣ Q) (n : ℕ) :
    divisorLegalPacket s c a m (n + Q) = divisorLegalPacket s c a m n := by
  unfold divisorLegalPacket
  apply Finset.sum_congr rfl
  intro i hi
  rw [dilation_residue_incidence_coordinates, dilation_residue_incidence_coordinates,
    residue_period_of_dvd (hperiod i hi), residue_period_of_dvd (hscale i hi)]

theorem divisorLegalPacket_reflection {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (a m : ι → ℕ) (Q : ℕ) (ha : ∀ i ∈ s, 0 < a i)
    (hm : ∀ i ∈ s, 0 < m i) (hperiod : ∀ i ∈ s, a i * m i ∣ Q)
    (hscale : ∀ i ∈ s, m i ∣ Q) (n : ℕ) (hn : n < Q) :
    divisorLegalPacket s c a m n + divisorLegalPacket s c a m (Q - 1 - n) =
      divisorLegalPacketReflectionConstant s c a m := by
  have hpoint (i : ι) (hi : i ∈ s) :
      dilation (m i) (residue (a i)) n +
        dilation (m i) (residue (a i)) (Q - 1 - n) =
          (((a i * m i : ℕ) : ℝ) - (m i : ℝ)) := by
    have h1 := residue_reflection_sum (Nat.mul_pos (ha i hi) (hm i hi))
      (hperiod i hi) hn
    have h2 := residue_reflection_sum (hm i hi) (hscale i hi) hn
    rw [Nat.cast_sub (Nat.succ_le_of_lt (Nat.mul_pos (ha i hi) (hm i hi))),
      Nat.cast_one] at h1
    rw [Nat.cast_sub (Nat.succ_le_of_lt (hm i hi)), Nat.cast_one] at h2
    rw [dilation_residue_incidence_coordinates, dilation_residue_incidence_coordinates]
    linarith
  unfold divisorLegalPacket divisorLegalPacketReflectionConstant
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_add, hpoint i hi]

theorem divisorLegalPacket_bounded {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (a m : ι → ℕ) (ha : ∀ i ∈ s, 0 < a i) :
    ∃ B : ℝ, ∀ n, |divisorLegalPacket s c a m n| ≤ B := by
  classical
  refine ⟨∑ i ∈ s, |c i| * ((m i : ℝ) * (a i : ℝ)), ?_⟩
  intro n
  unfold divisorLegalPacket
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (dilation_abs_le (fun k => residue_abs_le (a i) k (ha i hi)) (m i) n)
    (abs_nonneg _)

/-- The complete infinite Pareto mean of the actual packet. -/
theorem paretoMean_divisorLegalPacket {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (a m : ι → ℕ) (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i) :
    paretoMean (divisorLegalPacket s c a m) = ∑ i ∈ s, c i * Real.log (a i) := by
  classical
  have hs : ∀ i ∈ s, Summable (fun n =>
      positiveWeight n * (c i * dilation (m i) (residue (a i)) n)) := by
    intro i hi
    apply weighted_summable_of_bounded
    exact bounded_const_mul
      (dilation_abs_le (fun k => residue_abs_le (a i) k (ha i hi)) (m i)) (c i)
  have he (i : ι) (hi : i ∈ s) :
      (∑' n, positiveWeight n * (c i * dilation (m i) (residue (a i)) n)) =
        c i * Real.log (a i) := by
    calc
      _ = c i * paretoMean (dilation (m i) (residue (a i))) := by
        unfold paretoMean
        simp_rw [mul_left_comm (positiveWeight _) (c i)]
        exact tsum_mul_left
      _ = _ := by
        rw [paretoMean_dilation (fun k => residue_abs_le (a i) k (ha i hi))
          (by simp [residue]) (m i) (hm i hi), paretoMean_residue (a i) (ha i hi)]
  unfold paretoMean divisorLegalPacket
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum hs]
  exact Finset.sum_congr rfl he

/-- Actual Pareto normalization in the exact signed von Mangoldt coordinates. -/
theorem paretoMean_divisorLegalPacket_eq_vonMangoldt {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (a m : ι → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ Q) (hscale : ∀ i ∈ s, m i ∣ Q) :
    paretoMean (divisorLegalPacket s c a m) =
      ∑ d ∈ Q.divisors,
        ArithmeticFunction.vonMangoldt d * legalPacketDivisorCoordinate s c a m d := by
  rw [paretoMean_divisorLegalPacket s c a m ha hm,
    legalPacketDivisorCoordinate_log_mean s c a m Q hQ ha hm hperiod hscale]

/-- The proposed optimization objective, with its actual arithmetic penalty. -/
theorem reflectionSurrogate_divisorLegalPacket {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (a m : ι → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ Q) (hscale : ∀ i ∈ s, m i ∣ Q)
    (t : ℝ) :
    reflectionSurrogate Q (divisorLegalPacket s c a m) t
      (divisorLegalPacketReflectionConstant s c a m) =
        reflectionCalibration Q (divisorLegalPacket s c a m) t +
          Real.pi ^ 2 / (12 * (Q : ℝ)) *
            ∑ d ∈ Q.divisors,
              jordanTwo d * legalPacketDivisorCoordinate s c a m d ^ 2 := by
  unfold reflectionSurrogate
  rw [uniformReflectionVariance_divisorLegalPacket s c a m Q hQ ha hm hperiod hscale]
  ring

/-- Uniform comparison with the full Pareto variance for actual mean-one legal packets. -/
theorem divisorLegalPacket_variance_surrogate_comparison {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (a m : ι → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (heven : Even Q) (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ Q) (hscale : ∀ i ∈ s, m i ∣ Q)
    (hmean : ∑ i ∈ s, c i * Real.log (a i) = 1) :
    paretoVariance (divisorLegalPacket s c a m) ≤
      reflectionSurrogate Q (divisorLegalPacket s c a m) 1
        (divisorLegalPacketReflectionConstant s c a m) ∧
      reflectionSurrogate Q (divisorLegalPacket s c a m) 1
        (divisorLegalPacketReflectionConstant s c a m) ≤
          (1 + Real.pi ^ 2) * paretoVariance (divisorLegalPacket s c a m) := by
  obtain ⟨B, hB⟩ := divisorLegalPacket_bounded s c a m ha
  have h := paretoVariance_reflectionSurrogate_comparison Q hQ heven
    (divisorLegalPacket s c a m) hB
    (divisorLegalPacket_period s c a m Q hperiod hscale)
    (divisorLegalPacketReflectionConstant s c a m)
    (divisorLegalPacket_reflection s c a m Q ha hm hperiod hscale)
  simpa only [paretoMean_divisorLegalPacket s c a m ha hm, hmean] using h

/-- The explicit signed arithmetic objective sandwiches the actual mean-one variance. -/
theorem divisorLegalPacket_variance_jordan_comparison {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (a m : ι → ℕ) (Q : ℕ) (hQ : 0 < Q)
    (heven : Even Q) (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ Q) (hscale : ∀ i ∈ s, m i ∣ Q)
    (hmean : ∑ i ∈ s, c i * Real.log (a i) = 1) :
    let L := reflectionCalibration Q (divisorLegalPacket s c a m) 1 +
      Real.pi ^ 2 / (12 * (Q : ℝ)) *
        ∑ d ∈ Q.divisors,
          jordanTwo d * legalPacketDivisorCoordinate s c a m d ^ 2
    paretoVariance (divisorLegalPacket s c a m) ≤ L ∧
      L ≤ (1 + Real.pi ^ 2) * paretoVariance (divisorLegalPacket s c a m) := by
  dsimp only
  have h := divisorLegalPacket_variance_surrogate_comparison s c a m Q hQ
    heven ha hm hperiod hscale hmean
  simpa only [reflectionSurrogate_divisorLegalPacket s c a m Q hQ ha hm hperiod hscale] using h

end
end RiemannResearch.RH.Pareto
