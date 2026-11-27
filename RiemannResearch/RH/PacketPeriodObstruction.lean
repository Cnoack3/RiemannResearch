import RiemannResearch.CategoryTheory.ParetoPacketCharacters
import RiemannResearch.RH.ParetoDilation

/-! # The zero residue class of a packet trial

Every conductor dividing an even common period vanishes on its multiples.
Consequently the physical centered parity error equals minus one on a set of
exactly known inverse-square mass, uniformly in the coefficients.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory
open RiemannResearch.RH.ZetaTwoProbability
namespace RiemannResearch.RH.Pareto

private theorem packet_zero_at_multiple {q n : ℕ} (h : q ∣ n) :
    ramanujanPacket q n = 0 := by
  unfold ramanujanPacket
  apply Finset.sum_eq_zero
  intro d hd
  have hdn := (Nat.dvd_of_mem_divisors hd).trans h
  simp [residue, Nat.mod_eq_zero_of_dvd hdn]

/-- The discrepancy is independent of the number and size of the coefficients
on the full zero class. The formula holds for unmixed packets as well. -/
theorem packetTrial_error_on_common_multiple {L n : ℕ} (evenPeriod : 2 ∣ L)
    (hn : L ∣ n) (s : Finset ℕ) (c : ℕ → ℝ) (hs : ∀ q ∈ s, q ∣ L) :
    ramanujanPacket 2 n / Real.log 2 - 1 -
      ∑ q ∈ s, c q * ramanujanPacket q n = -1 := by
  have hsum : ∑ q ∈ s, c q * ramanujanPacket q n = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    simp [packet_zero_at_multiple ((hs q hq).trans hn)]
  simp [packet_zero_at_multiple (evenPeriod.trans hn), hsum]

/-- An infinite Q-mass obstruction for any dictionary supported on divisors
of one fixed even period. -/
theorem measure_packetTrial_error_neg_one_ge {L : ℕ} (hL : 0 < L) (evenPeriod : 2 ∣ L)
    (s : Finset ℕ) (c : ℕ → ℝ) (hs : ∀ q ∈ s, q ∣ L) :
    ENNReal.ofReal (1 / (L : ℝ)^2) ≤ Q {n : ℕ+ |
      ramanujanPacket 2 n / Real.log 2 - 1 - ∑ q ∈ s, c q * ramanujanPacket q n = -1} := by
  rw [← measure_dvd L hL]
  apply measure_mono
  exact fun n hn => packetTrial_error_on_common_multiple evenPeriod hn s c hs

/-- The full Q mean squared error has the same lower bound. -/
theorem packetTrial_qSquareError_ge {L : ℕ} (hL : 0 < L) (evenPeriod : 2 ∣ L)
    (s : Finset ℕ) (c : ℕ → ℝ) (hs : ∀ q ∈ s, q ∣ L) :
    ENNReal.ofReal (1 / (L : ℝ)^2) ≤
      ∫⁻ n : ℕ+, ENNReal.ofReal ((ramanujanPacket 2 n / Real.log 2 - 1 -
        ∑ q ∈ s, c q * ramanujanPacket q n)^2) ∂Q := by
  classical
  let A : Set ℕ+ := {n | L ∣ (n : ℕ)}
  rw [← measure_dvd L hL]
  calc
    Q A = ∫⁻ n, A.indicator (fun _ => (1 : ENNReal)) n ∂Q := by
      rw [lintegral_indicator (Set.to_countable A).measurableSet, setLIntegral_one]
    _ ≤ _ := by
      apply lintegral_mono
      intro n
      by_cases h : n ∈ A
      · rw [Set.indicator_of_mem h]
        dsimp only
        rw [packetTrial_error_on_common_multiple evenPeriod h s c hs]
        norm_num
      · rw [Set.indicator_of_notMem h]
        exact bot_le

open RiemannResearch.RH.ZetaTwoHilbert

/-- Every conductor with exactly one factor of two and an odd cofactor greater
than one vanishes at site two, regardless of the cofactor's factorization. -/
theorem oddDoublePacket_at_two {m : ℕ} (hm : 1 < m) (hodd : ¬ 2 ∣ m) :
    ramanujanPacket (2*m) 2 = 0 := by
  have hR : ramanujanPacket m 2 = 2 * ramanujanPacket m 1 := by
    unfold ramanujanPacket
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    obtain hdn := Nat.dvd_of_mem_divisors hd
    have hpos := Nat.pos_of_mem_divisors hd
    by_cases hone : d = 1
    · subst d
      simp [residue]
    · have hne : d ≠ 2 := fun he => hodd (he ▸ hdn)
      have hbig : 2 < d := by omega
      simp only [residue, Nat.mod_eq_of_lt hbig, Nat.mod_eq_of_lt (by omega : 1 < d),
        Nat.cast_ofNat, Nat.cast_one]
      ring
  have h := RiemannResearch.CategoryTheory.ParetoPacketCharacters.packet_prime_gcd_step
    2 m 1 Nat.prime_two hm
  simpa [hodd, hR] using h

/-- Physical centered parity minus a finite packet synthesis on each site. -/
def centeredPacketTrialError (s : Finset ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ramanujanPacket 2 n / Real.log 2 - 1 - ∑ q ∈ s, c q * ramanujanPacket q n

theorem oddDoubleTrial_error_at_two (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, ∃ m, 1 < m ∧ ¬ 2 ∣ m ∧ q = 2*m) :
    centeredPacketTrialError s c 2 = -1 := by
  have hs0 : ∑ q ∈ s, c q * ramanujanPacket q 2 = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨m, hm, hodd, rfl⟩ := hs q hq
    simp [oddDoublePacket_at_two hm hodd]
  simp [centeredPacketTrialError, packet_zero_at_multiple (dvd_refl 2), hs0]

private theorem centeredPacketTrialError_bounded (s : Finset ℕ) (c : ℕ → ℝ) :
    ∃ D, ∀ n, |centeredPacketTrialError s c n| ≤ D := by
  obtain ⟨C, hC⟩ := packetCombination_bounded s c
  refine ⟨2 / |Real.log 2| + 1 + C, fun n => ?_⟩
  have hj : |ramanujanPacket 2 n| ≤ 2 := by
    rw [ramanujanPacket_prime_eq_residue 2 Nat.prime_two]
    exact residue_abs_le 2 n (by decide)
  have hj' : |ramanujanPacket 2 n / Real.log 2| ≤ 2 / |Real.log 2| := by
    rw [abs_div]
    exact div_le_div_of_nonneg_right hj (abs_nonneg _)
  unfold centeredPacketTrialError
  calc
    _ ≤ |ramanujanPacket 2 n / Real.log 2 - 1| + |∑ q ∈ s, c q * ramanujanPacket q n| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
        (ramanujanPacket 2 n / Real.log 2 - 1) 0 (∑ q ∈ s, c q * ramanujanPacket q n)
    _ ≤ (|ramanujanPacket 2 n / Real.log 2| + 1) + C := by
      apply add_le_add _ (hC n)
      simpa only [sub_zero, zero_sub, abs_neg, abs_one] using abs_sub_le
        (ramanujanPacket 2 n / Real.log 2) 0 1
    _ ≤ _ := by linarith

/-- Uniform, complete squared-error lower bounds for the entire family with
two-adic order one. The conductors and the real coefficients are unrestricted
within this family. -/
theorem oddDoubleTrial_completeError_lower (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, ∃ m, 1 < m ∧ ¬ 2 ∣ m ∧ q = 2*m) :
    (1 / 6 : ℝ) ≤ ∑' n, positiveWeight n * (centeredPacketTrialError s c n)^2 ∧
    1 / (4*zetaTwo) ≤ ∑' n, positiveQWeight n * (centeredPacketTrialError s c n)^2 := by
  let e := centeredPacketTrialError s c
  obtain ⟨D, hD⟩ := centeredPacketTrialError_bounded s c
  have hD0 := (abs_nonneg _).trans (hD 0)
  have hp : Summable (fun n => positiveWeight n * (e n)^2) := by
    apply weighted_summable_of_bounded (C := D^2)
    intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg _) (hD n) 2)
  have hq := boundedQ_square_summable e D hD0 hD
  have h2 : e 2 = -1 := oddDoubleTrial_error_at_two s c hs
  have hp2 := hp.le_tsum 2 (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
  have hq2 := hq.le_tsum 2 (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
  change positiveWeight 2 * (e 2)^2 ≤ _ at hp2
  change positiveQWeight 2 * (e 2)^2 ≤ _ at hq2
  rw [h2] at hp2 hq2
  constructor
  · convert hp2 using 1 <;> norm_num [positiveWeight]
  · convert hq2 using 1 <;> norm_num [positiveQWeight, mul_comm]

end RiemannResearch.RH.Pareto
