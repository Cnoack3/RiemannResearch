import RiemannResearch.RH.ScreenedPrimePowerTelescope
import RiemannResearch.RH.ParetoAmplitudeCertificates

/-!
# A rational mixed-conductor certificate for the conductor-two projection

The mixed conductors 6, 10, 12, 14 and 15 give a trial for the projection of
integrated parity. Translating parity by one half leaves its mixed projection
unchanged and makes its squared norm exactly one quarter. We certify the trial
with a rational period-420 residual and the complete Pareto tail bound.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

/-- A centered variational identity for an arbitrary mixed trial.
The final square is the exact loss from choosing that trial. -/
theorem fixedTwo_centered_trial_balance (B : ℕ) {y : ThresholdHilbert}
    (hy : y ∈ mixedSpace (Finset.Icc 2 B)) :
    let J := ramanujanPacketHilbert 2
    let p := (mixedSpace (Finset.Icc 2 B)).starProjection J
    ‖p‖ ^ 2 + ‖(J - (1 / 2 : ℝ) • hilbertOne) - y‖ ^ 2 =
      1 / 4 + ‖p - y‖ ^ 2 := by
  let J := ramanujanPacketHilbert 2
  let K := mixedSpace (Finset.Icc 2 B)
  let p := K.starProjection J
  have hm : inner ℝ J hilbertOne = Real.log 2 := by
    rw [hilbert_inner_one]
    simp only [J, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat]
  have hy1 : inner ℝ hilbertOne y = 0 :=
    (real_inner_comm _ _).trans (((K.mem_orthogonal _).mp (one_mem_mixed_orthogonal _) y hy))
  have hp : inner ℝ p y = inner ℝ J y := by
    have h := (K.mem_orthogonal _).mp (K.sub_starProjection_mem_orthogonal J) y hy
    rw [inner_sub_right, sub_eq_zero] at h
    exact ((real_inner_comm _ _).trans (h.symm.trans (real_inner_comm _ _)))
  change ‖p‖ ^ 2 + ‖(J - (1 / 2 : ℝ) • hilbertOne) - y‖ ^ 2 =
    1 / 4 + ‖p - y‖ ^ 2
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, inner_sub_left,
    real_inner_smul_left, real_inner_smul_right, hm, hy1, hp,
    show ‖J‖ ^ 2 = Real.log 2 from ramanujanPacketHilbert_two_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hilbertOne_norm_sq]
  ring

private theorem packet_ten_residue (k : ℕ) :
    ramanujanPacket 10 k = residue 10 k - residue 5 k - residue 2 k := by
  rw [ramanujanPacket, show (10 : ℕ).divisors = {1,2,5,10} by decide]
  norm_num [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5), residue, Nat.mod_one]
  ring

private theorem packet_fifteen_residue (k : ℕ) :
    ramanujanPacket 15 k = residue 15 k - residue 5 k - residue 3 k := by
  rw [ramanujanPacket, show (15 : ℕ).divisors = {1,3,5,15} by decide]
  norm_num [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5), residue, Nat.mod_one]
  ring

private theorem packet_twelve_residue (k : ℕ) :
    ramanujanPacket 12 k = residue 12 k - residue 6 k - residue 4 k + residue 2 k := by
  have h4 : ArithmeticFunction.moebius 4 = 0 := by
    rw [show (4 : ℕ) = 2*2 by rfl, moebius_prime_mul 2 2 Nat.prime_two]
    simp
  have h6 : ArithmeticFunction.moebius 6 = 1 := by
    rw [show (6 : ℕ) = 2*3 by rfl, moebius_prime_mul 2 3 Nat.prime_two]
    norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  rw [ramanujanPacket, show (12 : ℕ).divisors = {1,2,3,4,6,12} by decide]
  norm_num [h4, h6, ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three, residue, Nat.mod_one]
  ring

private theorem packet_fourteen_residue (k : ℕ) :
    ramanujanPacket 14 k = residue 14 k - residue 7 k - residue 2 k := by
  rw [ramanujanPacket, show (14 : ℕ).divisors = {1,2,7,14} by decide]
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 7), residue, Nat.mod_one]
  ring

private def parityMixedTrial : ThresholdHilbert :=
  (-(4/50 : ℝ)) • ramanujanPacketHilbert 6 +
  (-(5/50 : ℝ)) • ramanujanPacketHilbert 10 +
  (4/50 : ℝ) • ramanujanPacketHilbert 12 +
  (-(5/50 : ℝ)) • ramanujanPacketHilbert 14 +
  (3/50 : ℝ) • ramanujanPacketHilbert 15

private def parityTrialRow (k : ℕ) : ℤ :=
  32 * ((k % 2 : ℕ) : ℤ) - 25 + 8 * ((k % 6 : ℕ) : ℤ) - ((k % 3 : ℕ) : ℤ) +
  5 * ((k % 10 : ℕ) : ℤ) - 2 * ((k % 5 : ℕ) : ℤ) - 3 * ((k % 15 : ℕ) : ℤ) +
  4 * ((k % 4 : ℕ) : ℤ) - 4 * ((k % 12 : ℕ) : ℤ) - 5 * ((k % 7 : ℕ) : ℤ) +
  5 * ((k % 14 : ℕ) : ℤ)

private theorem parityTrialRow_mod (k : ℕ) :
    parityTrialRow (k % 420) = parityTrialRow k := by
  unfold parityTrialRow
  simp only [Nat.mod_mod_of_dvd k (by decide : 2 ∣ 420),
    Nat.mod_mod_of_dvd k (by decide : 3 ∣ 420),
    Nat.mod_mod_of_dvd k (by decide : 5 ∣ 420),
    Nat.mod_mod_of_dvd k (by decide : 6 ∣ 420),
    Nat.mod_mod_of_dvd k (by decide : 10 ∣ 420),
    Nat.mod_mod_of_dvd k (by decide : 15 ∣ 420),
    Nat.mod_mod_of_dvd k (by decide : 4 ∣ 420),
    Nat.mod_mod_of_dvd k (by decide : 7 ∣ 420),
    Nat.mod_mod_of_dvd k (by decide : 12 ∣ 420),
    Nat.mod_mod_of_dvd k (by decide : 14 ∣ 420)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem parityTrialRow_bound (k : ℕ) : |parityTrialRow k| ≤ 91 := by
  rw [← parityTrialRow_mod k]
  exact (show ∀ i : Fin 420, |parityTrialRow i| ≤ 91 by decide +kernel) ⟨_, Nat.mod_lt _ (by decide)⟩

private theorem parityTrialRow_physical (k : ℕ) :
    hilbertSequence ((ramanujanPacketHilbert 2 - (1/2 : ℝ) • hilbertOne) -
      parityMixedTrial) (k + 1) = (parityTrialRow (k+1) : ℝ) / 50 := by
  rw [← anchoredEvaluationCLM_apply]
  unfold parityMixedTrial
  simp only [map_sub, map_add, map_smul, smul_eq_mul, anchoredEvaluationCLM_apply,
    hilbertSequence_ramanujanPacketHilbert, hilbertOne_sequence,
    ramanujanPacket_prime_eq_residue 2 Nat.prime_two, MeanOneSix.packet_six_residue,
    packet_ten_residue, packet_fifteen_residue, packet_twelve_residue, packet_fourteen_residue]
  simp only [zeroAnchor, Nat.succ_ne_zero, if_false, residue, parityTrialRow,
    Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_ofNat]
  ring

private def parityTrialHeadQ (K : ℕ) : ℚ :=
  ∑ k ∈ Finset.range K, ((parityTrialRow (k+1) : ℚ)/50)^2 /
    (((k : ℚ)+1)*((k : ℚ)+2))

private theorem parityTrialHead_cast (K : ℕ) :
    AmplitudeCertificates.head (fun k => (parityTrialRow k : ℝ) / 50) K =
      (parityTrialHeadQ K : ℝ) := by
  unfold AmplitudeCertificates.head parityTrialHeadQ
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  unfold paretoWeight
  ring

private theorem parityTrial_norm_le :
    ‖(ramanujanPacketHilbert 2 - (1/2 : ℝ) • hilbertOne) - parityMixedTrial‖ ^ 2 <
      11 / 60 := by
  let r := fun k => (parityTrialRow k : ℝ) / 50
  have hnorm : ‖(ramanujanPacketHilbert 2 - (1/2 : ℝ) • hilbertOne) -
      parityMixedTrial‖ ^ 2 = AmplitudeCertificates.energy r := by
    rw [hilbert_norm_weighted_sq, (hilbertSequence_square_summable _).tsum_eq_zero_add]
    simp only [hilbertSequence_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add,
      positiveWeight_succ, parityTrialRow_physical, AmplitudeCertificates.energy, r]
  have hr (k : ℕ) : |r (k+1)| ≤ (91/50 : ℝ) := by
    have h : |(parityTrialRow (k+1) : ℝ)| ≤ 91 := by
      exact_mod_cast parityTrialRow_bound (k+1)
    change |(parityTrialRow (k+1) : ℝ)/50| ≤ _
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 50), div_le_iff₀ (by norm_num)]
    linarith
  have h := (AmplitudeCertificates.certificate_bounds r (91/50) (by norm_num) hr 900).1
  rw [hnorm]
  apply lt_of_le_of_lt h
  unfold AmplitudeCertificates.certificate
  rw [show AmplitudeCertificates.head r 900 = _ from parityTrialHead_cast 900]
  have hc : parityTrialHeadQ 900 + (91/50 : ℚ)^2 / 901 < 11/60 := by
    set_option maxRecDepth 30000 in
    set_option maxHeartbeats 6000000 in
    decide +kernel
  have lift (t : ℚ) (ht : t + (91/50 : ℚ)^2 / 901 < 11/60) :
      (t : ℝ) + (91/50)^2 / ((900 : ℝ)+1) < 11/60 := by
    rw [show (900 : ℝ) + 1 = 901 by norm_num]
    have htR : ((t + (91/50 : ℚ)^2 / 901 : ℚ) : ℝ) < ((11/60 : ℚ) : ℝ) :=
      Rat.cast_lt.mpr ht
    push_cast at htR
    exact htR
  exact lift _ hc

/-- Every cutoff from fifteen onward captures more than 1/15 in squared projection
norm. The computation includes the complete Pareto tail. -/
theorem fixedTwo_mixed_capture_gt_one_fifteenth (B : ℕ) (hB : 15 ≤ B) :
    1 / 15 < ‖(mixedSpace (Finset.Icc 2 B)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 := by
  let K := mixedSpace (Finset.Icc 2 B)
  have h6 : ramanujanPacketHilbert 6 ∈ K :=
    mixed_packet_mul_of_coprime_mem_window (a := 2) (b := 3)
      (by decide) (by decide) (by decide) (by omega)
  have h10 : ramanujanPacketHilbert 10 ∈ K :=
    mixed_packet_mul_of_coprime_mem_window (a := 2) (b := 5)
      (by decide) (by decide) (by decide) (by omega)
  have h12 : ramanujanPacketHilbert 12 ∈ K :=
    mixed_packet_mul_of_coprime_mem_window (a := 3) (b := 4)
      (by decide) (by decide) (by decide) (by omega)
  have h14 : ramanujanPacketHilbert 14 ∈ K :=
    mixed_packet_mul_of_coprime_mem_window (a := 2) (b := 7)
      (by decide) (by decide) (by decide) (by omega)
  have h15 : ramanujanPacketHilbert 15 ∈ K :=
    mixed_packet_mul_of_coprime_mem_window (a := 3) (b := 5)
      (by decide) (by decide) (by decide) (by omega)
  have ht : parityMixedTrial ∈ K := K.add_mem (K.add_mem (K.add_mem (K.add_mem
    (K.smul_mem _ h6) (K.smul_mem _ h10)) (K.smul_mem _ h12))
    (K.smul_mem _ h14)) (K.smul_mem _ h15)
  have hb := fixedTwo_centered_trial_balance B ht
  dsimp only at hb
  linarith [parityTrial_norm_le,
    sq_nonneg (‖K.starProjection (ramanujanPacketHilbert 2) - parityMixedTrial‖)]

end RiemannResearch.RH.Pareto.PrimePowerSchur
