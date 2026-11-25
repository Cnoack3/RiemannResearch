import RiemannResearch.RH.CotangentContraction
import RiemannResearch.RH.CotangentMultiplication
import RiemannResearch.RH.MeanOneSix
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.ParetoParityAdjointCriterion
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The conductor-six correlation of the dyadic parity adjoint

The signed observation of the first mixed packet is evaluated by the
repository's complete cotangent expression for the period-twelve Gram matrix.
The finite cotangent multiplication at three removes the two twelfth angles.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

private theorem twelve_quarter : periodCotangent 12 3 = 1 := by
  unfold periodCotangent
  norm_num only [Nat.cast_ofNat]
  rw [show Real.pi*(3:ℝ)/12 = Real.pi/4 by ring,Real.cos_pi_div_four,Real.sin_pi_div_four]
  exact div_self (by positivity)

private theorem twelve_odd_sum : periodCotangent 12 1 + periodCotangent 12 5 = 4 := by
  have h := cotangent_finite_multiplication 3 (by norm_num) (1/12) (by norm_num) (by norm_num)
  norm_num [Fin.sum_univ_succ] at h
  have he (n : ℕ) : cotangentAt ((n:ℝ)/12) = periodCotangent 12 n := by
    unfold cotangentAt periodCotangent
    rw [show Real.pi*((n:ℝ)/12) = Real.pi*(n:ℝ)/12 by ring]
    norm_num
  have hk : cotangentAt (3/4) = -1 := by
    have h9 := he 9
    norm_num only [Nat.cast_ofNat] at h9
    rw [h9,
      show (9:ℕ) = 12-3 by decide, periodCotangent_negative_reflection 12 3 (by decide) (by decide),
      twelve_quarter]
  have hl : cotangentAt (1/4) = 1 := by
    have h3 := he 3
    norm_num only [Nat.cast_ofNat] at h3
    rw [h3, twelve_quarter]
  have ha : cotangentAt (1/12) = periodCotangent 12 1 := by simpa using he 1
  have hb : cotangentAt (5/12) = periodCotangent 12 5 := by simpa using he 5
  linarith only [h, ha,hb,hk,hl]

set_option maxHeartbeats 1600000 in
-- The two divisor lists expand against twelve finite residue classes.
private theorem packet_two_twelve_core :
    packetDifferenceCotangentCoreEntry 12 2 12 = 1/Real.sqrt 3-1 := by
  let F (a b : ℕ) := (ArithmeticFunction.moebius (2/a) : ℝ) *
    (ArithmeticFunction.moebius (12/b) : ℝ) * residueDifferenceCotangentCore 12 a b
  have hF : packetDifferenceCotangentCoreEntry 12 2 12 =
      ∑ a ∈ (2:ℕ).divisors, ∑ b ∈ (12:ℕ).divisors, F a b := by
    unfold packetDifferenceCotangentCoreEntry
    calc
      _ = ∑ a : (2:ℕ).divisors, ∑ b ∈ (12:ℕ).divisors, F a.val b := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_coe_sort (12:ℕ).divisors (F a.val)
      _ = _ := Finset.sum_coe_sort (2:ℕ).divisors (fun a => ∑ b ∈ (12:ℕ).divisors, F a b)
  have h4 : ArithmeticFunction.moebius 4 = 0 := by
    rw [show (4:ℕ) = 2*2 by rfl, moebius_prime_mul 2 2 Nat.prime_two]
    simp
  have h6 : ArithmeticFunction.moebius 6 = 1 := by
    rw [show (6:ℕ) = 2*3 by rfl, moebius_prime_mul 2 3 Nat.prime_two]
    norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  have h12 : ArithmeticFunction.moebius 12 = 0 := by
    rw [show (12:ℕ) = 2*6 by rfl, moebius_prime_mul 2 6 Nat.prime_two]
    norm_num
  have hcot2 : periodCotangent 12 2 = Real.sqrt 3 := by
    unfold periodCotangent
    norm_num only [Nat.cast_ofNat]
    rw [show Real.pi*2/12 = Real.pi/6 by ring,Real.cos_pi_div_six,Real.sin_pi_div_six]
    ring
  have hcot4 : periodCotangent 12 4 = 1/Real.sqrt 3 := by
    unfold periodCotangent
    norm_num only [Nat.cast_ofNat]
    rw [show Real.pi*4/12 = Real.pi/3 by ring,Real.cos_pi_div_three,Real.sin_pi_div_three]
    field_simp [(Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3)).ne']
  have hr (r : ℕ) (h : r ≤ 12) :
      periodCotangent 12 (12-r) = -periodCotangent 12 r :=
    periodCotangent_negative_reflection 12 r (by decide) h
  have h7 : periodCotangent 12 7 = -periodCotangent 12 5 := by simpa using hr 5 (by decide)
  have h8 : periodCotangent 12 8 = -periodCotangent 12 4 := by simpa using hr 4 (by decide)
  have h9 : periodCotangent 12 9 = -periodCotangent 12 3 := by simpa using hr 3 (by decide)
  have h10 : periodCotangent 12 10 = -periodCotangent 12 2 := by simpa using hr 2 (by decide)
  have h11 : periodCotangent 12 11 = -periodCotangent 12 1 := by simpa using hr 1 (by decide)
  rw [hF]
  norm_num [F, show (2:ℕ).divisors = {1,2} by decide,
    show (12:ℕ).divisors = {1,2,3,4,6,12} by decide, h4,h6,h12,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three, residueDifferenceCotangentCore,
    Fin.sum_univ_succ, centeredResidueProduct, residue, h7,h8,h9,h10,h11,hcot2,hcot4,twelve_quarter,
    periodCotangent_zero, periodCotangent_terminal 12 (by decide)]
  have hs : Real.sqrt 3 = 3 / Real.sqrt 3 := by
    apply (eq_div_iff (Real.sqrt_pos.mpr (by norm_num)).ne').mpr
    simpa only [← pow_two] using (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3))
  rw [div_eq_mul_inv] at hs
  linear_combination -(1/6:ℝ)*twelve_odd_sum+(1/4:ℝ)*hs

/-- Exact, nonzero correlation of the parity adjoint with a mean-zero mixed
packet. Equivalently, this is the full Gram entry for conductors two and twelve. -/
theorem parityAdjointPacket_inner_six :
    inner ℝ (ramanujanPacketHilbert 6) parityAdjointPacket =
      2*Real.log 2 - (1-1/Real.sqrt 3)*Real.pi := by
  have hd : hilbertDilation 2 (by decide) (ramanujanPacketHilbert 6) = ramanujanPacketHilbert 12 := by
    apply hilbertSequence_injective
    rw [hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert, hilbertSequence_ramanujanPacketHilbert]
    funext k
    exact (ramanujanPacket_mul_prime_of_dvd 2 6 k Nat.prime_two (by decide) (by decide)).symm
  have hzero : ArithmeticFunction.vonMangoldt 12 = 0 := by
    have hm := (mem_mixedClosure_iff_mem_closedSpace_and_mean_zero _).mp
      (mixed_packet_mem_closure 12 (by decide) (by decide))
    simpa only [hilbert_inner_one,hilbertSequence_ramanujanPacketHilbert,paretoMean_ramanujanPacket] using hm.2
  change inner ℝ _ ((hilbertDilationContinuous 2 (by decide)).adjoint (ramanujanPacketHilbert 2)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, hilbertDilationContinuous_apply, hd, real_inner_comm,
    hilbert_inner_weighted, hilbertSequence_ramanujanPacketHilbert, hilbertSequence_ramanujanPacketHilbert,
    packet_inner_eq_differenceCotangentCore 12 2 12 (by decide) (by decide) (by decide) (by decide) (by decide),
    packet_two_twelve_core,ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,hzero,
    show Nat.totient 12 = 4 by decide]
  push_cast
  ring

theorem parityAdjointPacket_inner_six_pos :
    0 < inner ℝ (ramanujanPacketHilbert 6) parityAdjointPacket := by
  rw [parityAdjointPacket_inner_six]
  have h : Real.sqrt 3 ≤ 7/4 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), sq_nonneg (Real.sqrt 3-7/4)]
  have hi : (4/7:ℝ) ≤ 1/Real.sqrt 3 := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr (by norm_num))).mpr
    linarith only [h]
  have hp := mul_le_mul_of_nonneg_right (show 1-1/Real.sqrt 3 ≤ 3/7 by linarith only [hi])
    Real.pi_pos.le
  linarith only [hp,Real.pi_lt_d2,Real.log_two_gt_d9]

end RiemannResearch.RH.Pareto.PrimePowerSchur
