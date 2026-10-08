/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CotangentContraction
import RiemannResearch.RH.MeanOneSix
import RiemannResearch.RH.PhysicalCoreMonotonicity

/-!
# A strictly improved exact physical trial at conductor thirty

The rational packet coefficients (8/15,1/2,1/30,1/6) at (2,3,5,6)
give f6+(H5-4H2)/30. The tangent has ordinary mean zero. The complete
physical error is evaluated through the proved original double-V core;
every V denominator is at most six. No finite-tail numerical Gram is used.
This is an unconditional finite bound, not an asymptotic saturation provider.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.MeanOneThirtyTrial
open PhysicalPacketCore PhysicalCoreMonotonicity

def cotFiveOne : ℝ := periodCotangent 5 1
def cotFiveTwo : ℝ := periodCotangent 5 2

private theorem sqrt_three_inv : (Real.sqrt 3)⁻¹ = Real.sqrt 3 / 3 := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  field_simp [ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
  nlinarith

private theorem cotangent_two_one : periodCotangent 2 1 = 0 := by
  unfold periodCotangent
  norm_num only [Nat.cast_ofNat,Nat.cast_one,mul_one]
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two]
  norm_num

private theorem cotangent_three_one : periodCotangent 3 1 = 1/Real.sqrt 3 := by
  unfold periodCotangent
  norm_num only [Nat.cast_ofNat,Nat.cast_one,mul_one]
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three]
  ring

private theorem cotangent_three_two : periodCotangent 3 2 = -1/Real.sqrt 3 := by
  have h := periodCotangent_negative_reflection 3 1 (by norm_num) (by norm_num)
  norm_num at h
  rw [h,cotangent_three_one]
  ring

private theorem cotangent_five_three : periodCotangent 5 3 = -cotFiveTwo := by
  rw [show 3 = 5-2 by decide,
    periodCotangent_negative_reflection 5 2 (by norm_num) (by norm_num)]
  rfl

private theorem cotangent_five_four : periodCotangent 5 4 = -cotFiveOne := by
  rw [show 4 = 5-1 by decide,
    periodCotangent_negative_reflection 5 1 (by norm_num) (by norm_num)]
  rfl

private theorem V_one (a : ℕ) : cotangentV a 1 = 0 := by
  simp [cotangentV]

private theorem V_two (a : ℕ) : cotangentV a 2 = 0 := by
  rw [cotangentV_eq_range a 2 (by norm_num)]
  norm_num [Finset.sum_range_succ, residue, periodCotangent_zero, cotangent_two_one]

private theorem V_three (a : ℕ) : cotangentV a 3 =
    ((a % 3 : ℕ) : ℝ) / (3*Real.sqrt 3) -
      ((a*2 % 3 : ℕ) : ℝ) / (3*Real.sqrt 3) := by
  rw [cotangentV_eq_range a 3 (by norm_num)]
  norm_num [Finset.sum_range_succ, residue, periodCotangent_zero,
    cotangent_three_one, cotangent_three_two]
  ring

private theorem V_five (a : ℕ) : cotangentV a 5 =
    (((a % 5 : ℕ) : ℝ) - ((a*4 % 5 : ℕ) : ℝ))*cotFiveOne/5 +
      (((a*2 % 5 : ℕ) : ℝ) - ((a*3 % 5 : ℕ) : ℝ))*cotFiveTwo/5 := by
  rw [cotangentV_eq_range a 5 (by norm_num)]
  norm_num [Finset.sum_range_succ, residue, periodCotangent_zero,
    cotangent_five_three, cotangent_five_four, cotFiveOne, cotFiveTwo]
  ring

private theorem V_six (a : ℕ) : cotangentV a 6 =
    (((a % 6 : ℕ) : ℝ) - ((a*5 % 6 : ℕ) : ℝ))*Real.sqrt 3/6 +
      (((a*2 % 6 : ℕ) : ℝ) - ((a*4 % 6 : ℕ) : ℝ))/(6*Real.sqrt 3) := by
  rw [cotangentV_eq_range a 6 (by norm_num)]
  norm_num [Finset.sum_range_succ, residue, MeanOneSix.cotangent_six_zero,
    MeanOneSix.cotangent_six_one, MeanOneSix.cotangent_six_two,
    MeanOneSix.cotangent_six_three, MeanOneSix.cotangent_six_four,
    MeanOneSix.cotangent_six_five]
  ring

def packetSet : Finset ℕ := {2,3,5,6}
def coefficients (q : packetSet) : ℝ :=
  if q.val = 2 then 8/15 else if q.val = 3 then 1/2
    else if q.val = 5 then 1/30 else 1/6

private def qTwo : packetSet := ⟨2, by decide⟩
private def qThree : packetSet := ⟨3, by decide⟩
private def qFive : packetSet := ⟨5, by decide⟩
private def qSix : packetSet := ⟨6, by decide⟩

private theorem sum_packetSet (f : packetSet → ℝ) :
    (∑ q : packetSet, f q) = f qTwo+f qThree+f qFive+f qSix := by
  classical
  have he : (Finset.univ : Finset packetSet) = {qTwo,qThree,qFive,qSix} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hq := q.property
    simp only [packetSet, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with hq|hq|hq|hq
    · left; exact Subtype.ext hq
    · right; left; exact Subtype.ext hq
    · right; right; left; exact Subtype.ext hq
    · right; right; right; exact Subtype.ext hq
  rw [he]
  simp [qTwo,qThree,qFive,qSix,add_assoc]

private theorem packetSet_legal : ∀ q ∈ packetSet, 1 < q := by
  intro q hq
  simp only [packetSet,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl <;> norm_num

private theorem packetSet_period : ∀ q ∈ packetSet, q ∣ 30 := by
  intro q hq
  simp only [packetSet,Finset.mem_insert,Finset.mem_singleton] at hq
  rcases hq with rfl|rfl|rfl|rfl <;> norm_num

def coreTable (d e : ℕ) : ℝ :=
  if d = 5 then
    if e = 2 then -(cotFiveOne+2*cotFiveTwo)/5
    else if e = 3 then -(2*cotFiveOne-cotFiveTwo)/5-1/(3*Real.sqrt 3)
    else if e = 5 then -(3*cotFiveOne+cotFiveTwo)/5
    else (3*cotFiveOne+cotFiveTwo)/5-2/Real.sqrt 3
  else if e = 5 then
    if d = 2 then -(cotFiveOne+2*cotFiveTwo)/5
    else if d = 3 then -(2*cotFiveOne-cotFiveTwo)/5-1/(3*Real.sqrt 3)
    else (3*cotFiveOne+cotFiveTwo)/5-2/Real.sqrt 3
  else MeanOneSix.coreTable d e

set_option maxHeartbeats 2000000 in
theorem packet_core_table (d e : ℕ) (hd : d ∈ packetSet) (he : e ∈ packetSet) :
    ramanujanCotangentCoreEntry d e = coreTable d e := by
  unfold ramanujanCotangentCoreEntry
  simp only [packetSet,Finset.mem_insert,Finset.mem_singleton] at hd he
  rcases hd with rfl|rfl|rfl|rfl <;> rcases he with rfl|rfl|rfl|rfl <;>
    norm_num [
      show (2 : ℕ).divisors = {1,2} by decide,
      show (3 : ℕ).divisors = {1,3} by decide,
      show (5 : ℕ).divisors = {1,5} by decide,
      show (6 : ℕ).divisors = {1,2,3,6} by decide,
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 5),
      V_one,V_two,V_three,V_five,V_six,coreTable,MeanOneSix.coreTable]
  all_goals
    simp only [div_eq_mul_inv,_root_.mul_inv_rev,sqrt_three_inv]
    ring

theorem coefficients_mean_one : ramanujanTotientVector packetSet ⬝ᵥ coefficients = 2 := by
  unfold dotProduct
  rw [sum_packetSet]
  norm_num [qTwo,qThree,qFive,qSix,coefficients,ramanujanTotientVector,
    show Nat.totient 2 = 1 by decide, show Nat.totient 3 = 2 by decide,
    show Nat.totient 5 = 4 by decide, show Nat.totient 6 = 2 by decide]

theorem synthesis_eq_screened_six (k : ℕ) :
    synthesis packetSet coefficients k =
      residue 2 k/2+residue 3 k/3+residue 6 k/6 +
        (ramanujanPacket 5 k-4*ramanujanPacket 2 k)/30 := by
  unfold synthesis FiniteSchur.combination
  rw [sum_packetSet]
  norm_num [qTwo,qThree,qFive,qSix,coefficients,
    ramanujanPacket_prime_eq_residue 2 (by norm_num),
    ramanujanPacket_prime_eq_residue 3 (by norm_num),
    ramanujanPacket_prime_eq_residue 5 (by norm_num), MeanOneSix.packet_six_residue]
  ring

theorem synthesis_period_mean_one :
    (∑ r : Fin 30, synthesis packetSet coefficients r.val)/(30 : ℝ) = 1 := by
  have hm := synthesis_period_mean 30 packetSet coefficients (by norm_num)
    packetSet_legal packetSet_period
  rw [coefficients_mean_one] at hm
  norm_num at hm
  exact hm

/-- Exact complete physical error, retaining the entire Pareto tail. -/
theorem trial_error : paretoError (synthesis packetSet coefficients) =
    1-Real.pi*(140*Real.sqrt 3+13*cotFiveOne+5*cotFiveTwo)/900 := by
  rw [synthesis_error_of_totient_constraint _ _ coefficients_mean_one,
    ← specified_core_eq_derivedCore_of_legal packetSet packetSet_legal]
  have hentry (i j : packetSet) := packet_core_table i.val j.val i.property j.property
  simp only [dotProduct,Matrix.mulVec]
  simp_rw [hentry]
  simp_rw [sum_packetSet]
  norm_num [qTwo,qThree,qFive,qSix,coefficients,coreTable,MeanOneSix.coreTable]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,sqrt_three_inv]
  ring

theorem cotFiveOne_gt_four_thirds : 4/3 < cotFiveOne := by
  have hsp : 0 < Real.sin (Real.pi/5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hc : (4/5 : ℝ) < Real.cos (Real.pi/5) := by
    rw [Real.cos_pi_div_five]
    have hsq : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg (5 : ℝ)
    nlinarith
  have hs : Real.sin (Real.pi/5) < 3/5 := by
    have hsq := Real.sin_sq_add_cos_sq (Real.pi/5)
    nlinarith
  unfold cotFiveOne periodCotangent
  norm_num only [Nat.cast_ofNat,Nat.cast_one,mul_one]
  exact (lt_div_iff₀ hsp).mpr (by linarith)

theorem cotFiveTwo_pos : 0 < cotFiveTwo := by
  change 0 < Real.cos (Real.pi*2/5)/Real.sin (Real.pi*2/5)
  exact div_pos
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩)
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos]))

/-- A strict arithmetic gain, established by exact trig inequalities. -/
theorem strict_trial_gain : 0 < 13*cotFiveOne+5*cotFiveTwo-10*Real.sqrt 3 := by
  have hsq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hroot : 10*Real.sqrt 3 < 52/3 := by nlinarith
  linarith [cotFiveOne_gt_four_thirds,cotFiveTwo_pos]

theorem trial_strictly_better_than_six :
    paretoError (synthesis packetSet coefficients) < 1-Real.pi/(2*Real.sqrt 3) := by
  rw [trial_error]
  have hg := mul_pos Real.pi_pos strict_trial_gain
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,sqrt_three_inv] at hg ⊢
  nlinarith

/-- The actual full seven-packet optimizer at thirty inherits the exact trial bound. -/
theorem constrained_minimum_thirty_le_trial :
    1+4*Real.pi/inverseCharge (divisorPackets 30) ≤
      1-Real.pi*(140*Real.sqrt 3+13*cotFiveOne+5*cotFiveTwo)/900 := by
  have hsub : packetSet ⊆ divisorPackets 30 := by decide
  have hmean : ramanujanTotientVector (divisorPackets 30) ⬝ᵥ
      extendCoefficients packetSet (divisorPackets 30) coefficients = 2 := by
    rw [totient_extendCoefficients packetSet _ _ hsub,coefficients_mean_one]
  have ho : ∃ p ∈ divisorPackets 30, p.Prime ∧ 2 < p := by
    exact ⟨3,by decide,by norm_num,by norm_num⟩
  have hm := (constrainedOptimizer_unique_minimum (divisorPackets 30)
    (divisorPackets_legal 30) ho _ hmean).1
  rw [synthesis_extendCoefficients packetSet _ _ hsub,trial_error] at hm
  exact hm

theorem constrained_minimum_thirty_strictly_better_than_six :
    1+4*Real.pi/inverseCharge (divisorPackets 30) < 1-Real.pi/(2*Real.sqrt 3) :=
  constrained_minimum_thirty_le_trial.trans_lt
    (by rw [← trial_error]; exact trial_strictly_better_than_six)

/-- The finite arithmetic trial improves the unconditional charge lower bound. -/
theorem inverseCharge_thirty_ge_trial :
    -3600/(140*Real.sqrt 3+13*cotFiveOne+5*cotFiveTwo) ≤
      inverseCharge (divisorPackets 30) := by
  let K : ℝ := 140*Real.sqrt 3+13*cotFiveOne+5*cotFiveTwo
  have hc1 : 0 < cotFiveOne := lt_trans (by norm_num) cotFiveOne_gt_four_thirds
  have hc2 := cotFiveTwo_pos
  have hK : 0 < K := by dsimp [K]; positivity
  have ho : ∃ p ∈ divisorPackets 30, p.Prime ∧ 2 < p :=
    ⟨3,by decide,by norm_num,by norm_num⟩
  have hC := inverseCharge_neg (divisorPackets 30) (divisorPackets_legal 30) ho
  have hfrac : Real.pi*K/900 ≤ 4*Real.pi/(-inverseCharge (divisorPackets 30)) := by
    have hm := constrained_minimum_thirty_le_trial
    change 1+4*Real.pi/inverseCharge (divisorPackets 30) ≤ 1-Real.pi*K/900 at hm
    rw [div_neg]
    linarith only [hm]
  have hm := (le_div_iff₀ (neg_pos.mpr hC)).mp hfrac
  have hm' : Real.pi*(-K*inverseCharge (divisorPackets 30)/900) ≤ Real.pi*4 := by
    nlinarith only [hm]
  have hnum := (mul_le_mul_iff_right₀ Real.pi_pos).mp hm'
  change -3600/K ≤ inverseCharge (divisorPackets 30)
  exact (div_le_iff₀ hK).mpr (by nlinarith only [hnum])

/-- Every later multiple of thirty inherits the stronger complete error bound. -/
theorem constrained_minimum_le_trial_of_thirty_dvd (L : ℕ) (hL : 2 < L)
    (h30 : 30 ∣ L) :
    1+4*Real.pi/inverseCharge (divisorPackets L) ≤
      1-Real.pi*(140*Real.sqrt 3+13*cotFiveOne+5*cotFiveTwo)/900 := by
  have ho : ∃ p ∈ divisorPackets 30, p.Prime ∧ 2 < p :=
    ⟨3,by decide,by norm_num,by norm_num⟩
  have hm := constrained_error_antitone (divisorPackets 30) (divisorPackets L)
    (divisorPackets_subset_of_dvd 30 L h30 (by omega))
    (divisorPackets_legal 30) (divisorPackets_legal L) ho
  exact hm.trans constrained_minimum_thirty_le_trial

/-- The exact improved charge bound persists at every physical multiple of thirty. -/
theorem inverseCharge_ge_trial_of_thirty_dvd (L : ℕ) (hL : 2 < L)
    (h30 : 30 ∣ L) :
    -3600/(140*Real.sqrt 3+13*cotFiveOne+5*cotFiveTwo) ≤
      inverseCharge (divisorPackets L) := by
  have ho : ∃ p ∈ divisorPackets 30, p.Prime ∧ 2 < p :=
    ⟨3,by decide,by norm_num,by norm_num⟩
  exact inverseCharge_thirty_ge_trial.trans
    (inverseCharge_mono (divisorPackets 30) (divisorPackets L)
      (divisorPackets_subset_of_dvd 30 L h30 (by omega))
      (divisorPackets_legal 30) (divisorPackets_legal L) ho)

/-- A stronger rational trial in the same four physical packet coordinates. -/
def improvedCoefficients (q : packetSet) : ℝ :=
  if q.val = 2 then 1/2 else if q.val = 3 then 1/3
    else if q.val = 5 then 1/5 else 1/60

theorem improvedCoefficients_mean_one :
    ramanujanTotientVector packetSet ⬝ᵥ improvedCoefficients = 2 := by
  unfold dotProduct
  rw [sum_packetSet]
  norm_num [qTwo,qThree,qFive,qSix,improvedCoefficients,ramanujanTotientVector,
    show Nat.totient 2 = 1 by decide, show Nat.totient 3 = 2 by decide,
    show Nat.totient 5 = 4 by decide, show Nat.totient 6 = 2 by decide]

theorem improved_synthesis_period_mean_one :
    (∑ r : Fin 30, synthesis packetSet improvedCoefficients r.val)/(30 : ℝ) = 1 := by
  have hm := synthesis_period_mean 30 packetSet improvedCoefficients (by norm_num)
    packetSet_legal packetSet_period
  rw [improvedCoefficients_mean_one] at hm
  norm_num at hm
  exact hm

/-- A stronger exact complete error, using no additional core entries. -/
theorem improved_trial_error : paretoError (synthesis packetSet improvedCoefficients) =
    1-Real.pi*(797*Real.sqrt 3+1224*cotFiveOne+648*cotFiveTwo)/10800 := by
  rw [synthesis_error_of_totient_constraint _ _ improvedCoefficients_mean_one,
    ← specified_core_eq_derivedCore_of_legal packetSet packetSet_legal]
  have hentry (i j : packetSet) := packet_core_table i.val j.val i.property j.property
  simp only [dotProduct,Matrix.mulVec]
  simp_rw [hentry]
  simp_rw [sum_packetSet]
  norm_num [qTwo,qThree,qFive,qSix,improvedCoefficients,coreTable,MeanOneSix.coreTable]
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,sqrt_three_inv]
  ring

theorem cotFiveTwo_gt_seven_twentyfifths : 7/25 < cotFiveTwo := by
  have hc : (4/5 : ℝ) < Real.cos (Real.pi/5) := by
    rw [Real.cos_pi_div_five]
    have hsq : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
    have hn := Real.sqrt_nonneg (5 : ℝ)
    nlinarith
  have hc2 : (7/25 : ℝ) < Real.cos (Real.pi*2/5) := by
    rw [show Real.pi*2/5 = 2*(Real.pi/5) by ring,Real.cos_two_mul]
    nlinarith [sq_nonneg (Real.cos (Real.pi/5)-4/5)]
  have hs : 0 < Real.sin (Real.pi*2/5) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  change 7/25 < Real.cos (Real.pi*2/5)/Real.sin (Real.pi*2/5)
  apply (lt_div_iff₀ hs).mpr
  nlinarith only [hc2,Real.sin_le_one (Real.pi*2/5)]

theorem improved_strict_trial_gain :
    0 < 1224*cotFiveOne+648*cotFiveTwo-1003*Real.sqrt 3 := by
  have hsq : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hroot : Real.sqrt 3 < 7/4 := by nlinarith
  linarith [cotFiveOne_gt_four_thirds,cotFiveTwo_gt_seven_twentyfifths]

theorem improved_trial_strictly_better_than_six :
    paretoError (synthesis packetSet improvedCoefficients) <
      1-Real.pi/(2*Real.sqrt 3) := by
  rw [improved_trial_error]
  have hg := mul_pos Real.pi_pos improved_strict_trial_gain
  simp only [div_eq_mul_inv,_root_.mul_inv_rev,sqrt_three_inv] at hg ⊢
  nlinarith

theorem constrained_minimum_thirty_le_improved_trial :
    1+4*Real.pi/inverseCharge (divisorPackets 30) ≤
      1-Real.pi*(797*Real.sqrt 3+1224*cotFiveOne+648*cotFiveTwo)/10800 := by
  have hsub : packetSet ⊆ divisorPackets 30 := by decide
  have hmean : ramanujanTotientVector (divisorPackets 30) ⬝ᵥ
      extendCoefficients packetSet (divisorPackets 30) improvedCoefficients = 2 := by
    rw [totient_extendCoefficients packetSet _ _ hsub,improvedCoefficients_mean_one]
  have ho : ∃ p ∈ divisorPackets 30, p.Prime ∧ 2 < p :=
    ⟨3,by decide,by norm_num,by norm_num⟩
  have hm := (constrainedOptimizer_unique_minimum (divisorPackets 30)
    (divisorPackets_legal 30) ho _ hmean).1
  rw [synthesis_extendCoefficients packetSet _ _ hsub,improved_trial_error] at hm
  exact hm

theorem inverseCharge_thirty_ge_improved_trial :
    -43200/(797*Real.sqrt 3+1224*cotFiveOne+648*cotFiveTwo) ≤
      inverseCharge (divisorPackets 30) := by
  let K : ℝ := 797*Real.sqrt 3+1224*cotFiveOne+648*cotFiveTwo
  have hc1 : 0 < cotFiveOne := lt_trans (by norm_num) cotFiveOne_gt_four_thirds
  have hc2 := cotFiveTwo_pos
  have hK : 0 < K := by dsimp [K]; positivity
  have ho : ∃ p ∈ divisorPackets 30, p.Prime ∧ 2 < p :=
    ⟨3,by decide,by norm_num,by norm_num⟩
  have hC := inverseCharge_neg (divisorPackets 30) (divisorPackets_legal 30) ho
  have hfrac : Real.pi*K/10800 ≤ 4*Real.pi/(-inverseCharge (divisorPackets 30)) := by
    have hm := constrained_minimum_thirty_le_improved_trial
    change 1+4*Real.pi/inverseCharge (divisorPackets 30) ≤ 1-Real.pi*K/10800 at hm
    rw [div_neg]
    linarith only [hm]
  have hm := (le_div_iff₀ (neg_pos.mpr hC)).mp hfrac
  have hm' : Real.pi*(-K*inverseCharge (divisorPackets 30)/10800) ≤ Real.pi*4 := by
    nlinarith only [hm]
  have hnum := (mul_le_mul_iff_right₀ Real.pi_pos).mp hm'
  change -43200/K ≤ inverseCharge (divisorPackets 30)
  exact (div_le_iff₀ hK).mpr (by nlinarith only [hnum])

theorem constrained_minimum_le_improved_trial_of_thirty_dvd (L : ℕ) (hL : 2 < L)
    (h30 : 30 ∣ L) :
    1+4*Real.pi/inverseCharge (divisorPackets L) ≤
      1-Real.pi*(797*Real.sqrt 3+1224*cotFiveOne+648*cotFiveTwo)/10800 := by
  have ho : ∃ p ∈ divisorPackets 30, p.Prime ∧ 2 < p :=
    ⟨3,by decide,by norm_num,by norm_num⟩
  have hm := constrained_error_antitone (divisorPackets 30) (divisorPackets L)
    (divisorPackets_subset_of_dvd 30 L h30 (by omega))
    (divisorPackets_legal 30) (divisorPackets_legal L) ho
  exact hm.trans constrained_minimum_thirty_le_improved_trial

theorem inverseCharge_ge_improved_trial_of_thirty_dvd (L : ℕ) (hL : 2 < L)
    (h30 : 30 ∣ L) :
    -43200/(797*Real.sqrt 3+1224*cotFiveOne+648*cotFiveTwo) ≤
      inverseCharge (divisorPackets L) := by
  have ho : ∃ p ∈ divisorPackets 30, p.Prime ∧ 2 < p :=
    ⟨3,by decide,by norm_num,by norm_num⟩
  exact inverseCharge_thirty_ge_improved_trial.trans
    (inverseCharge_mono (divisorPackets 30) (divisorPackets L)
      (divisorPackets_subset_of_dvd 30 L h30 (by omega))
      (divisorPackets_legal 30) (divisorPackets_legal L) ho)

end RiemannResearch.RH.Pareto.MeanOneThirtyTrial
