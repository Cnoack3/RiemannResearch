import RiemannResearch.RH.MixedConductorCaptureGains
import RiemannResearch.RH.MixedConductorDilation
import RiemannResearch.RH.ThresholdHilbertProjection
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A ternary digit separates the conductor-six orbit

The indicator of leading ternary digit one is fixed by the adjoint of
the scaled dilation by three. After centering, it annihilates every
dilation of the conductor-six packet and pairs positively with centered
parity. This gives a uniform squared-error lower bound on the closed orbit.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.TernaryOrbit

/-- On a positive integer this is the indicator that its leading ternary
digit equals one. The zero index has value zero. -/
def digit (n : ℕ) : ℝ :=
  if h : n < 3 then (if n = 1 then 1 else 0) else digit (n / 3)
termination_by n
decreasing_by omega

private theorem digit_small {n : ℕ} (hn : n < 3) :
    digit n = (if n = 1 then 1 else 0) := by rw [digit, dif_pos hn]

private theorem digit_zero : digit 0 = 0 := by
  rw [digit_small (by decide), if_neg (by decide)]

private theorem digit_one : digit 1 = 1 := by
  rw [digit_small (by decide), if_pos rfl]

private theorem digit_three : digit 3 = 1 := by
  rw [digit, dif_neg (by decide)]
  exact digit_one

private theorem digit_five : digit 5 = 1 := by
  rw [digit, dif_neg (by decide)]
  exact digit_one

private theorem digit_cases (n : ℕ) : digit n = 0 ∨ digit n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [digit]
    split_ifs with h h1
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact ih (n / 3) (by omega)

private theorem digit_sq (n : ℕ) : digit n ^ 2 = digit n := by
  rcases digit_cases n with hn | hn <;> rw [hn] <;> norm_num

private theorem digit_step (n : ℕ) :
    digit n = (if n = 1 then 1 else 0) + digit (n / 3) := by
  by_cases h : n < 3
  · rw [digit_small h, Nat.div_eq_of_lt h, digit_zero, add_zero]
  · have hn : n ≠ 1 := by omega
    conv_lhs => rw [digit, dif_neg h]
    simp [hn]

def digitVector : ThresholdHilbert := sequenceHilbert digit
  (weighted_summable_of_bounded (C := 1) fun n => by
    rcases digit_cases n with h | h <;> simp [h])

@[simp] theorem digitVector_sequence : hilbertSequence digitVector = digit :=
  hilbertSequence_sequenceHilbert _ _ digit_zero

private def firstSite : ThresholdHilbert := sequenceHilbert (fun n => if n = 1 then 1 else 0)
  (weighted_summable_of_bounded (C := 1) fun n => by split_ifs <;> norm_num)

private theorem firstSite_sequence :
    hilbertSequence firstSite = fun n => if n = 1 then 1 else 0 :=
  hilbertSequence_sequenceHilbert _ _ (by norm_num)

private theorem firstSite_pair (f : ThresholdHilbert) :
    inner ℝ f firstSite = (1 / 2 : ℝ) * hilbertSequence f 1 := by
  rw [hilbert_inner_weighted, firstSite_sequence]
  unfold paretoInner
  rw [tsum_eq_single 1 (fun k hk => by simp [hk])]
  norm_num [positiveWeight]

private theorem digitVector_split :
    digitVector = firstSite + (1 / 3 : ℝ) • hilbertDilation 3 (by decide) digitVector := by
  apply hilbertSequence_injective
  funext n
  conv_rhs => rw [← anchoredEvaluationCLM_apply, map_add, map_smul]
  simp only [anchoredEvaluationCLM_apply, digitVector_sequence, firstSite_sequence,
    hilbertDilation_sequence, dilation, smul_eq_mul, Nat.cast_ofNat]
  rw [show (1 / 3 : ℝ) * (3 * digit (n / 3)) = digit (n / 3) by ring]
  exact digit_step n

theorem digitVector_mean : inner ℝ digitVector hilbertOne = 3 / 4 := by
  have he := congrArg (fun z : ThresholdHilbert => inner ℝ z hilbertOne) digitVector_split
  change inner ℝ digitVector hilbertOne = inner ℝ (_ + _) hilbertOne at he
  have hfirst : inner ℝ firstSite hilbertOne = 1/2 := by
    calc
      _ = inner ℝ hilbertOne firstSite := real_inner_comm ..
      _ = _ := by rw [firstSite_pair, hilbertOne_sequence]; norm_num [zeroAnchor]
  have hm : inner ℝ (hilbertDilation 3 (by decide) digitVector) hilbertOne =
      inner ℝ digitVector hilbertOne := by
    simp only [hilbert_inner_one, hilbertDilation_mean]
  rw [inner_add_left, real_inner_smul_left, hfirst, hm] at he
  linarith

theorem digitVector_dilation_pair (f : ThresholdHilbert) :
    inner ℝ (hilbertDilation 3 (by decide) f) digitVector = inner ℝ f digitVector := by
  conv_lhs => rw [digitVector_split]
  rw [inner_add_right, real_inner_smul_right, firstSite_pair,
    hilbertDilation_sequence, hilbertDilation_inner]
  norm_num [dilation] <;> ring

/-- Centering keeps the dilation invariance and reduces the witness norm. -/
def centeredDigit : ThresholdHilbert := digitVector - (3 / 4 : ℝ) • hilbertOne

theorem centeredDigit_dilation_pair (f : ThresholdHilbert) :
    inner ℝ (hilbertDilation 3 (by decide) f) centeredDigit = inner ℝ f centeredDigit := by
  unfold centeredDigit
  simp only [inner_sub_right, real_inner_smul_right, digitVector_dilation_pair,
    hilbert_inner_one, hilbertDilation_mean]

theorem centeredDigit_norm_sq : ‖centeredDigit‖ ^ 2 = 3 / 16 := by
  have hd : ‖digitVector‖ ^ 2 = 3 / 4 := by
    calc
      _ = paretoMean digit := by
        rw [hilbert_norm_weighted_sq, digitVector_sequence]
        exact tsum_congr fun k => by rw [digit_sq]
      _ = _ := by simpa only [hilbert_inner_one, digitVector_sequence] using digitVector_mean
  rw [centeredDigit, norm_sub_sq_real, real_inner_smul_right, digitVector_mean,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hilbertOne_norm_sq, hd]
  norm_num

private theorem parity_digit_lower :
    (37 / 60 : ℝ) ≤ inner ℝ (ramanujanPacketHilbert 2) digitVector := by
  let f : ℕ → ℝ := fun k => positiveWeight k * (residue 2 k * digit k)
  have hp : hilbertSequence (ramanujanPacketHilbert 2) = residue 2 := by
    rw [hilbertSequence_ramanujanPacketHilbert]
    exact ramanujanPacket_prime_eq_residue 2 Nat.prime_two
  have hs := weighted_product_summable_of_square
    (hilbertSequence_square_summable (ramanujanPacketHilbert 2))
    (hilbertSequence_square_summable digitVector)
  rw [hp, digitVector_sequence] at hs
  have hnn (k : ℕ) : 0 ≤ f k := by
    have h : 0 ≤ digit k := by rcases digit_cases k with h | h <;> simp [h]
    exact mul_nonneg (positiveWeight_nonneg _) (mul_nonneg (Nat.cast_nonneg _) h)
  rw [hilbert_inner_weighted, hp, digitVector_sequence]
  change (37 / 60 : ℝ) ≤ ∑' k, f k
  calc
    _ = ∑ k ∈ ({1, 3, 5} : Finset ℕ), f k := by norm_num [f, residue, positiveWeight, digit_one, digit_three, digit_five]
    _ ≤ _ := Summable.sum_le_tsum _ (fun k _ => hnn k) hs

theorem centeredParity_pair_gt : (577 / 6000 : ℝ) <
    inner ℝ CaptureGains.centeredParity centeredDigit := by
  have hq : inner ℝ (ramanujanPacketHilbert 2) hilbertOne = Real.log 2 := by
    rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert,
      paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hone : inner ℝ hilbertOne digitVector = 3 / 4 := (real_inner_comm ..).trans digitVector_mean
  have hl : Real.log 2 < 347 / 500 := lt_trans Real.log_two_lt_d9 (by norm_num)
  rw [CaptureGains.centeredParity, centeredDigit, inner_sub_left, real_inner_smul_left]
  simp only [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    hilbertOne_norm_sq, hq, hone]
  linarith only [parity_digit_lower, hl]

private theorem commute_three_pair (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    inner ℝ (hilbertDilation m hm (hilbertDilation 3 (by decide) f)) centeredDigit =
      inner ℝ (hilbertDilation m hm f) centeredDigit := by
  calc
    _ = inner ℝ (hilbertDilation 3 (by decide) (hilbertDilation m hm f)) centeredDigit := by
      rw [hilbertDilation_comp, hilbertDilation_comp]
      have hcong (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (he : i = j) :
          hilbertDilation i hi f = hilbertDilation j hj f := by subst j; rfl
      exact congrArg (fun v : ThresholdHilbert => inner ℝ v centeredDigit)
        (hcong _ _ _ _ (Nat.mul_comm m 3))
    _ = _ := centeredDigit_dilation_pair _

private theorem triple_packet (q : ℕ) (hq : 1 < q) :
    ramanujanPacketHilbert (3*q) = hilbertDilation 3 (by decide) (ramanujanPacketHilbert q) -
      (if 3 ∣ q then 0 else ramanujanPacketHilbert q) := by
  apply hilbertSequence_injective
  funext n
  conv_rhs => rw [← anchoredEvaluationCLM_apply, map_sub]
  by_cases hd : 3 ∣ q
  · simpa only [if_pos hd, map_zero, anchoredEvaluationCLM_apply,
      hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert] using
      (ramanujanPacket_mul_prime 3 q n Nat.prime_three hq)
  · simpa only [if_neg hd, anchoredEvaluationCLM_apply,
      hilbertDilation_sequence, hilbertSequence_ramanujanPacketHilbert] using
      (ramanujanPacket_mul_prime 3 q n Nat.prime_three hq)

private theorem triple_packet_pair (m : ℕ) (hm : 0 < m) (q : ℕ) (hq : 1 < q) :
    inner ℝ (hilbertDilation m hm (ramanujanPacketHilbert (3*q))) centeredDigit =
      if 3 ∣ q then inner ℝ (hilbertDilation m hm (ramanujanPacketHilbert q)) centeredDigit
      else 0 := by
  rw [triple_packet q hq]
  by_cases hd : 3 ∣ q
  · simpa only [if_pos hd, sub_zero] using commute_three_pair m hm (ramanujanPacketHilbert q)
  · simp only [if_neg hd]
    change inner ℝ ((hilbertDilationLinear m hm) (_ - _)) centeredDigit = 0
    rw [map_sub, inner_sub_left]
    exact sub_eq_zero.mpr (commute_three_pair m hm _)

/-- Every conductor with positive 3-adic valuation and a nontrivial factor
coprime to three is annihilated, including after any further integer dilation. -/
theorem ternary_mixed_layer_pair_zero (a r m : ℕ) (hr : 1 < r) (h3 : ¬ 3 ∣ r)
    (hm : 0 < m) :
    inner ℝ (hilbertDilation m hm (ramanujanPacketHilbert (3 ^ (a + 1) * r)))
      centeredDigit = 0 := by
  induction a with
  | zero => simpa [h3] using triple_packet_pair m hm r hr
  | succ a ih =>
    have hp : 0 < 3 ^ (a + 1) := by positivity
    have hd : 3 ∣ 3 ^ (a + 1) * r :=
      (dvd_pow_self 3 (by omega : a + 1 ≠ 0)).trans (dvd_mul_right _ _)
    rw [pow_succ' 3 (a + 1), Nat.mul_assoc,
      triple_packet_pair m hm _ (hr.trans_le (Nat.le_mul_of_pos_left _ hp)), if_pos hd]
    exact ih

theorem dilated_six_pair_zero (m : ℕ) (hm : 0 < m) :
    inner ℝ (hilbertDilation m hm (ramanujanPacketHilbert 6)) centeredDigit = 0 :=
  ternary_mixed_layer_pair_zero 0 2 m (by decide) (by decide) hm

/-- The closed span of all positive integer dilations of the mixed packet J₆. -/
def sixOrbit : Submodule ℝ ThresholdHilbert :=
  (Submodule.span ℝ (Set.range (fun m : ℕ =>
    hilbertDilation (m + 1) (by omega) (ramanujanPacketHilbert 6)))).topologicalClosure

theorem sixOrbit_orthogonal : centeredDigit ∈ sixOrbitᗮ := by
  let F := innerSL ℝ centeredDigit
  have hle : sixOrbit ≤ F.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨m, rfl⟩
      change inner ℝ centeredDigit _ = 0
      exact (real_inner_comm ..).trans (dilated_six_pair_zero _ _)
    · exact F.isClosed_ker
  apply (sixOrbit.mem_orthogonal _).mpr
  intro x hx
  exact (real_inner_comm ..).trans (hle hx)

/-- The witness bounds the error of every vector it annihilates. -/
theorem error_gt_of_centeredDigit_pair_zero {x : ThresholdHilbert}
    (h0 : inner ℝ x centeredDigit = 0) :
    (49 / 1000 : ℝ) < ‖CaptureGains.centeredParity - x‖ ^ 2 := by
  have hh := centeredParity_pair_gt
  have hl : (577 / 6000 : ℝ) < inner ℝ (CaptureGains.centeredParity - x) centeredDigit := by
    rwa [inner_sub_left, h0, sub_zero]
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
    (abs_real_inner_le_norm (CaptureGains.centeredParity - x) centeredDigit)
  rw [sq_abs, mul_pow, centeredDigit_norm_sq] at hs
  have hsq := (sq_lt_sq₀ (by norm_num : (0 : ℝ) ≤ 577/6000) (by linarith : 0 ≤
    inner ℝ (CaptureGains.centeredParity - x) centeredDigit)).mpr hl
  linarith only [hs, hsq]

/-- Every vector in the closed conductor-six orbit has squared error above
the bound achieved by the rational full mixed-window trial at conductor 120. -/
theorem sixOrbit_error_gt {x : ThresholdHilbert} (hx : x ∈ sixOrbit) :
    (49 / 1000 : ℝ) < ‖CaptureGains.centeredParity - x‖ ^ 2 :=
  error_gt_of_centeredDigit_pair_zero
    ((sixOrbit.mem_orthogonal _).mp sixOrbit_orthogonal x hx)

/-- The first mixed conductor coprime to three already detects the witness.
Four physical sites suffice for the signed estimate. -/
theorem packet_ten_pair_le : inner ℝ (ramanujanPacketHilbert 10) centeredDigit ≤ -(1 / 30) := by
  let J := ramanujanPacketHilbert 10
  have hj (k : ℕ) : hilbertSequence J k =
      (5 : ℝ) * ((k / 5 % 2 : ℕ) : ℝ) - (k % 2 : ℕ) := by
    have h := ramanujanPacket_mul_prime 5 2 k (by decide) (by decide)
    have h5 : ¬ 5 ∣ 2 := by decide
    simpa only [J, hilbertSequence_ramanujanPacketHilbert, show 5 * 2 = 10 by decide,
      if_neg h5, ramanujanPacket_prime_eq_residue 2 Nat.prime_two, dilation, residue,
      Nat.cast_ofNat] using h
  have hjle (k : ℕ) : hilbertSequence J k ≤ 5 := by
    rw [hj]
    have hb : (k / 5 % 2 : ℕ) ≤ 1 := by omega
    have hb' : ((k / 5 % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hb
    linarith [Nat.cast_nonneg (α := ℝ) (k % 2)]
  let f : ℕ → ℝ := fun k => positiveWeight k * ((5 - hilbertSequence J k) * digit k)
  have hdS : Summable (fun k => positiveWeight k * digit k) :=
    weighted_summable_of_bounded (C := 1) (fun k => by rcases digit_cases k with h | h <;> simp [h])
  have hjS := weighted_product_summable_of_square (hilbertSequence_square_summable J)
    (hilbertSequence_square_summable digitVector)
  rw [digitVector_sequence] at hjS
  have he (k : ℕ) : positiveWeight k * ((5 - hilbertSequence J k) * digit k) =
      5 * (positiveWeight k * digit k) -
        positiveWeight k * (hilbertSequence J k * digit k) := by ring
  have hs : Summable f := ((hdS.mul_left 5).sub hjS).congr (fun k => (he k).symm)
  have hnon (k : ℕ) : 0 ≤ f k := by
    have h : 0 ≤ digit k := by rcases digit_cases k with h | h <;> simp [h]
    exact mul_nonneg (positiveWeight_nonneg _) (mul_nonneg (sub_nonneg.mpr (hjle k)) h)
  have hfour : digit 4 = 1 := by rw [digit, dif_neg (by decide)]; exact digit_one
  have hsum : (227 / 60 : ℝ) ≤ ∑' k, f k := by
    calc
      _ = ∑ k ∈ ({1, 3, 4, 5} : Finset ℕ), f k := by
        norm_num [f, hj, positiveWeight, digit_one, digit_three, hfour, digit_five]
      _ ≤ _ := Summable.sum_le_tsum _ (fun k _ => hnon k) hs
  have hdiff : (∑' k, f k) = 5 * inner ℝ digitVector hilbertOne - inner ℝ J digitVector := by
    rw [hilbert_inner_one, hilbert_inner_weighted, digitVector_sequence]
    unfold paretoMean paretoInner
    simp only [f, he]
    rw [Summable.tsum_sub (hdS.mul_left 5) hjS, tsum_mul_left]
  have hm : inner ℝ J hilbertOne = 0 := by
    have h := mixed_packet_inner_one (Finset.Icc 2 10)
      (⟨10, Finset.mem_filter.mpr ⟨by decide, by decide⟩⟩ : mixedConductors (Finset.Icc 2 10))
    exact h
  change inner ℝ J (digitVector - (3 / 4 : ℝ) • hilbertOne) ≤ _
  rw [inner_sub_right, real_inner_smul_right, hm, mul_zero, sub_zero]
  rw [digitVector_mean] at hdiff
  linarith only [hsum, hdiff]

theorem packet_ten_not_mem_sixOrbit : ramanujanPacketHilbert 10 ∉ sixOrbit := by
  intro h
  have hz := (sixOrbit.mem_orthogonal _).mp sixOrbit_orthogonal _ h
  linarith only [hz, packet_ten_pair_le]

end RiemannResearch.RH.Pareto.PrimePowerSchur.TernaryOrbit
