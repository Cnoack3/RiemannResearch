import RiemannResearch.RH.DilationWaveletAsymptoticTargets
import RiemannResearch.Analysis.PeriodicHarmonicMean
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
Exact adjacent binary-wavelet logarithmic asymptotic.
The proof retains a nonnegative
tail bounded by 4/[m(m+1)] after evaluating disjoint moved-jump intervals.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter
noncomputable section

private theorem mother_value (k : ℕ) :
    dilationWaveletSequence 2 1 k =
      if k % 4 = 1 then 1 else if k % 4 = 2 then -1 else 0 := by
  have hk : k % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases h : k % 4
  all_goals
    have h1 : k % 2 = (k % 4) % 2 := by omega
    have h2 : k / 2 % 2 = (k % 4) / 2 := by omega
    simp [dilationWaveletSequence, digitSequence, h1, h2, h]

private theorem mother_jump (j : ℕ) (hj : 0 < j) :
    dilationWaveletSequence 2 1 j - dilationWaveletSequence 2 1 (j-1) =
      binaryWaveletJump j := by
  rw [mother_value, mother_value]
  have hj4 : j % 4 < 4 := Nat.mod_lt _ (by omega)
  interval_cases h : j % 4
  all_goals
    have hp : (j-1) % 4 = (j % 4 + 3) % 4 := by omega
    norm_num [binaryWaveletJump, h, hp]

private def jumpSq (j : ℕ) : ℝ := binaryWaveletJump j ^ 2

private theorem jumpSq_bounds (j : ℕ) : 0 ≤ jumpSq j ∧ jumpSq j ≤ 4 := by
  unfold jumpSq binaryWaveletJump
  split_ifs <;> norm_num

private def jumpMask (m j k : ℕ) : ℝ :=
  if k ∈ Finset.Ico (m*j) ((m+1)*j) then positiveWeight k * jumpSq j else 0

private def waveletEnergyTerm (m k : ℕ) : ℝ := positiveWeight k *
  (dilationWaveletSequence 2 m k - dilationWaveletSequence 2 (m+1) k)^2

private def waveletTailTerm (m k : ℕ) : ℝ :=
  if m*(m+1) ≤ k then waveletEnergyTerm m k else 0

private theorem interval_quotients (m j k : ℕ) (hm : 0 < m)
    (hj : 0 < j) (hjm : j ≤ m)
    (hk : k ∈ Finset.Ico (m*j) ((m+1)*j)) :
    k/m = j ∧ k/(m+1) = j-1 := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
  constructor
  · apply Nat.div_eq_of_lt_le
    · nlinarith
    · nlinarith
  · apply Nat.div_eq_of_lt_le
    · have he : j-1+1 = j := by omega
      have hh : (m+1)*(j-1) ≤ m*j := by nlinarith
      exact (by simpa only [Nat.mul_comm] using hh.trans hlo)
    · have he : j-1+1 = j := by omega
      simpa only [he, Nat.mul_comm] using hhi

private theorem interval_value (m j k : ℕ) (hm : 0 < m)
    (hj : 0 < j) (hjm : j ≤ m)
    (hk : k ∈ Finset.Ico (m*j) ((m+1)*j)) :
    waveletEnergyTerm m k = positiveWeight k * jumpSq j := by
  obtain ⟨hq, hq'⟩ := interval_quotients m j k hm hj hjm hk
  unfold waveletEnergyTerm jumpSq
  rw [dilationWaveletSequence_two_pullback m k,
    dilationWaveletSequence_two_pullback (m+1) k, hq, hq', mother_jump j hj]

private theorem jumpMask_summable (m j : ℕ) : Summable (jumpMask m j) := by
  apply summable_of_ne_finset_zero (s := Finset.Ico (m*j) ((m+1)*j))
  intro k hk
  simp [jumpMask, hk]

private theorem jumpMask_tsum (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    (∑' k, jumpMask m j k) = jumpSq j / ((m:ℝ)*((m:ℝ)+1)*(j:ℝ)) := by
  rw [tsum_eq_sum (s := Finset.Ico (m*j) ((m+1)*j))
    (fun k hk => by simp [jumpMask, hk])]
  have he : (∑ k ∈ Finset.Ico (m*j) ((m+1)*j), jumpMask m j k) =
      (∑ k ∈ Finset.Ico (m*j) ((m+1)*j), positiveWeight k) * jumpSq j := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k hk => by simp [jumpMask, hk])
  rw [he, positiveWeight_interval _ _ (Nat.mul_pos hm hj)
    (Nat.mul_le_mul_right j (Nat.le_succ m))]
  push_cast
  field_simp
  <;> ring

private theorem tailWeight_summable (M : ℕ) :
    Summable (fun k => if M ≤ k then positiveWeight k else (0:ℝ)) := by
  have h := weighted_summable_of_bounded
    (f := fun k => if M ≤ k then (1:ℝ) else 0) (C := 1)
    (fun k => by split_ifs <;> norm_num)
  simpa only [mul_ite, mul_one, mul_zero] using h

private theorem tailWeight_tsum (M : ℕ) (hM : 0 < M) :
    (∑' k, if M ≤ k then positiveWeight k else (0:ℝ)) = 1/(M:ℝ) := by
  have hs : Summable (fun k => if k < M then positiveWeight k else (0:ℝ)) := by
    apply summable_of_ne_finset_zero (s := Finset.range M)
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [Nat.not_lt.mpr hk]
  have he : (fun k => (if k < M then positiveWeight k else (0:ℝ)) +
      (if M ≤ k then positiveWeight k else 0)) = positiveWeight := by
    funext k
    by_cases hk : k < M
    · simp [hk, Nat.not_le.mpr hk]
    · simp [hk, Nat.le_of_not_gt hk]
  have hsum := hs.tsum_add (tailWeight_summable M)
  rw [he, positiveWeight_tsum] at hsum
  have hh : (∑' k, if k < M then positiveWeight k else (0:ℝ)) = 1-1/(M:ℝ) := by
    rw [tsum_eq_sum (s := Finset.range M)
      (fun k hk => by simp only [Finset.mem_range] at hk; simp [hk])]
    have hprefix : (∑ k ∈ Finset.range M, if k < M then positiveWeight k else (0:ℝ)) =
        ∑ k ∈ Finset.range M, positiveWeight k :=
      Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))
    rw [hprefix, Finset.sum_range_eq_add_Ico positiveWeight hM,
      positiveWeight_interval 1 M (by omega) hM]
    norm_num [positiveWeight]
  rw [hh] at hsum
  linarith

private theorem waveletEnergyTerm_summable (m : ℕ) : Summable (waveletEnergyTerm m) := by
  apply weighted_summable_of_bounded (C := 4)
  intro k
  rw [abs_of_nonneg (sq_nonneg _)]
  exact binary_wavelet_difference_sq_le_four m (m+1) k

private theorem waveletTailTerm_summable (m : ℕ) : Summable (waveletTailTerm m) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((tailWeight_summable (m*(m+1))).mul_left 4)
  ·
    have hp := positiveWeight_nonneg k
    unfold waveletTailTerm waveletEnergyTerm
    split_ifs <;> positivity
  ·
    unfold waveletTailTerm waveletEnergyTerm
    split_ifs with hk
    · nlinarith [mul_le_mul_of_nonneg_left
        (binary_wavelet_difference_sq_le_four m (m+1) k) (positiveWeight_nonneg k)]
    · simp

private theorem pointwise_head_tail (m k : ℕ) (hm : 0 < m) :
    waveletEnergyTerm m k =
      (∑ j ∈ Finset.Icc 1 m, jumpMask m j k) + waveletTailTerm m k := by
  classical
  by_cases ht : m*(m+1) ≤ k
  · have hz : (∑ j ∈ Finset.Icc 1 m, jumpMask m j k) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjm := (Finset.mem_Icc.mp hj).2
      have hk : k ∉ Finset.Ico (m*j) ((m+1)*j) := by
        simp only [Finset.mem_Ico, not_and]
        intro _
        nlinarith
      simp [jumpMask, hk]
    simp [hz, waveletTailTerm, ht]
  · have htail : waveletTailTerm m k = 0 := by simp [waveletTailTerm, ht]
    rw [htail, add_zero]
    by_cases he : dilationWaveletSequence 2 m k = dilationWaveletSequence 2 (m+1) k
    · have hz : waveletEnergyTerm m k = 0 := by simp [waveletEnergyTerm, he]
      rw [hz]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hk : k ∈ Finset.Ico (m*j) ((m+1)*j)
      · have hv := interval_value m j k hm (Finset.mem_Icc.mp hj).1
          (Finset.mem_Icc.mp hj).2 hk
        simpa [jumpMask, hk, hz] using hv.symm
      · simp [jumpMask, hk]
    · obtain ⟨j, hj1, hjM, hlo, hhi⟩ := binaryWavelet_nearby_mismatch_support
        m (m+1) (m+1) k hm (by omega) (by omega) he
      have hjm : j ≤ m := by
        by_contra h
        have hj : j = m+1 := by omega
        subst j
        omega
      have hj : j ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨hj1, hjm⟩
      have hk : k ∈ Finset.Ico (m*j) ((m+1)*j) := Finset.mem_Ico.mpr ⟨hlo,hhi⟩
      rw [Finset.sum_eq_single j]
      · simpa [jumpMask, hk] using interval_value m j k hm hj1 hjm hk
      · intro i hi hij
        have hki : k ∉ Finset.Ico (m*i) ((m+1)*i) := by
          intro hki
          have hqi := (interval_quotients m i k hm (Finset.mem_Icc.mp hi).1
            (Finset.mem_Icc.mp hi).2 hki).1
          have hqj := (interval_quotients m j k hm hj1 hjm hk).1
          exact hij (hqi.symm.trans hqj)
        simp [jumpMask, hki]
      · exact fun h => (h hj).elim

private def jumpHarmonic (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, jumpSq (k+1) / ((k:ℝ)+1)

/-- Exact complete-energy decomposition: the nonnegative tail is retained. -/
theorem binary_wavelet_adjacent_exact_head_tail (m : ℕ) (hm : 0 < m) :
    (∑' k, waveletEnergyTerm m k) =
      jumpHarmonic m / ((m:ℝ)*((m:ℝ)+1)) + ∑' k, waveletTailTerm m k := by
  have hhead : Summable (fun k => ∑ j ∈ Finset.Icc 1 m, jumpMask m j k) :=
    summable_sum (fun j _ => jumpMask_summable m j)
  calc
    _ = (∑' k, ((∑ j ∈ Finset.Icc 1 m, jumpMask m j k) + waveletTailTerm m k)) := by
      congr 1
      funext k
      exact pointwise_head_tail m k hm
    _ = (∑ j ∈ Finset.Icc 1 m, jumpSq j / ((m:ℝ)*((m:ℝ)+1)*(j:ℝ))) +
        ∑' k, waveletTailTerm m k := by
      rw [hhead.tsum_add (waveletTailTerm_summable m),
        Summable.tsum_finsetSum (fun j hj => jumpMask_summable m j)]
      congr 1
      exact Finset.sum_congr rfl (fun j hj => jumpMask_tsum m j hm
        (Finset.mem_Icc.mp hj).1)
    _ = _ := by
      congr 1
      rw [show Finset.Icc 1 m = Finset.Ico 1 (m+1) by ext j; simp,
        Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_right]
      unfold jumpHarmonic
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Nat.add_comm 1]
      push_cast
      field_simp
      <;> ring

theorem binary_wavelet_adjacent_tail_bounds (m : ℕ) (hm : 0 < m) :
    0 ≤ ∑' k, waveletTailTerm m k ∧
      (∑' k, waveletTailTerm m k) ≤ 4/((m:ℝ)*((m:ℝ)+1)) := by
  constructor
  · apply tsum_nonneg
    intro k
    have hp := positiveWeight_nonneg k
    unfold waveletTailTerm waveletEnergyTerm
    split_ifs <;> positivity
  · calc
      _ ≤ ∑' k, 4 * (if m*(m+1) ≤ k then positiveWeight k else (0:ℝ)) := by
        apply (waveletTailTerm_summable m).tsum_le_tsum _
          ((tailWeight_summable (m*(m+1))).mul_left 4)
        intro k
        unfold waveletTailTerm waveletEnergyTerm
        split_ifs
        · nlinarith [mul_le_mul_of_nonneg_left
            (binary_wavelet_difference_sq_le_four m (m+1) k) (positiveWeight_nonneg k)]
        · simp
      _ = _ := by
        rw [tsum_mul_left, tailWeight_tsum _ (by positivity)]
        push_cast
        ring

private theorem jumpHarmonic_log_bound (m : ℕ) (hm : 0 < m) :
    |jumpHarmonic m - (3/2:ℝ)*Real.log m| ≤ 46 := by
  have hper : ∀ k, jumpSq (k+4+1) = jumpSq (k+1) := by
    intro k
    simp [jumpSq, binaryWaveletJump, Nat.add_mod]
  have hmean : RiemannResearch.Analysis.periodicMean (fun k => jumpSq (k+1)) 4 =
      (3/2:ℝ) := by
    norm_num [RiemannResearch.Analysis.periodicMean, Finset.sum_range_succ,
      jumpSq, binaryWaveletJump]
  have hb := RiemannResearch.Analysis.periodic_harmonic_mean_error_bound
    (fun k => jumpSq (k+1)) 4 (by omega) hper 4
    (fun k => by rw [abs_of_nonneg (jumpSq_bounds _).1]; exact (jumpSq_bounds _).2) m
  rw [hmean] at hb
  norm_num at hb
  have hlo := log_add_one_le_harmonic m
  push_cast at hlo
  have hhi := harmonic_le_one_add_log m
  have hl : Real.log (m:ℝ) ≤ Real.log ((m:ℝ)+1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hh : |(harmonic m:ℝ) - Real.log m| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have ht := abs_add_le (jumpHarmonic m - (3/2:ℝ)*(harmonic m:ℝ))
    ((3/2:ℝ)*((harmonic m:ℝ)-Real.log m))
  have he : jumpHarmonic m - (3/2:ℝ)*Real.log m =
      (jumpHarmonic m - (3/2:ℝ)*(harmonic m:ℝ)) +
        (3/2:ℝ)*((harmonic m:ℝ)-Real.log m) := by ring
  rw [he]
  apply ht.trans
  rw [abs_mul]
  norm_num
  change |jumpHarmonic m - (3/2:ℝ)*(harmonic m:ℝ)| ≤ 44 at hb
  nlinarith

private theorem hilbert_adjacent_energy (m : ℕ) (hm : 0 < m) :
    ‖dilationWaveletHilbert 2 m (by omega) hm -
      dilationWaveletHilbert 2 (m+1) (by omega) (by omega)‖^2 =
      ∑' k, waveletEnergyTerm m k := by
  rw [hilbert_norm_weighted_sq]
  have he : hilbertSequence
      (dilationWaveletHilbert 2 m (by omega) hm -
        dilationWaveletHilbert 2 (m+1) (by omega) (by omega)) =
      dilationWaveletSequence 2 m - dilationWaveletSequence 2 (m+1) := by
    change hilbertSequenceLinear (_-_) = _
    rw [map_sub]
    change hilbertSequence _ - hilbertSequence _ = _
    rw [hilbertSequence_dilationWaveletHilbert, hilbertSequence_dilationWaveletHilbert]
  rw [he]
  rfl

private theorem normalized_energy_comparison {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x y : E) (hx : x ≠ 0) (hy : y ≠ 0)
    (hm : ℝ) (hmpos : 0 < hm)
    (hratio : (‖y‖/‖x‖)^2 = hm/(hm+1)) :
    |‖NormedSpace.normalize x - NormedSpace.normalize y‖^2 -
      ‖x-y‖^2/‖x‖^2| ≤ 4/hm := by
  let a := ‖x‖
  let b := ‖y‖
  let U := NormedSpace.normalize x - NormedSpace.normalize y
  let q := b/a
  let d := ‖x-y‖/a
  have ha : 0 < a := norm_pos_iff.mpr hx
  have hb : 0 < b := norm_pos_iff.mpr hy
  have hq0 : 0 ≤ q := (div_pos hb ha).le
  have hq2 : q^2 = hm/(hm+1) := hratio
  have hfrac : 0 ≤ hm/(hm+1) ∧ hm/(hm+1) ≤ 1 :=
    ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩
  have hq1 : q ≤ 1 := by nlinarith
  have hab : b ≤ a := (div_le_one ha).mp hq1
  have hgap : 1-q ≤ 1/hm := by
    have hsmall : 1-q ≤ 1-q^2 := by
      nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
    have hid : 1-q^2 = 1/(hm+1) := by rw [hq2]; field_simp <;> ring
    rw [hid] at hsmall
    exact hsmall.trans (one_div_le_one_div_of_le hmpos (by linarith))
  have hU : ‖U‖ ≤ 2 := by
    have h := norm_sub_le (NormedSpace.normalize x) (NormedSpace.normalize y)
    simpa [U, NormedSpace.norm_normalize hx, NormedSpace.norm_normalize hy, one_add_one_eq_two] using! h
  have hd0 : 0 ≤ d := div_nonneg (norm_nonneg _) ha.le
  have hd2 : d ≤ 2 := by
    have hd : ‖x-y‖ ≤ a+b := norm_sub_le x y
    apply (div_le_iff₀ ha).mpr
    linarith
  have hidentity : a • U - (x-y) = (b-a) • NormedSpace.normalize y := by
    dsimp [a,b,U]
    rw [RiemannResearch.Analysis.NormalizedPairObstruction.normalize_difference_identity]
    abel
  have hrev := abs_norm_sub_norm_le (a • U) (x-y)
  rw [hidentity, norm_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos ha, Real.norm_eq_abs, NormedSpace.norm_normalize hy,
    mul_one, abs_of_nonpos (sub_nonpos.mpr hab)] at hrev
  have hdiff : |‖U‖-d| ≤ 1-q := by
    have he : ‖U‖-d = (a*‖U‖-‖x-y‖)/a := by dsimp [d]; field_simp <;> ring
    rw [he, abs_div, abs_of_pos ha]
    apply (div_le_iff₀ ha).mpr
    have heq : (1-q)*a = a-b := by dsimp [q]; field_simp <;> ring
    rw [heq]
    linarith
  have hsq : |‖U‖^2-d^2| ≤ 4*(1-q) := by
    rw [show ‖U‖^2-d^2 = (‖U‖-d)*(‖U‖+d) by ring,
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖U‖+d)]
    calc
      _ ≤ (1-q)*(‖U‖+d) := mul_le_mul_of_nonneg_right hdiff (by positivity)
      _ ≤ 4*(1-q) := by
        have hh := mul_le_mul_of_nonneg_left (show ‖U‖+d ≤ 4 by linarith)
          (show 0 ≤ 1-q by linarith)
        nlinarith
  have hfin := hsq.trans (mul_le_mul_of_nonneg_left hgap (by norm_num))
  simpa only [U,d,a,div_pow,mul_one_div] using hfin

private theorem normalized_wavelet_energy_comparison (m : ℕ) (hm : 0 < m) :
    |‖normalizedBinaryWavelet m hm -
        normalizedBinaryWavelet (m+1) (by omega)‖^2 -
      (4*(m:ℝ)/Real.pi) * (∑' k, waveletEnergyTerm m k)| ≤ 4/(m:ℝ) := by
  let x := dilationWaveletHilbert 2 m (by omega) hm
  let y := dilationWaveletHilbert 2 (m+1) (by omega) (by omega)
  have hx : x ≠ 0 := binary_wavelet_hilbert_ne_zero m hm
  have hy : y ≠ 0 := binary_wavelet_hilbert_ne_zero (m+1) (by omega)
  have ha : ‖x‖^2 = Real.pi/(4*(m:ℝ)) := binary_wavelet_hilbert_norm_sq m hm
  have hb : ‖y‖^2 = Real.pi/(4*((m:ℝ)+1)) := by
    simpa using binary_wavelet_hilbert_norm_sq (m+1) (by omega)
  have hr : (‖y‖/‖x‖)^2 = (m:ℝ)/((m:ℝ)+1) := by
    rw [div_pow, ha, hb]
    field_simp
    <;> ring
  have h := normalized_energy_comparison x y hx hy (m:ℝ) (by positivity) hr
  rw [ha] at h
  have he : ‖x-y‖^2 = ∑' k, waveletEnergyTerm m k := hilbert_adjacent_energy m hm
  rw [he] at h
  have halg : (∑' k, waveletEnergyTerm m k) / (Real.pi/(4*(m:ℝ))) =
      (4*(m:ℝ)/Real.pi)*(∑' k, waveletEnergyTerm m k) := by
    field_simp
    <;> ring
  rw [halg] at h
  exact h

private theorem scaled_wavelet_energy_log_bound (m : ℕ) (hm : 0 < m) :
    |(4*(m:ℝ)/Real.pi)*(∑' k, waveletEnergyTerm m k) -
      (6/Real.pi)*Real.log m/(m:ℝ)| ≤ (206/Real.pi)/(m:ℝ) := by
  let M : ℝ := m
  let S := jumpHarmonic m
  let T := ∑' k, waveletTailTerm m k
  have hM : 0 < M := by dsimp [M]; positivity
  have hpi := Real.pi_pos
  have hT := binary_wavelet_adjacent_tail_bounds m hm
  have hS := jumpHarmonic_log_bound m hm
  have hlog : 0 ≤ Real.log M := Real.log_nonneg
    (by dsimp [M]; exact_mod_cast (show 1 ≤ m by omega))
  have hlogle : Real.log M ≤ M := by
    have h := Real.log_le_sub_one_of_pos hM
    linarith
  have hid : (4*M/Real.pi)*(∑' k, waveletEnergyTerm m k) -
      (6/Real.pi)*Real.log M/M =
      (4/Real.pi)*(S-(3/2:ℝ)*Real.log M)/(M+1) +
        (4*M/Real.pi)*T - (6/Real.pi)*Real.log M/(M*(M+1)) := by
    rw [binary_wavelet_adjacent_exact_head_tail m hm]
    dsimp [M,S,T]
    field_simp
    <;> ring
  have hfirst : |(4/Real.pi)*(S-(3/2:ℝ)*Real.log M)/(M+1)| ≤
      (184/Real.pi)/M := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 4/Real.pi),
      abs_of_pos (by positivity : 0 < M+1)]
    calc
      _ ≤ (4/Real.pi)*46/(M+1) := by
        gcongr
      _ ≤ (184/Real.pi)/M := by
        have hd := one_div_le_one_div_of_le hM (show M ≤ M+1 by linarith)
        have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 184/Real.pi by positivity)
        convert! hh using 1 <;> ring
  have hsecond : |(4*M/Real.pi)*T| ≤ (16/Real.pi)/M := by
    rw [abs_of_nonneg (mul_nonneg (by positivity) hT.1)]
    calc
      _ ≤ (4*M/Real.pi)*(4/(M*(M+1))) := by
        apply mul_le_mul_of_nonneg_left hT.2 (by positivity)
      _ = (16/Real.pi)/(M+1) := by field_simp <;> ring
      _ ≤ (16/Real.pi)/M := by gcongr <;> linarith
  have hthird : |(6/Real.pi)*Real.log M/(M*(M+1))| ≤ (6/Real.pi)/M := by
    rw [abs_of_nonneg (by positivity : 0 ≤ (6/Real.pi)*Real.log M/(M*(M+1)))]
    calc
      _ ≤ (6/Real.pi)*M/(M*(M+1)) := by
        gcongr
      _ = (6/Real.pi)/(M+1) := by field_simp <;> ring
      _ ≤ (6/Real.pi)/M := by gcongr <;> linarith
  change |(4*M/Real.pi)*(∑' k, waveletEnergyTerm m k) -
    (6/Real.pi)*Real.log M/M| ≤ (206/Real.pi)/M
  rw [hid]
  have ht := abs_sub_le
    ((4/Real.pi)*(S-(3/2:ℝ)*Real.log M)/(M+1) + (4*M/Real.pi)*T) 0
    ((6/Real.pi)*Real.log M/(M*(M+1)))
  simp only [sub_zero, zero_sub, abs_neg] at ht
  have ha := abs_add_le ((4/Real.pi)*(S-(3/2:ℝ)*Real.log M)/(M+1))
    ((4*M/Real.pi)*T)
  have hc : (184/Real.pi)/M+(16/Real.pi)/M+(6/Real.pi)/M = (206/Real.pi)/M := by ring
  nlinarith

/-- The exact stronger target, with the 6/pi leading coefficient. -/
theorem binaryWaveletAdjacentAsymptotic_proved : BinaryWaveletAdjacentAsymptoticTarget := by
  apply Asymptotics.IsBigO.of_bound (4+206/Real.pi)
  apply Filter.Eventually.of_forall
  intro n
  have hn : 0 < n+1 := by omega
  have h1 := normalized_wavelet_energy_comparison (n+1) hn
  have h2 := scaled_wavelet_energy_log_bound (n+1) hn
  have htri := abs_add_le
    (‖normalizedBinaryWavelet (n+1) hn - normalizedBinaryWavelet (n+1+1) (by omega)‖^2 -
      (4*((n+1:ℕ):ℝ)/Real.pi)*(∑' k, waveletEnergyTerm (n+1) k))
    ((4*((n+1:ℕ):ℝ)/Real.pi)*(∑' k, waveletEnergyTerm (n+1) k) -
      (6/Real.pi)*Real.log ((n+1:ℕ):ℝ)/((n+1:ℕ):ℝ))
  have he : (4+206/Real.pi)*(1/((n+1:ℕ):ℝ)) =
      4/((n+1:ℕ):ℝ)+(206/Real.pi)/((n+1:ℕ):ℝ) := by ring
  simp only [sub_add_sub_cancel] at htri
  simp only [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1/((n:ℝ)+1))]
  push_cast at h1 h2 htri he
  simp only [Nat.add_assoc] at htri h1
  linarith

end
end RiemannResearch.RH.Pareto
