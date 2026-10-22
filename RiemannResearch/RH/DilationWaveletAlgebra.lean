import RiemannResearch.RH.ThresholdHilbertDilation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Legal dilation wavelets and their exact Hilbert tails

Source: user-provided argument `analytic_wavelet_foothold.md`, §§1–2.
These are the actual integer residue generators in the complete Pareto
Hilbert space. Every positive integer dilation is retained. No RH hypothesis
or arithmetic repair estimate is used.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def digitSequence (a m k : ℕ) : ℝ := ((k / m) % a : ℕ)

def dilationWaveletSequence (a m : ℕ) : ℕ → ℝ :=
  digitSequence a m - digitSequence a (a*m)

@[simp] theorem digitSequence_zero (a m : ℕ) : digitSequence a m 0 = 0 := by
  simp [digitSequence]

theorem digitSequence_abs_le (a m : ℕ) (ha : 0 < a) (k : ℕ) :
    |digitSequence a m k| ≤ a := by
  unfold digitSequence
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Nat.le_of_lt (Nat.mod_lt (k / m) ha))

theorem digitSequence_square_summable (a m : ℕ) (ha : 0 < a) :
    Summable (fun k => positiveWeight k * digitSequence a m k ^ 2) := by
  simpa only [pow_two] using weighted_summable_of_bounded
    (bounded_product (digitSequence_abs_le a m ha) (digitSequence_abs_le a m ha))

/-- Actual weighted Hilbert vector, with summability discharged. -/
def digitHilbert (a m : ℕ) (ha : 0 < a) (_hm : 0 < m) : ThresholdHilbert :=
  sequenceHilbert (digitSequence a m) (digitSequence_square_summable a m ha)

@[simp] theorem hilbertSequence_digitHilbert (a m : ℕ) (ha : 0 < a) (hm : 0 < m) :
    hilbertSequence (digitHilbert a m ha hm) = digitSequence a m :=
  hilbertSequence_sequenceHilbert _ _ (digitSequence_zero a m)

def dilationWaveletHilbert (a m : ℕ) (ha : 0 < a) (hm : 0 < m) : ThresholdHilbert :=
  digitHilbert a m ha hm - digitHilbert a (a*m) ha (Nat.mul_pos ha hm)

@[simp] theorem hilbertSequence_dilationWaveletHilbert (a m : ℕ)
    (ha : 0 < a) (hm : 0 < m) :
    hilbertSequence (dilationWaveletHilbert a m ha hm) = dilationWaveletSequence a m := by
  change hilbertSequenceLinear (_ - _) = _
  rw [map_sub]
  change hilbertSequence (digitHilbert a m ha hm) -
    hilbertSequence (digitHilbert a (a*m) ha (Nat.mul_pos ha hm)) = _
  rw [hilbertSequence_digitHilbert, hilbertSequence_digitHilbert]
  rfl

/-- Exact identity with the original integer residue generator. -/
theorem digitSequence_generator (a m k : ℕ) :
    (m : ℝ) * digitSequence a m k = residue (a*m) k - residue m k := by
  simpa only [dilation, residue, digitSequence, Nat.mul_comm m a] using
    residue_mul_floor m a k

theorem digitSequence_eq_scaled_generator (a m : ℕ) (hm : 0 < m) :
    digitSequence a m = (1 / (m : ℝ)) • dilation m (residue a) := by
  funext k
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  simp only [Pi.smul_apply, smul_eq_mul, dilation, residue, digitSequence]
  field_simp

theorem dilationWaveletSequence_generator (a m : ℕ) (ha : 0 < a) (hm : 0 < m) :
    dilationWaveletSequence a m =
      (1 / (m : ℝ)) • dilation m (residue a) -
      (1 / ((a*m : ℕ) : ℝ)) • dilation (a*m) (residue a) := by
  unfold dilationWaveletSequence
  rw [digitSequence_eq_scaled_generator a m hm,
    digitSequence_eq_scaled_generator a (a*m) (Nat.mul_pos ha hm)]

theorem digitSequence_periodic (a m : ℕ) (hm : 0 < m) (k : ℕ) :
    digitSequence a m (k + a*m) = digitSequence a m k := by
  simp [digitSequence, Nat.add_mul_div_right _ _ hm]

theorem dilationWaveletSequence_periodic (a m : ℕ) (ha : 0 < a)
    (hm : 0 < m) (k : ℕ) :
    dilationWaveletSequence a m (k+a*a*m) = dilationWaveletSequence a m k := by
  have h1 : digitSequence a m (k+a*a*m) = digitSequence a m k := by
    simp [digitSequence, Nat.add_mul_div_right _ _ hm, Nat.add_mod]
  have h2 : digitSequence a (a*m) (k+a*a*m) = digitSequence a (a*m) k := by
    rw [show a*a*m = a*(a*m) by ring]
    exact digitSequence_periodic a (a*m) (Nat.mul_pos ha hm) k
  simp only [dilationWaveletSequence, Pi.sub_apply, h1, h2]

private theorem residue_sum_periods (a N : ℕ) :
    (∑ k ∈ Finset.range (a*N), ((k % a : ℕ) : ℝ)) =
      (N : ℝ) * ∑ k ∈ Finset.range a, ((k % a : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have hs : (∑ k ∈ Finset.range a, (((a*N+k) % a : ℕ) : ℝ)) =
        ∑ k ∈ Finset.range a, ((k % a : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [Nat.add_mod]
    rw [hs]
    push_cast
    ring

theorem digitSequence_sum_blocks (a m N : ℕ) (hm : 0 < m) :
    (∑ k ∈ Finset.range (m*N), digitSequence a m k) =
      (m : ℝ) * ∑ j ∈ Finset.range N, ((j % a : ℕ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    have hs : (∑ k ∈ Finset.range m, digitSequence a m (m*N+k)) =
        (m : ℝ) * ((N % a : ℕ) : ℝ) := by
      calc
        _ = ∑ k ∈ Finset.range m, ((N % a : ℕ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk' : k < m := Finset.mem_range.mp hk
          simp [digitSequence, Nat.add_comm (m*N) k,
            Nat.add_mul_div_left k N hm, Nat.div_eq_of_lt hk']
        _ = _ := by simp
    rw [hs]
    ring

/-- Zero average over a full common period. This is not a weighted-mean claim. -/
theorem dilationWaveletSequence_period_sum_zero (a m : ℕ)
    (ha : 0 < a) (hm : 0 < m) :
    (∑ k ∈ Finset.range (a*a*m), dilationWaveletSequence a m k) = 0 := by
  simp only [dilationWaveletSequence, Pi.sub_apply, Finset.sum_sub_distrib]
  have h1 : (∑ k ∈ Finset.range (a*a*m), digitSequence a m k) =
      (m : ℝ) * ((a : ℝ) * ∑ k ∈ Finset.range a, ((k % a : ℕ) : ℝ)) := by
    rw [show a*a*m = m*(a*a) by ring, digitSequence_sum_blocks a m (a*a) hm,
      residue_sum_periods a a]
  have h2 : (∑ k ∈ Finset.range (a*a*m), digitSequence a (a*m) k) =
      ((a*m : ℕ) : ℝ) * ∑ k ∈ Finset.range a, ((k % a : ℕ) : ℝ) := by
    rw [show a*a*m = (a*m)*a by ring,
      digitSequence_sum_blocks a (a*m) a (Nat.mul_pos ha hm)]
  rw [h1, h2]
  push_cast
  ring

theorem digitHilbert_dilation (a m p : ℕ) (ha : 0 < a)
    (hm : 0 < m) (hp : 0 < p) :
    digitHilbert a (p*m) ha (Nat.mul_pos hp hm) =
      (1 / (p : ℝ)) • hilbertDilation p hp (digitHilbert a m ha hm) := by
  apply hilbertSequence_injective
  simp only [hilbertSequence_smul, hilbertDilation_sequence, hilbertSequence_digitHilbert]
  funext k
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  simp only [digitSequence, Pi.smul_apply, smul_eq_mul, dilation,
    Nat.div_div_eq_div_mul]
  field_simp

/-- Exact norm scaling in the genuine Hilbert space, for every integer dilation. -/
theorem digitHilbert_norm_sq_scale (a m p : ℕ) (ha : 0 < a)
    (hm : 0 < m) (hp : 0 < p) :
    ‖digitHilbert a (p*m) ha (Nat.mul_pos hp hm)‖^2 =
      ‖digitHilbert a m ha hm‖^2 / (p : ℝ) := by
  rw [digitHilbert_dilation a m p ha hm hp, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, hilbertDilation_norm_sq]
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  field_simp

theorem dilationWaveletHilbert_dilation (a m : ℕ) (ha : 0 < a) (hm : 0 < m) :
    dilationWaveletHilbert a m ha hm =
      (1 / (m : ℝ)) • hilbertDilation m hm
        (dilationWaveletHilbert a 1 ha Nat.zero_lt_one) := by
  have hleft := digitHilbert_dilation a 1 m ha Nat.zero_lt_one hm
  have hright := digitHilbert_dilation a a m ha ha hm
  simp only [Nat.mul_one] at hleft
  unfold dilationWaveletHilbert
  rw [hleft]
  have hr : digitHilbert a (a*m) ha (Nat.mul_pos ha hm) =
      (1 / (m : ℝ)) • hilbertDilation m hm (digitHilbert a (a*1) ha
        (Nat.mul_pos ha Nat.zero_lt_one)) := by
    simpa only [Nat.mul_comm m a, Nat.mul_one] using hright
  rw [hr, ← smul_sub]
  congr 1
  exact (hilbertDilationLinear m hm).map_sub _ _ |>.symm

theorem dilationWaveletHilbert_norm_sq (a m : ℕ) (ha : 0 < a) (hm : 0 < m) :
    ‖dilationWaveletHilbert a m ha hm‖^2 =
      ‖dilationWaveletHilbert a 1 ha Nat.zero_lt_one‖^2 / (m : ℝ) := by
  rw [dilationWaveletHilbert_dilation, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs, hilbertDilation_norm_sq]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp

/-- Exact finite expansion with its full Hilbert-valued remainder. -/
theorem digitHilbert_wavelet_telescope (a m N : ℕ) (ha : 0 < a) (hm : 0 < m) :
    (∑ j ∈ Finset.range N, dilationWaveletHilbert a (a^j*m) ha
      (Nat.mul_pos (pow_pos ha j) hm)) =
      digitHilbert a m ha hm -
        digitHilbert a (a^N*m) ha (Nat.mul_pos (pow_pos ha N) hm) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    unfold dilationWaveletHilbert
    have he : a * (a^N*m) = a^(N+1)*m := by rw [pow_succ]; ring
    simp only [he]
    abel

/-- Exact squared remainder, with no tail terms omitted. -/
theorem digitHilbert_wavelet_error_sq (a m N : ℕ) (ha : 0 < a) (hm : 0 < m) :
    ‖digitHilbert a m ha hm -
      (∑ j ∈ Finset.range N, dilationWaveletHilbert a (a^j*m) ha
        (Nat.mul_pos (pow_pos ha j) hm))‖^2 =
      ((1 / (a : ℝ))^N) * ‖digitHilbert a m ha hm‖^2 := by
  rw [digitHilbert_wavelet_telescope a m N ha hm]
  have he : digitHilbert a m ha hm -
      (digitHilbert a m ha hm -
        digitHilbert a (a^N*m) ha (Nat.mul_pos (pow_pos ha N) hm)) =
      digitHilbert a (a^N*m) ha (Nat.mul_pos (pow_pos ha N) hm) := by abel
  rw [he, digitHilbert_norm_sq_scale a m (a^N) ha hm (pow_pos ha N)]
  push_cast
  rw [one_div_pow]
  ring

theorem hilbertDilation_digit_one_sequence (a m : ℕ) (ha : 0 < a) (hm : 0 < m) :
    hilbertSequence (hilbertDilation m hm (digitHilbert a 1 ha (by omega))) =
      dilation m (residue a) := by
  rw [hilbertDilation_sequence, hilbertSequence_digitHilbert]
  funext k
  simp [digitSequence, residue, dilation]

end
end RiemannResearch.RH.Pareto
