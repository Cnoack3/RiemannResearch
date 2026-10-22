import RiemannResearch.RH.DilationWaveletAlgebra
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Exact logarithmic means of every integer residue seed

Source: user-provided argument in the contracting evolution research note.
The proof evaluates the actual full Pareto sum. Its finite identity is
H_(aN)-H_N; the only external analytic input is Mathlib's unconditional
convergence of harmonic n - log n to Euler's constant.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Exact discrete integration by parts, including the endpoint term. -/
theorem pareto_partial_abel (f : ℕ → ℝ) (hf0 : f 0 = 0) (K : ℕ) :
    (∑ k ∈ Finset.range (K+1), positiveWeight k * f k) =
      (∑ k ∈ Finset.range K, (f (k+1)-f k) / ((k : ℝ)+1)) -
        f K / ((K : ℝ)+1) := by
  induction K with
  | zero => simp [hf0, positiveWeight]
  | succ K ih =>
    have hj : (∑ k ∈ Finset.range (K+1), (f (k+1)-f k) / ((k : ℝ)+1)) =
        (∑ k ∈ Finset.range K, (f (k+1)-f k) / ((k : ℝ)+1)) +
          (f (K+1)-f K) / ((K : ℝ)+1) := Finset.sum_range_succ _ K
    rw [Finset.sum_range_succ, ih, hj]
    unfold positiveWeight
    push_cast
    have h1 : (K : ℝ)+1 ≠ 0 := by positivity
    have h2 : (K : ℝ)+1+1 ≠ 0 := by positivity
    field_simp
    ring

private theorem real_harmonic_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ k ∈ Finset.range N, 1 / ((k : ℝ)+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [harmonic_succ, Finset.sum_range_succ]
    push_cast
    rw [ih]
    simp only [one_div]

private theorem multiple_reciprocal_sum (a N : ℕ) (ha : 0 < a) :
    (∑ k ∈ Finset.range (a*N), if a ∣ k+1 then (a : ℝ) / ((k : ℝ)+1) else 0) =
      (harmonic N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, harmonic_succ]
    push_cast
    congr 1
    have hmemb : a-1 ∈ Finset.range a := Finset.mem_range.2 (by omega)
    rw [Finset.sum_eq_single (a-1)]
    · have he : a*N+(a-1)+1 = a*(N+1) := by rw [Nat.mul_succ]; omega
      have hd : a ∣ a*N+(a-1)+1 := by rw [he]; exact dvd_mul_right a (N+1)
      rw [if_pos hd]
      have her : (a*N+(a-1) : ℕ) + 1 = a*(N+1) := he
      have heR : ((a*N+(a-1) : ℕ) : ℝ)+1 = (a : ℝ)*((N : ℝ)+1) := by
        exact_mod_cast her
      push_cast at heR
      rw [heR]
      have ha0 : (a : ℝ) ≠ 0 := by positivity
      have hN0 : (N : ℝ)+1 ≠ 0 := by positivity
      field_simp
    · intro j hj hjne
      have hjlt : j < a := Finset.mem_range.1 hj
      have hnd : ¬ a ∣ a*N+j+1 := by
        intro hd
        have hdmod := Nat.mod_eq_zero_of_dvd hd
        have hemod : (a*N+j+1)%a = (j+1)%a := by
          simp [Nat.add_assoc, Nat.add_mod]
        rw [hemod] at hdmod
        have hjp : j+1 < a := by omega
        rw [Nat.mod_eq_of_lt hjp] at hdmod
        omega
      simp only [hnd, if_false]
    · intro hnot
      exact (hnot hmemb).elim

/-- Exact finite identity at every full residue period. -/
theorem residue_pareto_partial_harmonic (a N : ℕ) (ha : 0 < a) :
    (∑ k ∈ Finset.range (a*N), positiveWeight k * residue a k) =
      (harmonic (a*N) : ℝ) - (harmonic N : ℝ) := by
  have h := pareto_partial_abel (residue a) (by simp [residue]) (a*N)
  have he : residue a (a*N) = 0 := by simp [residue]
  rw [Finset.sum_range_succ, he] at h
  simp only [mul_zero, add_zero, zero_div, sub_zero] at h
  rw [h]
  calc
    _ = ∑ k ∈ Finset.range (a*N),
        (1 / ((k : ℝ)+1) - if a ∣ k+1 then (a : ℝ) / ((k : ℝ)+1) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hd := residue_difference a (k+1) (by omega)
      simp only [Nat.add_sub_cancel] at hd
      rw [hd]
      split_ifs <;> ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← real_harmonic_sum,
        multiple_reciprocal_sum a N ha]

private theorem harmonic_multiple_difference_tendsto (a : ℕ) (ha : 0 < a) :
    Filter.Tendsto (fun N : ℕ => (harmonic (a*N) : ℝ) - harmonic N)
      Filter.atTop (nhds (Real.log a)) := by
  have hN : Filter.Tendsto (fun N : ℕ => a*N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N ha) Filter.tendsto_id
  have hs := (Real.tendsto_harmonic_sub_log.comp hN).sub
    Real.tendsto_harmonic_sub_log
  have hs' := hs.add_const (Real.log a)
  simp only [sub_self, zero_add] at hs'
  apply hs'.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with N hpos
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_def, Nat.cast_mul, Real.log_mul ha0 hN0]
  ring

/-- The mean of every positive integer residue seed is exactly log a. -/
theorem paretoMean_residue (a : ℕ) (ha : 0 < a) :
    paretoMean (residue a) = Real.log a := by
  have hb : ∀ k, |residue a k| ≤ (a : ℝ) := by
    intro k
    unfold residue
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.le_of_lt (Nat.mod_lt k ha))
  have hs := (weighted_summable_of_bounded hb).hasSum.tendsto_sum_nat
  have hN : Filter.Tendsto (fun N : ℕ => a*N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N ha) Filter.tendsto_id
  have h := hs.comp hN
  simp only [Function.comp_def, residue_pareto_partial_harmonic a _ ha] at h
  exact tendsto_nhds_unique h (harmonic_multiple_difference_tendsto a ha)

theorem paretoMean_digitSequence (a m : ℕ) (ha : 0 < a) (hm : 0 < m) :
    paretoMean (digitSequence a m) = Real.log a / (m : ℝ) := by
  have hb : ∀ k, |residue a k| ≤ (a : ℝ) := by
    intro k
    unfold residue
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.le_of_lt (Nat.mod_lt k ha))
  change paretoMean (rawPullback m (residue a)) = _
  rw [paretoMean_rawPullback hb m hm, paretoMean_residue a ha]
  simp [residue]

/-- Zero period mean and nonzero Pareto mean are different notions. -/
theorem paretoMean_dilationWaveletSequence (a m : ℕ) (ha : 0 < a) (hm : 0 < m) :
    paretoMean (dilationWaveletSequence a m) =
      (1 - 1 / (a : ℝ)) * Real.log a / (m : ℝ) := by
  have hs1 := weighted_summable_of_bounded (digitSequence_abs_le a m ha)
  have hs2 := weighted_summable_of_bounded (digitSequence_abs_le a (a*m) ha)
  unfold paretoMean dilationWaveletSequence
  simp only [Pi.sub_apply, mul_sub]
  rw [hs1.tsum_sub hs2]
  change paretoMean (digitSequence a m) - paretoMean (digitSequence a (a*m)) = _
  rw [paretoMean_digitSequence a m ha hm,
    paretoMean_digitSequence a (a*m) ha (Nat.mul_pos ha hm)]
  push_cast
  have ha0 : (a : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp

/-- The binary digit is idempotent, so its norm is its exact logarithmic mean. -/
theorem digitHilbert_two_norm_sq (m : ℕ) (hm : 0 < m) :
    ‖digitHilbert 2 m (by norm_num) hm‖^2 = Real.log 2 / (m : ℝ) := by
  rw [hilbert_norm_weighted_sq, hilbertSequence_digitHilbert]
  have hid (k : ℕ) : digitSequence 2 m k ^ 2 = digitSequence 2 m k := by
    have hk : k/m%2 = 0 ∨ k/m%2 = 1 := by omega
    rcases hk with hk | hk <;> simp [digitSequence, hk]
  simp_rw [hid]
  exact paretoMean_digitSequence 2 m (by norm_num) hm

/-- Closed-form binary remainder for every truncation, including N=0. -/
theorem binary_wavelet_error_sq_log (m N : ℕ) (hm : 0 < m) :
    ‖digitHilbert 2 m (by norm_num) hm -
      (∑ j ∈ Finset.range N, dilationWaveletHilbert 2 (2^j*m) (by norm_num)
        (Nat.mul_pos (pow_pos (by norm_num) j) hm))‖^2 =
      Real.log 2 / ((m : ℝ)*2^N) := by
  rw [digitHilbert_wavelet_error_sq 2 m N (by norm_num) hm,
    digitHilbert_two_norm_sq m hm]
  rw [one_div_pow]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hp0 : (2 : ℝ)^N ≠ 0 := by positivity
  field_simp
  ring

end
end RiemannResearch.RH.Pareto
