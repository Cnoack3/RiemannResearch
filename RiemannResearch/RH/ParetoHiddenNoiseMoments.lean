import RiemannResearch.RH.ParetoHiddenNoise
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Ring

/-!
# Complete first- and second-moment bounds for the hidden-noise family

Source: RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf, §6.
The finite mismatch contribution, the remaining head, and the full infinite tail are
retained in an exact decomposition before any estimates are made.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- A sharper global amplitude bound than the triangle inequality for the two dilations. -/
theorem hiddenNoise_abs_le_add_two (n k : ℕ) :
    |hiddenNoise n k| ≤ (n : ℝ) + 2 := by
  have hw (a : ℕ) : 0 ≤ squareWave a k ∧ squareWave a k ≤ 1 := by
    constructor
    · unfold squareWave; positivity
    · unfold squareWave
      exact_mod_cast (show (k / a) % 2 ≤ 1 by omega)
  rw [hiddenNoise_squareWave]
  apply abs_le.mpr
  have ha := hw (n + 2)
  have hb := hw n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor <;> nlinarith

/-- After both jumps in a block the value is precisely zero or two. -/
theorem hiddenNoise_regular_value (n j k : ℕ)
    (hklo : j * (n + 2) ≤ k) (hkhi : k < (j + 1) * n) :
    hiddenNoise n k = 2 * (j % 2 : ℕ) := by
  have hl : k / n = j := by
    apply Nat.div_eq_of_lt_le
    · nlinarith
    · exact hkhi
  have hr : k / (n + 2) = j := by
    apply Nat.div_eq_of_lt_le
    · exact hklo
    · nlinarith
  simp only [hiddenNoise, dilation, residue, hl, hr, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- The complete probability of the infinite tail. -/
theorem positiveWeight_tsum_tail (N : ℕ) (hN : 0 < N) :
    (∑' k, positiveWeight (k + N)) = 1 / (N : ℝ) := by
  have hi := positiveWeight_interval 1 N (by omega) (by omega)
  rw [Finset.sum_Ico_eq_sub _ (by omega)] at hi
  have hs := positiveWeight_summable.sum_add_tsum_nat_add N
  rw [positiveWeight_tsum] at hs
  have hz : positiveWeight 0 = 0 := by norm_num [positiveWeight]
  simp only [Finset.sum_range_one, hz, sub_zero, Nat.cast_one, div_one] at hi
  linarith

/-- Exact finite decomposition into adjacent blocks; no disjointness approximation. -/
theorem sum_Ico_mul_blocks (f : ℕ → ℝ) (n L : ℕ) :
    (∑ k ∈ Finset.Ico n ((L + 1) * n), f k) =
      ∑ j ∈ Finset.range L, ∑ k ∈ Finset.Ico ((j + 1) * n) ((j + 2) * n), f k := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ← ih]
    rw [Finset.sum_Ico_eq_sub _ (by nlinarith),
      Finset.sum_Ico_eq_sub _ (by nlinarith),
      Finset.sum_Ico_eq_sub _ (by nlinarith)]
    ring

/-- Both moment integrands are absolutely summable against the full Pareto law. -/
theorem hiddenNoise_square_summable (n : ℕ) :
    Summable (fun k => positiveWeight k * (hiddenNoise n k)^2) := by
  simpa only [pow_two] using weighted_summable_of_bounded
    (bounded_product (hiddenNoise_abs_le_add_two n) (hiddenNoise_abs_le_add_two n))

theorem hiddenNoise_absolute_summable (n : ℕ) :
    Summable (fun k => positiveWeight k * |hiddenNoise n k|) := by
  apply weighted_summable_of_bounded
  intro k
  simpa only [abs_abs] using hiddenNoise_abs_le_add_two n k

/-- Exact first moment of one mismatch interval. -/
theorem hiddenNoise_interval_absolute (n j : ℕ) (hj : 0 < j)
    (hjn : 2 * j ≤ n) :
    (∑ k ∈ Finset.Ico (j * n) (j * (n + 2)),
      positiveWeight k * |hiddenNoise n k|) =
      if j % 2 = 1 then 2 / ((j : ℝ) * ((n : ℝ) + 2))
      else 2 / ((j : ℝ) * n) := by
  have hn : 0 < n := by omega
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hnp : (n : ℝ) + 2 ≠ 0 := by positivity
  by_cases ho : j % 2 = 1
  · rw [if_pos ho]
    calc
      _ = (∑ k ∈ Finset.Ico (j * n) (j * (n + 2)), positiveWeight k) * (n : ℝ) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [hiddenNoise_interval_odd n j k hj hjn
          (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2 ho]
        simp
      _ = _ := by
        rw [hiddenNoise_interval_mass n j hn hj]
        field_simp
  · have he : j % 2 = 0 := by omega
    rw [if_neg ho]
    calc
      _ = (∑ k ∈ Finset.Ico (j * n) (j * (n + 2)), positiveWeight k) * ((n : ℝ) + 2) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        rw [hiddenNoise_interval_even n j k hj hjn
          (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2 he]
        rw [abs_of_nonneg (by positivity)]
      _ = _ := by
        rw [hiddenNoise_interval_mass n j hn hj]
        field_simp

/-- The mismatch part of the second moment, keeping the parity coefficient exactly. -/
def hiddenNoiseMismatchSquare (n j : ℕ) : ℝ :=
  if j % 2 = 1 then 2 * n / ((j : ℝ) * ((n : ℝ) + 2))
  else 2 * ((n : ℝ) + 2) / ((j : ℝ) * n)

/-- The mismatch part of the first moment. -/
def hiddenNoiseMismatchAbsolute (n j : ℕ) : ℝ :=
  if j % 2 = 1 then 2 / ((j : ℝ) * ((n : ℝ) + 2))
  else 2 / ((j : ℝ) * n)

/-- Exact block decomposition for the squared norm, including its regular remainder. -/
theorem hiddenNoise_block_square_exact (n j : ℕ) (hj : 0 < j)
    (hjn : 2 * j ≤ n) :
    (∑ k ∈ Finset.Ico (j * n) ((j + 1) * n),
      positiveWeight k * (hiddenNoise n k)^2) =
      hiddenNoiseMismatchSquare n j +
      ∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n),
        positiveWeight k * (2 * (j % 2 : ℕ))^2 := by
  have hleft : j * n ≤ j * (n + 2) := by nlinarith
  have hright : j * (n + 2) ≤ (j + 1) * n := by nlinarith
  have he : (∑ k ∈ Finset.Ico (j * n) (j * (n + 2)),
      positiveWeight k * (hiddenNoise n k)^2) = hiddenNoiseMismatchSquare n j := by
    by_cases ho : j % 2 = 1
    · simpa only [hiddenNoiseMismatchSquare, if_pos ho] using
        hiddenNoise_interval_energy_odd n j hj hjn ho
    · have hev : j % 2 = 0 := by omega
      simpa only [hiddenNoiseMismatchSquare, if_neg ho] using
        hiddenNoise_interval_energy_even n j hj hjn hev
  have hr : (∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n),
      positiveWeight k * (hiddenNoise n k)^2) =
      ∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n),
        positiveWeight k * (2 * (j % 2 : ℕ))^2 := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hiddenNoise_regular_value n j k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2]
  rw [← he, ← hr]
  rw [Finset.sum_Ico_eq_sub _ (le_trans hleft hright),
    Finset.sum_Ico_eq_sub _ hleft, Finset.sum_Ico_eq_sub _ hright]
  ring

/-- Exact block decomposition for the first absolute moment. -/
theorem hiddenNoise_block_absolute_exact (n j : ℕ) (hj : 0 < j)
    (hjn : 2 * j ≤ n) :
    (∑ k ∈ Finset.Ico (j * n) ((j + 1) * n),
      positiveWeight k * |hiddenNoise n k|) =
      hiddenNoiseMismatchAbsolute n j +
      ∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n),
        positiveWeight k * (2 * (j % 2 : ℕ)) := by
  have hleft : j * n ≤ j * (n + 2) := by nlinarith
  have hright : j * (n + 2) ≤ (j + 1) * n := by nlinarith
  have he := hiddenNoise_interval_absolute n j hj hjn
  change (∑ k ∈ Finset.Ico (j * n) (j * (n + 2)),
    positiveWeight k * |hiddenNoise n k|) = hiddenNoiseMismatchAbsolute n j at he
  have hr : (∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n),
      positiveWeight k * |hiddenNoise n k|) =
      ∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n),
        positiveWeight k * (2 * (j % 2 : ℕ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hiddenNoise_regular_value n j k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2]
    rw [abs_of_nonneg (by positivity)]
  rw [← he, ← hr]
  rw [Finset.sum_Ico_eq_sub _ (le_trans hleft hright),
    Finset.sum_Ico_eq_sub _ hleft, Finset.sum_Ico_eq_sub _ hright]
  ring

/-- Exact head/block/tail decomposition for every bounded anchored nonnegative sequence. -/
theorem paretoMean_blocks_exact (f : ℕ → ℝ) {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (n L : ℕ) (hhead : ∀ k < n, f k = 0) :
    paretoMean f =
      (∑ j ∈ Finset.range L, ∑ k ∈ Finset.Ico ((j + 1) * n) ((j + 2) * n),
        positiveWeight k * f k) +
      ∑' k, positiveWeight (k + (L + 1) * n) * f (k + (L + 1) * n) := by
  have hz : (∑ k ∈ Finset.range n, positiveWeight k * f k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hhead k (Finset.mem_range.mp hk), mul_zero]
  have hb := sum_Ico_mul_blocks (fun k => positiveWeight k * f k) n L
  rw [Finset.sum_Ico_eq_sub _ (by nlinarith), hz, sub_zero] at hb
  unfold paretoMean
  rw [← (weighted_summable_of_bounded hf).sum_add_tsum_nat_add ((L + 1) * n), hb]

/-- A full-tail bound with actual summability and exact Pareto tail mass. -/
theorem pareto_nonnegative_tail_bounds (f : ℕ → ℝ) {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : ∀ k, 0 ≤ f k) (N : ℕ) (hN : 0 < N) :
    0 ≤ (∑' k, positiveWeight (k + N) * f (k + N)) ∧
      (∑' k, positiveWeight (k + N) * f (k + N)) ≤ C / N := by
  have hs := (summable_nat_add_iff N).mpr (weighted_summable_of_bounded hf)
  have hw := (summable_nat_add_iff N).mpr positiveWeight_summable
  constructor
  · exact tsum_nonneg (fun k => mul_nonneg (positiveWeight_nonneg _) (hf0 _))
  · calc
      _ ≤ ∑' k, positiveWeight (k + N) * C := by
        apply Summable.tsum_le_tsum _ hs (hw.mul_right C)
        intro k
        exact mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (hf _)) (positiveWeight_nonneg _)
      _ = C / N := by
        rw [hw.tsum_mul_right, positiveWeight_tsum_tail N hN]
        ring

/-- A finite block error passes to the infinite Pareto mean with a retained tail term. -/
theorem paretoMean_block_error_bound (f : ℕ → ℝ) {C B ε : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hf0 : ∀ k, 0 ≤ f k)
    (hB : 0 ≤ B) (n L : ℕ) (hn : 0 < n)
    (hhead : ∀ k < n, f k = 0)
    (herr : ∀ j ∈ Finset.range L,
      |(∑ k ∈ Finset.Ico ((j + 1) * n) ((j + 2) * n), positiveWeight k * f k) -
        2 / ((j + 1 : ℕ) : ℝ)| ≤ ε +
        B * ∑ k ∈ Finset.Ico ((j + 1) * n) ((j + 2) * n), positiveWeight k) :
    |paretoMean f - 2 * (∑ j ∈ Finset.range L, (1 : ℝ) / ((j + 1 : ℕ) : ℝ))| ≤
      (L : ℝ) * ε + B / n + C / (((L + 1) * n : ℕ) : ℝ) := by
  have hN : 0 < (L + 1) * n := Nat.mul_pos (by omega) hn
  have hb := sum_Ico_mul_blocks positiveWeight n L
  rw [positiveWeight_interval n ((L + 1) * n) hn (by nlinarith)] at hb
  have he :
      |(∑ j ∈ Finset.range L, ∑ k ∈ Finset.Ico ((j + 1) * n) ((j + 2) * n),
        positiveWeight k * f k) -
        2 * (∑ j ∈ Finset.range L, (1 : ℝ) / ((j + 1 : ℕ) : ℝ))| ≤
      (L : ℝ) * ε + B / n := by
    have hsum := Finset.sum_le_sum herr
    have htri := Finset.abs_sum_le_sum_abs
      (fun j => (∑ k ∈ Finset.Ico ((j + 1) * n) ((j + 2) * n),
        positiveWeight k * f k) - 2 / ((j + 1 : ℕ) : ℝ)) (Finset.range L)
    have hsumref : (∑ j ∈ Finset.range L, 2 / ((j + 1 : ℕ) : ℝ)) =
        2 * ∑ j ∈ Finset.range L, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [Finset.sum_sub_distrib, hsumref] at htri
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hb] at hsum
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have htail : 0 ≤ B * (1 / (((L + 1) * n : ℕ) : ℝ)) := by positivity
    have har : B * (1 / (n : ℝ) - 1 / (((L + 1) * n : ℕ) : ℝ)) =
        B / n - B * (1 / (((L + 1) * n : ℕ) : ℝ)) := by ring
    rw [har] at hsum
    linarith
  have ht := pareto_nonnegative_tail_bounds f hf hf0 ((L + 1) * n) hN
  rw [paretoMean_blocks_exact f hf n L hhead]
  calc
    _ = |((∑ j ∈ Finset.range L, ∑ k ∈ Finset.Ico ((j + 1) * n) ((j + 2) * n),
        positiveWeight k * f k) -
        2 * (∑ j ∈ Finset.range L, (1 : ℝ) / ((j + 1 : ℕ) : ℝ))) +
        ∑' k, positiveWeight (k + (L + 1) * n) * f (k + (L + 1) * n)| := by
      congr 1
      ring
    _ ≤ _ := by
      apply (abs_add_le _ _).trans
      rw [abs_of_nonneg ht.1]
      exact add_le_add he ht.2

/-- Uniform error of the exact mismatch square coefficient against its harmonic main term. -/
theorem hiddenNoiseMismatchSquare_error (n j : ℕ) (hn : 0 < n) (hj : 0 < j) :
    |hiddenNoiseMismatchSquare n j - 2 / (j : ℝ)| ≤ 4 / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hnp : (n : ℝ) + 2 ≠ 0 := by positivity
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold hiddenNoiseMismatchSquare
  split_ifs
  · have he : 2 * (n : ℝ) / ((j : ℝ) * ((n : ℝ) + 2)) - 2 / (j : ℝ) =
        -(4 / ((j : ℝ) * ((n : ℝ) + 2))) := by field_simp; ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (by positivity) hnr).mpr
    nlinarith
  · have he : 2 * ((n : ℝ) + 2) / ((j : ℝ) * n) - 2 / (j : ℝ) =
        4 / ((j : ℝ) * n) := by field_simp; ring
    rw [he, abs_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (by positivity) hnr).mpr
    nlinarith

/-- The first absolute-moment mismatch coefficient has the same harmonic main term after scaling. -/
theorem hiddenNoiseMismatchAbsolute_error (n j : ℕ) (hn : 0 < n) (hj : 0 < j) :
    |(n : ℝ) * hiddenNoiseMismatchAbsolute n j - 2 / (j : ℝ)| ≤ 4 / (n : ℝ) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hnp : (n : ℝ) + 2 ≠ 0 := by positivity
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold hiddenNoiseMismatchAbsolute
  split_ifs
  · have he : (n : ℝ) * (2 / ((j : ℝ) * ((n : ℝ) + 2))) - 2 / (j : ℝ) =
        -(4 / ((j : ℝ) * ((n : ℝ) + 2))) := by field_simp; ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (by positivity) hnr).mpr
    nlinarith
  · have he : (n : ℝ) * (2 / ((j : ℝ) * n)) - 2 / (j : ℝ) = 0 := by field_simp; ring
    rw [he, abs_zero]
    positivity

/-- Bounding the regular piece uses containment in its own block, before summing any blocks. -/
theorem hiddenNoise_regular_sum_bounds (n j : ℕ) {a B : ℝ}
    (ha : 0 ≤ a) (haB : a ≤ B) :
    0 ≤ (∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n), positiveWeight k * a) ∧
    (∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n), positiveWeight k * a) ≤
      B * ∑ k ∈ Finset.Ico (j * n) ((j + 1) * n), positiveWeight k := by
  have hsub : Finset.Ico (j * (n + 2)) ((j + 1) * n) ⊆
      Finset.Ico (j * n) ((j + 1) * n) := by
    intro k hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
    apply Finset.mem_Ico.mpr
    constructor
    · nlinarith
    · exact hhi
  constructor
  · exact Finset.sum_nonneg (fun k hk => mul_nonneg (positiveWeight_nonneg _) ha)
  · calc
      _ ≤ ∑ k ∈ Finset.Ico (j * n) ((j + 1) * n), positiveWeight k * a :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun k hk hnk => mul_nonneg (positiveWeight_nonneg _) ha)
      _ ≤ ∑ k ∈ Finset.Ico (j * n) ((j + 1) * n), positiveWeight k * B :=
        Finset.sum_le_sum (fun k hk =>
          mul_le_mul_of_nonneg_left haB (positiveWeight_nonneg _))
      _ = _ := by rw [← Finset.sum_mul]; ring

/-- Complete square-moment block bound, including the regular head contribution. -/
theorem hiddenNoise_block_square_error (n j : ℕ) (hj : 0 < j) (hjn : 2 * j ≤ n) :
    |(∑ k ∈ Finset.Ico (j * n) ((j + 1) * n),
      positiveWeight k * (hiddenNoise n k)^2) - 2 / (j : ℝ)| ≤
      4 / (n : ℝ) + 4 * ∑ k ∈ Finset.Ico (j * n) ((j + 1) * n), positiveWeight k := by
  have hn : 0 < n := by omega
  have hp : (0 : ℝ) ≤ (j % 2 : ℕ) := Nat.cast_nonneg _
  have hp1 : ((j % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show j % 2 ≤ 1 by omega)
  have hr := hiddenNoise_regular_sum_bounds n j
    (sq_nonneg (2 * ((j % 2 : ℕ) : ℝ))) (show (2 * ((j % 2 : ℕ) : ℝ))^2 ≤ 4 by nlinarith)
  rw [hiddenNoise_block_square_exact n j hj hjn]
  calc
    _ = |(hiddenNoiseMismatchSquare n j - 2 / (j : ℝ)) +
        ∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n),
          positiveWeight k * (2 * (j % 2 : ℕ))^2| := by congr 1; ring
    _ ≤ _ := by
      apply (abs_add_le _ _).trans
      rw [abs_of_nonneg hr.1]
      exact add_le_add (hiddenNoiseMismatchSquare_error n j hn hj) hr.2

/-- Complete scaled absolute-moment block bound. -/
theorem hiddenNoise_block_scaled_absolute_error (n j : ℕ) (hj : 0 < j)
    (hjn : 2 * j ≤ n) :
    |(∑ k ∈ Finset.Ico (j * n) ((j + 1) * n),
      positiveWeight k * ((n : ℝ) * |hiddenNoise n k|)) - 2 / (j : ℝ)| ≤
      4 / (n : ℝ) + (2 * n) * ∑ k ∈ Finset.Ico (j * n) ((j + 1) * n), positiveWeight k := by
  have hn : 0 < n := by omega
  have hp : (0 : ℝ) ≤ (j % 2 : ℕ) := Nat.cast_nonneg _
  have hp1 : ((j % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show j % 2 ≤ 1 by omega)
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr := hiddenNoise_regular_sum_bounds n j
    (show 0 ≤ (n : ℝ) * (2 * ((j % 2 : ℕ) : ℝ)) by positivity)
    (show (n : ℝ) * (2 * ((j % 2 : ℕ) : ℝ)) ≤ 2 * n by nlinarith)
  have he : (∑ k ∈ Finset.Ico (j * n) ((j + 1) * n),
      positiveWeight k * ((n : ℝ) * |hiddenNoise n k|)) =
      (n : ℝ) * (∑ k ∈ Finset.Ico (j * n) ((j + 1) * n),
        positiveWeight k * |hiddenNoise n k|) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, hiddenNoise_block_absolute_exact n j hj hjn]
  have he' : (n : ℝ) *
      (∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n),
        positiveWeight k * (2 * (j % 2 : ℕ))) =
      ∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n),
        positiveWeight k * ((n : ℝ) * (2 * (j % 2 : ℕ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [mul_add, he']
  calc
    _ = |((n : ℝ) * hiddenNoiseMismatchAbsolute n j - 2 / (j : ℝ)) +
        ∑ k ∈ Finset.Ico (j * (n + 2)) ((j + 1) * n),
          positiveWeight k * ((n : ℝ) * (2 * (j % 2 : ℕ)))| := by congr 1; ring
    _ ≤ _ := by
      apply (abs_add_le _ _).trans
      rw [abs_of_nonneg hr.1]
      exact add_le_add (hiddenNoiseMismatchAbsolute_error n j hn hj) hr.2

/-- The actual infinite squared norm is within a universal constant of twice a finite harmonic sum. -/
theorem hiddenNoise_secondMoment_harmonic_bound (n : ℕ) (hn : 3 ≤ n) :
    |paretoInner (hiddenNoise n) (hiddenNoise n) -
      2 * (∑ j ∈ Finset.range (n / 2), (1 : ℝ) / ((j + 1 : ℕ) : ℝ))| ≤ 16 := by
  have hnp : 0 < n := by omega
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < n := by positivity
  have hL : (n / 2 : ℕ) ≤ n := by omega
  have hLR : ((n / 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hL
  have hLhi : n ≤ 2 * (n / 2) + 1 := by omega
  have hLhiR : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hLhi
  have hf : ∀ k, |(hiddenNoise n k)^2| ≤ ((n : ℝ) + 2)^2 := by
    intro k
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hiddenNoise_abs_le_add_two n k, sq_abs (hiddenNoise n k), abs_nonneg (hiddenNoise n k)]
  have he := paretoMean_block_error_bound (fun k => (hiddenNoise n k)^2) hf
    (fun k => sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 4) n (n / 2) hnp
    (fun k hk => by rw [hiddenNoise_head_zero n k hk]; norm_num)
    (fun j hj => by
      simpa only [Nat.add_assoc] using hiddenNoise_block_square_error n (j + 1) (by omega)
        (by have hj' := Finset.mem_range.mp hj; omega))
  have hfirst : ((n / 2 : ℕ) : ℝ) * (4 / (n : ℝ)) ≤ 4 := by
    have heq : ((n / 2 : ℕ) : ℝ) * (4 / (n : ℝ)) =
        (((n / 2 : ℕ) : ℝ) * 4) / (n : ℝ) := by ring
    rw [heq]
    apply (div_le_iff₀ hnRpos).mpr
    nlinarith
  have hsecond : (4 : ℝ) / n ≤ 4 := by
    apply (div_le_iff₀ hnRpos).mpr
    nlinarith
  have hthird : ((n : ℝ) + 2)^2 / ((((n / 2 + 1) * n : ℕ)) : ℝ) ≤ 6 := by
    push_cast
    apply (div_le_iff₀ (by positivity : 0 < (((n / 2 : ℕ) : ℝ) + 1) * (n : ℝ))).mpr
    have hmul := mul_le_mul_of_nonneg_left hLhiR (le_of_lt hnRpos)
    nlinarith [sq_nonneg ((n : ℝ) - 3)]
  change |paretoInner (hiddenNoise n) (hiddenNoise n) -
    2 * (∑ j ∈ Finset.range (n / 2), (1 : ℝ) / ((j + 1 : ℕ) : ℝ))| ≤ 16
  have heq : paretoMean (fun k => (hiddenNoise n k)^2) =
      paretoInner (hiddenNoise n) (hiddenNoise n) := by
    simp only [paretoMean, paretoInner, pow_two]
  rw [heq] at he
  linarith

/-- The complete scaled first absolute moment has the same harmonic main term. -/
theorem hiddenNoise_firstMoment_harmonic_bound (n : ℕ) (hn : 3 ≤ n) :
    |(n : ℝ) * paretoMean (fun k => |hiddenNoise n k|) -
      2 * (∑ j ∈ Finset.range (n / 2), (1 : ℝ) / ((j + 1 : ℕ) : ℝ))| ≤ 16 := by
  have hnp : 0 < n := by omega
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < n := by positivity
  have hnRnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : (n / 2 : ℕ) ≤ n := by omega
  have hLR : ((n / 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hL
  have hLhi : n ≤ 2 * (n / 2) + 1 := by omega
  have hLhiR : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hLhi
  have hf : ∀ k, abs ((n : ℝ) * abs (hiddenNoise n k)) ≤ (n : ℝ) * ((n : ℝ) + 2) := by
    intro k
    rw [abs_mul, abs_of_nonneg hnRnonneg, abs_abs]
    exact mul_le_mul_of_nonneg_left (hiddenNoise_abs_le_add_two n k) hnRnonneg
  have he := paretoMean_block_error_bound (fun k => (n : ℝ) * |hiddenNoise n k|) hf
    (fun k => mul_nonneg hnRnonneg (abs_nonneg _))
    (by positivity : (0 : ℝ) ≤ 2 * n) n (n / 2) hnp
    (fun k hk => by rw [hiddenNoise_head_zero n k hk]; norm_num)
    (fun j hj => by
      simpa only [Nat.add_assoc] using hiddenNoise_block_scaled_absolute_error n (j + 1) (by omega)
        (by have hj' := Finset.mem_range.mp hj; omega))
  have hfirst : ((n / 2 : ℕ) : ℝ) * (4 / (n : ℝ)) ≤ 4 := by
    have heq : ((n / 2 : ℕ) : ℝ) * (4 / (n : ℝ)) =
        (((n / 2 : ℕ) : ℝ) * 4) / (n : ℝ) := by ring
    rw [heq]
    apply (div_le_iff₀ hnRpos).mpr
    nlinarith
  have hsecond : (2 * (n : ℝ)) / n ≤ 2 := by
    apply (div_le_iff₀ hnRpos).mpr
    linarith
  have hthird : ((n : ℝ) * ((n : ℝ) + 2)) /
      ((((n / 2 + 1) * n : ℕ)) : ℝ) ≤ 4 := by
    push_cast
    apply (div_le_iff₀ (by positivity : 0 < (((n / 2 : ℕ) : ℝ) + 1) * (n : ℝ))).mpr
    have hmul := mul_le_mul_of_nonneg_left hLhiR hnRnonneg
    nlinarith
  have heq : paretoMean (fun k => (n : ℝ) * |hiddenNoise n k|) =
      (n : ℝ) * paretoMean (fun k => |hiddenNoise n k|) := by
    unfold paretoMean
    have hp : (fun k => positiveWeight k * ((n : ℝ) * |hiddenNoise n k|)) =
        (fun k => (n : ℝ) * (positiveWeight k * |hiddenNoise n k|)) := by
      funext k
      ring
    rw [hp, (hiddenNoise_absolute_summable n).tsum_mul_left]
  rw [heq] at he
  linarith

end
end RiemannResearch.RH.Pareto
