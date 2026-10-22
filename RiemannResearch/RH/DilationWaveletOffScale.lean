import RiemannResearch.Analysis.BoundedPrimitiveAbel
import RiemannResearch.RH.BinaryWaveletPrimitive
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Complete signed Gram bounds across dilation scales

Source: analytic_wavelet_foothold.md, §§4–5, with a discrete Abel proof.
The nonnegative triangular primitive yields an interval estimate; summing
all coarse blocks gives a complete infinite weighted Gram bound. No Gram
operator, block norm, lower Riesz bound, or RH assertion follows from this
pairwise theorem.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter RiemannResearch.Analysis
noncomputable section

theorem binary_wavelet_abs_le (m k : ℕ) : |dilationWaveletSequence 2 m k| ≤ 1 := by
  have h₁ : k / m % 2 < 2 := Nat.mod_lt _ (by omega)
  have h₂ : k / (2*m) % 2 < 2 := Nat.mod_lt _ (by omega)
  have h₁' : k / m % 2 = 0 ∨ k / m % 2 = 1 := by omega
  have h₂' : k / (2*m) % 2 = 0 ∨ k / (2*m) % 2 = 1 := by omega
  rcases h₁' with h₁' | h₁' <;> rcases h₂' with h₂' | h₂' <;>
    norm_num [dilationWaveletSequence, digitSequence, h₁', h₂']

private theorem positiveWeight_shift_antitone (p : ℕ) (hp : 0 < p) :
    Antitone (fun k : ℕ => positiveWeight (p+k)) := by
  intro i j hij
  have hp' : 0 < (p:ℝ) := by exact_mod_cast hp
  have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg i
  have hij' : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
  unfold positiveWeight
  push_cast
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul (add_le_add le_rfl hij')
    (by linarith) (by positivity) (by positivity)

/-- Exact signed interval identity for the actual binary wavelet. -/
theorem binary_wavelet_interval_abel (m p N : ℕ) (hm : 0 < m) :
    (∑ k ∈ Finset.range N, dilationWaveletSequence 2 m (p+k) * positiveWeight (p+k)) =
      binaryWaveletPrimitive m (p+N) * positiveWeight (p+N) -
      binaryWaveletPrimitive m p * positiveWeight p +
      ∑ k ∈ Finset.range N, binaryWaveletPrimitive m (p+k+1) *
        (positiveWeight (p+k) - positiveWeight (p+k+1)) := by
  have h := boundedPrimitive_abel_identity
    (fun k => binaryWaveletPrimitive m (p+k))
    (fun k => positiveWeight (p+k)) N
  simpa only [← Nat.add_assoc, Nat.add_zero, binaryWaveletPrimitive_step m hm] using h

/-- The whole signed interval is bounded using its starting weight. -/
theorem binary_wavelet_weighted_interval (m p N : ℕ) (hm : 0 < m) (hp : 0 < p) :
    |∑ k ∈ Finset.range N,
      dilationWaveletSequence 2 m (p+k) * positiveWeight (p+k)| ≤
      (m:ℝ) * positiveWeight p := by
  have h := boundedPrimitive_weighted_interval_bound
    (fun k => binaryWaveletPrimitive m (p+k))
    (fun k => positiveWeight (p+k)) (m:ℝ) N
    (fun k => binaryWaveletPrimitive_bounds m hm (p+k))
    (fun k => positiveWeight_nonneg (p+k)) (positiveWeight_shift_antitone p hp)
  simpa only [← Nat.add_assoc, Nat.add_zero, binaryWaveletPrimitive_step m hm] using h

/-- Full infinite signed Abel identity for the actual Gram entry, with all
summability and the vanishing endpoint proved for the binary wavelets. -/
theorem binary_wavelet_gram_abel (m n : ℕ) (hm : 0 < m) :
    paretoInner (dilationWaveletSequence 2 m) (dilationWaveletSequence 2 n) =
      ∑' k, binaryWaveletPrimitive m (k+1) *
        (positiveWeight k * dilationWaveletSequence 2 n k -
          positiveWeight (k+1) * dilationWaveletSequence 2 n (k+1)) := by
  let B := binaryWaveletPrimitive m
  let f := fun k => positiveWeight k * dilationWaveletSequence 2 n k
  have hB (k : ℕ) : |B k| ≤ (m:ℝ) := by
    rw [abs_of_nonneg (binaryWaveletPrimitive_bounds m hm k).1]
    exact (binaryWaveletPrimitive_bounds m hm k).2
  have hend_sum : Summable (fun k => B k * f k) := by
    convert weighted_summable_of_bounded
      (bounded_product hB (binary_wavelet_abs_le n)) using 1
    funext k
    dsimp [f]
    ring
  have hfirst : Summable (fun k => B (k+1) * f k) := by
    convert weighted_summable_of_bounded
      (bounded_product (fun k => hB (k+1)) (binary_wavelet_abs_le n)) using 1
    funext k
    dsimp [f]
    ring
  have hsecond : Summable (fun k => B (k+1) * f (k+1)) :=
    (summable_nat_add_iff 1).mpr hend_sum
  have hright : Summable (fun k => B (k+1) * (f k - f (k+1))) := by
    simpa only [mul_sub] using hfirst.sub hsecond
  have hleft : Summable (fun k => (B (k+1)-B k) * f k) := by
    have h := weighted_summable_of_bounded
      (bounded_product (binary_wavelet_abs_le m) (binary_wavelet_abs_le n))
    convert h using 1
    funext k
    dsimp [B, f]
    rw [binaryWaveletPrimitive_step m hm]
    ring
  have h := boundedPrimitive_abel_tsum B f hleft hright hend_sum.tendsto_atTop_zero
  simpa only [B, f, binaryWaveletPrimitive_step m hm, binaryWaveletPrimitive_zero,
    neg_zero, zero_mul, zero_add, mul_assoc, mul_left_comm, paretoInner] using h

private theorem binary_wavelet_block_value (n j k : ℕ) (_hn : 0 < n) (hk : k < n) :
    dilationWaveletSequence 2 n (n*j+k) = dilationWaveletSequence 2 1 j := by
  rw [dilationWaveletSequence_two_pullback]
  congr 1
  apply Nat.div_eq_of_lt_le
  · simpa only [Nat.mul_comm] using Nat.le_add_right (n*j) k
  · calc
      n*j+k < n*j+n := Nat.add_lt_add_left hk _
      _ = (j+1)*n := by ring

private theorem binary_wavelet_gram_block (m n j : ℕ) (hm : 0 < m) (hn : 0 < n) :
    |∑ k ∈ Finset.range n, positiveWeight (n*j+k) *
      (dilationWaveletSequence 2 m (n*j+k) * dilationWaveletSequence 2 n (n*j+k))| ≤
      (m:ℝ) * positiveWeight (n*j) := by
  have he : (∑ k ∈ Finset.range n, positiveWeight (n*j+k) *
      (dilationWaveletSequence 2 m (n*j+k) * dilationWaveletSequence 2 n (n*j+k))) =
      dilationWaveletSequence 2 1 j *
        ∑ k ∈ Finset.range n, dilationWaveletSequence 2 m (n*j+k) * positiveWeight (n*j+k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [binary_wavelet_block_value n j k hn (Finset.mem_range.mp hk)]
    ring
  rw [he, abs_mul]
  by_cases hj : j = 0
  · subst j
    simp [dilationWaveletSequence, digitSequence, positiveWeight]
  · have hnj : 0 < n*j := Nat.mul_pos hn (Nat.pos_of_ne_zero hj)
    calc
      _ ≤ 1 * |∑ k ∈ Finset.range n,
          dilationWaveletSequence 2 m (n*j+k) * positiveWeight (n*j+k)| := by
        exact mul_le_mul_of_nonneg_right (binary_wavelet_abs_le 1 j) (abs_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using binary_wavelet_weighted_interval m (n*j) n hm hnj

theorem positiveWeight_mul_bound (n j : ℕ) (hn : 0 < n) :
    positiveWeight (n*j) ≤ (2 / (n:ℝ)^2) * positiveWeight j := by
  by_cases hj : j = 0
  · subst j; simp [positiveWeight]
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hj' : 1 ≤ (j:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
  unfold positiveWeight
  push_cast
  rw [show 2 / (n:ℝ)^2 * (1 / ((j:ℝ)*((j:ℝ)+1))) =
      2 / ((n:ℝ)^2*(j:ℝ)*((j:ℝ)+1)) by
        field_simp
        <;> ring]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have h := mul_nonneg (mul_nonneg (sq_nonneg (n:ℝ)) (Nat.cast_nonneg j))
    (sub_nonneg.mpr hj')
  have hnj : 0 ≤ (n:ℝ)*(j:ℝ) := by positivity
  nlinarith

private theorem sum_range_mul_blocks (f : ℕ → ℝ) (n N : ℕ) :
    (∑ k ∈ Finset.range (n*N), f k) =
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range n, f (n*j+k) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Complete finite block estimate, uniform in the number of blocks. -/
theorem binary_wavelet_gram_partial_bound (m n N : ℕ) (hm : 0 < m) (hn : 0 < n) :
    |∑ k ∈ Finset.range (n*N), positiveWeight k *
      (dilationWaveletSequence 2 m k * dilationWaveletSequence 2 n k)| ≤
      2*(m:ℝ)/(n:ℝ)^2 := by
  rw [sum_range_mul_blocks]
  calc
    _ ≤ ∑ j ∈ Finset.range N, |∑ k ∈ Finset.range n, positiveWeight (n*j+k) *
        (dilationWaveletSequence 2 m (n*j+k) * dilationWaveletSequence 2 n (n*j+k))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range N, (m:ℝ) * positiveWeight (n*j) :=
      Finset.sum_le_sum fun j _ => binary_wavelet_gram_block m n j hm hn
    _ ≤ ∑ j ∈ Finset.range N, (m:ℝ) * ((2/(n:ℝ)^2) * positiveWeight j) := by
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (positiveWeight_mul_bound n j hn) (Nat.cast_nonneg m)
    _ = (2*(m:ℝ)/(n:ℝ)^2) * ∑ j ∈ Finset.range N, positiveWeight j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := by
      have hw : (∑ j ∈ Finset.range N, positiveWeight j) ≤ 1 := by
        rw [← positiveWeight_tsum]
        exact positiveWeight_summable.sum_le_tsum _ (fun j _ => positiveWeight_nonneg j)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hw
        (by positivity : 0 ≤ 2*(m:ℝ)/(n:ℝ)^2)

/-- Unconditional full signed Gram estimate at every pair of positive integer
scales. The factor 2 improves the paper's factor 3 via the discrete primitive. -/
theorem binary_wavelet_gram_bound (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    |paretoInner (dilationWaveletSequence 2 m) (dilationWaveletSequence 2 n)| ≤
      2*(m:ℝ)/(n:ℝ)^2 := by
  have hs := weighted_summable_of_bounded
    (bounded_product (binary_wavelet_abs_le m) (binary_wavelet_abs_le n))
  have hcofinal : Tendsto (fun N : ℕ => n*N) atTop atTop := by
    apply tendsto_atTop_mono (fun N => ?_) tendsto_id
    exact Nat.le_mul_of_pos_left N hn
  have hlim := (hs.hasSum.tendsto_sum_nat.comp hcofinal).abs
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall fun N => binary_wavelet_gram_partial_bound m n N hm hn

/-- Use both orientations of the signed Gram estimate. -/
theorem binary_wavelet_gram_bound_symmetric (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    |paretoInner (dilationWaveletSequence 2 m) (dilationWaveletSequence 2 n)| ≤
      min (2*(m:ℝ)/(n:ℝ)^2) (2*(n:ℝ)/(m:ℝ)^2) := by
  apply le_min (binary_wavelet_gram_bound m n hm hn)
  have he : paretoInner (dilationWaveletSequence 2 m) (dilationWaveletSequence 2 n) =
      paretoInner (dilationWaveletSequence 2 n) (dilationWaveletSequence 2 m) := by
    unfold paretoInner
    apply tsum_congr
    intro k
    rw [mul_comm (dilationWaveletSequence 2 m k) (dilationWaveletSequence 2 n k)]
  rw [he]
  exact binary_wavelet_gram_bound n m hn hm

/-- The same complete estimate in the actual Hilbert inner product. -/
theorem binary_wavelet_hilbert_gram_bound (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    |inner ℝ (dilationWaveletHilbert 2 m (by omega) hm)
      (dilationWaveletHilbert 2 n (by omega) hn)| ≤
      min (2*(m:ℝ)/(n:ℝ)^2) (2*(n:ℝ)/(m:ℝ)^2) := by
  rw [hilbert_inner_weighted, hilbertSequence_dilationWaveletHilbert,
    hilbertSequence_dilationWaveletHilbert]
  exact binary_wavelet_gram_bound_symmetric m n hm hn

end
end RiemannResearch.RH.Pareto
