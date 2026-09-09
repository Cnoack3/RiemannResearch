import RiemannResearch.RH.DilationWaveletOffScale
import RiemannResearch.RH.BinaryWaveletNearbySupport

/-!
# A complete nearby-dilation energy estimate

Source: analytic_wavelet_foothold.md, §7. This discrete proof retains an
explicit complete tail and proves the near-parallel phenomenon without
assuming a Riesz or frame estimate. The sharper logarithmic leading term
from §8 is not asserted here.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

private def weightMask (s : Finset ℕ) (k : ℕ) : ℝ :=
  if k ∈ s then positiveWeight k else 0

private theorem weightMask_summable (s : Finset ℕ) : Summable (weightMask s) := by
  change Summable (fun k => if k ∈ s then positiveWeight k else 0)
  have h := weighted_summable_of_bounded (f := fun k => if k ∈ s then (1:ℝ) else 0)
    (C := 1) (fun k => by split_ifs <;> norm_num)
  simpa only [mul_ite, mul_one, mul_zero] using h

private theorem weightMask_tsum (s : Finset ℕ) :
    (∑' k, weightMask s k) = ∑ k ∈ s, positiveWeight k := by
  rw [tsum_eq_sum (s := s) (fun k hk => by simp [weightMask, hk])]
  exact Finset.sum_congr rfl fun k hk => by simp [weightMask, hk]

private def tailMask (M k : ℕ) : ℝ := if M ≤ k then positiveWeight k else 0

private theorem tailMask_summable (M : ℕ) : Summable (tailMask M) := by
  change Summable (fun k => if M ≤ k then positiveWeight k else 0)
  have h := weighted_summable_of_bounded (f := fun k => if M ≤ k then (1:ℝ) else 0)
    (C := 1) (fun k => by split_ifs <;> norm_num)
  simpa only [mul_ite, mul_one, mul_zero] using h

private theorem tailMask_tsum (M : ℕ) (hM : 0 < M) :
    (∑' k, tailMask M k) = 1 / (M:ℝ) := by
  have heq : (fun k => weightMask (Finset.range M) k + tailMask M k) = positiveWeight := by
    funext k
    by_cases hk : k < M
    · simp [weightMask, tailMask, Finset.mem_range, hk, Nat.not_le.mpr hk]
    · simp [weightMask, tailMask, Finset.mem_range, hk, Nat.le_of_not_gt hk]
  have he := (weightMask_summable (Finset.range M)).tsum_add (tailMask_summable M)
  rw [heq, positiveWeight_tsum, weightMask_tsum] at he
  have hh : (∑ k ∈ Finset.range M, positiveWeight k) = 1-1/(M:ℝ) := by
    rw [Finset.sum_range_eq_add_Ico positiveWeight hM,
      positiveWeight_interval 1 M (by omega) hM]
    norm_num [positiveWeight]
  rw [hh] at he
  linarith

theorem binary_wavelet_difference_sq_le_four (m n k : ℕ) :
    (dilationWaveletSequence 2 m k - dilationWaveletSequence 2 n k)^2 ≤ 4 := by
  have h : |dilationWaveletSequence 2 m k - dilationWaveletSequence 2 n k| ≤
      |dilationWaveletSequence 2 m k| + |dilationWaveletSequence 2 n k| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      (abs_sub_le (dilationWaveletSequence 2 m k) 0 (dilationWaveletSequence 2 n k))
  have hm := binary_wavelet_abs_le m k
  have hn := binary_wavelet_abs_le n k
  have hh : |dilationWaveletSequence 2 m k - dilationWaveletSequence 2 n k| ≤ 2 := by
    linarith
  have hp := abs_le.mp hh
  nlinarith

private theorem binary_wavelet_difference_square_summable (m n : ℕ) :
    Summable (fun k => positiveWeight k *
      (dilationWaveletSequence 2 m k - dilationWaveletSequence 2 n k)^2) := by
  apply weighted_summable_of_bounded (C := 4)
  intro k
  rw [abs_of_nonneg (sq_nonneg _)]
  exact binary_wavelet_difference_sq_le_four m n k

private theorem nearby_pointwise_energy (m J k : ℕ) (hm : 0 < m) :
    positiveWeight k * (dilationWaveletSequence 2 m k - dilationWaveletSequence 2 (m+1) k)^2 ≤
      4 * ((∑ j ∈ Finset.Icc 1 J,
        weightMask (Finset.Ico (m*j) ((m+1)*j)) k) + tailMask (m*J) k) := by
  have hsum : 0 ≤ ∑ j ∈ Finset.Icc 1 J,
      weightMask (Finset.Ico (m*j) ((m+1)*j)) k := by
    exact Finset.sum_nonneg fun j _ => by
      unfold weightMask
      split_ifs
      · exact positiveWeight_nonneg k
      · exact le_rfl
  have htail : 0 ≤ tailMask (m*J) k := by
    unfold tailMask
    split_ifs
    · exact positiveWeight_nonneg k
    · exact le_rfl
  have hbound := mul_le_mul_of_nonneg_left
    (binary_wavelet_difference_sq_le_four m (m+1) k) (positiveWeight_nonneg k)
  by_cases hk : m*J ≤ k
  · have ht : tailMask (m*J) k = positiveWeight k := by simp [tailMask, hk]
    rw [ht]
    nlinarith
  · by_cases he : dilationWaveletSequence 2 m k = dilationWaveletSequence 2 (m+1) k
    · rw [he, sub_self, zero_pow (by omega : 2 ≠ 0), mul_zero]
      positivity
    · obtain ⟨j, hj1, hjJ, hjlo, hjhi⟩ :=
        binaryWavelet_nearby_mismatch_support m (m+1) J k hm (by omega) (by omega) he
      have hj : j ∈ Finset.Icc 1 J := Finset.mem_Icc.mpr ⟨hj1, hjJ⟩
      have hmask : weightMask (Finset.Ico (m*j) ((m+1)*j)) k = positiveWeight k := by
        simp [weightMask, Finset.mem_Ico.mpr ⟨hjlo, hjhi⟩]
      have hle : weightMask (Finset.Ico (m*j) ((m+1)*j)) k ≤
          ∑ j ∈ Finset.Icc 1 J, weightMask (Finset.Ico (m*j) ((m+1)*j)) k := by
        apply Finset.single_le_sum (fun i hi => ?_) hj
        unfold weightMask
        split_ifs
        · exact positiveWeight_nonneg k
        · exact le_rfl
      rw [hmask] at hle
      nlinarith

private theorem nearby_mask_mass (m j : ℕ) (hm : 0 < m) (hj : 0 < j) :
    (∑' k, weightMask (Finset.Ico (m*j) ((m+1)*j)) k) =
      1 / ((m:ℝ)*((m:ℝ)+1)*(j:ℝ)) := by
  rw [weightMask_tsum, positiveWeight_interval _ _ (Nat.mul_pos hm hj)
    (Nat.mul_le_mul_right j (Nat.le_succ m))]
  push_cast
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hj0 : (j:ℝ) ≠ 0 := by positivity
  have hm1 : (m:ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Complete infinite energy estimate, with both the finite union of moved
jump intervals and the entire tail controlled explicitly. -/
theorem binary_wavelet_nearby_energy_bound (m J : ℕ) (hm : 0 < m) (hJ : 0 < J) :
    (∑' k, positiveWeight k *
      (dilationWaveletSequence 2 m k - dilationWaveletSequence 2 (m+1) k)^2) ≤
      4 * ((J:ℝ)/((m:ℝ)*((m:ℝ)+1)) + 1/((m:ℝ)*(J:ℝ))) := by
  have hhead : Summable (fun k => ∑ j ∈ Finset.Icc 1 J,
      weightMask (Finset.Ico (m*j) ((m+1)*j)) k) := by
    exact summable_sum fun j _ => weightMask_summable _
  have htail := tailMask_summable (m*J)
  have hrhs := (hhead.add htail).mul_left 4
  calc
    _ ≤ ∑' k, 4 * ((∑ j ∈ Finset.Icc 1 J,
        weightMask (Finset.Ico (m*j) ((m+1)*j)) k) + tailMask (m*J) k) :=
      (binary_wavelet_difference_square_summable m (m+1)).tsum_le_tsum
        (nearby_pointwise_energy m J · hm) hrhs
    _ = 4 * ((∑ j ∈ Finset.Icc 1 J,
        1/((m:ℝ)*((m:ℝ)+1)*(j:ℝ))) + 1/((m*J:ℕ):ℝ)) := by
      rw [(hhead.add htail).tsum_mul_left, hhead.tsum_add htail,
        Summable.tsum_finsetSum (fun j hj => weightMask_summable _),
        tailMask_tsum _ (Nat.mul_pos hm hJ)]
      congr 2
      apply Finset.sum_congr rfl
      intro j hj
      exact nearby_mask_mass m j hm (Finset.mem_Icc.mp hj).1
    _ ≤ _ := by
      push_cast
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add _ le_rfl
      calc
        _ ≤ ∑ j ∈ Finset.Icc 1 J, 1/((m:ℝ)*((m:ℝ)+1)) := by
          apply Finset.sum_le_sum
          intro j hj
          apply one_div_le_one_div_of_le (by positivity)
          have hj' : (1:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
          have hp : 0 ≤ (m:ℝ)*((m:ℝ)+1) := by positivity
          nlinarith
        _ = _ := by simp [Nat.card_Icc, div_eq_mul_inv]

/-- The same bound in the actual complete weighted Hilbert space. -/
theorem binary_wavelet_nearby_hilbert_energy_bound (m J : ℕ)
    (hm : 0 < m) (hJ : 0 < J) :
    ‖dilationWaveletHilbert 2 m (by omega) hm -
      dilationWaveletHilbert 2 (m+1) (by omega) (by omega)‖^2 ≤
      4 * ((J:ℝ)/((m:ℝ)*((m:ℝ)+1)) + 1/((m:ℝ)*(J:ℝ))) := by
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
  exact binary_wavelet_nearby_energy_bound m J hm hJ

end
end RiemannResearch.RH.Pareto
