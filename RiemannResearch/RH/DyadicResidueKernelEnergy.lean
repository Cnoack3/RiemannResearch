import RiemannResearch.RH.DyadicResidueJumps
import RiemannResearch.RH.DyadicKernelJumpEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Real


namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Exact square of the signed triadic jump. The coefficient 3 retains the
cross term: at triple multiples the square is 4m², not 10m². -/
theorem hilbertDilation_residue_three_difference_sq
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    (hilbertSequence (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) k -
      hilbertSequence (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) (k-1))^2 =
      (if m ∣ k then (m : ℝ)^2 else 0) +
        (if m*3 ∣ k then 3*(m : ℝ)^2 else 0) := by
  rw [hilbertDilation_residue_difference m 3 k hm (by norm_num) hk]
  by_cases hmd : m ∣ k
  · by_cases hmt : m*3 ∣ k
    · simp [hmd, hmt]
      ring
    · simp [hmd, hmt]
  · have hmt : ¬ m*3 ∣ k := by
      intro h
      exact hmd (dvd_trans (show m ∣ m*3 from ⟨3, rfl⟩) h)
    simp [hmd, hmt]

/-- The exceptional first physical coordinate occurs only at m=1. -/
theorem hilbertDilation_residue_three_head
    (m : ℕ) (hm : 0 < m) :
    hilbertSequence (hilbertDilation m hm (hilbertResidue 3 (by norm_num))) 1 =
      if m = 1 then 1 else 0 := by
  rw [hilbertDilation_sequence, hilbertResidue_sequence]
  by_cases he : m = 1
  · subst m
    norm_num [dilation, residue]
  · have hml : 1 < m := by omega
    simp [dilation, residue, Nat.div_eq_of_lt hml, he]

/-- Exact infinite kernel energy of the actual arithmetic vector, with both
nested divisibility channels and their mixed-term compensation included. -/
theorem dyadicKernelDefect_residue_three_norm_sq_arithmetic
    (m : ℕ) (hm : 0 < m) :
    ‖dyadicKernelDefect (hilbertDilation m hm (hilbertResidue 3 (by norm_num)))‖^2 =
      (if m = 1 then (1 : ℝ)/2 else 0) +
      ∑' n : ℕ,
        ((if m ∣ 2*(n+1)+1 then (m : ℝ)^2 else 0) +
          (if m*3 ∣ 2*(n+1)+1 then 3*(m : ℝ)^2 else 0)) /
            (2 * (2*((n : ℝ)+1)+1)^2) := by
  rw [dyadicKernelDefect_norm_sq_jumps, hilbertDilation_residue_three_head]
  congr 1
  · by_cases he : m = 1 <;> simp [he]
  · apply tsum_congr
    intro n
    have h := hilbertDilation_residue_three_difference_sq m (2*(n+1)+1) hm
      (by positivity)
    simpa only [Nat.add_sub_cancel] using congrArg
      (fun x : ℝ => x / (2 * (2*((n : ℝ)+1)+1)^2)) h

end
end RiemannResearch.RH.Pareto


/-!
# Uniform first-level kernel bound for the actual triadic residue dilations

Source: independently developed from the exact arithmetic jumps in the
user-provided September 10, 2026 dyadic regularization continuation.
The signed jumps are calculated first. Only then is their exact square
bounded. Sparse reindexing retains every nonzero arithmetic jump.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Sparse first-level jump energy has a uniform bound, independently of m. -/
theorem dyadicKernelDefect_residue_three_norm_sq_le_four
    (m : ℕ) (hm : 0 < m) :
    ‖dyadicKernelDefect (hilbertDilation m hm (hilbertResidue 3 (by norm_num)))‖^2 ≤ 4 := by
  classical
  let f := hilbertDilation m hm (hilbertResidue 3 (by norm_num))
  let e : ℕ → ℝ := fun n =>
    (hilbertSequence f (2*n+1) - hilbertSequence f (2*n))^2 /
      (2 * (2*(n : ℝ)+1)^2)
  let q : ℕ → ℕ := fun n => (2*n+1)/m
  have he0 : 0 ≤ e := by
    intro n
    dsimp [e]
    positivity
  have hezero (n : ℕ) (hnd : ¬ m ∣ 2*n+1) : e n = 0 := by
    have h := hilbertDilation_residue_difference_eq_zero m 3 (2*n+1) hm
      (by norm_num) (by positivity) hnd
    simp only [Nat.add_sub_cancel] at h
    change hilbertSequence f (2*n+1) - hilbertSequence f (2*n) = 0 at h
    dsimp only [e]
    rw [h]
    simp
  have hele (n : ℕ) (hd : m ∣ 2*n+1) : e n ≤ 4 * positiveWeight (q n) := by
    have hkn : 0 < 2*n+1 := by positivity
    have hq : 0 < q n := Nat.div_pos_iff.mpr ⟨hm, Nat.le_of_dvd hkn hd⟩
    have hqR : (1 : ℝ) ≤ q n := by
      exact_mod_cast (show 1 ≤ q n by omega)
    have hcast : 2*(n : ℝ)+1 = (m : ℝ)*(q n : ℝ) := by
      have hnat : 2*n+1 = m*q n := by
        simpa [q, Nat.mul_comm] using (Nat.div_mul_cancel hd).symm
      exact_mod_cast hnat
    have hd2 : (hilbertSequence f (2*n+1) - hilbertSequence f (2*n))^2 ≤
        4*(m : ℝ)^2 := by
      have h := hilbertDilation_residue_three_difference_values m (2*n+1) hm hkn
      dsimp only at h
      simp only [Nat.add_sub_cancel] at h
      change (hilbertSequence f (2*n+1) - hilbertSequence f (2*n) = 0 ∨
        hilbertSequence f (2*n+1) - hilbertSequence f (2*n) = (m : ℝ) ∨
        hilbertSequence f (2*n+1) - hilbertSequence f (2*n) = -2*(m : ℝ)) at h
      rcases h with h | h | h
      · rw [h]
        nlinarith [sq_nonneg (m : ℝ)]
      · rw [h]
        nlinarith [sq_nonneg (m : ℝ)]
      · rw [h]
        nlinarith [sq_nonneg (m : ℝ)]
    calc
      e n ≤ (4*(m : ℝ)^2)/(2*(2*(n : ℝ)+1)^2) :=
        div_le_div_of_nonneg_right hd2 (by positivity)
      _ = 2 / (q n : ℝ)^2 := by
        rw [hcast]
        have hmR : (m : ℝ) ≠ 0 := by positivity
        have hqR0 : (q n : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      _ ≤ 4 * positiveWeight (q n) := by
        unfold positiveWeight
        have hqpos : (0 : ℝ) < q n := by positivity
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ (sq_pos_of_pos hqpos) (by positivity)).mpr
        nlinarith
  have hfinite (s : Finset ℕ) : (∑ n ∈ s, e n) ≤ 4 := by
    let t := s.filter (fun n => m ∣ 2*n+1)
    have ht (n : ℕ) (hn : n ∈ t) : m ∣ 2*n+1 := (Finset.mem_filter.mp hn).2
    have hinj : Set.InjOn q (t : Set ℕ) := by
      intro a ha b hb hab
      have h1 := Nat.div_mul_cancel (ht a ha)
      have h2 := Nat.div_mul_cancel (ht b hb)
      change q a*m = 2*a+1 at h1
      change q b*m = 2*b+1 at h2
      rw [hab] at h1
      omega
    calc
      (∑ n ∈ s, e n) = ∑ n ∈ t, e n := by
        dsimp only [t]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hd : m ∣ 2*n+1
        · simp [hd]
        · simp [hd, hezero n hd]
      _ ≤ ∑ n ∈ t, 4 * positiveWeight (q n) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hele n (ht n hn)
      _ = ∑ r ∈ t.image q, 4 * positiveWeight r := by rw [Finset.sum_image hinj]
      _ ≤ ∑' r : ℕ, 4 * positiveWeight r :=
        (positiveWeight_summable.mul_left 4).sum_le_tsum _ (fun _ _ => by
          exact mul_nonneg (by norm_num) (positiveWeight_nonneg _))
      _ = 4 := by rw [tsum_mul_left, positiveWeight_tsum]; norm_num
  have hes : Summable e := summable_of_sum_le he0 hfinite
  have henorm : ‖dyadicKernelDefect f‖^2 = ∑' n : ℕ, e n := by
    rw [dyadicKernelDefect_norm_sq_jumps, hes.tsum_eq_zero_add]
    congr 1
    · dsimp only [e]
      simp only [Nat.mul_zero, Nat.zero_add, Nat.cast_zero, mul_zero,
        zero_add, hilbertSequence_zero, sub_zero, one_pow, mul_one]
    · apply tsum_congr
      intro n
      simp only [e, Nat.cast_add, Nat.cast_one]
  change ‖dyadicKernelDefect f‖^2 ≤ 4
  rw [henorm]
  exact Real.tsum_le_of_sum_le he0 hfinite

end
end RiemannResearch.RH.Pareto
