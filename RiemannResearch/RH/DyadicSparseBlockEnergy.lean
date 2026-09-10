import RiemannResearch.RH.DyadicKernelJumpEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Sparse block energy from the first arithmetic crossing

Source: independently developed from the weighted two-block argument in the
user-provided DyadicResidueKernelVerification20260910(1).md (September 10, 2026).

For adjacent blocks of common integer length d, the first interior multiple
of m gives an injective arithmetic label.  A uniform amplitude bound and
constancy when there is no crossing imply a kernel norm bound of four.
No comparison between d and m is required.  The zeroth pair includes the
exceptional first coordinate through hilbertSequence f 0 = 0.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- A sparse crossing estimate for the complete physical dyadic kernel energy.
The hypotheses concern actual physical coordinate differences, including the
first coordinate.  No series estimate or norm estimate is assumed. -/
theorem dyadicKernelDefect_norm_sq_le_sixteen_of_sparse_block_jumps
    (f : ThresholdHilbert) (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hbound : ∀ n : ℕ,
      |hilbertSequence f (2*n+1) - hilbertSequence f (2*n)| ≤
        2 * (m : ℝ) / (d : ℝ))
    (hzero : ∀ n : ℕ,
      2*d*(n+1) ≤ ((2*d*n)/m+1)*m →
      hilbertSequence f (2*n+1) - hilbertSequence f (2*n) = 0) :
    ‖dyadicKernelDefect f‖^2 ≤ 16 := by
  classical
  let e : ℕ → ℝ := fun n =>
    (hilbertSequence f (2*n+1) - hilbertSequence f (2*n))^2 /
      (2 * (2*(n : ℝ)+1)^2)
  let q : ℕ → ℕ := fun n => (2*d*n)/m+1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hqpositive (n : ℕ) : 0 < q n := Nat.zero_lt_succ _
  have hqlower (n : ℕ) : 2*d*n < q n*m := by
    dsimp only [q]
    have hmod := Nat.mod_lt (2*d*n) hm
    have heq := Nat.mod_add_div (2*d*n) m
    nlinarith
  have he0 : 0 ≤ e := by
    intro n
    dsimp [e]
    positivity
  have hezero (n : ℕ) (hn : ¬ q n*m < 2*d*(n+1)) : e n = 0 := by
    have hz := hzero n (by change 2*d*(n+1) ≤ q n*m; omega)
    dsimp only [e]
    rw [hz]
    simp
  have hele (n : ℕ) (hn : q n*m < 2*d*(n+1)) :
      e n ≤ 16 * positiveWeight (q n) := by
    have hqR : (1 : ℝ) ≤ q n := by
      exact_mod_cast (show 1 ≤ q n by have := hqpositive n; omega)
    have hqpos : (0 : ℝ) < q n := by positivity
    have hnR : (0 : ℝ) ≤ n := by positivity
    have hcrossR : (q n : ℝ)*(m : ℝ) <
        2*(d : ℝ)*((n : ℝ)+1) := by exact_mod_cast hn
    have hcross : (m : ℝ)*(q n : ℝ) ≤
        2*(d : ℝ)*(2*(n : ℝ)+1) := by
      have hdn : (0 : ℝ) ≤ (d : ℝ)*(n : ℝ) := by positivity
      nlinarith
    have hsq : ((m : ℝ)*(q n : ℝ))^2 ≤
        (2*(d : ℝ)*(2*(n : ℝ)+1))^2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hcross)
        (show (0 : ℝ) ≤ 2*(d : ℝ)*(2*(n : ℝ)+1) +
          (m : ℝ)*(q n : ℝ) by positivity)
      nlinarith
    have hdiff :
        (hilbertSequence f (2*n+1) - hilbertSequence f (2*n))^2 ≤
          (2*(m : ℝ)/(d : ℝ))^2 := by
      obtain ⟨hl, hu⟩ := abs_le.mp (hbound n)
      have hp := mul_nonneg (sub_nonneg.mpr hu)
        (show (0 : ℝ) ≤ 2*(m : ℝ)/(d : ℝ) +
          (hilbertSequence f (2*n+1) - hilbertSequence f (2*n)) by linarith)
      nlinarith
    have hscaled : (2*(m : ℝ)/(d : ℝ))^2 ≤
        16*(2*(n : ℝ)+1)^2/(q n : ℝ)^2 := by
      rw [div_pow]
      apply (div_le_div_iff₀ (sq_pos_of_pos hdR) (sq_pos_of_pos hqpos)).mpr
      nlinarith [hsq]
    calc
      e n ≤ (2*(m : ℝ)/(d : ℝ))^2 /
          (2*(2*(n : ℝ)+1)^2) :=
        div_le_div_of_nonneg_right hdiff (by positivity)
      _ ≤ (16*(2*(n : ℝ)+1)^2/(q n : ℝ)^2) /
          (2*(2*(n : ℝ)+1)^2) :=
        div_le_div_of_nonneg_right hscaled (by positivity)
      _ = 8/(q n : ℝ)^2 := by
        have hb : 2*(n : ℝ)+1 ≠ 0 := by positivity
        have hqne : (q n : ℝ) ≠ 0 := by positivity
        field_simp <;> ring
      _ ≤ 16 * positiveWeight (q n) := by
        unfold positiveWeight
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ (sq_pos_of_pos hqpos) (by positivity)).mpr
        nlinarith
  have hfinite (s : Finset ℕ) : (∑ n ∈ s, e n) ≤ 16 := by
    let t := s.filter (fun n => q n*m < 2*d*(n+1))
    have ht (n : ℕ) (hn : n ∈ t) : q n*m < 2*d*(n+1) :=
      (Finset.mem_filter.mp hn).2
    have hinj : Set.InjOn q (t : Set ℕ) := by
      intro a ha b hb hab
      have haL := hqlower a
      have hbL := hqlower b
      have haU := ht a ha
      have hbU := ht b hb
      apply le_antisymm
      · by_contra hnot
        have hba : b+1 ≤ a := by omega
        have hmul := Nat.mul_le_mul_left (2*d) hba
        rw [hab] at haL
        omega
      · by_contra hnot
        have hab' : a+1 ≤ b := by omega
        have hmul := Nat.mul_le_mul_left (2*d) hab'
        rw [hab] at haU
        omega
    calc
      (∑ n ∈ s, e n) = ∑ n ∈ t, e n := by
        dsimp only [t]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro n hn
        by_cases hc : q n*m < 2*d*(n+1)
        · simp [hc]
        · simp [hc, hezero n hc]
      _ ≤ ∑ n ∈ t, 16 * positiveWeight (q n) := by
        apply Finset.sum_le_sum
        intro n hn
        exact hele n (ht n hn)
      _ = ∑ r ∈ t.image q, 16 * positiveWeight r := by
        rw [Finset.sum_image hinj]
      _ ≤ ∑' r : ℕ, 16 * positiveWeight r :=
        (positiveWeight_summable.mul_left 16).sum_le_tsum _ (fun _ _ => by
          exact mul_nonneg (by norm_num) (positiveWeight_nonneg _))
      _ = 16 := by rw [tsum_mul_left, positiveWeight_tsum]; norm_num
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
  rw [henorm]
  exact Real.tsum_le_of_sum_le he0 hfinite

/-- Coordinate positivity and amplitude imply the required jump bound. -/
theorem dyadicKernelDefect_norm_sq_le_sixteen_of_sparse_block_coordinates
    (f : ThresholdHilbert) (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hcoordinates : ∀ k : ℕ,
      0 ≤ hilbertSequence f k ∧ hilbertSequence f k ≤
        2 * (m : ℝ) / (d : ℝ))
    (hzero : ∀ n : ℕ,
      2*d*(n+1) ≤ ((2*d*n)/m+1)*m →
      hilbertSequence f (2*n+1) - hilbertSequence f (2*n) = 0) :
    ‖dyadicKernelDefect f‖^2 ≤ 16 := by
  apply dyadicKernelDefect_norm_sq_le_sixteen_of_sparse_block_jumps f d m hd hm
    (fun n => ?_) hzero
  obtain ⟨ha0, ha1⟩ := hcoordinates (2*n+1)
  obtain ⟨hb0, hb1⟩ := hcoordinates (2*n)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The sparse block hypotheses give the stronger norm constant four. -/
theorem dyadicKernelDefect_norm_le_four_of_sparse_block_coordinates
    (f : ThresholdHilbert) (d m : ℕ) (hd : 0 < d) (hm : 0 < m)
    (hcoordinates : ∀ k : ℕ,
      0 ≤ hilbertSequence f k ∧ hilbertSequence f k ≤
        2 * (m : ℝ) / (d : ℝ))
    (hzero : ∀ n : ℕ,
      2*d*(n+1) ≤ ((2*d*n)/m+1)*m →
      hilbertSequence f (2*n+1) - hilbertSequence f (2*n) = 0) :
    ‖dyadicKernelDefect f‖ ≤ 4 := by
  have h := dyadicKernelDefect_norm_sq_le_sixteen_of_sparse_block_coordinates
    f d m hd hm hcoordinates hzero
  nlinarith [norm_nonneg (dyadicKernelDefect f)]

end
end RiemannResearch.RH.Pareto
