import RiemannResearch.RH.ParetoRepairCovariance
import RiemannResearch.RH.ParetoResidueMoments
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact adjacent-repair calculus

Source: user-provided argument, `ParetoCovarianceRepairReport_Advanced_2026-09-08.md`,
Section 6; the source supplies the statements and summation-by-parts argument.
The sequence, full Pareto inner products, signed covariance, and terminal anchor
are explicit. No infinite-series convergence is inferred merely from these
finite identities.
-/

open scoped BigOperators

namespace Finset

/-- Finite Abel summation with both endpoints retained. -/
theorem sum_range_weighted_forward_difference (A t : ℕ → ℝ) (M N : ℕ) :
    (∑ j ∈ range (N + 1), t (M + j) * (A (M + j + 1) - A (M + j))) =
      -t M * A M +
        (∑ j ∈ range N, (t (M + j) - t (M + j + 1)) * A (M + j + 1)) +
        t (M + N) * A (M + N + 1) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    simp only [Nat.add_assoc]
    ring

end Finset

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Actual binary dilated residue profile. -/
def binaryDilation (n : ℕ) : ℕ → ℝ := dilation n (residue 2)

/-- The all-integer adjacent repair, with its genuine four residue terms. -/
def adjacentBinaryRepair (n : ℕ) : ℕ → ℝ := arithmeticRepair 2 n (n + 1)

/-- The full, infinite Pareto dilation kernel. -/
def binaryDilationKernel (a b : ℕ) : ℝ :=
  paretoInner (binaryDilation a) (binaryDilation b)

theorem binaryDilation_nonneg (n k : ℕ) : 0 ≤ binaryDilation n k := by
  unfold binaryDilation dilation residue
  positivity

theorem binaryDilation_le (n k : ℕ) : binaryDilation n k ≤ n := by
  have hr : (k / n) % 2 ≤ 1 := by omega
  have hrR : (((k / n) % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hr
  unfold binaryDilation dilation residue
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hrR (Nat.cast_nonneg n)

theorem binaryDilation_abs_le (n k : ℕ) : |binaryDilation n k| ≤ n := by
  rw [abs_of_nonneg (binaryDilation_nonneg n k)]
  exact binaryDilation_le n k

theorem binaryDilation_residue (n k : ℕ) :
    binaryDilation n k = residue (2 * n) k - residue n k := by
  unfold binaryDilation
  rw [residue_mul_floor]
  rw [Nat.mul_comm n 2]

theorem binaryDilation_head_zero (n k : ℕ) (hk : k < n) :
    binaryDilation n k = 0 := by
  simp [binaryDilation, dilation, residue, Nat.div_eq_of_lt hk]

theorem binaryDilation_mean (n : ℕ) (hn : 0 < n) :
    paretoMean (binaryDilation n) = Real.log 2 := by
  rw [binaryDilation, paretoMean_dilation (fun k => residue_abs_le 2 k (by omega))
    (by simp [residue]) n hn, paretoMean_residue_two]

theorem binaryDilationKernel_self (n : ℕ) (hn : 0 < n) :
    binaryDilationKernel n n = (n : ℝ) * Real.log 2 := by
  rw [binaryDilationKernel, binaryDilation,
    paretoInner_dilation (fun k => residue_abs_le 2 k (by omega))
      (fun k => residue_abs_le 2 k (by omega)) (by simp [residue]) n hn,
    paretoInner_residue_two]

theorem binaryDilationKernel_comm (a b : ℕ) :
    binaryDilationKernel a b = binaryDilationKernel b a :=
  paretoInner_comm _ _

theorem binaryDilationKernel_nonneg (a b : ℕ) : 0 ≤ binaryDilationKernel a b := by
  unfold binaryDilationKernel paretoInner
  exact tsum_nonneg (fun k => mul_nonneg (positiveWeight_nonneg k)
    (mul_nonneg (binaryDilation_nonneg a k) (binaryDilation_nonneg b k)))

/-- Positivity controls the full kernel by either scale, without a false
positive-semidefinite comparison for arbitrary signed coefficient vectors. -/
theorem binaryDilationKernel_le_left (a b : ℕ) (hb : 0 < b) :
    binaryDilationKernel a b ≤ (a : ℝ) * Real.log 2 := by
  have hprod := weighted_summable_of_bounded
    (bounded_product (binaryDilation_abs_le a) (binaryDilation_abs_le b))
  have hscaled := weighted_summable_of_bounded
    (bounded_const_mul (binaryDilation_abs_le b) (a : ℝ))
  have hs := weighted_summable_of_bounded (binaryDilation_abs_le b)
  calc
    binaryDilationKernel a b ≤
        ∑' k, positiveWeight k * ((a : ℝ) * binaryDilation b k) := by
      apply Summable.tsum_le_tsum _ hprod hscaled
      intro k
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (binaryDilation_le a k)
          (binaryDilation_nonneg b k)) (positiveWeight_nonneg k)
    _ = (a : ℝ) * paretoMean (binaryDilation b) := by
      calc
        _ = ∑' k, (a : ℝ) * (positiveWeight k * binaryDilation b k) := by
          apply tsum_congr
          intro k
          ring
        _ = _ := hs.tsum_mul_left _
    _ = (a : ℝ) * Real.log 2 := by rw [binaryDilation_mean b hb]

theorem binaryDilationKernel_le_min (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    binaryDilationKernel a b ≤ (min a b : ℕ) * Real.log 2 := by
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab]
    exact binaryDilationKernel_le_left a b hb
  · rw [min_eq_right hba, binaryDilationKernel_comm]
    exact binaryDilationKernel_le_left b a ha

theorem adjacentBinaryRepair_eq_difference (n k : ℕ) :
    adjacentBinaryRepair n k =
      (n : ℝ)⁻¹ * (binaryDilation (n + 1) k - binaryDilation n k) :=
  arithmeticRepair_eq_dilation 2 n (n + 1) k

theorem adjacentBinaryRepair_head_zero (n k : ℕ) (hk : k < n) :
    adjacentBinaryRepair n k = 0 :=
  arithmeticRepair_head_zero 2 n (n + 1) k (by omega) (by omega) hk

theorem adjacentBinaryRepair_at_anchor (n : ℕ) (hn : 0 < n) :
    adjacentBinaryRepair n n = -1 := by
  rw [adjacentBinaryRepair_eq_difference, binaryDilation_head_zero (n + 1) n (by omega)]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  simp [binaryDilation, dilation, residue, Nat.div_self hn, hn0]

theorem adjacentBinaryRepair_mean_zero (n : ℕ) (hn : 0 < n) :
    paretoMean (adjacentBinaryRepair n) = 0 :=
  arithmeticRepair_mean_zero 2 n (n + 1) (by omega) hn (by omega)

/-- The four mixed terms of the complete covariance are retained. -/
theorem adjacentBinaryRepair_covariance (m n : ℕ) :
    paretoInner (adjacentBinaryRepair m) (adjacentBinaryRepair n) =
      (binaryDilationKernel (m + 1) (n + 1) - binaryDilationKernel (m + 1) n -
        binaryDilationKernel m (n + 1) + binaryDilationKernel m n) /
          ((m : ℝ) * (n : ℝ)) := by
  unfold adjacentBinaryRepair
  rw [arithmeticRepair_eq_scaleRepair, arithmeticRepair_eq_scaleRepair,
    paretoInner_scaleRepair (fun k => residue_abs_le 2 k (by omega))
      (fun k => residue_abs_le 2 k (by omega))]
  simp only [binaryDilationKernel, binaryDilation, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact finite Abel transform for the actual adjacent repairs. The final
dilation anchor cannot be discarded when taking a limit. -/
theorem adjacentBinaryRepair_abel (t : ℕ → ℝ) (M N k : ℕ) (hM : 0 < M) :
    (∑ j ∈ Finset.range (N + 1),
      ((M + j : ℕ) : ℝ) * t (M + j) * adjacentBinaryRepair (M + j) k) =
      -t M * binaryDilation M k +
        (∑ j ∈ Finset.range N,
          (t (M + j) - t (M + j + 1)) * binaryDilation (M + j + 1) k) +
        t (M + N) * binaryDilation (M + N + 1) k := by
  calc
    _ = ∑ j ∈ Finset.range (N + 1),
        t (M + j) * (binaryDilation (M + j + 1) k - binaryDilation (M + j) k) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [adjacentBinaryRepair_eq_difference]
      have hj0 : ((M + j : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hj0]
    _ = _ := Finset.sum_range_weighted_forward_difference
      (fun n => binaryDilation n k) t M N

/-- In particular the all-one coefficients have an exact positive-variation
representation together with their terminal term. -/
theorem adjacentBinaryRepair_sum (M N k : ℕ) (hM : 0 < M) :
    (∑ j ∈ Finset.range (N + 1), adjacentBinaryRepair (M + j) k) =
      -(M : ℝ)⁻¹ * binaryDilation M k +
        (∑ j ∈ Finset.range N,
          (((M + j : ℕ) : ℝ)⁻¹ - ((M + j + 1 : ℕ) : ℝ)⁻¹) *
            binaryDilation (M + j + 1) k) +
        ((M + N : ℕ) : ℝ)⁻¹ * binaryDilation (M + N + 1) k := by
  have h := adjacentBinaryRepair_abel (fun n => (n : ℝ)⁻¹) M N k hM
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  have hj0 : ((M + j : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [mul_inv_cancel₀ hj0, one_mul]

end
end RiemannResearch.RH.Pareto
