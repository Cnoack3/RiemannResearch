import RiemannResearch.Analysis.FiniteStrictTail
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Counting logarithmic tails and reducing symmetric moments

The tail estimate counts positive integers below `n * exp (-t)` by bounding
them by its natural floor.  The symmetry reduction is a finite-sum induction,
independent of the analytic proof of the one-sided moment estimate.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.LogarithmicMatrixMoments

/-- The strict-tail indicator sum is the real cardinality of its filter. -/
theorem tail_eq_card_filter {ι : Type*} (s : Finset ι) (x : ι → ℝ) (t : ℝ) :
    FiniteStrictTail.tail s x t = ((s.filter (fun i => t < x i)).card : ℝ) := by
  classical
  rw [FiniteStrictTail.tail, ← Finset.sum_filter]
  simp

/-- A logarithmic tail contains at most `n * exp (-t)` positive integers.
The bound holds for every real `t`, hence in particular for `0 ≤ t`. -/
theorem log_tail_card_le_exp {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (((Finset.Icc 1 (n - 1)).filter
      (fun m : ℕ => t < Real.log ((n : ℝ) / (m : ℝ)))).card : ℝ) ≤
      (n : ℝ) * Real.exp (-t) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx : 0 ≤ (n : ℝ) * Real.exp (-t) :=
    (mul_pos hnR (Real.exp_pos _)).le
  have hsubset :
      (Finset.Icc 1 (n - 1)).filter
        (fun m : ℕ => t < Real.log ((n : ℝ) / (m : ℝ))) ⊆
      Finset.Icc 1 ⌊(n : ℝ) * Real.exp (-t)⌋₊ := by
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hm, htail⟩
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmR : (0 : ℝ) < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
    have hExp : Real.exp t < (n : ℝ) / (m : ℝ) :=
      (Real.lt_log_iff_exp_lt (div_pos hnR hmR)).mp htail
    have hProduct : Real.exp t * (m : ℝ) < (n : ℝ) :=
      (lt_div_iff₀ hmR).mp hExp
    have hM : (m : ℝ) < (n : ℝ) / Real.exp t :=
      (lt_div_iff₀ (Real.exp_pos t)).mpr (by simpa [mul_comm] using hProduct)
    have hMexp : (m : ℝ) < (n : ℝ) * Real.exp (-t) := by
      simpa only [Real.exp_neg, div_eq_mul_inv] using hM
    exact Finset.mem_Icc.mpr ⟨hm1, Nat.le_floor hMexp.le⟩
  calc
    (((Finset.Icc 1 (n - 1)).filter
        (fun m : ℕ => t < Real.log ((n : ℝ) / (m : ℝ)))).card : ℝ) ≤
        ((Finset.Icc 1 ⌊(n : ℝ) * Real.exp (-t)⌋₊).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ = (⌊(n : ℝ) * Real.exp (-t)⌋₊ : ℝ) := by simp
    _ ≤ (n : ℝ) * Real.exp (-t) := Nat.floor_le hx

/-- Strict-tail form of `log_tail_card_le_exp`, ready for finite layer cake. -/
theorem tail_log_ratio_le_exp {n : ℕ} (hn : 0 < n) (t : ℝ) :
    FiniteStrictTail.tail (Finset.Icc 1 (n - 1))
      (fun m : ℕ => Real.log ((n : ℝ) / (m : ℝ))) t ≤
        (n : ℝ) * Real.exp (-t) := by
  rw [tail_eq_card_filter]
  exact log_tail_card_le_exp hn t

/-- A symmetric kernel with zero diagonal has twice its lower-triangular sum.
This recurrence avoids any reindexing of a product finset. -/
theorem symmetric_square_sum_succ (f : ℕ → ℕ → ℝ)
    (hsymm : ∀ n m, f n m = f m n) (hdiag : ∀ n, f n n = 0) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 (X + 1), ∑ m ∈ Finset.Icc 1 (X + 1), f n m) =
      (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X, f n m) +
        2 * ∑ m ∈ Finset.Icc 1 X, f (X + 1) m := by
  have hX : 1 ≤ X + 1 := Nat.succ_le_succ (Nat.zero_le X)
  have hcol : (∑ n ∈ Finset.Icc 1 X, f n (X + 1)) =
      ∑ m ∈ Finset.Icc 1 X, f (X + 1) m := by
    exact Finset.sum_congr rfl (fun n _ => hsymm n (X + 1))
  calc
    (∑ n ∈ Finset.Icc 1 (X + 1), ∑ m ∈ Finset.Icc 1 (X + 1), f n m) =
        (∑ n ∈ Finset.Icc 1 X,
          ((∑ m ∈ Finset.Icc 1 X, f n m) + f n (X + 1))) +
          ((∑ m ∈ Finset.Icc 1 X, f (X + 1) m) + f (X + 1) (X + 1)) := by
      rw [Finset.sum_Icc_succ_top hX]
      congr 1
      · exact Finset.sum_congr rfl (fun n _ => Finset.sum_Icc_succ_top hX _)
      · exact Finset.sum_Icc_succ_top hX _
    _ = (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X, f n m) +
        2 * ∑ m ∈ Finset.Icc 1 X, f (X + 1) m := by
      rw [Finset.sum_add_distrib, hcol, hdiag]
      ring

/-- A bound `C * n` for each lower-triangular row gives the square bound
`C * X * (X + 1)`.  No sign assumption on `C` or the kernel is needed. -/
theorem symmetric_square_sum_le_of_row_bound (f : ℕ → ℕ → ℝ)
    (hsymm : ∀ n m, f n m = f m n) (hdiag : ∀ n, f n n = 0)
    (C : ℝ)
    (hrow : ∀ n : ℕ, 0 < n →
      (∑ m ∈ Finset.Icc 1 (n - 1), f n m) ≤ C * (n : ℝ)) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X, f n m) ≤
      C * (X : ℝ) * ((X : ℝ) + 1) := by
  induction X with
  | zero => simp
  | succ X ih =>
      have hrowX : (∑ m ∈ Finset.Icc 1 X, f (X + 1) m) ≤
          C * ((X : ℝ) + 1) := by
        simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
          hrow (X + 1) (Nat.succ_pos X)
      calc
        (∑ n ∈ Finset.Icc 1 (X + 1), ∑ m ∈ Finset.Icc 1 (X + 1), f n m) =
            (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X, f n m) +
              2 * ∑ m ∈ Finset.Icc 1 X, f (X + 1) m :=
          symmetric_square_sum_succ f hsymm hdiag X
        _ ≤ C * (X : ℝ) * ((X : ℝ) + 1) + 2 * (C * ((X : ℝ) + 1)) :=
          add_le_add ih (mul_le_mul_of_nonneg_left hrowX (by norm_num))
        _ = C * ((X + 1 : ℕ) : ℝ) * (((X + 1 : ℕ) : ℝ) + 1) := by
          push_cast
          ring

/-- The absolute logarithmic kernel is symmetric even when an input is zero. -/
theorem abs_log_div_symm (a b : ℝ) :
    |Real.log (a / b)| = |Real.log (b / a)| := by
  calc
    |Real.log (a / b)| = |Real.log ((b / a)⁻¹)| := by rw [inv_div]
    _ = |Real.log (b / a)| := by rw [Real.log_inv, abs_neg]

/-- Reduction of all positive absolute logarithmic moments to the one-sided
factorial row bound.  In particular it applies to every positive even exponent. -/
theorem double_abs_log_moment_le_of_one_sided {k : ℕ} (hk : 0 < k)
    (hrow : ∀ n : ℕ, 0 < n →
      (∑ m ∈ Finset.Icc 1 (n - 1),
        (Real.log ((n : ℝ) / (m : ℝ))) ^ k) ≤
          (Nat.factorial k : ℝ) * (n : ℝ)) (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
      |Real.log ((n : ℝ) / (m : ℝ))| ^ k) ≤
        (Nat.factorial k : ℝ) * (X : ℝ) * ((X : ℝ) + 1) := by
  apply symmetric_square_sum_le_of_row_bound
    (fun n m => |Real.log ((n : ℝ) / (m : ℝ))| ^ k)
    (fun n m => congrArg (fun x : ℝ => x ^ k) (abs_log_div_symm _ _))
    (fun n => by simp [Nat.ne_of_gt hk]) (Nat.factorial k : ℝ) ?_ X
  intro n hn
  calc
    (∑ m ∈ Finset.Icc 1 (n - 1),
        |Real.log ((n : ℝ) / (m : ℝ))| ^ k) =
        ∑ m ∈ Finset.Icc 1 (n - 1),
          (Real.log ((n : ℝ) / (m : ℝ))) ^ k := by
      apply Finset.sum_congr rfl
      intro m hm
      rcases Finset.mem_Icc.mp hm with ⟨hm1, hmn⟩
      have hmR : (0 : ℝ) < (m : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
      have hmnR : (m : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans hmn (Nat.sub_le n 1))
      have hratio : 1 ≤ (n : ℝ) / (m : ℝ) :=
        (le_div_iff₀ hmR).mpr (by simpa using hmnR)
      rw [abs_of_nonneg (Real.log_nonneg hratio)]
    _ ≤ (Nat.factorial k : ℝ) * (n : ℝ) := hrow n hn

end RiemannResearch.Analysis.LogarithmicMatrixMoments
