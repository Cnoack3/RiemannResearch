/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.PSeriesTail
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Dirichlet coefficient tails from a linear second-moment bound

Finite Abel summation retains the terminal prefix and all first differences.
Applied to nonnegative coefficients with linear partial sums it gives the
cutoff factor and explicit exponent constant needed in the sharp moving
right-line mean square. For the arithmetic input on truncated Möbius divisor
coefficients see de la Bretèche, Dress and Tenenbaum, Mathematika 66 (2020),
416–421, equation (1.5), DOI 10.1112/mtk.12021.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.DirichletMeanSquare

/-- Abel summation with the last weighted prefix visible. -/
theorem coefficient_prefix_abel_identity (a w : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, a k * w k) =
      (∑ i ∈ Finset.range N, a i) * w N +
        ∑ k ∈ Finset.range N,
          (∑ i ∈ Finset.range (k + 1), a i) * (w k - w (k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rw [Finset.sum_range_succ (f := fun k =>
      (∑ i ∈ Finset.range (k + 1), a i) * (w k - w (k + 1)))]
    rw [Finset.sum_range_succ (f := a)]
    ring

private theorem linear_prefix_abel_identity (w : ℕ → ℝ) (C A : ℝ) (N : ℕ) :
    C * (A + N) * w N +
      (∑ k ∈ Finset.range N, C * (A + (k + 1 : ℕ)) * (w k - w (k + 1))) =
        C * A * w 0 + C * ∑ k ∈ Finset.range N, w k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ (f := w)]
    push_cast at *
    linarith only [ih]

/-- A cutoff term and the ordinary weight sum control all finite weighted prefixes. -/
theorem coefficient_prefix_weighted_le (a w : ℕ → ℝ) (C A : ℝ)
    (hprefix : ∀ n : ℕ, (∑ i ∈ Finset.range n, a i) ≤ C * (A + n))
    (hw : ∀ n, 0 ≤ w n) (hdec : Antitone w) (N : ℕ) :
    (∑ k ∈ Finset.range N, a k * w k) ≤ C * A * w 0 + C * ∑ k ∈ Finset.range N, w k := by
  rw [coefficient_prefix_abel_identity, ← linear_prefix_abel_identity]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (hprefix N) (hw N)
  · apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_right (hprefix (k + 1)) (sub_nonneg.mpr (hdec (Nat.le_succ k)))

/-- A linear bound for cumulative mass gives a summable Dirichlet tail and
its explicit sharp integral-test constant. The cutoff is at the last removed index. -/
theorem coefficient_rpow_tail_of_linear_prefix {b : ℕ → ℝ} {C p : ℝ} {X : ℕ}
    (hb : ∀ n, 0 ≤ b n) (hC : 0 ≤ C) (hX : 1 ≤ X) (hp : 1 < p)
    (hprefix : ∀ n : ℕ, (∑ i ∈ Finset.range (n + 1), b i) ≤ C * n) :
    Summable (fun k : ℕ => b (k + X + 1) * ((k + X + 1 : ℕ) : ℝ) ^ (-p)) ∧
      (∑' k : ℕ, b (k + X + 1) * ((k + X + 1 : ℕ) : ℝ) ^ (-p)) ≤
        C * p / (p - 1) * (X : ℝ) ^ (1 - p) := by
  let a : ℕ → ℝ := fun k => b (k + X + 1)
  let w : ℕ → ℝ := fun k => ((k + X + 1 : ℕ) : ℝ) ^ (-p)
  have hx : 0 < (X : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hw : ∀ k, 0 ≤ w k := fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hdec : Antitone w := by
    intro i j hij
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast (show i + X + 1 ≤ j + X + 1 by omega)) (by linarith)
  have hmass (n : ℕ) : ∑ i ∈ Finset.range n, a i ≤ C * ((X : ℝ) + n) := by
    have h := hprefix (X + n)
    rw [show X + n + 1 = X + 1 + n by omega, Finset.sum_range_add] at h
    have h0 : 0 ≤ ∑ i ∈ Finset.range (X + 1), b i :=
      Finset.sum_nonneg (fun i _ => hb i)
    have heq : (∑ i ∈ Finset.range n, b (X + 1 + i)) = ∑ i ∈ Finset.range n, a i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [a, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    rw [heq, Nat.cast_add] at h
    linarith
  have hsum : Summable w := by
    simpa only [w, Nat.add_assoc] using (summable_nat_add_iff (X + 1)).mpr
      (Real.summable_nat_rpow.mpr (by linarith : -p < -1))
  have hterm : ∀ n, 0 ≤ a n * w n := fun n => mul_nonneg (hb _) (hw n)
  have hfirst : (X : ℝ) * w 0 ≤ (X : ℝ) ^ (1 - p) := by
    have hmono : w 0 ≤ (X : ℝ) ^ (-p) := by
      apply Real.rpow_le_rpow_of_nonpos hx _ (by linarith)
      exact_mod_cast (show X ≤ 0 + X + 1 by omega)
    calc
      _ ≤ (X : ℝ) * (X : ℝ) ^ (-p) := mul_le_mul_of_nonneg_left hmono hx.le
      _ = (X : ℝ) ^ (1 - p) := by
        rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  have htail : (∑' n : ℕ, w n) ≤ (X : ℝ) ^ (1 - p) / (p - 1) :=
    Real.tsum_nat_rpow_tail_le hp hX
  have hbound (N : ℕ) : (∑ k ∈ Finset.range N, a k * w k) ≤
      C * p / (p - 1) * (X : ℝ) ^ (1 - p) := by
    calc
      _ ≤ C * X * w 0 + C * ∑ k ∈ Finset.range N, w k :=
        coefficient_prefix_weighted_le a w C X hmass hw hdec N
      _ ≤ C * (X : ℝ) ^ (1 - p) + C * ((X : ℝ) ^ (1 - p) / (p - 1)) := by
        rw [mul_assoc C]
        exact add_le_add (mul_le_mul_of_nonneg_left hfirst hC)
          (mul_le_mul_of_nonneg_left ((hsum.sum_le_tsum _ (fun n _ => hw n)).trans htail) hC)
      _ = _ := by
        field_simp [ne_of_gt (sub_pos.mpr hp)]
        <;> ring
  exact ⟨summable_of_sum_range_le hterm hbound, Real.tsum_le_of_sum_range_le hterm hbound⟩

end RiemannResearch.Analysis.DirichletMeanSquare
