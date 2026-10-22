import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Exact Gram coupling of finite jump rows

For the Pareto weight `1 / (n * (n+1))`, the Riesz Gram form of consecutive
differences is an exact diagonal term minus the two adjacent-jump terms.  The
finite boundary contribution is retained explicitly before support assumptions
remove it.  This gives the general algebra behind the component network.
-/

namespace RiemannResearch.RH.ComponentJumpGram

open scoped BigOperators

def gram (b c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ((n : ℝ) + 1) *
    (b n - b (n + 1)) * (c n - c (n + 1))

/-- Exact finite summation by parts, including its upper boundary. -/
theorem gram_exact_boundary (b c : ℕ → ℝ) (N : ℕ) :
    gram b c N =
      2 * (∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ 2 * b n * c n) -
      (∑ n ∈ Finset.range (N + 1), (n : ℝ) * ((n : ℝ) + 1) *
        (b n * c (n + 1) + b (n + 1) * c n)) +
      (N : ℝ) * ((N : ℝ) + 1) * b (N + 1) * c (N + 1) := by
  unfold gram
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ _ (N + 1),
      Finset.sum_range_succ (fun n => (n : ℝ) ^ 2 * b n * c n) (N + 1),
      Finset.sum_range_succ
        (fun n => (n : ℝ) * ((n : ℝ) + 1) *
          (b n * c (n + 1) + b (n + 1) * c n)) (N + 1), ih]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem gram_exact (b c : ℕ → ℝ) (N : ℕ)
    (hboundary : b (N + 1) * c (N + 1) = 0) :
    gram b c N =
      2 * (∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ 2 * b n * c n) -
      (∑ n ∈ Finset.range (N + 1), (n : ℝ) * ((n : ℝ) + 1) *
        (b n * c (n + 1) + b (n + 1) * c n)) := by
  rw [gram_exact_boundary]
  have he : (N : ℝ) * ((N : ℝ) + 1) * b (N + 1) * c (N + 1) = 0 := by
    nlinarith [congrArg (fun x : ℝ => (N : ℝ) * ((N : ℝ) + 1) * x) hboundary]
  rw [he, add_zero]

/-- Disjoint jump supports leave exactly the signed adjacency terms. -/
theorem gram_disjoint_exact (b c : ℕ → ℝ) (N : ℕ)
    (hdisjoint : ∀ n ≤ N + 1, b n * c n = 0) :
    gram b c N =
      -(∑ n ∈ Finset.range (N + 1), (n : ℝ) * ((n : ℝ) + 1) *
        (b n * c (n + 1) + b (n + 1) * c n)) := by
  rw [gram_exact b c N (hdisjoint (N + 1) le_rfl)]
  have hd : (∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ 2 * b n * c n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have h := hdisjoint n (Nat.le_of_lt (Finset.mem_range.mp hn))
    nlinarith [congrArg (fun x : ℝ => (n : ℝ) ^ 2 * x) h]
  rw [hd]
  ring

theorem gram_disjoint_nonpos (b c : ℕ → ℝ) (N : ℕ)
    (hdisjoint : ∀ n ≤ N + 1, b n * c n = 0)
    (hb : ∀ n ≤ N + 1, 0 ≤ b n) (hc : ∀ n ≤ N + 1, 0 ≤ c n) :
    gram b c N ≤ 0 := by
  rw [gram_disjoint_exact b c N hdisjoint]
  apply neg_nonpos.mpr
  apply Finset.sum_nonneg
  intro n hn
  have hn' : n + 1 ≤ N + 1 := by exact Finset.mem_range.mp hn
  have hn0 : n ≤ N + 1 := (Nat.le_succ n).trans hn'
  have hbn := hb n hn0
  have hbn1 := hb (n + 1) hn'
  have hcn := hc n hn0
  have hcn1 := hc (n + 1) hn'
  positivity

/-- The positive diagonal bound is taken only after the exact adjacency identity. -/
theorem gram_self_le (b : ℕ → ℝ) (N : ℕ) (hboundary : b (N + 1) = 0)
    (hb : ∀ n ≤ N + 1, 0 ≤ b n) :
    gram b b N ≤ 2 * ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ 2 * (b n) ^ 2 := by
  rw [gram_exact b b N (by rw [hboundary]; ring)]
  have hdiag : (∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ 2 * b n * b n) =
      ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ 2 * (b n) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hdiag]
  have hpos : 0 ≤ ∑ n ∈ Finset.range (N + 1), (n : ℝ) * ((n : ℝ) + 1) *
      (b n * b (n + 1) + b (n + 1) * b n) := by
    apply Finset.sum_nonneg
    intro n hn
    have hn' : n + 1 ≤ N + 1 := by exact Finset.mem_range.mp hn
    have hn0 : n ≤ N + 1 := (Nat.le_succ n).trans hn'
    have hbn := hb n hn0
    have hbn1 := hb (n + 1) hn'
    positivity
  linarith

end RiemannResearch.RH.ComponentJumpGram
