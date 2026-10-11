import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Abel bounds from bounds on cumulative sums

Source: user-provided quotient norm proof, September 10, 2026, N28--N29.
This proves the Abel summation step. It does not assume or prove the
number-theoretic bound on the logarithmic orbit used in that application.
-/

namespace RiemannResearch.Analysis
open scoped BigOperators Topology
open Filter

def prefixSum (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, a n

def geometricPrefix (r : ℝ) (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, r ^ n * a n

@[simp] theorem prefixSum_succ (a : ℕ → ℝ) (N : ℕ) :
    prefixSum a (N + 1) = prefixSum a N + a N := by
  simp [prefixSum, Finset.sum_range_succ]

/-- Finite summation by parts for any real ratio and signed sequence, retaining
the terminal correction `r^N * prefixSum a N`. -/
theorem geometricPrefix_eq (r : ℝ) (a : ℕ → ℝ) (N : ℕ) :
    geometricPrefix r a N =
      (1-r) * (∑ n ∈ Finset.range N, r^n * prefixSum a (n+1)) +
        r^N * prefixSum a N := by
  induction N with
  | zero => simp [geometricPrefix, prefixSum]
  | succ N ih =>
    rw [geometricPrefix, Finset.sum_range_succ]
    change geometricPrefix r a N + r^N * a N = _
    rw [ih, Finset.sum_range_succ, prefixSum_succ, pow_succ]
    ring

/-- Decreasing geometric weights preserve the ordering of all prefix sums. -/
theorem geometricPrefix_mono_of_prefix (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (a b : ℕ → ℝ) (N : ℕ)
    (h : ∀ n ≤ N, prefixSum a n ≤ prefixSum b n) :
    geometricPrefix r a N ≤ geometricPrefix r b N := by
  rw [geometricPrefix_eq, geometricPrefix_eq]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hr1)
    apply Finset.sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 n)
    exact h (n+1) (Nat.succ_le_of_lt (Finset.mem_range.mp hn))
  · exact mul_le_mul_of_nonneg_left (h N le_rfl) (pow_nonneg hr0 N)

theorem one_sub_mul_geometricPrefix_one (r : ℝ) (N : ℕ) :
    (1-r) * geometricPrefix r (fun _ => 1) N = 1-r^N := by
  induction N with
  | zero => simp [geometricPrefix]
  | succ N ih =>
    simp only [geometricPrefix, Finset.sum_range_succ, mul_one] at ih ⊢
    rw [mul_add, ih, pow_succ]
    ring

/-- A linear upper bound on cumulative sums gives a uniform finite Abel bound. -/
theorem normalized_geometricPrefix_le (r C : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hC : 0 ≤ C) (a : ℕ → ℝ) (N : ℕ)
    (h : ∀ n ≤ N, prefixSum a n ≤ C * n) :
    (1-r) * geometricPrefix r a N ≤ C := by
  have hp : geometricPrefix r a N ≤ geometricPrefix r (fun _ => C) N := by
    apply geometricPrefix_mono_of_prefix r hr0 hr1 a (fun _ => C) N
    intro n hn
    simpa [prefixSum, mul_comm] using h n hn
  have hc : geometricPrefix r (fun _ => C) N =
      C * geometricPrefix r (fun _ => 1) N := by
    simp [geometricPrefix, Finset.mul_sum, mul_comm]
  calc
    (1-r) * geometricPrefix r a N ≤
        (1-r) * geometricPrefix r (fun _ => C) N :=
      mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hr1)
    _ = C * (1-r^N) := by rw [hc, ← mul_assoc, mul_comm (1-r) C,
        mul_assoc, one_sub_mul_geometricPrefix_one]
    _ ≤ C := by nlinarith [pow_nonneg hr0 N]

/-- Infinite Abel bound. Summability is explicit, not inferred from a one-sided
prefix bound for an arbitrary signed sequence. -/
theorem normalized_geometric_tsum_le (r C : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hC : 0 ≤ C) (a : ℕ → ℝ)
    (hs : Summable (fun n => r^n * a n))
    (h : ∀ n, prefixSum a n ≤ C * n) :
    (1-r) * (∑' n, r^n * a n) ≤ C := by
  apply le_of_tendsto (hs.hasSum.tendsto_sum_nat.const_mul (1-r))
  exact Filter.Eventually.of_forall (fun N =>
    normalized_geometricPrefix_le r C hr0 hr1 hC a N (fun n _ => h n))

/-- For a nonnegative sequence, the prefix hypothesis also proves summability. -/
theorem summable_geometric_of_nonneg_prefix_le (r C : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hC : 0 ≤ C) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (h : ∀ n, prefixSum a n ≤ C * n) :
    Summable (fun n => r^n * a n) := by
  apply summable_of_sum_range_le (fun n => mul_nonneg (pow_nonneg hr0 n) (ha n))
    (c := C / (1-r))
  intro N
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  simpa only [geometricPrefix, mul_comm] using
    normalized_geometricPrefix_le r C hr0 hr1.le hC a N (fun n _ => h n)

/-- The exact positive-sequence Abel estimate needed after the logarithmic
orbit counting lemma. No separate convergence assumption is needed. -/
theorem normalized_geometric_tsum_le_of_nonneg (r C : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hC : 0 ≤ C) (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (h : ∀ n, prefixSum a n ≤ C * n) :
    (1-r) * (∑' n, r^n * a n) ≤ C :=
  normalized_geometric_tsum_le r C hr0 hr1.le hC a
    (summable_geometric_of_nonneg_prefix_le r C hr0 hr1 hC a ha h) h

end RiemannResearch.Analysis
