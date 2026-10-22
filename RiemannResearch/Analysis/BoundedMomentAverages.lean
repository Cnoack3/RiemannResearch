import RiemannResearch.Analysis.BoundedMomentRepair
import Mathlib.Tactic.FieldSimp

/-!
# Equal-weight averages and complete mixed-term control

Source: user-provided bounded-moment averaging argument, September 11, 2026.
The exact finite Gram expansion retains every signed pairing. A total
upper-triangular pairing bound of two gives the stated B/m + 4/m² estimate.
A weakly null family permits successive selection with geometrically small
pairings against each previously selected partial sum; no independence is used.
-/

open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The sum of all signed off-diagonal pairings, with each pair counted once. -/
def prefixCross (u : ℕ → E) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, inner ℝ (∑ i ∈ Finset.range j, u i) (u j)

/-- Exact finite Gram expansion, including all signed mixed terms. -/
theorem norm_sq_sum_range_eq_diagonal_add_cross (u : ℕ → E) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, u i‖ ^ 2 =
      (∑ i ∈ Finset.range n, ‖u i‖ ^ 2) + 2 * prefixCross u n := by
  have hadd (x y : E) :
      ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + 2 * inner ℝ x y := by
    simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right]
    rw [real_inner_comm y x]
    ring
  induction n with
  | zero => simp [prefixCross]
  | succ n ih =>
      simp only [Finset.sum_range_succ, hadd, prefixCross] at *
      linarith

/-- Equal-weight averages have the page's exact quantitative upper bound
whenever the complete signed upper-triangular pairing sum is at most two. -/
theorem norm_sq_average_le_of_prefixCross
    (u : ℕ → E) {B : ℝ} (hbound : ∀ n, ‖u n‖ ^ 2 ≤ B)
    {m : ℕ} (hm : 0 < m) (hcross : prefixCross u m ≤ 2) :
    ‖((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, u i)‖ ^ 2 ≤
      B / m + 4 / (m : ℝ) ^ 2 := by
  have hdiag : (∑ i ∈ Finset.range m, ‖u i‖ ^ 2) ≤ (m : ℝ) * B := by
    calc
      _ ≤ ∑ _i ∈ Finset.range m, B := Finset.sum_le_sum (fun i _ => hbound i)
      _ = _ := by simp
  have hsum : ‖∑ i ∈ Finset.range m, u i‖ ^ 2 ≤ (m : ℝ) * B + 4 := by
    rw [norm_sq_sum_range_eq_diagonal_add_cross]
    linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have he : ((m : ℝ)⁻¹) ^ 2 * ((m : ℝ) * B + 4) =
      B / m + 4 / (m : ℝ) ^ 2 := by
    field_simp [ne_of_gt hm']
    <;> ring
  calc
    _ = ((m : ℝ)⁻¹) ^ 2 * ‖∑ i ∈ Finset.range m, u i‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    _ ≤ ((m : ℝ)⁻¹) ^ 2 * ((m : ℝ) * B + 4) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := he

/-- Geometrically small pairing with each preceding partial sum bounds the
sum of every signed off-diagonal term. -/
theorem prefixCross_le_two_of_geometric
    (u : ℕ → E)
    (hcross : ∀ j, |inner ℝ (∑ i ∈ Finset.range j, u i) (u j)| ≤
      (1 / 2 : ℝ) ^ j) (n : ℕ) :
    prefixCross u n ≤ 2 := by
  have hgeom (n : ℕ) :
      (∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j) =
        2 * (1 - (1 / 2 : ℝ) ^ n) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  calc
    prefixCross u n ≤ ∑ j ∈ Finset.range n, (1 / 2 : ℝ) ^ j := by
      exact Finset.sum_le_sum (fun j _ => (le_abs_self _).trans (hcross j))
    _ = 2 * (1 - (1 / 2 : ℝ) ^ n) := hgeom n
    _ ≤ 2 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]

/-- Full equal-weight energy estimate, derived from signed pairings rather than
an independence assumption. -/
theorem norm_sq_average_le_of_geometric_cross
    (u : ℕ → E) {B : ℝ} (hbound : ∀ n, ‖u n‖ ^ 2 ≤ B)
    (hcross : ∀ j, |inner ℝ (∑ i ∈ Finset.range j, u i) (u j)| ≤
      (1 / 2 : ℝ) ^ j) {m : ℕ} (hm : 0 < m) :
    ‖((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, u i)‖ ^ 2 ≤
      B / m + 4 / (m : ℝ) ^ 2 :=
  norm_sq_average_le_of_prefixCross u hbound hm
    (prefixCross_le_two_of_geometric u hcross m)

/-- Weak nullity supplies arbitrarily late indices with prescribed positive
pairing tolerance against any fixed vector, including a selected partial sum. -/
theorem exists_late_small_pairing
    (u : ℕ → E)
    (hweak : ∀ x, Tendsto (fun n => inner ℝ x (u n)) atTop (𝓝 0))
    (x : E) (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, N ≤ n ∧ |inner ℝ x (u n)| ≤ ε := by
  have he := (hweak x).eventually (Metric.ball_mem_nhds (0 : ℝ) hε)
  obtain ⟨n, hn, he'⟩ := ((eventually_ge_atTop N).and he).exists
  refine ⟨n, hn, le_of_lt ?_⟩
  simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using he'

/-- Select a strictly increasing subsequence with a geometric bound on every
new pairing against its preceding selected sum. This is the constructive
selection step behind the equal-weight averaging estimate. -/
theorem exists_strictMono_geometric_pairing_subsequence
    (u : ℕ → E)
    (hweak : ∀ x, Tendsto (fun n => inner ℝ x (u n)) atTop (𝓝 0)) :
    ∃ q : ℕ → ℕ, StrictMono q ∧
      ∀ j, |inner ℝ (∑ i ∈ Finset.range j, u (q i)) (u (q j))| ≤
        (1 / 2 : ℝ) ^ j := by
  classical
  have hnextExists : ∀ (N j : ℕ) (x : E),
      ∃ n, N ≤ n ∧ |inner ℝ x (u n)| ≤ (1 / 2 : ℝ) ^ j := by
    intro N j x
    exact exists_late_small_pairing u hweak x N (by positivity)
  choose next hnext using hnextExists
  let state : ℕ → ℕ × E := fun n =>
    Nat.rec (0, 0) (fun j s =>
      (next s.1 j s.2 + 1, s.2 + u (next s.1 j s.2))) n
  let q : ℕ → ℕ := fun j => next (state j).1 j (state j).2
  have hs (j : ℕ) :
      state (j + 1) = (q j + 1, (state j).2 + u (q j)) := rfl
  have hsum (j : ℕ) :
      (∑ i ∈ Finset.range j, u (q i)) = (state j).2 := by
    induction j with
    | zero => simp [state]
    | succ j ih => rw [Finset.sum_range_succ, ih, hs]
  refine ⟨q, ?_, ?_⟩
  · apply strictMono_nat_of_lt_succ
    intro j
    have hl := (hnext (state (j + 1)).1 (j + 1) (state (j + 1)).2).1
    change (state (j + 1)).1 ≤ q (j + 1) at hl
    rw [hs] at hl
    exact lt_of_lt_of_le (Nat.lt_succ_self (q j)) hl
  · intro j
    rw [hsum]
    exact (hnext (state j).1 j (state j).2).2

/-- A bounded weakly null sequence has a subsequence whose equal-weight finite
averages satisfy B/m + 4/m² at every positive averaging length. -/
theorem exists_strictMono_average_norm_sq_bound
    (u : ℕ → E) {B : ℝ} (hbound : ∀ n, ‖u n‖ ^ 2 ≤ B)
    (hweak : ∀ x, Tendsto (fun n => inner ℝ x (u n)) atTop (𝓝 0)) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ ∀ m : ℕ, 0 < m →
      ‖((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, u (q i))‖ ^ 2 ≤
        B / m + 4 / (m : ℝ) ^ 2 := by
  obtain ⟨q, hq, hcross⟩ := exists_strictMono_geometric_pairing_subsequence u hweak
  refine ⟨q, hq, fun m hm => ?_⟩
  exact norm_sq_average_le_of_geometric_cross (fun j => u (q j))
    (fun j => hbound (q j)) hcross hm

end RiemannResearch.Analysis
