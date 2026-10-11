/- Unconditional finite lag phase estimates.  The exact boundary identity and
metric consequences follow the corrected prime-phase note (2026-10-11),
Section 6.  No analytic zero-distribution or Riemann Hypothesis premise occurs.
The quotient metric estimate uses Mathlib's norm-contractivity theorem for the
canonical quotient map. -/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators
open Filter

namespace RiemannResearch.Analysis.LagPhase

/-- Exact boundary cancellation; no ordering or zeta assumptions are required. -/
theorem sum_step_gap (eta : ℕ → ℝ) (count lag : ℕ) :
    (∑ j ∈ Finset.range count, (eta (j + lag + 1) - eta (j + lag))) =
      eta (count + lag) - eta lag := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.succ_add, Nat.add_succ]
    ring

/-- A sum of fixed-lag gaps consists exactly of the last `lag` values minus the
first `lag` values, including the overlap case `count < lag`. -/
theorem sum_lag_gap_eq_boundary (eta : ℕ → ℝ) (count lag : ℕ) :
    (∑ j ∈ Finset.range count, (eta (j + lag) - eta j)) =
      ∑ k ∈ Finset.range lag, (eta (count + k) - eta k) := by
  induction lag with
  | zero => simp
  | succ lag ih =>
    calc
      (∑ j ∈ Finset.range count, (eta (j + (lag + 1)) - eta j)) =
          (∑ j ∈ Finset.range count, (eta (j + lag) - eta j)) +
          (∑ j ∈ Finset.range count,
            (eta (j + lag + 1) - eta (j + lag))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Nat.add_assoc]
        ring
      _ = (∑ k ∈ Finset.range lag, (eta (count + k) - eta k)) +
          (eta (count + lag) - eta lag) := by
        rw [ih, sum_step_gap]
      _ = ∑ k ∈ Finset.range (lag + 1), (eta (count + k) - eta k) := by
        rw [Finset.sum_range_succ]

/-- The endpoint-width bound needs only boundary bounds, not monotonicity. -/
theorem sum_lag_gap_le (eta : ℕ → ℝ) (count lag : ℕ) (a b : ℝ)
    (hlo : ∀ k < lag, a ≤ eta k)
    (hhi : ∀ k < lag, eta (count + k) ≤ b) :
    (∑ j ∈ Finset.range count, (eta (j + lag) - eta j)) ≤
      (lag : ℝ) * (b - a) := by
  rw [sum_lag_gap_eq_boundary]
  calc
    (∑ k ∈ Finset.range lag, (eta (count + k) - eta k)) ≤
        ∑ k ∈ Finset.range lag, (b - a) := by
      apply Finset.sum_le_sum
      intro k hk
      exact sub_le_sub (hhi k (Finset.mem_range.mp hk))
        (hlo k (Finset.mem_range.mp hk))
    _ = (lag : ℝ) * (b - a) := by simp; ring

variable {X : Type*} [PseudoMetricSpace X]

/-- Every Lipschitz phase map inherits the lag-width estimate.  The hypothesis
is written directly as a metric estimate to allow quotient and product tori. -/
theorem sum_lag_phase_dist_le (eta : ℕ → ℝ) (phase : ℝ → X)
    (count lag : ℕ) (a b L : ℝ) (hL : 0 ≤ L)
    (hmono : Monotone eta)
    (hphase : ∀ s t : ℝ, dist (phase s) (phase t) ≤ L * |s - t|)
    (hlo : ∀ k < lag, a ≤ eta k)
    (hhi : ∀ k < lag, eta (count + k) ≤ b) :
    (∑ j ∈ Finset.range count,
      dist (phase (eta (j + lag))) (phase (eta j))) ≤
      L * (lag : ℝ) * (b - a) := by
  have hgap : ∀ j, 0 ≤ eta (j + lag) - eta j := by
    intro j
    exact sub_nonneg.mpr (hmono (Nat.le_add_right j lag))
  calc
    (∑ j ∈ Finset.range count,
        dist (phase (eta (j + lag))) (phase (eta j))) ≤
        ∑ j ∈ Finset.range count, L * (eta (j + lag) - eta j) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [abs_of_nonneg (hgap j)] using
        hphase (eta (j + lag)) (eta j)
    _ = L * (∑ j ∈ Finset.range count, (eta (j + lag) - eta j)) := by
      rw [Finset.mul_sum]
    _ ≤ L * ((lag : ℝ) * (b - a)) :=
      mul_le_mul_of_nonneg_left (sum_lag_gap_le eta count lag a b hlo hhi) hL
    _ = L * (lag : ℝ) * (b - a) := by ring

/-- Normalized version; meaningful for positive `count`, and also true when
`count = 0` under Lean's usual division convention. -/
theorem mean_lag_phase_dist_le (eta : ℕ → ℝ) (phase : ℝ → X)
    (count lag : ℕ) (a b L : ℝ) (hL : 0 ≤ L)
    (hmono : Monotone eta)
    (hphase : ∀ s t : ℝ, dist (phase s) (phase t) ≤ L * |s - t|)
    (hlo : ∀ k < lag, a ≤ eta k)
    (hhi : ∀ k < lag, eta (count + k) ≤ b) :
    (∑ j ∈ Finset.range count,
      dist (phase (eta (j + lag))) (phase (eta j))) / (count : ℝ) ≤
      L * ((lag : ℝ) * (b - a) / (count : ℝ)) := by
  have h := div_le_div_of_nonneg_right
    (sum_lag_phase_dist_le eta phase count lag a b L hL hmono hphase hlo hhi)
    (Nat.cast_nonneg count : (0 : ℝ) ≤ (count : ℝ))
  simpa only [mul_div_assoc, mul_assoc] using h

/-- Growing lags collapse whenever their width-to-sample ratio tends to zero.
For a zero window of width `T` and size comparable to `T * log T`, this allows
`lag = o(log T)` rather than only fixed lags. -/
theorem mean_lag_phase_dist_tendsto_zero
    (eta : ℕ → ℕ → ℝ) (phase : ℝ → X)
    (count lag : ℕ → ℕ) (a b : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hmono : ∀ n, Monotone (eta n))
    (hphase : ∀ s t : ℝ, dist (phase s) (phase t) ≤ L * |s - t|)
    (hlo : ∀ n k, k < lag n → a n ≤ eta n k)
    (hhi : ∀ n k, k < lag n → eta n (count n + k) ≤ b n)
    (hratio : Tendsto
      (fun n => (lag n : ℝ) * (b n - a n) / (count n : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun n => (∑ j ∈ Finset.range (count n),
      dist (phase (eta n (j + lag n))) (phase (eta n j))) / (count n : ℝ))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg (Finset.sum_nonneg fun j hj => dist_nonneg)
      (Nat.cast_nonneg (count n))
  · intro n
    exact mean_lag_phase_dist_le (eta n) phase (count n) (lag n)
      (a n) (b n) L hL (hmono n) hphase (hlo n) (hhi n)
  · simpa using tendsto_const_nhds.mul hratio

/-- The quotient map from the real line to an additive circle is contractive.
This proves the phase estimate itself rather than assuming it.  The period may
be any real number; zero period simply gives the original real line. -/
theorem scaled_addCircle_dist_le (period omega s t : ℝ) :
    dist ((omega * s : ℝ) : AddCircle period)
      ((omega * t : ℝ) : AddCircle period) ≤ |omega| * |s - t| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  calc
    ‖((omega * s - omega * t : ℝ) : AddCircle period)‖ ≤
        ‖omega * s - omega * t‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |omega| * |s - t| := by rw [← mul_sub, Real.norm_eq_abs, abs_mul]

theorem mean_lag_addCircle_dist_le (eta : ℕ → ℝ)
    (count lag : ℕ) (a b period omega : ℝ)
    (hmono : Monotone eta)
    (hlo : ∀ k < lag, a ≤ eta k)
    (hhi : ∀ k < lag, eta (count + k) ≤ b) :
    (∑ j ∈ Finset.range count,
      dist ((omega * eta (j + lag) : ℝ) : AddCircle period)
        ((omega * eta j : ℝ) : AddCircle period)) / (count : ℝ) ≤
      |omega| * ((lag : ℝ) * (b - a) / (count : ℝ)) :=
  mean_lag_phase_dist_le eta
    (fun t => ((omega * t : ℝ) : AddCircle period))
    count lag a b |omega| (abs_nonneg omega) hmono
    (scaled_addCircle_dist_le period omega) hlo hhi

/-- Frequencies and lags may both grow.  Only the explicit product budget is
required; this is independent of uniform Fourier asymptotics for zeta zeros. -/
theorem mean_lag_addCircle_dist_tendsto_zero
    (eta : ℕ → ℕ → ℝ) (count lag : ℕ → ℕ)
    (a b omega : ℕ → ℝ) (period : ℝ)
    (hmono : ∀ n, Monotone (eta n))
    (hlo : ∀ n k, k < lag n → a n ≤ eta n k)
    (hhi : ∀ n k, k < lag n → eta n (count n + k) ≤ b n)
    (hbudget : Tendsto (fun n =>
      |omega n| * ((lag n : ℝ) * (b n - a n) / (count n : ℝ)))
      atTop (nhds 0)) :
    Tendsto (fun n => (∑ j ∈ Finset.range (count n),
      dist ((omega n * eta n (j + lag n) : ℝ) : AddCircle period)
        ((omega n * eta n j : ℝ) : AddCircle period)) / (count n : ℝ))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact div_nonneg (Finset.sum_nonneg fun j hj => dist_nonneg)
      (Nat.cast_nonneg (count n))
  · intro n
    exact mean_lag_addCircle_dist_le (eta n) (count n) (lag n)
      (a n) (b n) period (omega n) (hmono n) (hlo n) (hhi n)
  · exact hbudget

/-- Exact finite diagonal-test comparison with the lag-width error retained. -/
theorem mean_lag_test_sub_diagonal_norm_le (eta : ℕ → ℝ) (phase : ℝ → X)
    (F : X → X → ℂ) (count lag : ℕ) (a b K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hmono : Monotone eta)
    (hphase : ∀ s t : ℝ, dist (phase s) (phase t) ≤ L * |s - t|)
    (hF : ∀ x y, ‖F x y - F x x‖ ≤ K * dist y x)
    (hlo : ∀ k < lag, a ≤ eta k) (hhi : ∀ k < lag, eta (count + k) ≤ b) :
    ‖(∑ j ∈ Finset.range count, F (phase (eta j)) (phase (eta (j + lag)))) /
        (count : ℂ) - (∑ j ∈ Finset.range count, F (phase (eta j)) (phase (eta j))) /
        (count : ℂ)‖ ≤ K * L * ((lag : ℝ) * (b - a) / (count : ℝ)) := by
  rw [← sub_div, ← Finset.sum_sub_distrib]
  have hsum : ‖∑ j ∈ Finset.range count,
      (F (phase (eta j)) (phase (eta (j + lag))) - F (phase (eta j)) (phase (eta j)))‖ ≤
      K * (L * (lag : ℝ) * (b - a)) := by
    calc
      _ ≤ ∑ j ∈ Finset.range count,
          ‖F (phase (eta j)) (phase (eta (j + lag))) - F (phase (eta j)) (phase (eta j))‖ :=
        norm_sum_le _ _
      _ ≤ K * (∑ j ∈ Finset.range count,
          dist (phase (eta (j + lag))) (phase (eta j))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j hj => hF (phase (eta j)) (phase (eta (j + lag)))
      _ ≤ K * (L * (lag : ℝ) * (b - a)) := mul_le_mul_of_nonneg_left
        (sum_lag_phase_dist_le eta phase count lag a b L hL hmono hphase hlo hhi) hK
  calc
    _ = ‖∑ j ∈ Finset.range count,
      (F (phase (eta j)) (phase (eta (j + lag))) - F (phase (eta j)) (phase (eta j)))‖ /
      (count : ℝ) := by simp
    _ ≤ (K * (L * (lag : ℝ) * (b - a))) / (count : ℝ) :=
      div_le_div_of_nonneg_right hsum (Nat.cast_nonneg count)
    _ = K * L * ((lag : ℝ) * (b - a) / (count : ℝ)) := by ring

/-- A proved diagonal average transfers to the lag average; no equidistribution
provider or zeta hypothesis is asserted by this deterministic theorem. -/
theorem lag_test_tendsto_of_diagonal (eta : ℕ → ℕ → ℝ) (phase : ℝ → X)
    (F : X → X → ℂ) (count lag : ℕ → ℕ) (a b : ℕ → ℝ) (K L : ℝ) (z : ℂ)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hmono : ∀ n, Monotone (eta n))
    (hphase : ∀ s t : ℝ, dist (phase s) (phase t) ≤ L * |s - t|)
    (hF : ∀ x y, ‖F x y - F x x‖ ≤ K * dist y x)
    (hlo : ∀ n k, k < lag n → a n ≤ eta n k)
    (hhi : ∀ n k, k < lag n → eta n (count n + k) ≤ b n)
    (hbudget : Tendsto (fun n => K * L * ((lag n : ℝ) * (b n - a n) / (count n : ℝ)))
      atTop (nhds 0))
    (hdiag : Tendsto (fun n => (∑ j ∈ Finset.range (count n),
      F (phase (eta n j)) (phase (eta n j))) / (count n : ℂ)) atTop (nhds z)) :
    Tendsto (fun n => (∑ j ∈ Finset.range (count n),
      F (phase (eta n j)) (phase (eta n (j + lag n)))) / (count n : ℂ)) atTop (nhds z) := by
  have hdiff : Tendsto (fun n =>
      (∑ j ∈ Finset.range (count n), F (phase (eta n j)) (phase (eta n (j + lag n)))) /
        (count n : ℂ) - (∑ j ∈ Finset.range (count n), F (phase (eta n j)) (phase (eta n j))) /
        (count n : ℂ)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n =>
      mean_lag_test_sub_diagonal_norm_le (eta n) phase F (count n) (lag n)
        (a n) (b n) K L hK hL (hmono n) hphase hF (hlo n) (hhi n)) hbudget
  simpa only [zero_add, sub_add_cancel] using hdiff.add hdiag

end RiemannResearch.Analysis.LagPhase
