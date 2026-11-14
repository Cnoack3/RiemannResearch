import RiemannResearch.Analysis.ResidualGainProduct
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite accounting and exhaustion from lower bounds on residual loss

Source: the user's residual-projection question of 2026-11-14. The application
is the squared norm of a nested-projection residual. This module proves scalar
consumers only; it supplies no arithmetic lower bound on a residual projection.

The exact accounting identity retains both the slack in the proposed lower
bound and the difference between earlier and terminal energies. The ensuing
bound and nonsummability criterion allow finite termination and do not assume
that the proposed relative-loss lower bounds are at most one.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ResidualGain

/-- Exact finite accounting, with no sign or monotonicity hypotheses. -/
theorem loss_accounting (d a : ℕ → ℝ) (n : ℕ) :
    d 0 = d n * (1 + ∑ i ∈ Finset.range n, a i) +
      (∑ i ∈ Finset.range n, a i * (d i - d n)) +
      ∑ i ∈ Finset.range n, (d i - d (i + 1) - a i * d i) := by
  calc
    d 0 = d n + ∑ i ∈ Finset.range n, (d i - d (i + 1)) := by
      rw [Finset.sum_range_sub']
      ring
    _ = d n + ∑ i ∈ Finset.range n,
        (d n * a i + a i * (d i - d n) + (d i - d (i + 1) - a i * d i)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- Nonnegative lower bounds on relative loss imply monotonicity, including
stages where the residual has already vanished. -/
theorem antitone_of_loss {d a : ℕ → ℝ} (hd : ∀ n, 0 ≤ d n)
    (ha : ∀ n, 0 ≤ a n)
    (hgain : ∀ n, a n * d n ≤ d n - d (n + 1)) : Antitone d := by
  apply antitone_nat_of_succ_le
  intro n
  have hmul := mul_nonneg (ha n) (hd n)
  have h := hgain n
  linarith

/-- A finite quantitative bound, retaining the exact slack terms in
`loss_accounting` before estimating them. -/
theorem residual_mul_one_add_cumulative_loss_le {d a : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n) (ha : ∀ n, 0 ≤ a n)
    (hgain : ∀ n, a n * d n ≤ d n - d (n + 1)) (n : ℕ) :
    d n * (1 + ∑ i ∈ Finset.range n, a i) ≤ d 0 := by
  have hmono := antitone_of_loss hd ha hgain
  have hvariation : 0 ≤ ∑ i ∈ Finset.range n, a i * (d i - d n) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (ha i) (sub_nonneg.mpr (hmono (Nat.le_of_lt (Finset.mem_range.mp hi))))
  have hslack : 0 ≤ ∑ i ∈ Finset.range n, (d i - d (i + 1) - a i * d i) := by
    exact Finset.sum_nonneg (fun i hi => sub_nonneg.mpr (hgain i))
  linarith only [loss_accounting d a n, hvariation, hslack]

theorem residual_le_div_one_add_cumulative_loss {d a : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n) (ha : ∀ n, 0 ≤ a n)
    (hgain : ∀ n, a n * d n ≤ d n - d (n + 1)) (n : ℕ) :
    d n ≤ d 0 / (1 + ∑ i ∈ Finset.range n, a i) := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range n, a i :=
    Finset.sum_nonneg (fun i hi => ha i)
  exact (le_div_iff₀ (by linarith : 0 < 1 + ∑ i ∈ Finset.range n, a i)).mpr
    (residual_mul_one_add_cumulative_loss_le hd ha hgain n)

/-- Exponential finite bound. Even an oversized proposed gain is harmless:
the loss inequality then forces the nonnegative residual to terminate. -/
theorem residual_le_exp_neg_cumulative_loss {d a : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n)
    (hgain : ∀ n, a n * d n ≤ d n - d (n + 1)) (n : ℕ) :
    d n ≤ d 0 * Real.exp (-(∑ i ∈ Finset.range n, a i)) := by
  have hstep (k : ℕ) : d (k + 1) ≤ d k * Real.exp (-a k) := by
    have he : 1 - a k ≤ Real.exp (-a k) := by
      linarith only [Real.add_one_le_exp (-a k)]
    have hm := mul_le_mul_of_nonneg_left he (hd k)
    have hg := hgain k
    nlinarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, neg_add, Real.exp_add]
    calc
      d (n + 1) ≤ d n * Real.exp (-a n) := hstep n
      _ ≤ (d 0 * Real.exp (-(∑ i ∈ Finset.range n, a i))) * Real.exp (-a n) :=
        mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)
      _ = _ := by ring

/-- Divergent cumulative lower loss exhausts every nonnegative residual.
No strict positivity or no-finite-termination hypothesis is needed. -/
theorem tendsto_zero_of_cumulative_loss {d a : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n)
    (hgain : ∀ n, a n * d n ≤ d n - d (n + 1))
    (hdiv : Tendsto (fun n => ∑ i ∈ Finset.range n, a i) atTop atTop) :
    Tendsto d atTop (𝓝 0) := by
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp hdiv
  have hupper : Tendsto (fun n => d 0 * Real.exp (-(∑ i ∈ Finset.range n, a i)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hexp :
      Tendsto (fun n => d 0 * Real.exp (-(∑ i ∈ Finset.range n, a i)))
        atTop (𝓝 (d 0 * 0)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    hd (residual_le_exp_neg_cumulative_loss hd hgain)

theorem tendsto_zero_of_not_summable_loss {d a : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n) (ha : ∀ n, 0 ≤ a n)
    (hgain : ∀ n, a n * d n ≤ d n - d (n + 1)) (hdiv : ¬Summable a) :
    Tendsto d atTop (𝓝 0) :=
  tendsto_zero_of_cumulative_loss hd hgain
    ((not_summable_iff_tendsto_nat_atTop_of_nonneg ha).mp hdiv)

/-- The lower bound is needed only eventually; deleting finitely many stages
does not change nonsummability of the nonnegative loss coefficients. -/
theorem tendsto_zero_of_eventually_not_summable_loss {d a : ℕ → ℝ}
    (hd : ∀ n, 0 ≤ d n) (ha : ∀ n, 0 ≤ a n)
    (hgain : ∀ᶠ n in atTop, a n * d n ≤ d n - d (n + 1))
    (hdiv : ¬Summable a) : Tendsto d atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgain
  have htail : ¬Summable (fun n => a (n + N)) := by
    intro hs
    exact hdiv ((summable_nat_add_iff N).mp hs)
  apply (tendsto_add_atTop_iff_nat N).mp
  apply tendsto_zero_of_not_summable_loss (fun n => hd (n + N))
    (fun n => ha (n + N)) _ htail
  intro n
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    hN (n + N) (Nat.le_add_left N n)

/-- A nonzero limiting residual forces infinitely many failures of every
nonsummable proposed lower bound on relative loss. -/
theorem frequently_loss_lt_of_nonzero_limit {d a : ℕ → ℝ} {l : ℝ}
    (hd : ∀ n, 0 ≤ d n) (ha : ∀ n, 0 ≤ a n) (hdiv : ¬Summable a)
    (hlim : Tendsto d atTop (𝓝 l)) (hl : l ≠ 0) :
    ∃ᶠ n in atTop, d n - d (n + 1) < a n * d n := by
  by_contra h
  have hgain : ∀ᶠ n in atTop, a n * d n ≤ d n - d (n + 1) := by
    simpa only [Filter.Frequently, not_not, not_lt] using h
  exact hl (tendsto_nhds_unique hlim
    (tendsto_zero_of_eventually_not_summable_loss hd ha hgain hdiv))

end RiemannResearch.Analysis.ResidualGain
