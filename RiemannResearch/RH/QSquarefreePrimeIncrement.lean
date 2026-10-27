/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PrimeIncrementEnvelope
import RiemannResearch.RH.QSquarefreeLogResidualTail
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

/-!
# Prime - increment criteria for the actual projected smoothed residual

Source: PrimeResamplingResearch20261027.md, Sections 6 and 8, supplied by
the user. The prime - factor telescoping argument extends the proposed
logarithmic increment bound to arbitrary fixed integer logarithmic losses.
The arithmetic bound on the actual correction remains Open. These theorems
do not assert RH or an RH - to - squarefree - density converse.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreePrimeIncrement
open ZetaTwoHilbert ZetaTwoOptimizerStage
open QSquarefreeSmoothedProjection QSquarefreeLogResidualTail QPolylogTailEnergy
open RiemannResearch.Analysis.PrimeIncrementEnvelope

/-- A local estimate along prime multiplication gives the complete physical
envelope needed by the existing squarefree logarithmic-tail theorem. -/
theorem residual_zero_of_correction_prime_increments
    (m : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hstep : ∀ p n : ℕ, p.Prime → 0 < n →
      |qSequence correction (p * n) - qSequence correction n| ≤
        L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m) :
    limitingResidual = 0 := by
  let C := |qSequence correction 1| + L
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) hL
  have henv : ∀ n : ℕ, |qSequence correction n| ≤
      C * (6 + Real.log (n : ℝ)) ^ (m + 1) := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [qSequence_zero, abs_zero, Nat.cast_zero, Real.log_zero, add_zero]
      positivity
    exact abs_le_polylog_of_prime_increments (qSequence correction) L hL m
      hstep n (Nat.pos_of_ne_zero hn)
  obtain ⟨D, hD⟩ := exists_log_scaled_tail_bound_of_polylog
    correction (m + 1) C hC henv
  exact (residual_zero_iff_correction_frequently_bounded_log_scaled_tail
    (2 * (m + 1) + 2)).mpr ⟨D, (Eventually.of_forall hD).frequently⟩

/-- Exact criterion for the limit, for each chosen nonnegative L and exponent.
Its forward direction is trivial because residual zero makes the correction zero. -/
theorem residual_zero_iff_correction_prime_increments
    (m : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    limitingResidual = 0 ↔ ∀ p n : ℕ, p.Prime → 0 < n →
      |qSequence correction (p * n) - qSequence correction n| ≤
        L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m := by
  constructor
  · intro hr p n hp hn
    have hz (k : ℕ) : qSequence correction k = 0 := by
      rw [correction, hr, map_zero, map_zero]
      cases k <;> simp [qSequence]
    rw [hz, hz, sub_self, abs_zero]
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hpn : (1 : ℝ) ≤ ((p * n : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_pos hp.pos hn)
    positivity [Real.log_nonneg hp1, Real.log_nonneg hpn]
  · exact residual_zero_of_correction_prime_increments m L hL

/-- Each fixed prime edge only needs its own cofinal set of bounded stages.
No common stage set, rate of convergence, or full-period bound is required. -/
theorem residual_zero_of_frequently_moving_prime_increments
    (m : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hstep : ∀ p n : ℕ, p.Prime → 0 < n → ∃ᶠ N : ℕ in atTop,
      |qSequence (movingCorrection N) (p * n) - qSequence (movingCorrection N) n| ≤
        L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m) :
    limitingResidual = 0 := by
  apply residual_zero_of_correction_prime_increments m L hL
  intro p n hp hn
  by_contra h
  have ht := ((qSequence_tendsto_of_tendsto movingCorrection_tendsto (p * n)).sub
    (qSequence_tendsto_of_tendsto movingCorrection_tendsto n)).abs
  have hg := ht.eventually (Ioi_mem_nhds (lt_of_not_ge h))
  obtain ⟨N, hN, hgt⟩ := ((hstep p n hp hn).and_eventually hg).exists
  exact (not_lt_of_ge hN) hgt

/-- For every strictly positive fixed allowance, the cofinal-stage test is exact. -/
theorem residual_zero_iff_frequently_moving_prime_increments
    (m : ℕ) (L : ℝ) (hL : 0 < L) :
    limitingResidual = 0 ↔ ∀ p n : ℕ, p.Prime → 0 < n → ∃ᶠ N : ℕ in atTop,
      |qSequence (movingCorrection N) (p * n) - qSequence (movingCorrection N) n| ≤
        L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m := by
  constructor
  · intro hr p n hp hn
    have hz (k : ℕ) : qSequence correction k = 0 := by
      rw [correction, hr, map_zero, map_zero]
      cases k <;> simp [qSequence]
    have ht := ((qSequence_tendsto_of_tendsto movingCorrection_tendsto (p * n)).sub
      (qSequence_tendsto_of_tendsto movingCorrection_tendsto n)).abs
    have hpn : (1 : ℝ) ≤ ((p * n : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_pos hp.pos hn)
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hB : 0 < L * Real.log (p : ℝ) *
        (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m := by
      positivity [Real.log_pos hp1, Real.log_nonneg hpn]
    simp only [hz, sub_self, abs_zero] at ht
    exact (ht.eventually (Iio_mem_nhds hB)).frequently.mono (fun N hN => hN.le)
  · exact residual_zero_of_frequently_moving_prime_increments m L hL.le

/-- Conditional RH reduction; the frequent prime-increment bound is the
explicit, unresolved arithmetic premise. -/
theorem riemannHypothesis_of_frequently_moving_prime_increments
    (m : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hstep : ∀ p n : ℕ, p.Prime → 0 < n → ∃ᶠ N : ℕ in atTop,
      |qSequence (movingCorrection N) (p * n) - qSequence (movingCorrection N) n| ≤
        L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m) :
    RiemannHypothesis := by
  have hr := residual_zero_of_frequently_moving_prime_increments m L hL hstep
  exact ZetaTwoParetoTransfer.riemannHypothesis_of_qOne_mem_squarefree_closure
    (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm)

/-- Failure of density forces an arbitrarily large normalized prime increment,
for every fixed logarithmic allowance. This is an unconditional dichotomy. -/
theorem exists_large_prime_increment_of_residual_ne_zero
    (hr : limitingResidual ≠ 0) (m : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ p n : ℕ, p.Prime ∧ 0 < n ∧
      L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m <
        |qSequence correction (p * n) - qSequence correction n| := by
  by_contra h
  push Not at h
  exact hr (residual_zero_of_correction_prime_increments m L hL h)


/-- If the residual is nonzero, one fixed prime edge eventually violates
each proposed allowance at all sufficiently large stages. -/
theorem eventually_large_moving_prime_increment_of_residual_ne_zero
    (hr : limitingResidual ≠ 0) (m : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    ∃ p n : ℕ, p.Prime ∧ 0 < n ∧ ∀ᶠ N : ℕ in atTop,
      L * Real.log (p : ℝ) * (6 + Real.log ((p * n : ℕ) : ℝ)) ^ m <
        |qSequence (movingCorrection N) (p * n) - qSequence (movingCorrection N) n| := by
  obtain ⟨p, n, hp, hn, hlarge⟩ :=
    exists_large_prime_increment_of_residual_ne_zero hr m L hL
  refine ⟨p, n, hp, hn, ?_⟩
  have ht := ((qSequence_tendsto_of_tendsto movingCorrection_tendsto (p * n)).sub
    (qSequence_tendsto_of_tendsto movingCorrection_tendsto n)).abs
  exact ht.eventually (Ioi_mem_nhds hlarge)

end RiemannResearch.RH.QSquarefreePrimeIncrement
