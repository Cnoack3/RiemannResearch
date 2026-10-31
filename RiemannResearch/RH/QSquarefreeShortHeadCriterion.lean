/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeLogResidualTail
import RiemannResearch.RH.QSquarefreeKernelLocalization
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Limiting-stage logarithmic short-head criteria

Source: SquarefreeShortHeadSchurResearch20261030.md, sections 1 and 6.
These consumers use the actual complete-squarefree canonical residual and
kernel. The signed short-head envelope remains an explicit Open arithmetic
hypothesis. It is sufficient that the bound occur at arbitrarily large stages
for each fixed physical site; the subsequence may depend on the site.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeShortHeadCriterion
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QSquarefreeSmoothedProjection QSquarefreeCorrectionKernel
open QSquarefreeLogResidualTail QPolylogTailEnergy
open QFiniteSupportDualCriterion QAnnihilatorTailEscape QShiftedReciprocal
open RiemannResearch.Analysis.ResidualizedProjectionKernel

/-- A frequent bound is enough because the actual coordinate sequence converges.
There is no uniform finite-stage threshold in this statement. -/
theorem riemannHypothesis_of_frequently_polylog_moving_bound (m : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, 0 < n → ∃ᶠ N : ℕ in atTop,
      |qSequence (movingCorrection N) n| ≤ C * (6 + Real.log (n : ℝ)) ^ m) :
    RiemannHypothesis := by
  have hlim : ∀ n : ℕ,
      |qSequence correction n| ≤ C * (6 + Real.log (n : ℝ)) ^ m := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp only [qSequence_zero, abs_zero, Nat.cast_zero, Real.log_zero, add_zero]
      positivity
    have ht := (qSequence_tendsto_of_tendsto movingCorrection_tendsto n).abs
    by_contra hbad
    have hlt : C * (6 + Real.log (n : ℝ)) ^ m < |qSequence correction n| :=
      lt_of_not_ge hbad
    have he : ∀ᶠ N : ℕ in atTop,
        C * (6 + Real.log (n : ℝ)) ^ m < |qSequence (movingCorrection N) n| :=
      (tendsto_order.1 ht).1 _ hlt
    obtain ⟨N, hN, hgt⟩ := ((hb n (Nat.pos_of_ne_zero hn)).and_eventually he).exists
    exact (not_lt_of_ge hN) hgt
  obtain ⟨D, hD⟩ := exists_log_scaled_tail_bound_of_polylog correction m C hC hlim
  exact riemannHypothesis_of_cofinal_correction_log_tail_bound
    (2 * m + 2) id tendsto_id D hD

def logarithmicCutoff (n : ℕ) : ℕ :=
  ⌊(n : ℝ) / (6 + Real.log (n : ℝ))⌋₊

def logarithmicHeadResponse (N n : ℕ) : ℝ :=
  inner ℝ (residual N)
    (finiteHead (logarithmicCutoff (n + 1))
      (B (kernel N (n + 1)) -
        (1 / ((n : ℝ) + 2)) • kernel N (n + 1)))

theorem log_shift_ge_one (n : ℕ) :
    1 ≤ 6 + Real.log ((n + 1 : ℕ) : ℝ) := by
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  linarith [Real.log_nonneg hn]

/-- The arithmetic scale condition of the existing complete-tail localization
is supplied by the actual logarithmic floor cutoff. -/
theorem logarithmicCutoff_scale (n : ℕ) :
    (n : ℝ) + 2 ≤
      ((6 + Real.log ((n + 1 : ℕ) : ℝ)) + 1) *
        ((logarithmicCutoff (n + 1) : ℝ) + 2) := by
  let L : ℝ := 6 + Real.log ((n + 1 : ℕ) : ℝ)
  have hL : 1 ≤ L := log_shift_ge_one n
  have hLp : 0 < L := by linarith
  have hf : ((n + 1 : ℕ) : ℝ) / L <
      (logarithmicCutoff (n + 1) : ℝ) + 1 := by
    exact Nat.lt_floor_add_one _
  have hm := (div_lt_iff₀ hLp).mp hf
  have hH := Nat.cast_nonneg (α := ℝ) (logarithmicCutoff (n + 1))
  norm_num only [Nat.cast_add, Nat.cast_one] at hm
  change (n : ℝ) + 2 ≤ (L + 1) * ((logarithmicCutoff (n + 1) : ℝ) + 2)
  nlinarith

/-- Unconditional localization; the entire omitted physical tail is retained. -/
theorem logarithmicHeadResponse_remainder_abs_le (N n : ℕ) :
    |qSequence (movingCorrection N) (n + 1) - logarithmicHeadResponse N n| ≤
      Real.sqrt zetaTwo * (6 + Real.log ((n + 1 : ℕ) : ℝ)) := by
  let L : ℝ := 6 + Real.log ((n + 1 : ℕ) : ℝ)
  have hL : 1 ≤ L := log_shift_ge_one n
  have hr : ‖residual N‖ ^ 2 ≤ 1 := by
    have hp := residual_norm_sq (stage N) qOne
    rw [qOne_norm] at hp
    change ‖residual N‖ ^ 2 = _ at hp
    nlinarith [sq_nonneg ‖(stage N).starProjection qOne‖]
  have htail : ‖tail (logarithmicCutoff (n + 1)) (residual N)‖ ^ 2 ≤ 1 := by
    have h := tail_norm_le (logarithmicCutoff (n + 1)) (residual N)
    nlinarith [norm_nonneg (tail (logarithmicCutoff (n + 1)) (residual N)),
      norm_nonneg (residual N)]
  have he := movingCorrection_relativeHead_remainder_sq_le N n
    (logarithmicCutoff (n + 1)) L hL (logarithmicCutoff_scale n)
  change (qSequence (movingCorrection N) (n + 1) - logarithmicHeadResponse N n) ^ 2 ≤
    zetaTwo * L ^ 2 * ‖tail (logarithmicCutoff (n + 1)) (residual N)‖ ^ 2 at he
  have he' : (qSequence (movingCorrection N) (n + 1) - logarithmicHeadResponse N n) ^ 2 ≤
      zetaTwo * L ^ 2 := he.trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left htail
          (mul_nonneg zetaTwo_pos.le (sq_nonneg L)))
  have hroot := Real.sq_sqrt zetaTwo_pos.le
  have hroot0 := Real.sqrt_nonneg zetaTwo
  have hprod : 0 ≤ Real.sqrt zetaTwo * L :=
    mul_nonneg hroot0 (le_trans (by norm_num : (0 : ℝ) ≤ 1) hL)
  have heq : (Real.sqrt zetaTwo * L) ^ 2 = zetaTwo * L ^ 2 := by
    rw [mul_pow, hroot]
  change |qSequence (movingCorrection N) (n + 1) - logarithmicHeadResponse N n| ≤
    Real.sqrt zetaTwo * L
  nlinarith [sq_abs (qSequence (movingCorrection N) (n + 1) - logarithmicHeadResponse N n),
    abs_nonneg (qSequence (movingCorrection N) (n + 1) - logarithmicHeadResponse N n)]

/-- Conditional research reduction with the original max(m,1) logarithmic
exponent. Every n may use its own unbounded set of stages. -/
theorem riemannHypothesis_of_frequently_polylog_logarithmicHead_bound
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n : ℕ, ∃ᶠ N : ℕ in atTop,
      |logarithmicHeadResponse N n| ≤ C * (6 + Real.log ((n + 1 : ℕ) : ℝ)) ^ m) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_polylog_moving_bound (max m 1)
    (C + Real.sqrt zetaTwo) (add_nonneg hC (Real.sqrt_nonneg _))
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  apply (hb n).mono
  intro N hN
  let L : ℝ := 6 + Real.log ((n + 1 : ℕ) : ℝ)
  have hL : 1 ≤ L := log_shift_ge_one n
  have hm : L ^ m ≤ L ^ (max m 1) := pow_le_pow_right₀ hL (Nat.le_max_left _ _)
  have h1 : L ≤ L ^ (max m 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hL (Nat.le_max_right m 1)
  have he := logarithmicHeadResponse_remainder_abs_le N n
  calc
    _ ≤ |qSequence (movingCorrection N) (n + 1) - logarithmicHeadResponse N n| +
        |logarithmicHeadResponse N n| := by
      simpa only [sub_add_cancel] using
        abs_add_le (qSequence (movingCorrection N) (n + 1) - logarithmicHeadResponse N n)
          (logarithmicHeadResponse N n)
    _ ≤ Real.sqrt zetaTwo * L + C * L ^ m := add_le_add he hN
    _ ≤ Real.sqrt zetaTwo * L ^ (max m 1) + C * L ^ (max m 1) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _))
        (mul_le_mul_of_nonneg_left hm hC)
    _ = _ := by dsimp [L]; ring

end RiemannResearch.RH.QSquarefreeShortHeadCriterion
