/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sharp coefficient variation of balanced signed rows

Source: the user-provided Two_Prime_Mellin_Parity_Handoff_2026-10-20,
Section 7, for the signed mass-one and drift-zero constraints. The finite
inequality below strengthens the negative-weight consequence to an optimal
total-variation bound. It does not assert any Hilbert norm bound.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.SignedBalancedRows

/-- Exact finite slack identity, before imposing either balance constraint
or an interval restriction on the slopes. -/
theorem totalVariation_slack_identity {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b : ℝ) :
    (a - b) * (∑ i ∈ S, |w i|) -
        (a + b) * (∑ i ∈ S, w i) +
        2 * (∑ i ∈ S, w i * slope i) =
      ∑ i ∈ S, ((|w i| + w i) * (slope i - b) +
        (|w i| - w i) * (a - slope i)) := by
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- For a balanced row the excess variation is exactly the signed endpoint
slack. This equality retains the information discarded by the lower bound. -/
theorem totalVariation_gap_exact {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b : ℝ)
    (hmass : ∑ i ∈ S, w i = 1)
    (hbal : ∑ i ∈ S, w i * slope i = 0) :
    (a - b) * (∑ i ∈ S, |w i|) - (a + b) =
      ∑ i ∈ S, ((|w i| + w i) * (slope i - b) +
        (|w i| - w i) * (a - slope i)) := by
  simpa only [hmass, hbal, mul_one, mul_zero, add_zero] using
    totalVariation_slack_identity S w slope a b

/-- Each endpoint-slack summand is nonnegative when its slope is in the interval. -/
theorem totalVariation_slack_nonneg {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b : ℝ)
    (hlo : ∀ i ∈ S, b ≤ slope i)
    (hhi : ∀ i ∈ S, slope i ≤ a) :
    0 ≤ ∑ i ∈ S, ((|w i| + w i) * (slope i - b) +
      (|w i| - w i) * (a - slope i)) := by
  apply Finset.sum_nonneg
  intro i hi
  have hplus : 0 ≤ |w i| + w i := by linarith [neg_abs_le (w i)]
  have hminus : 0 ≤ |w i| - w i := sub_nonneg.mpr (le_abs_self (w i))
  exact add_nonneg
    (mul_nonneg hplus (sub_nonneg.mpr (hlo i hi)))
    (mul_nonneg hminus (sub_nonneg.mpr (hhi i hi)))

/-- A signed row with mass one and zero moment must pay for the width of
the interval containing its positive slopes. No positivity assumptions are
needed for this undivided finite algebraic inequality. -/
theorem totalVariation_gap {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b : ℝ)
    (hlo : ∀ i ∈ S, b ≤ slope i)
    (hhi : ∀ i ∈ S, slope i ≤ a)
    (hmass : ∑ i ∈ S, w i = 1)
    (hbal : ∑ i ∈ S, w i * slope i = 0) :
    a + b ≤ (a - b) * (∑ i ∈ S, |w i|) := by
  have he := totalVariation_gap_exact S w slope a b hmass hbal
  have hs := totalVariation_slack_nonneg S w slope a b hlo hhi
  linarith

/-- The exact minimum possible variation for slopes in a fixed positive interval. -/
theorem totalVariation_lower {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b : ℝ) (hba : b < a)
    (hlo : ∀ i ∈ S, b ≤ slope i)
    (hhi : ∀ i ∈ S, slope i ≤ a)
    (hmass : ∑ i ∈ S, w i = 1)
    (hbal : ∑ i ∈ S, w i * slope i = 0) :
    (a + b) / (a - b) ≤ ∑ i ∈ S, |w i| := by
  apply (div_le_iff₀ (sub_pos.mpr hba)).mpr
  simpa only [mul_comm] using totalVariation_gap S w slope a b hlo hhi hmass hbal

/-- Bounded variation prevents all slopes from approaching the same positive
value relative to their maximum. -/
theorem slope_ratio_le_of_totalVariation_le {ι : Type*}
    (S : Finset ι) (w slope : ι → ℝ) (a b M : ℝ)
    (ha : 0 < a) (hba : b < a) (hM : 0 ≤ M)
    (hlo : ∀ i ∈ S, b ≤ slope i)
    (hhi : ∀ i ∈ S, slope i ≤ a)
    (hmass : ∑ i ∈ S, w i = 1)
    (hbal : ∑ i ∈ S, w i * slope i = 0)
    (hvar : ∑ i ∈ S, |w i| ≤ M) :
    b / a ≤ (M - 1) / (M + 1) := by
  have hgap := totalVariation_gap S w slope a b hlo hhi hmass hbal
  have hbound := mul_le_mul_of_nonneg_left hvar (sub_pos.mpr hba).le
  apply (div_le_div_iff₀ ha (by linarith : 0 < M + 1)).mpr
  nlinarith

/-- The endpoint pair has mass one. -/
theorem endpoint_mass (a b : ℝ) (hba : b < a) :
    -b / (a - b) + a / (a - b) = 1 := by
  field_simp [ne_of_gt (sub_pos.mpr hba)]
  ring

/-- The endpoint pair exactly cancels the positive slopes. -/
theorem endpoint_moment (a b : ℝ) :
    (-b / (a - b)) * a + (a / (a - b)) * b = 0 := by
  ring

/-- Sharpness: the two endpoint weights attain the lower variation bound. -/
theorem endpoint_totalVariation (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    |-b / (a - b)| + |a / (a - b)| = (a + b) / (a - b) := by
  have hg : 0 < a - b := sub_pos.mpr hba
  have ha : 0 < a := hb.trans hba
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hg.le),
    abs_of_nonneg (div_nonneg ha.le hg.le)]
  ring

end RiemannResearch.Analysis.SignedBalancedRows
