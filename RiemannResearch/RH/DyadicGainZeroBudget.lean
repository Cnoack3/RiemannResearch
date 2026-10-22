import RiemannResearch.RH.DyadicGainEndpoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite logarithmic gain budgets forced by a hypothetical off-line zero

Source: user-provided
`RH_Zero_Ordinates_Haar_and_Actual_Residual_Gain_Consolidated_2026-10-11 (1).md`,
Sections 5--6, followed by the exact recurrence deductions below.

The results are unconditional implications for
the actual Pareto projection distances. It supplies no gain lower estimate
and assumes neither RH nor a reverse RH-to-two-seed-density theorem.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoupledResidual
open RiemannResearch.Analysis.ResidualGain
open FiniteTwoSeedCompletion RamanujanLaguerre

/-- The Mellin separator obstructs every actual finite projection. -/
theorem distance_lower_bound_of_zeta_zero (M : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2 * s.re - 1) / ‖s‖ ^ 2 ≤ distance M := by
  have hA : ∀ a ∈ ({2, 3} : Set ℕ), 0 < a := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl <;> norm_num
  have hmem : fit M ∈ hilbertLegalClosure {2, 3} :=
    budget_le_twoSeedClosure M ((budgetHilbert M).starProjection_apply_mem _)
  simpa only [distance, error] using
    legalClosure_distance_sq_lower_bound_of_zeta {2, 3} hA s hs hs1 hz hmem

theorem zero_mellin_floor_pos (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    0 < (2 * s.re - 1) / ‖s‖ ^ 2 := by
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  exact div_pos (by linarith) (pow_pos (norm_pos_iff.mpr hs0) 2)

/-- Exact accounting, retaining every logarithmic gain. -/
theorem dyadic_log_gain_sum_eq (J N : ℕ) :
    (∑ n ∈ Finset.range N, -Real.log (1 - dyadicRelativeGain J n)) =
      Real.log (distance (2 ^ J)) - Real.log (distance (2 ^ (J + N))) := by
  have h := log_recurrence_eq_initial_sub_sum
    (d := fun n => distance (2 ^ (J + n))) (r := dyadicRelativeGain J)
    (by simpa only [Nat.add_zero] using distance_pos (2 ^ J))
    (dyadicRelativeGain_lt_one J) (dyadic_distance_recurrence J) N
  simpa only [Nat.add_zero] using (by linarith :
    (∑ n ∈ Finset.range N, -Real.log (1 - dyadicRelativeGain J n)) =
      Real.log (distance (2 ^ (J + 0))) -
        Real.log (distance (2 ^ (J + N))))

/-- Any positive residual floor limits the entire finite logarithmic gain. -/
theorem dyadic_log_gain_sum_le_of_floor (J N : ℕ) (L : ℝ) (hL : 0 < L)
    (hfloor : L ≤ distance (2 ^ (J + N))) :
    (∑ n ∈ Finset.range N, -Real.log (1 - dyadicRelativeGain J n)) ≤
      Real.log (distance (2 ^ J)) - Real.log L := by
  rw [dyadic_log_gain_sum_eq]
  exact sub_le_sub_left (Real.log_le_log hL hfloor) _

/-- A hypothetical off-line zero imposes an explicit finite gain budget. -/
theorem dyadic_log_gain_sum_le_of_zeta_zero (J N : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (∑ n ∈ Finset.range N, -Real.log (1 - dyadicRelativeGain J n)) ≤
      Real.log (distance (2 ^ J)) -
        Real.log ((2 * s.re - 1) / ‖s‖ ^ 2) :=
  dyadic_log_gain_sum_le_of_floor J N _ (zero_mellin_floor_pos s hs)
    (distance_lower_bound_of_zeta_zero _ s hs hs1 hz)

/-- Ordinary relative gains consume at most the same logarithmic budget. -/
theorem dyadic_gain_sum_le_of_zeta_zero (J N : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (∑ n ∈ Finset.range N, dyadicRelativeGain J n) ≤
      Real.log (distance (2 ^ J)) -
        Real.log ((2 * s.re - 1) / ‖s‖ ^ 2) := by
  apply le_trans (Finset.sum_le_sum (fun n _ =>
    gain_le_neg_log_one_sub (dyadicRelativeGain_lt_one J n)))
  exact dyadic_log_gain_sum_le_of_zeta_zero J N s hs hs1 hz

/-- The hypothetical zero forces actual relative gains to be summable. -/
theorem dyadic_gain_summable_of_zeta_zero (J : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    Summable (dyadicRelativeGain J) := by
  by_contra hns
  have hd := (dyadic_distance_tendsto_zero_iff J).mpr hns
  have hbad : (2 * s.re - 1) / ‖s‖ ^ 2 ≤ 0 :=
    ge_of_tendsto hd (Filter.Eventually.of_forall (fun n =>
      distance_lower_bound_of_zeta_zero (2 ^ (J + n)) s hs hs1 hz))
  exact (not_le_of_gt (zero_mellin_floor_pos s hs)) hbad

/-- The complete logarithmic gain remains within the zero's explicit budget. -/
theorem dyadic_log_gain_tsum_le_of_zeta_zero (J : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (∑' n, -Real.log (1 - dyadicRelativeGain J n)) ≤
      Real.log (distance (2 ^ J)) -
        Real.log ((2 * s.re - 1) / ‖s‖ ^ 2) := by
  have hsum := (summable_neg_log_one_sub_iff
    (dyadicRelativeGain_nonneg J) (dyadicRelativeGain_lt_one J)).mpr
    (dyadic_gain_summable_of_zeta_zero J s hs hs1 hz)
  exact le_of_tendsto hsum.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall (fun N =>
      dyadic_log_gain_sum_le_of_zeta_zero J N s hs hs1 hz))

theorem dyadic_gain_tsum_le_of_zeta_zero (J : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (∑' n, dyadicRelativeGain J n) ≤
      Real.log (distance (2 ^ J)) -
        Real.log ((2 * s.re - 1) / ‖s‖ ^ 2) := by
  have hsum := dyadic_gain_summable_of_zeta_zero J s hs hs1 hz
  exact le_of_tendsto hsum.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall (fun N =>
      dyadic_gain_sum_le_of_zeta_zero J N s hs hs1 hz))

/-- Exceeding this finite logarithmic budget excludes the chosen point as a zero. -/
theorem zeta_ne_zero_of_dyadic_log_gain (J N : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hgain : Real.log (distance (2 ^ J)) -
      Real.log ((2 * s.re - 1) / ‖s‖ ^ 2) <
        ∑ n ∈ Finset.range N, -Real.log (1 - dyadicRelativeGain J n)) :
    riemannZeta s ≠ 0 := by
  intro hz
  exact (not_le_of_gt hgain)
    (dyadic_log_gain_sum_le_of_zeta_zero J N s hs hs1 hz)

/-- A lower bound for just the ordinary finite gains can also certify zero exclusion. -/
theorem zeta_ne_zero_of_dyadic_gain (J N : ℕ) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hgain : Real.log (distance (2 ^ J)) -
      Real.log ((2 * s.re - 1) / ‖s‖ ^ 2) <
        ∑ n ∈ Finset.range N, dyadicRelativeGain J n) :
    riemannZeta s ≠ 0 := by
  intro hz
  exact (not_le_of_gt hgain)
    (dyadic_gain_sum_le_of_zeta_zero J N s hs hs1 hz)

/-- Finite normalized correction certificates consume the same zero budget.
Only the first `N` stages need witnesses. -/
theorem dyadic_reciprocal_cost_sum_le_of_zeta_zero (J N : ℕ) (B : ℕ → ℝ)
    (hB : ∀ n < N, 0 < B n)
    (hw : ∀ n < N, ∃ w : ThresholdHilbert,
      w ∈ budgetHilbert (2 * 2 ^ (J + n)) ∧
      w ∈ (budgetHilbert (2 ^ (J + n)))ᗮ ∧
      inner ℝ (error (2 ^ (J + n))) w = distance (2 ^ (J + n)) ∧
      ‖w‖ ^ 2 ≤ B n * distance (2 ^ (J + n)))
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (∑ n ∈ Finset.range N, 1 / B n) ≤
      Real.log (distance (2 ^ J)) -
        Real.log ((2 * s.re - 1) / ‖s‖ ^ 2) := by
  apply le_trans (Finset.sum_le_sum (fun n hn =>
    (normalized_dyadic_cost_iff J n (B n) (hB n (Finset.mem_range.mp hn))).mp
      (hw n (Finset.mem_range.mp hn))))
  exact dyadic_gain_sum_le_of_zeta_zero J N s hs hs1 hz

/-- Keeping the exact logarithmic cost yields a sharper finite certificate. -/
theorem dyadic_log_cost_sum_le_of_zeta_zero (J N : ℕ) (B : ℕ → ℝ)
    (hB : ∀ n < N, 0 < B n)
    (hw : ∀ n < N, ∃ w : ThresholdHilbert,
      w ∈ budgetHilbert (2 * 2 ^ (J + n)) ∧
      w ∈ (budgetHilbert (2 ^ (J + n)))ᗮ ∧
      inner ℝ (error (2 ^ (J + n))) w = distance (2 ^ (J + n)) ∧
      ‖w‖ ^ 2 ≤ B n * distance (2 ^ (J + n)))
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (∑ n ∈ Finset.range N, -Real.log (1 - 1 / B n)) ≤
      Real.log (distance (2 ^ J)) -
        Real.log ((2 * s.re - 1) / ‖s‖ ^ 2) := by
  apply le_trans (Finset.sum_le_sum (fun n hn => ?_))
    (dyadic_log_gain_sum_le_of_zeta_zero J N s hs hs1 hz)
  have hnN := Finset.mem_range.mp hn
  have hgain := (normalized_dyadic_cost_iff J n (B n) (hB n hnN)).mp (hw n hnN)
  exact neg_le_neg (Real.log_le_log
    (sub_pos.mpr (dyadicRelativeGain_lt_one J n))
    (sub_le_sub_left hgain 1))

/-- A finite collection of legal cost certificates can already exclude `s`. -/
theorem zeta_ne_zero_of_dyadic_log_cost (J N : ℕ) (B : ℕ → ℝ)
    (hB : ∀ n < N, 0 < B n)
    (hw : ∀ n < N, ∃ w : ThresholdHilbert,
      w ∈ budgetHilbert (2 * 2 ^ (J + n)) ∧
      w ∈ (budgetHilbert (2 ^ (J + n)))ᗮ ∧
      inner ℝ (error (2 ^ (J + n))) w = distance (2 ^ (J + n)) ∧
      ‖w‖ ^ 2 ≤ B n * distance (2 ^ (J + n)))
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hcost : Real.log (distance (2 ^ J)) -
      Real.log ((2 * s.re - 1) / ‖s‖ ^ 2) <
        ∑ n ∈ Finset.range N, -Real.log (1 - 1 / B n)) :
    riemannZeta s ≠ 0 := by
  intro hz
  exact (not_le_of_gt hcost)
    (dyadic_log_cost_sum_le_of_zeta_zero J N B hB hw s hs hs1 hz)

end RiemannResearch.RH.Pareto.CoupledResidual
