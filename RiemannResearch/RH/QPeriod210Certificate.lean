/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPhysicalDifference
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.SquarefreeStageExhaustion
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.QDifferenceGram
import RiemannResearch.RH.QPrimorialRegularization
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# An explicit strict period-210 full-Q certificate

Source: QLatticeRegularizationResearch20261018.md, exact rational certificate.
All coefficients and finite checks are rational; `decide +kernel` checks
the finite arithmetic inside the kernel. Complete infinite tails are retained.
This is one positive-penalty certificate, not a vanishing-penalty provider.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QPeriod210Certificate
open ZetaTwoHilbert ZetaTwoProbability QPhysicalDifference
open QFiniteEnergyBounds QDifferenceGram QPrimorialRegularization
open QSquarefreePrimorialCofinality

def coefficientNumerator (d : ℕ) : ℤ :=
  match d with
  | 2 => 9783 | 3 => 9770 | 5 => 9549 | 6 => -8824 | 7 => 9426
  | 10 => -7399 | 14 => -5918 | 15 => -5955 | 21 => -4698
  | 30 => 7574 | 35 => -4122 | 42 => 5233 | 70 => 2704
  | 105 => 363 | 210 => -6191 | _ => 0

def conductors : Finset ℕ := {2,3,5,6,7,10,14,15,21,30,35,42,70,105,210}

def rationalValue (n : ℕ) : ℚ :=
  ∑ d ∈ conductors, (coefficientNumerator d : ℚ)/10000 * ((n%d : ℕ) : ℚ)/d

def candidate : QHilbert :=
  ∑ d ∈ conductors, ((coefficientNumerator d : ℝ)/10000) • qResidue d

theorem conductor_data (d : ℕ) (hd : d ∈ conductors) : 2 ≤ d ∧ d ∣ 210 := by
  simp only [conductors, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem conductor_squarefree (d : ℕ) (hd : d ∈ conductors) : Squarefree d :=
  (show Squarefree 210 by decide +kernel).squarefree_of_dvd (conductor_data d hd).2

theorem candidate_mem_stage : candidate ∈ primorialStage 4 := by
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨d, (conductor_data d hd).1, ?_, rfl⟩
  have hp : Pareto.SquarefreeStageExhaustion.primorialPeriod 4 = 210 := by decide +kernel
  rw [hp]
  exact (conductor_data d hd).2

theorem candidate_squarefree_legal : candidate ∈ qSquarefreeCRTSpan :=
  primorialStage_le_squarefreeSpan 4 candidate_mem_stage

theorem candidate_sequence (n : ℕ) :
    qSequence candidate n = (rationalValue n : ℝ) := by
  change qSequenceLinear candidate n = _
  simp only [candidate, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ d ∈ conductors, (coefficientNumerator d : ℝ)/10000 *
    qSequence (qResidue d) n) = _
  simp_rw [qSequence_qResidue]
  simp only [rationalValue, Rat.cast_sum, Rat.cast_div, Rat.cast_mul,
    Rat.cast_intCast, Rat.cast_natCast, Rat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro d hd
  unfold ArithmeticCumulative.residueFraction
  ring

theorem rationalValue_mod (n : ℕ) : rationalValue (n % 210) = rationalValue n := by
  unfold rationalValue
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.mod_mod_of_dvd n (conductor_data d hd).2]

theorem candidate_periodic (n : ℕ) :
    qSequence candidate (n + 210) = qSequence candidate n := by
  simp only [candidate_sequence]
  rw [← rationalValue_mod (n+210), ← rationalValue_mod n]
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Kernel evaluation of 210 rational values, each containing 15 atoms.
theorem rationalValue_bound : ∀ n : Fin 210,
    |rationalValue n| ≤ 1224169/1050000 := by decide +kernel

theorem candidate_abs_le (n : ℕ) : |qSequence candidate n| ≤ 7/6 := by
  rw [candidate_sequence, ← rationalValue_mod n]
  have hb := rationalValue_bound ⟨n%210, Nat.mod_lt n (by norm_num)⟩
  have hr : |(rationalValue (n%210) : ℝ)| ≤ ((1224169/1050000 : ℚ) : ℝ) := by
    exact_mod_cast hb
  norm_num at hr ⊢
  linarith

theorem candidate_maximum_value : qSequence candidate 109 = 1224169/1050000 := by
  rw [candidate_sequence]
  norm_num [rationalValue, conductors, coefficientNumerator]

theorem candidate_exact_uniform_bound (n : ℕ) :
    |qSequence candidate n| ≤ 1224169/1050000 := by
  rw [candidate_sequence, ← rationalValue_mod n]
  have h := rationalValue_bound ⟨n%210, Nat.mod_lt n (by norm_num)⟩
  have h' : |(rationalValue (n%210) : ℝ)| ≤ ((1224169/1050000 : ℚ) : ℝ) := by
    exact_mod_cast h
  norm_num at h' ⊢
  exact h'

theorem candidate_first_value : qSequence candidate 1 = 221089/262500 := by
  rw [candidate_sequence]
  norm_num [rationalValue, conductors, coefficientNumerator]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Kernel evaluation of the complete first-period rational weighted sum.
theorem rational_head_bound :
    (∑ n ∈ Finset.range 210, rationalValue (n+1)^2/(n+1 : ℚ)^2) < 229/250 := by
  decide +kernel

theorem candidate_head_bound :
    (∑ n ∈ Finset.range 210, (qSequence candidate (n+1))^2/(n+1 : ℝ)^2) <
      229/250 := by
  have h : (((∑ n ∈ Finset.range 210, rationalValue (n+1)^2/(n+1 : ℚ)^2) : ℚ) : ℝ) <
      (((229 : ℚ)/250) : ℝ) := by exact_mod_cast rational_head_bound
  push_cast at h
  simpa only [candidate_sequence] using h

theorem candidate_norm_bound : ‖candidate‖^2 <
    (76/125 : ℝ) * (229/250 + (7/6)^2/210) := by
  have h := norm_sq_le_head_tail candidate 210 (by norm_num) (7/6) (by norm_num)
    candidate_abs_le
  have ha := inverse_zetaTwo_rational_bounds
  have hp : 0 < 1/zetaTwo := one_div_pos.mpr zetaTwo_pos
  have hh : (∑ n ∈ Finset.range 210, (qSequence candidate (n+1))^2/(n+1 : ℝ)^2) +
      (7/6 : ℝ)^2/210 < 229/250 + (7/6)^2/210 := by linarith [candidate_head_bound]
  have hhead := mul_lt_mul_of_pos_left hh hp
  have hnorm := h.trans_lt hhead
  have hconst := mul_lt_mul_of_pos_right ha.2
    (show (0 : ℝ) < 229/250 + (7/6)^2/210 by norm_num)
  exact hnorm.trans hconst

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Kernel evaluation of the 225 exact rational Gram terms.
theorem candidate_difference_energy :
    ‖differenceCLM candidate‖^2 = 52823902806611/115762500000000 := by
  rw [← real_inner_self_eq_norm_sq]
  have he : inner ℝ (differenceCLM candidate) (differenceCLM candidate) =
      ∑ d ∈ conductors, ∑ e ∈ conductors,
        ((coefficientNumerator d : ℝ)/10000) * ((coefficientNumerator e : ℝ)/10000) *
          derivativeGram d e := by
    simp only [candidate, map_sum, map_smul, inner_sum, sum_inner,
      real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    rw [inner_difference_qResidue e d (conductor_data e he).1 (conductor_data d hd).1]
    unfold derivativeGram
    rw [Nat.lcm_comm e d]
    ring
  rw [he]
  have hr : (∑ d ∈ conductors, ∑ e ∈ conductors,
      ((coefficientNumerator d : ℚ)/10000) * ((coefficientNumerator e : ℚ)/10000) *
        (1/((d:ℚ)*e) - 1/((d:ℚ)*e^2) - 1/((d:ℚ)^2*e) +
          1/(Nat.lcm d e : ℚ)^2)) = 52823902806611/115762500000000 := by
    decide +kernel
  have hc : (((∑ d ∈ conductors, ∑ e ∈ conductors,
      ((coefficientNumerator d : ℚ)/10000) * ((coefficientNumerator e : ℚ)/10000) *
        (1/((d:ℚ)*e) - 1/((d:ℚ)*e^2) - 1/((d:ℚ)^2*e) +
          1/(Nat.lcm d e : ℚ)^2)) : ℚ) : ℝ) =
      ((52823902806611/115762500000000 : ℚ) : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) hr
  push_cast at hc
  exact hc

theorem candidate_objective_exact (lam : ℝ) :
    objective lam candidate = 52823902806611/115762500000000 +
      (1/zetaTwo)*(1-2*(221089/262500)) + lam*‖candidate‖^2 := by
  have hs : qSequence (differenceCLM candidate) 1 = 221089/262500 := by
    rw [qSequence_differenceCLM, SquarefreeRadicalDifference.qDifference]
    norm_num only [Nat.reduceSub, qSequence_zero, sub_zero]
    exact candidate_first_value
  have hb := inner_difference_qOne (differenceCLM candidate)
  rw [hs] at hb
  have hc := real_inner_comm (differenceCLM candidate) (differenceCLM qOne)
  rw [objective, norm_sub_sq_real, candidate_difference_energy, norm_difference_qOne_sq]
  nlinarith only [hb, hc]

theorem candidate_strict_certificate :
    objective (1/10) candidate < 3715960194137/38587500000000 := by
  rw [candidate_objective_exact]
  have ha := inverse_zetaTwo_rational_bounds
  have hn := candidate_norm_bound
  have hs := mul_lt_mul_of_neg_right ha.1
    (show (1-2*(221089/262500) : ℝ) < 0 by norm_num)
  nlinarith

theorem candidate_strict_budget : objective (1/10) candidate < 1/10 :=
  candidate_strict_certificate.trans (by norm_num)

theorem stage_four_strict_budget : value 4 (1/10) (by norm_num) < 1/10 :=
  (minimizer_le_trial 4 (1/10) (by norm_num) candidate candidate_mem_stage).trans_lt
    candidate_strict_budget

end RiemannResearch.RH.QPeriod210Certificate
