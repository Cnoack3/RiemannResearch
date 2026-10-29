/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.QCRTPeriod9699690Certificate
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.Analysis.InverseSquareAbelTail
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Quantitative epsilon bounds from an actual exact head

Source: the user's request to formulate the CRT approximation program using
forall epsilon, exists a legal approximant, 28 October 2026. The exact signed
tail identity precedes its estimate. Both quantities use the complete Q norm.
The resulting finite epsilon witness does not assert the universal arithmetic
existence statement needed for closure.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QExactHeadEpsilonBounds
open ZetaTwoHilbert ZetaTwoProbability QFiniteSupportDualCriterion QFiniteEnergyBounds
open RiemannResearch.Analysis.InverseSquareAbelTail

/-- The complete probability mass beyond the physical head. -/
def targetTail (H : ℕ) : ℝ := ‖qOne - finiteHead H qOne‖ ^ 2

theorem finiteHead_eq_of_exact_head (H : ℕ) (f : QHilbert)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = 1) :
    finiteHead H f = finiteHead H qOne := by
  apply lp.ext
  funext n
  by_cases hn : n < H
  · rw [finiteHead_apply_of_lt H f n hn, finiteHead_apply_of_lt H qOne n hn]
    have he : qSequence f (n + 1) = qSequence qOne (n + 1) := by
      rw [hh (n + 1) (by omega) (by omega), qSequence_qOne]
      simp [qOneSequence]
    have hne : Real.sqrt (qWeight n) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n))
    simpa only [qSequence_succ, div_left_inj' hne] using he
  · rw [finiteHead_apply_eq_zero H f n (by omega),
      finiteHead_apply_eq_zero H qOne n (by omega)]

/-- Full signed tail equality; the mixed term is not discarded. -/
theorem exact_head_error_identity (H : ℕ) (f : QHilbert)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = 1) :
    ‖qOne - f‖ ^ 2 = ‖f‖ ^ 2 - 1 + 2 * targetTail H -
      2 * inner ℝ (qOne - finiteHead H qOne) (f - finiteHead H qOne) := by
  have hF := finiteHead_norm_sq_split H f
  rw [finiteHead_eq_of_exact_head H f hh] at hF
  have h1 := finiteHead_norm_sq_split H qOne
  rw [qOne_norm_sq] at h1
  have hd : qOne - f =
      (qOne - finiteHead H qOne) - (f - finiteHead H qOne) := by abel
  rw [hd, norm_sub_sq_real]
  dsimp [targetTail]
  linarith

/-- An energy excess and the target tail together control the complete error. -/
theorem error_sq_le_head_energy (H : ℕ) (f : QHilbert)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = 1) :
    ‖qOne - f‖ ^ 2 ≤ 2 * (‖f‖ ^ 2 - 1) + 4 * targetTail H := by
  have hF := finiteHead_norm_sq_split H f
  rw [finiteHead_eq_of_exact_head H f hh] at hF
  have h1 := finiteHead_norm_sq_split H qOne
  rw [qOne_norm_sq] at h1
  have hd : qOne - f =
      (qOne - finiteHead H qOne) - (f - finiteHead H qOne) := by abel
  have ht := norm_sub_le (qOne - finiteHead H qOne) (f - finiteHead H qOne)
  rw [← hd] at ht
  have hsquare : 0 ≤
      (‖qOne - finiteHead H qOne‖ + ‖f - finiteHead H qOne‖ - ‖qOne - f‖) *
      (‖qOne - finiteHead H qOne‖ + ‖f - finiteHead H qOne‖ + ‖qOne - f‖) :=
    mul_nonneg (sub_nonneg.mpr ht) (by positivity)
  dsimp [targetTail]
  nlinarith [norm_nonneg (qOne - f), norm_nonneg (qOne - finiteHead H qOne),
    norm_nonneg (f - finiteHead H qOne),
    sq_nonneg (‖qOne - finiteHead H qOne‖ - ‖f - finiteHead H qOne‖)]

theorem target_head_norm_sq (H : ℕ) :
    ‖finiteHead H qOne‖ ^ 2 = (1 / zetaTwo) *
      ∑ n ∈ Finset.range H, 1 / (n + 1 : ℝ) ^ 2 := by
  have hi : inner ℝ (finiteHead H qOne) (finiteHead H qOne) =
      inner ℝ qOne (finiteHead H qOne) := by
    rw [finiteHead_inner, finiteHead_idem]
  have hn (n : ℕ) : (qOne n) ^ 2 = positiveQWeight (n + 1) := by
    have h := qSequence_weighted_square qOne n
    rw [qSequence_qOne] at h
    simpa [qOneSequence] using h.symm
  rw [← real_inner_self_eq_norm_sq, hi, inner_finiteHead_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hnH
  rw [← pow_two, hn]
  unfold positiveQWeight
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact complete target-tail mass, before the elementary integral bound. -/
theorem targetTail_eq (H : ℕ) :
    targetTail H = (1 / zetaTwo) * ∑' n : ℕ, weight H n := by
  have hs := finiteHead_norm_sq_split H qOne
  rw [qOne_norm_sq, target_head_norm_sq] at hs
  have hz := congrArg (fun x : ℝ => (1 / zetaTwo) * x) (zetaTwo_split H)
  have hmul : (1 / zetaTwo) * zetaTwo = 1 := by
    field_simp [ne_of_gt zetaTwo_pos]
  rw [hmul, mul_add] at hz
  dsimp [targetTail]
  linarith

theorem targetTail_le (H : ℕ) (hH : 0 < H) :
    targetTail H ≤ 1 / (zetaTwo * (H : ℝ)) := by
  rw [targetTail_eq]
  have h := mul_le_mul_of_nonneg_left (weight_mass_upper H hH)
    (one_div_pos.mpr zetaTwo_pos).le
  simpa only [div_eq_mul_inv, mul_inv_rev, one_mul, mul_one, mul_comm] using h

/-- A rational tail bound suited to exact finite epsilon certificates. -/
theorem targetTail_le_rational (H : ℕ) (hH : 0 < H) :
    targetTail H ≤ (76 / 125 : ℝ) / (H : ℝ) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ 1 / (zetaTwo * (H : ℝ)) := targetTail_le H hH
    _ = (1 / zetaTwo) / (H : ℝ) := by
      simp [div_eq_mul_inv, mul_comm]
    _ ≤ _ := div_le_div_of_nonneg_right inverse_zetaTwo_rational_bounds.2.le hHR.le

/-- No bound on an entire predetermined family is a hypothesis here.
The chosen witness must pay both its energy excess and its complete target tail. -/
theorem norm_error_lt_of_epsilon_budget (H : ℕ) (f : QHilbert)
    (hh : ∀ n, 0 < n → n ≤ H → qSequence f n = 1)
    (ε : ℝ) (hε : 0 < ε)
    (henergy : ‖f‖ ^ 2 ≤ 1 + ε ^ 2 / 8)
    (htail : targetTail H ≤ ε ^ 2 / 8) :
    ‖qOne - f‖ < ε := by
  have h := error_sq_le_head_energy H f hh
  nlinarith [sq_pos_of_pos hε, norm_nonneg (qOne - f)]

/-- A genuine finite epsilon witness, distinct from the unproved forall-epsilon claim. -/
theorem period9699690_error_lt_seventeen_fiftieths :
    ‖qOne - QCRTPeriod9699690Certificate.certificate‖ < (17 : ℝ) / 50 := by
  have h := error_sq_le_head_energy 20 QCRTPeriod9699690Certificate.certificate
    QCRTPeriod9699690Certificate.certificate_exact_head
  have ht := targetTail_le_rational 20 (by norm_num)
  have he := QCRTPeriod9699690Certificate.certificate_energy_bound
  norm_num only [Nat.cast_ofNat] at ht
  nlinarith [norm_nonneg (qOne - QCRTPeriod9699690Certificate.certificate)]

theorem exists_legal_epsilon_034 : ∃ f : QHilbert,
    f ∈ qSquarefreeCRTSpan ∧ ‖qOne - f‖ < (17 : ℝ) / 50 :=
  ⟨QCRTPeriod9699690Certificate.certificate,
    QCRTPeriod9699690Certificate.certificate_legal,
    period9699690_error_lt_seventeen_fiftieths⟩

end RiemannResearch.RH.QExactHeadEpsilonBounds
