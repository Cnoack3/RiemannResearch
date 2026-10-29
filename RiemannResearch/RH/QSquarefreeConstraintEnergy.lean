/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeFiniteDualClosure
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# An exact finite-constraint energy certificate beyond the prescribed head

Source: the user-directed finite-head dual investigation, 29 October 2026.
The radical relation at 25 couples sites 5, 24, and 25 to a prescribed value
at 4. Completing the weighted square retains the entire omitted-site series.
This gives a lower bound, with no upper bound on legal extension energy.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeConstraintEnergy
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeFiniteDualClosure
open SquarefreeRadicalDifference UniqueFactorizationMonoid

def certificateSites : Finset ℕ := {1, 2, 3, 4, 5, 24, 25}

def omittedEnergy (F : QHilbert) : ℝ :=
  ∑' k : {n : ℕ // n ∉ certificateSites}, positiveQWeight k * qSequence F k ^ 2

theorem omittedEnergy_nonneg (F : QHilbert) : 0 ≤ omittedEnergy F :=
  tsum_nonneg (fun k => mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg _))

theorem certificate_norm_split (F : QHilbert) :
    ‖F‖ ^ 2 = (∑ k ∈ certificateSites, positiveQWeight k * qSequence F k ^ 2) +
      omittedEnergy F := by
  rw [qNorm_weighted_sq]
  exact ((qSequence_square_summable F).sum_add_tsum_subtype_compl certificateSites).symm

theorem radical_twentyfive : radical (25 : ℕ) = 5 := by
  rw [show (25 : ℕ) = 5 ^ 2 by norm_num, radical_pow 5 (by norm_num : 2 ≠ 0)]
  have hs : Squarefree (5 : ℕ) := (by norm_num : Nat.Prime 5).squarefree
  exact Nat.dvd_antisymm radical_dvd_self
    ((dvd_radical_iff hs.isRadical (by norm_num : (5 : ℕ) ≠ 0)).mpr (dvd_refl 5))

theorem constrained_three_site_relation (F : QHilbert) (hF : F ∈ radicalCompatible)
    (h4 : qSequence F 4 = 1) :
    qSequence F 5 + qSequence F 24 - qSequence F 25 = 1 := by
  have h := hF 25 (by norm_num)
  rw [radical_twentyfive] at h
  simp only [qDifference, show 25 - 1 = 24 from rfl,
    show 5 - 1 = 4 from rfl, h4] at h
  linarith

theorem three_site_Q_completion (x y z : ℝ) (h : x + y - z = 1) :
    x ^ 2 / 25 + y ^ 2 / 576 + z ^ 2 / 625 =
      1 / 1226 + (x - 25 / 1226) ^ 2 / 25 +
        (y - 576 / 1226) ^ 2 / 576 + (z + 625 / 1226) ^ 2 / 625 := by
  nlinarith

theorem three_site_Pareto_completion (x y z : ℝ) (h : x + y - z = 1) :
    x ^ 2 / 30 + y ^ 2 / 600 + z ^ 2 / 650 =
      1 / 1280 + (x - 30 / 1280) ^ 2 / 30 +
        (y - 600 / 1280) ^ 2 / 600 + (z + 650 / 1280) ^ 2 / 650 := by
  nlinarith

theorem certificate_head_energy (F : QHilbert)
    (hh : ∀ k, 0 < k → k ≤ 4 → qSequence F k = 1) :
    (∑ k ∈ certificateSites, positiveQWeight k * qSequence F k ^ 2) =
      (205 / 144 + qSequence F 5 ^ 2 / 25 + qSequence F 24 ^ 2 / 576 +
        qSequence F 25 ^ 2 / 625) / zetaTwo := by
  have h1 := hh 1 (by norm_num) (by norm_num)
  have h2 := hh 2 (by norm_num) (by norm_num)
  have h3 := hh 3 (by norm_num) (by norm_num)
  have h4 := hh 4 (by norm_num) (by norm_num)
  simp [certificateSites, positiveQWeight, h1, h2, h3, h4, -qSequence_succ]
  field_simp [ne_of_gt zetaTwo_pos]
  ring

/-- Every omitted physical site and all three completed squares are retained. -/
theorem exact_head_four_energy_completion (F : QHilbert) (hF : F ∈ radicalCompatible)
    (hh : ∀ k, 0 < k → k ≤ 4 → qSequence F k = 1) :
    ‖F‖ ^ 2 = (125737 / 88272 +
      (qSequence F 5 - 25 / 1226) ^ 2 / 25 +
      (qSequence F 24 - 576 / 1226) ^ 2 / 576 +
      (qSequence F 25 + 625 / 1226) ^ 2 / 625) / zetaTwo + omittedEnergy F := by
  have h := three_site_Q_completion (qSequence F 5) (qSequence F 24) (qSequence F 25)
    (constrained_three_site_relation F hF (hh 4 (by norm_num) (by norm_num)))
  rw [certificate_norm_split, certificate_head_energy F hh]
  congr 1
  congr 1
  linarith

theorem exact_head_four_energy_lower_bound (F : QHilbert) (hF : F ∈ radicalCompatible)
    (hh : ∀ k, 0 < k → k ≤ 4 → qSequence F k = 1) :
    125737 / (88272 * zetaTwo) ≤ ‖F‖ ^ 2 := by
  rw [exact_head_four_energy_completion F hF hh]
  have ho := omittedEnergy_nonneg F
  have hs : 0 ≤ ((qSequence F 5 - 25 / 1226) ^ 2 / 25 +
      (qSequence F 24 - 576 / 1226) ^ 2 / 576 +
      (qSequence F 25 + 625 / 1226) ^ 2 / 625) / zetaTwo := by
    exact div_nonneg (by positivity) zetaTwo_pos.le
  have he : (125737 / 88272 +
      (qSequence F 5 - 25 / 1226) ^ 2 / 25 +
      (qSequence F 24 - 576 / 1226) ^ 2 / 576 +
      (qSequence F 25 + 625 / 1226) ^ 2 / 625) / zetaTwo =
      125737 / (88272 * zetaTwo) +
      ((qSequence F 5 - 25 / 1226) ^ 2 / 25 +
      (qSequence F 24 - 576 / 1226) ^ 2 / 576 +
      (qSequence F 25 + 625 / 1226) ^ 2 / 625) / zetaTwo := by ring
  rw [he]
  linarith

theorem legal_exact_head_four_energy_lower_bound (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan)
    (hh : ∀ k, 0 < k → k ≤ 4 → qSequence F k = 1) :
    125737 / (88272 * zetaTwo) ≤ ‖F‖ ^ 2 :=
  exact_head_four_energy_lower_bound F (legal_le_radicalCompatible hF) hh

end RiemannResearch.RH.QSquarefreeConstraintEnergy
