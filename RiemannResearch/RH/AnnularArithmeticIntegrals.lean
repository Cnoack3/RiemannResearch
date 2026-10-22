import RiemannResearch.RH.AnnularArithmeticWeight
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

Expected companion module:
`RiemannResearch.RH.AnnularArithmeticWeight` from AnnularArithmeticWeightDraft.lean.

The interval-integral APIs were checked source-only at pinned Mathlib commit
51e6992efd06126df61a496bebf8f49482a4e129:
* Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean: global integral_pow, integral_id.
* Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean: integral_congr,
  integral_add, integral_const_mul, integral_const, integral_add_adjacent_intervals,
  Continuous.intervalIntegrable.

All polynomial integrals below are actual Lebesgue interval integrals, not a
symbolic surrogate or hypotheses supplied as numerical certificates.
-/

open MeasureTheory Set

namespace RiemannResearch.RH

theorem continuous_rieszTwoWeight : Continuous rieszTwoWeight := by
  unfold rieszTwoWeight
  exact ((continuous_const.sub continuous_id).sup continuous_const).pow 2

theorem continuous_annularArithmeticWeight : Continuous annularArithmeticWeight := by
  have h2 : Continuous (fun u : ℝ => rieszTwoWeight (2 * u)) :=
    continuous_rieszTwoWeight.comp (continuous_const.mul continuous_id)
  have h4 : Continuous (fun u : ℝ => rieszTwoWeight (4 * u)) :=
    continuous_rieszTwoWeight.comp (continuous_const.mul continuous_id)
  have h8 : Continuous (fun u : ℝ => rieszTwoWeight (8 * u)) :=
    continuous_rieszTwoWeight.comp (continuous_const.mul continuous_id)
  unfold annularArithmeticWeight
  exact ((continuous_rieszTwoWeight.sub (continuous_const.mul h2)).add
    (continuous_const.mul h4)).sub (continuous_const.mul h8)

theorem intervalIntegral_quartic (a b c0 c1 c2 c3 c4 : ℝ) :
    (∫ u in a..b, c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4) =
      (b - a) * c0 + c1 * (b ^ 2 - a ^ 2) / 2 +
        c2 * (b ^ 3 - a ^ 3) / 3 + c3 * (b ^ 4 - a ^ 4) / 4 +
        c4 * (b ^ 5 - a ^ 5) / 5 := by
  have h0 : IntervalIntegrable (fun _ : ℝ => c0) volume a b :=
    continuous_const.intervalIntegrable a b
  have h1 : IntervalIntegrable (fun u : ℝ => c1 * u) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun u : ℝ => c2 * u ^ 2) volume a b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable a b
  have h3 : IntervalIntegrable (fun u : ℝ => c3 * u ^ 3) volume a b :=
    (continuous_const.mul (continuous_id.pow 3)).intervalIntegrable a b
  have h4 : IntervalIntegrable (fun u : ℝ => c4 * u ^ 4) volume a b :=
    (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable a b
  rw [intervalIntegral.integral_add (((h0.add h1).add h2).add h3) h4,
    intervalIntegral.integral_add ((h0.add h1).add h2) h3,
    intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1]
  rw [intervalIntegral.integral_const_mul c1 (fun u : ℝ => u),
    intervalIntegral.integral_const_mul c2 (fun u : ℝ => u ^ 2),
    intervalIntegral.integral_const_mul c3 (fun u : ℝ => u ^ 3),
    intervalIntegral.integral_const_mul c4 (fun u : ℝ => u ^ 4)]
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    _root_.integral_id, _root_.integral_pow, smul_eq_mul]
  ring

theorem integral_annularArithmeticWeight_first :
    (∫ u in (1 / 8 : ℝ)..1 / 4, annularArithmeticWeight u) = 1 / 192 := by
  have heq : (∫ u in (1 / 8 : ℝ)..1 / 4, annularArithmeticWeight u) =
      ∫ u in (1 / 8 : ℝ)..1 / 4,
        (1 / 8 : ℝ) + (-2) * u + 8 * u ^ 2 + 0 * u ^ 3 + 0 * u ^ 4 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)] at hu
    dsimp only
    rw [annularArithmeticWeight_first_piece hu.1 hu.2]
    ring
  rw [heq, intervalIntegral_quartic]
  norm_num

theorem integral_annularArithmeticWeight_middle :
    (∫ u in (1 / 4 : ℝ)..1 / 2, annularArithmeticWeight u) = 1 / 16 := by
  have heq : (∫ u in (1 / 4 : ℝ)..1 / 2, annularArithmeticWeight u) =
      ∫ u in (1 / 4 : ℝ)..1 / 2,
        -(3 / 4 : ℝ) + 5 * u + (-6) * u ^ 2 + 0 * u ^ 3 + 0 * u ^ 4 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] at hu
    dsimp only
    rw [annularArithmeticWeight_middle_piece hu.1 hu.2]
    ring
  rw [heq, intervalIntegral_quartic]
  norm_num

theorem integral_annularArithmeticWeight_last :
    (∫ u in (1 / 2 : ℝ)..1, annularArithmeticWeight u) = 1 / 24 := by
  have heq : (∫ u in (1 / 2 : ℝ)..1, annularArithmeticWeight u) =
      ∫ u in (1 / 2 : ℝ)..1,
        (1 : ℝ) + (-2) * u + 1 * u ^ 2 + 0 * u ^ 3 + 0 * u ^ 4 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hu
    dsimp only
    rw [annularArithmeticWeight_last_piece hu.1 hu.2]
    ring
  rw [heq, intervalIntegral_quartic]
  norm_num

theorem integral_annularArithmeticWeight :
    (∫ u in (1 / 8 : ℝ)..1, annularArithmeticWeight u) = 7 / 64 := by
  have h1 : IntervalIntegrable annularArithmeticWeight volume (1 / 8 : ℝ) (1 / 4) :=
    continuous_annularArithmeticWeight.intervalIntegrable _ _
  have h2 : IntervalIntegrable annularArithmeticWeight volume (1 / 4 : ℝ) (1 / 2) :=
    continuous_annularArithmeticWeight.intervalIntegrable _ _
  have h3 : IntervalIntegrable annularArithmeticWeight volume (1 / 2 : ℝ) 1 :=
    continuous_annularArithmeticWeight.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 (h2.trans h3),
    ← intervalIntegral.integral_add_adjacent_intervals h2 h3,
    integral_annularArithmeticWeight_first,
    integral_annularArithmeticWeight_middle,
    integral_annularArithmeticWeight_last]
  norm_num

theorem integral_annularArithmeticWeight_sq_first :
    (∫ u in (1 / 8 : ℝ)..1 / 4, annularArithmeticWeight u ^ 2) = 1 / 2560 := by
  have heq : (∫ u in (1 / 8 : ℝ)..1 / 4, annularArithmeticWeight u ^ 2) =
      ∫ u in (1 / 8 : ℝ)..1 / 4,
        (1 / 64 : ℝ) + (-1 / 2) * u + 6 * u ^ 2 + (-32) * u ^ 3 + 64 * u ^ 4 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1 / 8 : ℝ) ≤ 1 / 4)] at hu
    dsimp only
    rw [annularArithmeticWeight_first_piece hu.1 hu.2]
    ring
  rw [heq, intervalIntegral_quartic]
  norm_num

theorem integral_annularArithmeticWeight_sq_middle :
    (∫ u in (1 / 4 : ℝ)..1 / 2, annularArithmeticWeight u ^ 2) = 31 / 1920 := by
  have heq : (∫ u in (1 / 4 : ℝ)..1 / 2, annularArithmeticWeight u ^ 2) =
      ∫ u in (1 / 4 : ℝ)..1 / 2,
        (9 / 16 : ℝ) + (-15 / 2) * u + 34 * u ^ 2 + (-60) * u ^ 3 + 36 * u ^ 4 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)] at hu
    dsimp only
    rw [annularArithmeticWeight_middle_piece hu.1 hu.2]
    ring
  rw [heq, intervalIntegral_quartic]
  norm_num

theorem integral_annularArithmeticWeight_sq_last :
    (∫ u in (1 / 2 : ℝ)..1, annularArithmeticWeight u ^ 2) = 1 / 160 := by
  have heq : (∫ u in (1 / 2 : ℝ)..1, annularArithmeticWeight u ^ 2) =
      ∫ u in (1 / 2 : ℝ)..1,
        (1 : ℝ) + (-4) * u + 6 * u ^ 2 + (-4) * u ^ 3 + 1 * u ^ 4 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hu
    dsimp only
    rw [annularArithmeticWeight_last_piece hu.1 hu.2]
    ring
  rw [heq, intervalIntegral_quartic]
  norm_num

theorem integral_annularArithmeticWeight_sq :
    (∫ u in (1 / 8 : ℝ)..1, annularArithmeticWeight u ^ 2) = 35 / 1536 := by
  have h1 : IntervalIntegrable (fun u : ℝ => annularArithmeticWeight u ^ 2)
      volume (1 / 8 : ℝ) (1 / 4) :=
    (continuous_annularArithmeticWeight.pow 2).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun u : ℝ => annularArithmeticWeight u ^ 2)
      volume (1 / 4 : ℝ) (1 / 2) :=
    (continuous_annularArithmeticWeight.pow 2).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun u : ℝ => annularArithmeticWeight u ^ 2)
      volume (1 / 2 : ℝ) 1 :=
    (continuous_annularArithmeticWeight.pow 2).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 (h2.trans h3),
    ← intervalIntegral.integral_add_adjacent_intervals h2 h3,
    integral_annularArithmeticWeight_sq_first,
    integral_annularArithmeticWeight_sq_middle,
    integral_annularArithmeticWeight_sq_last]
  norm_num

end RiemannResearch.RH
