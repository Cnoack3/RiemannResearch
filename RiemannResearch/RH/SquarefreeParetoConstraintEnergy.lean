/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.WeightedConstraintEnergy
import RiemannResearch.RH.QSquarefreeConstraintEnergy
import RiemannResearch.RH.QSquarefreeFiniteDualClosure
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ParetoDilation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete Pareto energy certificates from squarefree radical constraints

Source: user-provided general-d argument, 29 October 2026.
The existing Q-to-Pareto map preserves the entire physical sequence.
All omitted coordinates and square remainders are retained.

The norm is the actual Pareto Hilbert norm, with no assumed upper-energy bound.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.SquarefreeParetoConstraintEnergy
open ZetaTwoHilbert QSquarefreeFiniteDualClosure QSquarefreeConstraintEnergy
open ZetaTwoParetoTransfer Pareto UniqueFactorizationMonoid
open RiemannResearch.Analysis.WeightedConstraintEnergy

def paretoDenominator (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) + 1)

def pCertificateDenominator (d m : ℕ) : ℝ :=
  (d : ℝ) * ((d : ℝ) + 1) + 2 * (m : ℝ) ^ 2

def pGeneralRemainder (F : QHilbert) (d m : ℕ) : ℝ :=
  threeSiteRemainder (paretoDenominator d) (paretoDenominator (m - 1))
    (paretoDenominator m) (qSequence F d) (qSequence F (m - 1)) (qSequence F m)

def pGeneralOmittedEnergy (F : QHilbert) (d m : ℕ) : ℝ :=
  RiemannResearch.Analysis.WeightedConstraintEnergy.omittedEnergy
    paretoDenominator (qSequence F) d m

theorem paretoDenominator_nonneg (k : ℕ) : 0 ≤ paretoDenominator k := by
  unfold paretoDenominator
  positivity

theorem paretoDenominator_pos {k : ℕ} (hk : 0 < k) : 0 < paretoDenominator k := by
  unfold paretoDenominator
  positivity

theorem pGeneralRemainder_nonneg (F : QHilbert) (d m : ℕ) :
    0 ≤ pGeneralRemainder F d m :=
  threeSiteRemainder_nonneg _ _ _ _ _ _
    (paretoDenominator_nonneg _) (paretoDenominator_nonneg _) (paretoDenominator_nonneg _)

theorem pGeneralOmittedEnergy_nonneg (F : QHilbert) (d m : ℕ) :
    0 ≤ pGeneralOmittedEnergy F d m :=
  RiemannResearch.Analysis.WeightedConstraintEnergy.omittedEnergy_nonneg
    _ _ _ _ paretoDenominator_nonneg

theorem raw_P_term (F : QHilbert) (k : ℕ) :
    positiveWeight k * qSequence F k ^ 2 =
      qSequence F k ^ 2 / paretoDenominator k := by
  unfold positiveWeight paretoDenominator
  ring

theorem raw_P_summable (F : QHilbert) :
    Summable (fun k => qSequence F k ^ 2 / paretoDenominator k) :=
  (qSequence_pareto_square_summable F).congr (raw_P_term F)

theorem raw_P_energy (F : QHilbert) :
    (∑' k, qSequence F k ^ 2 / paretoDenominator k) = ‖toPareto F‖ ^ 2 := by
  rw [hilbert_norm_weighted_sq, toPareto_sequence]
  exact tsum_congr (fun k => (raw_P_term F k).symm)

theorem pareto_head_energy {d : ℕ} (hd : 2 ≤ d) :
    (∑ k ∈ Finset.Ico 1 d, 1 / paretoDenominator k) = ((d : ℝ) - 1) / d := by
  change (∑ k ∈ Finset.Ico 1 d, positiveWeight k) = _
  rw [positiveWeight_interval 1 d (by omega) (by omega)]
  norm_num
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  field_simp [hd0]

theorem pareto_three_denominators {d m : ℕ} (hm : 0 < m) :
    paretoDenominator d + paretoDenominator (m - 1) + paretoDenominator m =
      pCertificateDenominator d m := by
  unfold paretoDenominator pCertificateDenominator
  rw [Nat.cast_sub (by omega : 1 ≤ m)]
  push_cast
  ring

theorem radical_fiber_pareto_energy_completion (F : QHilbert)
    (hF : F ∈ radicalCompatible) {d m : ℕ}
    (hd : 2 ≤ d) (hm : d + 1 < m) (hr : radical m = d)
    (hh : ∀ k, 0 < k → k < d → qSequence F k = 1) :
    ‖toPareto F‖ ^ 2 = ((d : ℝ) - 1) / d +
      1 / pCertificateDenominator d m + pGeneralRemainder F d m +
      pGeneralOmittedEnergy F d m := by
  have hrel := constrained_radical_fiber_relation F hF (by omega) hr
    (hh (d - 1) (by omega) (by omega))
  have h := complete_head_three_completion paretoDenominator (qSequence F)
    hm (raw_P_summable F) hh (paretoDenominator_pos (by omega))
      (paretoDenominator_pos (by omega)) (paretoDenominator_pos (by omega)) hrel
  rw [raw_P_energy, pareto_head_energy hd,
    pareto_three_denominators (by omega : 0 < m)] at h
  exact h

theorem radical_fiber_pareto_energy_lower_bound (F : QHilbert)
    (hF : F ∈ radicalCompatible) {d m : ℕ}
    (hd : 2 ≤ d) (hm : d + 1 < m) (hr : radical m = d)
    (hh : ∀ k, 0 < k → k < d → qSequence F k = 1) :
    ((d : ℝ) - 1) / d + 1 / pCertificateDenominator d m ≤ ‖toPareto F‖ ^ 2 := by
  rw [radical_fiber_pareto_energy_completion F hF hd hm hr hh]
  exact le_trans (le_add_of_nonneg_right (pGeneralRemainder_nonneg F d m))
    (le_add_of_nonneg_right (pGeneralOmittedEnergy_nonneg F d m))

theorem pCertificateDenominator_square (d : ℕ) :
    pCertificateDenominator d (d ^ 2) = 2 * (d : ℝ) ^ 4 + (d : ℝ) ^ 2 + d := by
  unfold pCertificateDenominator
  push_cast
  ring

theorem exact_head_square_pareto_energy_completion (F : QHilbert)
    (hF : F ∈ radicalCompatible) {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hh : ∀ k, 0 < k → k < d → qSequence F k = 1) :
    ‖toPareto F‖ ^ 2 = ((d : ℝ) - 1) / d +
      1 / (2 * (d : ℝ) ^ 4 + (d : ℝ) ^ 2 + d) +
      pGeneralRemainder F d (d ^ 2) + pGeneralOmittedEnergy F d (d ^ 2) := by
  have h := radical_fiber_pareto_energy_completion F hF hd
    (show d + 1 < d ^ 2 by nlinarith) (radical_square_of_squarefree hd hs) hh
  rwa [pCertificateDenominator_square] at h

theorem exact_head_square_pareto_energy_lower_bound (F : QHilbert)
    (hF : F ∈ radicalCompatible) {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hh : ∀ k, 0 < k → k < d → qSequence F k = 1) :
    ((d : ℝ) - 1) / d + 1 / (2 * (d : ℝ) ^ 4 + (d : ℝ) ^ 2 + d) ≤
      ‖toPareto F‖ ^ 2 := by
  have h := radical_fiber_pareto_energy_lower_bound F hF hd
    (show d + 1 < d ^ 2 by nlinarith) (radical_square_of_squarefree hd hs) hh
  rwa [pCertificateDenominator_square] at h

theorem legal_exact_head_square_pareto_energy_lower_bound (F : QHilbert)
    (hF : F ∈ ZetaTwoProbability.qSquarefreeCRTSpan) {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hh : ∀ k, 0 < k → k < d → qSequence F k = 1) :
    ((d : ℝ) - 1) / d + 1 / (2 * (d : ℝ) ^ 4 + (d : ℝ) ^ 2 + d) ≤
      ‖toPareto F‖ ^ 2 :=
  exact_head_square_pareto_energy_lower_bound F (legal_le_radicalCompatible hF) hd hs hh

theorem pareto_head_five_certificate_constant :
    ((5 : ℝ) - 1) / 5 + 1 / (2 * (5 : ℝ) ^ 4 + (5 : ℝ) ^ 2 + 5) = 205 / 256 := by
  norm_num

/-- Native Pareto formulation; compatibility is stated in physical coordinates. -/
theorem pareto_exact_head_square_energy_lower_bound (F : ThresholdHilbert)
    (hF : ∀ m, 2 ≤ m →
      hilbertSequence F m - hilbertSequence F (m - 1) =
        hilbertSequence F (radical m) - hilbertSequence F (radical m - 1))
    {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hh : ∀ k, 0 < k → k < d → hilbertSequence F k = 1) :
    ((d : ℝ) - 1) / d + 1 / (2 * (d : ℝ) ^ 4 + (d : ℝ) ^ 2 + d) ≤ ‖F‖ ^ 2 := by
  have hq : QParetoEquivalence.toQ F ∈ radicalCompatible := by
    intro m hm
    simpa only [SquarefreeRadicalDifference.qDifference,
      QParetoEquivalence.toQ_sequence] using hF m hm
  have h := exact_head_square_pareto_energy_lower_bound
    (QParetoEquivalence.toQ F) hq hd hs (by
      simpa only [QParetoEquivalence.toQ_sequence] using hh)
  simpa only [QParetoEquivalence.toPareto_toQ] using h

end RiemannResearch.RH.SquarefreeParetoConstraintEnergy
