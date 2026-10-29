/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.WeightedConstraintEnergy
import RiemannResearch.RH.QSquarefreeFiniteDualClosure
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
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
  simpa only [show (25 : ℝ) + 576 + 625 = 1226 by norm_num, one_pow, mul_one] using
    RiemannResearch.Analysis.WeightedConstraintEnergy.three_site_completion
      25 576 625 x y z 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

theorem three_site_Pareto_completion (x y z : ℝ) (h : x + y - z = 1) :
    x ^ 2 / 30 + y ^ 2 / 600 + z ^ 2 / 650 =
      1 / 1280 + (x - 30 / 1280) ^ 2 / 30 +
        (y - 600 / 1280) ^ 2 / 600 + (z + 650 / 1280) ^ 2 / 650 := by
  simpa only [show (30 : ℝ) + 600 + 650 = 1280 by norm_num, one_pow, mul_one] using
    RiemannResearch.Analysis.WeightedConstraintEnergy.three_site_completion
      30 600 650 x y z 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h

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

/-!
## General parameterized certificates

The complete identities retain all omitted coordinates.
-/

/-- The radical constraint at a square of any squarefree integer. -/
theorem radical_square_of_squarefree {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d) :
    radical (d ^ 2) = d := by
  rw [radical_pow d (by norm_num : 2 ≠ 0)]
  exact Nat.dvd_antisymm radical_dvd_self
    ((dvd_radical_iff hs.isRadical (by omega : d ≠ 0)).mpr (dvd_refl d))

/-- Any later coordinate in the radical fibre gives the same signed relation. -/
theorem constrained_radical_fiber_relation (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d m : ℕ} (hm : 2 ≤ m) (hr : radical m = d)
    (hh : qSequence F (d - 1) = 1) :
    qSequence F d + qSequence F (m - 1) - qSequence F m = 1 := by
  have h := hF m hm
  rw [hr] at h
  simp only [qDifference, hh] at h
  linarith

theorem constrained_square_relation (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hh : qSequence F (d - 1) = 1) :
    qSequence F d + qSequence F (d ^ 2 - 1) - qSequence F (d ^ 2) = 1 := by
  exact constrained_radical_fiber_relation F hF (by nlinarith)
    (radical_square_of_squarefree hd hs) hh

open RiemannResearch.Analysis.WeightedConstraintEnergy

def inverseSquareDenominator (k : ℕ) : ℝ := (k : ℝ) ^ 2

def qHeadEnergy (d : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 d, 1 / (k : ℝ) ^ 2

def qCertificateDenominator (d m : ℕ) : ℝ :=
  (d : ℝ) ^ 2 + ((m - 1 : ℕ) : ℝ) ^ 2 + (m : ℝ) ^ 2

def qGeneralRemainder (F : QHilbert) (d m : ℕ) : ℝ :=
  threeSiteRemainder ((d : ℝ) ^ 2) (((m - 1 : ℕ) : ℝ) ^ 2) ((m : ℝ) ^ 2)
    (qSequence F d) (qSequence F (m - 1)) (qSequence F m)

def qGeneralOmittedEnergy (F : QHilbert) (d m : ℕ) : ℝ :=
  RiemannResearch.Analysis.WeightedConstraintEnergy.omittedEnergy
    inverseSquareDenominator (qSequence F) d m / zetaTwo

theorem qGeneralRemainder_nonneg (F : QHilbert) (d m : ℕ) :
    0 ≤ qGeneralRemainder F d m :=
  threeSiteRemainder_nonneg _ _ _ _ _ _ (sq_nonneg _) (sq_nonneg _) (sq_nonneg _)

theorem qGeneralOmittedEnergy_nonneg (F : QHilbert) (d m : ℕ) :
    0 ≤ qGeneralOmittedEnergy F d m :=
  div_nonneg (RiemannResearch.Analysis.WeightedConstraintEnergy.omittedEnergy_nonneg
    _ _ _ _ (fun k => sq_nonneg (k : ℝ))) zetaTwo_pos.le

theorem raw_Q_term (F : QHilbert) (k : ℕ) :
    zetaTwo * (positiveQWeight k * qSequence F k ^ 2) =
      qSequence F k ^ 2 / inverseSquareDenominator k := by
  unfold positiveQWeight inverseSquareDenominator
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  calc
    _ = (zetaTwo * zetaTwo⁻¹) * (qSequence F k ^ 2 * ((k : ℝ) ^ 2)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (ne_of_gt zetaTwo_pos), one_mul]

theorem raw_Q_summable (F : QHilbert) :
    Summable (fun k => qSequence F k ^ 2 / inverseSquareDenominator k) := by
  exact ((qSequence_square_summable F).mul_left zetaTwo).congr (raw_Q_term F)

theorem raw_Q_energy (F : QHilbert) :
    (∑' k, qSequence F k ^ 2 / inverseSquareDenominator k) =
      zetaTwo * ‖F‖ ^ 2 := by
  calc
    _ = ∑' k, zetaTwo * (positiveQWeight k * qSequence F k ^ 2) :=
      tsum_congr (fun k => (raw_Q_term F k).symm)
    _ = zetaTwo * (∑' k, positiveQWeight k * qSequence F k ^ 2) :=
      (qSequence_square_summable F).tsum_mul_left zetaTwo
    _ = _ := by rw [← qNorm_weighted_sq]

/-- Complete Q energy: the prescribed head, the optimal three-site contribution,
all three square remainders, and the entire omitted-coordinate series. -/
theorem radical_fiber_energy_completion (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d m : ℕ} (hd : 2 ≤ d) (hm : d + 1 < m) (hr : radical m = d)
    (hh : ∀ k, 0 < k → k < d → qSequence F k = 1) :
    ‖F‖ ^ 2 = (qHeadEnergy d + 1 / qCertificateDenominator d m +
      qGeneralRemainder F d m) / zetaTwo + qGeneralOmittedEnergy F d m := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hm1R : (0 : ℝ) < (m - 1 : ℕ) := by
    exact_mod_cast (show 0 < m - 1 by omega)
  have hrel := constrained_radical_fiber_relation F hF (by omega) hr
    (hh (d - 1) (by omega) (by omega))
  have h := complete_head_three_completion inverseSquareDenominator (qSequence F)
    hm (raw_Q_summable F) hh (sq_pos_of_pos hdR)
      (sq_pos_of_pos hm1R) (sq_pos_of_pos hmR) hrel
  rw [raw_Q_energy] at h
  change zetaTwo * ‖F‖ ^ 2 =
    qHeadEnergy d + 1 / qCertificateDenominator d m + qGeneralRemainder F d m +
      RiemannResearch.Analysis.WeightedConstraintEnergy.omittedEnergy
        inverseSquareDenominator (qSequence F) d m at h
  unfold qGeneralOmittedEnergy
  rw [← add_div]
  apply (eq_div_iff (ne_of_gt zetaTwo_pos)).mpr
  simpa only [mul_comm] using h

theorem radical_fiber_energy_lower_bound (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d m : ℕ} (hd : 2 ≤ d) (hm : d + 1 < m) (hr : radical m = d)
    (hh : ∀ k, 0 < k → k < d → qSequence F k = 1) :
    (qHeadEnergy d + 1 / qCertificateDenominator d m) / zetaTwo ≤ ‖F‖ ^ 2 := by
  have hR := div_nonneg (qGeneralRemainder_nonneg F d m) zetaTwo_pos.le
  have hO := qGeneralOmittedEnergy_nonneg F d m
  rw [radical_fiber_energy_completion F hF hd hm hr hh]
  simp only [add_div]
  exact le_trans (le_add_of_nonneg_right hR) (le_add_of_nonneg_right hO)

theorem qCertificateDenominator_square {d : ℕ} (hd : 2 ≤ d) :
    qCertificateDenominator d (d ^ 2) = 2 * (d : ℝ) ^ 4 - (d : ℝ) ^ 2 + 1 := by
  unfold qCertificateDenominator
  rw [Nat.cast_sub (by nlinarith : 1 ≤ d ^ 2)]
  push_cast
  ring

theorem exact_head_square_energy_completion (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hh : ∀ k, 0 < k → k < d → qSequence F k = 1) :
    ‖F‖ ^ 2 = (qHeadEnergy d + 1 / (2 * (d : ℝ) ^ 4 - (d : ℝ) ^ 2 + 1) +
      qGeneralRemainder F d (d ^ 2)) / zetaTwo +
      qGeneralOmittedEnergy F d (d ^ 2) := by
  have h := radical_fiber_energy_completion F hF hd
    (show d + 1 < d ^ 2 by nlinarith) (radical_square_of_squarefree hd hs) hh
  rwa [qCertificateDenominator_square hd] at h

/-- The requested parameterized complete-Q lower bound. -/
theorem exact_head_square_energy_lower_bound (F : QHilbert) (hF : F ∈ radicalCompatible)
    {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hh : ∀ k, 0 < k → k < d → qSequence F k = 1) :
    ((∑ k ∈ Finset.Ico 1 d, 1 / (k : ℝ) ^ 2) +
      1 / (2 * (d : ℝ) ^ 4 - (d : ℝ) ^ 2 + 1)) / zetaTwo ≤ ‖F‖ ^ 2 := by
  have h := radical_fiber_energy_lower_bound F hF hd
    (show d + 1 < d ^ 2 by nlinarith) (radical_square_of_squarefree hd hs) hh
  rw [qCertificateDenominator_square hd] at h
  exact h

theorem legal_exact_head_square_energy_lower_bound (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan) {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hh : ∀ k, 0 < k → k < d → qSequence F k = 1) :
    ((∑ k ∈ Finset.Ico 1 d, 1 / (k : ℝ) ^ 2) +
      1 / (2 * (d : ℝ) ^ 4 - (d : ℝ) ^ 2 + 1)) / zetaTwo ≤ ‖F‖ ^ 2 :=
  exact_head_square_energy_lower_bound F (legal_le_radicalCompatible hF) hd hs hh

theorem closed_legal_exact_head_square_energy_lower_bound (F : QHilbert)
    (hF : F ∈ qSquarefreeCRTSpan.topologicalClosure)
    {d : ℕ} (hd : 2 ≤ d) (hs : Squarefree d)
    (hh : ∀ k, 0 < k → k < d → qSequence F k = 1) :
    ((∑ k ∈ Finset.Ico 1 d, 1 / (k : ℝ) ^ 2) +
      1 / (2 * (d : ℝ) ^ 4 - (d : ℝ) ^ 2 + 1)) / zetaTwo ≤ ‖F‖ ^ 2 :=
  exact_head_square_energy_lower_bound F (legalClosure_le_radicalCompatible hF) hd hs hh

/-- Exact d=5 consistency check, with no numerical approximation. -/
theorem head_five_certificate_constants :
    qHeadEnergy 5 = 205 / 144 ∧ qCertificateDenominator 5 25 = 1226 := by
  have hI : Finset.Ico 1 5 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  norm_num [qHeadEnergy, qCertificateDenominator, hI]


end RiemannResearch.RH.QSquarefreeConstraintEnergy
