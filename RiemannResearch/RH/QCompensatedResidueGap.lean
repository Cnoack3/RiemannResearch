/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DiscreteFloorGap
import RiemannResearch.RH.QSquarefreeHeadStep
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete - Q compensated residue energy controlled by the conductor gap

Source: the user - provided minimum - energy remaining - obligations handoff,
29 October 2026, priorities 1 and 3. The elementary argument here retains
the actual signed floor identity and bounds the complete infinite tail.
For 2 <= n < r <= 2n, delta = r - n, the final bound is
delta * (7 + log(n / delta)) / (zeta(2) * n ^ 2).
No prime or squarefree gap theorem is assumed. Squarefree dictionary
membership and the actual optimizer application belong to QSquarefreeGapHeadCost.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCompensatedResidueGap
open ZetaTwoHilbert QSquarefreeLatticePackets ArithmeticCumulative
open RiemannResearch.Analysis.DiscreteFloorGap

theorem floor_gap_sq (n r k : ℕ) (hn : 0 < n) (hnr : n ≤ r) (hr2 : r ≤ 2 * n) :
    (qSequence (compensatedResidue n r) k) ^ 2 ≤
      ((k / n : ℕ) : ℝ) - ((k / r : ℕ) : ℝ) + (((r : ℝ) - n) / n * ((k / r : ℕ) : ℝ)) ^ 2 := by
  have hr : 0 < r := lt_of_lt_of_le hn hnr
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hnrR : (n : ℝ) ≤ r := by exact_mod_cast hnr
  have hle : k / r ≤ k / n := Nat.div_le_div_left hnr hn
  have hmodn : k % n + n * (k / n) = k := Nat.mod_add_div k n
  have hmodr : k % r + r * (k / r) = k := Nat.mod_add_div k r
  have hmodnR : ((k % n : ℕ) : ℝ) + n * ((k / n : ℕ) : ℝ) = k := by exact_mod_cast hmodn
  have hmodrR : ((k % r : ℕ) : ℝ) + r * ((k / r : ℕ) : ℝ) = k := by exact_mod_cast hmodr
  have hseq : qSequence (compensatedResidue n r) k =
      ((r : ℝ) - n) / n * ((k / r : ℕ) : ℝ) - (((k / n : ℕ) : ℝ) - ((k / r : ℕ) : ℝ)) := by
    rw [compensatedResidue_sequence]
    unfold residueFraction
    field_simp
    nlinarith
  have hD : 0 ≤ ((k / n : ℕ) : ℝ) - ((k / r : ℕ) : ℝ) := sub_nonneg.mpr (by exact_mod_cast hle)
  have hbound : (((k / n : ℕ) : ℝ) - ((k / r : ℕ) : ℝ)) ≤
      1 + 2 * (((r : ℝ) - n) / n * ((k / r : ℕ) : ℝ)) := by
    by_cases hb : k / r = 0
    · have hk : k < r := (Nat.div_eq_zero_iff).mp hb |>.resolve_left (ne_of_gt hr)
      have ha : k / n ≤ 1 := by
        have := (Nat.div_lt_iff_lt_mul hn).mpr (show k < 2 * n by omega)
        omega
      simp only [hb, Nat.cast_zero, sub_zero, mul_zero, add_zero]
      exact_mod_cast ha
    · have hb1 : (1 : ℝ) ≤ ((k / r : ℕ) : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hb)
      have hm : ((k % r : ℕ) : ℝ) < r := by exact_mod_cast Nat.mod_lt k hr
      have hm0 := Nat.cast_nonneg (α := ℝ) (k % n)
      have ht : (((r : ℝ) - n) / n * ((k / r : ℕ) : ℝ)) * n =
          ((r : ℝ) - n) * ((k / r : ℕ) : ℝ) := by field_simp
      nlinarith [mul_nonneg (sub_nonneg.mpr hnrR) (sub_nonneg.mpr hb1)]
  rw [hseq]
  nlinarith [mul_nonneg hD (sub_nonneg.mpr hbound)]


theorem compensatedResidue_gap_energy (n r J : ℕ) (hn : 1 < n)
    (hnr : n ≤ r) (hr2 : r ≤ 2 * n) (hJ : 0 < J) :
    ‖compensatedResidue n r‖^2 ≤ (1 / ZetaTwoProbability.zetaTwo) * ((((r : ℝ) - n) / (n : ℝ) ^ 2) * (∑ j ∈ Finset.range (J + 1), (1 : ℝ) / (j : ℝ)) + ((J * n + 1 : ℕ) : ℝ) * (((r : ℝ) - n) / ((n : ℝ) * r)) ^ 2 + ((r : ℝ) / n) ^ 2 / ((J * n : ℕ) : ℝ)) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hr : 0 < r := lt_of_lt_of_le hn0 hnr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hδ : 0 ≤ (r : ℝ) - n := sub_nonneg.mpr (by exact_mod_cast hnr)
  have htail := QFiniteEnergyBounds.norm_sq_le_head_tail (compensatedResidue n r)
    (J * n) (Nat.mul_pos hJ hn0) ((r : ℝ) / n) (by positivity)
    (QSquarefreeHeadStep.compensatedResidue_abs_le n r hn0 hnr)
  have hhead :
      (∑ k ∈ Finset.range (J * n),
        (qSequence (compensatedResidue n r) (k + 1)) ^ 2 / (k + 1 : ℝ) ^ 2) =
      ∑ k ∈ Finset.range (J * n + 1),
        (qSequence (compensatedResidue n r) k) ^ 2 / (k : ℝ) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp only [qSequence_zero, zero_pow (by decide : 2 ≠ 0), zero_div,
      add_zero, Nat.cast_add, Nat.cast_one]
  have hp (k : ℕ) :
      (qSequence (compensatedResidue n r) k) ^ 2 / (k : ℝ) ^ 2 ≤
        (((k / n : ℕ) : ℝ) - ((k / r : ℕ) : ℝ)) / (k : ℝ) ^ 2 + (((r : ℝ) - n) / ((n : ℝ) * r)) ^ 2 := by
    by_cases hk : k = 0
    · subst k
      simp only [qSequence_zero, zero_pow (by decide : 2 ≠ 0), Nat.cast_zero,
        zero_div, Nat.zero_div, sub_self, zero_add]
      positivity
    have hkR : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hb : ((k / r : ℕ) : ℝ) ≤ (k : ℝ) / r := by
      apply (le_div_iff₀ hrR).mpr
      exact_mod_cast Nat.div_mul_le_self k r
    have hmul := mul_le_mul_of_nonneg_left hb (div_nonneg hδ hnR.le)
    have hbase : (((r : ℝ) - n) / n * ((k / r : ℕ) : ℝ)) / (k : ℝ) ≤
        ((r : ℝ) - n) / ((n : ℝ) * r) := by
      apply (div_le_iff₀ hkR).mpr
      convert hmul using 1 <;> field_simp
    have hsquare : ((((r : ℝ) - n) / n * ((k / r : ℕ) : ℝ)) / (k : ℝ)) ^ 2 ≤
        (((r : ℝ) - n) / ((n : ℝ) * r)) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr hbase
    have hv := div_le_div_of_nonneg_right (floor_gap_sq n r k hn0 hnr hr2)
      (sq_nonneg (k : ℝ))
    rw [add_div] at hv
    rw [div_pow] at hsquare
    linarith
  have hfinite := Finset.sum_le_sum (s := Finset.range (J * n + 1)) (fun k _ => hp k)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hfinite
  have hfloor := floor_gap_sum_le n r (J + 1) (J * n + 1) hn0 hnr (by nlinarith)
  have hsum :
      (∑ j ∈ Finset.range (J + 1), ((r : ℝ) - n) / ((j : ℝ) * (n : ℝ) ^ 2)) =
      (((r : ℝ) - n) / (n : ℝ) ^ 2) * (∑ j ∈ Finset.range (J + 1), (1 : ℝ) / (j : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum] at hfloor
  rw [hhead] at htail
  apply htail.trans
  apply mul_le_mul_of_nonneg_left _ (one_div_pos.mpr ZetaTwoProbability.zetaTwo_pos).le
  linarith

theorem compensatedResidue_gap_log_bound (n r : ℕ) (hn : 1 < n)
    (hnr : n < r) (hr2 : r ≤ 2 * n) :
    ‖compensatedResidue n r‖^2 ≤
      (1 / ZetaTwoProbability.zetaTwo) * (((r : ℝ) - n) / (n : ℝ) ^ 2 * (7 + Real.log ((n : ℝ) / ((r : ℝ) - n)))) := by
  let d := r - n
  let J := n / d + 1
  have hd : 0 < d := by dsimp [d]; omega
  have hJ : 0 < J := Nat.succ_pos _
  have hcast : (d : ℝ) = (r : ℝ) - n := Nat.cast_sub hnr.le
  have hlow : n ≤ J * d := by
    have hm := Nat.mod_lt n hd
    have he := Nat.mod_add_div n d
    dsimp [J]
    nlinarith
  have hupp : J * d ≤ r := by
    have he := Nat.div_mul_le_self n d
    have hnd : n + d = r := by dsimp [d]; omega
    dsimp [J]
    nlinarith
  have hsum : (∑ j ∈ Finset.range (J + 1), (1 : ℝ) / (j : ℝ)) = (harmonic J : ℝ) := by
    rw [Finset.sum_range_succ']
    simp [harmonic]
  have he := compensatedResidue_gap_energy n r J hn hnr.le hr2 hJ
  rw [hsum] at he
  have hH := harmonic_le_one_add_log J
  have hdR : (0 : ℝ) < (r : ℝ) - n := sub_pos.mpr (by exact_mod_cast hnr)
  have hHmul := mul_le_mul_of_nonneg_left hH
    (show 0 ≤ ((r : ℝ) - n) / (n : ℝ) ^ 2 by positivity)
  have hg := gap_majorant_log (n : ℝ) (r : ℝ) (J : ℝ)
    (by exact_mod_cast (show 1 ≤ n by omega))
    (by exact_mod_cast hnr) (by exact_mod_cast hr2)
    (by exact_mod_cast hJ)
    (by rw [← hcast]; exact_mod_cast hlow)
    (by rw [← hcast]; exact_mod_cast hupp)
  have hmajor :
      (((r : ℝ) - n) / (n : ℝ) ^ 2) * (harmonic J : ℝ) + ((J * n + 1 : ℕ) : ℝ) * (((r : ℝ) - n) / ((n : ℝ) * r)) ^ 2 + ((r : ℝ) / n) ^ 2 / ((J * n : ℕ) : ℝ) ≤
      ((r : ℝ) - n) / (n : ℝ) ^ 2 * (7 + Real.log ((n : ℝ) / ((r : ℝ) - n))) := by
    push_cast
    linarith
  exact he.trans (mul_le_mul_of_nonneg_left hmajor
    (one_div_pos.mpr ZetaTwoProbability.zetaTwo_pos).le)


end RiemannResearch.RH.QCompensatedResidueGap
