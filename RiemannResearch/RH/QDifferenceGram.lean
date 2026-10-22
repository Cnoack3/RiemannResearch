/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Tactic.NormNum
import RiemannResearch.RH.QPhysicalDifference
import RiemannResearch.RH.CRTGCDGram
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact derivative Gram in the complete inverse-square Hilbert space

The jump formula is `SquarefreeRadicalDifference.residueFraction_difference`;
the complete divisibility mass is obtained from `CRTGCDGram.inverseSquare_multiples`.
Every mixed term and the complete infinite Q tail are retained. Squarefreeness
is unnecessary for these identities; it is a separate legality condition.

Source: user-requested full-Q period-210 certificate formalization, 18 October 2026.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QDifferenceGram

open ZetaTwoHilbert ZetaTwoProbability QPhysicalDifference
open SquarefreeRadicalDifference
open RiemannResearch.RH.Pareto.CRTSparseEnergy

/-- The Q weight restricted to the multiples of `d`. -/
def divisibilityQMass (d n : ℕ) : ℝ :=
  if d ∣ n then positiveQWeight n else 0

theorem divisibilityQMass_summable (d : ℕ) :
    Summable (divisibilityQMass d) := by
  apply Summable.of_nonneg_of_le _ _ positiveQWeight_summable
  · intro n
    unfold divisibilityQMass
    split_ifs
    · exact positiveQWeight_nonneg n
    · exact le_refl 0
  · intro n
    unfold divisibilityQMass
    split_ifs
    · exact le_refl _
    · exact positiveQWeight_nonneg n

/-- Exact normalized mass; no finite truncation or residue independence. -/
theorem divisibilityQMass_tsum (d : ℕ) (hd : 0 < d) :
    (∑' n : ℕ, divisibilityQMass d n) = 1 / (d : ℝ) ^ 2 := by
  have hZ : zetaTwo ≠ 0 := ne_of_gt zetaTwo_pos
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  have hsame : zetaTwoSeries = zetaTwo := by
    exact zetaTwo_eq_nat_sum.symm
  calc
    (∑' n : ℕ, divisibilityQMass d n) =
        (1 / zetaTwo) * (∑' n : ℕ, if d ∣ n then 1 / (n : ℝ)^2 else 0) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      by_cases hn : d ∣ n <;>
        simp only [divisibilityQMass, hn, if_true, if_false, mul_zero,
          positiveQWeight] <;> ring
    _ = (1 / zetaTwo) * (zetaTwoSeries / (d : ℝ)^2) := by
      rw [inverseSquare_multiples d hd]
    _ = 1 / (d : ℝ)^2 := by
      rw [hsame]
      field_simp [hZ, hdR]

/-- The exact rational arithmetic derivative Gram kernel. -/
def derivativeGram (d e : ℕ) : ℝ :=
  1 / ((d : ℝ) * (e : ℝ)) - 1 / ((d : ℝ) * (e : ℝ)^2) -
    1 / ((d : ℝ)^2 * (e : ℝ)) + 1 / (Nat.lcm d e : ℝ)^2

private theorem weighted_difference_product (d e n : ℕ)
    (hd : 2 ≤ d) (he : 2 ≤ e) :
    positiveQWeight n * qSequence (differenceCLM (qResidue d)) n *
        qSequence (differenceCLM (qResidue e)) n =
      positiveQWeight n / ((d : ℝ) * (e : ℝ)) -
        divisibilityQMass e n / (d : ℝ) -
        divisibilityQMass d n / (e : ℝ) +
        divisibilityQMass (Nat.lcm d e) n := by
  by_cases hn : n = 0
  · subst n
    simp [positiveQWeight, divisibilityQMass]
  · have hnpos : 1 ≤ n := by omega
    simp only [qSequence_differenceCLM, qDifference, qSequence_qResidue]
    rw [residueFraction_difference d n hd hnpos,
      residueFraction_difference e n he hnpos]
    unfold divisibilityQMass
    simp only [Nat.lcm_dvd_iff]
    by_cases hdn : d ∣ n <;> by_cases hen : e ∣ n <;>
      simp only [hdn, hen, and_self, and_false, false_and, if_true, if_false] <;> ring

/-- Complete physical derivative inner product of arbitrary legal conductors. -/
theorem inner_difference_qResidue (d e : ℕ) (hd : 2 ≤ d) (he : 2 ≤ e) :
    inner ℝ (differenceCLM (qResidue d)) (differenceCLM (qResidue e)) =
      derivativeGram d e := by
  have hdpos : 0 < d := by omega
  have hepos : 0 < e := by omega
  have hLpos : 0 < Nat.lcm d e := by
    by_contra h
    have hz : Nat.lcm d e = 0 := Nat.eq_zero_of_not_pos h
    have hp := Nat.gcd_mul_lcm d e
    rw [hz, mul_zero] at hp
    have hde : 0 < d * e := Nat.mul_pos hdpos hepos
    omega
  let A : ℕ → ℝ := fun n => positiveQWeight n / ((d : ℝ) * (e : ℝ))
  let B : ℕ → ℝ := fun n => divisibilityQMass e n / (d : ℝ)
  let C : ℕ → ℝ := fun n => divisibilityQMass d n / (e : ℝ)
  let D : ℕ → ℝ := divisibilityQMass (Nat.lcm d e)
  have hA : Summable A := positiveQWeight_summable.div_const _
  have hB : Summable B := (divisibilityQMass_summable e).div_const _
  have hC : Summable C := (divisibilityQMass_summable d).div_const _
  have hD : Summable D := divisibilityQMass_summable _
  calc
    inner ℝ (differenceCLM (qResidue d)) (differenceCLM (qResidue e)) =
        ∑' n : ℕ, (A n - B n - C n + D n) := by
      rw [qInner_weighted]
      apply tsum_congr
      intro n
      exact weighted_difference_product d e n hd he
    _ = (∑' n, A n) - (∑' n, B n) - (∑' n, C n) + (∑' n, D n) := by
      rw [((hA.sub hB).sub hC).tsum_add hD,
        (hA.sub hB).tsum_sub hC, hA.tsum_sub hB]
    _ = derivativeGram d e := by
      simp only [A, B, C, D, tsum_div_const, positiveQWeight_tsum,
        divisibilityQMass_tsum e hepos, divisibilityQMass_tsum d hdpos,
        divisibilityQMass_tsum (Nat.lcm d e) hLpos, derivativeGram]
      ring

/-- Literal unit impulse obtained by differencing the constant Q vector. -/
@[simp] theorem qSequence_difference_qOne (n : ℕ) :
    qSequence (differenceCLM qOne) n = if n = 1 then 1 else 0 := by
  rw [qSequence_differenceCLM]
  by_cases hn0 : n = 0
  · subst n
    simp [qDifference]
  · by_cases hn1 : n = 1
    · subst n
      simp only [qDifference, qSequence_qOne]
      norm_num [qOneSequence]
    · have hn2 : 2 ≤ n := by omega
      rw [qDifference_qOne n hn2, if_neg hn1]

/-- Pairing the unit impulse reads the physical first coordinate. -/
theorem inner_difference_qOne (f : QHilbert) :
    inner ℝ (differenceCLM qOne) f = (1 / zetaTwo) * qSequence f 1 := by
  rw [qInner_weighted]
  simp_rw [qSequence_difference_qOne]
  calc
    (∑' n : ℕ, positiveQWeight n * (if n = 1 then (1 : ℝ) else 0) * qSequence f n) =
        ∑' n : ℕ, if n = 1 then positiveQWeight 1 * qSequence f 1 else 0 := by
      apply tsum_congr
      intro n
      by_cases hn : n = 1
      · subst n
        simp
      · simp [hn]
    _ = (1 / zetaTwo) * qSequence f 1 := by
      simp [positiveQWeight]

/-- Exact target-residue derivative pairing. -/
theorem inner_difference_qOne_qResidue (d : ℕ) (hd : 2 ≤ d) :
    inner ℝ (differenceCLM qOne) (differenceCLM (qResidue d)) =
      (1 / zetaTwo) / (d : ℝ) := by
  have hnot : ¬ d ∣ 1 := by
    intro h
    have hd1 : d = 1 := Nat.dvd_one.mp h
    omega
  rw [inner_difference_qOne]
  simp only [qSequence_differenceCLM, qDifference, qSequence_qResidue]
  rw [residueFraction_difference d 1 hd (by omega), if_neg hnot, sub_zero]
  ring

/-- Complete Q norm of the unit impulse. -/
theorem norm_difference_qOne_sq :
    ‖differenceCLM qOne‖ ^ 2 = 1 / zetaTwo := by
  rw [← real_inner_self_eq_norm_sq, inner_difference_qOne,
    qSequence_difference_qOne]
  norm_num

end RiemannResearch.RH.QDifferenceGram
