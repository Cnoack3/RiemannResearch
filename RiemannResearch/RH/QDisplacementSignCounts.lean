/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QCofinalDisplacementMoments
import RiemannResearch.RH.SquarefreeRadicalDifference

/-!
# Counts of sites of either displacement sign

The harmonic mass on the strictly positive support of a signed displacement
is bounded by Cauchy–Schwarz using its unconditional complete-Q energy.
The existing cofinal harmonic criterion then requires only site counts.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert

/-- Sites through X carrying strictly positive mass of the chosen sign. -/
def displacementSignSupport (ε : ℝ) (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter (fun n => 0 < ε * qSequence displacement n)

/-- The complete normalized energy bounds the squared harmonic sign mass per site. -/
theorem harmonicSide_sq_le_sign_count (ε : ℝ) (hε : |ε| = 1) (X : ℕ) :
    (harmonicSide ε X) ^ 2 ≤ ((displacementSignSupport ε X).card : ℝ) *
      ∑' n : ℕ, (qSequence displacement n / (n : ℝ)) ^ 2 := by
  classical
  have hsum : harmonicSide ε X =
      ∑ n ∈ displacementSignSupport ε X, |qSequence displacement n / (n : ℝ)| := by
    rw [harmonicSide, displacementSignSupport, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hn : 0 < ε * qSequence displacement n
    · have he : ε * qSequence displacement n = |qSequence displacement n| := by
        calc
          _ = |ε * qSequence displacement n| := (abs_of_pos hn).symm
          _ = _ := by rw [abs_mul, hε, one_mul]
      have hnabs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
      rw [if_pos hn, max_eq_left hn.le, abs_div, hnabs, he]
    · simp only [if_neg hn, max_eq_right (le_of_not_gt hn), zero_div]
  have hfin := sq_sum_le_card_mul_sum_sq (s := displacementSignSupport ε X)
    (f := fun n : ℕ => |qSequence displacement n / (n : ℝ)|)
  rw [hsum]
  simp only [sq_abs] at hfin
  exact hfin.trans (mul_le_mul_of_nonneg_left
    ((SquarefreeRadicalDifference.qNormalized_square_summable displacement).sum_le_tsum
      (displacementSignSupport ε X) (fun _ _ => sq_nonneg _)) (Nat.cast_nonneg _))

/-- Polylogarithmically many sites of either sign on arbitrarily large
cutoffs suffice for RH. The sign may change with the cutoff. -/
theorem riemannHypothesis_of_cofinal_polylog_sign_count (B C : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hgood : ∃ᶠ X : ℕ in atTop, ∃ ε : ℝ, |ε| = 1 ∧
      ((displacementSignSupport ε X).card : ℝ) ≤ C * (Real.log (X : ℝ)) ^ B) :
    RiemannHypothesis := by
  let T := ∑' n : ℕ, (qSequence displacement n / (n : ℝ)) ^ 2
  have hT : 0 ≤ T := tsum_nonneg (fun _ => sq_nonneg _)
  apply riemannHypothesis_of_cofinal_harmonic_polylog (B / 2) (Real.sqrt (C * T))
    (by linarith) (Real.sqrt_nonneg _)
  apply (hgood.and_eventually (eventually_ge_atTop (1 : ℕ))).mono
  rintro X ⟨⟨ε, hε, hc⟩, hX⟩
  have hl : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
  have hmin : minimumHarmonicPrefix X ≤ harmonicSide ε X := by
    rcases le_total 0 ε with h | h
    · have he : ε = 1 := (abs_of_nonneg h).symm.trans hε
      rw [he]
      exact min_le_left _ _
    · rw [abs_of_nonpos h] at hε
      have he : ε = -1 := by linarith
      rw [he]
      exact min_le_right _ _
  apply hmin.trans
  apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hl _))
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hC hT)]
  have hp : ((Real.log (X : ℝ)) ^ (B / 2)) ^ 2 = (Real.log (X : ℝ)) ^ B := by
    rw [← Real.rpow_two, ← Real.rpow_mul hl, show B / 2 * (2 : ℝ) = B by ring]
  rw [hp]
  calc
    _ ≤ ((displacementSignSupport ε X).card : ℝ) * T := harmonicSide_sq_le_sign_count ε hε X
    _ ≤ (C * (Real.log (X : ℝ)) ^ B) * T := mul_le_mul_of_nonneg_right hc hT
    _ = _ := by ring

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
