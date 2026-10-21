/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParityBasis
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact complete-Q conductor-three moments

Source: user-provided legal-basis continuation, 21 October 2026.
Residue arithmetic and full weighted reindexing determine the mean-dependent
parity coefficient and second moment. These identities supply the normalization
of the first new squarefree legal Gram–Schmidt direction.
-/
noncomputable section
open scoped RealInnerProductSpace
namespace RiemannResearch.RH.ZetaTwoParitySignal
open ZetaTwoHilbert ArithmeticCumulative

private def nondivThreeWeight (n : ℕ) : ℝ := if 3 ∣ n then 0 else positiveQWeight n

private theorem divThreeWeight_summable :
    Summable (fun n : ℕ => if 3 ∣ n then positiveQWeight n else 0) := by
  apply Summable.of_nonneg_of_le _ _ positiveQWeight_summable
  · intro n
    by_cases hd : 3 ∣ n <;> simp [hd, positiveQWeight_nonneg]
  · intro n
    by_cases hd : 3 ∣ n <;> simp [hd, positiveQWeight_nonneg]

private theorem nondivThreeWeight_summable : Summable nondivThreeWeight := by
  apply Summable.of_nonneg_of_le _ _ positiveQWeight_summable
  · intro n
    by_cases hd : 3 ∣ n <;> simp [nondivThreeWeight, hd, positiveQWeight_nonneg]
  · intro n
    by_cases hd : 3 ∣ n <;> simp [nondivThreeWeight, hd, positiveQWeight_nonneg]

private theorem nondivThreeWeight_tsum : (∑' n, nondivThreeWeight n) = (8 / 9 : ℝ) := by
  have he : nondivThreeWeight = fun n : ℕ =>
      positiveQWeight n - (if 3 ∣ n then positiveQWeight n else 0) := by
    funext n
    by_cases hd : 3 ∣ n <;> simp [nondivThreeWeight, hd]
  rw [he, Summable.tsum_sub positiveQWeight_summable divThreeWeight_summable,
    positiveQWeight_tsum, positiveQWeight_dvd_tsum 3 (by norm_num)]
  norm_num

private theorem residue_three_double (n : ℕ) :
    residueFraction 3 (2 * n) =
      (if 3 ∣ n then 0 else 1) - residueFraction 3 n := by
  have hn := Nat.mod_lt n (by norm_num : 0 < 3)
  have hc : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hc with h | h | h <;>
    norm_num [residueFraction, Nat.mul_mod, h, Nat.dvd_iff_mod_eq_zero]

private theorem residue_three_square (n : ℕ) :
    residueFraction 3 n ^ 2 =
      residueFraction 3 n - (2 / 9) * (if 3 ∣ n then 0 else 1) := by
  have hn := Nat.mod_lt n (by norm_num : 0 < 3)
  have hc : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hc with h | h | h <;>
    norm_num [residueFraction, h, Nat.dvd_iff_mod_eq_zero]

private theorem weightedResidueThree_summable :
    Summable (fun n : ℕ => positiveQWeight n * residueFraction 3 n) := by
  simpa only [qSequence_qResidue] using qWeighted_summable (qResidue 3)

/-- The even-index reindexing retains the entire inverse-square tail. -/
theorem qResidue_three_inner_even_exact :
    inner ℝ (qResidue 3) qEven =
      (8 / 9 - inner ℝ (qResidue 3) qOne) / 4 := by
  rw [qInner_even_reindex]
  have he : (fun n : ℕ => positiveQWeight (2 * n) *
      qSequence (qResidue 3) (2 * n)) =
      fun n => (1 / 4 : ℝ) *
        (nondivThreeWeight n - positiveQWeight n * residueFraction 3 n) := by
    funext n
    rw [qSequence_qResidue, positiveQWeight_mul, residue_three_double]
    by_cases hd : 3 ∣ n <;> simp [nondivThreeWeight, hd] <;> ring
  rw [he, tsum_mul_left,
    Summable.tsum_sub nondivThreeWeight_summable weightedResidueThree_summable,
    nondivThreeWeight_tsum, qInner_one_tsum, qSequence_qResidue]
  ring

theorem qResidue_three_inner_parity_exact :
    inner ℝ (qResidue 3) parityUnit =
      (8 / 9 - 2 * inner ℝ (qResidue 3) qOne) / Real.sqrt 3 := by
  rw [parityUnit, real_inner_smul_right, parityCentered,
    inner_sub_right, real_inner_smul_right, qResidue_three_inner_even_exact]
  ring

theorem qResidue_three_norm_sq_exact :
    ‖qResidue 3‖ ^ 2 = inner ℝ (qResidue 3) qOne - 16 / 81 := by
  rw [qNorm_weighted_sq, qSequence_qResidue]
  have he : (fun n : ℕ => positiveQWeight n * residueFraction 3 n ^ 2) =
      fun n => positiveQWeight n * residueFraction 3 n -
        (2 / 9 : ℝ) * nondivThreeWeight n := by
    funext n
    rw [residue_three_square]
    by_cases hd : 3 ∣ n <;> simp [nondivThreeWeight, hd] <;> ring
  rw [he, Summable.tsum_sub weightedResidueThree_summable
    (nondivThreeWeight_summable.mul_left (2 / 9)),
    tsum_mul_left, nondivThreeWeight_tsum, qInner_one_tsum, qSequence_qResidue]
  ring

end RiemannResearch.RH.ZetaTwoParitySignal
