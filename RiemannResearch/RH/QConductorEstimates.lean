/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.Analysis.FiniteHarmonicBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Complete-Q estimates for a high conductor

Source: the elementary head/tail arguments in
LegalSubspaceProjectionObstruction.md and SingleConductorProjectionBound.md.
These estimates concern the actual physical residue atoms and include the
whole inverse-square tail. The upper norm estimate already exists in
QConductorCoefficientMass, with the stronger constant two.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ZetaTwoHilbert
open ZetaTwoProbability ArithmeticCumulative QFiniteEnergyBounds QShiftedReciprocal

theorem qResidue_physical_nonneg (d n : ℕ) :
    0 ≤ qSequence (qResidue d) n := by
  rw [qSequence_qResidue]
  unfold residueFraction
  positivity

theorem qResidue_physical_le_div (d n : ℕ) :
    qSequence (qResidue d) n ≤ (n : ℝ) / d := by
  rw [qSequence_qResidue]
  unfold residueFraction
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
  exact_mod_cast Nat.mod_le n d

theorem qResidue_physical_abs_le_one (d n : ℕ) :
    |qSequence (qResidue d) n| ≤ 1 := by
  rw [abs_of_nonneg (qResidue_physical_nonneg d n)]
  by_cases hd : d = 0
  · simp [hd, qSequence_qResidue, residueFraction]
  have hdp : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  rw [qSequence_qResidue]
  unfold residueFraction
  apply (div_le_one hdp).mpr
  exact_mod_cast (Nat.mod_lt n (Nat.pos_of_ne_zero hd)).le

/-- The positive exact head gives a complete-Q lower norm bound. -/
theorem qResidue_norm_sq_ge_head (d : ℕ) (hd : 0 < d) :
    ((d : ℝ) - 1) / (zetaTwo * (d : ℝ) ^ 2) ≤ ‖qResidue d‖ ^ 2 := by
  have hz := zetaTwo_pos
  rw [qResidue_norm_sq_head_tail d hd]
  have ht : 0 ≤ ∑' n : ℕ,
      (qSequence (qResidue d) (n + d + 1)) ^ 2 / (n + d + 1 : ℝ) ^ 2 :=
    tsum_nonneg (fun n => div_nonneg (sq_nonneg _) (sq_nonneg _))
  have he : ((d : ℝ) - 1) / (zetaTwo * (d : ℝ) ^ 2) =
      (1 / zetaTwo) * (((d : ℝ) - 1) / (d : ℝ) ^ 2) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ht) (by positivity)

/-- Uniform lower bound of order inverse conductor; no primality is used. -/
theorem qResidue_norm_sq_ge_half_div (d : ℕ) (hd : 2 ≤ d) :
    1 / (2 * zetaTwo * (d : ℝ)) ≤ ‖qResidue d‖ ^ 2 := by
  have hz := zetaTwo_pos
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : (0 : ℝ) < d := by linarith
  apply le_trans _ (qResidue_norm_sq_ge_head d (by omega))
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * zetaTwo * (d : ℝ))
    (by positivity : 0 < zetaTwo * (d : ℝ) ^ 2)).mpr
  nlinarith [mul_nonneg (mul_nonneg zetaTwo_pos.le hdp.le) (sub_nonneg.mpr hdR)]

/-- A physical sup bound controls the actual Q norm, since Q has total mass one. -/
theorem qNorm_le_of_physical_bound (f : QHilbert) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, |qSequence f n| ≤ C) : ‖f‖ ≤ C := by
  have hsq : ‖f‖ ^ 2 ≤ C ^ 2 := by
    rw [qNorm_weighted_sq]
    calc
      _ ≤ ∑' n, positiveQWeight n * C ^ 2 := by
        apply (qSequence_square_summable f).tsum_le_tsum _
          (positiveQWeight_summable.mul_right (C ^ 2))
        intro n
        apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg n)
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hf n)
      _ = C ^ 2 := by rw [tsum_mul_right, positiveQWeight_tsum, one_mul]
  nlinarith [norm_nonneg f]

/-- Reciprocal smoothing gives a full physical bound inverse in the conductor. -/
theorem B_qResidue_physical_le (d n : ℕ) (hd : 0 < d) :
    |qSequence (B (qResidue d)) n| ≤ 1 / (d : ℝ) := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hnp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [qSequence_B, abs_div, abs_of_nonneg (qResidue_physical_nonneg d n),
    abs_of_pos hnp]
  apply (div_le_iff₀ hnp).mpr
  calc
    _ ≤ (n : ℝ) / d := qResidue_physical_le_div d n
    _ ≤ 1 / (d : ℝ) * ((n : ℝ) + 1) := by
      calc
        _ ≤ ((n : ℝ) + 1) / d := div_le_div_of_nonneg_right (by linarith) hdp.le
        _ = _ := by ring

theorem B_qResidue_norm_le (d : ℕ) (hd : 0 < d) :
    ‖B (qResidue d)‖ ≤ 1 / (d : ℝ) :=
  qNorm_le_of_physical_bound _ _ (by positivity) (fun n => B_qResidue_physical_le d n hd)

theorem qResidue_mean_nonnegative (d : ℕ) :
    0 ≤ inner ℝ qOne (qResidue d) := by
  rw [qInner_weighted]
  apply tsum_nonneg
  intro n
  have ho : 0 ≤ qSequence qOne n := by
    rw [qSequence_qOne]
    unfold qOneSequence
    split_ifs <;> norm_num
  exact mul_nonneg (mul_nonneg (positiveQWeight_nonneg n) ho)
    (qResidue_physical_nonneg d n)

/-- A logarithmic complete first-moment estimate. -/
theorem qResidue_mean_le_log_div (d : ℕ) (hd : 2 ≤ d) :
    inner ℝ qOne (qResidue d) ≤ (2 + Real.log (d : ℝ)) / (zetaTwo * d) := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hz := zetaTwo_pos
  have hOne (n : ℕ) : |qSequence qOne n| ≤ 1 := by
    rw [qSequence_qOne]
    unfold qOneSequence
    split_ifs <;> norm_num
  have hupper := inner_le_head_tail qOne (qResidue d) d (by omega)
    1 1 zero_le_one zero_le_one hOne (qResidue_physical_abs_le_one d)
  have hhead : (∑ n ∈ Finset.range d,
      qSequence qOne (n + 1) * qSequence (qResidue d) (n + 1) / (n + 1 : ℝ) ^ 2) ≤
      (harmonic d : ℝ) / d := by
    rw [RiemannResearch.Analysis.harmonic_cast_range, Finset.sum_div]
    apply Finset.sum_le_sum
    intro n hn
    have hnp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hterm := qResidue_physical_le_div d (n + 1)
    simp only [Nat.cast_add, Nat.cast_one] at hterm
    have hone : qSequence qOne (n + 1) = 1 := by
      rw [qSequence_qOne]
      simp [qOneSequence]
    rw [hone, one_mul]
    calc
      _ ≤ (((n : ℝ) + 1) / d) / ((n : ℝ) + 1) ^ 2 :=
        div_le_div_of_nonneg_right hterm (sq_nonneg _)
      _ = (1 / ((n : ℝ) + 1)) / d := by field_simp
  have hh := harmonic_le_one_add_log d
  have hhead' : (harmonic d : ℝ) / d ≤ (1 + Real.log (d : ℝ)) / d :=
    div_le_div_of_nonneg_right hh hdp.le
  calc
    _ ≤ (1 / zetaTwo) * ((harmonic d : ℝ) / d + 1 / d) := by
      apply hupper.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using add_le_add hhead (le_refl (1 / (d : ℝ)))
    _ ≤ (1 / zetaTwo) * ((1 + Real.log (d : ℝ)) / d + 1 / d) :=
      mul_le_mul_of_nonneg_left (add_le_add hhead' le_rfl) (by positivity)
    _ = _ := by ring

end RiemannResearch.RH.ZetaTwoHilbert
