/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Coefficient mass required by large-conductor Q approximants

Source: user-provided quantitative coefficient-mass argument, 19 October 2026,
for the conductor bound, finite signed synthesis estimate, and necessary mass.
The exact head--tail identity precedes the bound. All tails are complete;
no squarefreeness, coprimality, or sign restriction is needed.
These are necessary conditions, not a bounded-energy construction or RH proof.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoHilbert
open ZetaTwoProbability ArithmeticCumulative QFiniteEnergyBounds

private theorem qResidue_unweighted_head (d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Finset.range d,
      (qSequence (qResidue d) (n + 1))^2 / (n + 1 : ℝ)^2) =
      ((d : ℝ) - 1) / (d : ℝ)^2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hd)
  rw [Finset.sum_range_succ]
  have hterm (n : ℕ) (hn : n ∈ Finset.range m) :
      (qSequence (qResidue (m + 1)) (n + 1))^2 / (n + 1 : ℝ)^2 =
        1 / (m + 1 : ℝ)^2 := by
    rw [qSequence_qResidue, residueFraction,
      Nat.mod_eq_of_lt (by have := Finset.mem_range.mp hn; omega)]
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [qSequence_qResidue]
  simp [residueFraction, div_eq_mul_inv]

/-- Exact conductor split: the remainder contains every physical site above d. -/
theorem qResidue_norm_sq_head_tail (d : ℕ) (hd : 0 < d) :
    ‖qResidue d‖^2 = (1 / zetaTwo) *
      (((d : ℝ) - 1) / (d : ℝ)^2 +
        ∑' n : ℕ, (qSequence (qResidue d) (n + d + 1))^2 / (n + d + 1 : ℝ)^2) := by
  have hs := SquarefreeRadicalDifference.qNormalized_square_summable (qResidue d)
  simp only [div_pow] at hs
  have hs' : Summable (fun n : ℕ =>
      (qSequence (qResidue d) (n + 1))^2 / (n + 1 : ℝ)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  rw [norm_sq_unweighted, ← hs'.sum_add_tsum_nat_add d, qResidue_unweighted_head d hd]
  simp only [Nat.cast_add]

/-- An elementary bound for the complete Q atom norm, including the infinite tail. -/
theorem qResidue_norm_sq_le_two_div (d : ℕ) (hd : 2 ≤ d) :
    ‖qResidue d‖^2 ≤ 2 / (zetaTwo * (d : ℝ)) := by
  have hZ := zetaTwo_pos
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hb : ∀ n, |qSequence (qResidue d) n| ≤ 1 := by
    intro n
    rw [qSequence_qResidue]
    unfold residueFraction
    rw [abs_of_nonneg (by positivity)]
    apply (div_le_one hdR).mpr
    exact_mod_cast (Nat.mod_lt n hdpos).le
  have he := norm_sq_le_head_tail (qResidue d) d hdpos 1 zero_le_one hb
  rw [qResidue_unweighted_head d hdpos] at he
  have hhead : ((d : ℝ) - 1) / (d : ℝ)^2 ≤ 1 / (d : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hdR) hdR).mpr
    nlinarith
  calc
    _ ≤ (1 / zetaTwo) * (((d : ℝ) - 1) / (d : ℝ)^2 + 1^2 / (d : ℝ)) := he
    _ ≤ (1 / zetaTwo) * (1 / (d : ℝ) + 1 / (d : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (by simpa using hhead) (by positivity)
    _ = _ := by ring

/-- Every signed finite combination satisfies the absolute-coefficient estimate. -/
theorem qResidue_sum_norm_le_mass {ι : Type*} (s : Finset ι)
    (d : ι → ℕ) (c : ι → ℝ) (D : ℕ) (hD : 2 ≤ D)
    (hd : ∀ i ∈ s, D ≤ d i) :
    ‖∑ i ∈ s, c i • qResidue (d i)‖ ≤
      Real.sqrt (2 / (zetaTwo * (D : ℝ))) * ∑ i ∈ s, |c i| := by
  have hZ := zetaTwo_pos
  have hDR : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  calc
    _ ≤ ∑ i ∈ s, ‖c i • qResidue (d i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, |c i| * ‖qResidue (d i)‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i ∈ s, |c i| * Real.sqrt (2 / (zetaTwo * (D : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Real.le_sqrt_of_sq_le
      apply (qResidue_norm_sq_le_two_div (d i) (hD.trans (hd i hi))).trans
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hd i hi) zetaTwo_pos.le
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- Approximating one with support at least D forces square-root coefficient mass.
For epsilon < 1 the lower bound is strictly positive. -/
theorem qResidue_sum_mass_lower {ι : Type*} (s : Finset ι)
    (d : ι → ℕ) (c : ι → ℝ) (D : ℕ) (hD : 2 ≤ D)
    (hd : ∀ i ∈ s, D ≤ d i) (epsilon : ℝ)
    (herr : ‖qOne - ∑ i ∈ s, c i • qResidue (d i)‖ ≤ epsilon) :
    (1 - epsilon) * Real.sqrt (zetaTwo * (D : ℝ) / 2) ≤ ∑ i ∈ s, |c i| := by
  have hZ := zetaTwo_pos
  have hDR : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hn := norm_sub_norm_le qOne (∑ i ∈ s, c i • qResidue (d i))
  rw [qOne_norm] at hn
  have hb := qResidue_sum_norm_le_mass s d c D hD hd
  have he : 1 - epsilon ≤
      Real.sqrt (2 / (zetaTwo * (D : ℝ))) * ∑ i ∈ s, |c i| := by linarith
  have hp : Real.sqrt (zetaTwo * (D : ℝ) / 2) *
      Real.sqrt (2 / (zetaTwo * (D : ℝ))) = 1 := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ zetaTwo * (D : ℝ) / 2)]
    have hh : (zetaTwo * (D : ℝ) / 2) * (2 / (zetaTwo * (D : ℝ))) = 1 := by
      field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hDR]
    rw [hh, Real.sqrt_one]
  calc
    _ = Real.sqrt (zetaTwo * (D : ℝ) / 2) * (1 - epsilon) := mul_comm _ _
    _ ≤ Real.sqrt (zetaTwo * (D : ℝ) / 2) *
        (Real.sqrt (2 / (zetaTwo * (D : ℝ))) * ∑ i ∈ s, |c i|) :=
      mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)
    _ = _ := by rw [← mul_assoc, hp, one_mul]

end RiemannResearch.RH.ZetaTwoHilbert
