/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Convergence and effective tails of the archimedean screw series

The series with rates (4k+1)/2 and weights 1/(4k+1)^2 is continuous, even,
and zero at the origin. A summable uniform majorant gives an explicit tail
bound B_J tending to zero. Pointwise nonnegativity is not quadratic positivity;
the latter is treated separately in ScrewArchimedeanPositivity.

Source: Suzuki (2023), equation (1.1), https://arxiv.org/abs/2206.03682,
supports the archimedean term. The elementary exponential-series rewrite and
telescoping majorant follow the user-provided RH trace attack plan (2026-09-05).
Agreement with the source's Lerch/digamma normalization remains separate.
-/

namespace RiemannResearch.RH
open scoped BigOperators
noncomputable section

def archimedeanWeight (k : ℕ) : ℝ := 1 / (4*(k : ℝ)+1)^2
def archimedeanRate (k : ℕ) : ℝ := (4*(k : ℝ)+1)/2
def archimedeanScrewTerm (k : ℕ) (t : ℝ) : ℝ :=
  4 * (1 - Real.exp (-archimedeanRate k * |t|)) * archimedeanWeight k
def archimedeanScrewSeries (t : ℝ) : ℝ := ∑' k : ℕ, archimedeanScrewTerm k t

theorem archimedeanWeight_nonneg (k : ℕ) : 0 ≤ archimedeanWeight k := by
  unfold archimedeanWeight
  positivity

theorem archimedeanRate_pos (k : ℕ) : 0 < archimedeanRate k := by
  unfold archimedeanRate
  positivity

theorem summable_archimedeanWeight : Summable archimedeanWeight := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr h
  apply hs.of_nonneg_of_le archimedeanWeight_nonneg
  intro n
  unfold archimedeanWeight
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]

theorem archimedeanScrewTerm_nonneg (k : ℕ) (t : ℝ) :
    0 ≤ archimedeanScrewTerm k t := by
  have he : Real.exp (-archimedeanRate k * |t|) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (archimedeanRate_pos k).le) (abs_nonneg t))
  unfold archimedeanScrewTerm
  exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr he))
    (archimedeanWeight_nonneg k)

theorem norm_archimedeanScrewTerm_le (k : ℕ) (t : ℝ) :
    ‖archimedeanScrewTerm k t‖ ≤ 4 * archimedeanWeight k := by
  rw [Real.norm_eq_abs, abs_of_nonneg (archimedeanScrewTerm_nonneg k t)]
  unfold archimedeanScrewTerm
  have he := (Real.exp_pos (-archimedeanRate k * |t|)).le
  nlinarith [mul_nonneg he (archimedeanWeight_nonneg k)]

theorem summable_archimedeanScrewTerm (t : ℝ) :
    Summable (fun k => archimedeanScrewTerm k t) :=
  (summable_archimedeanWeight.mul_left 4).of_norm_bounded
    (fun k => norm_archimedeanScrewTerm_le k t)

theorem continuous_archimedeanScrewTerm (k : ℕ) :
    Continuous (archimedeanScrewTerm k) :=
  (continuous_const.mul (continuous_const.sub
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)))).mul continuous_const

theorem continuous_archimedeanScrewSeries : Continuous archimedeanScrewSeries :=
  continuous_tsum continuous_archimedeanScrewTerm
    (summable_archimedeanWeight.mul_left 4) norm_archimedeanScrewTerm_le

theorem archimedeanScrewSeries_zero : archimedeanScrewSeries 0 = 0 := by
  simp [archimedeanScrewSeries, archimedeanScrewTerm]

theorem archimedeanScrewSeries_neg (t : ℝ) :
    archimedeanScrewSeries (-t) = archimedeanScrewSeries t := by
  simp [archimedeanScrewSeries, archimedeanScrewTerm, abs_neg]

def archimedeanTailMajorant (J : ℕ) : ℝ :=
  archimedeanWeight J + 1 / (4*(4*(J : ℝ)+1))

private def tailTelescoper (k : ℕ) : ℝ := 1 / (4*(4*(k : ℝ)+1))

private theorem archimedeanWeight_succ_le (k : ℕ) :
    archimedeanWeight (k+1) ≤ tailTelescoper k - tailTelescoper (k+1) := by
  have h1 : (4*(k : ℝ)+1) ≠ 0 := by positivity
  have h5 : (4*(k : ℝ)+5) ≠ 0 := by positivity
  have he : tailTelescoper k - tailTelescoper (k+1) =
      1 / ((4*(k : ℝ)+1)*(4*(k : ℝ)+5)) := by
    unfold tailTelescoper
    push_cast
    field_simp
    ring
  rw [he]
  unfold archimedeanWeight
  push_cast
  convert! one_div_le_one_div_of_le
    (by positivity : 0 < (4*(k : ℝ)+1)*(4*(k : ℝ)+5))
    (by nlinarith [sq_nonneg (k : ℝ)] :
      (4*(k : ℝ)+1)*(4*(k : ℝ)+5) ≤ (4*(k : ℝ)+5)^2) using 1
  ring

private theorem sum_archimedeanWeight_tail_le (J M : ℕ) :
    ∑ k ∈ Finset.range M, archimedeanWeight (k+J+1) ≤
      tailTelescoper J - tailTelescoper (M+J) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      have h := archimedeanWeight_succ_le (M+J)
      have he : M+1+J = M+J+1 := by omega
      rw [he]
      linarith

theorem tsum_archimedeanWeight_tail_le (J : ℕ) :
    (∑' k : ℕ, archimedeanWeight (k+J)) ≤ archimedeanTailMajorant J := by
  have hs := (summable_nat_add_iff J).mpr summable_archimedeanWeight
  rw [hs.tsum_eq_zero_add]
  have htail : (∑' k : ℕ, archimedeanWeight (k+1+J)) ≤ tailTelescoper J := by
    apply ((summable_nat_add_iff 1).mpr hs).tsum_le_of_sum_range_le
    intro M
    have h := sum_archimedeanWeight_tail_le J M
    have hp : 0 ≤ tailTelescoper (M+J) := by
      unfold tailTelescoper
      positivity
    simpa only [Nat.add_assoc, Nat.add_comm 1 J] using (h.trans (sub_le_self _ hp))
  simpa [archimedeanTailMajorant, tailTelescoper] using add_le_add_left htail (archimedeanWeight J)

theorem archimedeanScrewSeries_eq_sum_add_tail (J : ℕ) (t : ℝ) :
    archimedeanScrewSeries t =
      (∑ k ∈ Finset.range J, archimedeanScrewTerm k t) +
      ∑' k : ℕ, archimedeanScrewTerm (k+J) t :=
  ((summable_archimedeanScrewTerm t).sum_add_tsum_nat_add J).symm

theorem archimedeanScrewSeries_tail_bounds (J : ℕ) (t : ℝ) :
    0 ≤ (∑' k : ℕ, archimedeanScrewTerm (k+J) t) ∧
    (∑' k : ℕ, archimedeanScrewTerm (k+J) t) ≤ 4*archimedeanTailMajorant J := by
  constructor
  · exact tsum_nonneg (fun k => archimedeanScrewTerm_nonneg _ _)
  · have hs := (summable_nat_add_iff J).mpr (summable_archimedeanScrewTerm t)
    have hw := (summable_nat_add_iff J).mpr summable_archimedeanWeight
    calc
      _ ≤ ∑' k : ℕ, 4*archimedeanWeight (k+J) := by
        apply Summable.tsum_le_tsum _ hs (hw.mul_left 4)
        intro k
        exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using (norm_archimedeanScrewTerm_le (k+J) t))
      _ = 4 * (∑' k : ℕ, archimedeanWeight (k+J)) := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left (tsum_archimedeanWeight_tail_le J) (by norm_num)

open Filter
open scoped Topology

theorem tendsto_archimedeanTailMajorant_zero :
    Tendsto archimedeanTailMajorant atTop (𝓝 0) := by
  have hd : Tendsto (fun J : ℕ => 4*(4*(J : ℝ)+1)) atTop atTop :=
    tendsto_atTop_mono (fun J => by nlinarith [Nat.cast_nonneg (α := ℝ) J])
      tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun J : ℕ => 1 / (4*(4*(J : ℝ)+1))) atTop (𝓝 0) := by
    convert! hd.inv_tendsto_atTop using 1
    funext J
    simp [one_div]
  convert! summable_archimedeanWeight.tendsto_atTop_zero.add hi using 1
  norm_num

end
end RiemannResearch.RH
