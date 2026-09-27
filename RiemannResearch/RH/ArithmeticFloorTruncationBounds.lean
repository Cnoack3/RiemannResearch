/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ArithmeticFloorHilbertSeries
import RiemannResearch.RH.HyperbolaLogCutoff
import RiemannResearch.Analysis.WeightedMertensTransfer

/-!
# Uniform logarithmic bounds under conductor truncation

A signed weight with half-power logarithmic prefix and density-tail bounds
retains these bounds under every conductor cutoff. The existing exact
hyperbola theorem then gives one envelope for the entire physical sequence
of every Hilbert partial sum. This supplies the full-tail control for
the damped Mobius endpoint.

Proof strategy: finite prefix identities, monotonicity of the shifted
logarithmic profile, and the classical Dirichlet hyperbola decomposition.
No new arithmetic estimate or novelty claim is assumed.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Truncate an arithmetic weight in conductor, retaining all its signs. -/
def arithmeticCutoffWeight (w : ℕ → ℝ) (M d : ℕ) : ℝ :=
  if d ≤ M then w d else 0

theorem arithmeticCutoffWeight_zero (w : ℕ → ℝ) (hw : w 0 = 0) (M : ℕ) :
    arithmeticCutoffWeight w M 0 = 0 := by simp [arithmeticCutoffWeight, hw]

theorem positiveArithmeticPrefix_cutoff (w : ℕ → ℝ) (M t : ℕ) :
    positiveArithmeticPrefix (arithmeticCutoffWeight w M) t =
      positiveArithmeticPrefix w (min M t) := by
  unfold positiveArithmeticPrefix
  calc
    _ = ∑ d ∈ Finset.range (min M t), arithmeticCutoffWeight w M (d + 1) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (min_le_right M t))
      intro d hd hdm
      have ht := Finset.mem_range.mp hd
      have hm : ¬ d + 1 ≤ M := by
        simp only [Finset.mem_range] at hdm
        omega
      simp [arithmeticCutoffWeight, hm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hm : d + 1 ≤ M := by
        have := Finset.mem_range.mp hd
        omega
      simp [arithmeticCutoffWeight, hm]

theorem arithmeticFloorHilbert_cutoff_eq_partial (w : ℕ → ℝ) (M : ℕ) :
    arithmeticFloorHilbert (arithmeticCutoffWeight w M) =
      arithmeticFloorHilbertPartial w M := by
  unfold arithmeticFloorHilbert arithmeticFloorHilbertPartial
  congr 1
  rw [tsum_eq_sum (s := Finset.range M) (fun m hm => by
    have h : ¬ m + 1 ≤ M := by simpa only [Finset.mem_range, Nat.succ_le_iff] using hm
    simp [arithmeticResidueTerm, arithmeticCutoffWeight, h])]
  apply Finset.sum_congr rfl
  intro m hm
  have h : m + 1 ≤ M := Finset.mem_range.mp hm
  simp [arithmeticResidueTerm, arithmeticCutoffWeight, h]

theorem arithmeticFloorDensity_cutoff (w : ℕ → ℝ) (M : ℕ) :
    arithmeticFloorDensity (arithmeticCutoffWeight w M) =
      positiveArithmeticPrefix (fun d => w d / (d : ℝ)) M := by
  unfold arithmeticFloorDensity positiveArithmeticPrefix
  rw [tsum_eq_sum (s := Finset.range M) (fun m hm => by
    have h : ¬ m + 1 ≤ M := by simpa only [Finset.mem_range, Nat.succ_le_iff] using hm
    simp [arithmeticCutoffWeight, h])]
  apply Finset.sum_congr rfl
  intro m hm
  simp [arithmeticCutoffWeight, show m + 1 ≤ M from Finset.mem_range.mp hm]

theorem arithmeticFloorHilbertPartial_sequence_cutoff (w : ℕ → ℝ) (M n : ℕ) :
    hilbertSequence (arithmeticFloorHilbertPartial w M) n =
      arithmeticFloorPrefix (arithmeticCutoffWeight w M) n -
        (n : ℝ) * positiveArithmeticPrefix (fun d => w d / (d : ℝ)) M := by
  rw [← arithmeticFloorHilbert_cutoff_eq_partial]
  have hs : Summable (fun m : ℕ =>
      |arithmeticCutoffWeight w M (m + 1)| / ((m + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by
    apply summable_of_ne_finset_zero (s := Finset.range M)
    intro m hm
    have h : ¬ m + 1 ≤ M := by simpa only [Finset.mem_range, Nat.succ_le_iff] using hm
    simp [arithmeticCutoffWeight, h]
  rw [arithmeticFloorHilbert_sequence _ hs, arithmeticFloorDensity_cutoff]

/-- Cutting the coefficients preserves the full logarithmic prefix saving,
with the same constant. -/
theorem arithmeticCutoff_prefix_log_bound (w : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hp : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤
      B * Real.sqrt (t : ℝ) / (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ))
    (M t : ℕ) (ht : 0 < t) :
    |positiveArithmeticPrefix (arithmeticCutoffWeight w M) t| ≤
      B * Real.sqrt (t : ℝ) / (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ) := by
  rw [positiveArithmeticPrefix_cutoff]
  by_cases hm : min M t = 0
  · simp only [hm, positiveArithmeticPrefix_zero, abs_zero]
    positivity
  · have hmp : 0 < min M t := Nat.pos_of_ne_zero hm
    have hm1 : (1 : ℝ) ≤ min M t := by exact_mod_cast hmp
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hmono := halfLogPrimitive_monotoneOn hm1 ht1
      (by exact_mod_cast min_le_right M t)
    rw [halfLogPrimitive_eq_sqrt_div hm1, halfLogPrimitive_eq_sqrt_div ht1] at hmono
    have h := mul_le_mul_of_nonneg_left hmono hB
    simp only [← mul_div_assoc] at h
    exact (hp (min M t) hmp).trans h

/-- Cutting the coefficients preserves the signed density-tail estimate
with at most a factor two, uniformly in the conductor cutoff. -/
theorem arithmeticCutoff_density_tail_log_bound (w : ℕ → ℝ)
    (C : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hT : ∀ t : ℕ, 0 < t →
      |C - positiveArithmeticPrefix (fun d => w d / (d : ℝ)) t| ≤
        D / (Real.sqrt (t : ℝ) * (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ)))
    (M t : ℕ) (ht : 0 < t) :
    |positiveArithmeticPrefix (fun d => w d / (d : ℝ)) M -
      ∑ d ∈ Finset.range (t + 1), arithmeticCutoffWeight w M d / (d : ℝ)| ≤
      (2 * D) / (Real.sqrt (t : ℝ) * (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ)) := by
  have he : (∑ d ∈ Finset.range (t + 1), arithmeticCutoffWeight w M d / (d : ℝ)) =
      positiveArithmeticPrefix (fun d => w d / (d : ℝ)) (min M t) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, add_zero]
    change positiveArithmeticPrefix (fun d => arithmeticCutoffWeight w M d / (d : ℝ)) t = _
    have hf : (fun d => arithmeticCutoffWeight w M d / (d : ℝ)) =
        arithmeticCutoffWeight (fun d => w d / (d : ℝ)) M := by
      funext d
      simp only [arithmeticCutoffWeight]
      split_ifs <;> simp
    rw [hf, positiveArithmeticPrefix_cutoff]
  rw [he]
  by_cases hMt : M ≤ t
  · simp only [min_eq_left hMt, sub_self, abs_zero]
    positivity
  · have htM : t ≤ M := by omega
    have hMp : 0 < M := ht.trans_le htM
    have htR : (0 : ℝ) < t := by exact_mod_cast ht
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hMR : (t : ℝ) ≤ M := by exact_mod_cast htM
    have hL := shiftedLog_pos ht1
    have hden : Real.sqrt (t : ℝ) * (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ) ≤
        Real.sqrt (M : ℝ) * (6 + Real.log (M : ℝ)) ^ (3 / 2 : ℝ) :=
      mul_le_mul (Real.sqrt_le_sqrt hMR)
        (Real.rpow_le_rpow hL.le (by linarith [Real.log_le_log htR hMR]) (by norm_num))
        (by positivity) (Real.sqrt_nonneg _)
    have htailM := (hT M hMp).trans
      (div_le_div_of_nonneg_left hD (by positivity) hden)
    rw [min_eq_right htM]
    have hh := abs_sub_le (positiveArithmeticPrefix (fun d => w d / (d : ℝ)) M)
      C (positiveArithmeticPrefix (fun d => w d / (d : ℝ)) t)
    rw [abs_sub_comm (positiveArithmeticPrefix (fun d => w d / (d : ℝ)) M) C] at hh
    rw [mul_div_assoc]
    linarith [hT t ht]

/-- A single endpoint envelope controls all conductor-truncated Hilbert
approximants on their entire physical tail. -/
theorem arithmeticFloorHilbertPartial_uniform_log_bound
    (w : ℕ → ℝ) (hw0 : w 0 = 0) (C : ℝ) {W B D : ℝ}
    (hW : 0 ≤ W) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hw : ∀ d : ℕ, 0 < d → |w d| ≤ W / Real.sqrt (d : ℝ))
    (hP : ∀ t : ℕ, 0 < t → |positiveArithmeticPrefix w t| ≤
      B * Real.sqrt (t : ℝ) / (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ))
    (hT : ∀ t : ℕ, 0 < t →
      |C - positiveArithmeticPrefix (fun d => w d / (d : ℝ)) t| ≤
        D / (Real.sqrt (t : ℝ) * (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ)))
    (M n : ℕ) (hn : 0 < n) (hlarge : 200 ≤ Real.log (n : ℝ)) :
    |hilbertSequence (arithmeticFloorHilbertPartial w M) n| ≤
      (2 * W + 24 * B + 16 * D) * Real.sqrt (n : ℝ) /
        (6 + Real.log (n : ℝ)) ^ (3 / 4 : ℝ) := by
  rw [arithmeticFloorHilbertPartial_sequence_cutoff]
  have hwcut (d : ℕ) (hd : 0 < d) :
      |arithmeticCutoffWeight w M d| ≤ W / Real.sqrt (d : ℝ) := by
    unfold arithmeticCutoffWeight
    split_ifs
    · exact hw d hd
    · simp only [abs_zero]; positivity
  have h := arithmeticFloorPrefix_endpoint_log_bound (arithmeticCutoffWeight w M)
    (arithmeticCutoffWeight_zero w hw0 M)
    (positiveArithmeticPrefix (fun d => w d / (d : ℝ)) M)
    hW hB (show 0 ≤ 2 * D by positivity) hwcut
    (arithmeticCutoff_prefix_log_bound w hB hP M)
    (arithmeticCutoff_density_tail_log_bound w C hD hT M) hn hlarge
  convert h using 1
  ring

end RiemannResearch.RH.Pareto
