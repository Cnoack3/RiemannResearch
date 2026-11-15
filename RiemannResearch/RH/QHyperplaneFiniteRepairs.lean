/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHyperplaneRepairs
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Finite-support exact-head minimizers in the matched hyperplane model

Source: the reciprocal-head investigation, 7 November 2026, Section 7.
Every support condition and the entire constrained norm-square remainder are
explicit. The denominator is the actual finite Q block mass.
-/

noncomputable section
namespace RiemannResearch.RH.QHyperplaneCountermodel
open ZetaTwoHilbert QFiniteSupportDualCriterion

theorem finiteHead_eq_self_of_supported (M : ℕ) (x : QHilbert)
    (hx : ∀ n, M ≤ n → x n = 0) : finiteHead M x = x := by
  apply Subtype.ext
  funext n
  by_cases hn : n < M
  · exact finiteHead_apply_of_lt M x n hn
  · rw [finiteHead_apply_eq_zero M x n (Nat.le_of_not_gt hn), hx n (Nat.le_of_not_gt hn)]

theorem finiteHead_nested_of_le (N M : ℕ) (hNM : N ≤ M) (x : QHilbert) :
    finiteHead N (finiteHead M x) = finiteHead N x := by
  apply Subtype.ext
  funext n
  by_cases hn : n < N
  · rw [finiteHead_apply_of_lt N _ n hn, finiteHead_apply_of_lt N _ n hn,
      finiteHead_apply_of_lt M _ n (lt_of_lt_of_le hn hNM)]
  · rw [finiteHead_apply_eq_zero N _ n (Nat.le_of_not_gt hn),
      finiteHead_apply_eq_zero N _ n (Nat.le_of_not_gt hn)]

theorem finiteHead_outer_of_le (N M : ℕ) (hNM : N ≤ M) (x : QHilbert) :
    finiteHead M (finiteHead N x) = finiteHead N x := by
  apply finiteHead_eq_self_of_supported
  intro n hn
  exact finiteHead_apply_eq_zero N x n (hNM.trans hn)

def blockTail (N M : ℕ) : QHilbert := finiteHead M qOne - finiteHead N qOne

def blockRepair (N M : ℕ) (x : QHilbert) : QHilbert :=
  finiteHead N x - (headMean N x / ‖blockTail N M‖ ^ 2) • blockTail N M

theorem blockTail_supported (N M : ℕ) (hNM : N ≤ M) (n : ℕ) (hn : M ≤ n) :
    blockTail N M n = 0 := by
  change finiteHead M qOne n - finiteHead N qOne n = 0
  rw [finiteHead_apply_eq_zero M qOne n hn,
    finiteHead_apply_eq_zero N qOne n (hNM.trans hn)]
  ring

theorem blockTail_ne_zero (N M : ℕ) (hNM : N < M) : blockTail N M ≠ 0 := by
  intro hz
  have hn := congrArg (fun f : QHilbert => f N) hz
  change finiteHead M qOne N - finiteHead N qOne N = 0 at hn
  rw [finiteHead_apply_of_lt M qOne N hNM,
    finiteHead_apply_eq_zero N qOne N (le_refl N), sub_zero] at hn
  exact qOne_coordinate_ne_zero N hn

theorem blockTail_norm_sq_pos (N M : ℕ) (hNM : N < M) : 0 < ‖blockTail N M‖ ^ 2 :=
  sq_pos_of_pos (norm_pos_iff.mpr (blockTail_ne_zero N M hNM))

theorem blockTail_mean (N M : ℕ) (hNM : N ≤ M) :
    inner ℝ qOne (blockTail N M) = ‖blockTail N M‖ ^ 2 := by
  have hp : finiteHead M (blockTail N M) = blockTail N M :=
    finiteHead_eq_self_of_supported M _ (blockTail_supported N M hNM)
  have ho := inner_finiteHead_tail N (finiteHead M qOne) (finiteHead M qOne)
  rw [finiteHead_nested_of_le N M hNM] at ho
  have he : finiteHead M qOne = finiteHead N qOne + blockTail N M := by
    unfold blockTail
    abel
  calc
    _ = inner ℝ (finiteHead M qOne) (blockTail N M) := by
      rw [finiteHead_inner, hp]
    _ = inner ℝ (finiteHead N qOne + blockTail N M) (blockTail N M) :=
      congrArg (fun z => inner ℝ z (blockTail N M)) he
    _ = ‖blockTail N M‖ ^ 2 := by
      rw [inner_add_left, show inner ℝ (finiteHead N qOne) (blockTail N M) = 0 from ho,
        real_inner_self_eq_norm_sq, zero_add]

theorem blockRepair_mem (N M : ℕ) (hNM : N < M) (x : QHilbert) :
    blockRepair N M x ∈ meanZero := by
  rw [mem_meanZero]
  unfold blockRepair
  rw [inner_sub_right, real_inner_smul_right, blockTail_mean N M hNM.le]
  change headMean N x - (headMean N x / ‖blockTail N M‖ ^ 2) * ‖blockTail N M‖ ^ 2 = 0
  rw [div_mul_cancel₀ _ (ne_of_gt (blockTail_norm_sq_pos N M hNM))]
  ring

theorem blockRepair_head (N M : ℕ) (hNM : N ≤ M) (x : QHilbert)
    (n : ℕ) (hn : n < N) : blockRepair N M x n = x n := by
  change finiteHead N x n - (headMean N x / ‖blockTail N M‖ ^ 2) *
    (finiteHead M qOne n - finiteHead N qOne n) = x n
  rw [finiteHead_apply_of_lt N x n hn,
    finiteHead_apply_of_lt M qOne n (lt_of_lt_of_le hn hNM),
    finiteHead_apply_of_lt N qOne n hn]
  ring

theorem blockRepair_supported (N M : ℕ) (hNM : N ≤ M) (x : QHilbert)
    (n : ℕ) (hn : M ≤ n) : blockRepair N M x n = 0 := by
  change finiteHead N x n - (headMean N x / ‖blockTail N M‖ ^ 2) * blockTail N M n = 0
  rw [finiteHead_apply_eq_zero N x n (hNM.trans hn), blockTail_supported N M hNM n hn]
  ring

/-- The finite block version of the full completion, for all legal support<M trials. -/
theorem blockRepair_raw_completion (N M : ℕ) (hNM : N < M) (x F : QHilbert)
    (hF : F ∈ meanZero) (hh : ∀ n < N, F n = x n)
    (hs : ∀ n, M ≤ n → F n = 0) :
    ‖F‖ ^ 2 = ‖finiteHead N x‖ ^ 2 +
      (headMean N x) ^ 2 / ‖blockTail N M‖ ^ 2 + ‖F - blockRepair N M x‖ ^ 2 := by
  have hMF : finiteHead M F = F := finiteHead_eq_self_of_supported M F hs
  have horth : inner ℝ (finiteHead M qOne) F = 0 := by
    rw [finiteHead_inner, hMF]
    exact (mem_meanZero F).mp hF
  have ht : ‖finiteHead M qOne - finiteHead N (finiteHead M qOne)‖ ^ 2 ≠ 0 := by
    rw [finiteHead_nested_of_le N M hNM.le]
    exact ne_of_gt (blockTail_norm_sq_pos N M hNM)
  have hc := matching_head_residual_completion N x F (finiteHead M qOne) horth hh ht
  dsimp only at hc
  rw [finiteHead_nested_of_le N M hNM.le] at hc
  have ha : inner ℝ (finiteHead M qOne) (finiteHead N x) = headMean N x := by
    rw [finiteHead_inner, finiteHead_outer_of_le N M hNM.le]
    rfl
  rw [ha] at hc
  have hr : F - finiteHead N x +
      (headMean N x / ‖blockTail N M‖ ^ 2) • blockTail N M = F - blockRepair N M x := by
    unfold blockRepair
    abel
  change ‖F‖ ^ 2 = ‖finiteHead N x‖ ^ 2 +
      (headMean N x) ^ 2 / ‖blockTail N M‖ ^ 2 +
      ‖F - finiteHead N x +
        (headMean N x / ‖blockTail N M‖ ^ 2) • blockTail N M‖ ^ 2 at hc
  rwa [hr] at hc

theorem blockRepair_energy (N M : ℕ) (hNM : N < M) (x : QHilbert) :
    ‖blockRepair N M x‖ ^ 2 = ‖finiteHead N x‖ ^ 2 +
      (headMean N x) ^ 2 / ‖blockTail N M‖ ^ 2 := by
  have hc := blockRepair_raw_completion N M hNM x (blockRepair N M x)
    (blockRepair_mem N M hNM x) (blockRepair_head N M hNM.le x)
    (blockRepair_supported N M hNM.le x)
  simpa only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] using hc

theorem blockRepair_completion (N M : ℕ) (hNM : N < M) (x F : QHilbert)
    (hF : F ∈ meanZero) (hh : ∀ n < N, F n = x n)
    (hs : ∀ n, M ≤ n → F n = 0) :
    ‖F‖ ^ 2 = ‖blockRepair N M x‖ ^ 2 + ‖F - blockRepair N M x‖ ^ 2 := by
  rw [blockRepair_energy N M hNM x]
  exact blockRepair_raw_completion N M hNM x F hF hh hs

end RiemannResearch.RH.QHyperplaneCountermodel
