/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QHyperplaneFiniteRepairs
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite-support mean-zero vectors are dense in the complete hyperplane

Source: the reciprocal-head investigation, 7 November 2026, Section 7.
A fixed first-coordinate correction removes the exact truncation mean error.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QHyperplaneCountermodel
open ZetaTwoHilbert QFiniteSupportDualCriterion

def meanAnchor : QHilbert := (‖finiteHead 1 qOne‖ ^ 2)⁻¹ • finiteHead 1 qOne

theorem first_head_ne_zero : finiteHead 1 qOne ≠ 0 := by
  intro hz
  have hn := congrArg (fun f : QHilbert => f 0) hz
  rw [finiteHead_apply_of_lt 1 qOne 0 (by norm_num)] at hn
  exact qOne_coordinate_ne_zero 0 hn

theorem meanAnchor_mean : inner ℝ qOne meanAnchor = 1 := by
  have hi := finiteHead_inner 1 qOne (finiteHead 1 qOne)
  rw [finiteHead_idem, real_inner_self_eq_norm_sq] at hi
  unfold meanAnchor
  rw [real_inner_smul_right, ← hi]
  exact inv_mul_cancel₀ (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr first_head_ne_zero)))

theorem meanAnchor_supported (n : ℕ) (hn : 1 ≤ n) : meanAnchor n = 0 := by
  change (‖finiteHead 1 qOne‖ ^ 2)⁻¹ * finiteHead 1 qOne n = 0
  rw [finiteHead_apply_eq_zero 1 qOne n hn, mul_zero]

def centeredHead (N : ℕ) (f : QHilbert) : QHilbert :=
  finiteHead N f - headMean N f • meanAnchor

theorem centeredHead_mem (N : ℕ) (f : QHilbert) : centeredHead N f ∈ meanZero := by
  rw [mem_meanZero]
  unfold centeredHead
  rw [inner_sub_right, real_inner_smul_right, meanAnchor_mean, mul_one]
  exact sub_self _

theorem centeredHead_supported (N : ℕ) (f : QHilbert) (n : ℕ) (hn : max N 1 ≤ n) :
    centeredHead N f n = 0 := by
  change finiteHead N f n - headMean N f * meanAnchor n = 0
  rw [finiteHead_apply_eq_zero N f n (le_trans (le_max_left N 1) hn),
    meanAnchor_supported n (le_trans (le_max_right N 1) hn), mul_zero, sub_self]

theorem centeredHead_tendsto (f : QHilbert) (hf : f ∈ meanZero) :
    Tendsto (fun N => centeredHead N f) atTop (𝓝 f) := by
  unfold centeredHead
  have hm := headMean_tendsto f
  rw [(mem_meanZero f).mp hf] at hm
  have hc := (finiteHead_tendsto f).sub
    (hm.smul (tendsto_const_nhds : Tendsto (fun _ : ℕ => meanAnchor) atTop (𝓝 meanAnchor)))
  simpa only [zero_smul, sub_zero] using hc

/-- An explicit sequential density certificate with the actual finite-support condition. -/
theorem finite_support_meanZero_dense (f : QHilbert) (hf : f ∈ meanZero) :
    ∃ F : ℕ → QHilbert,
      (∀ N, F N ∈ meanZero ∧ ∃ M, ∀ n, M ≤ n → F N n = 0) ∧
      Tendsto F atTop (𝓝 f) := by
  refine ⟨fun N => centeredHead N f, ?_, centeredHead_tendsto f hf⟩
  intro N
  exact ⟨centeredHead_mem N f, max N 1, centeredHead_supported N f⟩

end RiemannResearch.RH.QHyperplaneCountermodel
