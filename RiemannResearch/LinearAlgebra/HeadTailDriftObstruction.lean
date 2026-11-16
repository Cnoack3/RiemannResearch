/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact attainable head-tail drift and a target-independent obstruction

Source: Christian Noack, *Best Nyman Beurling for RH — A1–A2 Audited
Revision*, Google Drive file 1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG,
Section 23.9 (reviewed 2026-11-16). The paper supplies the residual-graph
construction. We strengthen it to an exact range characterization and a
strict-angle obstruction in arbitrary real inner-product spaces.

The complete tail Gram map is an explicit linear equivalence; its inverse
is never replaced by a diagonal approximation. No completeness or finite
dimension of the ambient head/tail spaces is required. These are finite
design statements, not a proof of the actual arithmetic A1/A2 estimates.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.HeadTailDrift

variable {H K ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [Fintype ι]

/-- Orthogonality of a target to every column of the full design. -/
def Normal (a : ι → H) (b : ι → K) (h : H) (t : K) : Prop :=
  ∀ i, inner ℝ h (a i) + inner ℝ t (b i) = 0

/-- The exact two-block least-squares objective. -/
def loss (a : ι → H) (b : ι → K) (h : H) (t : K) (c : ι → ℝ) : ℝ :=
  ‖h - finiteSchurCombination a c‖ ^ 2 + ‖t - finiteSchurCombination b c‖ ^ 2

/-- Full normal equations give an exact completion, retaining both energies. -/
theorem normal_completion (a : ι → H) (b : ι → K) (h : H) (t : K)
    (hn : Normal a b h t) (c : ι → ℝ) :
    loss a b h t c = ‖h‖ ^ 2 + ‖t‖ ^ 2 +
      (‖finiteSchurCombination a c‖ ^ 2 + ‖finiteSchurCombination b c‖ ^ 2) := by
  have ho : inner ℝ h (finiteSchurCombination a c) +
      inner ℝ t (finiteSchurCombination b c) = 0 := by
    calc
      _ = ∑ i, c i * (inner ℝ h (a i) + inner ℝ t (b i)) := by
        simp [finiteSchurCombination, inner_sum, real_inner_smul_right,
          mul_add, Finset.sum_add_distrib]
      _ = 0 := by simp [Normal] at hn; simp [hn]
  unfold loss
  rw [norm_sub_sq_real, norm_sub_sq_real]
  linarith

theorem normal_minimizes (a : ι → H) (b : ι → K) (h : H) (t : K)
    (hn : Normal a b h t) (c : ι → ℝ) :
    loss a b h t 0 ≤ loss a b h t c := by
  have hzero : loss a b h t 0 = ‖h‖ ^ 2 + ‖t‖ ^ 2 := by
    simp [loss, finiteSchurCombination]
  rw [hzero, normal_completion a b h t hn c]
  exact le_add_of_nonneg_right (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The complete inverse-tail-Gram response to the head target. -/
def accessible (a : ι → H) (b : ι → K)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (h : H) : K :=
  finiteSchurCombination b (e.symm (fun i => inner ℝ h (a i)))

/-- Full optimizer minus tail optimizer, mapped into the tail observation space,
when the full optimizer is zero. -/
def drift (b : ι → K) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (t : K) : K :=
  -finiteSchurCombination b (e.symm (fun i => inner ℝ t (b i)))

theorem accessible_pairing (a : ι → H) (b : ι → K)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ c i, e c i = inner ℝ (finiteSchurCombination b c) (b i))
    (h : H) (i : ι) :
    inner ℝ (accessible a b e h) (b i) = inner ℝ h (a i) := by
  have hh := congrFun (e.apply_symm_apply (fun j => inner ℝ h (a j))) i
  rw [he] at hh
  exact hh

/-- Every accessible drift has an explicit target satisfying full normal equations. -/
theorem graph_normal (a : ι → H) (b : ι → K)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ c i, e c i = inner ℝ (finiteSchurCombination b c) (b i))
    (h : H) : Normal a b h (-accessible a b e h) := by
  intro i
  rw [inner_neg_left, accessible_pairing a b e he h i]
  ring

/-- Normal equations determine exactly the accessible endpoint drift. -/
theorem drift_eq_accessible (a : ι → H) (b : ι → K)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (h : H) (t : K)
    (hn : Normal a b h t) :
    drift b e t = accessible a b e h := by
  have hr : (fun i => inner ℝ t (b i)) = -(fun i => inner ℝ h (a i)) := by
    funext i
    have hi := hn i
    simp only [Pi.neg_apply]
    linarith
  simp [drift, accessible, hr, finiteSchurCombination, neg_smul,
    Finset.sum_neg_distrib]

/-- Exact range, not merely one inclusion: no accessible direction is
excluded by the full normal equations. -/
theorem attainable_iff (a : ι → H) (b : ι → K)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ c i, e c i = inner ℝ (finiteSchurCombination b c) (b i))
    (u : K) :
    (∃ h t, Normal a b h t ∧ drift b e t = u) ↔
      ∃ h, accessible a b e h = u := by
  constructor
  · rintro ⟨h, t, hn, hu⟩
    exact ⟨h, (drift_eq_accessible a b e h t hn).symm.trans hu⟩
  · rintro ⟨h, hu⟩
    have hn := graph_normal a b e he h
    exact ⟨h, -accessible a b e h, hn,
      (drift_eq_accessible a b e h _ hn).trans hu⟩

/-- A nonzero accessible signal admits perfect alignment for a legitimate
normal-equation target. Hence no strict universal angle gain can follow
from those normal equations alone. -/
theorem no_uniform_strict_angle (a : ι → H) (b : ι → K)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ c i, e c i = inner ℝ (finiteSchurCombination b c) (b i))
    (u : K) (hu : u ≠ 0) (ha : ∃ h, accessible a b e h = u)
    (κ : ℝ) (hκ : κ < 1) :
    ∃ h t, Normal a b h t ∧
      κ * ‖drift b e t‖ * ‖u‖ < inner ℝ (drift b e t) u := by
  obtain ⟨h, t, hn, hd⟩ := (attainable_iff a b e he u).mpr ha
  refine ⟨h, t, hn, ?_⟩
  rw [hd, real_inner_self_eq_norm_sq]
  have hp : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  nlinarith

/-- The inverse full tail Gram really is the tail least-squares optimizer. -/
theorem tail_completion (b : ι → K)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ c i, e c i = inner ℝ (finiteSchurCombination b c) (b i))
    (t : K) (c : ι → ℝ) :
    ‖t - finiteSchurCombination b c‖ ^ 2 =
      ‖t - finiteSchurCombination b (e.symm (fun i => inner ℝ t (b i)))‖ ^ 2 +
      ‖finiteSchurCombination b c -
        finiteSchurCombination b (e.symm (fun i => inner ℝ t (b i)))‖ ^ 2 := by
  apply finiteSchurResidual_completion
  intro i
  have hh := congrFun (e.apply_symm_apply (fun j => inner ℝ t (b j))) i
  rw [he] at hh
  simpa only [real_inner_comm] using hh

/-- The complete tail Gram excludes any nonzero coefficient in the nullspace
of the full objective. Thus the full optimizer is uniquely zero. -/
theorem normal_minimizer_unique (a : ι → H) (b : ι → K)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ c i, e c i = inner ℝ (finiteSchurCombination b c) (b i))
    (h : H) (t : K) (hn : Normal a b h t) (c : ι → ℝ) :
    loss a b h t c = loss a b h t 0 ↔ c = 0 := by
  constructor
  · intro hc
    have hzero : loss a b h t 0 = ‖h‖ ^ 2 + ‖t‖ ^ 2 := by
      simp [loss, finiteSchurCombination]
    rw [normal_completion a b h t hn c, hzero] at hc
    have hb : ‖finiteSchurCombination b c‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖finiteSchurCombination a c‖,
        sq_nonneg ‖finiteSchurCombination b c‖]
    have hbc : finiteSchurCombination b c = 0 := by
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hb)
    apply e.injective
    ext i
    rw [he, hbc]
    simp
  · rintro rfl
    rfl

/-- Pythagoras for every normal-equation extension of a prescribed head.
The residual graph is therefore the unique minimum-energy extension. -/
theorem normal_tail_energy (a : ι → H) (b : ι → K)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ c i, e c i = inner ℝ (finiteSchurCombination b c) (b i))
    (h : H) (t : K) (hn : Normal a b h t) :
    ‖t‖ ^ 2 = ‖accessible a b e h‖ ^ 2 + ‖t + accessible a b e h‖ ^ 2 := by
  have hi (i : ι) : inner ℝ (t + accessible a b e h) (b i) = 0 := by
    rw [inner_add_left, accessible_pairing a b e he h i]
    have := hn i
    linarith
  have hz : inner ℝ (t + accessible a b e h) (accessible a b e h) = 0 := by
    conv_rhs => rw [← Finset.sum_const_zero (s := (Finset.univ : Finset ι))]
    unfold accessible
    rw [finiteSchurCombination, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_smul_right]
    change _ * inner ℝ (t + accessible a b e h) (b i) = 0
    rw [hi, mul_zero]
  have hp := norm_sub_sq_real (t + accessible a b e h) (accessible a b e h)
  rw [add_sub_cancel_right, hz] at hp
  linarith

end RiemannResearch.LinearAlgebra.HeadTailDrift
