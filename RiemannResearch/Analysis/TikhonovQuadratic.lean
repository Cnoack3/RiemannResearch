/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact Tikhonov objective certificates

For finite legal dictionaries, the normal equations are computed from complete
Gram matrices. The following Hilbert identities retain the exact remainder and
therefore apply without changing the physical measure or truncating the tail.
This file asserts no uniform bound on the minimizers as alpha tends to zero.
-/

noncomputable section

namespace RiemannResearch.Analysis.TikhonovQuadratic

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

def objective (T : H →L[ℝ] K) (y : K) (α : ℝ) (v : H) : ℝ :=
  ‖T v - y‖ ^ 2 + α * ‖v‖ ^ 2

def normalDefect (T : H →L[ℝ] K) (y : K) (α : ℝ) (w u : H) : ℝ :=
  inner ℝ (T w - y) (T u) + α * inner ℝ w u

/-- Exact expansion, including the signed normal-equation defect. -/
theorem objective_expansion (T : H →L[ℝ] K) (y : K) (α : ℝ) (v w : H) :
    objective T y α v = objective T y α w +
      ‖T (v - w)‖ ^ 2 + α * ‖v - w‖ ^ 2 +
        2 * normalDefect T y α w (v - w) := by
  have ht : T v - y = (T w - y) + T (v - w) := by
    rw [map_sub]
    abel
  have htv : ‖T v - y‖ ^ 2 = ‖T w - y‖ ^ 2 +
      ‖T (v - w)‖ ^ 2 + 2 * inner ℝ (T w - y) (T (v - w)) := by
    rw [ht, norm_add_sq_real]
    ring
  have hvw : ‖v‖ ^ 2 = ‖w‖ ^ 2 + ‖v - w‖ ^ 2 +
      2 * inner ℝ w (v - w) := by
    have he : w + (v - w) = v := by abel
    have hn := norm_add_sq_real w (v - w)
    rw [he] at hn
    nlinarith
  unfold objective normalDefect
  rw [htv, hvw]
  ring

/-- The normal equations remove precisely the cross term. -/
theorem objective_remainder (T : H →L[ℝ] K) (y : K) (α : ℝ)
    (v w : H) (hn : normalDefect T y α w (v - w) = 0) :
    objective T y α v = objective T y α w +
      ‖T (v - w)‖ ^ 2 + α * ‖v - w‖ ^ 2 := by
  rw [objective_expansion T y α v w, hn, mul_zero, add_zero]

/-- A certified normal-equation residual bounds suboptimality even for an
inexact numerical candidate. The bound holds against every admissible trial
for which the displayed dual residual estimate is proved. -/
theorem objective_gap_of_normal_defect_bound (T : H →L[ℝ] K) (y : K)
    (α : ℝ) (hα : 0 < α) (v w : H) (η : ℝ)
    (hd : |normalDefect T y α w (v - w)| ≤ η * ‖v - w‖) :
    objective T y α w ≤ objective T y α v + η ^ 2 / α := by
  have he := objective_expansion T y α v w
  have hlo := (abs_le.mp hd).1
  have heα := congrArg (fun t : ℝ => α * t) he
  have hloα := mul_le_mul_of_nonneg_left hlo hα.le
  have hs := sq_nonneg (α * ‖v - w‖ - η)
  have ht := mul_nonneg hα.le (sq_nonneg ‖T (v - w)‖)
  have hmul : (objective T y α w - objective T y α v) * α ≤ η ^ 2 := by
    nlinarith
  have hgap : objective T y α w - objective T y α v ≤ η ^ 2 / α :=
    (le_div_iff₀ hα).mpr hmul
  linarith

/-- A constrained normal-equation solution has the same exact remainder. -/
theorem objective_remainder_on_submodule (S : Submodule ℝ H)
    (T : H →L[ℝ] K) (y : K) (α : ℝ) (w : H) (hw : w ∈ S)
    (hn : ∀ u ∈ S, normalDefect T y α w u = 0)
    (v : H) (hv : v ∈ S) :
    objective T y α v = objective T y α w +
      ‖T (v - w)‖ ^ 2 + α * ‖v - w‖ ^ 2 :=
  objective_remainder T y α v w (hn _ (S.sub_mem hv hw))

/-- Nonnegative regularization makes the complete normal-equation solution minimal. -/
theorem objective_minimal_on_submodule (S : Submodule ℝ H)
    (T : H →L[ℝ] K) (y : K) (α : ℝ) (hα : 0 ≤ α)
    (w : H) (hw : w ∈ S)
    (hn : ∀ u ∈ S, normalDefect T y α w u = 0)
    (v : H) (hv : v ∈ S) :
    objective T y α w ≤ objective T y α v := by
  rw [objective_remainder_on_submodule S T y α w hw hn v hv]
  have hp := mul_nonneg hα (sq_nonneg ‖v - w‖)
  nlinarith [sq_nonneg ‖T (v - w)‖]

/-- Positive regularization gives a rigorous gap bound in the original norm. -/
theorem objective_gap_controls_norm (S : Submodule ℝ H)
    (T : H →L[ℝ] K) (y : K) (α : ℝ)
    (w : H) (hw : w ∈ S)
    (hn : ∀ u ∈ S, normalDefect T y α w u = 0)
    (v : H) (hv : v ∈ S) :
    α * ‖v - w‖ ^ 2 ≤ objective T y α v - objective T y α w := by
  rw [objective_remainder_on_submodule S T y α w hw hn v hv]
  nlinarith [sq_nonneg ‖T (v - w)‖]

/-- A zero objective gap identifies the same physical vector, irrespective of
redundant coefficient representations in a finite dictionary. -/
theorem eq_of_objective_eq (S : Submodule ℝ H)
    (T : H →L[ℝ] K) (y : K) (α : ℝ) (hα : 0 < α)
    (w : H) (hw : w ∈ S)
    (hn : ∀ u ∈ S, normalDefect T y α w u = 0)
    (v : H) (hv : v ∈ S)
    (he : objective T y α v = objective T y α w) : v = w := by
  have hgap := objective_gap_controls_norm S T y α w hw hn v hv
  rw [he, sub_self] at hgap
  have hprod : α * ‖v - w‖ ^ 2 = 0 :=
    le_antisymm hgap (mul_nonneg hα.le (sq_nonneg _))
  have hs : ‖v - w‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hα)
  have hz : ‖v - w‖ = 0 := by
    nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end RiemannResearch.Analysis.TikhonovQuadratic
