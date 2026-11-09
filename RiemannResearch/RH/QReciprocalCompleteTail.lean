/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QReciprocalFiniteHead
import RiemannResearch.RH.QOptimizerParityRH
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Complete-tail lifting of reciprocal convergence

Source: Reciprocal_Density_CRT_Nyman_Beurling_2026-11-08.pdf, Section 8.2.
Uniform control concerns the full infinite Q-tail, not truncated energy.
The generic convergence theorem assumes no legal-space membership.
The RH corollary keeps uniform complete-tail control as an open provider.

The inverse graph condition explicitly requires Cauchy preimages.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QReciprocalCompleteTail
open ZetaTwoHilbert QShiftedReciprocal QFiniteSupportDualCriterion
open QReciprocalFiniteHead

/-- The inverse graph route contains a Cauchy estimate for the preimages.
Completeness then supplies a limit and reciprocal injectivity identifies it. -/
theorem tendsto_of_reciprocal_tendsto_cauchySeq
    (F : ℕ → QHilbert) (x : QHilbert)
    (hR : Tendsto (fun j => B (F j)) atTop (𝓝 (B x)))
    (hC : CauchySeq F) : Tendsto F atTop (𝓝 x) := by
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hC
  have hRy := (B.continuous.tendsto y).comp hy
  have he : B y = B x := tendsto_nhds_unique hRy hR
  have hyx : y = x := by
    apply sub_eq_zero.mp
    apply B_faithful (y - x)
    rw [map_sub, he, sub_self, inner_zero_right]
  simpa only [hyx] using hy

theorem finiteHead_sub (N : ℕ) (f g : QHilbert) :
    finiteHead N (f - g) = finiteHead N f - finiteHead N g := by
  apply lp.ext
  funext n
  by_cases hn : n < N
  · simp only [finiteHead_apply_of_lt N _ n hn, lp.coeFn_sub, Pi.sub_apply]
  · simp only [finiteHead_apply_eq_zero N _ n (by omega), lp.coeFn_sub,
      Pi.sub_apply, sub_self]

theorem finiteHead_absorb_of_le (M N : ℕ) (hMN : M ≤ N) (f : QHilbert) :
    finiteHead M (finiteHead N f) = finiteHead M f := by
  apply lp.ext
  funext n
  by_cases hn : n < M
  · rw [finiteHead_apply_of_lt M _ n hn,
      finiteHead_apply_of_lt N f n (lt_of_lt_of_le hn hMN),
      finiteHead_apply_of_lt M f n hn]
  · rw [finiteHead_apply_eq_zero M _ n (by omega),
      finiteHead_apply_eq_zero M _ n (by omega)]

/-- Enlarging the physical head decreases its complete tail norm. -/
theorem completeTail_norm_antitone (M N : ℕ) (hMN : M ≤ N) (f : QHilbert) :
    ‖f - finiteHead N f‖ ≤ ‖f - finiteHead M f‖ := by
  have hh : ‖finiteHead M f‖ ≤ ‖finiteHead N f‖ := by
    simpa only [finiteHead_absorb_of_le M N hMN f] using
      finiteHead_norm_le M (finiteHead N f)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  have hM := finiteHead_norm_sq_split M f
  have hN := finiteHead_norm_sq_split N f
  nlinarith [norm_nonneg (f - finiteHead N f), norm_nonneg (f - finiteHead M f)]

theorem finiteHead_norm_le_reciprocal (N : ℕ) (f : QHilbert) :
    ‖finiteHead N f‖ ≤ ((N : ℝ) + 1) * ‖B f‖ := by
  have h := finiteHead_norm_sq_le_reciprocal N f
  have hp : 0 ≤ ((N : ℝ) + 1) * ‖B f‖ := by positivity
  nlinarith [norm_nonneg (finiteHead N f)]

/-- Reciprocal convergence gives convergence on each fixed finite head. -/
theorem finiteHead_error_tendsto_zero (F : ℕ → QHilbert) (x : QHilbert)
    (hR : Tendsto (fun j => B (F j)) atTop (𝓝 (B x))) (N : ℕ) :
    Tendsto (fun j => ‖finiteHead N (F j - x)‖) atTop (𝓝 0) := by
  have hRn : Tendsto (fun j => ‖B (F j - x)‖) atTop (𝓝 0) := by
    simpa only [map_sub, sub_self, norm_zero] using
      (hR.sub (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => B x) atTop (𝓝 (B x)))).norm
  have hu : Tendsto (fun j => ((N : ℝ) + 1) * ‖B (F j - x)‖)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hRn.const_mul ((N : ℝ) + 1)
  exact squeeze_zero (fun j => norm_nonneg _) (fun j =>
    finiteHead_norm_le_reciprocal N (F j - x)) hu

/-- Route B: reciprocal convergence plus uniform complete tails gives strong convergence. -/
theorem tendsto_of_reciprocal_tendsto_uniform_completeTail
    (F : ℕ → QHilbert) (x : QHilbert)
    (hR : Tendsto (fun j => B (F j)) atTop (𝓝 (B x)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j,
      ‖F j - finiteHead N (F j)‖ ≤ ε) : Tendsto F atTop (𝓝 x) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have he3 : 0 < ε / 3 := by linarith
  obtain ⟨N₁, hN₁⟩ := htail (ε / 3) he3
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.1 (finiteHead_tendsto x)) (ε / 3) he3
  let N := max N₁ N₂
  have hxtail : ‖x - finiteHead N x‖ < ε / 3 := by
    have hx := hN₂ N (le_max_right N₁ N₂)
    rw [dist_eq_norm] at hx
    rwa [norm_sub_rev] at hx
  have hFtail (j : ℕ) : ‖F j - finiteHead N (F j)‖ ≤ ε / 3 :=
    (completeTail_norm_antitone N₁ N (le_max_left N₁ N₂) (F j)).trans (hN₁ j)
  filter_upwards [(finiteHead_error_tendsto_zero F x hR N).eventually
    (gt_mem_nhds he3)] with j hj
  have hdecomp : F j - x =
      (finiteHead N (F j - x) + (F j - finiteHead N (F j))) -
        (x - finiteHead N x) := by
    rw [finiteHead_sub]
    abel
  calc
    dist (F j) x = ‖(finiteHead N (F j - x) +
        (F j - finiteHead N (F j))) - (x - finiteHead N x)‖ := by
      rw [dist_eq_norm]
      exact congrArg norm hdecomp
    _ ≤ ‖finiteHead N (F j - x) + (F j - finiteHead N (F j))‖ +
        ‖x - finiteHead N x‖ := norm_sub_le _ _
    _ ≤ ‖finiteHead N (F j - x)‖ + ‖F j - finiteHead N (F j)‖ +
        ‖x - finiteHead N x‖ := add_le_add (norm_add_le _ _) le_rfl
    _ < ε := by linarith [hFtail j]

/-- The target remains in any closed set containing the approximants. -/
theorem mem_of_reciprocal_tendsto_uniform_completeTail
    (S : Set QHilbert) (hS : IsClosed S)
    (F : ℕ → QHilbert) (x : QHilbert) (hmem : ∀ j, F j ∈ S)
    (hR : Tendsto (fun j => B (F j)) atTop (𝓝 (B x)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j,
      ‖F j - finiteHead N (F j)‖ ≤ ε) : x ∈ S :=
  hS.mem_of_tendsto
    (tendsto_of_reciprocal_tendsto_uniform_completeTail F x hR htail)
    (Eventually.of_forall hmem)

/-- Conditional RH reduction: the entire uniform tail bound is still required. -/
theorem riemannHypothesis_of_reciprocal_uniform_completeTail
    (F : ℕ → QHilbert) (hmem : ∀ j, F j ∈ QFullResidueProjection.closure)
    (hR : Tendsto (fun j => B (F j)) atTop (𝓝 (B qOne)))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j,
      ‖F j - finiteHead N (F j)‖ ≤ ε) : RiemannHypothesis := by
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  exact mem_of_reciprocal_tendsto_uniform_completeTail
    (QFullResidueProjection.closure : Set QHilbert)
    QFullResidueProjection.legalSpan.isClosed_topologicalClosure F qOne hmem hR htail

end RiemannResearch.RH.QReciprocalCompleteTail
