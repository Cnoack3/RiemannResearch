/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusHeadRepair
import RiemannResearch.RH.ParetoExactHeadClosure
import RiemannResearch.RH.CanonicalMobiusCovarianceMinimum
import RiemannResearch.RH.CanonicalMobiusSignedAverages
import RiemannResearch.RH.ResidueClosureDensity
import RiemannResearch.RH.CanonicalMobiusWindowMinimum

/-!
# Fixed-head capacity under residue density

Source: the user's affine-exhaustion handoff, Section 12. At a fixed head,
density permits approximation of its finitely supported indicator, with
the head imposed exactly by continuous triangular repair. Capacity then
diverges with conductor. The density hypothesis is not discharged here;
no unformalized converse from RH is silently assumed.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The target has physical value one precisely on the first N sites. -/
def finiteHeadIndicator (N : ℕ) : ThresholdHilbert :=
  ∑ n ∈ Finset.range N, paretoPointHilbert n

theorem finiteHeadIndicator_sequence_succ (N n : ℕ) :
    hilbertSequence (finiteHeadIndicator N) (n + 1) = if n < N then 1 else 0 := by
  rw [← anchoredEvaluationCLM_apply (n + 1)]
  unfold finiteHeadIndicator
  simp only [map_sum, anchoredEvaluationCLM_apply, hilbertSequence_paretoPoint,
    paretoPointSequence, Nat.add_right_cancel_iff]
  simp

theorem finiteHeadIndicator_exact (N j : ℕ) (hj : 0 < j) (hjN : j ≤ N) :
    hilbertSequence (finiteHeadIndicator N) j = 1 := by
  cases j with
  | zero => omega
  | succ n => rw [finiteHeadIndicator_sequence_succ, if_pos (by omega)]

theorem finiteHeadIndicator_tail_zero (N : ℕ) :
    hilbertTailShift (finiteHeadIndicator N) N = 0 := by
  apply Subtype.ext
  funext n
  change finiteHeadIndicator N (n + N) = 0
  have h := finiteHeadIndicator_sequence_succ N (n + N)
  rw [if_neg (by omega : ¬ n + N < N)] at h
  change finiteHeadIndicator N (n + N) / Real.sqrt (paretoWeight (n + N)) = 0 at h
  exact (div_eq_zero_iff.mp h).resolve_right
    (ne_of_gt (Real.sqrt_pos.mpr (by unfold paretoWeight; positivity)))

theorem finiteHeadIndicator_norm_sq (N : ℕ) :
    ‖finiteHeadIndicator N‖ ^ 2 = (N : ℝ) / ((N : ℝ) + 1) := by
  rw [exact_head_norm_sq_split _ N (finiteHeadIndicator_exact N),
    finiteHeadIndicator_tail_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero]

/-- Density supplies actual finite legal vectors with a prescribed head and
arbitrarily small complete infinite tails. The conductor is existential. -/
theorem exists_legal_exact_head_small_tail_of_density
    (hDensity : closedSpace = ⊤) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M, N ≤ M ∧ ∃ x : ThresholdHilbert, x ∈ finiteSpace M ∧
      (∀ j, 0 < j → j ≤ N → hilbertSequence x j = 1) ∧
      ‖hilbertTailShift x N‖ ^ 2 < ε := by
  have hz : finiteHeadIndicator N ∈ closedSpace := by rw [hDensity]; trivial
  obtain ⟨M, hNM, x, hx, hhead, hsmall⟩ :=
    exists_legal_exact_head_near (finiteHeadIndicator N) hz N ε hε
  refine ⟨M, hNM, x, hx, ?_, ?_⟩
  · intro j hj hjN
    exact (hhead j hj hjN).trans (finiteHeadIndicator_exact N j hj hjN)
  · have hshift : hilbertTailShift (x - finiteHeadIndicator N) N =
        hilbertTailShift x N := by
      have h := (hilbertTailShiftLinear N).map_sub x (finiteHeadIndicator N)
      change hilbertTailShift (x - finiteHeadIndicator N) N =
        hilbertTailShift x N - hilbertTailShift (finiteHeadIndicator N) N at h
      simpa only [finiteHeadIndicator_tail_zero, sub_zero] using h
    have hle : ‖hilbertTailShift x N‖ ^ 2 ≤ ‖x - finiteHeadIndicator N‖ ^ 2 := by
      rw [← hshift, hilbertTailShift_norm_sq]
      exact sub_le_self _ (Finset.sum_nonneg (fun n hn => sq_nonneg _))
    exact hle.trans_lt hsmall

namespace SignedCovariance

theorem canonicalWindow_capacity_mono (N : ℕ) (hN : 0 < N) :
    Monotone (fun M => capacity N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN)) := by
  intro M K hMK
  let e : Fin (M - N + 1) → Fin (K - N + 1) :=
    fun i => ⟨i.val, by omega⟩
  exact capacity_mono_of_family_map N (canonicalWindowIndex N M)
    (canonicalWindowIndex N K) (canonicalWindowIndex_pos N M hN)
    (canonicalWindowIndex_pos N K hN) e (fun i => rfl)

/-- At every fixed positive head, capacity is unbounded in conductor under density. -/
theorem canonicalWindow_capacity_unbounded_of_density
    (hDensity : closedSpace = ⊤) (N : ℕ) (hN : 0 < N)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ M, N ≤ M ∧ C < capacity N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN) := by
  obtain ⟨M, hNM, x, hx, hhead, hsmall⟩ :=
    exists_legal_exact_head_small_tail_of_density hDensity N
      (C + 1)⁻¹ (inv_pos.mpr (by linarith))
  refine ⟨M, hNM, ?_⟩
  have hmin := (canonicalWindow_tail_isLeast_all_legal N M hN hNM).2
    ⟨x, hx, hhead, rfl⟩
  have hc : C + 1 < capacity N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN) :=
    (inv_lt_inv₀
      (capacity_pos N (canonicalWindowIndex N M) (canonicalWindowIndex_pos N M hN))
      (by linarith : 0 < C + 1)).mp (hmin.trans_lt hsmall)
  linarith

/-- The complete conductor limit is infinite at each fixed positive head under
density. This is distinct from an estimate at a prescribed diagonal budget. -/
theorem canonicalWindow_capacity_tendsto_atTop_of_density
    (hDensity : closedSpace = ⊤) (N : ℕ) (hN : 0 < N) :
    Tendsto (fun M => capacity N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN)) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  obtain ⟨M, hNM, hM⟩ := canonicalWindow_capacity_unbounded_of_density
    hDensity N hN (max C 0) (le_max_right _ _)
  filter_upwards [eventually_ge_atTop M] with K hK
  exact (le_max_left C 0).trans
    (hM.le.trans (canonicalWindow_capacity_mono N hN hK))

/-- Uniformly bounded exact-head optimizers force residue density. This
direction uses no converse from RH. -/
theorem density_of_canonicalWindow_capacity_ge_one
    (h : ∀ N : ℕ, ∃ M : ℕ, N + 1 ≤ M ∧
      1 ≤ capacity (N + 1) (canonicalWindowIndex (N + 1) M)
        (canonicalWindowIndex_pos (N + 1) M (by omega))) :
    closedSpace = ⊤ := by
  choose M hNM hcap using h
  let f : ℕ → ThresholdHilbert := fun N =>
    optimizedAverage (N + 1) (canonicalWindowIndex (N + 1) (M N))
      (canonicalWindowIndex_pos (N + 1) (M N) (by omega))
  have hfmem : ∀ N, f N ∈ closedSpace := by
    intro N
    exact optimizedAverage_mem_closedSpace _ _ _
  have hfhead : ∀ N j, 0 < j → j ≤ N → hilbertSequence (f N) j = 1 := by
    intro N j hj hjN
    exact optimizedAverage_exact _ _ _ (canonicalWindowIndex_ge (N + 1) (M N))
      j hj (by omega)
  have hbound : ∀ N, ‖f N‖ ^ 2 ≤ 2 := by
    intro N
    rw [show f N = optimizedAverage (N + 1)
      (canonicalWindowIndex (N + 1) (M N))
      (canonicalWindowIndex_pos (N + 1) (M N) (by omega)) from rfl,
      optimizedAverage_norm_sq _ _ _ (canonicalWindowIndex_ge (N + 1) (M N))]
    have hi : (capacity (N + 1) (canonicalWindowIndex (N + 1) (M N))
        (canonicalWindowIndex_pos (N + 1) (M N) (by omega)))⁻¹ ≤ 1 := by
      have := (inv_le_inv₀
        (capacity_pos (N + 1) (canonicalWindowIndex (N + 1) (M N))
          (canonicalWindowIndex_pos (N + 1) (M N) (by omega)))
        (by norm_num : (0 : ℝ) < 1)).2 (hcap N)
      simpa only [inv_one] using this
    have hh : ((N + 1 : ℕ) : ℝ) / (((N + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (((N + 1 : ℕ) : ℝ) + 1))).2
      linarith
    linarith
  have hone := hilbertOne_mem_closure_of_bounded_exact_head_energy
    closedSpace f hfmem hfhead hbound
  apply closedSpace_eq_top_iff_one_mem.mpr
  exact (closedSpace.topologicalClosure_minimal le_rfl
    (Submodule.isClosed_topologicalClosure _)) hone

/-- Exact geometric equivalence, independent of any unformalized RH converse. -/
theorem density_iff_canonicalWindow_capacity_ge_one :
    closedSpace = ⊤ ↔ ∀ N : ℕ, ∃ M : ℕ, N + 1 ≤ M ∧
      1 ≤ capacity (N + 1) (canonicalWindowIndex (N + 1) M)
        (canonicalWindowIndex_pos (N + 1) M (by omega)) := by
  constructor
  · intro h N
    obtain ⟨M, hNM, hM⟩ := canonicalWindow_capacity_unbounded_of_density h
      (N + 1) (by omega) 1 (by norm_num)
    exact ⟨M, hNM, hM.le⟩
  · exact density_of_canonicalWindow_capacity_ge_one

/-- The conductor limit criterion for all fixed positive heads is exactly
density of the actual closed residue span. -/
theorem density_iff_canonicalWindow_capacity_diverges :
    closedSpace = ⊤ ↔ ∀ N : ℕ, ∀ hN : 0 < N,
      Tendsto (fun M => capacity N (canonicalWindowIndex N M)
        (canonicalWindowIndex_pos N M hN)) atTop atTop := by
  constructor
  · intro h N hN
    exact canonicalWindow_capacity_tendsto_atTop_of_density h N hN
  · intro h
    apply density_of_canonicalWindow_capacity_ge_one
    intro N
    have he := (tendsto_atTop.1 (h (N + 1) (by omega))) 1
    obtain ⟨M, hcap, hNM⟩ := (he.and (eventually_ge_atTop (N + 1))).exists
    exact ⟨M, hNM, hcap⟩

/-- Conditional research reduction to actual Mathlib RH. The conductor-limit
premise is the open provider; no converse from RH is used. -/
theorem riemannHypothesis_of_all_fixed_head_capacity_divergence
    (h : ∀ N : ℕ, ∀ hN : 0 < N,
      Tendsto (fun M => capacity N (canonicalWindowIndex N M)
        (canonicalWindowIndex_pos N M hN)) atTop atTop) : RiemannHypothesis := by
  have hd := density_iff_canonicalWindow_capacity_diverges.mpr h
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
    (fun _ hn => hn)
  apply closedSpace_le_legalClosure
  exact closedSpace_eq_top_iff_one_mem.mp hd

end SignedCovariance
end RiemannResearch.RH.Pareto.CoefficientStabilization
