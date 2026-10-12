/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusWindowRecursion
import RiemannResearch.RH.ParetoFiniteHeadDilation
import RiemannResearch.RH.CanonicalMobiusWindowDuality
import RiemannResearch.RH.ResidueClosureDensity

/-!
# Fixed-head capacity and membership of its indicator

Source: user-provided Exact Schur Continuation handoff, Section 13,
for the full-tail optimizer and continuous head repair. This continuation
identifies the precise target of the complete conductor limit. No capacity
or gain divergence is assumed to have an unconditional provider.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- For an exact-head vector, its distance to the head indicator is exactly
its complete tail energy. -/
theorem exact_head_sub_indicator_norm_sq (x : ThresholdHilbert) (N : ℕ)
    (hx : ∀ j, 0 < j → j ≤ N → hilbertSequence x j = 1) :
    ‖x - finiteHeadIndicator N‖ ^ 2 = ‖hilbertTailShift x N‖ ^ 2 := by
  have hz : ∀ n < N, (x - finiteHeadIndicator N) n = 0 := by
    intro n hn
    have hs : hilbertSequence x (n + 1) =
        hilbertSequence (finiteHeadIndicator N) (n + 1) :=
      (hx (n + 1) (by omega) (by omega)).trans
        (finiteHeadIndicator_exact N (n + 1) (by omega) (by omega)).symm
    have hw : Real.sqrt (paretoWeight n) ≠ 0 := by
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      unfold paretoWeight
      positivity
    have he : x n = finiteHeadIndicator N n := (div_left_inj' hw).mp hs
    change x n - finiteHeadIndicator N n = 0
    exact sub_eq_zero.mpr he
  have ht : hilbertTailShift (x - finiteHeadIndicator N) N = hilbertTailShift x N := by
    have h := (hilbertTailShiftLinear N).map_sub x (finiteHeadIndicator N)
    change hilbertTailShift (x - finiteHeadIndicator N) N =
      hilbertTailShift x N - hilbertTailShift (finiteHeadIndicator N) N at h
    simpa only [finiteHeadIndicator_tail_zero, sub_zero] using h
  have h := hilbertTailShift_inner (x - finiteHeadIndicator N)
    (x - finiteHeadIndicator N) N hz
  simpa only [ht, real_inner_self_eq_norm_sq] using h.symm

namespace SignedCovariance

/-- Exact distance of the actual optimized window vector to the head indicator. -/
theorem canonicalWindow_optimizer_distance_sq (N M : ℕ) (hN : 0 < N) :
    ‖optimizedAverage N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN) - finiteHeadIndicator N‖ ^ 2 =
      (windowCapacity N M hN)⁻¹ := by
  rw [exact_head_sub_indicator_norm_sq _ N
    (optimizedAverage_exact _ _ _ (canonicalWindowIndex_ge N M)),
    optimizedAverage_tail_energy]
  rfl

/-- Membership of this single head indicator is enough for divergence at this head. -/
theorem windowCapacity_tendsto_atTop_of_indicator_mem
    (N : ℕ) (hN : 0 < N) (he : finiteHeadIndicator N ∈ closedSpace) :
    Tendsto (fun M => windowCapacity N M hN) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  let B := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨M, hNM, x, hx, hh, hs⟩ :=
    exists_legal_exact_head_near (finiteHeadIndicator N) he N B⁻¹ (inv_pos.mpr hB)
  have hhead : ∀ j, 0 < j → j ≤ N → hilbertSequence x j = 1 := by
    intro j hj hjN
    exact (hh j hj hjN).trans (finiteHeadIndicator_exact N j hj hjN)
  rw [exact_head_sub_indicator_norm_sq x N hhead] at hs
  have hmin := (canonicalWindow_tail_isLeast_all_legal N M hN hNM).2
    ⟨x, hx, hhead, rfl⟩
  have hc : B < windowCapacity N M hN :=
    (inv_lt_inv₀ (capacity_pos N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN)) hB).mp (hmin.trans_lt hs)
  filter_upwards [eventually_ge_atTop M] with K hK
  exact (show C ≤ B by dsimp [B]; linarith [le_max_left C 0]).trans
    (hc.le.trans (canonicalWindow_capacity_mono N hN hK))

/-- The complete conductor limit cannot diverge unless its head indicator
belongs to the actual legal closure. -/
theorem indicator_mem_of_windowCapacity_tendsto_atTop
    (N : ℕ) (hN : 0 < N)
    (h : Tendsto (fun M => windowCapacity N M hN) atTop atTop) :
    finiteHeadIndicator N ∈ closedSpace := by
  have hclosed : IsClosed (closedSpace : Set ThresholdHilbert) :=
    Submodule.isClosed_topologicalClosure _
  change finiteHeadIndicator N ∈ (closedSpace : Set ThresholdHilbert)
  rw [← hclosed.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := ((tendsto_atTop.1 h) ((ε ^ 2)⁻¹ + 1)).exists
  let x := optimizedAverage N (canonicalWindowIndex N M)
    (canonicalWindowIndex_pos N M hN)
  refine ⟨x, optimizedAverage_mem_closedSpace _ _ _, ?_⟩
  have hc : (ε ^ 2)⁻¹ < windowCapacity N M hN := by linarith
  have hi : (windowCapacity N M hN)⁻¹ < ε ^ 2 := by
    have := (inv_lt_inv₀ (capacity_pos N (canonicalWindowIndex N M)
      (canonicalWindowIndex_pos N M hN)) (inv_pos.mpr (sq_pos_of_pos hε))).2 hc
    simpa only [inv_inv, windowCapacity] using this
  have he := canonicalWindow_optimizer_distance_sq N M hN
  change ‖x - finiteHeadIndicator N‖ ^ 2 = (windowCapacity N M hN)⁻¹ at he
  have hn : ‖x - finiteHeadIndicator N‖ < ε := by
    nlinarith [norm_nonneg (x - finiteHeadIndicator N)]
  simpa only [dist_eq_norm, norm_sub_rev] using hn

/-- An exact geometric equivalence for each individual positive head. -/
theorem indicator_mem_iff_windowCapacity_diverges (N : ℕ) (hN : 0 < N) :
    finiteHeadIndicator N ∈ closedSpace ↔
      Tendsto (fun M => windowCapacity N M hN) atTop atTop :=
  ⟨windowCapacity_tendsto_atTop_of_indicator_mem N hN,
    indicator_mem_of_windowCapacity_tendsto_atTop N hN⟩

/-- Divergence at any ONE fixed positive head is equivalent to full legal density. -/
theorem density_iff_single_windowCapacity_diverges (N : ℕ) (hN : 0 < N) :
    closedSpace = ⊤ ↔ Tendsto (fun M => windowCapacity N M hN) atTop atTop :=
  (finiteHeadIndicator_mem_iff_density N hN).symm.trans
    (indicator_mem_iff_windowCapacity_diverges N hN)

/-- The exact Schur gain series at a single fixed positive head detects density. -/
theorem density_iff_single_windowGain_diverges (N : ℕ) (hN : 0 < N) :
    closedSpace = ⊤ ↔
      Tendsto (fun L => ∑ j ∈ Finset.range L, windowGain N (N + j) hN)
        atTop atTop := by
  constructor
  · intro hd
    have hc := (density_iff_single_windowCapacity_diverges N hN).mp hd
    apply tendsto_atTop.2
    intro C
    obtain ⟨M, hM⟩ := ((tendsto_atTop.1 hc)
      (C + (‖hilbertTailShift (canonicalMobiusHilbert N) N‖ ^ 2)⁻¹)).exists
    filter_upwards [eventually_ge_atTop M] with L hL
    have hcap := hM.trans (canonicalWindow_capacity_mono N hN (by omega : M ≤ N + L))
    change C + _ ≤ windowCapacity N (N + L) hN at hcap
    rw [windowCapacity_eq_base_add_gains] at hcap
    linarith
  · intro hg
    apply (density_iff_single_windowCapacity_diverges N hN).mpr
    apply tendsto_atTop.2
    intro C
    obtain ⟨L, hL⟩ := ((tendsto_atTop.1 hg) C).exists
    have hb : 0 ≤ (‖hilbertTailShift (canonicalMobiusHilbert N) N‖ ^ 2)⁻¹ := by
      positivity
    have hc : C ≤ windowCapacity N (N + L) hN := by
      rw [windowCapacity_eq_base_add_gains]
      linarith
    filter_upwards [eventually_ge_atTop (N + L)] with M hM
    exact hc.trans (canonicalWindow_capacity_mono N hN hM)

/-- Conditional research reduction: only one fixed-head series is needed.
Its divergence remains the open substantive hypothesis. -/
theorem riemannHypothesis_of_single_windowGain_divergence
    (N : ℕ) (hN : 0 < N)
    (h : Tendsto (fun L => ∑ j ∈ Finset.range L, windowGain N (N + j) hN)
      atTop atTop) : RiemannHypothesis := by
  have hd := (density_iff_single_windowGain_diverges N hN).mpr h
  exact riemannHypothesis_of_all_fixed_head_capacity_divergence
    (density_iff_canonicalWindow_capacity_diverges.mp hd)

/-- At every fixed positive head, bounded capacity is exactly failure of
legal-span density. Mixed finite/infinite behavior between heads is impossible. -/
theorem windowCapacity_bddAbove_iff_not_density (N : ℕ) (hN : 0 < N) :
    BddAbove (Set.range (fun M => windowCapacity N M hN)) ↔ closedSpace ≠ ⊤ := by
  constructor
  · rintro ⟨C, hC⟩ hd
    have ht := (density_iff_single_windowCapacity_diverges N hN).mp hd
    obtain ⟨M, hM⟩ := ((tendsto_atTop.1 ht) (C + 1)).exists
    have hb := hC (Set.mem_range_self M)
    linarith
  · intro hd
    have hp : 0 < limitEnergy := by
      have hn : 0 ≤ limitEnergy := sq_nonneg _
      by_contra h
      have hz : limitEnergy = 0 := by linarith
      exact hd (closedSpace_eq_top_iff_one_mem.mpr (limitEnergy_zero_iff_mem.mp hz))
    exact windowCapacity_bddAbove_of_residual_pos N hN hp

/-- The infinite common-normal obstruction exists precisely in the nondense case. -/
theorem commonNormal_exists_iff_not_density (N : ℕ) (hN : 0 < N) :
    (∃ Z : ThresholdHilbert, ∀ k, N ≤ k →
      inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N) Z = 1) ↔
      closedSpace ≠ ⊤ :=
  (windowCapacity_bddAbove_iff_commonNormal N hN).symm.trans
    (windowCapacity_bddAbove_iff_not_density N hN)

/-- Under not RH the complete signed-gain series converges to an exact finite
normal-energy excess. This is a consequence, not a contradiction. -/
theorem windowGain_sum_tendsto_of_not_RH (N : ℕ) (hN : 0 < N)
    (hRH : ¬ RiemannHypothesis) :
    ∃ Z : ThresholdHilbert,
      (∀ k, N ≤ k →
        inner ℝ (hilbertTailShift (canonicalMobiusHilbert k) N) Z = 1) ∧
      Tendsto (fun L => ∑ j ∈ Finset.range L, windowGain N (N + j) hN)
        atTop (𝓝 (‖Z‖ ^ 2 -
          (‖hilbertTailShift (canonicalMobiusHilbert N) N‖ ^ 2)⁻¹)) := by
  obtain ⟨Z, _, hZ, ht⟩ := exists_commonNormal_limit_of_not_RH N hN hRH
  refine ⟨Z, hZ, ?_⟩
  have hs : Tendsto (fun L : ℕ => N + L) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [eventually_ge_atTop K] with L hL
    omega
  have he := (ht.comp hs).sub (tendsto_const_nhds
    (x := (‖hilbertTailShift (canonicalMobiusHilbert N) N‖ ^ 2)⁻¹))
  simpa only [Function.comp_def, windowCapacity_eq_base_add_gains,
    add_sub_cancel_left] using he

end SignedCovariance
end RiemannResearch.RH.Pareto.CoefficientStabilization
