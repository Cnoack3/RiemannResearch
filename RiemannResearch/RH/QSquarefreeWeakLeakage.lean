/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.ApproximateSquareTests
import RiemannResearch.RH.QSquarefreeApproximateTests
import RiemannResearch.RH.QSquarefreeMultiplierLeakage
import RiemannResearch.Analysis.HilbertWeakCompactness
import RiemannResearch.RH.ZetaTwoCoordinateDual
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.ENNReal.Real
/-!
# Weak cluster points of scaled multiplier leakage
Source: the user's four-criteria continuation, 5 November 2026.
Weak compactness of a closed Hilbert ball upgrades vanishing scaled leakage
to a bound at arbitrarily large conductors. The arithmetic bound is OPEN.
The proof uses the actual displacement and returns Mathlib's RiemannHypothesis.
-/
noncomputable section
open Filter
open scoped Topology


namespace RiemannResearch.RH.QSquarefreeMultiplierLeakage
open ZetaTwoHilbert
open RiemannResearch.NumberTheory.ApproximateSquareTests
theorem normalized_fourSite_tendsto_zero (f : QHilbert) :
    Tendsto (fun n : ℕ => fourSite f n / (n : ℝ) ^ 2) atTop (𝓝 0) := by
  have hd := normalized_difference_tendsto_zero (qSequence f)
    (qSequence_div_nat_tendsto_zero f)
  have hp : Tendsto (fun n : ℕ => n ^ 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (max b 1)] with n hn
    have hb := le_max_left b 1
    have h1 := le_max_right b 1
    nlinarith
  have hs := hd.comp hp
  have hl := hd.mul (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have ht := hs.sub hl
  simp only [zero_mul, sub_zero] at ht
  convert ht using 1
  funext n
  simp only [Function.comp_def, Nat.cast_pow, fourSite]
  ring
end RiemannResearch.RH.QSquarefreeMultiplierLeakage

namespace RiemannResearch.RH.QSquarefreeMultiplierLeakage
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeDisplacementRigidity
open RiemannResearch.NumberTheory.ApproximateSquareTests
open RiemannResearch.Analysis.HilbertWeakCompactness

def fourSiteDual (n : ℕ) : QHilbert →L[ℝ] ℝ :=
  innerSL ℝ (qSiteRiesz (n ^ 2)) - innerSL ℝ (qSiteRiesz (n ^ 2 - 1)) -
    innerSL ℝ (qSiteRiesz n) + innerSL ℝ (qSiteRiesz (n - 1))

theorem fourSiteDual_apply (n : ℕ) (hn : 2 ≤ n) (f : QHilbert) :
    fourSiteDual n f = fourSite f n := by
  have hn2 : 0 < n ^ 2 := by positivity
  have hn4 : 4 ≤ n ^ 2 := by nlinarith
  have hn21 : 0 < n ^ 2 - 1 := by omega
  change inner ℝ (qSiteRiesz (n ^ 2)) f - inner ℝ (qSiteRiesz (n ^ 2 - 1)) f -
    inner ℝ (qSiteRiesz n) f + inner ℝ (qSiteRiesz (n - 1)) f = _
  rw [qSiteRiesz_inner _ hn2, qSiteRiesz_inner _ hn21,
    qSiteRiesz_inner _ (by omega : 0 < n),
    qSiteRiesz_inner _ (by omega : 0 < n - 1)]
  rfl

theorem riemannHypothesis_of_scaledError_weak_cluster (e : QHilbert)
    (he : ClusterPt (toWeakSpace ℝ QHilbert e)
      (Filter.map (fun m => toWeakSpace ℝ QHilbert (scaledError m)) atTop)) :
    RiemannHypothesis := by
  have htest (n : ℕ) (hn : 2 ≤ n) :
      fourSite e n = weightedTest (qSequence displacement) n := by
    let ev : WeakSpace ℝ QHilbert → ℝ :=
      fun x => ((topDualPairing ℝ QHilbert).flip x) (fourSiteDual n)
    have hc : Continuous ev :=
      WeakBilin.eval_continuous _ (fourSiteDual n)
    have ha (f : QHilbert) : ev (toWeakSpace ℝ QHilbert f) = fourSite f n := by
      exact fourSiteDual_apply n hn f
    have ht : Tendsto ev
        (Filter.map (fun m => toWeakSpace ℝ QHilbert (scaledError m)) atTop)
        (𝓝 (weightedTest (qSequence displacement) n)) := by
      apply Filter.tendsto_map'_iff.mpr
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (n ^ 2)] with m hm
      change weightedTest (qSequence displacement) n =
        ev (toWeakSpace ℝ QHilbert (scaledError m))
      rw [ha, scaledError_fourSite n m hn hm]
    have hx := he.map hc.continuousAt ht
    have heq := eq_of_nhds_neBot hx
    simpa only [ha] using heq
  apply QSquarefreeApproximateTests.riemannHypothesis_of_normalized_weighted_tests
  apply (normalized_fourSite_tendsto_zero e).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  rw [htest n hn]

theorem riemannHypothesis_of_frequently_bounded_scaled_leakage (C : ℝ)
    (hC : ∃ᶠ m : ℕ in atTop, (m : ℝ) * leakage m ≤ C) :
    RiemannHypothesis := by
  let F : ℕ → WeakSpace ℝ QHilbert :=
    fun m => toWeakSpace ℝ QHilbert (scaledError m)
  have hf : ∃ᶠ x in Filter.map F atTop,
      x ∈ toWeakSpace ℝ QHilbert '' Metric.closedBall (0 : QHilbert) C := by
    change ∃ᶠ m in atTop,
      F m ∈ toWeakSpace ℝ QHilbert '' Metric.closedBall (0 : QHilbert) C
    apply hC.mono
    intro m hm
    refine ⟨scaledError m, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, scaledError_norm] using hm
  obtain ⟨x, hx, hc⟩ :=
    (isCompact_closedBall_weak (H := QHilbert) C).exists_clusterPt_of_frequently hf
  obtain ⟨e, _, rfl⟩ := hx
  exact riemannHypothesis_of_scaledError_weak_cluster e hc

end RiemannResearch.RH.QSquarefreeMultiplierLeakage


namespace RiemannResearch.RH.QSquarefreeMultiplierLeakage
theorem riemannHypothesis_of_scaled_leakage_liminf_finite
    (h : Filter.liminf (fun m : ℕ => ENNReal.ofReal ((m : ℝ) * leakage m)) atTop < ⊤) :
    RiemannHypothesis := by
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ne_of_lt h)
  have hf := Filter.frequently_lt_of_liminf_lt (h := hN)
  apply riemannHypothesis_of_frequently_bounded_scaled_leakage (N : ℝ)
  apply hf.mono
  intro m hm
  have hnn : 0 ≤ (m : ℝ) * leakage m := by rw [← scaledError_norm]; exact norm_nonneg _
  have hlt : ENNReal.ofReal ((m : ℝ) * leakage m) < ENNReal.ofReal (N : ℝ) := by
    simpa only [ENNReal.ofReal_natCast] using hm
  exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn).mp hlt).le

theorem riemannHypothesis_of_scaled_leakage_liminf_zero
    (h : Filter.liminf (fun m : ℕ => ENNReal.ofReal ((m : ℝ) * leakage m)) atTop = 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_scaled_leakage_liminf_finite
  rw [h]
  exact ENNReal.zero_lt_top

theorem scaled_leakage_diverges_of_not_RH (h : ¬ RiemannHypothesis) :
    Tendsto (fun m : ℕ => (m : ℝ) * leakage m) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  by_contra hn
  have hf : ∃ᶠ m : ℕ in atTop, ¬ C ≤ (m : ℝ) * leakage m := by
    simpa only [Filter.Frequently, not_not] using hn
  apply h
  apply riemannHypothesis_of_frequently_bounded_scaled_leakage C
  exact hf.mono (fun m hm => (lt_of_not_ge hm).le)

end RiemannResearch.RH.QSquarefreeMultiplierLeakage
