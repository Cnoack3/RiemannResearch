/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # Countable testing for nonnegative interval masses

A rational-density and monotonicity argument reduces all interval limits on
`[1,∞)` to the anchored rational intervals `[1,q]`. The Montgomery consumer is
`MontgomeryIntervalCriterion`; no arithmetic convergence is proved here.
Source: independently developed dense-set squeeze argument, motivated by
Carneiro--Milinovich--Ramos, arXiv:2310.01913, equation (1.4).
-/

open Filter MeasureTheory
open scoped Topology

namespace RiemannResearch.Analysis

/-- Monotonicity extends rational-point convergence on a closed half-line
to every real point, when the limit is the affine function x ↦ x - 1. -/
theorem tendsto_monotoneOn_Ici_of_rat
    {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ}
    (hm : ∀ᶠ t in l, MonotoneOn (F t) (Set.Ici 1))
    (hq : ∀ q : ℚ, 1 ≤ (q : ℝ) →
      Tendsto (fun t => F t q) l (𝓝 ((q : ℝ) - 1)))
    {x : ℝ} (hx : 1 ≤ x) :
    Tendsto (fun t => F t x) l (𝓝 (x - 1)) := by
  rcases eq_or_lt_of_le hx with hxe | hx
  · subst x
    simpa using hq 1 (by norm_num)
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨q, hqa, hqx⟩ := exists_rat_btwn
      (show max 1 (a + 1) < x from max_lt hx (by linarith))
    have hq1 : 1 ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hqa)
    have haq : a < (q : ℝ) - 1 := by
      have h := lt_of_le_of_lt (le_max_right _ _) hqa
      linarith
    filter_upwards [hm, (hq q hq1).eventually (eventually_gt_nhds haq)] with t hmt ht
    exact lt_of_lt_of_le ht (hmt hq1 (le_of_lt hx) (le_of_lt hqx))
  · intro b hb
    obtain ⟨q, hxq, hqb⟩ := exists_rat_btwn (show x < b + 1 by linarith)
    have hq1 : 1 ≤ (q : ℝ) := le_trans (le_of_lt hx) (le_of_lt hxq)
    have hqb' : (q : ℝ) - 1 < b := by linarith
    filter_upwards [hm, (hq q hq1).eventually (eventually_lt_nhds hqb')] with t hmt ht
    exact lt_of_le_of_lt (hmt (le_of_lt hx) hq1 (le_of_lt hxq)) ht


/-- To prove convergence of nonnegative interval masses to interval length
above 1, it suffices to check the countable family of intervals [1,q]. -/
theorem tendsto_intervalIntegral_of_rat_Ici
    {ι : Type*} {l : Filter ι} {f : ι → ℝ → ℝ}
    (hn : ∀ᶠ t in l, ∀ x : ℝ, 1 ≤ x → 0 ≤ f t x)
    (hi : ∀ t a b, IntervalIntegrable (f t) volume a b)
    (hq : ∀ q : ℚ, 1 ≤ (q : ℝ) →
      Tendsto (fun t => ∫ x in (1 : ℝ)..(q : ℝ), f t x) l (𝓝 ((q : ℝ) - 1)))
    {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Tendsto (fun t => ∫ x in a..b, f t x) l (𝓝 (b - a)) := by
  have hm : ∀ᶠ t in l, MonotoneOn
      (fun z => ∫ x in (1 : ℝ)..z, f t x) (Set.Ici 1) := by
    filter_upwards [hn] with t hnt
    intro x hx y hy hxy
    apply intervalIntegral.integral_mono_interval le_rfl hx hxy _ (hi t 1 y)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact hnt z (le_of_lt hz.1)
  have hl (z : ℝ) (hz : 1 ≤ z) :
      Tendsto (fun t => ∫ x in (1 : ℝ)..z, f t x) l (𝓝 (z - 1)) :=
    tendsto_monotoneOn_Ici_of_rat hm hq hz
  have hd := (hl b hb).sub (hl a ha)
  convert hd using 1
  · funext t
    have he := intervalIntegral.integral_add_adjacent_intervals (hi t 1 a) (hi t a b)
    linarith
  · congr 1
    ring


/-- Rational-point convergence and eventual monotonicity also control moving
arguments converging within the closed half-line. -/
theorem tendsto_monotoneOn_Ici_of_rat_moving
    {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ}
    (hm : ∀ᶠ t in l, MonotoneOn (F t) (Set.Ici 1))
    (hq : ∀ q : ℚ, 1 ≤ (q : ℝ) →
      Tendsto (fun t => F t q) l (𝓝 ((q : ℝ) - 1)))
    {y : ι → ℝ} {x : ℝ} (hx : 1 ≤ x)
    (hy : Tendsto y l (𝓝 x)) (hy1 : ∀ᶠ t in l, 1 ≤ y t) :
    Tendsto (fun t => F t (y t)) l (𝓝 (x - 1)) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases hx1 : x = 1
    · subst x
      have h1 : Tendsto (fun t => F t 1) l (𝓝 0) := by
        simpa using hq 1 (by norm_num)
      have ha' : a < 0 := by simpa using ha
      filter_upwards [hm, hy1, h1.eventually (eventually_gt_nhds ha')] with t hmt hyt ht
      exact lt_of_lt_of_le ht (hmt (by simp) hyt hyt)
    · have hx' : 1 < x := lt_of_le_of_ne hx (Ne.symm hx1)
      obtain ⟨q, hqa, hqx⟩ := exists_rat_btwn
        (show max 1 (a + 1) < x from max_lt hx' (by linarith))
      have hq1 : 1 ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hqa)
      have haq : a < (q : ℝ) - 1 := by
        have h := lt_of_le_of_lt (le_max_right _ _) hqa
        linarith
      filter_upwards [hm, hy1, (hq q hq1).eventually (eventually_gt_nhds haq),
        hy.eventually (eventually_gt_nhds hqx)] with t hmt hyt ht hqt
      exact lt_of_lt_of_le ht (hmt hq1 hyt (le_of_lt hqt))
  · intro b hb
    obtain ⟨q, hxq, hqb⟩ := exists_rat_btwn (show x < b + 1 by linarith)
    have hq1 : 1 ≤ (q : ℝ) := le_trans hx (le_of_lt hxq)
    have hqb' : (q : ℝ) - 1 < b := by linarith
    filter_upwards [hm, hy1, (hq q hq1).eventually (eventually_lt_nhds hqb'),
      hy.eventually (eventually_lt_nhds hxq)] with t hmt hyt ht htq
    exact lt_of_le_of_lt (hmt hyt hq1 (le_of_lt htq)) ht

/-- The rational anchored-mass provider controls interval integrals even when
both endpoints move with the limiting parameter. -/
theorem tendsto_intervalIntegral_of_rat_Ici_moving
    {ι : Type*} {l : Filter ι} {f : ι → ℝ → ℝ}
    (hn : ∀ᶠ t in l, ∀ x : ℝ, 1 ≤ x → 0 ≤ f t x)
    (hi : ∀ t a b, IntervalIntegrable (f t) volume a b)
    (hq : ∀ q : ℚ, 1 ≤ (q : ℝ) →
      Tendsto (fun t => ∫ x in (1 : ℝ)..(q : ℝ), f t x) l (𝓝 ((q : ℝ) - 1)))
    {a b : ℝ} {a' b' : ι → ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha' : Tendsto a' l (𝓝 a)) (hb' : Tendsto b' l (𝓝 b))
    (ha1 : ∀ᶠ t in l, 1 ≤ a' t) (hb1 : ∀ᶠ t in l, 1 ≤ b' t) :
    Tendsto (fun t => ∫ x in a' t..b' t, f t x) l (𝓝 (b - a)) := by
  have hm : ∀ᶠ t in l, MonotoneOn
      (fun z => ∫ x in (1 : ℝ)..z, f t x) (Set.Ici 1) := by
    filter_upwards [hn] with t hnt
    intro x hx y hy hxy
    apply intervalIntegral.integral_mono_interval le_rfl hx hxy _ (hi t 1 y)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact hnt z (le_of_lt hz.1)
  have hla := tendsto_monotoneOn_Ici_of_rat_moving hm hq ha ha' ha1
  have hlb := tendsto_monotoneOn_Ici_of_rat_moving hm hq hb hb' hb1
  have hd := hlb.sub hla
  convert hd using 1
  · funext t
    have he := intervalIntegral.integral_add_adjacent_intervals (hi t 1 (a' t))
      (hi t (a' t) (b' t))
    linarith
  · congr 1
    ring

end RiemannResearch.Analysis
