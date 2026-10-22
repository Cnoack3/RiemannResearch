/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteSpectralBudget
import Mathlib.Topology.Algebra.Order.Field

/-!
# Complete source mass escaping to infinity

Source: user-provided Green-Pareto-Schur continuation, Appendix C,
and its finite source-mass improvement.
This module strengthens the finite spectral consumer without asserting an
arithmetic provider. If the complete optimizer tail S tends to zero while
the correction T tends to delta, then the source mass above EVERY fixed
positive threshold tends to exactly delta. Consequently tightness at infinity
is equivalent to zero defect. The normalized logarithmic and double-logarithmic
conditions are sufficient ways to furnish this tightness, not consequences of
tail convergence or eigenvalue positivity.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.FiniteSpectralBudget

variable {ι : Type*}

theorem highMass_tendsto_of_correction_and_tail
    (s : ℕ → Finset ι) (w lam : ℕ → ι → ℝ) (delta R : ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i) (hR : 0 < R)
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hS : Tendsto (fun n => optimizerTail (s n) (w n) (lam n)) atTop (𝓝 0)) :
    Tendsto (fun n => highMass (s n) (w n) (lam n) R) atTop (𝓝 delta) := by
  have hdiff : Tendsto (fun n =>
      highMass (s n) (w n) (lam n) R - correction (s n) (w n) (lam n))
      atTop (𝓝 0) := by
    have habs : Tendsto (fun n =>
        |highMass (s n) (w n) (lam n) R - correction (s n) (w n) (lam n)|)
        atTop (𝓝 0) := by
      apply squeeze_zero (fun n => abs_nonneg _)
        (fun n => abs_highMass_sub_correction_le_threshold_tail
          (s n) (w n) (lam n) R (hw n) (hlam n) hR)
      simpa using hS.const_mul (max (1+R) ((1+R)/R))
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [habs.eventually (Iio_mem_nhds (neg_pos.mpr ha))] with n hn
      have hlow := neg_abs_le
        (highMass (s n) (w n) (lam n) R - correction (s n) (w n) (lam n))
      linarith
    · intro b hb
      filter_upwards [habs.eventually (Iio_mem_nhds hb)] with n hn
      exact (le_abs_self _).trans_lt hn
  convert hdiff.add hT using 1 <;> simp

/-- At one fixed positive threshold, no escaped mass is already equivalent
to zero defect. It is unnecessary to impose convergence at every threshold. -/
theorem highMass_tendsto_zero_iff_defect_zero
    (s : ℕ → Finset ι) (w lam : ℕ → ι → ℝ) (delta R : ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i) (hR : 0 < R)
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hS : Tendsto (fun n => optimizerTail (s n) (w n) (lam n)) atTop (𝓝 0)) :
    Tendsto (fun n => highMass (s n) (w n) (lam n) R) atTop (𝓝 0) ↔
      delta = 0 := by
  have hB := highMass_tendsto_of_correction_and_tail s w lam delta R hw hlam hR hT hS
  constructor
  · intro hz
    exact tendsto_nhds_unique hB hz
  · intro hz
    simpa only [hz] using hB

/-- A moving cutoff is permitted all the way up to a vanishing low spectral
budget. At these cutoffs, escaped source mass converges to the SAME defect. -/
theorem moving_highMass_tendsto_of_correction_and_low_budget
    (s : ℕ → Finset ι) (w lam : ℕ → ι → ℝ) (delta : ℝ) (R : ℕ → ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i) (hR : ∀ n, 1 ≤ R n)
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hlow : Tendsto (fun n =>
      (1+R n) * optimizerTail (s n) (w n) (lam n)) atTop (𝓝 0)) :
    Tendsto (fun n => highMass (s n) (w n) (lam n) (R n)) atTop (𝓝 delta) := by
  have hdiff : Tendsto (fun n =>
      highMass (s n) (w n) (lam n) (R n) - correction (s n) (w n) (lam n))
      atTop (𝓝 0) := by
    have habs : Tendsto (fun n =>
        |highMass (s n) (w n) (lam n) (R n) - correction (s n) (w n) (lam n)|)
        atTop (𝓝 0) := by
      apply squeeze_zero (fun n => abs_nonneg _) _ hlow
      intro n
      have hpos : 0 < R n := lt_of_lt_of_le zero_lt_one (hR n)
      have hratio : (1+R n)/(R n) ≤ 1+R n := by
        apply (div_le_iff₀ hpos).mpr
        nlinarith [hR n]
      have hbound := abs_highMass_sub_correction_le_threshold_tail
        (s n) (w n) (lam n) (R n) (hw n) (hlam n) hpos
      simpa only [max_eq_left hratio] using hbound
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [habs.eventually (Iio_mem_nhds (neg_pos.mpr ha))] with n hn
      have hlow := neg_abs_le
        (highMass (s n) (w n) (lam n) (R n) - correction (s n) (w n) (lam n))
      linarith
    · intro b hb
      filter_upwards [habs.eventually (Iio_mem_nhds hb)] with n hn
      exact (le_abs_self _).trans_lt hn
  convert hdiff.add hT using 1 <;> simp

/-- Standard tightness, stated in an eventual form appropriate to variable
finite spectra. This retains all original source weights. -/
def SourceTightAtInfinity (s : ℕ → Finset ι) (w lam : ℕ → ι → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ∀ᶠ n in atTop, highMass (s n) (w n) (lam n) R ≤ ε

/-- Under unconditional tail decay and existence of the correction limit,
the exact additional condition is complete-source tightness at infinity. -/
theorem sourceTightAtInfinity_iff_defect_zero
    (s : ℕ → Finset ι) (w lam : ℕ → ι → ℝ) (delta : ℝ)
    (hw : ∀ n i, i ∈ s n → 0 ≤ w n i)
    (hlam : ∀ n i, i ∈ s n → 0 ≤ lam n i)
    (hT : Tendsto (fun n => correction (s n) (w n) (lam n)) atTop (𝓝 delta))
    (hS : Tendsto (fun n => optimizerTail (s n) (w n) (lam n)) atTop (𝓝 0)) :
    SourceTightAtInfinity s w lam ↔ delta = 0 := by
  have hdelta : 0 ≤ delta :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hT (Filter.Eventually.of_forall
      (fun n => correction_nonneg (s n) (w n) (lam n) (hw n) (hlam n)))
  constructor
  · intro htight
    by_contra hne
    have hpos : 0 < delta := lt_of_le_of_ne hdelta (Ne.symm hne)
    obtain ⟨R, hR, hupper⟩ := htight (delta/2) (by linarith)
    have hB := highMass_tendsto_of_correction_and_tail s w lam delta R hw hlam hR hT hS
    have hlower := hB.eventually_const_lt (show delta/2 < delta by linarith)
    obtain ⟨n, hn⟩ := (hupper.and hlower).exists
    linarith [hn.1, hn.2]
  · intro hzero ε hε
    refine ⟨1, by norm_num, ?_⟩
    have hz := (highMass_tendsto_zero_iff_defect_zero s w lam delta 1
      hw hlam (by norm_num) hT hS).mpr hzero
    exact (hz.eventually_lt_const hε).mono (fun n hn => le_of_lt hn)

end RiemannResearch.Analysis.FiniteSpectralBudget
