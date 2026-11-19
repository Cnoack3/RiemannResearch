import RiemannResearch.Analysis.ResidueOscillation
import RiemannResearch.RH.QDisplacementProfiniteContinuity
import RiemannResearch.RH.QFullDivisorProjection
import RiemannResearch.RH.QHilbertConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Finite-head oscillation of matched conductor projections

Source: the Stage 3 atom/carry CRT handoff, 14.7.2. The finite data here are
values of the actual difference of the two physical projections. A fixed
positive modulus and a fixed positive bound suffice. Each finite head may
select its own cofinal set of good stages.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QFullDisplacementFiniteHeads

open ZetaTwoHilbert QDisplacementProfiniteContinuity
open RiemannResearch.Analysis.ResidueOscillation

/-- Oscillation at positive sites up to a finite head, within classes modulo `L`. -/
def HeadBound (f : ℕ → ℝ) (L : ℕ) (C : ℝ) (H : ℕ) : Prop :=
  ∀ n m : ℕ, 0 < n → 0 < m → n ≤ H → m ≤ H → n % L = m % L →
    |f n - f m| ≤ C

/-- Failure of extension is detected by a single fixed pair at every sufficiently late
stage. The pair may depend on the modulus and the prescribed bound. -/
theorem eventual_bad_pair_of_no_extension
    {u : ℕ → QHilbert} (hu : Tendsto u atTop (𝓝 QFullDisplacement.displacement))
    (h : ¬ HasContinuousProfiniteExtension QFullDisplacement.displacement)
    (L : ℕ) (hL : 0 < L) (C : ℝ) :
    ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ n % L = m % L ∧
      ∀ᶠ j : ℕ in atTop, C < |qSequence (u j) n - qSequence (u j) m| := by
  have hbad : ¬ Bound (qSequence QFullDisplacement.displacement) L C := by
    intro hb
    have hr := (QFullCRTDisplacement.residual_zero_iff_finite_residue_oscillation L hL).mpr
      ⟨C, hb⟩
    exact h (Full.profinite_extension_iff_zero.mpr
      (QFullDisplacement.displacement_eq_zero_of_qResidual_eq_zero hr))
  unfold Bound at hbad
  push Not at hbad
  obtain ⟨n, m, hn, hm, hnm, hgt⟩ := hbad
  exact ⟨n, m, hn, hm, hnm, (((qSequence_tendsto_of_tendsto hu n).sub
    (qSequence_tendsto_of_tendsto hu m)).abs).eventually (Ioi_mem_nhds hgt)⟩

/-- Characterization for any approximants converging to the full physical displacement. -/
theorem extension_iff_frequent_head_bound
    {u : ℕ → QHilbert} (hu : Tendsto u atTop (𝓝 QFullDisplacement.displacement))
    (L : ℕ) (hL : 0 < L) (C : ℝ) (hC : 0 < C) :
    HasContinuousProfiniteExtension QFullDisplacement.displacement ↔
      ∀ H : ℕ, ∃ᶠ j : ℕ in atTop, HeadBound (qSequence (u j)) L C H := by
  constructor
  · intro hext
    have hz := Full.profinite_extension_iff_zero.mp hext
    have hsite (n : ℕ) : ∀ᶠ j : ℕ in atTop, |qSequence (u j) n| < C / 2 := by
      have ht := (qSequence_tendsto_of_tendsto hu n).abs
      simp only [hz, ← qEvalCLM_apply, map_zero, abs_zero] at ht
      simpa only [qEvalCLM_apply] using ht.eventually (Iio_mem_nhds (half_pos hC))
    have hhead (H : ℕ) :
        ∀ᶠ j : ℕ in atTop, ∀ n ≤ H, |qSequence (u j) n| < C / 2 := by
      induction H with
      | zero =>
        filter_upwards [hsite 0] with j hj n hn
        simpa only [Nat.le_zero.mp hn] using hj
      | succ H ih =>
        filter_upwards [ih, hsite (H + 1)] with j hj hk n hn
        rcases lt_or_eq_of_le hn with hlt | hEq
        · exact hj n (Nat.le_of_lt_succ hlt)
        · simpa only [hEq] using hk
    intro H
    apply Filter.Eventually.frequently
    filter_upwards [hhead H] with j hj
    intro n m _ _ hn hm _
    calc
      |qSequence (u j) n - qSequence (u j) m| ≤
          |qSequence (u j) n| + |qSequence (u j) m| := by
            simpa only [sub_zero, zero_sub, abs_neg] using
              abs_sub_le (qSequence (u j) n) 0 (qSequence (u j) m)
      _ ≤ C := by linarith [hj n hn, hj m hm]
  · intro hgood
    by_contra h
    obtain ⟨n, m, hn, hm, hnm, hbad⟩ := eventual_bad_pair_of_no_extension hu h L hL C
    obtain ⟨j, hj, hgt⟩ := ((hgood (max n m)).and_eventually hbad).exists
    exact (not_lt_of_ge (hj n m hn hm (le_max_left _ _) (le_max_right _ _) hnm)) hgt

/-- The equivalence on the actual all-divisor LCM stages for any monotone cofinal cutoff. -/
theorem lcm_extension_iff_frequent_head_bound
    (M : ℕ → ℕ) (hmono : Monotone M) (hM : Tendsto M atTop atTop)
    (L : ℕ) (hL : 0 < L) (C : ℝ) (hC : 0 < C) :
    HasContinuousProfiniteExtension QFullDisplacement.displacement ↔
      ∀ H : ℕ, ∃ᶠ j : ℕ in atTop, HeadBound
        (qSequence (QFullDivisorProjection.displacement (QFullDivisorProjection.lcmPeriod (M j))))
        L C H :=
  extension_iff_frequent_head_bound
    (QFullDivisorProjection.lcm_displacement_tendsto M hmono hM) L hL C hC

/-- Conditional RH consequence. The finite-head bound, uniform in the head size, is open. -/
theorem rh_of_lcm_frequent_head_bound
    (M : ℕ → ℕ) (hmono : Monotone M) (hM : Tendsto M atTop atTop)
    (L : ℕ) (hL : 0 < L) (C : ℝ) (hC : 0 < C)
    (h : ∀ H : ℕ, ∃ᶠ j : ℕ in atTop, HeadBound
      (qSequence (QFullDivisorProjection.displacement (QFullDivisorProjection.lcmPeriod (M j))))
      L C H) : RiemannHypothesis :=
  Full.rh_of_profinite_extension
    ((lcm_extension_iff_frequent_head_bound M hmono hM L hL C hC).mpr h)

end RiemannResearch.RH.QFullDisplacementFiniteHeads
