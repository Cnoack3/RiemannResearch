/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QScaledTailPerturbation
import Mathlib.Tactic.Linarith

/-!
# Uniform complete tails of norm-convergent Q sequences

Source: direct compactness argument developed for the user's signed regularity
handoff. This supplies unscaled uniform tail tightness, without a rate.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QAnnihilatorTailEscape
open ZetaTwoHilbert QFiniteSupportDualCriterion

theorem tail_norm_le (H : ℕ) (f : QHilbert) : ‖tail H f‖ ≤ ‖f‖ := by
  have h := finiteHead_norm_sq_split H f
  change ‖f - finiteHead H f‖ ≤ ‖f‖
  nlinarith [sq_nonneg ‖finiteHead H f‖, norm_nonneg f,
    norm_nonneg (f - finiteHead H f)]

theorem tail_norm_le_sub_add (H : ℕ) (f g : QHilbert) :
    ‖tail H f‖ ≤ ‖f - g‖ + ‖tail H g‖ := by
  calc
    ‖tail H f‖ = ‖tail H (f - g) + tail H g‖ := by
      rw [tail_sub, sub_add_cancel]
    _ ≤ ‖tail H (f - g)‖ + ‖tail H g‖ := norm_add_le _ _
    _ ≤ ‖f - g‖ + ‖tail H g‖ :=
      add_le_add (tail_norm_le H (f - g)) le_rfl

private theorem eventually_tail_norm_lt_finite (f : ℕ → QHilbert)
    (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ H in atTop, ∀ n < K, ‖tail H (f n)‖ < ε := by
  induction K with
  | zero => exact Filter.Eventually.of_forall (by simp)
  | succ K ih =>
    have ht : Tendsto (fun H => ‖tail H (f K)‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using (tail_tendsto_zero (f K)).norm
    have hK := (tendsto_order.1 ht).2 ε hε
    filter_upwards [ih, hK] with H hH hHK
    intro n hn
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hn) with hlt | rfl
    · exact hH n hlt
    · exact hHK

/-- Every norm-convergent sequence is uniformly tight for complete Q tails.
This does not give a rate and does not give scaled-tail boundedness. -/
theorem uniform_tail_tightness_of_tendsto (f : ℕ → QHilbert) (g : QHilbert)
    (hf : Tendsto f atTop (𝓝 g)) (ε : ℝ) (hε : 0 < ε) :
    ∃ H₀ : ℕ, ∀ H ≥ H₀, ∀ n : ℕ, ‖tail H (f n)‖ < ε := by
  have hhalf : 0 < ε / 2 := by linarith
  have hdiff : Tendsto (fun n => ‖f n - g‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (hf.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => g) atTop (𝓝 g))).norm
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1
    ((tendsto_order.1 hdiff).2 (ε / 2) hhalf)
  have hg : Tendsto (fun H => ‖tail H g‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using (tail_tendsto_zero g).norm
  have hgsmall := (tendsto_order.1 hg).2 (ε / 2) hhalf
  have hfinite := eventually_tail_norm_lt_finite f K ε hε
  have hevent : ∀ᶠ H in atTop, ∀ n : ℕ, ‖tail H (f n)‖ < ε := by
    filter_upwards [hgsmall, hfinite] with H hHg hHfinite
    intro n
    by_cases hn : n < K
    · exact hHfinite n hn
    · have hnorm : ‖f n - g‖ < ε / 2 := hK n (Nat.le_of_not_gt hn)
      have hb := tail_norm_le_sub_add H (f n) g
      linarith
  exact Filter.eventually_atTop.1 hevent

end RiemannResearch.RH.QAnnihilatorTailEscape
