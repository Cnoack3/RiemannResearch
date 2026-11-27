import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # A cofinal absorption criterion for two errors with a common limit

This real-sequence lemma applies to the total and remaining errors of a fixed
finite zero family in §9 of the Mellin/prime-orbit handoff.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis

/-- Among two real errors with the same nonnegative limit, cofinal absorption
by a strict constant with a vanishing additive budget detects exactly a zero
limit. This allows the good cutoff set to depend on the chosen budget. -/
theorem common_limit_zero_iff_cofinal_absorption {E R : ℕ → ℝ} {e θ : ℝ}
    (he : 0 ≤ e) (hE : Tendsto E atTop (𝓝 e)) (hR : Tendsto R atTop (𝓝 e))
    (hθ : θ < 1) :
    e = 0 ↔ ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ Tendsto B atTop (𝓝 0) ∧
      ∃ᶠ n in atTop, R n ≤ θ * E n + B n := by
  constructor
  · rintro rfl
    refine ⟨fun n => |R n - θ * E n|, fun n => abs_nonneg _, ?_, ?_⟩
    · simpa only [mul_zero, sub_zero, abs_zero] using (hR.sub (hE.const_mul θ)).abs
    · apply Filter.Eventually.frequently
      apply Filter.Eventually.of_forall
      intro n
      linarith [le_abs_self (R n - θ * E n)]
  · rintro ⟨B, _, hB, hab⟩
    by_contra h
    have hpos : 0 < e := lt_of_le_of_ne he (Ne.symm h)
    have hgap : Tendsto (fun n => R n - (θ * E n + B n)) atTop (𝓝 (e - θ * e)) := by
      simpa only [add_zero] using hR.sub ((hE.const_mul θ).add hB)
    have hgap_pos : 0 < e - θ * e := by nlinarith [mul_pos (sub_pos.mpr hθ) hpos]
    apply hab
    filter_upwards [hgap.eventually (lt_mem_nhds hgap_pos)] with n hn
    exact not_le_of_gt (sub_pos.mp hn)

/-- When the common limit is positive, the relative remainder tends to one.
The first-order asymptotic of the absolute loss gives that of the relative
loss on the same scale. -/
theorem common_positive_limit_relative_loss {E R S : ℕ → ℝ} {e c : ℝ}
    (he : 0 < e) (hE : Tendsto E atTop (𝓝 e)) (hR : Tendsto R atTop (𝓝 e))
    (hS : Tendsto (fun n => S n * (E n - R n)) atTop (𝓝 c)) :
    Tendsto (fun n => R n / E n) atTop (𝓝 1) ∧
    Tendsto (fun n => S n * (E n - R n) / E n) atTop (𝓝 (c / e)) :=
  ⟨by simpa only [Pi.div_def, div_self he.ne'] using hR.div hE he.ne', hS.div hE he.ne'⟩

/-- Without an additive budget, a cofinal strict relative improvement forces
a reciprocal-scale upper bound for the original error along the good cutoffs.
The coefficient is the first-order loss divided by the fraction removed. -/
theorem frequently_scaled_error_le_of_relative_absorption {E R S : ℕ → ℝ} {c θ : ℝ}
    (hS : ∀ n, 0 ≤ S n) (hθ : θ < 1)
    (hloss : Tendsto (fun n => S n * (E n - R n)) atTop (𝓝 c))
    (hrel : ∃ᶠ n in atTop, R n ≤ θ * E n) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n in atTop, S n * E n ≤ (c + ε) / (1 - θ) := by
  have hupper := hloss.eventually (gt_mem_nhds (show c < c + ε by linarith))
  apply (hrel.and_eventually hupper).mono
  intro n hn
  obtain ⟨hr, hu⟩ := hn
  apply (le_div_iff₀ (sub_pos.mpr hθ)).mpr
  calc
    S n * E n * (1 - θ) = S n * (E n - θ * E n) := by ring
    _ ≤ S n * (E n - R n) := mul_le_mul_of_nonneg_left (sub_le_sub_left hr _) (hS n)
    _ ≤ c + ε := le_of_lt hu

end RiemannResearch.Analysis
