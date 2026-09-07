import RiemannResearch.RH.WeilExtension
import RiemannResearch.Analysis.CompactCutoffVerticalDecay
import Mathlib.Analysis.Normed.Group.Tannery

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual arithmetic-series convergence under the smooth compact cutoff

The unchanged von Mangoldt weights are bounded by the original test's
absolutely summable arithmetic terms. This removes the compact-test cutoff
on both signed arguments without dropping any prime power.
-/

open MeasureTheory Filter
open scoped Topology

namespace RiemannResearch.RH.SignedWeilCorrelation

open RiemannResearch.Analysis

theorem norm_compactCutoff_le (N : ℕ) (k : ℝ → ℂ) (x : ℝ) :
    ‖compactCutoff N k x‖ ≤ ‖k x‖ := by
  rw [compactCutoff, Pi.mul_apply, norm_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (norm_smoothCutoff_le_one N x) (norm_nonneg (k x))

theorem tendsto_compactCutoff_apply (k : ℝ → ℂ) (x : ℝ) :
    Tendsto (fun N : ℕ => compactCutoff N k x) atTop (𝓝 (k x)) := by
  apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => k x) atTop (𝓝 (k x))).congr'
  filter_upwards [eventually_iteratedDeriv_compactCutoff_eq k 0 x] with N hN
  simpa only [iteratedDeriv_zero] using hN.symm

theorem tendsto_paired_primePower_sum_compactCutoff {k : ℝ → ℂ}
    (hk : SmoothSuperexponentialDecay k) :
    Tendsto (fun N : ℕ => ∑' n : ℕ, (primePowerWeight n : ℂ) *
      (compactCutoff N k (Real.log n) + compactCutoff N k (-Real.log n))) atTop
      (𝓝 (∑' n : ℕ, (primePowerWeight n : ℂ) *
        (k (Real.log n) + k (-Real.log n)))) := by
  obtain ⟨A, _, hA⟩ := hk.decay 3 (by norm_num)
  have hp := summable_norm_primePowerTerm_of_exp_decay k A
    (fun t ht => by simpa only [abs_of_nonneg ht] using hA t)
  have hn := summable_norm_primePowerTerm_of_exp_decay (fun t => k (-t)) A
    (fun t ht => by simpa only [abs_neg, abs_of_nonneg ht] using hA (-t))
  apply tendsto_tsum_of_dominated_convergence (hp.add hn)
  · intro n
    exact ((tendsto_compactCutoff_apply k (Real.log n)).add
      (tendsto_compactCutoff_apply k (-Real.log n))).const_mul (primePowerWeight n : ℂ)
  · apply Eventually.of_forall
    intro N n
    have hb (x : ℝ) : ‖(primePowerWeight n : ℂ) * compactCutoff N k x‖ ≤
        ‖(primePowerWeight n : ℂ) * k x‖ := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_compactCutoff_le N k x) (norm_nonneg _)
    rw [mul_add]
    exact (norm_add_le _ _).trans (add_le_add (hb _) (hb _))

end RiemannResearch.RH.SignedWeilCorrelation
