import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

/-!
# Translation differences detect alternating Lebesgue points

The right moving averages of an integrable real function recover its values almost
everywhere. Four successive jumps in such averages are bounded by the global L¹
translation difference divided by the step. This implements the elementary
one-dimensional variation argument used for spectral DPP rigidity.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace RiemannResearch.DPPSpectral

noncomputable def rightAverage (f : ℝ → ℝ) (h x : ℝ) : ℝ := (∫ t in x..(x+h), f t) / h

theorem ae_tendsto_rightAverage {f : ℝ → ℝ} (hf : Integrable f)
    {h : ℕ → ℝ} (hp : ∀ n, 0 < h n) (hz : Tendsto h atTop (𝓝 0)) :
    ∀ᵐ x, Tendsto (fun n => rightAverage f (h n) x) atTop (𝓝 (f x)) := by
  have ht : Tendsto h atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, Eventually.of_forall hp⟩
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf.locallyIntegrable] with x hx
  simpa [Function.comp_def, rightAverage, div_eq_inv_mul, smul_eq_mul] using
    ((hx x).tendsto_slope_zero_right.comp ht)

private theorem average_step_le {f : ℝ → ℝ} (hf : Integrable f) {h a b : ℝ}
    (hp : 0 < h) (hab : a ≤ b) :
    |rightAverage f h b - rightAverage f h a| ≤
      (∫ t in a..b, |f (t+h) - f t|) / h := by
  have eq : (∫ t in b..(b+h), f t) - (∫ t in a..(a+h), f t) =
      ∫ t in a..b, f (t+h) - f t := by
    rw [intervalIntegral.integral_sub (hf.comp_add_right h).intervalIntegrable
      hf.intervalIntegrable,
      intervalIntegral.integral_comp_add_right]
    exact intervalIntegral.integral_interval_sub_interval_comm'
      hf.intervalIntegrable hf.intervalIntegrable hf.intervalIntegrable
  rw [rightAverage, rightAverage, ← sub_div, eq, abs_div, abs_of_pos hp]
  exact div_le_div_of_nonneg_right (intervalIntegral.abs_integral_le_integral_abs hab) hp.le

/-- For any five ordered probes, the sum of the four adjacent oscillations of the
right moving average is bounded by the normalized total translation difference. -/
theorem fivePoint_variation_bound {f : ℝ → ℝ} (hf : Integrable f) {h a b c d e : ℝ}
    (hp : 0 < h) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) (hde : d ≤ e) :
    |rightAverage f h b - rightAverage f h a| + |rightAverage f h c - rightAverage f h b| +
    |rightAverage f h d - rightAverage f h c| + |rightAverage f h e - rightAverage f h d| ≤
    (∫ t, |f t - f (t+h)|) / h := by
  let g := fun t => |f (t+h) - f t|
  have hg : Integrable g := ((hf.comp_add_right h).sub hf).abs
  have hsum : ((∫ t in a..b, g t) + (∫ t in b..c, g t) + (∫ t in c..d, g t) +
      (∫ t in d..e, g t)) = ∫ t in a..e, g t := by
    rw [intervalIntegral.integral_add_adjacent_intervals hg.intervalIntegrable
      hg.intervalIntegrable,
      intervalIntegral.integral_add_adjacent_intervals hg.intervalIntegrable hg.intervalIntegrable,
      intervalIntegral.integral_add_adjacent_intervals hg.intervalIntegrable hg.intervalIntegrable]
  have hglobal : (∫ t in a..e, g t) ≤ ∫ t, |f t - f (t+h)| := by
    rw [intervalIntegral.integral_of_le (hab.trans (hbc.trans (hcd.trans hde)))]
    have ig := setIntegral_le_integral (s := Ioc a e) hg (ae_of_all _ fun x => abs_nonneg _)
    exact ig.trans_eq (integral_congr_ae (ae_of_all _ fun x => abs_sub_comm (f (x+h)) (f x)))
  have h := add_le_add (add_le_add (add_le_add (average_step_le hf hp hab)
    (average_step_le hf hp hbc)) (average_step_le hf hp hcd)) (average_step_le hf hp hde)
  refine h.trans ?_
  change (∫ t in a..b, g t) / _ + (∫ t in b..c, g t) / _ + (∫ t in c..d, g t) / _ +
    (∫ t in d..e, g t) / _ ≤ _
  rw [← add_div, ← add_div, ← add_div, hsum]
  exact div_le_div_of_nonneg_right hglobal hp.le

end RiemannResearch.DPPSpectral
