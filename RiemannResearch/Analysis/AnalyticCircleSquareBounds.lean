import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-!
Analytic control of compact uniform norms from finitely many circle second
moments. The analytic input is mathlib's proved complex Cauchy/mean-value
formula (`DiffContOnCl.circleAverage_smul_div`); Jensen's inequality and the
compact finite-subcover theorem supply the remaining steps. These results are
standard analytic consequences and do not claim new literature theorems.

Mathlib source (supports the imported analytic/arithmetic identity):
https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/Complex/MeanValue.lean
-/

open Complex Filter Metric Real Set MeasureTheory
open scoped Interval

namespace RiemannResearch.Analysis
namespace AnalyticCircleSquareBounds

/-- Circle averaging is a contraction from the circle's integral norm. -/
theorem norm_circleAverage_le (g : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    ‖circleAverage g c R‖ ≤ circleAverage (fun z => ‖g z‖) c R := by
  simp only [circleAverage_def, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos Real.two_pi_pos, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le)
    (inv_nonneg.mpr Real.two_pi_pos.le)

/-- Jensen on the circle. No holomorphic hypothesis is used in this lemma. -/
theorem sq_norm_circleAverage_le {g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hg : ContinuousOn g (sphere c |R|)) :
    ‖circleAverage g c R‖ ^ 2 ≤ circleAverage (fun z => ‖g z‖ ^ 2) c R := by
  have hcont : Continuous (fun θ : ℝ => ‖g (circleMap c R θ)‖) :=
    (hg.comp_continuous (continuous_circleMap c R)
      (circleMap_mem_sphere' c R)).norm
  have hnonneg : 0 ≤ circleAverage (fun z => ‖g z‖) c R :=
    circleAverage_nonneg_of_nonneg (fun z hz => norm_nonneg _)
  calc
    ‖circleAverage g c R‖ ^ 2
      ≤ (circleAverage (fun z => ‖g z‖) c R) ^ 2 := by
          nlinarith [norm_circleAverage_le g c R, norm_nonneg (circleAverage g c R)]
    _ ≤ circleAverage (fun z => ‖g z‖ ^ 2) c R := by
      rw [circleAverage_eq_intervalAverage, circleAverage_eq_intervalAverage]
      exact (convexOn_pow 2).map_set_average_le
        (continuousOn_pow 2) isClosed_Ici (by simp)
        (by rw [uIoc_of_le Real.two_pi_pos.le]; exact measure_Ioc_lt_top.ne)
        (by filter_upwards; simp)
        hcont.integrableOn_uIoc
        ((continuous_pow 2).comp hcont).integrableOn_uIoc

/-- The center evaluation of a holomorphic function is bounded by the circle's
    mean square, with exact constant one. -/
theorem sq_norm_center_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : DiffContOnCl ℂ f (ball c |R|)) :
    ‖f c‖ ^ 2 ≤ circleAverage (fun z => ‖f z‖ ^ 2) c R := by
  by_cases hR : R = 0
  · simp [hR]
  have hpos : 0 < |R| := abs_pos.mpr hR
  have hfc : ContinuousOn f (sphere c |R|) := by
    apply hf.2.mono
    rw [closure_ball c hpos.ne']
    exact sphere_subset_closedBall
  simpa only [hf.circleAverage] using sq_norm_circleAverage_le hfc

/-- A uniform inner-disk mean-square bound, proved directly from Cauchy's
    weighted mean-value formula. This replaces an assumed compact L²-to-sup
    estimate by an actual analytic theorem. -/
theorem sq_norm_le_circleAverage_innerDisk {f : ℂ → ℂ} {c w : ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hf : DiffContOnCl ℂ f (ball c |R|)) (hw : w ∈ closedBall c r) :
    ‖f w‖ ^ 2 ≤ (R / (R - r)) ^ 2 * circleAverage (fun z => ‖f z‖ ^ 2) c R := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have hwNorm : ‖w - c‖ ≤ r := mem_closedBall_iff_norm.mp hw
  have hwBall : w ∈ ball c |R| := by
    rw [abs_of_pos hR, mem_ball_iff_norm]
    exact lt_of_le_of_lt hwNorm hrR
  have hfc : ContinuousOn f (sphere c |R|) := by
    apply hf.2.mono
    rw [closure_ball c (by positivity : |R| ≠ 0)]
    exact sphere_subset_closedBall
  let g : ℂ → ℂ := fun z => ((z - c) / (z - w)) * f z
  have hden : ∀ z ∈ sphere c |R|, 0 < ‖z - w‖ := by
    intro z hz
    have hzNorm : ‖z - c‖ = R := by
      simpa only [abs_of_pos hR] using mem_sphere_iff_norm.mp hz
    have htri := norm_sub_norm_le (z - c) (w - c)
    have heq : (z - c) - (w - c) = z - w := by ring
    rw [heq] at htri
    nlinarith
  have hgc : ContinuousOn g (sphere c |R|) := by
    apply ContinuousOn.mul _ hfc
    apply ContinuousOn.div (continuousOn_id.sub continuousOn_const)
      (continuousOn_id.sub continuousOn_const)
    intro z hz
    exact norm_pos_iff.mp (hden z hz)
  have hmean : circleAverage g c R = f w := by
    simpa only [g, smul_eq_mul] using hf.circleAverage_smul_div hwBall
  have hpoint : ∀ z ∈ sphere c |R|,
      ‖g z‖ ^ 2 ≤ (R / (R - r)) ^ 2 * ‖f z‖ ^ 2 := by
    intro z hz
    have hzNorm : ‖z - c‖ = R := by
      simpa only [abs_of_pos hR] using mem_sphere_iff_norm.mp hz
    have htri := norm_sub_norm_le (z - c) (w - c)
    have heq : (z - c) - (w - c) = z - w := by ring
    rw [heq, hzNorm] at htri
    have hratio : ‖(z - c) / (z - w)‖ ≤ R / (R - r) := by
      rw [norm_div, hzNorm]
      apply (div_le_div_iff₀ (hden z hz) hRr).2
      nlinarith
    have hratio0 : 0 ≤ R / (R - r) := le_of_lt (div_pos hR hRr)
    have hsq : ‖(z - c) / (z - w)‖ ^ 2 ≤ (R / (R - r)) ^ 2 := by
      nlinarith [norm_nonneg ((z - c) / (z - w))]
    simpa only [g, norm_mul, mul_pow] using
      mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖f z‖)
  calc
    ‖f w‖ ^ 2 = ‖circleAverage g c R‖ ^ 2 := by rw [hmean]
    _ ≤ circleAverage (fun z => ‖g z‖ ^ 2) c R := sq_norm_circleAverage_le hgc
    _ ≤ circleAverage (fun z => (R / (R - r)) ^ 2 * ‖f z‖ ^ 2) c R := by
      apply circleAverage_mono (hgc.norm.pow 2).circleIntegrable'
        ((continuousOn_const.mul (hfc.norm.pow 2)).circleIntegrable') hpoint
    _ = (R / (R - r)) ^ 2 * circleAverage (fun z => ‖f z‖ ^ 2) c R := by
      simpa only [smul_eq_mul] using circleAverage_fun_smul
        (a := (R / (R - r)) ^ 2) (f := fun z => ‖f z‖ ^ 2) (c := c) (R := R)

/-- Every compact set in an open domain admits a finite collection of circle
    mean-square functionals controlling all point evaluations, with universal
    coefficient four. The circles and radii depend only on the domain and
    compact set, and are independent of the analytic function. -/
theorem exists_compact_circleSquare_control {K U : Set ℂ}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (S : Finset K) (R : K → ℝ),
      (∀ c : K, 0 < R c ∧ closedBall (c : ℂ) (R c) ⊆ U) ∧
      ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f U → ∀ w ∈ K,
        ‖f w‖ ^ 2 ≤ 4 * ∑ c ∈ S, circleAverage (fun z => ‖f z‖ ^ 2) (c : ℂ) (R c) := by
  classical
  have hex : ∀ c : K, ∃ r : ℝ, 0 < r ∧ closedBall (c : ℂ) r ⊆ U := by
    intro c
    exact Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds (hKU c.property))
  choose R hRpos hRsub using hex
  have hcover : K ⊆ ⋃ c : K, ball (c : ℂ) (R c / 2) := by
    intro w hw
    apply mem_iUnion.mpr
    refine ⟨⟨w, hw⟩, ?_⟩
    exact mem_ball_self (div_pos (hRpos ⟨w, hw⟩) (by norm_num))
  obtain ⟨S, hS⟩ := hK.elim_finite_subcover
    (fun c : K => ball (c : ℂ) (R c / 2)) (fun _ => isOpen_ball) hcover
  refine ⟨S, R, (fun c => ⟨hRpos c, hRsub c⟩), ?_⟩
  intro f hf w hw
  rcases mem_iUnion.mp (hS hw) with ⟨c, hc⟩
  rcases mem_iUnion.mp hc with ⟨hcS, hwc⟩
  have hDiff : DiffContOnCl ℂ f (ball (c : ℂ) |R c|) := by
    simpa only [abs_of_pos (hRpos c)] using hf.diffContOnCl_ball (hRsub c)
  have hb := sq_norm_le_circleAverage_innerDisk
    (le_of_lt (div_pos (hRpos c) (by norm_num))) (by nlinarith [hRpos c]) hDiff
    (ball_subset_closedBall hwc)
  have hdenne : R c - R c / 2 ≠ 0 := by nlinarith [hRpos c]
  have hratio : R c / (R c - R c / 2) = 2 := (div_eq_iff hdenne).mpr (by ring)
  rw [hratio] at hb
  norm_num only at hb
  have hterm : circleAverage (fun z => ‖f z‖ ^ 2) (c : ℂ) (R c) ≤
      ∑ i ∈ S, circleAverage (fun z => ‖f z‖ ^ 2) (i : ℂ) (R i) := by
    apply Finset.single_le_sum _ hcS
    intro i hi
    exact circleAverage_nonneg_of_nonneg (fun z hz => sq_nonneg ‖f z‖)
  exact hb.trans (mul_le_mul_of_nonneg_left hterm (by norm_num))

end AnalyticCircleSquareBounds
end RiemannResearch.Analysis
