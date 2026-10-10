import RiemannResearch.Analysis.WeightedMellinTopologyTargets
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Higher derivative continuity from weighted Mellin energy

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

These elementary Cauchy bounds prove quantitative continuity for every
derivative order. They do not assert the sharper logarithmic-kernel
factorial constant recorded in DerivativeEvaluationBoundProvider, and
do not supply HigherDerivativeIntegralProvider.

The only analytic inputs are the project's already proved point-evaluation
and holomorphy theorems, and Mathlib's Cauchy estimate on a closed disc.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped Topology

namespace RiemannResearch.Analysis.WeightedMellinTopology
open MeasureTheory.WeightedMellin

theorem normSquared_nonneg (a : ℝ) (f : ℝ → ℂ) : 0 ≤ normSquared a f := by
  unfold normSquared energy
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (lt_trans zero_lt_one hx).le _)

private theorem realPart_ge_sub_radius {z w : ℂ} {R : ℝ}
    (hw : w ∈ closedBall z R) : z.re - R ≤ w.re := by
  have hn : ‖w - z‖ ≤ R := by
    simpa only [dist_eq_norm] using (mem_closedBall.mp hw)
  have hr := (abs_le.mp (Complex.abs_re_le_norm (w - z))).1
  simp only [Complex.sub_re] at hr
  linarith

/-- Every closed disc strictly inside the weighted half-plane has an
explicit pointwise bound, derived from the exact project evaluation norm. -/
theorem transform_norm_bound_closedBall {f : ℝ → ℂ} {a : ℝ}
    (hf : Ha a f) {z w : ℂ} {R : ℝ} (hR : R < z.re - a)
    (hw : w ∈ closedBall z R) :
    ‖transform f w‖ ≤ Real.sqrt (normSquared a f / (2 * (z.re - a - R))) := by
  have hr := realPart_ge_sub_radius hw
  have ha : a < w.re := by linarith
  have hd : 0 < 2 * (w.re - a) := by linarith
  have hd0 : 0 < 2 * (z.re - a - R) := by linarith
  have hden : 2 * (z.re - a - R) ≤ 2 * (w.re - a) := by linarith
  have hpoint := (le_div_iff₀ hd).mp (evaluation_norm_sq_le hf ha)
  have hprod := mul_le_mul_of_nonneg_left hden (sq_nonneg ‖transform f w‖)
  have hsq : ‖transform f w‖ ^ 2 ≤ normSquared a f / (2 * (z.re - a - R)) :=
    (le_div_iff₀ hd0).mpr (hprod.trans hpoint)
  have hs := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _)] at hs

/-- Cauchy's estimate supplies an unconditional bound for every derivative
evaluation; the radius is freely chosen inside the half-plane margin. -/
theorem evaluation_iteratedDeriv_cauchy_bound {f : ℝ → ℂ} {a : ℝ}
    (hf : Ha a f) (k : ℕ) {z : ℂ} {R : ℝ}
    (hR0 : 0 < R) (hR : R < z.re - a) :
    ‖iteratedDeriv k (transform f) z‖ ≤
      (k.factorial : ℝ) *
        Real.sqrt (normSquared a f / (2 * (z.re - a - R))) / R ^ k := by
  have hdiff : DifferentiableOn ℂ (transform f) {w : ℂ | a < w.re} := by
    intro w hw
    change a < w.re at hw
    have ha := transform_analyticAt hf (by linarith : (2 * a) / 2 < w.re)
    exact ha.differentiableAt.differentiableWithinAt
  have hclosed : closedBall z R ⊆ {w : ℂ | a < w.re} := by
    intro w hw
    have hr := realPart_ge_sub_radius hw
    change a < w.re
    linarith
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR0
    (hdiff.diffContOnCl_ball hclosed)
    (fun w hw => transform_norm_bound_closedBall hf hR (sphere_subset_closedBall hw))

theorem evaluation_iteratedDeriv_cauchy_norm_sq_le {f : ℝ → ℂ} {a : ℝ}
    (hf : Ha a f) (k : ℕ) {z : ℂ} {R : ℝ}
    (hR0 : 0 < R) (hR : R < z.re - a) :
    ‖iteratedDeriv k (transform f) z‖ ^ 2 ≤
      (k.factorial : ℝ) ^ 2 * normSquared a f /
        (2 * (z.re - a - R) * R ^ (2 * k)) := by
  have hd : 0 < 2 * (z.re - a - R) := by linarith
  have hq : 0 ≤ normSquared a f / (2 * (z.re - a - R)) :=
    div_nonneg (normSquared_nonneg a f) hd.le
  calc
    ‖iteratedDeriv k (transform f) z‖ ^ 2 ≤
        ((k.factorial : ℝ) *
          Real.sqrt (normSquared a f / (2 * (z.re - a - R))) / R ^ k) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (evaluation_iteratedDeriv_cauchy_bound hf k hR0 hR) 2
    _ = (k.factorial : ℝ) ^ 2 * normSquared a f /
          (2 * (z.re - a - R) * R ^ (2 * k)) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hq, ← pow_mul, Nat.mul_comm k 2]
      field_simp [ne_of_gt hd, ne_of_gt hR0]
      <;> ring

/-- A convenient fixed-radius bound for every derivative. -/
theorem evaluation_iteratedDeriv_half_margin {f : ℝ → ℂ} {a : ℝ}
    (hf : Ha a f) (k : ℕ) {z : ℂ} (hz : a < z.re) :
    ‖iteratedDeriv k (transform f) z‖ ^ 2 ≤
      (k.factorial : ℝ) ^ 2 * normSquared a f /
        ((z.re - a) * ((z.re - a) / 2) ^ (2 * k)) := by
  have hR0 : 0 < (z.re - a) / 2 := by linarith
  have hR : (z.re - a) / 2 < z.re - a := by linarith
  have h := evaluation_iteratedDeriv_cauchy_norm_sq_le hf k hR0 hR
  simpa only [show 2 * (z.re - a - (z.re - a) / 2) = z.re - a by ring] using h

end RiemannResearch.Analysis.WeightedMellinTopology
