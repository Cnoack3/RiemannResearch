import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Holomorphic parameter integrals with a local majorant

A Cauchy bound on a smaller parameter disc supplies domination for the
derivative. This permits analytic continuation of scalar tests of the
weighted critical-line family. -/

open Set MeasureTheory Filter Metric
open scoped Topology
noncomputable section
namespace RiemannResearch.Analysis.DominatedHolomorphicTest

theorem analyticAt_parameter_integral {F : ℂ → ℝ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) {M : ℝ → ℝ} (hM : Integrable M)
    (hF : ∀ w ∈ ball z r, AEStronglyMeasurable (F w) volume)
    (hF' : ∀ w ∈ ball z r,
      AEStronglyMeasurable (fun t => deriv (fun u => F u t) w) volume)
    (ha : ∀ t w, w ∈ ball z r → DifferentiableAt ℂ (fun u => F u t) w)
    (hb : ∀ᵐ t, ∀ w ∈ ball z r, ‖F w t‖ ≤ M t) :
    AnalyticAt ℂ (fun w => ∫ t, F w t) z := by
  have hsub {p q : ℂ} (hp : p ∈ ball z (r/2)) (hq : q ∈ closedBall p (r/4)) :
      q ∈ ball z r := by
    rw [mem_ball] at hp ⊢
    rw [mem_closedBall] at hq
    exact (dist_triangle q p z).trans_lt (by linarith)
  have hder : ∀ᵐ t, ∀ w ∈ ball z (r/2), ‖deriv (fun u => F u t) w‖ ≤ M t/(r/4) := by
    filter_upwards [hb] with t hb w hw
    have hd : DiffContOnCl ℂ (fun u => F u t) (ball w (r/4)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (show r/4 ≠ 0 by positivity)]
      exact fun q hq => (ha t q (hsub hw hq)).differentiableWithinAt
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1
      (show 0 < r/4 by positivity) hd (fun q hq => hb q (hsub hw (sphere_subset_closedBall hq)))
    simpa using h
  have hd : DifferentiableOn ℂ (fun w => ∫ t, F w t) (ball z (r/2)) := by
    intro w hw
    have hw' : w ∈ ball z r := ball_subset_ball (by linarith) hw
    have hI := hM.mono' (hF w hw') (hb.mono fun t ht => ht w hw')
    have hme : ∀ᶠ u in 𝓝 w, AEStronglyMeasurable (F u) volume := by
      filter_upwards [isOpen_ball.mem_nhds hw'] with u hu
      exact hF u hu
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (isOpen_ball.mem_nhds hw) hme hI (hF' w hw') hder (hM.div_const (r/4))
      (Eventually.of_forall fun t u hu =>
        (ha t u (ball_subset_ball (by linarith) hu)).hasDerivAt)).2.differentiableAt.differentiableWithinAt
  exact hd.analyticAt (ball_mem_nhds z (by positivity))

end RiemannResearch.Analysis.DominatedHolomorphicTest

namespace RiemannResearch.Analysis.DominatedHolomorphicTest

/--
info: 'RiemannResearch.Analysis.DominatedHolomorphicTest.analyticAt_parameter_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms analyticAt_parameter_integral

end RiemannResearch.Analysis.DominatedHolomorphicTest
