import RiemannResearch.RH.ParetoShiftedZetaSimpleWindow

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint)

/-- A simple critical zero gives a full-line lower bound in the damping
scale. Taking windows of all fixed rescaled radii recovers the entire
Cauchy mass π, with the physical weight at that ordinate. -/
theorem global_shifted_budget_lower_at_simple_zero (hRH : RiemannHypothesis)
    (a : ℝ) (hm : Zeta23.zeroMult (criticalPoint a) = 1) {b : ℝ}
    (hb : b < Real.pi / (1/4+a^2)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), b*ε <
      ∫ t, boundarySquare (fun v => 1-shiftedZetaQuotient ε v) t := by
  have hl : Tendsto (fun L : ℝ => 2*Real.arctan L/(1/4+a^2)) atTop
      (𝓝 (Real.pi/(1/4+a^2))) := by
    have h := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_mul 2).div_const (1/4+a^2)
    simpa only [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using h
  obtain ⟨L,hL,hbL⟩ := ((eventually_ge_atTop (0:ℝ)).and (hl.eventually (lt_mem_nhds hb))).exists
  have hlocal := (simple_zero_scaled_window a L hL hm).eventually (lt_mem_nhds hbL)
  have hi := (shiftedZetaQuotient_budget_of_riemannHypothesis hRH).1
  filter_upwards [hlocal,hi,(self_mem_nhdsWithin : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε)] with ε hloc hi he
  change 0 < ε at he
  have hab : a-ε*L ≤ a+ε*L := by linarith [mul_nonneg he.le hL]
  rw [intervalIntegral.integral_of_le hab] at hloc
  apply ((lt_div_iff₀ he).mp hloc).trans_le
  exact setIntegral_le_integral hi (Eventually.of_forall fun t => by dsimp [boundarySquare]; positivity)

theorem exists_positive_global_shifted_budget_lower (hRH : RiemannHypothesis) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ), c*ε <
      ∫ t, boundarySquare (fun v => 1-shiftedZetaQuotient ε v) t := by
  obtain ⟨s, _, hre, _, hm⟩ := RiemannResearch.RH.exists_simple_critical_zero_above 0
  have hs : criticalPoint s.im = s := by
    unfold criticalPoint
    rw [←Complex.re_add_im s]
    simp [hre]
  let c := Real.pi/(1/4+s.im^2)
  have hc : 0 < c := by dsimp [c]; positivity
  exact ⟨c/2, by positivity, global_shifted_budget_lower_at_simple_zero hRH s.im (by rwa [hs]) (by change c/2 < c; linarith)⟩

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.global_shifted_budget_lower_at_simple_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms global_shifted_budget_lower_at_simple_zero

end RiemannResearch.RH.Pareto.ResidueMellin
