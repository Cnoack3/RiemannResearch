import RiemannResearch.RH.ParetoHiddenConditioningConstant
import RiemannResearch.RH.FermiIntegral
import RiemannResearch.RH.ParetoNoiseResearchTargets

/-!
# The fully evaluated hidden-noise conditioned limit

Source: RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf, §6.
The proof combines the actual geometric-series transform, exact exponential
substitution, proved domination and integral convergence, an explicit primitive,
and the independently evaluated Fermi integral.  No analytic research target is
assumed.  The limit holds along all natural indices, hence along the odd indices
used in the original statement.
-/

open Filter MeasureTheory
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem hiddenConditioning_derivative_energy :
    (∫ x : ℝ in Set.Ioi 0, hiddenConditioningDerivative x ^ 2) =
      (Real.pi^2 - 6) / 36 := by
  rw [hiddenConditioning_derivative_energy_eq_fermi]
  unfold hiddenConditioningProfile
  rw [integral_fermi_first]
  ring

/-- The fully evaluated conditioned asymptotic holds along all natural indices. -/
theorem hiddenNoise_conditioned_limit_all :
    Tendsto (fun n : ℕ => (n : ℝ) * (∫ t : ℝ in Set.Ioc 0 1,
      (geometricTransform (fun k => hiddenNoise n (k + 1)) t)^2)) atTop
      (nhds ((Real.pi^2 - 6) / 9)) := by
  have h := hiddenNoise_conditioned_norm_tendsto
  rw [hiddenConditioning_derivative_energy] at h
  have he : 4 * ((Real.pi^2 - 6) / 36) = (Real.pi^2 - 6) / 9 := by ring
  simpa only [he] using h

/-- The exact previously unproved research target, now with all hypotheses closed. -/
theorem hiddenNoiseConditionedLimit : ResearchTargets.HiddenNoiseConditionedLimit := by
  exact hiddenNoise_conditioned_limit_all.mono_left inf_le_left

end
end RiemannResearch.RH.Pareto
