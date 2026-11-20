import RiemannResearch.RH.ParetoParity8192Jordan

/-! # Kernel-evaluated constants for the signed conductor-8192 trial -/

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor8192
section
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem twiceMean_value : twiceMean = 112901299 := by
  have hc : fastSum (fun d => coeff d*((d:ℤ)-1)) = 1887098701 := by decide +kernel
  rw [fastSum_spec] at hc
  unfold twiceMean
  rw [hc]
  decide

theorem oscillation_value : oscillation = 5074605440756600 :=
  (fastSum_spec (fun d => abs (coeff d)*(d:ℤ)*((d:ℤ)-1))).symm.trans
    (by decide +kernel)

theorem covariance_value : covariance = 161141128064221680975 :=
  covariance_eq_jordanEnergy.trans (fastJordan_spec.symm.trans
    (by decide +kernel : fastJordan = 161141128064221680975))

end
end RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor8192
