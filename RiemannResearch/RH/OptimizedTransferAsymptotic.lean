import RiemannResearch.RH.OptimizedCorrectionNormAsymptotic
import RiemannResearch.RH.ParetoSchurTransfer

/-!
# The sharp one-step transfer energy grows logarithmically

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 7. The sharp constant for the actual optimized transfer has leading
coefficient 1/2. This does not control products of the transfer maps along
the particular arithmetic trajectory.
-/

namespace RiemannResearch.RH.Pareto
open Filter
noncomputable section

theorem optimizedPacketTransferEnergy_div_log_tendsto :
    Tendsto (fun n : ℕ => optimizedPacketTransferEnergy n / Real.log ((n:ℝ)+1))
      atTop (nhds (1/2:ℝ)) := by
  have h := optimizedCorrectionHilbert_norm_scaled_tendsto.sub
    ((optimizedComplementaryCorrectionHilbert_inner_scaled_tendsto.pow 2).div
      complementaryCorrectionHilbert_norm_scaled_tendsto (by norm_num))
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have hn0 : (n:ℝ)+1 ≠ 0 := by positivity
  have hlog0 : Real.log ((n:ℝ)+1) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    linarith
  have hd0 : ‖complementaryCorrectionHilbert (n+1) (Nat.succ_pos n)‖^2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (complementaryCorrectionHilbert_ne_zero
      (n+1) (Nat.succ_pos n)))
  dsimp [optimizedPacketTransferEnergy]
  field_simp
  <;> ring

end
end RiemannResearch.RH.Pareto
