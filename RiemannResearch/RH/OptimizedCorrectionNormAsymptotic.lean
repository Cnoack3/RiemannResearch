import RiemannResearch.RH.OptimizedResidueAsymptotic
import RiemannResearch.RH.OptimizedResidueHilbert

/-!
# Hilbert norm limits of the concrete optimized correction directions

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Sections 3--6. This identifies the complete weighted Gram limits with the
actual bundled Hilbert-space norms and inner products.
-/

namespace RiemannResearch.RH.Pareto
open Filter
noncomputable section

theorem optimizedCorrectionHilbert_norm_scaled_tendsto :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2 *
      ‖optimizedCorrectionHilbert (n+1) (Nat.succ_pos n)‖^2 / Real.log ((n:ℝ)+1))
      atTop (nhds (1/2:ℝ)) := by
  have ht : Tendsto (fun n : ℕ => n+1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have h := optimizedCorrection_energy_scaled_tendsto.comp ht
  apply h.congr'
  filter_upwards [] with n
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
  rw [← real_inner_self_eq_norm_sq, hilbert_inner_weighted,
    optimizedCorrectionHilbert_sequence]

theorem complementaryCorrectionHilbert_norm_scaled_tendsto :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2 *
      ‖complementaryCorrectionHilbert (n+1) (Nat.succ_pos n)‖^2 / Real.log ((n:ℝ)+1))
      atTop (nhds (1/2:ℝ)) := by
  have ht : Tendsto (fun n : ℕ => n+1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have h := complementaryCorrection_energy_scaled_tendsto.comp ht
  apply h.congr'
  filter_upwards [] with n
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
  rw [← real_inner_self_eq_norm_sq, hilbert_inner_weighted,
    complementaryCorrectionHilbert_sequence]

theorem optimizedComplementaryCorrectionHilbert_inner_scaled_tendsto :
    Tendsto (fun n : ℕ => ((n:ℝ)+1)^2 *
      inner ℝ (optimizedCorrectionHilbert (n+1) (Nat.succ_pos n))
        (complementaryCorrectionHilbert (n+1) (Nat.succ_pos n)) / Real.log ((n:ℝ)+1))
      atTop (nhds (0:ℝ)) := by
  have ht : Tendsto (fun n : ℕ => n+1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have h := optimizedComplementaryCorrection_gram_scaled_tendsto.comp ht
  apply h.congr'
  filter_upwards [] with n
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
  rw [hilbert_inner_weighted, optimizedCorrectionHilbert_sequence,
    complementaryCorrectionHilbert_sequence]

end
end RiemannResearch.RH.Pareto
