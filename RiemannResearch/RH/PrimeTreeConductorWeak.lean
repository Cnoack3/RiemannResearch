/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeTreeScalingEnergy
import RiemannResearch.RH.RamanujanWeakConvergence
import RiemannResearch.RH.QConductorDecay

/-! # The unrescaled high-conductor vectors
The last assertion of Section 6 in *Prime trees, fractional parts, and zeta
zeros* concerns arbitrary Hilbert test vectors. The complete norm square has
a strictly positive limit, even though every fixed test pairing vanishes. -/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.PrimeTreeScalingEnergy
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open RiemannResearch.Analysis.HilbertWeakNorm

theorem normalizedConductor_innerWeak :
    InnerWeakTendsto normalizedConductor atTop (0 : QHilbert) := by
  apply RamanujanWeakConvergence.q_innerWeak_of_bounded_pointwise _ _ _ (2 / zetaTwo)
  · exact (eventually_ge_atTop 2).mono fun D hD => normalizedConductor_norm_sq_le D hD
  · intro k hk
    have hi : Tendsto (fun D : ℕ => (Real.sqrt (D : ℝ))⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_def] using tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hz : qSequence (0 : QHilbert) k = 0 := by
      change qSequenceLinear 0 k = 0
      rw [map_zero]
      rfl
    rw [hz]
    have ht := hi.const_mul (k : ℝ)
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop k] with D hD
    have hDr : 0 < (D : ℝ) := by exact_mod_cast (hk.trans hD)
    have hsr := Real.sqrt_pos.mpr hDr
    change _ = qSequenceLinear ((Real.sqrt (D : ℝ)) • qResidue D) k
    rw [map_smul]
    change _ = Real.sqrt (D : ℝ) * qSequence (qResidue D) k
    rw [qSequence_qResidue, residueFraction, Nat.mod_eq_of_lt hD]
    field_simp [hDr.ne', hsr.ne'] <;> ring_nf <;> simp [Real.sq_sqrt hDr.le] <;> ring

theorem normalizedConductor_not_tendsto_zero :
    ¬ Tendsto normalizedConductor atTop (𝓝 (0 : QHilbert)) := by
  intro h
  have he : Tendsto (fun D => ‖normalizedConductor D‖ ^ 2) atTop
      (𝓝 ((Real.log (2 * Real.pi) - Real.eulerMascheroniConstant) / zetaTwo)) := by
    simpa only [normalizedConductor_norm_sq] using tendsto_conductor_energy
  have hz : Tendsto (fun D => ‖normalizedConductor D‖ ^ 2) atTop (𝓝 0) := by
    simpa using h.norm.pow 2
  have hp := StepCorrectionNorm.residueEnergy_pos
  rw [StepCorrectionNorm.residueEnergy_eq_log_two_pi_sub_gamma] at hp
  exact (div_pos hp zetaTwo_pos).ne' (tendsto_nhds_unique he hz)

end RiemannResearch.RH.PrimeTreeScalingEnergy
