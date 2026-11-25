import RiemannResearch.Analysis.MontgomeryMacroscopicTriangle
import RiemannResearch.Analysis.MontgomeryMacroscopicGapSecondTerm

/-! # The full macroscopic cubic triangle law for actual zero occurrences -/

noncomputable section
open Filter Set Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroWindowVariance ActualZeroCollisionCertificate

/-- The entire actual physical triangle, including all equal-height
multiplicities and off-critical coincidences, has the cubic macroscopic
profile uniformly over the observation-width fractions. -/
theorem eventually_macroscopicPhysicalTriangle_uniform {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ c ∈ Icc (0:ℝ) 1,
      |actualPhysicalTriangleEnergy T (c*T)/(unfoldedCutoff T)^2-(c^2-c^3/3)| ≤ ε := by
  apply eventually_macroscopicPhysicalTriangle_uniform_of_collision _ hε
  have h := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).mul
    log_mul_collision_div_mainTerm_sq_tendsto_zero
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  change (Real.log T)⁻¹*(Real.log T*((actualCollision T:ℝ)/(unfoldedCutoff T)^2)) = _
  rw [← mul_assoc,inv_mul_cancel₀ (Real.log_pos hT).ne',one_mul]

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_macroscopicPhysicalTriangle_uniform'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_macroscopicPhysicalTriangle_uniform

end RiemannResearch.Analysis.MontgomeryPositiveGap
