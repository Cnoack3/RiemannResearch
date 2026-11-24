import RiemannResearch.RH.MixedConductorGramBoundary
import RiemannResearch.RH.MixedConductorPolarizedParseval
import RiemannResearch.RH.ScreenedParityOneSided
import RiemannResearch.RH.ParetoMobiusHeadInterpolation
import RiemannResearch.RH.CanonicalResidualGramMinimum

/-!
# Strict finite packet bounds and zero-free disks

Write `I_n` for the centered inverse Gram quadratic form of the first `n`
packets. A zero of zeta to the right of the critical line must lie strictly
outside the disk of center `1 + I_n` and squared radius `I_n * (I_n + 1)`.
Every finite stage has slack, because the minimum-norm legal mean-one vector
cannot belong to a finite packet span. The disk uses the complete Pareto norm.
-/

noncomputable section
open Filter
open scoped Topology BigOperators Matrix

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary

open CoefficientStabilization RamanujanCanonicalOptimizer MixedConductorBasis

/-- A finite legal span cannot contain the canonical mean-one section evaluated at one. -/
theorem normalizedScreenedTwo_not_mem_finiteSpace (n : ℕ) :
    normalizedScreenedTwo ∉ finiteSpace n := by
  intro hfin
  have hu := normalizedScreenedTwo_eq_one_of_oneSidedBound (Or.inr
    ⟨_, fun k _ => (le_abs_self _).trans (finiteSpace_sequence_abs_le n _ hfin k)⟩)
  exact hilbertOne_not_mem_finiteSpace n (hu ▸ hfin)


/-- Bounded legal support rules out exact containment of the mixed parity projection. -/
theorem two_mixed_projection_not_mem_subspace
    (S : Submodule ℝ mixedClosure) (n : ℕ)
    (hfinite : ∀ v ∈ S, (v : ThresholdHilbert) ∈ CoefficientStabilization.finiteSpace n)
    (htwo : ramanujanPacketHilbert 2 ∈ CoefficientStabilization.finiteSpace n) :
    mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2) ∉ S := by
  intro hx
  have hxfin := hfinite _ hx
  have he := fullScreening_packet_eq_mangoldt_smul 2 (by norm_num)
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at he
  norm_num only [Nat.cast_ofNat] at he
  change ramanujanPacketHilbert 2 - mixedClosure.starProjection (ramanujanPacketHilbert 2) =
    Real.log 2 • normalizedScreenedTwo at he
  have hs : Real.log 2 • normalizedScreenedTwo ∈ CoefficientStabilization.finiteSpace n :=
    he ▸ (CoefficientStabilization.finiteSpace n).sub_mem htwo hxfin
  have hu := (CoefficientStabilization.finiteSpace n).smul_mem (Real.log 2)⁻¹ hs
  have ha := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [smul_smul, inv_mul_cancel₀ ha, one_smul] at hu
  exact PacketGramBoundary.normalizedScreenedTwo_not_mem_finiteSpace n hu

/-- A balanced subspace supported in a finite legal span stays strictly below
the elementary two-prime target, including when the ambient boundary vanishes. -/
theorem finite_subspace_two_three_cross_lt_target
    (S : Submodule ℝ mixedClosure) [S.HasOrthogonalProjection]
    (hB : balancedTwoThree ∈ S) (n : ℕ)
    (hfinite : ∀ v ∈ S, (v : ThresholdHilbert) ∈ CoefficientStabilization.finiteSpace n)
    (htwo : ramanujanPacketHilbert 2 ∈ CoefficientStabilization.finiteSpace n) :
    inner ℝ
      (S.starProjection (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)))
      (S.starProjection (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 3))) <
      Real.log 2 + Real.log 3 / 2 - Real.pi / (3 * Real.sqrt 3) -
        Real.log 2 * Real.log 3 := by
  let x := mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2)
  have hne : x - S.starProjection x ≠ 0 := by
    intro hz
    have hx : x ∈ S := by
      rw [sub_eq_zero] at hz
      exact hz ▸ S.starProjection_apply_mem x
    exact two_mixed_projection_not_mem_subspace S n hfinite htwo hx
  have hr : 0 < ‖x - S.starProjection x‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hne)
  have hb := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  have hpos := mul_pos hb hr
  have hnonneg : 0 ≤ (Real.log 2)^2 * Real.log 3 * ‖CenteredMeanSnake.boundary‖^2 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hb.le) (sq_nonneg _)
  have h := subspace_two_three_target_deficit_exact S hB
  dsimp only at h
  change 0 < Real.log 3 * ‖mixedClosure.orthogonalProjectionOnto
    (ramanujanPacketHilbert 2) - S.starProjection
      (mixedClosure.orthogonalProjectionOnto (ramanujanPacketHilbert 2))‖^2 at hpos
  have ha := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  nlinarith only [h, hpos, hnonneg, ha]

/-- The two constructions of the limiting minimum-norm mean-one packet agree. -/
theorem packetUnitMeanLimit_eq_screened :
    packetUnitMeanLimit = normalizedScreenedTwo := by
  rw [packetUnitMeanLimit, limitProjection_eq_scaled_screenedTwo, smul_smul,
    inv_mul_cancel₀ packetLimitMass_pos.ne', one_smul]

/-- Every finite projection mass is strictly below its infinite endpoint. -/
theorem packetMass_lt_limitMass (n : ℕ) : packetMass n < 1 - limitEnergy := by
  cases n with
  | zero => simpa [packetMass] using packetLimitMass_pos
  | succ k =>
    have hsub : finiteSpace (k + 1) ≤ closedSpace :=
      (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_le residueAtom id _).trans
        (Submodule.le_topologicalClosure _)
    have he := packetUnitMeanLimit_completion (packetUnitMean k)
      (hsub (packetUnitMean_legal k)) (packetUnitMean_signal k)
    have hne : packetUnitMean k ≠ packetUnitMeanLimit := by
      intro h
      rw [packetUnitMeanLimit_eq_screened] at h
      exact normalizedScreenedTwo_not_mem_finiteSpace (k + 1) (h ▸ packetUnitMean_legal k)
    rw [packetUnitMean_energy] at he
    have hs := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
    exact (inv_lt_inv₀ packetLimitMass_pos (packetMass_pos (k+1) (by omega))).mp
      (by linarith only [he, hs])

/-- The finite information equals the ratio of captured mass to residual mass. -/
theorem centeredInverseGramMass_eq_div (n : ℕ) :
    centeredInverseGramMass n = packetMass n / (1 - packetMass n) := by
  rw [centeredInverseGramMass_eq]
  field_simp [(sub_pos.mpr (packetMass_bounds n).2).ne']
  <;> ring

theorem centeredInverseGramMass_nonneg (n : ℕ) : 0 ≤ centeredInverseGramMass n := by
  rw [centeredInverseGramMass_eq_div]
  exact div_nonneg (packetMass_bounds n).1 (sub_pos.mpr (packetMass_bounds n).2).le

/-- Even in the nonzero boundary branch, no finite stage exhausts the reciprocal budget. -/
theorem centeredInverseGramMass_mul_boundary_lt_one (n : ℕ) :
    centeredInverseGramMass n * ‖CenteredMeanSnake.boundary‖ ^ 2 < 1 := by
  rw [centeredInverseGramMass_eq_div, CenteredMeanSnake.boundary_norm_sq_eq_energy,
    div_mul_div_comm]
  apply (div_lt_one (mul_pos (sub_pos.mpr (packetMass_bounds n).2) packetLimitMass_pos)).mpr
  nlinarith only [packetMass_lt_limitMass n]

/-- One finite arithmetic matrix bounds the real part of every right-half-plane zero. -/
theorem single_zero_strict_gram_bound (n : ℕ) (z : ℂ) (hz : riemannZeta z = 0)
    (hre : (1 / 2 : ℝ) < z.re) (hne : z ≠ 1) :
    (2 * z.re - 1) * centeredInverseGramMass n < ‖1 - z‖ ^ 2 := by
  have h := legalMeanSection_single_zero_excess z hz hre hne screenedMeanSection
    legalPacketMean_comp_screenedMeanSection
  rw [norm_screenedMeanSection, ← CenteredMeanSnake.boundary_norm_sq] at h
  have hp : 0 < ‖1 - z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))
  calc
    _ ≤ (‖1 - z‖ ^ 2 * ‖CenteredMeanSnake.boundary‖ ^ 2) * centeredInverseGramMass n :=
      mul_le_mul_of_nonneg_right h (centeredInverseGramMass_nonneg n)
    _ = ‖1 - z‖ ^ 2 * (centeredInverseGramMass n * ‖CenteredMeanSnake.boundary‖ ^ 2) := by ring
    _ < ‖1 - z‖ ^ 2 := by
      simpa only [mul_one] using
        mul_lt_mul_of_pos_left (centeredInverseGramMass_mul_boundary_lt_one n) hp

private theorem one_sub_norm_sq_re_im (z : ℂ) :
    ‖1 - z‖ ^ 2 = (1 - z.re)^2 + z.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp <;> ring

/-- The closed disk with the displayed center and squared radius contains no such zero. -/
theorem single_zero_outside_gram_disk (n : ℕ) (z : ℂ) (hz : riemannZeta z = 0)
    (hre : (1 / 2 : ℝ) < z.re) (hne : z ≠ 1) :
    centeredInverseGramMass n * (centeredInverseGramMass n + 1) <
      (z.re - (1 + centeredInverseGramMass n))^2 + z.im^2 := by
  have h := single_zero_strict_gram_bound n z hz hre hne
  rw [one_sub_norm_sq_re_im] at h
  nlinarith only [h]

/-- A single finite exact comparison certifies a whole rectangle strictly right of the line. -/
theorem zeta_ne_zero_on_gram_rectangle (n : ℕ) (η T : ℝ) (hη : 0 < η)
    (hstage : T^2 + 1/4 ≤ 2 * η * centeredInverseGramMass n)
    (z : ℂ) (hleft : 1/2 + η ≤ z.re) (hright : z.re < 1) (ht : |z.im| ≤ T) :
    riemannZeta z ≠ 0 := by
  intro hz
  have hne : z ≠ 1 := by rintro rfl; norm_num at hright
  have hs := single_zero_strict_gram_bound n z hz (by linarith) hne
  rw [one_sub_norm_sq_re_im] at hs
  have hreal : (1 - z.re)^2 ≤ (1/2 : ℝ)^2 :=
    (sq_le_sq₀ (by linarith) (by norm_num)).mpr (by linarith)
  have him := (sq_le_sq₀ (abs_nonneg z.im) ((abs_nonneg z.im).trans ht)).mpr ht
  rw [sq_abs] at him
  have hmul := mul_le_mul_of_nonneg_right (show 2 * η ≤ 2 * z.re - 1 by linarith)
    (centeredInverseGramMass_nonneg n)
  linarith only [hs, hreal, him, hmul, hstage]

end RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary
