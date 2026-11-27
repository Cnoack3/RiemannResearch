import RiemannResearch.RH.MixedConductorBilinear
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MixedOrthogonalMean
import RiemannResearch.RH.ScreenedSectionDescent

/-!
# The Fekete slope of the centered screened packet

Source: the user's argument testing the residue slope on the mean-zero vector
`g - 1`, where `g = normalizedScreenedTwo`. Logarithmic rigidity fixes the
same normalized slope at each base and exponent. Its value on this test
vector is the squared norm of the defect. Its vanishing is equivalent to RH.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.ScreenedFeketeDefect

open CoefficientStabilization
open RiemannResearch.NumberTheory (powerRate pow_div_exponent_of_log powerRate_eq_of_log)

/-- The screened packet is the unique mean-one legal vector orthogonal to the mixed packets. -/
theorem mean_one_legal_orthogonal_set :
    {v : ThresholdHilbert | v ∈ closedSpace ∧ v ∈ mixedClosureᗮ ∧
        inner ℝ v hilbertOne = 1} = {normalizedScreenedTwo} := by
  ext v
  change (_ ∧ _ ∧ _) ↔ v = normalizedScreenedTwo
  constructor
  · rintro ⟨hv, ho, hm⟩
    have hs := fullScreening_eq_mean_smul hv
    change v - mixedClosure.starProjection v = _ at hs
    simpa only [(Submodule.starProjection_apply_eq_zero_iff _).mpr ho, sub_zero, hm,
      one_smul] using hs
  · rintro rfl
    have hg := normalizedScreenedTwo_mem_screenedPrimeClosure
    rw [screenedPrimeClosure_eq_inf_orthogonal] at hg
    exact ⟨hg.1, hg.2, normalizedScreenedTwo_mean⟩

/-- At any base greater than one the normalized Fekete infimum on the defect
is its exact squared norm. The test vector is already known to have zero mean. -/
theorem defect_fekete_rate_eq_norm_sq {a : ℕ} (ha : 1 < a) :
    powerRate (residuePairing (normalizedScreenedTwo - hilbertOne)) a / Real.log (a : ℝ) =
      ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  let h := normalizedScreenedTwo - hilbertOne
  have ho : h ∈ mixedClosureᗮ := CenteredMeanSnake.screenedTwo_sub_one_mem_orthogonals.2
  have hm : inner ℝ hilbertOne h = 0 := CenteredMeanSnake.defect.property
  calc
    _ = inner ℝ normalizedScreenedTwo h :=
      (Bilinear.mixedPacketCoefficient_eq_fekete_rate ⟨h, ho⟩ ha).symm
    _ = inner ℝ h h := by
      change inner ℝ normalizedScreenedTwo h = inner ℝ (normalizedScreenedTwo - hilbertOne) h
      rw [inner_sub_left, hm, sub_zero]
    _ = _ := real_inner_self_eq_norm_sq h

/-- Every positive exponent already attains the normalized infimum. -/
theorem defect_residue_power_eq_norm_sq {a k : ℕ} (ha : 1 < a) (hk : 0 < k) :
    residuePairing (normalizedScreenedTwo - hilbertOne) (a ^ k) / (k * Real.log (a : ℝ)) =
      ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  obtain ⟨c, hc⟩ := residuePairing_eq_log CenteredMeanSnake.screenedTwo_sub_one_mem_orthogonals.2
  have ha' : 0 < a := Nat.zero_lt_of_lt ha
  rw [← div_div, pow_div_exponent_of_log hc ha' hk, ← powerRate_eq_of_log hc ha']
  exact defect_fekete_rate_eq_norm_sq ha

/-- The packet at each prime power pairs to the same normalized defect slope.
Unlike the raw residue at exponent k, its normalizing logarithm is log p. -/
theorem defect_prime_power_packet_eq_norm_sq {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    inner ℝ (ramanujanPacketHilbert (p ^ k)) (normalizedScreenedTwo - hilbertOne) /
        Real.log (p : ℝ) = ‖normalizedScreenedTwo - hilbertOne‖ ^ 2 := by
  rw [Bilinear.prime_pow_packet_pairing_eq_powerRate
    CenteredMeanSnake.screenedTwo_sub_one_mem_orthogonals.2 hp hk]
  exact defect_fekete_rate_eq_norm_sq hp.one_lt

/-- A single base suffices to test equality of the screened packet with the constant. -/
theorem defect_fekete_rate_zero_iff_screened {a : ℕ} (ha : 1 < a) :
    powerRate (residuePairing (normalizedScreenedTwo - hilbertOne)) a / Real.log (a : ℝ) = 0 ↔
      normalizedScreenedTwo = hilbertOne := by
  rw [defect_fekete_rate_eq_norm_sq ha, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

/-- Zero slope is the remaining arithmetic assertion, equivalently RH. -/
theorem defect_fekete_rate_zero_iff_rh {a : ℕ} (ha : 1 < a) :
    powerRate (residuePairing (normalizedScreenedTwo - hilbertOne)) a / Real.log (a : ℝ) = 0 ↔
      RiemannHypothesis := by
  rw [defect_fekete_rate_eq_norm_sq ha, ← CenteredMeanSnake.boundary_norm,
    CenteredMeanSnake.boundary_norm_sq, sub_eq_zero, ← real_inner_self_eq_norm_sq]
  exact ScreenedSectionDescent.inner_self_eq_one_iff_rh

/-- The canonical mean-one generator spans the entire ambient mixed complement exactly under RH. -/
theorem ambient_mixedOrthogonal_eq_screenedLine_iff_rh :
    mixedClosureᗮ = Submodule.span ℝ {normalizedScreenedTwo} ↔ RiemannHypothesis := by
  constructor
  · intro hspan
    have hone := one_mem_mixedClosure_orthogonal
    rw [hspan, ← screenedPrimeClosure_eq_span_two] at hone
    exact riemannHypothesis_of_normalizedScreenedTwo
      (one_mem_closedSpace_iff_normalizedScreenedTwo.mp (screenedPrimeClosure_le_closedSpace hone))
  · intro hrh
    have htwo : 1 < (2 : ℕ) := by decide
    have hseed := (defect_fekete_rate_zero_iff_screened htwo).mp
      ((defect_fekete_rate_zero_iff_rh htwo).mpr hrh)
    rw [hseed]
    exact mixedOrthogonal_eq_span_one_iff_one_mem.mpr
      (one_mem_closedSpace_iff_normalizedScreenedTwo.mpr hseed)

/-- Allowing any legal generator for the ambient complement gives the same criterion. -/
theorem ambient_mixedOrthogonal_has_legal_generator_iff_rh :
    (∃ g : ThresholdHilbert, g ∈ closedSpace ⊓ mixedClosureᗮ ∧
      mixedClosureᗮ = Submodule.span ℝ {g}) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨g, hg, hspan⟩
    have hle : Submodule.span ℝ {g} ≤ closedSpace :=
      Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hg.1)
    have hone := one_mem_mixedClosure_orthogonal
    rw [hspan] at hone
    exact riemannHypothesis_of_normalizedScreenedTwo
      (one_mem_closedSpace_iff_normalizedScreenedTwo.mp (hle hone))
  · intro hrh
    refine ⟨normalizedScreenedTwo, ?_, ambient_mixedOrthogonal_eq_screenedLine_iff_rh.mpr hrh⟩
    rw [← screenedPrimeClosure_eq_inf_orthogonal]
    exact normalizedScreenedTwo_mem_screenedPrimeClosure

end RiemannResearch.RH.Pareto.PrimePowerSchur.ScreenedFeketeDefect
