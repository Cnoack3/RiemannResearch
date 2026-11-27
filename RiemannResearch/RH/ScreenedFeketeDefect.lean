import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import RiemannResearch.RH.CenteredMeanQuotients
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

The Hilbert vector `normalizedScreenedTwo` is the projection of the conductor-two packet off
the mixed subspace, divided by `Real.log 2`. It has Pareto mean one. The Fekete pairing on
legal test vectors evaluates the legal projection of an ambient mixed-orthogonal vector.
Restricting to legal inputs gives the screened line and its orthogonal complement inside `V`.
-/

noncomputable section

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.ScreenedFeketeDefect

open CoefficientStabilization
open RiemannResearch.NumberTheory (powerRate pow_div_exponent_of_log powerRate_eq_of_log)

/-- The Fekete pairing determines the projection of an ambient mixed-orthogonal vector into
the legal Hilbert space, at every base greater than one. -/
theorem legal_projection_eq_fekete_rate {h : ThresholdHilbert} (hh : h ∈ mixedClosureᗮ)
    {a : ℕ} (ha : 1 < a) :
    closedSpace.starProjection h =
      (powerRate (residuePairing h) a / Real.log (a : ℝ)) • limitProjection := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact closedSpace.smul_mem _ (closedSpace.starProjection_apply_mem hilbertOne)
  · intro v hv
    have hmean : inner ℝ v limitProjection = inner ℝ v hilbertOne :=
      CenteredMeanSnake.inner_projectedOne (⟨v, hv⟩ : closedSpace)
    have hpair : inner ℝ v h =
        (powerRate (residuePairing h) a / Real.log (a : ℝ)) * inner ℝ v hilbertOne :=
      (real_inner_comm _ _).trans (Bilinear.pairing_eq_fekete_rate_at_base hh hv ha)
    rw [inner_sub_right, real_inner_smul_right, hmean, hpair, sub_self]

/-- In the mean-one normalization, the coefficient of the orthogonal projection onto the
screened line includes the reciprocal squared norm of its generator. -/
theorem legal_projection_eq_screened_coefficient {h : ThresholdHilbert} (hh : h ∈ mixedClosureᗮ) :
    closedSpace.starProjection h =
      (inner ℝ normalizedScreenedTwo h / ‖normalizedScreenedTwo‖ ^ 2) • normalizedScreenedTwo := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact closedSpace.smul_mem _
      (screenedPrimeClosure_le_closedSpace normalizedScreenedTwo_mem_screenedPrimeClosure)
  · intro v hv
    have hpair : inner ℝ v h = inner ℝ normalizedScreenedTwo h * inner ℝ v hilbertOne :=
      (real_inner_comm _ _).trans (Bilinear.pairing_factorization_of_rigidity hh hv)
    rw [inner_sub_right, real_inner_smul_right, hpair, ← Bilinear.inner_screenedTwo_div_norm_sq hv]
    ring

/-- On the intersection with the legal space the projection fixes the vector. Its coordinate
on the screened line is therefore its Pareto mean. -/
theorem legal_mixedOrthogonal_eq_mean_smul {v : ThresholdHilbert}
    (hv : v ∈ closedSpace ⊓ mixedClosureᗮ) :
    v = inner ℝ v hilbertOne • normalizedScreenedTwo := by
  have hp := legal_projection_eq_screened_coefficient hv.2
  rwa [closedSpace.starProjection_eq_self_iff.mpr hv.1, real_inner_comm v normalizedScreenedTwo,
    Bilinear.inner_screenedTwo_div_norm_sq hv.1] at hp

/-- The subspace identity obtained by restricting the Fekete pairing to legal vectors. -/
theorem legal_inf_mixedOrthogonal_eq_screenedLine :
    closedSpace ⊓ mixedClosureᗮ = Submodule.span ℝ {normalizedScreenedTwo} := by
  apply le_antisymm
  · intro v hv
    exact Submodule.mem_span_singleton.mpr
      ⟨inner ℝ v hilbertOne, (legal_mixedOrthogonal_eq_mean_smul hv).symm⟩
  · apply Submodule.span_le.mpr
    apply Set.singleton_subset_iff.mpr
    rw [← screenedPrimeClosure_eq_inf_orthogonal]
    exact normalizedScreenedTwo_mem_screenedPrimeClosure

/-- The screened packet is the unique mean-one legal vector orthogonal to the mixed packets. -/
theorem mean_one_legal_orthogonal_set :
    {v : ThresholdHilbert | v ∈ closedSpace ∧ v ∈ mixedClosureᗮ ∧
        inner ℝ v hilbertOne = 1} = {normalizedScreenedTwo} := by
  ext v
  change (_ ∧ _ ∧ _) ↔ v = normalizedScreenedTwo
  constructor
  · rintro ⟨hv, ho, hm⟩
    simpa only [hm, one_smul] using legal_mixedOrthogonal_eq_mean_smul ⟨hv, ho⟩
  · rintro rfl
    have hg := normalizedScreenedTwo_mem_screenedPrimeClosure
    rw [screenedPrimeClosure_eq_inf_orthogonal] at hg
    exact ⟨hg.1, hg.2, normalizedScreenedTwo_mean⟩

/-- The two submodules are mutual orthogonal complements in the subtype `closedSpace`,
and form a direct sum there. -/
theorem legal_mixed_screened_complements :
    (mixedClosure.comap closedSpace.subtype)ᗮ = Submodule.span ℝ {screenedMeanSection 1} ∧
    IsCompl (mixedClosure.comap closedSpace.subtype)
      (Submodule.span ℝ {screenedMeanSection 1}) := by
  rw [← CenteredMeanSnake.screenedMeanSection_one_orthogonal_eq_mixed]
  exact ⟨by simp only [Submodule.orthogonal_orthogonal], (Submodule.isCompl_orthogonal _).symm⟩

/-- An ambient vector perpendicular to both the mixed space and the screened line
is exactly a vector perpendicular to the whole legal space. -/
theorem mixedOrthogonal_inf_screenedOrthogonal :
    mixedClosureᗮ ⊓ (Submodule.span ℝ {normalizedScreenedTwo})ᗮ = closedSpaceᗮ := by
  rw [Submodule.inf_orthogonal, CenteredMeanSnake.legal_mixed_screened_orthogonal_sum.1]

/-- In the ambient Hilbert space the perpendicular to the screened line consists of the
mixed component and the component orthogonal to the legal space. -/
theorem screenedOrthogonal_eq_mixed_sup_legalOrthogonal :
    (Submodule.span ℝ {normalizedScreenedTwo})ᗮ = mixedClosure ⊔ closedSpaceᗮ := by
  have hle := Submodule.orthogonal_le CenteredMeanSnake.legal_mixed_screened_orthogonal_sum.2
  rw [Submodule.orthogonal_orthogonal] at hle
  calc
    _ = mixedClosure ⊔ ((Submodule.span ℝ {normalizedScreenedTwo})ᗮ ⊓ mixedClosureᗮ) :=
      (RiemannResearch.Analysis.NestedOrthogonalDecomposition.prime_sup_carry hle).symm
    _ = _ := by rw [inf_comm _ mixedClosureᗮ, mixedOrthogonal_inf_screenedOrthogonal]

/-- Pythagoras on the ambient mixed complement retains the entire legal-orthogonal remainder. -/
theorem ambient_mixedOrthogonal_norm_split {h : ThresholdHilbert} (hh : h ∈ mixedClosureᗮ) :
    ‖h‖ ^ 2 = (inner ℝ normalizedScreenedTwo h) ^ 2 / ‖normalizedScreenedTwo‖ ^ 2 +
      ‖closedSpaceᗮ.starProjection h‖ ^ 2 := by
  have hn : ‖normalizedScreenedTwo‖ ≠ 0 :=
    (zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo).ne'
  calc
    ‖h‖ ^ 2 = ‖closedSpace.starProjection h‖ ^ 2 + ‖closedSpaceᗮ.starProjection h‖ ^ 2 :=
      Submodule.norm_sq_eq_add_norm_sq_starProjection h closedSpace
    _ = _ := by
      rw [legal_projection_eq_screened_coefficient hh, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      field_simp [hn]

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
