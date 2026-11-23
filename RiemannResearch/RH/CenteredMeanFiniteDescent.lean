import Mathlib.Analysis.Complex.ExponentialBounds
import RiemannResearch.RH.ScreenedTwoMixedApproximation
import RiemannResearch.RH.MixedConductorCaptureGains
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MixedParityCaptureFifteen
import RiemannResearch.RH.CenteredMeanRHCriteria
import RiemannResearch.RH.MixedConductorGramSites
import RiemannResearch.RH.CenteredMeanLongExact
import RiemannResearch.RH.PrimeSupportAlgebraDescent

/-!
# The centered snake boundary on representatives and in finite Gram coordinates

The legal support quotients all map to the same centered cokernel. Inclusion
identifies its image in the ambient legal quotient with the negative scalar
multiple of the constant class. The test for the algebra unit below uses a
single raw packet Gram solve for each allowed error and starting cutoff.

The module snake chase uses the sign convention of Weibel, *An Introduction
to Homological Algebra*, Lemma 1.3.2, and Stacks Project, Tag 07JV.
For the discrete Hilbert-space criterion see Bagchi, Theorem 1,
https://arxiv.org/abs/math/0607733.
-/

noncomputable section
open scoped Matrix

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization MixedConductorBasis LegalMeanAlgebra
open RamanujanCanonicalOptimizer PacketGramBoundary
open scoped LegalMeanAlgebra

/-- The ambient mean descends to the vertex of the support quotient tower. -/
def ambientQuotientMean : (ThresholdHilbert ⧸ mixedClosure) →L[ℝ] ℝ :=
  mixedClosure.liftQL hilbertMeanContinuous fun x hx => (mixedInclusion ⟨x, hx⟩).property

/-- The kernel at the vertex is exactly the embedded target of the centered snake. -/
theorem exact_boundaryToMixedQuotient_ambientQuotientMean :
    Function.Exact boundaryToMixedQuotient ambientQuotientMean := by
  intro q
  obtain ⟨x, rfl⟩ := mixedClosure.mkQ_surjective q
  constructor
  · intro hx
    exact ⟨mixedInMeanZero.mkQ ⟨x, hx⟩, rfl⟩
  · rintro ⟨a, ha⟩
    obtain ⟨z, rfl⟩ := mixedInMeanZero.mkQ_surjective a
    rw [← ha]
    exact z.property

/-- The ambient constant provides a continuous section at the same vertex. -/
def ambientQuotientSection : ℝ →L[ℝ] (ThresholdHilbert ⧸ mixedClosure) :=
  mixedClosure.mkQL.comp (ContinuousLinearMap.toSpanSingleton ℝ hilbertOne)

theorem ambientQuotientMean_comp_section :
    ambientQuotientMean.comp ambientQuotientSection = ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro t
  change hilbertMeanContinuous (t • hilbertOne) = t
  simp

/-- Transport the boundary of every stage representative into the ambient quotient. -/
theorem stageBoundary_ambient_representative (s : ℕ) (v : closedSpace) :
    boundaryTargetEquivLegalQuotient
      (stageMeanBoundary s (Ideal.Quotient.mk (supportIdeal s) v)) =
        -(legalPacketMean v • closedSpace.mkQ hilbertOne) := by
  rw [stageMeanBoundary_mk, ← boundary_of_lift, boundaryTargetEquivLegalQuotient_boundary]

/-- This describes the kernel on representatives even when the ambient boundary is nonzero. -/
theorem stageBoundary_mk_eq_zero_iff (s : ℕ) (v : closedSpace) :
    stageMeanBoundary s (Ideal.Quotient.mk (supportIdeal s) v) = 0 ↔
      legalPacketMean v = 0 ∨ hilbertOne ∈ closedSpace := by
  rw [← boundaryTargetEquivLegalQuotient.injective.eq_iff, map_zero,
    stageBoundary_ambient_representative, neg_eq_zero, smul_eq_zero]
  exact or_congr Iff.rfl (Submodule.Quotient.mk_eq_zero closedSpace)

/-- For the genuinely finite conductor window, its normalized squared error is the
boundary energy plus the squared distance from its mean-one fit to the limiting lift. -/
theorem finiteWindow_deficit_eq_boundary_add_tail (B : ℕ) :
    CaptureGains.deficit B / (Real.log 2)^2 =
      ‖boundary‖^2 + ‖fixedTwoTrial B - normalizedScreenedTwo‖^2 := by
  have h := CaptureGains.deficit_add_capture B
  rw [show CaptureGains.deficit B = Real.log 2 - (Real.log 2)^2 -
      ‖(mixedSpace (Finset.Icc 2 B)).starProjection (ramanujanPacketHilbert 2)‖^2
      by linarith only [h], ← fixedTwoTrial_error_eq_capture,
      fixedTwoTrial_error_sq_eq_limit_add_tail, boundary_norm_sq_eq_energy]

/-- Five explicit mixed packets already remove more than five sixteenths of
the parity variance from the finite window through conductor fifteen. -/
theorem finiteWindow_fifteen_deficit_lt :
    CaptureGains.deficit 15 < (11 / 16 : ℝ) * (Real.log 2 - (Real.log 2)^2) := by
  have hl : (693 / 1000 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hp := mul_nonneg (sub_nonneg.mpr hl.le)
    (show 0 ≤ Real.log 2 + 693 / 1000 - 1 by linarith only [hl])
  nlinarith only [hp, CaptureGains.deficit_add_capture 15,
    fixedTwo_mixed_capture_gt_one_fifteenth 15 (by decide)]

private theorem first_site_budget_solve (n : ℕ) (ε : ℝ) :
    (2 - ε) * (finitePacketGram n).det ≤
      (siteGram n 1).det + (2 - Real.sqrt 2) * (meanPencil n 1).det ↔
    let c := (finitePacketGram n)⁻¹.mulVec (meanVector n)
    1 - ε ≤ -dotProduct (finiteMoebiusSource n) c +
      (2 - Real.sqrt 2) * (1 - dotProduct (meanVector n) c) := by
  dsimp only
  have hm : dotProduct (meanVector n) ((finitePacketGram n)⁻¹.mulVec (meanVector n)) =
      packetMass n := (packetMass_eq_inverseGram n).symm
  rw [first_site_det_as_one_solve, det_meanPencil, one_mul, hm]
  let G := (finitePacketGram n).det
  let b := dotProduct (finiteMoebiusSource n) ((finitePacketGram n)⁻¹.mulVec (meanVector n))
  let t := (2 - Real.sqrt 2) * (1 - packetMass n)
  change (2 - ε) * G ≤ G * (1 - b) + (2 - Real.sqrt 2) * (G * (1 - packetMass n)) ↔
    1 - ε ≤ -b + t
  rw [show G * (1 - b) + (2 - Real.sqrt 2) * (G * (1 - packetMass n)) =
      (1 - b + t) * G by dsimp [t]; ring,
    mul_le_mul_iff_left₀ (finitePacketGram_det_pos n)]
  constructor <;> intro h <;> linarith only [h]

/-- The unit of any support stage dies in the ambient snake target precisely
when finite Gram solves meet the first-site budget at arbitrary precision and cutoff. -/
theorem stageUnit_zero_iff_cofinal_gram_solve (s : ℕ) :
    stageMeanBoundary s 1 = 0 ↔ ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      let c := (finitePacketGram n)⁻¹.mulVec (meanVector n)
      1 - ε ≤ -dotProduct (finiteMoebiusSource n) c +
        (2 - Real.sqrt 2) * (1 - dotProduct (meanVector n) c) := by
  rw [stageUnit_zero_iff_boundary, boundary_eq_zero_iff_first_site_det_budget]
  simp only [first_site_budget_solve]

/-- A vanishing error allowance in the finite first-site solves suffices for RH. -/
theorem riemannHypothesis_of_approximate_first_site_solves
    (h : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n ≥ N,
      let c := (finitePacketGram n)⁻¹.mulVec (meanVector n)
      1 - ε ≤ -dotProduct (finiteMoebiusSource n) c +
        (2 - Real.sqrt 2) * (1 - dotProduct (meanVector n) c)) : RiemannHypothesis :=
  riemannHypothesis_of_stageUnit_zero ((stageUnit_zero_iff_cofinal_gram_solve 0).2 h)

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
