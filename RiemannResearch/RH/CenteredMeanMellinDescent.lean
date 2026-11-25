import RiemannResearch.RH.CenteredMeanAmbientGeometry
import RiemannResearch.RH.LocalizedMellinObstruction
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-!
# Mellin evaluation on the centered mean boundary

An actual right-half-plane zeta zero annihilates the legal quotient's
denominator. Transporting the evaluation to the centered cokernel gives
a scalar multiple of the identity on its snake boundary. Localized
Cauchy--Schwarz gives a physical head cost for every representative.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization

/-- At an actual zero, continuous Mellin evaluation factors through the
ambient quotient by the closed legal subspace. -/
def legalQuotientMellin (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) : (ThresholdHilbert ⧸ closedSpace) →L[ℝ] ℂ :=
  closedSpace.liftQL (paretoMellinContinuous s hs) fun _ hv =>
    paretoMellin_zero_on_legalClosure_of_zeta {d : ℕ | 0 < d}
      (fun _ hd => hd) s hs hs1 hz (closedSpace_le_legalClosure hv)

/-- The descended evaluation in centered boundary coordinates. -/
def boundaryMellin (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) : BoundaryTarget →L[ℝ] ℂ :=
  (legalQuotientMellin s hs hs1 hz).comp
    boundaryTargetContinuousEquivLegalQuotient.toContinuousLinearMap

theorem boundaryMellin_mk (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (z : meanZero) :
    boundaryMellin s hs hs1 hz (mixedInMeanZero.mkQ z) = paretoMellin z.val s := rfl

/-- The signed complex evaluation of the boundary at a real scalar. -/
theorem boundaryMellin_boundary (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (a : ℝ) :
    boundaryMellin s hs hs1 hz (boundary a) = -((a : ℂ) / s) := by
  change legalQuotientMellin s hs hs1 hz (boundaryTargetEquivLegalQuotient (boundary a)) = -((a : ℂ) / s)
  rw [boundaryTargetEquivLegalQuotient_boundary, map_neg, map_smul]
  change -(a • paretoMellin hilbertOne s) = _
  rw [paretoMellin_one s hs, Complex.real_smul]
  ring

/-- The real part of the normalized zero evaluation retracts the snake
boundary onto its scalar domain. -/
def boundaryMellinRetraction (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) : BoundaryTarget →L[ℝ] ℝ :=
  Complex.reCLM.comp ((-s) • boundaryMellin s hs hs1 hz)

theorem boundaryMellinRetraction_comp (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) :
    (boundaryMellinRetraction s hs hs1 hz).comp boundary = ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro a
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  change (-s * boundaryMellin s hs hs1 hz (boundary a)).re = a
  rw [boundaryMellin_boundary, show -s * -((a : ℂ) / s) = a by field_simp [hs0]]
  rfl

/-- A right zero supplies an explicit splitting of the boundary arrow
in the category of real topological modules. -/
def boundarySplitMonoOfZetaZero (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) : CategoryTheory.SplitMono (TopModuleCat.ofHom boundary) where
  retraction := TopModuleCat.ofHom (boundaryMellinRetraction s hs hs1 hz)
  id := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro a
    exact congrArg (fun F : ℝ →L[ℝ] ℝ => F a) (boundaryMellinRetraction_comp s hs hs1 hz)

/-- Every representative of the boundary at a scalar, vanishing below K,
pays the exact localized Mellin power at an actual right zero. -/
theorem boundary_representative_mellin_power_lower (a : ℝ) (z : meanZero)
    (hzq : mixedInMeanZero.mkQ z = boundary a) (K : ℕ) (hK : 1 ≤ K)
    (hhead : ∀ k, 0 < k → k < K → hilbertSequence z.val k = 0)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2*s.re-1) * ‖(a : ℂ)/s‖^2 * (K : ℝ)^(2*s.re-1) ≤ ‖z‖^2 := by
  have h := mellin_zero_head_lower z.val K hK hhead s hs
  rwa [← boundaryMellin_mk s hs hs1 hz, hzq, boundaryMellin_boundary, norm_neg] at h

/-- Representatives beating every positive power budget for the unit
boundary exclude all zeros in the open right half-strip. -/
theorem riemannHypothesis_of_boundary_head_subpower
    (h : ∀ p c : ℝ, 0 < p → 0 < c → ∃ K : ℕ, 1 ≤ K ∧ ∃ z : meanZero,
      mixedInMeanZero.mkQ z = boundary 1 ∧
      (∀ k, 0 < k → k < K → hilbertSequence z.val k = 0) ∧ ‖z‖^2 < c * (K : ℝ)^p) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hlt hz
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hlt
  have hp : 0 < 2*s.re-1 := by linarith
  have hc := mul_pos hp (sq_pos_of_pos (norm_pos_iff.mpr (one_div_ne_zero hs0)))
  obtain ⟨K, hK, z, hzq, hhead, hb⟩ := h _ _ hp hc
  exact (not_lt_of_ge (by simpa using
    boundary_representative_mellin_power_lower 1 z hzq K hK hhead s hs hs1 hz)) hb

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
