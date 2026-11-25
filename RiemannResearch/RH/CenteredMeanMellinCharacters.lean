import RiemannResearch.RH.CenteredMeanMellinDescent
import RiemannResearch.RH.CenteredMeanQuotientNorm
import RiemannResearch.RH.QComplementZeroDimension
import RiemannResearch.RH.ParetoMellinDilation
import RiemannResearch.RH.MixedConductorSpanCriterion
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Tactic.FieldSimp

/-!
# Independence of the normalized Mellin evaluations on the snake target

The integer threshold tests realize Dedekind's independent multiplicative
characters on the centered cokernel. Each normalized zero evaluation takes
the same value on the snake arrow. A categorical epimorphism would identify
the evaluations of a right zero and its conjugate.
-/

noncomputable section
open CategoryTheory
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
open CoefficientStabilization QComplementZeroDimension

private theorem rightZero_ne_one (s : RightZero) : (s : ℂ) ≠ 1 := by
  intro he
  have hh := s.property.2.1
  simp [he] at hh

private theorem rightZero_ne_zero (s : RightZero) : (s : ℂ) ≠ 0 := by
  intro he
  have hh := s.property.1
  norm_num [he] at hh

/-- Mellin evaluation normalized by its value on the constant vector. -/
def normalizedBoundaryMellin (s : RightZero) : BoundaryTarget →L[ℝ] ℂ :=
  (s : ℂ) • boundaryMellin s s.property.1 (rightZero_ne_one s) s.property.2.2

/-- All normalized evaluations give the same map on the scalar boundary. -/
theorem normalizedBoundaryMellin_boundary (s : RightZero) (a : ℝ) :
    normalizedBoundaryMellin s (boundary a) = -(a : ℂ) := by
  change (s : ℂ) * boundaryMellin s _ _ _ (boundary a) = _
  rw [boundaryMellin_boundary]
  field_simp [rightZero_ne_zero s]

private def testBoundaryDilations : (BoundaryTarget →L[ℝ] ℂ) →ₗ[ℂ] (ℕ+ → ℂ) where
  toFun L n := L (boundaryTargetEquivLegalQuotient.symm
    (closedSpace.mkQ (hilbertDilation n n.pos hilbertOne)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem testBoundaryDilations_normalized (s : RightZero) :
    testBoundaryDilations (normalizedBoundaryMellin s) = powerCharacter s := by
  funext n
  change (s : ℂ) * legalQuotientMellin s s.property.1 (rightZero_ne_one s) s.property.2.2
    (boundaryTargetEquivLegalQuotient (boundaryTargetEquivLegalQuotient.symm
      (closedSpace.mkQ (hilbertDilation n n.pos hilbertOne)))) = powerCharacter s n
  rw [LinearEquiv.apply_symm_apply]
  change (s : ℂ) * paretoMellin (hilbertDilation n n.pos hilbertOne) s = _
  rw [paretoMellin_dilation, paretoMellin_one s s.property.1]
  change (s : ℂ) * (((n : ℕ) : ℂ)^(1-(s : ℂ)) * (1/(s : ℂ))) =
    ((n : ℕ) : ℂ)^(1-(s : ℂ))
  field_simp [rightZero_ne_zero s]

/-- The complex-valued real-linear maps associated with all actual right
zeros are linearly independent over the scalar field of their values. -/
theorem normalizedBoundaryMellin_linearIndependent :
    LinearIndependent ℂ normalizedBoundaryMellin := by
  apply LinearIndependent.of_comp testBoundaryDilations
  simpa only [Function.comp_def, testBoundaryDilations_normalized] using
    powerCharacters_linearIndependent.comp (fun s : RightZero => (s : ℂ)) Subtype.val_injective

/-- Subtracting two normalized zero evaluations gives a continuous
functional on the cokernel of the scalar snake boundary itself. -/
def boundaryCokernelMellinDifference (s t : RightZero) :
    (BoundaryTarget ⧸ boundary.toLinearMap.range) →L[ℝ] ℂ :=
  boundary.toLinearMap.range.liftQL (normalizedBoundaryMellin s - normalizedBoundaryMellin t)
    fun _ ⟨a, ha⟩ => by
      rw [← ha]
      change normalizedBoundaryMellin s (boundary a) - normalizedBoundaryMellin t (boundary a) = 0
      rw [normalizedBoundaryMellin_boundary, normalizedBoundaryMellin_boundary, sub_self]

theorem boundaryCokernelMellinDifference_ne_zero {s t : RightZero} (hst : s ≠ t) :
    boundaryCokernelMellinDifference s t ≠ 0 := by
  intro h
  apply hst
  apply normalizedBoundaryMellin_linearIndependent.injective
  apply ContinuousLinearMap.ext
  intro x
  apply sub_eq_zero.mp
  change boundaryCokernelMellinDifference s t (boundary.toLinearMap.range.mkQ x) = 0
  simp only [h, zero_apply]

/-- If the centered snake boundary is epic, the open right half-strip is
zero-free. Distinct conjugates give distinct normalized maps, while real
points of this strip are already zero-free. -/
theorem riemannHypothesis_of_boundary_epi [Epi (TopModuleCat.ofHom boundary)] :
    RiemannHypothesis := by
  have heq (s t : RightZero) : s = t := by
    apply normalizedBoundaryMellin_linearIndependent.injective
    apply ContinuousLinearMap.ext
    intro b
    have hs := boundary_surjective_iff_common_eq_bot.mpr
      (boundary_epi_iff_common_eq_bot.mp inferInstance)
    obtain ⟨a, rfl⟩ := hs b
    exact (normalizedBoundaryMellin_boundary s a).trans (normalizedBoundaryMellin_boundary t a).symm
  exact riemannHypothesis_iff_subsingleton_rightZero.mpr ⟨heq⟩

/-- The reverse direction uses the classical RH-to-natural-approximation
input. It makes the centered target itself a subsingleton. -/
theorem boundary_epi_iff_riemannHypothesis
    (hBD : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    Epi (TopModuleCat.ofHom boundary) ↔ RiemannHypothesis := by
  constructor
  · intro h
    let := h
    exact riemannHypothesis_of_boundary_epi
  · intro h
    have : Subsingleton BoundaryTarget := boundaryTarget_subsingleton_iff_one_mem.mpr
      (BaezDuarte.one_mem_of_riemannHypothesis hBD h)
    apply ConcreteCategory.epi_of_surjective (TopModuleCat.ofHom boundary)
    exact fun b => ⟨0, Subsingleton.elim _ b⟩

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake
