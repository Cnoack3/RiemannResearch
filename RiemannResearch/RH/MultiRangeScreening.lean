import RiemannResearch.RH.MultiRangeFiniteMinimum
import RiemannResearch.LinearAlgebra.FiniteConstrainedMatrixInverse
import RiemannResearch.RH.ConditionalResidueGram

/-! Exact signed old-range screening of new ranges. These are the actual
arithmetic Schur entries and source, with the old inverse constructed. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID
open RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix

variable {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
  (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)

theorem anchorGram_eq_inner (i j : Fin D) :
    anchorGram A d i j = conditionalMeanInner
      (divisorAnchorDirection A (d i)) (divisorAnchorDirection A (d j)) := by
  unfold anchorGram conditionalTailPairing conditionalMeanInner
  apply tsum_congr
  intro k
  simp only [Nat.add_zero]
  ring

theorem anchorInverseCoeff_eq_inverse (F : ℕ → ℝ) :
    anchorInverseCoeff A d hA hd hinj F =
      (anchorGram A d)⁻¹.mulVec (anchorSource A d F) := by
  exact gramEquiv_symm_eq_inv_mulVec _ _ _

def screenedByAnchors (F : ℕ → ℝ) : ℕ → ℝ :=
  fun n => F n + (-1) * anchorSynthesis A d (anchorInverseCoeff A d hA hd hinj F) n

theorem screenedByAnchors_legal (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) :
    screenedByAnchors A d hA hd hinj F ∈ legalSeedSpan (Set.Ici 1) :=
  legal_add_mul F _ hF (anchorSynthesis_legal A d _ hA
    (fun i => by have := (hd i).1; omega)) (-1)

/-- The exact screened source, before any absolute-value bound. -/
theorem screenedByAnchors_source (F G : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1)) :
    conditionalMeanInner (screenedByAnchors A d hA hd hinj F) G =
      conditionalMeanInner F G - ∑ i,
        anchorInverseCoeff A d hA hd hinj F i * anchorSource A d G i := by
  unfold screenedByAnchors
  rw [conditionalMeanInner_add_mul_left F _ G hF
    (anchorSynthesis_legal A d _ hA (fun i => by have := (hd i).1; omega)) hG,
    conditionalMeanInner_comm (anchorSynthesis A d _) G,
    anchorSource_synthesis A d hA (fun i => by have := (hd i).1; omega) G hG]
  ring

theorem screenedByAnchors_orthogonal_column (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (i : Fin D) :
    conditionalMeanInner (screenedByAnchors A d hA hd hinj F)
      (divisorAnchorDirection A (d i)) = 0 := by
  rw [screenedByAnchors_source A d hA hd hinj F _ hF
    (divisorAnchorDirection_legal A (d i) hA (by have := (hd i).1; omega))]
  have hn := congrFun (anchorInverseCoeff_normal A d hA hd hinj F) i
  have he : (∑ j, anchorInverseCoeff A d hA hd hinj F j *
      anchorSource A d (divisorAnchorDirection A (d i)) j) =
      (anchorGram A d).mulVec (anchorInverseCoeff A d hA hd hinj F) i := by
    unfold Matrix.mulVec dotProduct anchorSource
    apply Finset.sum_congr rfl
    intro j hj
    change anchorInverseCoeff A d hA hd hinj F j *
      conditionalMeanInner (divisorAnchorDirection A (d i)) (divisorAnchorDirection A (d j)) =
      anchorGram A d i j * anchorInverseCoeff A d hA hd hinj F j
    rw [anchorGram_eq_inner]
    ring
  rw [he, hn]
  simp [anchorSource]

theorem screenedByAnchors_orthogonal (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ) :
    conditionalMeanInner (screenedByAnchors A d hA hd hinj F) (anchorSynthesis A d x) = 0 := by
  rw [anchorSource_synthesis A d hA (fun i => by have := (hd i).1; omega) _
    (screenedByAnchors_legal A d hA hd hinj F hF)]
  apply Finset.sum_eq_zero
  intro i hi
  rw [anchorSource, screenedByAnchors_orthogonal_column A d hA hd hinj F hF, mul_zero]

/-- Each new-range Gram entry is Gnew - Bᵀ Gold⁻¹ B, exactly. -/
theorem screenedByAnchors_bilinear (F G : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1))
    (hG : G ∈ legalSeedSpan (Set.Ici 1)) :
    conditionalMeanInner (screenedByAnchors A d hA hd hinj F)
      (screenedByAnchors A d hA hd hinj G) =
      conditionalMeanInner F G - ∑ i,
        anchorInverseCoeff A d hA hd hinj F i * anchorSource A d G i := by
  change conditionalMeanInner (screenedByAnchors A d hA hd hinj F)
    (fun n => G n + (-1) * anchorSynthesis A d (anchorInverseCoeff A d hA hd hinj G) n) = _
  rw [conditionalMeanInner_add_mul_right _ G _
    (screenedByAnchors_legal A d hA hd hinj F hF) hG
    (anchorSynthesis_legal A d _ hA (fun i => by have := (hd i).1; omega)),
    screenedByAnchors_orthogonal A d hA hd hinj F hF, mul_zero, add_zero,
    screenedByAnchors_source A d hA hd hinj F G hF hG]

/-- Old optimized energy is its exact inverse-Gram subtraction. -/
theorem screenedByAnchors_energy (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) :
    conditionalMeanSquare (screenedByAnchors A d hA hd hinj F) =
      conditionalMeanSquare F - ∑ i,
        anchorInverseCoeff A d hA hd hinj F i * anchorSource A d F i := by
  have he := screenedByAnchors_bilinear A d hA hd hinj F F hF hF
  simpa only [conditionalMeanInner_self] using he

/-- Old ranges have zero Möbius charge at every unused conductor. -/
theorem anchorSynthesis_charge_outside (x : Fin D → ℝ) (m : ℕ)
    (hm : 1 < m) (hmA : m ≠ A) (hmd : ∀ i, m ≠ d i) :
    mobiusDifference m (anchorSynthesis A d x) = 0 := by
  have he : mobiusDifference m (anchorSynthesis A d x) =
      ∑ i, x i * mobiusDifference m (divisorAnchorDirection A (d i)) := by
    unfold anchorSynthesis mobiusDifference
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he]
  apply Finset.sum_eq_zero
  intro i hi
  rw [divisorAnchorDirection_charge A (d i) m hm hmA, if_neg (hmd i), mul_zero]

/-- Screening against old ranges preserves each unused arithmetic charge. -/
theorem screenedByAnchors_charge (F : ℕ → ℝ) (m : ℕ)
    (hm : 1 < m) (hmA : m ≠ A) (hmd : ∀ i, m ≠ d i) :
    mobiusDifference m (screenedByAnchors A d hA hd hinj F) = mobiusDifference m F := by
  have he : mobiusDifference m (screenedByAnchors A d hA hd hinj F) =
      mobiusDifference m F -
        mobiusDifference m (anchorSynthesis A d (anchorInverseCoeff A d hA hd hinj F)) := by
    unfold screenedByAnchors mobiusDifference
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he, anchorSynthesis_charge_outside A d _ m hm hmA hmd, sub_zero]

end RiemannResearch.RH.Pareto
