import RiemannResearch.RH.MultiRangeScreening
import RiemannResearch.RH.MultiRangeSignedFiniteFamily

/-! Exact attained signed gain for an entire new screened divisor range.
All matrix positivity and inverse existence are proved from distinct conductor
charges. No subpolynomial estimate is supplied. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID

variable {D E : ℕ} (A : ℕ) (d : Fin D → ℕ)
  (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
  (e : Fin E → ℕ) (he : ∀ i, 1 < e i ∧ e i ≠ A)
  (heinj : Function.Injective e) (hdis : ∀ i j, e i ≠ d j)

def screenedRangeFamily (i : Fin E) : ℕ → ℝ :=
  screenedByAnchors A d hA hd hinj (divisorAnchorDirection A (e i))

include he in
theorem screenedRangeFamily_legal (i : Fin E) :
    screenedRangeFamily A d hA hd hinj e i ∈ legalSeedSpan (Set.Ici 1) :=
  screenedByAnchors_legal A d hA hd hinj _
    (divisorAnchorDirection_legal A (e i) hA (by have := (he i).1; omega))

include he heinj hdis in
theorem screenedRangeFamily_charge (i j : Fin E) :
    mobiusDifference (e i) (screenedRangeFamily A d hA hd hinj e j) =
      if i = j then 1 else 0 := by
  unfold screenedRangeFamily
  rw [screenedByAnchors_charge A d hA hd hinj _ (e i) (he i).1 (he i).2 (hdis i),
    divisorAnchorDirection_charge A (e j) (e i) (he i).1 (he i).2]
  simp only [heinj.eq_iff]

include he heinj hdis in
/-- Old-range screening cannot destroy independence of disjoint new conductors. -/
theorem screenedRangeFamily_kernel (x : Fin E → ℝ)
    (hx : signedFamilySynthesis (screenedRangeFamily A d hA hd hinj e) x = 0) : x = 0 := by
  classical
  funext i
  have hsum : mobiusDifference (e i)
      (signedFamilySynthesis (screenedRangeFamily A d hA hd hinj e) x) =
      ∑ j, x j * mobiusDifference (e i) (screenedRangeFamily A d hA hd hinj e j) := by
    unfold signedFamilySynthesis mobiusDifference
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hx] at hsum
  simp_rw [screenedRangeFamily_charge A d hA hd hinj e he heinj hdis] at hsum
  simpa [mobiusDifference, mul_ite, Finset.sum_ite_eq', eq_comm] using hsum.symm

include he heinj hdis in
/-- The entire new Schur matrix is strictly positive definite. -/
theorem screenedRangeFamily_posDef :
    (signedFamilyGram (screenedRangeFamily A d hA hd hinj e)).PosDef :=
  signedFamilyGram_posDef _ (screenedRangeFamily_legal A d hA hd hinj e he)
    (screenedRangeFamily_kernel A d hA hd hinj e he heinj hdis)

include he in
/-- Actual Schur entries retain every old-new and new-new signed covariance. -/
theorem screenedRangeFamily_gram_entry (i j : Fin E) :
    signedFamilyGram (screenedRangeFamily A d hA hd hinj e) i j =
      conditionalMeanInner (divisorAnchorDirection A (e i)) (divisorAnchorDirection A (e j)) -
      ∑ k, anchorInverseCoeff A d hA hd hinj (divisorAnchorDirection A (e i)) k *
        anchorSource A d (divisorAnchorDirection A (e j)) k := by
  exact screenedByAnchors_bilinear A d hA hd hinj _ _
    (divisorAnchorDirection_legal A (e i) hA (by have := (he i).1; omega))
    (divisorAnchorDirection_legal A (e j) hA (by have := (he j).1; omega))

include he in
/-- Actual screened source k=hnew-Bᵀ Gold⁻¹ hold. -/
theorem screenedRangeFamily_source_entry (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (i : Fin E) :
    signedFamilySource (screenedRangeFamily A d hA hd hinj e)
      (screenedByAnchors A d hA hd hinj F) i =
      conditionalMeanInner F (divisorAnchorDirection A (e i)) -
      ∑ k, anchorInverseCoeff A d hA hd hinj F k *
        anchorSource A d (divisorAnchorDirection A (e i)) k := by
  exact screenedByAnchors_bilinear A d hA hd hinj F _ hF
    (divisorAnchorDirection_legal A (e i) hA (by have := (he i).1; omega))

def screenedBlockInverseCoeff (F : ℕ → ℝ) : Fin E → ℝ :=
  signedFamilyInverseCoeff (screenedRangeFamily A d hA hd hinj e)
    (screenedRangeFamily_legal A d hA hd hinj e he)
    (screenedRangeFamily_kernel A d hA hd hinj e he heinj hdis)
    (screenedByAnchors A d hA hd hinj F)

def screenedBlockWitness (F : ℕ → ℝ) : ℕ → ℝ :=
  fun n => screenedByAnchors A d hA hd hinj F n +
    signedFamilySynthesis (screenedRangeFamily A d hA hd hinj e)
      (-screenedBlockInverseCoeff A d hA hd hinj e he heinj hdis F) n

/-- The exact multi-column gain kᵀ S⁻¹ k, with no assumed inverse. -/
theorem screenedBlock_energy (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) :
    conditionalMeanSquare (screenedBlockWitness A d hA hd hinj e he heinj hdis F) =
      conditionalMeanSquare (screenedByAnchors A d hA hd hinj F) -
      ∑ i, screenedBlockInverseCoeff A d hA hd hinj e he heinj hdis F i *
        signedFamilySource (screenedRangeFamily A d hA hd hinj e)
          (screenedByAnchors A d hA hd hinj F) i := by
  exact signedFamily_minimum_value _ (screenedRangeFamily_legal A d hA hd hinj e he)
    (screenedRangeFamily_kernel A d hA hd hinj e he heinj hdis) _
    (screenedByAnchors_legal A d hA hd hinj F hF)

theorem screenedBlock_minimizes (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin E → ℝ) :
    conditionalMeanSquare (screenedBlockWitness A d hA hd hinj e he heinj hdis F) ≤
      conditionalMeanSquare (fun n => screenedByAnchors A d hA hd hinj F n +
        signedFamilySynthesis (screenedRangeFamily A d hA hd hinj e) x n) := by
  exact signedFamily_minimizes _ (screenedRangeFamily_legal A d hA hd hinj e he)
    (screenedRangeFamily_kernel A d hA hd hinj e he heinj hdis) _
    (screenedByAnchors_legal A d hA hd hinj F hF) x

include he in
/-- The new screened family is orthogonal to the entire old range. -/
theorem screenedRangeFamily_orthogonal (x : Fin E → ℝ) (z : Fin D → ℝ) :
    conditionalMeanInner (signedFamilySynthesis (screenedRangeFamily A d hA hd hinj e) x)
      (anchorSynthesis A d z) = 0 := by
  rw [conditionalMeanInner_comm,
    signedFamilySource_synthesis _ (screenedRangeFamily_legal A d hA hd hinj e he) _
      (anchorSynthesis_legal A d z hA (fun i => by have := (hd i).1; omega))]
  apply Finset.sum_eq_zero
  intro i hi
  unfold signedFamilySource screenedRangeFamily
  rw [conditionalMeanInner_comm,
    screenedByAnchors_orthogonal A d hA hd hinj _
      (divisorAnchorDirection_legal A (e i) hA (by have := (he i).1; omega)), mul_zero]

/-- Simultaneous optimization allows arbitrary additional old coefficients;
old and new screened ranges remain exactly orthogonal. -/
theorem screenedBlock_minimizes_with_old (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin E → ℝ) (z : Fin D → ℝ) :
    conditionalMeanSquare (screenedBlockWitness A d hA hd hinj e he heinj hdis F) ≤
      conditionalMeanSquare (fun n =>
        (screenedByAnchors A d hA hd hinj F n +
          signedFamilySynthesis (screenedRangeFamily A d hA hd hinj e) x n) +
        anchorSynthesis A d z n) := by
  let R := fun n => screenedByAnchors A d hA hd hinj F n +
    signedFamilySynthesis (screenedRangeFamily A d hA hd hinj e) x n
  have hS := screenedByAnchors_legal A d hA hd hinj F hF
  have hX := signedFamilySynthesis_legal _ (screenedRangeFamily_legal A d hA hd hinj e he) x
  have hZ := anchorSynthesis_legal A d z hA (fun i => by have := (hd i).1; omega)
  have hR : R ∈ legalSeedSpan (Set.Ici 1) := (legalSeedSpan _).add_mem hS hX
  have ho : conditionalMeanInner R (anchorSynthesis A d z) = 0 := by
    have hh := conditionalMeanInner_add_mul_left _ _ (anchorSynthesis A d z) hS hX hZ 1
    simp only [one_mul] at hh
    rw [screenedByAnchors_orthogonal A d hA hd hinj F hF,
      screenedRangeFamily_orthogonal A d hA hd hinj e he x z] at hh
    simpa only [add_zero] using hh
  have heq := conditionalMeanSquare_add_mul R (anchorSynthesis A d z) hR hZ 1
  simp only [one_mul, one_pow, mul_one, ho, mul_zero, add_zero] at heq
  rw [heq]
  exact (screenedBlock_minimizes A d hA hd hinj e he heinj hdis F hF x).trans
    (le_add_of_nonneg_right (conditionalMeanSquare_nonneg _))

/-- Exact triangular change of coordinates from screened to original ranges. -/
theorem screenedRangeFamily_synthesis (x : Fin E → ℝ) (n : ℕ) :
    signedFamilySynthesis (screenedRangeFamily A d hA hd hinj e) x n =
      anchorSynthesis A e x n - anchorSynthesis A d
        (fun j => ∑ i, x i * anchorInverseCoeff A d hA hd hinj
          (divisorAnchorDirection A (e i)) j) n := by
  have hc : (∑ i, x i * anchorSynthesis A d
      (anchorInverseCoeff A d hA hd hinj (divisorAnchorDirection A (e i))) n) =
      anchorSynthesis A d (fun j => ∑ i, x i * anchorInverseCoeff A d hA hd hinj
        (divisorAnchorDirection A (e i)) j) n := by
    unfold anchorSynthesis
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold signedFamilySynthesis screenedRangeFamily screenedByAnchors
  calc
    _ = (∑ i, x i * divisorAnchorDirection A (e i) n) -
        ∑ i, x i * anchorSynthesis A d
          (anchorInverseCoeff A d hA hd hinj (divisorAnchorDirection A (e i))) n := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [hc]; rfl

/-- Every original simultaneous coefficient vector lies in the screened chart. -/
theorem originalRanges_eq_screened (F : ℕ → ℝ) (x : Fin D → ℝ) (y : Fin E → ℝ) :
    (fun n => F n + anchorSynthesis A d x n + anchorSynthesis A e y n) =
      fun n => (screenedByAnchors A d hA hd hinj F n +
        signedFamilySynthesis (screenedRangeFamily A d hA hd hinj e) y n) +
        anchorSynthesis A d
          (fun j => x j + anchorInverseCoeff A d hA hd hinj F j +
            ∑ i, y i * anchorInverseCoeff A d hA hd hinj
              (divisorAnchorDirection A (e i)) j) n := by
  funext n
  rw [screenedRangeFamily_synthesis A d hA hd hinj e y n]
  unfold screenedByAnchors
  have heq : anchorSynthesis A d
      (fun j => x j + anchorInverseCoeff A d hA hd hinj F j +
        ∑ i, y i * anchorInverseCoeff A d hA hd hinj (divisorAnchorDirection A (e i)) j) n =
      anchorSynthesis A d x n + anchorSynthesis A d (anchorInverseCoeff A d hA hd hinj F) n +
        anchorSynthesis A d (fun j => ∑ i, y i * anchorInverseCoeff A d hA hd hinj
          (divisorAnchorDirection A (e i)) j) n := by
    simp only [anchorSynthesis, add_mul, Finset.sum_add_distrib]
  rw [heq]
  ring

/-- The block Schur value is the minimum over the original old and new ranges. -/
theorem screenedBlock_minimizes_original (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ) (y : Fin E → ℝ) :
    conditionalMeanSquare (screenedBlockWitness A d hA hd hinj e he heinj hdis F) ≤
      conditionalMeanSquare (fun n => F n + anchorSynthesis A d x n + anchorSynthesis A e y n) := by
  rw [originalRanges_eq_screened A d hA hd hinj e F x y]
  exact screenedBlock_minimizes_with_old A d hA hd hinj e he heinj hdis F hF y _

/-- The minimizing screened witness is attained in the original legal chart. -/
theorem screenedBlock_original_coefficients (F : ℕ → ℝ) :
    ∃ (x : Fin D → ℝ) (y : Fin E → ℝ),
      screenedBlockWitness A d hA hd hinj e he heinj hdis F =
        fun n => F n + anchorSynthesis A d x n + anchorSynthesis A e y n := by
  let y := -screenedBlockInverseCoeff A d hA hd hinj e he heinj hdis F
  let q : Fin D → ℝ := fun j => ∑ i, y i * anchorInverseCoeff A d hA hd hinj
    (divisorAnchorDirection A (e i)) j
  let x : Fin D → ℝ := fun j => -anchorInverseCoeff A d hA hd hinj F j - q j
  refine ⟨x, y, ?_⟩
  rw [originalRanges_eq_screened A d hA hd hinj e F x y]
  have hz : (fun j => x j + anchorInverseCoeff A d hA hd hinj F j +
      ∑ i, y i * anchorInverseCoeff A d hA hd hinj (divisorAnchorDirection A (e i)) j) = 0 := by
    funext j
    dsimp [x, q]
    ring
  rw [hz]
  funext n
  simp only [anchorSynthesis, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

end RiemannResearch.RH.Pareto
