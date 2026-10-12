import RiemannResearch.RH.MultiRangeFiniteMinimum
import RiemannResearch.LinearAlgebra.FiniteConstrainedMatrixInverse
import RiemannResearch.RH.ConditionalResidueGram

/-! Exact signed minimization for finite legal families, used for screened ranges. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro Analysis.FiniteSignedQuadratic
open RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix

variable {D : ℕ}

def signedFamilySynthesis (U : Fin D → ℕ → ℝ) (x : Fin D → ℝ) : ℕ → ℝ :=
  fun n => ∑ i, x i * U i n

def signedFamilyGram (U : Fin D → ℕ → ℝ) : Matrix (Fin D) (Fin D) ℝ :=
  fun i j => conditionalMeanInner (U i) (U j)

def signedFamilySource (U : Fin D → ℕ → ℝ) (F : ℕ → ℝ) : Fin D → ℝ :=
  fun i => conditionalMeanInner F (U i)

theorem signedFamilySynthesis_legal (U : Fin D → ℕ → ℝ)
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ) :
    signedFamilySynthesis U x ∈ legalSeedSpan (Set.Ici 1) := by
  have h : (∑ i, x i • U i) ∈ legalSeedSpan (Set.Ici 1) := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (hU i)
  convert h using 1
  funext n
  simp only [signedFamilySynthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem signedFamilySource_synthesis (U : Fin D → ℕ → ℝ)
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1)) (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ) :
    conditionalMeanInner F (signedFamilySynthesis U x) =
      ∑ i, x i * signedFamilySource U F i := by
  have hs (i : Fin D) := conditionalMeanInner_summable F (U i) hF (hU i)
  unfold conditionalMeanInner signedFamilySynthesis
  simp_rw [cesaro_finsetCombination, Finset.mul_sum]
  calc
    _ = ∑' k : ℕ, ∑ i, x i * (conditionalWeight k * cesaro F (k+1) * cesaro (U i) (k+1)) := by
      apply tsum_congr
      intro k
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, ∑' k : ℕ, x i * (conditionalWeight k * cesaro F (k+1) * cesaro (U i) (k+1)) :=
      Summable.tsum_finsetSum (fun i hi => (hs i).mul_left (x i))
    _ = _ := by simp only [tsum_mul_left, signedFamilySource, conditionalMeanInner]

theorem signedFamilyGram_quadratic (U : Fin D → ℕ → ℝ)
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ) :
    quadratic (signedFamilyGram U) x = conditionalMeanSquare (signedFamilySynthesis U x) := by
  rw [← conditionalMeanInner_self, signedFamilySource_synthesis U hU _
    (signedFamilySynthesis_legal U hU x)]
  unfold quadratic signedFamilyGram signedFamilySource
  apply Finset.sum_congr rfl
  intro i hi
  rw [conditionalMeanInner_comm, signedFamilySource_synthesis U hU (U i) (hU i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold signedFamilySource
  ring

/-- Positivity follows from actual legal arithmetic synthesis injectivity. -/
theorem signedFamilyGram_posDef (U : Fin D → ℕ → ℝ)
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1))
    (hker : ∀ x, signedFamilySynthesis U x = 0 → x = 0) :
    (signedFamilyGram U).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial, signedFamilyGram] using
      conditionalMeanInner_comm (U j) (U i)
  · intro x hx
    have hp := conditionalMeanTailSquare_pos (Set.Ici 1) (by intro a ha; exact ha)
      (signedFamilySynthesis_legal U hU x) (fun he => hx (hker x he)) 0
    simp only [conditionalMeanTailSquare, Nat.add_zero] at hp
    change 0 < conditionalMeanSquare (signedFamilySynthesis U x) at hp
    have he := signedFamilyGram_quadratic U hU x
    rw [quadratic_mulVec] at he
    simp only [star_trivial]
    change 0 < ∑ i, x i * (signedFamilyGram U).mulVec x i
    rw [he]
    exact hp

def signedFamilyInverseCoeff (U : Fin D → ℕ → ℝ)
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1))
    (hker : ∀ x, signedFamilySynthesis U x = 0 → x = 0) (F : ℕ → ℝ) : Fin D → ℝ :=
  (gramEquiv (signedFamilyGram U) (signedFamilyGram_posDef U hU hker)).symm
    (signedFamilySource U F)

theorem signedFamilyInverseCoeff_eq_inverse (U : Fin D → ℕ → ℝ)
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1))
    (hker : ∀ x, signedFamilySynthesis U x = 0 → x = 0) (F : ℕ → ℝ) :
    signedFamilyInverseCoeff U hU hker F =
      (signedFamilyGram U)⁻¹.mulVec (signedFamilySource U F) :=
  gramEquiv_symm_eq_inv_mulVec _ _ _

theorem signedFamily_affine_energy (U : Fin D → ℕ → ℝ)
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1)) (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ) :
    conditionalMeanSquare (fun n => F n + signedFamilySynthesis U x n) =
      conditionalMeanSquare F + 2 * (∑ i, x i * signedFamilySource U F i) +
        quadratic (signedFamilyGram U) x := by
  have he := conditionalMeanSquare_add_mul F (signedFamilySynthesis U x) hF
    (signedFamilySynthesis_legal U hU x) 1
  simp only [one_mul, one_pow] at he
  rw [signedFamilySource_synthesis U hU F hF x, ← signedFamilyGram_quadratic U hU x] at he
  simpa only [mul_one] using he

theorem signedFamily_completion (U : Fin D → ℕ → ℝ)
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1))
    (hker : ∀ x, signedFamilySynthesis U x = 0 → x = 0)
    (F : ℕ → ℝ) (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ) :
    conditionalMeanSquare (fun n => F n + signedFamilySynthesis U x n) =
      conditionalMeanSquare F -
        (∑ i, signedFamilyInverseCoeff U hU hker F i * signedFamilySource U F i) +
        quadratic (signedFamilyGram U) (x + signedFamilyInverseCoeff U hU hker F) := by
  rw [signedFamily_affine_energy U hU F hF]
  apply schur_completion
  · intro i j
    exact conditionalMeanInner_comm (U i) (U j)
  · exact (gramEquiv (signedFamilyGram U) (signedFamilyGram_posDef U hU hker)).apply_symm_apply _

/-- The block value is attained; the inverse is not an assumption. -/
theorem signedFamily_minimum_value (U : Fin D → ℕ → ℝ)
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1))
    (hker : ∀ x, signedFamilySynthesis U x = 0 → x = 0)
    (F : ℕ → ℝ) (hF : F ∈ legalSeedSpan (Set.Ici 1)) :
    conditionalMeanSquare (fun n => F n + signedFamilySynthesis U
      (-signedFamilyInverseCoeff U hU hker F) n) =
      conditionalMeanSquare F -
        ∑ i, signedFamilyInverseCoeff U hU hker F i * signedFamilySource U F i := by
  rw [signedFamily_completion U hU hker F hF]
  simp [quadratic]

theorem signedFamily_minimizes (U : Fin D → ℕ → ℝ)
    (hU : ∀ i, U i ∈ legalSeedSpan (Set.Ici 1))
    (hker : ∀ x, signedFamilySynthesis U x = 0 → x = 0)
    (F : ℕ → ℝ) (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ) :
    conditionalMeanSquare (fun n => F n + signedFamilySynthesis U
      (-signedFamilyInverseCoeff U hU hker F) n) ≤
      conditionalMeanSquare (fun n => F n + signedFamilySynthesis U x n) := by
  rw [signedFamily_minimum_value U hU hker F hF, signedFamily_completion U hU hker F hF,
    signedFamilyGram_quadratic U hU]
  exact le_add_of_nonneg_right (conditionalMeanSquare_nonneg _)

end RiemannResearch.RH.Pareto
