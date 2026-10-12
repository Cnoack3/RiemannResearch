import RiemannResearch.RH.MultiRangeIndependence
import RiemannResearch.RH.MultiRangeEnergyCertificates
import RiemannResearch.LinearAlgebra.FiniteConstrainedMatrixMinimum
import RiemannResearch.Analysis.FiniteSignedQuadratic
import RiemannResearch.RH.ConditionalResidueGram

/-! Actual signed finite anchor Gram matrices and their unconditional optimizer.
Source: RH_Multi_Range_Divisor_Corrections_2026-09-18.md, Section 4.
The inverse is constructed from proved positivity, with no arithmetic bound assumed. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative Probability.ConditionalIID Analysis.Cesaro
open Analysis.FiniteSignedQuadratic
open RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix

/-- Distinct conductor indices parameterize a finite family. -/
def anchorSynthesis {D : ℕ} (A : ℕ) (d : Fin D → ℕ) (x : Fin D → ℝ) : ℕ → ℝ :=
  fun n => ∑ i, x i * divisorAnchorDirection A (d i) n

def anchorGram {D : ℕ} (A : ℕ) (d : Fin D → ℕ) : Matrix (Fin D) (Fin D) ℝ :=
  fun i j => conditionalTailPairing 0
    (cesaro (divisorAnchorDirection A (d i))) (cesaro (divisorAnchorDirection A (d j)))

def anchorSource {D : ℕ} (A : ℕ) (d : Fin D → ℕ) (F : ℕ → ℝ) : Fin D → ℝ :=
  fun i => conditionalMeanInner F (divisorAnchorDirection A (d i))

theorem anchorSynthesis_legal {D : ℕ} (A : ℕ) (d : Fin D → ℕ) (x : Fin D → ℝ)
    (hA : 0 < A) (hd : ∀ i, 0 < d i) :
    anchorSynthesis A d x ∈ legalSeedSpan (Set.Ici 1) := by
  have h : (∑ i, x i • divisorAnchorDirection A (d i)) ∈ legalSeedSpan (Set.Ici 1) := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (divisorAnchorDirection_legal A (d i) hA (hd i))
  convert h using 1
  funext n
  simp only [anchorSynthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem anchorSynthesis_charge {D : ℕ} (A : ℕ) (d : Fin D → ℕ) (x : Fin D → ℝ)
    (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d) (i : Fin D) :
    mobiusDifference (d i) (anchorSynthesis A d x) = x i := by
  classical
  have he : mobiusDifference (d i) (anchorSynthesis A d x) =
      ∑ j, x j * mobiusDifference (d i) (divisorAnchorDirection A (d j)) := by
    unfold anchorSynthesis mobiusDifference
    simp only [← Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he]
  simp_rw [divisorAnchorDirection_charge A _ (d i) (hd i).1 (hd i).2]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hij : d i ≠ d j := fun h => hji (hinj h).symm
    simp [hij]
  · simp

theorem anchorGram_quadratic {D : ℕ} (A : ℕ) (d : Fin D → ℕ) (x : Fin D → ℝ)
    (hA : 0 < A) (hd : ∀ i, 0 < d i) :
    quadratic (anchorGram A d) x = conditionalMeanSquare (anchorSynthesis A d x) := by
  have hb (i : Fin D) (n : ℕ) :
      |cesaro (divisorAnchorDirection A (d i)) n| ≤ ((A : ℝ) / d i + 1) / 2 :=
    divisorAnchorDirection_mean_bound A (d i) n hA (hd i)
  calc
    _ = ∑ i, ∑ j, x i * x j * conditionalTailPairing 0
        (cesaro (divisorAnchorDirection A (d i)))
        (cesaro (divisorAnchorDirection A (d j))) := by
      unfold quadratic anchorGram
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = conditionalTailPairing 0
        (fun n => ∑ i, x i * cesaro (divisorAnchorDirection A (d i)) n)
        (fun n => ∑ i, x i * cesaro (divisorAnchorDirection A (d i)) n) :=
      (conditionalTailPairing_finsetCombination 0 Finset.univ x hb).symm
    _ = _ := by
      unfold conditionalTailPairing conditionalMeanSquare anchorSynthesis
      apply tsum_congr
      intro k
      rw [cesaro_finsetCombination]
      simp only [Nat.add_zero]
      ring

/-- Every actual nonzero anchor coefficient array has strictly positive energy. -/
theorem anchorGram_posDef {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d) :
    (anchorGram A d).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simpa only [Matrix.conjTranspose_apply, star_trivial, anchorGram] using
      conditionalTailPairing_comm 0
        (cesaro (divisorAnchorDirection A (d j))) (cesaro (divisorAnchorDirection A (d i)))
  · intro x hx
    have hd0 : ∀ i, 0 < d i := fun i => by have := (hd i).1; omega
    have hz : anchorSynthesis A d x ≠ 0 := by
      intro he
      apply hx
      funext i
      have hc := anchorSynthesis_charge A d x hd hinj i
      rw [he] at hc
      simpa [mobiusDifference] using hc.symm
    have hp := conditionalMeanTailSquare_pos (Set.Ici 1) (by intro a ha; exact ha)
      (anchorSynthesis_legal A d x hA hd0) hz 0
    have he := anchorGram_quadratic A d x hA hd0
    rw [quadratic_mulVec] at he
    simp only [conditionalMeanTailSquare, Nat.add_zero] at hp
    change 0 < conditionalMeanSquare (anchorSynthesis A d x) at hp
    change 0 < ∑ i, x i * (anchorGram A d).mulVec x i
    rw [he]
    exact hp

/-- The actual inverse Gram solution; its additive optimizer is the negative. -/
def anchorInverseCoeff {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (F : ℕ → ℝ) : Fin D → ℝ :=
  (gramEquiv (anchorGram A d) (anchorGram_posDef A d hA hd hinj)).symm
    (anchorSource A d F)

theorem anchorInverseCoeff_normal {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (F : ℕ → ℝ) :
    (anchorGram A d).mulVec (anchorInverseCoeff A d hA hd hinj F) = anchorSource A d F :=
  (gramEquiv (anchorGram A d) (anchorGram_posDef A d hA hd hinj)).apply_symm_apply _

/-- Exact finite signed completion with invertibility discharged arithmetically. -/
theorem anchor_quadratic_completion {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (F : ℕ → ℝ) (x : Fin D → ℝ) :
    conditionalMeanSquare F + 2 * (∑ i, x i * anchorSource A d F i) +
      quadratic (anchorGram A d) x =
    conditionalMeanSquare F -
      (∑ i, anchorInverseCoeff A d hA hd hinj F i * anchorSource A d F i) +
      quadratic (anchorGram A d) (x + anchorInverseCoeff A d hA hd hinj F) := by
  apply schur_completion
  · intro i j
    exact conditionalTailPairing_comm 0 _ _
  · exact anchorInverseCoeff_normal A d hA hd hinj F

theorem anchorSource_synthesis {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 0 < d i) (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ) :
    conditionalMeanInner F (anchorSynthesis A d x) =
      ∑ i, x i * anchorSource A d F i := by
  have hs (i : Fin D) := conditionalMeanInner_summable F
    (divisorAnchorDirection A (d i)) hF (divisorAnchorDirection_legal A (d i) hA (hd i))
  unfold conditionalMeanInner anchorSynthesis
  simp_rw [cesaro_finsetCombination, Finset.mul_sum]
  calc
    _ = ∑' k : ℕ, ∑ i, x i * (conditionalWeight k * cesaro F (k + 1) *
        cesaro (divisorAnchorDirection A (d i)) (k + 1)) := by
      apply tsum_congr
      intro k
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, ∑' k : ℕ, x i * (conditionalWeight k * cesaro F (k + 1) *
        cesaro (divisorAnchorDirection A (d i)) (k + 1)) :=
      Summable.tsum_finsetSum (fun i hi => (hs i).mul_left (x i))
    _ = _ := by simp only [tsum_mul_left, anchorSource, conditionalMeanInner]

/-- This quadratic is the original infinite conditional energy. -/
theorem anchor_affine_energy {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 0 < d i) (F : ℕ → ℝ)
    (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ) :
    conditionalMeanSquare (fun n => F n + anchorSynthesis A d x n) =
      conditionalMeanSquare F + 2 * (∑ i, x i * anchorSource A d F i) +
        quadratic (anchorGram A d) x := by
  have he := conditionalMeanSquare_add_mul F (anchorSynthesis A d x) hF
    (anchorSynthesis_legal A d x hA hd) 1
  simp only [one_mul, one_pow] at he
  rw [anchorSource_synthesis A d hA hd F hF x, ← anchorGram_quadratic A d x hA hd] at he
  simpa only [mul_one] using he

/-- The actual arithmetic affine family has an attained inverse-Gram value. -/
theorem anchor_minimum_value {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (F : ℕ → ℝ) (hF : F ∈ legalSeedSpan (Set.Ici 1)) :
    conditionalMeanSquare (fun n => F n + anchorSynthesis A d
      (-anchorInverseCoeff A d hA hd hinj F) n) =
      conditionalMeanSquare F -
        ∑ i, anchorInverseCoeff A d hA hd hinj F i * anchorSource A d F i := by
  rw [anchor_affine_energy A d hA (fun i => by have := (hd i).1; omega) F hF,
    anchor_quadratic_completion A d hA hd hinj F]
  simp [quadratic]

theorem anchor_minimizes {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (F : ℕ → ℝ) (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ) :
    conditionalMeanSquare (fun n => F n + anchorSynthesis A d
      (-anchorInverseCoeff A d hA hd hinj F) n) ≤
      conditionalMeanSquare (fun n => F n + anchorSynthesis A d x n) := by
  have hd0 : ∀ i, 0 < d i := fun i => by have := (hd i).1; omega
  rw [anchor_minimum_value A d hA hd hinj F hF,
    anchor_affine_energy A d hA hd0 F hF,
    anchor_quadratic_completion A d hA hd hinj F,
    anchorGram_quadratic A d _ hA hd0]
  exact le_add_of_nonneg_right (conditionalMeanSquare_nonneg _)

/-- Strict positivity gives uniqueness of the optimizing signed coefficient vector. -/
theorem anchor_minimizer_unique {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hA : 0 < A) (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (F : ℕ → ℝ) (hF : F ∈ legalSeedSpan (Set.Ici 1)) (x : Fin D → ℝ)
    (he : conditionalMeanSquare (fun n => F n + anchorSynthesis A d x n) =
      conditionalMeanSquare F -
        ∑ i, anchorInverseCoeff A d hA hd hinj F i * anchorSource A d F i) :
    x = -anchorInverseCoeff A d hA hd hinj F := by
  rw [anchor_affine_energy A d hA (fun i => by have := (hd i).1; omega) F hF,
    anchor_quadratic_completion A d hA hd hinj F] at he
  have hz : x + anchorInverseCoeff A d hA hd hinj F = 0 := by
    by_contra hn
    have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp
      (anchorGram_posDef A d hA hd hinj)).2 hn
    simp only [star_trivial] at hp
    rw [quadratic_mulVec] at he
    change 0 < ∑ i, (x + anchorInverseCoeff A d hA hd hinj F) i *
      (anchorGram A d).mulVec (x + anchorInverseCoeff A d hA hd hinj F) i at hp
    linarith
  exact eq_neg_of_add_eq_zero_left hz

/-- The finite optimizer belongs to the original legal exact-head class. -/
theorem anchor_affine_mem_class {D : ℕ} (Y : ℕ) (d : Fin D → ℕ)
    (hd : ∀ i, Y < d i) (x : Fin D → ℝ) :
    (fun n => canonicalMobiusHead Y n + anchorSynthesis (Y + 1) d x n) ∈
      conditionalHeadClass Y := by
  refine ⟨(legalSeedSpan _).add_mem (canonicalMobiusHead_mem_legal Y)
    (anchorSynthesis_legal (Y + 1) d x (by omega)
      (fun i => by have := hd i; omega)), ?_⟩
  intro n hn hnY
  change canonicalMobiusHead Y n + anchorSynthesis (Y+1) d x n = 1
  rw [canonicalMobiusHead_exact Y n hn hnY]
  have hz : anchorSynthesis (Y + 1) d x n = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [divisorAnchorDirection_zero_head Y (Y + 1) (d i) n (by omega) (hd i) hnY,
      mul_zero]
  rw [hz, add_zero]

end RiemannResearch.RH.Pareto
