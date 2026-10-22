import RiemannResearch.RH.MultiRangeTruncatedGram
import RiemannResearch.LinearAlgebra.FiniteConstrainedMatrixInverse
import RiemannResearch.RH.ConditionalResidueGram

/-! The rational inverse coefficients minimize the actual finite prefix objective.
Source: Section 7 of RH_Multi_Range_Divisor_Corrections_2026-09-18.md.
The arithmetic horizon theorem discharges positive definiteness for anchors. -/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open Probability.ConditionalIID Analysis.Cesaro Analysis.FiniteSignedQuadratic
open RiemannResearch.LinearAlgebra.FiniteConstrainedMatrix

theorem conditionalMeanPrefix_add (F G : ℕ → ℝ) (N : ℕ) :
    conditionalMeanPrefix (fun n => F n + G n) N =
      conditionalMeanPrefix F N + 2 * conditionalMeanPrefixInner F G N +
        conditionalMeanPrefix G N := by
  have he (t : ℕ) : cesaro (fun n => F n + G n) t = cesaro F t + cesaro G t := by
    simpa only [one_mul] using cesaro_add_mul F G 1 t
  unfold conditionalMeanPrefix conditionalMeanPrefixInner
  simp_rw [he]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem conditionalMeanPrefixInner_synthesis {D : ℕ} (F : ℕ → ℝ)
    (U : Fin D → ℕ → ℝ) (x : Fin D → ℝ) (N : ℕ) :
    conditionalMeanPrefixInner F (fun n => ∑ i, x i * U i n) N =
      ∑ i, x i * conditionalMeanPrefixInner F (U i) N := by
  unfold conditionalMeanPrefixInner
  simp_rw [cesaro_finsetCombination, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem prefixMeanOptimizer_minimizes {D : ℕ} (F : ℕ → ℝ)
    (U : Fin D → ℕ → ℝ) (N : ℕ) (hG : (prefixMeanGram U N).PosDef)
    (x : Fin D → ℝ) :
    conditionalMeanPrefix (fun n => F n + ∑ i, prefixMeanOptimizer F U N i * U i n) N ≤
      conditionalMeanPrefix (fun n => F n + ∑ i, x i * U i n) N := by
  let G := prefixMeanGram U N
  let h : Fin D → ℝ := fun i => conditionalMeanPrefixInner F (U i) N
  let z := (gramEquiv G hG).symm h
  have hz : G.mulVec z = h := (gramEquiv G hG).apply_symm_apply h
  have hx : prefixMeanOptimizer F U N = -z := by
    dsimp [z]
    rw [gramEquiv_symm_eq_inv_mulVec]
    rfl
  have hsym (i j : Fin D) : G i j = G j i := by
    unfold G prefixMeanGram conditionalMeanPrefixInner
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have he (v : Fin D → ℝ) :
      conditionalMeanPrefix (fun n => F n + ∑ i, v i * U i n) N =
      conditionalMeanPrefix F N - ∑ i, z i * h i + quadratic G (v+z) := by
    rw [conditionalMeanPrefix_add, conditionalMeanPrefixInner_synthesis,
      ← prefixMeanGram_quadratic]
    exact schur_completion G hsym h z v hz _
  rw [he,he,hx]
  simp only [neg_add_cancel,quadratic,Pi.zero_apply,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
  have hn : 0 ≤ quadratic G (x+z) := by
    rw [prefixMeanGram_quadratic]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (conditionalWeight_pos _).le (sq_nonneg _))
  exact le_add_of_nonneg_right hn

/-- For every horizon reaching all divisors, the displayed prefix inverse
really is a minimizer. It uses one coefficient vector for all mean indices. -/
theorem anchorPrefixOptimizer_minimizes {D : ℕ} (A : ℕ) (d : Fin D → ℕ)
    (hd : ∀ i, 1 < d i ∧ d i ≠ A) (hinj : Function.Injective d)
    (F : ℕ → ℝ) (N : ℕ) (hN : ∀ i, d i ≤ N) (x : Fin D → ℝ) :
    conditionalMeanPrefix (fun n => F n + anchorSynthesis A d
      (prefixMeanOptimizer F (fun i => divisorAnchorDirection A (d i)) N) n) N ≤
    conditionalMeanPrefix (fun n => F n + anchorSynthesis A d x n) N :=
  prefixMeanOptimizer_minimizes F _ N (anchor_prefixGram_posDef A d hd hinj N hN) x

end RiemannResearch.RH.Pareto
