import RiemannResearch.RH.LegalExactHeadSubpolynomial
import RiemannResearch.RH.SquarefreeWindowSubpolynomial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Signed affine combinations of exact-head trials

Source: Christian Noack's Green--Pareto--Schur continuation, Sections 21--28,
and its requested strengthening, 6 October 2026.
The complete residual Gram form retains every mixed signed term. Individual
trial energy bounds are unnecessary; only the combined form is an arithmetic
provider. No arithmetic cancellation estimate is asserted here.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.AffineHeadTrials

/-- A finite signed affine trial; nonnegative coefficients are not required. -/
def affineTrial (s : Finset ℕ) (a : ℕ → ℝ)
    (u : ℕ → ThresholdHilbert) : ThresholdHilbert :=
  ∑ i ∈ s, a i • u i

/-- The complete residual Gram form, retaining diagonal and all mixed terms. -/
def residualGramQuadratic (s : Finset ℕ) (a : ℕ → ℝ)
    (u : ℕ → ThresholdHilbert) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, a i * a j *
    inner ℝ (hilbertOne - u i) (hilbertOne - u j)

theorem affine_residual_eq_sum (s : Finset ℕ) (a : ℕ → ℝ)
    (u : ℕ → ThresholdHilbert) (ha : ∑ i ∈ s, a i = 1) :
    hilbertOne - affineTrial s a u =
      ∑ i ∈ s, a i • (hilbertOne - u i) := by
  unfold affineTrial
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, ha, one_smul]

/-- The arithmetic Gram form is the actual combined residual energy. -/
theorem affine_residual_norm_sq_eq_gram
    (s : Finset ℕ) (a : ℕ → ℝ) (u : ℕ → ThresholdHilbert)
    (ha : ∑ i ∈ s, a i = 1) :
    ‖hilbertOne - affineTrial s a u‖ ^ 2 = residualGramQuadratic s a u := by
  rw [affine_residual_eq_sum s a u ha, ← real_inner_self_eq_norm_sq]
  unfold residualGramQuadratic
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    mul_assoc]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm (hilbertOne - u j) (hilbertOne - u i)]

theorem residualGramQuadratic_nonneg
    (s : Finset ℕ) (a : ℕ → ℝ) (u : ℕ → ThresholdHilbert)
    (ha : ∑ i ∈ s, a i = 1) :
    0 ≤ residualGramQuadratic s a u := by
  rw [← affine_residual_norm_sq_eq_gram s a u ha]
  exact sq_nonneg _

theorem affineTrial_mem_legalClosure (A : Set ℕ)
    (s : Finset ℕ) (a : ℕ → ℝ) (u : ℕ → ThresholdHilbert)
    (hu : ∀ i ∈ s, u i ∈ hilbertLegalClosure A) :
    affineTrial s a u ∈ hilbertLegalClosure A := by
  unfold affineTrial
  exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (hu i hi))

theorem affineTrial_exact_head (s : Finset ℕ) (a : ℕ → ℝ)
    (u : ℕ → ThresholdHilbert) (n : ℕ)
    (ha : ∑ i ∈ s, a i = 1)
    (hu : ∀ i ∈ s, ∀ k, 0 < k → k < n → hilbertSequence (u i) k = 1) :
    ∀ k, 0 < k → k < n → hilbertSequence (affineTrial s a u) k = 1 := by
  intro k hk hkn
  change (hilbertSequenceLinear (∑ i ∈ s, a i • u i)) k = 1
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i ∈ s, a i * hilbertSequence (u i) k) = ∑ i ∈ s, a i * 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hu i hi k hk hkn]
    _ = 1 := by simp only [mul_one, ha]

/-- Conditional actual RH reduction. The weights may have either sign,
constituent norms may grow arbitrarily, and the complete mixed Gram form
is the only growth provider. No cancellation estimate is asserted. -/
theorem riemannHypothesis_of_cofinal_affine_exact_head_gram_subpolynomial
    (A : Set ℕ) (hA : ∀ d ∈ A, 0 < d)
    (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    (u : ℕ → ℕ → ThresholdHilbert) (n : ℕ → ℕ)
    (hn : Tendsto (fun p => (n p : ℝ)) atTop atTop)
    (ha : ∀ p, ∑ i ∈ s p, a p i = 1)
    (hu : ∀ p i, i ∈ s p → u p i ∈ hilbertLegalClosure A)
    (hhead : ∀ p i, i ∈ s p → ∀ k, 0 < k → k < n p →
      hilbertSequence (u p i) k = 1)
    (hsub : Tendsto (fun p =>
      Real.log (1 + residualGramQuadratic (s p) (a p) (u p)) /
        Real.log (n p : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_legal_exact_head_subpolynomial A hA
    (fun p => affineTrial (s p) (a p) (u p)) n
    (fun p => residualGramQuadratic (s p) (a p) (u p)) hn
  · intro p
    exact affineTrial_mem_legalClosure A (s p) (a p) (u p) (hu p)
  · intro p
    exact affineTrial_exact_head (s p) (a p) (u p) (n p) (ha p) (hhead p)
  · intro p
    exact residualGramQuadratic_nonneg (s p) (a p) (u p) (ha p)
  · intro p
    rw [affine_residual_norm_sq_eq_gram (s p) (a p) (u p) (ha p)]
    linarith
  · exact hsub

/-- Actual Möbius specialization: legality and exact head matching are proved
from the existing arithmetic construction. Reciprocal-charge crossings and
individual trial-energy estimates are not required by this consumer.
The full mixed Gram growth hypothesis remains mathematically open. -/
theorem riemannHypothesis_of_cofinal_canonicalMobius_affine_gram_subpolynomial
    (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ)
    (Y : ℕ → ℕ → ℕ) (n : ℕ → ℕ)
    (hn : Tendsto (fun p => (n p : ℝ)) atTop atTop)
    (ha : ∀ p, ∑ i ∈ s p, a p i = 1)
    (hcut : ∀ p i, i ∈ s p → n p ≤ Y p i + 1)
    (hsub : Tendsto (fun p =>
      Real.log (1 + residualGramQuadratic (s p) (a p)
        (fun i => BalancedSquarefree.trialHilbert (Y p i))) /
      Real.log (n p : ℝ)) atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_affine_exact_head_gram_subpolynomial
    (Set.Ici 1) (fun d hd => lt_of_lt_of_le Nat.zero_lt_one hd)
    s a (fun p i => BalancedSquarefree.trialHilbert (Y p i)) n hn ha
  · intro p i hi
    exact BalancedSquarefree.trialHilbert_mem_legalClosure (Y p i)
  · intro p i hi k hk hkn
    exact BalancedSquarefree.trialHilbert_head (Y p i) k hk
      (lt_of_lt_of_le hkn (hcut p i hi))
  · exact hsub

end RiemannResearch.RH.Pareto.AffineHeadTrials
