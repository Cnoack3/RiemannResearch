import RiemannResearch.Analysis.BoundedMomentRepair
import RiemannResearch.Analysis.BoundedMomentAverages
import RiemannResearch.RH.ParetoLegalApproximationClosure

/-!
# Conditional Pareto repair from bounded moment matching

Source: user-provided Ramanujan–Laguerre continuation, September 11, 2026.
The original finite legal packets are combined with finite convex weights.
Their exact Pareto mean and full signed error are preserved in the calculation.

This is a conditional research reduction. A complete family of actual testing
vectors, exact moment matching for actual legal packets, and a uniform bound on
their actual Pareto error are inputs. In particular, this module neither builds
Laguerre testing vectors nor proves the candidate optimizer's uniform bound.
The conditional RH conclusion uses the existing proved legal-closure bridge.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Finite mixtures of bounded, progressively moment-matched legal packets
achieve arbitrarily small actual Pareto error, with exact mean one. -/
theorem exists_legal_mean_one_convex_mixture_of_bounded_moments
    (A : Set ℕ) (b : ℕ → ThresholdHilbert)
    (htotal : (Submodule.span ℝ (Set.range b)).topologicalClosure = ⊤)
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ n, F n ∈ hilbertLegalSubspace A)
    (hmean : ∀ n, paretoMean (hilbertSequence (F n)) = 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, ‖hilbertOne - F n‖ ^ 2 ≤ B)
    (hmatch : ∀ n k, k ≤ n →
      inner ℝ (b k) (hilbertOne - F n) = 0)
    (N : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → ℝ) (j : κ → ℕ),
      (∀ k, 0 ≤ a k) ∧ (∑ k, a k) = 1 ∧
      (∀ k, N ≤ j k) ∧
      (∑ k, a k • F (j k)) ∈ hilbertLegalSubspace A ∧
      paretoMean (hilbertSequence (∑ k, a k • F (j k))) = 1 ∧
      paretoError (hilbertSequence (∑ k, a k • F (j k))) < η ^ 2 := by
  classical
  obtain ⟨κ, hκ, a, j, ha, haone, hj, hn⟩ :=
    RiemannResearch.Analysis.exists_convex_weights_small_of_bounded_matched_moments
      b htotal (fun n => hilbertOne - F n) hB hbound hmatch N hη
  let := hκ
  have he : (∑ k, a k • (hilbertOne - F (j k))) =
      hilbertOne - ∑ k, a k • F (j k) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, haone, one_smul]
  rw [he] at hn
  refine ⟨κ, hκ, a, j, ha, haone, hj, ?_, ?_, ?_⟩
  · exact (hilbertLegalSubspace A).sum_mem
      (fun k _ => (hilbertLegalSubspace A).smul_mem (a k) (hlegal (j k)))
  · rw [← hilbert_inner_one, sum_inner]
    simp only [real_inner_smul_left, hilbert_inner_one, hmean, mul_one]
    exact haone
  · rw [← hilbertOne_sub_norm_sq_eq_paretoError]
    nlinarith [norm_nonneg (hilbertOne - ∑ k, a k • F (j k))]

/-- The above hypotheses provide genuine finite legal approximation in the
original physical sequence space, rather than only an abstract weak limit. -/
theorem hilbertOne_mem_legalClosure_of_bounded_moments
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (b : ℕ → ThresholdHilbert)
    (htotal : (Submodule.span ℝ (Set.range b)).topologicalClosure = ⊤)
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ n, F n ∈ hilbertLegalSubspace A)
    (hmean : ∀ n, paretoMean (hilbertSequence (F n)) = 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, ‖hilbertOne - F n‖ ^ 2 ≤ B)
    (hmatch : ∀ n k, k ≤ n →
      inner ℝ (b k) (hilbertOne - F n) = 0) :
    hilbertOne ∈ hilbertLegalClosure A := by
  apply (hilbertOne_mem_legalClosure_iff_paretoError A hA).mpr
  intro ε hε
  obtain ⟨κ, hκ, a, j, _, _, _, hlegal', _, herr⟩ :=
    exists_legal_mean_one_convex_mixture_of_bounded_moments A b htotal
      F hlegal hmean hB hbound hmatch 0 (Real.sqrt_pos.mpr hε)
  let := hκ
  refine ⟨hilbertSequence (∑ k, a k • F (j k)), hlegal', ?_⟩
  simpa only [Real.sq_sqrt hε.le] using herr

/-- Conditional research reduction to actual RH. Dense testing vectors, exact
matching, and uniformly bounded actual legal errors are substantive inputs. -/
theorem riemannHypothesis_of_bounded_legal_moments
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (b : ℕ → ThresholdHilbert)
    (htotal : (Submodule.span ℝ (Set.range b)).topologicalClosure = ⊤)
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ n, F n ∈ hilbertLegalSubspace A)
    (hmean : ∀ n, paretoMean (hilbertSequence (F n)) = 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ n, ‖hilbertOne - F n‖ ^ 2 ≤ B)
    (hmatch : ∀ n k, k ≤ n →
      inner ℝ (b k) (hilbertOne - F n) = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_hilbertOne_mem_legalClosure A hA
    (hilbertOne_mem_legalClosure_of_bounded_moments A hA b htotal
      F hlegal hmean hB hbound hmatch)

/-- Actual finite legal mean-one equal-weight averages satisfy the quantitative
bound from the page. Weak nullity and the uniform actual error bound are inputs;
neither is replaced by finite numerical observations. -/
theorem exists_strictMono_legal_mean_one_average_error_bound
    (A : Set ℕ) (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ n, F n ∈ hilbertLegalSubspace A)
    (hmean : ∀ n, paretoMean (hilbertSequence (F n)) = 1)
    {B : ℝ} (hbound : ∀ n, ‖hilbertOne - F n‖ ^ 2 ≤ B)
    (hweak : ∀ x : ThresholdHilbert,
      Filter.Tendsto (fun n => inner ℝ x (hilbertOne - F n))
        Filter.atTop (nhds 0)) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ ∀ m : ℕ, 0 < m →
      (((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, F (q i))) ∈
          hilbertLegalSubspace A ∧
      paretoMean (hilbertSequence
        (((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, F (q i)))) = 1 ∧
      paretoError (hilbertSequence
        (((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, F (q i)))) ≤
          B / m + 4 / (m : ℝ) ^ 2 := by
  classical
  obtain ⟨q, hq, havg⟩ :=
    RiemannResearch.Analysis.exists_strictMono_average_norm_sq_bound
      (fun n => hilbertOne - F n) hbound hweak
  refine ⟨q, hq, ?_⟩
  intro m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hconst : (∑ _i ∈ Finset.range m, hilbertOne) =
      (m : ℝ) • hilbertOne := by
    simp only [Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul]
  have he : ((m : ℝ)⁻¹) •
        (∑ i ∈ Finset.range m, (hilbertOne - F (q i))) =
      hilbertOne - ((m : ℝ)⁻¹) •
        (∑ i ∈ Finset.range m, F (q i)) := by
    rw [Finset.sum_sub_distrib, hconst, smul_sub, smul_smul,
      inv_mul_cancel₀ hm', one_smul]
  refine ⟨?_, ?_, ?_⟩
  · exact (hilbertLegalSubspace A).smul_mem _ <|
      (hilbertLegalSubspace A).sum_mem
        (fun i _ => hlegal (q i))
  · rw [← hilbert_inner_one, real_inner_smul_left, sum_inner]
    simp only [hilbert_inner_one, hmean, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hm'
  · rw [← hilbertOne_sub_norm_sq_eq_paretoError]
    have h := havg m hm
    rwa [he] at h

end
end RiemannResearch.RH.Pareto
