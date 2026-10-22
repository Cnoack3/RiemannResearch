import RiemannResearch.Analysis.ProjectionTrialEnergy
import RiemannResearch.RH.IntegerDPPCertificateCutoffBridge
import RiemannResearch.RH.IntegerDPPAllSiteObstruction
import RiemannResearch.RH.PointTargetDilationSynthesis

/-!
# Finite-rank offsite budgets from first-site trial accuracy

Source: user-provided weighted-vacancy bridge continuation at commit c7c09ab
(2026-09-30). The proof reuses the existing exact residue dilation and finite
point-to-constant synthesis, then transfers accuracy to each physical site.
This is an independently assembled quantitative implication, with no claim
of mathematical novelty.

Full Gram energies, signed dilation mixed terms, and trial-fit squares appear
in the exact identities. The estimates specify the nonnegative fit squares
discarded and the mixed terms bounded. Every physical cutoff tail is retained.

The main bound assumes only finite rank enlargement and positive trial energy.
Arbitrarily small first-site vacancy remains the explicit Open arithmetic
provider. No RH, density, or uniform inverse-Gram estimate is assumed here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.FiniteHilbertGram
/-- Complete trial-to-projection square, before any upper bound. -/
theorem weightedVacancyTerm_eq_trial_energy (N i : ℕ)
    (y : ThresholdHilbert) (hy : y ∈ finiteSpace N) :
    weightedVacancyTerm N i = ‖paretoPointHilbert i - y‖ ^ 2 -
      ‖(finiteSpace N).starProjection (paretoPointHilbert i) - y‖ ^ 2 := by
  have h := RiemannResearch.Analysis.projection_trial_energy (finiteSpace N)
    (paretoPointHilbert i) y hy
  have hs := site_projection_complement (finiteSpace N) i
  change weightedVacancyTerm N i = _ at hs
  linarith


/-- All signed Gram mixed entries and the complete trial-fit square. -/
theorem weightedVacancyTerm_eq_fullGram_trial (N i : ℕ) (c : Fin N → ℝ) :
    weightedVacancyTerm N i =
      paretoWeight i -
      2 * (∑ d : Fin N, c d * inner ℝ (residueAtom d.val) (paretoPointHilbert i)) +
      (∑ d : Fin N, ∑ e : Fin N, c d * c e * fullGram N d e) -
      ‖(finiteSpace N).starProjection (paretoPointHilbert i) -
        Fintype.linearCombination ℝ (fun d : Fin N => residueAtom d.val) c‖ ^ 2 := by
  let y := Fintype.linearCombination ℝ (fun d : Fin N => residueAtom d.val) c
  have hy : y ∈ finiteSpace N := synthesis_mem (fun d : Fin N => residueAtom d.val) c
  rw [weightedVacancyTerm_eq_trial_energy N i y hy, norm_sub_sq_real]
  have hp : ‖paretoPointHilbert i‖ ^ 2 = paretoWeight i := by
    have h := site_projection_complement (⊥ : Submodule ℝ ThresholdHilbert) i
    simpa using h.symm
  have hi : inner ℝ (paretoPointHilbert i) y =
      ∑ d : Fin N, c d * inner ℝ (residueAtom d.val) (paretoPointHilbert i) := by
    rw [real_inner_comm]
    exact inner_synthesis_left (fun d : Fin N => residueAtom d.val) c _
  rw [hp, hi]
  have hg : ‖y‖ ^ 2 = ∑ d : Fin N, ∑ e : Fin N, c d * c e * fullGram N d e := by
    rw [gram_quadratic]
    simp_rw [gram_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    change c d * (inner ℝ (residueAtom d.val) (residueAtom e.val) * c e) =
      c d * c e * inner ℝ (residueAtom d.val) (residueAtom e.val)
    ring
  rw [hg]


/-- Exact half-ceiling minus the actual full inverse-Gram occupation trace. -/
theorem offsiteWeightedVacancyCutoff_eq_gram_trace (N M : ℕ) :
    offsiteWeightedVacancyPrefix N M + 1 / (((M + 1 : ℕ) : ℝ) + 1) =
      1 / 2 -
        Matrix.trace (Matrix.diagonal (fun i : Fin M => paretoWeight (i.val + 1)) *
          (windowFeatures N M (fun i => i.val + 1) * (fullGram N)⁻¹ *
            (windowFeatures N M (fun i => i.val + 1)).transpose)) := by
  have ht :
      Matrix.trace (Matrix.diagonal (fun i : Fin M => paretoWeight (i.val + 1)) *
        Matrix.of (fun i j : Fin M => integerKernel N (i.val + 1) (j.val + 1))) =
      ∑ i ∈ Finset.range M, paretoWeight (i + 1) * integerKernel N (i + 1) (i + 1) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Matrix.of_apply]
    exact Fin.sum_univ_eq_sum_range (fun i : ℕ =>
      paretoWeight (i + 1) * integerKernel N (i + 1) (i + 1)) M
  have hw : (∑ i ∈ Finset.range M, paretoWeight (i + 1)) +
      1 / (((M + 1 : ℕ) : ℝ) + 1) = 1 / 2 := by
    have h := paretoWeight_partial_sum (M + 1)
    rw [Finset.sum_range_succ'] at h
    have h0 : paretoWeight 0 = (1 / 2 : ℝ) := by norm_num [paretoWeight]
    rw [h0] at h
    linarith
  rw [← integerKernel_window_matrix, ht]
  unfold offsiteWeightedVacancyPrefix weightedVacancyTerm
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]
  linarith


private theorem norm_unscaled_dilation (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    ‖unscaledResidueDilation m hm f‖ = Real.sqrt (1 / (m : ℝ)) * ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [unscaledResidueDilation_norm_sq, mul_pow, Real.sq_sqrt (by positivity)]
  ring
/-- The legal trial for a physical point, obtained by adjacent floor dilations. -/
def siteDilationTrial (i : ℕ) (f : ThresholdHilbert) : ThresholdHilbert :=
  unscaledResidueDilation (i + 1) (by omega) f -
    unscaledResidueDilation (i + 2) (by omega) f


theorem siteDilationTrial_mem (n N i : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace n) (hN : (i + 2) * (n + 1) ≤ N + 1) :
    siteDilationTrial i f ∈ finiteSpace N := by
  have hmem (m : ℕ) (hm : 2 ≤ m) (hb : m * (n + 1) ≤ N + 1) :
      unscaledResidueDilation m (by omega) f ∈ finiteSpace N := by
    apply walkSpan_mono residueAtom id (by omega : m * (n + 1) - 1 ≤ N)
    exact unscaledResidueDilation_mem_finiteSpace n m hm f hf
  apply Submodule.sub_mem
  · by_cases hi : i = 0
    · subst i
      have hn : n ≤ N := by omega
      have he : unscaledResidueDilation 1 (by omega) f = f := by
        apply hilbertSequence_injective
        funext k
        rw [unscaledResidueDilation_sequence]
        simp only [Nat.div_one]
      simpa only [he] using (walkSpan_mono residueAtom id hn) hf
    · apply hmem (i + 1) (by omega)
      exact (Nat.mul_le_mul_right (n + 1) (by omega : i + 1 ≤ i + 2)).trans hN
  · exact hmem (i + 2) (by omega) hN

def siteDilationFactor (i : ℕ) : ℝ :=
  Real.sqrt (1 / ((i + 1 : ℕ) : ℝ)) + Real.sqrt (1 / ((i + 2 : ℕ) : ℝ))

/-- Exact signed error; no norm estimate has been taken. -/
theorem siteDilationTrial_error_exact (i : ℕ) (f : ThresholdHilbert) :
    paretoPointHilbert i - siteDilationTrial i f =
      siteDilationTrial i (hilbertOne - f) := by
  have happ (m : ℕ) (hm : 0 < m) :
      unscaledResidueDilation m hm hilbertOne =
        ((m : ℝ)⁻¹) • hilbertDilation m hm hilbertOne := by
    apply hilbertSequence_injective
    funext k
    rw [unscaledResidueDilation_sequence, hilbertSequence_smul, hilbertDilation_sequence]
    simp only [Pi.smul_apply, smul_eq_mul, dilation]
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
  have ht : paretoPointHilbert i = siteDilationTrial i hilbertOne := by
    rw [paretoPoint_eq_scaled_dilation_difference]
    unfold siteDilationTrial
    rw [happ, happ]
  rw [ht]
  unfold siteDilationTrial
  rw [map_sub, map_sub]
  abel

/-- Both the signed mixed dilation energy and the projection-fit square remain. -/
theorem weightedVacancyTerm_eq_dilation_energy (n N i : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace n) (hN : (i + 2) * (n + 1) ≤ N + 1) :
    weightedVacancyTerm N i =
      (1 / ((i + 1 : ℕ) : ℝ) + 1 / ((i + 2 : ℕ) : ℝ)) * ‖hilbertOne - f‖ ^ 2 -
      2 * inner ℝ
        (unscaledResidueDilation (i + 1) (by omega) (hilbertOne - f))
        (unscaledResidueDilation (i + 2) (by omega) (hilbertOne - f)) -
      ‖(finiteSpace N).starProjection (paretoPointHilbert i) - siteDilationTrial i f‖ ^ 2 := by
  rw [weightedVacancyTerm_eq_trial_energy N i _ (siteDilationTrial_mem n N i f hf hN),
    siteDilationTrial_error_exact]
  unfold siteDilationTrial
  rw [norm_sub_sq_real, unscaledResidueDilation_norm_sq, unscaledResidueDilation_norm_sq]
  ring


theorem siteDilationTrial_error_bound (i : ℕ) (f : ThresholdHilbert) :
    ‖paretoPointHilbert i - siteDilationTrial i f‖ ≤
      siteDilationFactor i * ‖hilbertOne - f‖ := by
  rw [siteDilationTrial_error_exact]
  exact (norm_sub_le _ _).trans_eq (by
    rw [norm_unscaled_dilation, norm_unscaled_dilation]
    unfold siteDilationFactor
    ring)

/-- Estimate the recorded mixed energy and discard its nonnegative fit square. -/
theorem weightedVacancyTerm_le_dilation_trial (n N i : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace n) (hN : (i + 2) * (n + 1) ≤ N + 1) :
    weightedVacancyTerm N i ≤ siteDilationFactor i ^ 2 * ‖hilbertOne - f‖ ^ 2 := by
  rw [weightedVacancyTerm_eq_trial_energy N i _ (siteDilationTrial_mem n N i f hf hN)]
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (by unfold siteDilationFactor; positivity) (norm_nonneg _))).mpr
      (siteDilationTrial_error_bound i f)
  rw [mul_pow] at hs
  nlinarith [sq_nonneg ‖(finiteSpace N).starProjection (paretoPointHilbert i) -
    siteDilationTrial i f‖]

/-- Explicit finite geometric cost for physical sites 2,...,M+1. -/
def offsiteDilationFactor (M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range M, siteDilationFactor (i + 1) ^ 2

theorem offsiteDilationFactor_le_reciprocal_sum (M : ℕ) :
    offsiteDilationFactor M ≤
      2 * ∑ i ∈ Finset.range M,
        (1 / ((i + 2 : ℕ) : ℝ) + 1 / ((i + 3 : ℕ) : ℝ)) := by
  unfold offsiteDilationFactor
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  unfold siteDilationFactor
  have h1 : Real.sqrt (1 / ((i + 1 + 1 : ℕ) : ℝ)) ^ 2 =
      1 / ((i + 1 + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt (1 / ((i + 1 + 2 : ℕ) : ℝ)) ^ 2 =
      1 / ((i + 1 + 2 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have hs := sq_nonneg (Real.sqrt (1 / ((i + 1 + 1 : ℕ) : ℝ)) -
    Real.sqrt (1 / ((i + 1 + 2 : ℕ) : ℝ)))
  norm_num only [Nat.add_assoc] at *
  nlinarith

/-- Sum of complete site identities with every trial-fit square retained. -/
theorem offsiteWeightedVacancyPrefix_eq_trial_squares (N M : ℕ)
    (y : ℕ → ThresholdHilbert) (hy : ∀ i < M, y i ∈ finiteSpace N) :
    offsiteWeightedVacancyPrefix N M =
      ∑ i ∈ Finset.range M,
        (‖paretoPointHilbert (i + 1) - y i‖ ^ 2 -
          ‖(finiteSpace N).starProjection (paretoPointHilbert (i + 1)) - y i‖ ^ 2) := by
  apply Finset.sum_congr rfl
  intro i hi
  exact weightedVacancyTerm_eq_trial_energy N (i + 1) _ (hy i (Finset.mem_range.mp hi))


/-- Transfer a first-site trial through existing finite geometric synthesis. -/
theorem offsiteWeightedVacancyPrefix_le_point_synthesis (n N M K : ℕ)
    (hn : 0 < n) (hN : (M + 2) * (2 ^ K * (n + 1)) ≤ N + 1)
    (y : ThresholdHilbert) (hy : y ∈ finiteSpace n) :
    offsiteWeightedVacancyPrefix N M ≤
      offsiteDilationFactor M *
        (dyadicContraction ^ (K + 1) +
          (1 - dyadicContraction ^ (K + 1)) / (1 - dyadicContraction) *
            ‖paretoPointHilbert 0 - y‖) ^ 2 := by
  have hy' : y ∈ finiteSpace ((n + 1) - 1) := by simpa using hy
  have hf := pointDilationSynthesis_mem (n + 1) (by omega) y hy' K
  have hs : offsiteWeightedVacancyPrefix N M ≤
      offsiteDilationFactor M * ‖hilbertOne - pointDilationSynthesis y (K + 1)‖ ^ 2 := by
    unfold offsiteWeightedVacancyPrefix offsiteDilationFactor
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hiM := Finset.mem_range.mp hi
    apply weightedVacancyTerm_le_dilation_trial (2 ^ K * (n + 1) - 1) N (i + 1) _ hf
    have hpos : 0 < 2 ^ K * (n + 1) := by positivity
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ K * (n + 1))]
    exact (Nat.mul_le_mul_right _ (by omega : i + 1 + 2 ≤ M + 2)).trans hN
  have hb := pointDilationSynthesis_error y (K + 1)
  have hB : 0 ≤ dyadicContraction ^ (K + 1) +
      (1 - dyadicContraction ^ (K + 1)) / (1 - dyadicContraction) * ‖paretoPointHilbert 0 - y‖ :=
    (norm_nonneg _).trans hb
  exact hs.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) hB).mpr hb) (by
      unfold offsiteDilationFactor
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
/-- The bridge's square slack makes the trial expression exactly the vacancy. -/
theorem first_site_error_eq_trial_budget (n : ℕ) (c : Fin n → ℝ)
    (hE : 0 < finiteTrialEnergy n c) :
    vacancy n / 2 =
      finiteTrialEnergy n c /
        (finiteTrialSource n c ^ 2 + 2 * finiteTrialEnergy n c) -
      finiteTrialVacancySlack n c := by
  have h := weightedVacancyCutoff_eq_trial_split n 0 c hE
  rw [weightedVacancyPrefix_first_site_split] at h
  linarith

theorem first_site_projection_error_norm (n : ℕ) :
    ‖paretoPointHilbert 0 - (finiteSpace n).starProjection (paretoPointHilbert 0)‖ =
      Real.sqrt (vacancy n / 2) := by
  have he := first_site_projection_complement (finiteSpace n)
  change 1 - integerKernel n 0 0 = _ at he
  rw [← vacancy_eq_kernel_complement] at he
  change vacancy n = 2 * ‖paretoPointHilbert 0 -
    (finiteSpace n).starProjection (paretoPointHilbert 0)‖ ^ 2 at he
  have he' : vacancy n / 2 =
      ‖paretoPointHilbert 0 - (finiteSpace n).starProjection (paretoPointHilbert 0)‖ ^ 2 := by
    linarith
  rw [he', Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]


/-- Rank-dependent offsite bound, with the original finite trial's square slack. -/
theorem offsiteWeightedVacancyPrefix_le_rank_trial_budget (n N M K : ℕ)
    (hN : (M + 2) * (2 ^ K * (n + 1)) ≤ N + 1)
    (c : Fin n → ℝ) (hE : 0 < finiteTrialEnergy n c) :
    offsiteWeightedVacancyPrefix N M ≤
      offsiteDilationFactor M *
        (dyadicContraction ^ (K + 1) +
          (1 - dyadicContraction ^ (K + 1)) / (1 - dyadicContraction) * Real.sqrt
          (finiteTrialEnergy n c /
            (finiteTrialSource n c ^ 2 + 2 * finiteTrialEnergy n c) -
            finiteTrialVacancySlack n c)) ^ 2 := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    simp [finiteTrialEnergy, Fintype.linearCombination_apply] at hE
  have h := offsiteWeightedVacancyPrefix_le_point_synthesis n N M K hn hN
    ((finiteSpace n).starProjection (paretoPointHilbert 0))
    ((finiteSpace n).starProjection_apply_mem _)
  rw [first_site_projection_error_norm, first_site_error_eq_trial_budget n c hE] at h
  exact h

/-- Complete finite physical cutoff, including its first site and tail. -/
theorem weightedVacancyCutoff_le_rank_trial_budget (n N M K : ℕ)
    (hN : (M + 2) * (2 ^ K * (n + 1)) ≤ N + 1)
    (c : Fin n → ℝ) (hE : 0 < finiteTrialEnergy n c) :
    weightedVacancyPrefix N (M + 1) + 1 / (((M + 1 : ℕ) : ℝ) + 1) ≤
      (finiteTrialEnergy n c /
        (finiteTrialSource n c ^ 2 + 2 * finiteTrialEnergy n c) -
        finiteTrialVacancySlack n c) +
      offsiteDilationFactor M *
        (dyadicContraction ^ (K + 1) +
          (1 - dyadicContraction ^ (K + 1)) / (1 - dyadicContraction) * Real.sqrt
          (finiteTrialEnergy n c /
            (finiteTrialSource n c ^ 2 + 2 * finiteTrialEnergy n c) -
            finiteTrialVacancySlack n c)) ^ 2 +
      1 / (((M + 1 : ℕ) : ℝ) + 1) := by
  have hn : n ≤ N := by
    have h1 := Nat.le_mul_of_pos_left (n + 1) (by positivity : 0 < 2 ^ K)
    have h2 := Nat.le_mul_of_pos_left (2 ^ K * (n + 1)) (by omega : 0 < M + 2)
    omega
  have hv := vacancy_antitone hn
  have ho := offsiteWeightedVacancyPrefix_le_rank_trial_budget n N M K hN c hE
  rw [weightedVacancyPrefix_first_site_split]
  rw [← first_site_error_eq_trial_budget n c hE] at ho ⊢
  linarith

end RiemannResearch.RH.Pareto.IntegerDPP
