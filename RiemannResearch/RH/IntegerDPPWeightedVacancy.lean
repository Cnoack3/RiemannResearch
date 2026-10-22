import RiemannResearch.RH.IntegerDPPHistoricalTargets
import RiemannResearch.RH.IntegerDPPCoupling
import RiemannResearch.RH.IntegerDPPGramDeterminant
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Pareto-weighted vacancy and certified physical cutoffs

Source: user-provided DPP coupling/Mellin/Fredholm/cutoff argument,
RH_DPP_Coupling_Mellin_Fredholm_and_Cutoff_Bounds_2026-09-21.md,
Sections 6--8. The proofs here concern the actual counting-coordinate
arithmetic kernel and retain the exact infinite tail before bounding it.

The weighted mass converges without RH. Its vanishing is equivalent to
density of the residue span. Arbitrarily small finite cutoff certificates
would imply Mathlib's RiemannHypothesis, but no provider of those
certificates is asserted. No infinite-dimensional operator Fredholm
identification, full negative association, or spatial transport provider
is assumed by these results.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization HistoricalTargets

private theorem limiting_diagonal_bounds (i : ℕ) :
    0 ≤ limitingKernel i i ∧ limitingKernel i i ≤ 1 :=
  RiemannResearch.Analysis.ProjectionDPP.diagonal_bounds
    closedSpace countingBasis i (countingBasis_norm_sq i)

/-- Counting coordinate i represents the physical site i+1. -/
def weightedVacancyTerm (N i : ℕ) : ℝ :=
  paretoWeight i * (1 - integerKernel N i i)

def finiteWeightedVacancyMass (N : ℕ) : ℝ := ∑' i, weightedVacancyTerm N i

def weightedVacancyPrefix (N M : ℕ) : ℝ :=
  ∑ i ∈ Finset.range M, weightedVacancyTerm N i

def weightedVacancyTail (N M : ℕ) : ℝ :=
  ∑' i, weightedVacancyTerm N (i + M)

theorem weightedVacancyTerm_bounds (N i : ℕ) :
    0 ≤ weightedVacancyTerm N i ∧ weightedVacancyTerm N i ≤ paretoWeight i := by
  have hk := integerKernel_diagonal_bounds N i
  have hw := (paretoWeight_pos i).le
  constructor
  · exact mul_nonneg hw (sub_nonneg.mpr hk.2)
  · unfold weightedVacancyTerm
    nlinarith [mul_nonneg hw hk.1]

theorem weightedVacancyTerm_summable (N : ℕ) : Summable (weightedVacancyTerm N) :=
  Summable.of_nonneg_of_le (fun i => (weightedVacancyTerm_bounds N i).1)
    (fun i => (weightedVacancyTerm_bounds N i).2) paretoWeight_hasSum.summable

theorem weightedVacancyMass_summable :
    Summable (fun i => paretoWeight i * (1 - limitingKernel i i)) := by
  apply Summable.of_nonneg_of_le _ _ paretoWeight_hasSum.summable
  · intro i
    exact mul_nonneg (paretoWeight_pos i).le
      (sub_nonneg.mpr (limiting_diagonal_bounds i).2)
  · intro i
    nlinarith [mul_nonneg (paretoWeight_pos i).le (limiting_diagonal_bounds i).1]

/-- Complete equality: the unestimated tail is retained. -/
theorem finiteWeightedVacancyMass_exact (N M : ℕ) :
    finiteWeightedVacancyMass N =
      weightedVacancyPrefix N M + weightedVacancyTail N M := by
  exact ((weightedVacancyTerm_summable N).sum_add_tsum_nat_add M).symm

private theorem weight_tail_exact (M : ℕ) :
    (∑' i, paretoWeight (i + M)) = 1 / ((M : ℝ) + 1) := by
  have h := paretoWeight_hasSum.summable.sum_add_tsum_nat_add M
  rw [paretoWeight_partial_sum, paretoWeight_hasSum.tsum_eq] at h
  linarith

theorem weightedVacancyTail_bounds (N M : ℕ) :
    0 ≤ weightedVacancyTail N M ∧
      weightedVacancyTail N M ≤ 1 / ((M : ℝ) + 1) := by
  constructor
  · exact tsum_nonneg (fun i => (weightedVacancyTerm_bounds N (i + M)).1)
  · unfold weightedVacancyTail
    rw [← weight_tail_exact M]
    exact Summable.tsum_le_tsum
      (fun i => (weightedVacancyTerm_bounds N (i + M)).2)
      ((summable_nat_add_iff M).mpr (weightedVacancyTerm_summable N))
      ((summable_nat_add_iff M).mpr paretoWeight_hasSum.summable)

theorem finiteWeightedVacancyMass_cutoff_bounds (N M : ℕ) :
    weightedVacancyPrefix N M ≤ finiteWeightedVacancyMass N ∧
      finiteWeightedVacancyMass N ≤
        weightedVacancyPrefix N M + 1 / ((M : ℝ) + 1) := by
  rw [finiteWeightedVacancyMass_exact N M]
  have h := weightedVacancyTail_bounds N M
  constructor <;> linarith

theorem finiteWeightedVacancyMass_tendsto :
    Tendsto finiteWeightedVacancyMass atTop (𝓝 weightedVacancyMass) := by
  apply tendsto_tsum_of_dominated_convergence paretoWeight_hasSum.summable
  · intro i
    exact tendsto_const_nhds.mul (tendsto_const_nhds.sub (integerKernel_tendsto i i))
  · apply Eventually.of_forall
    intro N i
    rw [Real.norm_eq_abs, abs_of_nonneg (weightedVacancyTerm_bounds N i).1]
    exact (weightedVacancyTerm_bounds N i).2

theorem finiteWeightedVacancyMass_bounds (N : ℕ) :
    0 < finiteWeightedVacancyMass N ∧ finiteWeightedVacancyMass N ≤ 1 := by
  have hl := (weightedVacancyTerm_summable N).le_tsum 0
    (fun i _ => (weightedVacancyTerm_bounds N i).1)
  have he : weightedVacancyTerm N 0 = vacancy N / 2 := by
    simp [weightedVacancyTerm, vacancy_eq_kernel_complement, paretoWeight]
    ring
  constructor
  · rw [he] at hl
    exact lt_of_lt_of_le (div_pos (vacancy_pos N) (by norm_num)) hl
  · exact (Summable.tsum_le_tsum (fun i => (weightedVacancyTerm_bounds N i).2)
      (weightedVacancyTerm_summable N) paretoWeight_hasSum.summable).trans_eq
      paretoWeight_hasSum.tsum_eq

theorem weightedVacancyMass_bounds : 0 ≤ weightedVacancyMass ∧ weightedVacancyMass ≤ 1 := by
  constructor
  · exact tsum_nonneg (fun i => mul_nonneg (paretoWeight_pos i).le
      (sub_nonneg.mpr (limiting_diagonal_bounds i).2))
  · apply (Summable.tsum_le_tsum _ weightedVacancyMass_summable
      paretoWeight_hasSum.summable).trans_eq paretoWeight_hasSum.tsum_eq
    intro i
    nlinarith [mul_nonneg (paretoWeight_pos i).le (limiting_diagonal_bounds i).1]

theorem limitingWeightedVacancyMass_first_site_lower :
    limitingVacancy / 2 ≤ weightedVacancyMass := by
  have h := weightedVacancyMass_summable.le_tsum 0
    (fun i _ => mul_nonneg (paretoWeight_pos i).le
      (sub_nonneg.mpr (limiting_diagonal_bounds i).2))
  simpa [weightedVacancyMass, paretoWeight, limitingVacancy_eq_kernel_complement,
    div_eq_mul_inv, mul_comm] using h

theorem weightedVacancyMass_zero_iff_top :
    weightedVacancyMass = 0 ↔ closedSpace = ⊤ := by
  constructor
  · intro h
    apply limitingVacancy_zero_iff_top.mp
    have hl := limitingWeightedVacancyMass_first_site_lower
    have hn := limitingVacancy_nonneg
    rw [h] at hl
    linarith
  · intro h
    unfold weightedVacancyMass
    have hk (i : ℕ) : limitingKernel i i = 1 :=
      (limitingKernel_diagonal_one_iff i).mpr (by rw [h]; trivial)
    simp_rw [hk, sub_self, mul_zero]
    simp

/-- Operator order is used only through its actual one-site compression. -/
theorem weightedVacancyMass_le_finite (N : ℕ) :
    weightedVacancyMass ≤ finiteWeightedVacancyMass N := by
  apply Summable.tsum_le_tsum _ weightedVacancyMass_summable
    (weightedVacancyTerm_summable N)
  intro i
  have h : 0 ≤ limitingKernel i i - integerKernel N i i := by
    exact (integerKernel_le_limitingKernel N 1 (fun _ => i)).diag_nonneg
      (i := (0 : Fin 1))
  unfold weightedVacancyTerm
  nlinarith [mul_nonneg (paretoWeight_pos i).le h]

theorem finiteWeightedVacancyMass_antitone : Antitone finiteWeightedVacancyMass := by
  intro N L hNL
  apply Summable.tsum_le_tsum _ (weightedVacancyTerm_summable L)
    (weightedVacancyTerm_summable N)
  intro i
  have h : 0 ≤ integerKernel L i i - integerKernel N i i := by
    exact (integerKernel_principal_monotone N L hNL 1 (fun _ => i)).diag_nonneg
      (i := (0 : Fin 1))
  unfold weightedVacancyTerm
  nlinarith [mul_nonneg (paretoWeight_pos i).le h]

theorem finiteWeightedVacancyMass_tendsto_zero_iff_top :
    Tendsto finiteWeightedVacancyMass atTop (𝓝 0) ↔ closedSpace = ⊤ := by
  constructor
  · intro h
    exact weightedVacancyMass_zero_iff_top.mp
      (tendsto_nhds_unique finiteWeightedVacancyMass_tendsto h)
  · intro h
    have hz := weightedVacancyMass_zero_iff_top.mpr h
    simpa only [hz] using finiteWeightedVacancyMass_tendsto

theorem weightedVacancyMass_pos_of_not_RH (h : ¬ RiemannHypothesis) :
    0 < weightedVacancyMass :=
  lt_of_lt_of_le (div_pos (limitingVacancy_pos_of_not_RH h) (by norm_num))
    limitingWeightedVacancyMass_first_site_lower

/-- Exact finite matrix expression for the weighted prefix. -/
theorem weightedVacancyPrefix_eq_trace (N M : ℕ) :
    weightedVacancyPrefix N M =
      1 - 1 / ((M : ℝ) + 1) -
        Matrix.trace (Matrix.diagonal (fun i : Fin M => paretoWeight i.val) *
          Matrix.of (fun i j : Fin M => integerKernel N i.val j.val)) := by
  have ht :
      Matrix.trace (Matrix.diagonal (fun i : Fin M => paretoWeight i.val) *
        Matrix.of (fun i j : Fin M => integerKernel N i.val j.val)) =
      ∑ i ∈ Finset.range M, paretoWeight i * integerKernel N i i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Matrix.of_apply]
    exact Fin.sum_univ_eq_sum_range (fun i : ℕ => paretoWeight i * integerKernel N i i) M
  unfold weightedVacancyPrefix weightedVacancyTerm
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, paretoWeight_partial_sum, ht]

/-- Full Gram matrices retain all arithmetic tails and mixed terms. -/
theorem weightedVacancyPrefix_eq_gram_trace (N M : ℕ) :
    weightedVacancyPrefix N M =
      1 - 1 / ((M : ℝ) + 1) -
        Matrix.trace (Matrix.diagonal (fun i : Fin M => paretoWeight i.val) *
          (windowFeatures N M (fun i => i.val) * (fullGram N)⁻¹ *
            (windowFeatures N M (fun i => i.val)).transpose)) := by
  rw [weightedVacancyPrefix_eq_trace, integerKernel_window_matrix]

/-- Open arithmetic provider: all quantities inside a certificate are finite. -/
def WeightedVacancyCutoffCertificates : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N M : ℕ,
    weightedVacancyPrefix N M + 1 / ((M : ℝ) + 1) < ε

theorem weightedVacancyCutoffCertificates_iff_top :
    WeightedVacancyCutoffCertificates ↔ closedSpace = ⊤ := by
  constructor
  · intro h
    apply weightedVacancyMass_zero_iff_top.mp
    apply le_antisymm _ weightedVacancyMass_bounds.1
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N, M, hNM⟩ := h ε hε
    have hlim := weightedVacancyMass_le_finite N
    have hcut := (finiteWeightedVacancyMass_cutoff_bounds N M).2
    linarith
  · intro h ε hε
    have ht := finiteWeightedVacancyMass_tendsto_zero_iff_top.mpr h
    obtain ⟨N, hN⟩ := ((tendsto_order.mp ht).2 (ε / 2) (by linarith)).exists
    obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
    have hM' := (div_lt_iff₀ hε).mp hM
    have htail : 1 / ((M : ℝ) + 1) < ε / 2 := by
      apply (div_lt_iff₀ (by positivity : 0 < (M : ℝ) + 1)).mpr
      nlinarith
    refine ⟨N, M, ?_⟩
    have hp := (finiteWeightedVacancyMass_cutoff_bounds N M).1
    linarith

theorem riemannHypothesis_of_weightedVacancyCutoffCertificates
    (h : WeightedVacancyCutoffCertificates) : RiemannHypothesis := by
  apply riemannHypothesis_of_vacancy_tendsto_zero
  apply vacancy_tendsto_zero_iff_limitingVacancy_zero.mpr
  exact limitingVacancy_zero_iff_top.mpr
    (weightedVacancyCutoffCertificates_iff_top.mp h)

end RiemannResearch.RH.Pareto.IntegerDPP
