import RiemannResearch.RH.ParetoDyadicCoefficientPolynomial
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.Analysis.BoundedInterpolation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual finite-budget Pareto moment optimizers

Source: the user-provided Ramanujan--Laguerre continuation, Section 6.
The finite budget is embedded in the genuine Pareto Hilbert space. All
observations are the original integrals. Finite-dimensional orthogonal
projection supplies a minimizer for each nonempty exact feasible set.
The uniform-in-budget cost estimate is not asserted.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.RamanujanLaguerre
open FiniteTwoSeedCompletion

private theorem finite_budget_generators (M : ℕ) :
    {f : ℕ → ℝ | ∃ a : ℕ, (a = 2 ∨ a = 3) ∧
      ∃ n : ℕ, 0 < n ∧ n ≤ M ∧ f = dilation n (residue a)}.Finite := by
  have h2 := (Set.finite_Icc 1 M).image (fun n => dilation n (residue 2))
  have h3 := (Set.finite_Icc 1 M).image (fun n => dilation n (residue 3))
  apply (h2.union h3).subset
  rintro f ⟨a, ha, n, hn, hnM, rfl⟩
  rcases ha with rfl | rfl
  · exact Or.inl ⟨n, ⟨hn, hnM⟩, rfl⟩
  · exact Or.inr ⟨n, ⟨hn, hnM⟩, rfl⟩

instance budgetSpanFiniteDimensional (M : ℕ) : FiniteDimensional ℝ (budgetSpan M) :=
  FiniteDimensional.span_of_finite ℝ (finite_budget_generators M)

/-- The exact algebraic finite budget inside the complete weighted space. -/
def budgetHilbert (M : ℕ) : Submodule ℝ ThresholdHilbert :=
  (budgetSpan M).comap hilbertSequenceLinear

private def budgetPhysical (M : ℕ) : budgetHilbert M →ₗ[ℝ] budgetSpan M where
  toFun f := ⟨hilbertSequence f, f.property⟩
  map_add' f g := Subtype.ext (hilbertSequenceLinear.map_add f g)
  map_smul' c f := Subtype.ext (hilbertSequenceLinear.map_smul c f)

instance budgetHilbertFiniteDimensional (M : ℕ) :
    FiniteDimensional ℝ (budgetHilbert M) := by
  apply FiniteDimensional.of_injective (budgetPhysical M)
  intro f g h
  apply Subtype.ext
  apply hilbertSequence_injective
  exact congrArg Subtype.val h

private theorem budgetHilbert_integrable (M : ℕ) (f : budgetHilbert M) :
    AllMomentsIntegrable (hilbertSequence f) := by
  obtain ⟨C, hC⟩ := budgetSpan_bounded f.property
  change ∀ k, |hilbertSequence (f : ThresholdHilbert) k| ≤ C at hC
  exact allMomentsIntegrable_of_bounded hC

/-- Every original ordinary moment is linear on the actual finite budget. -/
def budgetMomentLinear (M j : ℕ) : budgetHilbert M →ₗ[ℝ] ℝ where
  toFun f := ordinaryMoment (hilbertSequence f) j
  map_add' f g := by
    have hseq : hilbertSequence ((f + g : budgetHilbert M) : ThresholdHilbert) =
        hilbertSequence f + hilbertSequence g := hilbertSequenceLinear.map_add f g
    change ordinaryMoment (hilbertSequence ((f + g : budgetHilbert M) : ThresholdHilbert)) j = _
    rw [hseq]
    simp only [ordinaryMoment, exponentialLift, Pi.add_apply, add_mul]
    exact integral_add (budgetHilbert_integrable M f j) (budgetHilbert_integrable M g j)
  map_smul' c f := by
    have hseq : hilbertSequence ((c • f : budgetHilbert M) : ThresholdHilbert) =
        c • hilbertSequence f := hilbertSequenceLinear.map_smul c f
    change ordinaryMoment (hilbertSequence ((c • f : budgetHilbert M) : ThresholdHilbert)) j = _
    rw [hseq]
    simp only [ordinaryMoment, exponentialLift, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _

/-- Finite algebra packages the original coefficient integrals as a linear map. -/
def budgetCoefficientLinear (M k : ℕ) : budgetHilbert M →ₗ[ℝ] ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    RiemannResearch.Analysis.laguerreCoefficient k j • budgetMomentLinear M j

@[simp] theorem budgetCoefficientLinear_apply (M k : ℕ) (f : budgetHilbert M) :
    budgetCoefficientLinear M k f = coefficient (hilbertSequence f) k := by
  rw [coefficient_eq_momentTransform _ (budgetHilbert_integrable M f)]
  simp [budgetCoefficientLinear, budgetMomentLinear,
    RiemannResearch.Analysis.laguerreMomentTransform]

private theorem budgetCoefficient_zero (M : ℕ) (f : budgetHilbert M) :
    coefficient (hilbertSequence f) 0 = paretoMean (hilbertSequence f) := by
  rw [coefficient_eq_momentTransform _ (budgetHilbert_integrable M f),
    RiemannResearch.Analysis.laguerreMomentTransform_zero]
  obtain ⟨C, hC⟩ := budgetSpan_bounded f.property
  change ∀ k, |hilbertSequence (f : ThresholdHilbert) k| ≤ C at hC
  exact ordinaryMoment_zero_of_bounded hC

private theorem exists_budgetHilbert (M : ℕ) (F : ℕ → ℝ)
    (hF : F ∈ budgetSpan M) :
    ∃ f : budgetHilbert M, hilbertSequence f = F := by
  obtain ⟨C, hC⟩ := budgetSpan_bounded hF
  have hs : Summable (fun k => positiveWeight k * F k ^ 2) :=
    weighted_summable_of_bounded (by simpa only [pow_two] using bounded_product hC hC)
  have hz : F 0 = 0 := legalSeedSpan_zero_value _ (budgetSpan_le_legal M hF)
  obtain ⟨f, hf⟩ := (hilbertSequence_range F).mpr ⟨hz, hs⟩
  exact ⟨⟨f, by change hilbertSequence f ∈ budgetSpan M; rw [hf]; exact hF⟩, hf⟩

private theorem budget_norm_sq_eq_error_add_one (M : ℕ) (f : budgetHilbert M)
    (hf : paretoMean (hilbertSequence f) = 1) :
    ‖f‖ ^ 2 = paretoError (hilbertSequence f) + 1 := by
  obtain ⟨C, hC⟩ := budgetSpan_bounded f.property
  change ∀ k, |hilbertSequence (f : ThresholdHilbert) k| ≤ C at hC
  have he := paretoError_scale hC 1
  simp only [one_mul, one_pow] at he
  rw [paretoVariance_eq hC, hf] at he
  have hn : ‖f‖ ^ 2 = paretoInner (hilbertSequence f) (hilbertSequence f) := by
    change ‖(f : ThresholdHilbert)‖ ^ 2 = _
    simpa only [paretoInner, pow_two] using hilbert_norm_weighted_sq (f : ThresholdHilbert)
  linarith

/-- Actual optimizer existence follows from actual feasibility at each budget.
This statement preserves the complete infinite Pareto error and exact moments. -/
theorem everyBudgetOptimizerTarget_of_feasible
    (hfeas : EveryBudgetFeasibleTarget) : EveryBudgetOptimizerTarget := by
  intro K
  obtain ⟨F, hFM, hFI, hFm, hFc⟩ := hfeas K
  obtain ⟨f, hf⟩ := exists_budgetHilbert (2 ^ K) F hFM
  let ell : ℕ → budgetHilbert (2 ^ K) →L[ℝ] ℝ :=
    fun j => LinearMap.toContinuousLinearMap (budgetCoefficientLinear (2 ^ K) j)
  have hell (j : ℕ) (g : budgetHilbert (2 ^ K)) :
      ell j g = coefficient (hilbertSequence g) j :=
    budgetCoefficientLinear_apply (2 ^ K) j g
  obtain ⟨v, hvtop, hvhead, hvnorm, hvorth⟩ :=
    RiemannResearch.Analysis.BoundedInterpolation.exists_minimum_head
      (⊤ : Submodule ℝ (budgetHilbert (2 ^ K))) isClosed_univ ell K f (by trivial)
  have hvmean : paretoMean (hilbertSequence v) = 1 := by
    have h := hvhead 0 (Nat.zero_le K)
    rw [hell, hell, budgetCoefficient_zero, budgetCoefficient_zero, hf, hFm] at h
    exact h
  have hvcoeff : ∀ j : ℕ, 0 < j → j ≤ K → coefficient (hilbertSequence v) j = 0 := by
    intro j hj hjK
    have h := hvhead j hjK
    rw [hell, hell, hf, hFc j hj hjK] at h
    exact h
  refine ⟨hilbertSequence v, ⟨v.property, budgetHilbert_integrable _ v, hvmean, hvcoeff⟩, ?_⟩
  intro G hG
  obtain ⟨g, hg⟩ := exists_budgetHilbert (2 ^ K) G hG.1
  have hgmean : paretoMean (hilbertSequence g) = 1 := by rw [hg]; exact hG.2.2.1
  have hsame : ∀ j ≤ K, ell j g = ell j v := by
    intro j hjK
    rw [hell, hell]
    by_cases hj : j = 0
    · subst j
      rw [budgetCoefficient_zero, budgetCoefficient_zero, hgmean, hvmean]
    · rw [hg, hG.2.2.2 j (Nat.pos_of_ne_zero hj) hjK,
        hvcoeff j (Nat.pos_of_ne_zero hj) hjK]
  have he := RiemannResearch.Analysis.BoundedInterpolation.minimum_head_pythagoras
    (⊤ : Submodule ℝ (budgetHilbert (2 ^ K))) ell K v g hvtop (by trivial) hsame hvorth
  have hnv := budget_norm_sq_eq_error_add_one (2 ^ K) v hvmean
  have hng := budget_norm_sq_eq_error_add_one (2 ^ K) g hgmean
  rw [hg] at hng
  nlinarith [sq_nonneg ‖g - v‖]

/-- Unconditional existence of an actual full-error optimizer at every budget. -/
theorem everyBudgetOptimizerTarget : EveryBudgetOptimizerTarget :=
  everyBudgetOptimizerTarget_of_feasible everyBudgetFeasibleTarget

end RiemannResearch.RH.Pareto.RamanujanLaguerre
