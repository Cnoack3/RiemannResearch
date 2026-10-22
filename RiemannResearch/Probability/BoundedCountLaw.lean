import RiemannResearch.Probability.DeterminantalBernoulliCount
import RiemannResearch.Probability.DeterminantalMoments
import Mathlib.Probability.IdentDistrib

/-!
# Exact Bernoulli law and moments from a finite-range count PGF

This transports the existing finite Bernoulli subset law to an actual count on
an arbitrary probability space, using only its PGF and finite range. The
intended application is the number of points of the finite Mellin projection
process in a measurable frequency window.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Classical

namespace RiemannResearch.Probability

variable {Ω α β : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Polynomial uniqueness transfers an actual finite-valued statistic to the
cardinality law of an explicit finite PMF. -/
theorem finite_statistic_law_eq_of_generating
    [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [Fintype β] (X : Ω → α) (hX : Measurable X) (f : α → ℕ)
    (q : PMF β) (g : β → ℕ)
    (hpgf : ∀ z : ℝ, (∫ ω, z ^ f (X ω) ∂μ) =
      ∑ b, z ^ g b * (q b).toReal) :
    μ.map (fun ω => f (X ω)) = (q.map g).toMeasure := by
  let ν : Measure α := μ.map X
  letI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hf : Measurable f := measurable_of_finite f
  have hq : ν.toPMF.map f = q.map g := by
    apply PMF.map_nat_eq_of_generating_eq
    intro z
    have hsum := PMF.integral_eq_sum ν.toPMF (fun a => z ^ f a)
    rw [Measure.toPMF_toMeasure] at hsum
    calc
      (∑ a, z ^ f a * (ν.toPMF a).toReal) = (∫ a, z ^ f a ∂ν) := by
        simpa only [smul_eq_mul, mul_comm] using hsum.symm
      _ = (∫ ω, z ^ f (X ω) ∂μ) :=
        integral_map hX.aemeasurable (measurable_of_finite _).aestronglyMeasurable
      _ = _ := hpgf z
  have heq := congrArg (fun r : PMF ℕ => r.toMeasure) hq
  rw [← PMF.toMeasure_map f ν.toPMF hf, Measure.toPMF_toMeasure] at heq
  simpa only [ν, Measure.map_map hf hX, Function.comp_def] using heq

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The PGF of a bounded count determines its complete Poisson-binomial law.
Only the finite range is required; no independence on the original sample
space is assumed. -/
theorem count_law_eq_bernoulli_of_generating
    (Y : Ω → ℕ) (hY : Measurable Y) (hfinite : (Set.range Y).Finite)
    (p : ι → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hpgf : ∀ z : ℝ, (∫ ω, z ^ Y ω ∂μ) = ∏ i, (1 - p i + z * p i)) :
    μ.map Y = ((DPP.bernoulliSubsetLaw p hp).map Finset.card).toMeasure := by
  letI : Fintype (Set.range Y) := hfinite.fintype
  let X : Ω → Set.range Y := fun ω => ⟨Y ω, Set.mem_range_self ω⟩
  have hX : Measurable X := hY.subtype_mk
  apply finite_statistic_law_eq_of_generating X hX Subtype.val
    (DPP.bernoulliSubsetLaw p hp) Finset.card
  intro z
  exact (hpgf z).trans (DPP.bernoulliSubsetLaw_count_generating p hp z).symm

namespace DPP

section BernoulliMoments
variable [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

private theorem windowCount_coe_eq_card :
    windowCount (fun S : Finset ι => (S : Set ι)) (fun i : ι => i) =
      (fun S => (S.card : ℝ)) := by
  funext S
  simp [windowCount, occupancyIndicator, Set.indicator_apply]

/-- The expectation under the explicit Bernoulli product subset law. -/
theorem bernoulliSubsetLaw_integral_card (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    (∫ S, (S.card : ℝ) ∂(bernoulliSubsetLaw p hp).toMeasure) = ∑ i, p i := by
  have h := (finiteLaw_isDPP (Matrix.diagonal p)
    (exactWeight_diagonal_nonneg p hp)).expected_windowCount (fun i => i)
  rw [windowCount_coe_eq_card] at h
  simpa only [bernoulliSubsetLaw, Matrix.diagonal_apply_eq] using h

/-- The variance under the explicit Bernoulli product subset law. -/
theorem bernoulliSubsetLaw_variance_card (p : ι → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    variance (fun S : Finset ι => (S.card : ℝ)) (bernoulliSubsetLaw p hp).toMeasure =
      ∑ i, p i * (1 - p i) := by
  have h := (finiteLaw_isDPP (Matrix.diagonal p)
    (exactWeight_diagonal_nonneg p hp)).variance_windowCount (Function.Embedding.refl ι)
  change variance (windowCount (fun S : Finset ι => (S : Set ι)) (fun i => i))
      (bernoulliSubsetLaw p hp).toMeasure =
    (∑ i, Matrix.diagonal p i i) -
      ∑ i, ∑ j, Matrix.diagonal p i j * Matrix.diagonal p j i at h
  rw [windowCount_coe_eq_card] at h
  have hdiag : (∑ i, ∑ j, Matrix.diagonal p i j * Matrix.diagonal p j i) =
      ∑ i, (p i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp [pow_two]
    · intro j _ hij
      simp [Matrix.diagonal, hij, Ne.symm hij]
    · simp
  rw [h, hdiag]
  simp only [Matrix.diagonal_apply_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end BernoulliMoments
end DPP

/-- Equality of the complete count law yields the exact spectral mean and
variance of the actual count. -/
theorem count_moments_of_bernoulli_law
    (Y : Ω → ℕ) (hY : Measurable Y)
    (p : ι → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hlaw : μ.map Y = ((DPP.bernoulliSubsetLaw p hp).map Finset.card).toMeasure) :
    (∫ ω, (Y ω : ℝ) ∂μ) = ∑ i, p i ∧
      variance (fun ω => (Y ω : ℝ)) μ = ∑ i, p i * (1 - p i) := by
  letI : MeasurableSpace (Finset ι) := ⊤
  have hcard : Measurable (Finset.card : Finset ι → ℕ) := measurable_of_finite _
  have hid : IdentDistrib Y Finset.card μ (DPP.bernoulliSubsetLaw p hp).toMeasure := by
    refine ⟨hY.aemeasurable, hcard.aemeasurable, ?_⟩
    rw [PMF.toMeasure_map Finset.card (DPP.bernoulliSubsetLaw p hp) hcard]
    exact hlaw
  have hidR := hid.comp (measurable_of_countable (fun k : ℕ => (k : ℝ)))
  constructor
  · exact hidR.integral_eq.trans (DPP.bernoulliSubsetLaw_integral_card p hp)
  · exact hidR.variance_eq.trans (DPP.bernoulliSubsetLaw_variance_card p hp)

/-- Exact mean and variance follow from the actual finite-range PGF. -/
theorem count_moments_of_generating
    (Y : Ω → ℕ) (hY : Measurable Y) (hfinite : (Set.range Y).Finite)
    (p : ι → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hpgf : ∀ z : ℝ, (∫ ω, z ^ Y ω ∂μ) = ∏ i, (1 - p i + z * p i)) :
    (∫ ω, (Y ω : ℝ) ∂μ) = ∑ i, p i ∧
      variance (fun ω => (Y ω : ℝ)) μ = ∑ i, p i * (1 - p i) :=
  count_moments_of_bernoulli_law Y hY p hp
    (count_law_eq_bernoulli_of_generating Y hY hfinite p hp hpgf)

/-- The spectral variance is bounded by occupied mass, vacant mass, and one
quarter of the number of spectral parameters. -/
theorem bernoulli_variance_bounds
    (p : ι → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i, p i * (1 - p i)) ≤ ∑ i, p i ∧
      (∑ i, p i * (1 - p i)) ≤ (Fintype.card ι : ℝ) - ∑ i, p i ∧
      (∑ i, p i * (1 - p i)) ≤ (Fintype.card ι : ℝ) / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (p i)]
  · calc
      (∑ i, p i * (1 - p i)) ≤ ∑ i, (1 - p i) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_of_le_one_left (sub_nonneg.mpr (hp i).2) (hp i).2
      _ = (Fintype.card ι : ℝ) - ∑ i, p i := by
        rw [Finset.sum_sub_distrib]
        simp
  · calc
      (∑ i, p i * (1 - p i)) ≤ ∑ _ : ι, (1 / 4 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg (p i - 1 / 2)]
      _ = (Fintype.card ι : ℝ) / 4 := by simp [div_eq_mul_inv]

/-- Universal actual-count variance bounds, with no arithmetic rate premise. -/
theorem count_variance_bounds_of_generating
    (Y : Ω → ℕ) (hY : Measurable Y) (hfinite : (Set.range Y).Finite)
    (p : ι → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1)
    (hpgf : ∀ z : ℝ, (∫ ω, z ^ Y ω ∂μ) = ∏ i, (1 - p i + z * p i)) :
    variance (fun ω => (Y ω : ℝ)) μ ≤ (∫ ω, (Y ω : ℝ) ∂μ) ∧
      variance (fun ω => (Y ω : ℝ)) μ ≤
        (Fintype.card ι : ℝ) - (∫ ω, (Y ω : ℝ) ∂μ) ∧
      variance (fun ω => (Y ω : ℝ)) μ ≤ (Fintype.card ι : ℝ) / 4 := by
  obtain ⟨hmean, hvar⟩ := count_moments_of_generating Y hY hfinite p hp hpgf
  rw [hmean, hvar]
  exact bernoulli_variance_bounds p hp

end RiemannResearch.Probability
