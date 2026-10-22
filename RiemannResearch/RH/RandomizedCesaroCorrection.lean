import RiemannResearch.Probability.RandomizedCorrectionPythagoras
import RiemannResearch.Analysis.CesaroWeightedContraction
import RiemannResearch.RH.ThresholdLegalIntegrability

/-!
# Randomized corrections in the actual arithmetic Cesaro geometry

Source: the user-provided conditional-iid/Cesaro handoff, Section 9.
This RH consumer instantiates the abstract Hilbert identity with the constructed
weighted Cesaro operator and actual finite legal arithmetic directions. Their
Hilbert embeddings and all square summability are proved from legality.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID
open Probability.RandomizedCorrection ArithmeticCumulative

/-- Embed an actual legal direction; no integrability premise is added. -/
def legalCorrectionVector (g : legalSeedSpan (Set.Ici 1)) : ThresholdHilbert :=
  sequenceHilbert (g : ℕ → ℝ) (by
    simpa only [pow_two] using
      legalSeedSpan_mixed_summable (Set.Ici 1) (by intro a ha; exact ha)
        g.property g.property)

/-- The embedding recovers the original arithmetic function at every index. -/
@[simp] theorem hilbertSequence_legalCorrectionVector (g : legalSeedSpan (Set.Ici 1)) :
    hilbertSequence (legalCorrectionVector g) = (g : ℕ → ℝ) := by
  apply hilbertSequence_sequenceHilbert
  exact legalSeedSpan_zero_value _ g.property

/-- The operator norm appearing below is precisely the arithmetic conditional energy. -/
theorem legalCorrectionVector_conditional_energy (g : legalSeedSpan (Set.Ici 1)) :
    ‖cesaroOperator (legalCorrectionVector g)‖ ^ 2 =
      ∑' k : ℕ, mixtureWeight (k + 1) * cesaro (g : ℕ → ℝ) (k + 1) ^ 2 := by
  change ‖hilbertCesaro (legalCorrectionVector g)‖ ^ 2 = _
  rw [hilbertCesaro_norm_sq, hilbertSequence_legalCorrectionVector]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Mean coefficients stay in the identical finite legal arithmetic space. -/
theorem mean_coefficient_correction_legal {ι : Type*} (s : Finset ι)
    (w : ι → legalSeedSpan (Set.Ici 1)) (A : ι → Ω → ℝ)
    (_hA : ∀ i ∈ s, MemLp (A i) 2 μ) :
    (fun n => ∑ i ∈ s, (∫ ω, A i ω ∂μ) * (w i : ℕ → ℝ) n) ∈
      legalSeedSpan (Set.Ici 1) := by
  have h : (∑ i ∈ s, (∫ ω, A i ω ∂μ) • (w i : ℕ → ℝ)) ∈
      legalSeedSpan (Set.Ici 1) := by
    apply (legalSeedSpan _).sum_mem
    intro i hi
    exact (legalSeedSpan _).smul_mem _ (w i).property
  convert h using 1
  funext n
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Exact full-H randomization penalty for actual legal correction directions. -/
theorem legal_randomized_full_energy_decomposition {ι : Type*} (s : Finset ι)
    (w : ι → legalSeedSpan (Set.Ici 1)) (A : ι → Ω → ℝ)
    (hA : ∀ i ∈ s, MemLp (A i) 2 μ) (e : ThresholdHilbert) :
    (∫ ω, ‖e - ∑ i ∈ s, A i ω • legalCorrectionVector (w i)‖ ^ 2 ∂μ) =
      ‖e - ∑ i ∈ s, (∫ ω, A i ω ∂μ) • legalCorrectionVector (w i)‖ ^ 2 +
        ∫ ω, ‖∑ i ∈ s,
          (A i ω - ∫ η, A i η ∂μ) • legalCorrectionVector (w i)‖ ^ 2 ∂μ :=
  finite_coefficient_loss_decomposition s (fun i => legalCorrectionVector (w i)) A hA e

/-- Exact conditional-mean randomization penalty, using the actual Cesaro operator. -/
theorem legal_randomized_conditionalMean_decomposition {ι : Type*} (s : Finset ι)
    (w : ι → legalSeedSpan (Set.Ici 1)) (A : ι → Ω → ℝ)
    (hA : ∀ i ∈ s, MemLp (A i) 2 μ) (e : ThresholdHilbert) :
    (∫ ω, ‖cesaroOperator (e - ∑ i ∈ s,
      A i ω • legalCorrectionVector (w i))‖ ^ 2 ∂μ) =
      ‖cesaroOperator (e - ∑ i ∈ s,
        (∫ ω, A i ω ∂μ) • legalCorrectionVector (w i))‖ ^ 2 +
        ∫ ω, ‖cesaroOperator (∑ i ∈ s,
          (A i ω - ∫ η, A i η ∂μ) • legalCorrectionVector (w i))‖ ^ 2 ∂μ :=
  smoothed_finite_coefficient_loss_decomposition cesaroOperator s
    (fun i => legalCorrectionVector (w i)) A hA e

/-- Randomizing a fixed legal coefficient space cannot beat its mean coefficients. -/
theorem legal_mean_conditional_energy_le_randomized {ι : Type*} (s : Finset ι)
    (w : ι → legalSeedSpan (Set.Ici 1)) (A : ι → Ω → ℝ)
    (hA : ∀ i ∈ s, MemLp (A i) 2 μ) (e : ThresholdHilbert) :
    ‖cesaroOperator (e - ∑ i ∈ s,
      (∫ ω, A i ω ∂μ) • legalCorrectionVector (w i))‖ ^ 2 ≤
      ∫ ω, ‖cesaroOperator (e - ∑ i ∈ s,
        A i ω • legalCorrectionVector (w i))‖ ^ 2 ∂μ := by
  rw [legal_randomized_conditionalMean_decomposition s w A hA e]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

end RiemannResearch.RH.Pareto
