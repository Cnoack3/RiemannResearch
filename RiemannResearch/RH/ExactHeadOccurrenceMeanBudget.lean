import RiemannResearch.RH.ExactHeadOccurrencePartition
import RiemannResearch.RH.ExactHeadOccurrenceCertificates
import RiemannResearch.RH.ExactHeadOccurrenceProjection
import RiemannResearch.RH.ExactHeadAtomOptimizer
import RiemannResearch.RH.ExactHeadGcdAtoms
import RiemannResearch.Analysis.FiniteProfileEnergy
import RiemannResearch.Analysis.FiniteWeightedVarianceCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact losses in occurrence gap budgets

Source: independent algebra from the actual canonical block decomposition.
The endpoint-mean budget is smaller than the quarter-range budget. Two
explicit nonnegative remainders account for the full difference from the
actual energy. The final RH implication still needs a cofinal provider.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.FiniteWeightedVariance
open RiemannResearch.RH.ExactHeadGcdAtoms
open ExactHeadAtomOptimizer MobiusHeadGreen

/-- The sharper endpoint-mean budget keeps the actual position of every block mean. -/
def occurrenceMeanBudget (P x : ℕ) : ℝ :=
  energy (Finset.Ico 1 (occurrenceBoundary P x 0)) (progressionWeight P) (target P) +
  ∑ i ∈ Finset.range (freePositions P x).card,
    FiniteWeightedVariance.mass
      (Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)))
      (progressionWeight P) *
      (target P (occurrenceBoundary P x (i+1)-1) - occurrenceBlockMean P x i) *
      (occurrenceBlockMean P x i - target P (occurrenceBoundary P x i))

/-- The exact nonnegative loss from replacing variance by the endpoint-mean bound. -/
def occurrenceEndpointRemainder (P x : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (freePositions P x).card,
    ∑ r ∈ Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)),
      progressionWeight P r *
        (target P (occurrenceBoundary P x (i+1)-1) - target P r) *
        (target P r - target P (occurrenceBoundary P x i))

/-- The exact nonnegative loss from replacing the actual mean by the midpoint. -/
def occurrenceMidpointRemainder (P x : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (freePositions P x).card,
    FiniteWeightedVariance.mass
      (Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)))
      (progressionWeight P) *
      (occurrenceBlockMean P x i -
        (target P (occurrenceBoundary P x i) +
          target P (occurrenceBoundary P x (i+1)-1)) / 2)^2

/-- The stronger budget is exactly the true energy plus its retained endpoint remainder. -/
theorem occurrenceMeanBudget_exact (P x : ℕ) (hP : 0 < P) :
    occurrenceMeanBudget P x = occurrenceEnergy P x + occurrenceEndpointRemainder P x := by
  rw [occurrenceEnergy_eq_block_variances P x hP]
  unfold occurrenceMeanBudget occurrenceEndpointRemainder
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  symm
  exact variance_endpoint_identity _ _ _
    (occurrence_block_mass_pos P _ _
      (occurrenceBoundary_pos P x i hP)
      (occurrenceBoundary_strict P x i (Finset.mem_range.mp hi))
      (occurrenceBoundary_le_period P x (i+1))).ne' _ _

theorem occurrenceEndpointRemainder_nonneg (P x : ℕ) :
    0 ≤ occurrenceEndpointRemainder P x := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro r hr
  have hr' := Finset.mem_Ico.mp hr
  exact mul_nonneg
    (mul_nonneg (progressionWeight_nonneg P r)
      (sub_nonneg.mpr (occurrence_target_mono P (by omega))))
    (sub_nonneg.mpr (occurrence_target_mono P hr'.1))

theorem occurrenceMidpointRemainder_nonneg (P x : ℕ) :
    0 ≤ occurrenceMidpointRemainder P x := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (Finset.sum_nonneg (fun r hr => progressionWeight_nonneg P r))
    (sq_nonneg _)

/-- Both distinct sources of loss in the quarter-range budget are explicit squares/products. -/
theorem occurrenceGapBudget_eq_mean_add_midpoint (P x : ℕ) :
    occurrenceGapBudget P x = occurrenceMeanBudget P x + occurrenceMidpointRemainder P x := by
  unfold occurrenceGapBudget occurrenceMeanBudget occurrenceMidpointRemainder
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem occurrenceGapBudget_exact (P x : ℕ) (hP : 0 < P) :
    occurrenceGapBudget P x = occurrenceEnergy P x +
      occurrenceEndpointRemainder P x + occurrenceMidpointRemainder P x := by
  rw [occurrenceGapBudget_eq_mean_add_midpoint, occurrenceMeanBudget_exact P x hP]

theorem occurrenceEnergy_le_meanBudget (P x : ℕ) (hP : 0 < P) :
    occurrenceEnergy P x ≤ occurrenceMeanBudget P x := by
  rw [occurrenceMeanBudget_exact P x hP]
  exact le_add_of_nonneg_right (occurrenceEndpointRemainder_nonneg P x)

theorem occurrenceMeanBudget_le_gapBudget (P x : ℕ) :
    occurrenceMeanBudget P x ≤ occurrenceGapBudget P x := by
  rw [occurrenceGapBudget_eq_mean_add_midpoint]
  exact le_add_of_nonneg_right (occurrenceMidpointRemainder_nonneg P x)

theorem atomEnergy_le_meanBudget_add_green (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    atomEnergy P x ≤ occurrenceMeanBudget P x +
      energy (Finset.Icc 1 (P-1)) (progressionWeight P)
        (fit P x (occurrenceCoefficients P x) - synthesis P (upperDivisors P x) u) := by
  rw [atomEnergy_eq_occurrence_add_reuse]
  exact add_le_add (occurrenceEnergy_le_meanBudget P x hP) (reuseEnergy_le_trial P x u)

/-- Conditional reduction with a pointwise smaller budget.
The common cofinal provider remains open. -/
theorem riemannHypothesis_of_cofinal_mean_green_budget (B : ℝ) (u : ℕ → ℕ → ℝ)
    (hdata : ∀ J : ℕ, ∃ x, J ≤ x ∧
      occurrenceMeanBudget (greenPeriod x) x +
        energy (Finset.Icc 1 (greenPeriod x - 1)) (progressionWeight (greenPeriod x))
          (fit (greenPeriod x) x (occurrenceCoefficients (greenPeriod x) x) -
            synthesis (greenPeriod x) (upperDivisors (greenPeriod x) x) (u x)) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_bounded_atomEnergy B
  intro J
  obtain ⟨x,hx,hbound⟩ := hdata J
  exact ⟨x,hx,(atomEnergy_le_meanBudget_add_green (greenPeriod x) x
    (lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x)) (u x)).trans hbound⟩

/-- The complete objective in the cofinal mean--Green hypothesis. -/
def meanGreenBudget (P x : ℕ) (u : ℕ → ℝ) : ℝ :=
  occurrenceMeanBudget P x +
    energy (Finset.Icc 1 (P-1)) (progressionWeight P)
      (fit P x (occurrenceCoefficients P x) - synthesis P (upperDivisors P x) u)

/-- The endpoint remainder and the exact synthesis excess are both charged. -/
theorem meanGreenBudget_eq_atom_add_remainders (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    meanGreenBudget P x u = atomEnergy P x + occurrenceEndpointRemainder P x +
      energy (Finset.Icc 1 (P-1)) (progressionWeight P)
        (synthesis P (upperDivisors P x) (atomNormalCoefficients P x) -
          synthesis P (upperDivisors P x) u) := by
  unfold meanGreenBudget
  rw [occurrenceMeanBudget_exact P x hP, reuse_trial_identity,
    atomEnergy_eq_occurrence_add_reuse]
  ring

/-- Orthogonality eliminates the occurrence optimizer from the combined budget.
This identity preserves the initial interval and the endpoint remainder. -/
theorem meanGreenBudget_eq_target_trial (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    meanGreenBudget P x u =
    energy (Finset.Icc 1 (P-1)) (progressionWeight P)
      (target P - synthesis P (upperDivisors P x) u) +
        occurrenceEndpointRemainder P x := by
  unfold meanGreenBudget
  have h := occurrence_trial_identity P x (fun n => u (Nat.gcd n P))
  have hs : ∀ r ∈ Finset.Icc 1 (P-1),
      fit P x (fun n => u (Nat.gcd n P)) r =
        synthesis P (upperDivisors P x) u r := by
    intro r hr
    exact lift_synthesis P x u r (by have := Finset.mem_Icc.mp hr; omega)
  have ht : energy (Finset.Icc 1 (P-1)) (progressionWeight P)
      (target P - fit P x (fun n => u (Nat.gcd n P))) =
      energy (Finset.Icc 1 (P-1)) (progressionWeight P)
        (target P - synthesis P (upperDivisors P x) u) := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Pi.sub_apply, hs r hr]
  have hd : energy (Finset.Icc 1 (P-1)) (progressionWeight P)
      (fit P x (occurrenceCoefficients P x) - fit P x (fun n => u (Nat.gcd n P))) =
      energy (Finset.Icc 1 (P-1)) (progressionWeight P)
        (fit P x (occurrenceCoefficients P x) - synthesis P (upperDivisors P x) u) := by
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Pi.sub_apply, hs r hr]
  rw [ht, hd] at h
  rw [occurrenceMeanBudget_exact P x hP, h]
  ring

/-- The best possible shared correction has cost atom energy plus endpoint loss. -/
theorem meanGreenBudget_optimal (P x : ℕ) (hP : 0 < P) :
    meanGreenBudget P x (atomNormalCoefficients P x) =
      atomEnergy P x + occurrenceEndpointRemainder P x := by
  rw [meanGreenBudget_eq_atom_add_remainders P x hP]
  simp [energy]

theorem meanGreenBudget_minimizes (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    atomEnergy P x + occurrenceEndpointRemainder P x ≤ meanGreenBudget P x u := by
  rw [meanGreenBudget_eq_atom_add_remainders P x hP]
  exact le_add_of_nonneg_right
    (energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg P r))

theorem meanGreenBudget_nonneg (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    0 ≤ meanGreenBudget P x u := by
  rw [meanGreenBudget_eq_target_trial P x hP]
  exact add_nonneg (energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg P r))
    (occurrenceEndpointRemainder_nonneg P x)

/-- This is an exact characterization, not a provider of the bound. -/
theorem exists_meanGreenBudget_le_iff (P x : ℕ) (hP : 0 < P) (B : ℝ) :
    (∃ u : ℕ → ℝ, meanGreenBudget P x u ≤ B) ↔
      atomEnergy P x + occurrenceEndpointRemainder P x ≤ B := by
  constructor
  · rintro ⟨u, hu⟩
    exact (meanGreenBudget_minimizes P x hP u).trans hu
  · intro h
    exact ⟨atomNormalCoefficients P x, (meanGreenBudget_optimal P x hP).trans_le h⟩

/-- Optimizing the correction family leaves precisely the cofinal atom-plus-endpoint
bound. In particular the endpoint remainder cannot be canceled by synthesis. -/
theorem cofinal_meanGreenBudget_iff_atom_endpoint (B : ℝ) :
    (∃ u : ℕ → ℕ → ℝ, ∀ J : ℕ, ∃ x, J ≤ x ∧
      meanGreenBudget (greenPeriod x) x (u x) ≤ B) ↔
    (∀ J : ℕ, ∃ x, J ≤ x ∧
      atomEnergy (greenPeriod x) x + occurrenceEndpointRemainder (greenPeriod x) x ≤ B) := by
  constructor
  · rintro ⟨u, hu⟩ J
    obtain ⟨x, hx, hb⟩ := hu J
    exact ⟨x, hx, (meanGreenBudget_minimizes _ _
      (lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x)) (u x)).trans hb⟩
  · intro h
    refine ⟨fun x => atomNormalCoefficients (greenPeriod x) x, ?_⟩
    intro J
    obtain ⟨x, hx, hb⟩ := h J
    exact ⟨x, hx, (meanGreenBudget_optimal _ _
      (lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x))).trans_le hb⟩

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
