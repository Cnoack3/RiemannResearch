import RiemannResearch.RH.ExactHeadOccurrenceMeanBudget
import RiemannResearch.RH.ExactHeadOccurrenceRational
import RiemannResearch.RH.ExactHeadOccurrencePartition
import RiemannResearch.RH.ExactHeadOccurrenceBlocks
import RiemannResearch.RH.ExactHeadOccurrenceProjection
import RiemannResearch.RH.ExactHeadAtomOptimizer
import RiemannResearch.RH.MobiusHeadGreen
import RiemannResearch.RH.ParetoRationalWeightConvergence
import RiemannResearch.RH.ExactHeadGcdAtoms
import RiemannResearch.Analysis.FiniteProfileEnergy
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Uniform relative certificates for the complete mean--Green budget

Source: the repository's occurrence orthogonality, exact endpoint identity,
and complete elementary progression intervals. The direct trial expression
eliminates the occurrence optimizer before certification. No numerical
coefficient interval, normal-equation solve, or cofinal provider is assumed.
The remaining arithmetic bound is explicitly conditional.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.RH.ExactHeadGcdAtoms
open ExactHeadAtomOptimizer MobiusHeadGreen

/-- A positive linear functional of the weights for a fixed legal atom trial.
It includes the full target trial and the explicit endpoint loss. -/
def weightedMeanGreenBudget (P x : ℕ) (w u : ℕ → ℝ) : ℝ :=
  energy (Finset.Icc 1 (P-1)) w (target P - synthesis P (upperDivisors P x) u) +
    ∑ i ∈ Finset.range (freePositions P x).card,
      ∑ r ∈ Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)),
        w r * ((target P (occurrenceBoundary P x (i+1)-1) - target P r) *
          (target P r - target P (occurrenceBoundary P x i)))

/-- Exact equality to the original mean budget plus the complete Green residual. -/
theorem weightedMeanGreenBudget_complete (P x : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    weightedMeanGreenBudget P x (progressionWeight P) u = meanGreenBudget P x u := by
  rw [meanGreenBudget_eq_target_trial P x hP]
  simp only [weightedMeanGreenBudget, occurrenceEndpointRemainder, mul_assoc]

theorem weightedMeanGreenBudget_mono (P x : ℕ) (hP : 0 < P) (w v u : ℕ → ℝ)
    (hw : ∀ r ∈ Finset.Icc 1 (P-1), w r ≤ v r) :
    weightedMeanGreenBudget P x w u ≤ weightedMeanGreenBudget P x v u := by
  apply add_le_add
  · exact Finset.sum_le_sum (fun r hr =>
      mul_le_mul_of_nonneg_right (hw r hr) (sq_nonneg _))
  · apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro r hr
    have hr' := Finset.mem_Ico.mp hr
    have ha := occurrenceBoundary_pos P x i hP
    have hb := occurrenceBoundary_le_period P x (i+1)
    have hmem : r ∈ Finset.Icc 1 (P-1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact mul_le_mul_of_nonneg_right (hw r hmem)
      (mul_nonneg
        (sub_nonneg.mpr (occurrence_target_mono P (by omega)))
        (sub_nonneg.mpr (occurrence_target_mono P hr'.1)))

theorem weightedMeanGreenBudget_smul (P x : ℕ) (w u : ℕ → ℝ) (a : ℝ) :
    weightedMeanGreenBudget P x (fun r => a * w r) u =
      a * weightedMeanGreenBudget P x w u := by
  simp only [weightedMeanGreenBudget, energy, mul_add, Finset.mul_sum, mul_assoc]

/-- Soundness of complete upper weights holds even at depth zero. -/
theorem meanGreenBudget_le_upper (P x K : ℕ) (hP : 0 < P) (u : ℕ → ℝ) :
    meanGreenBudget P x u ≤
      weightedMeanGreenBudget P x
        (fun r => ((elementaryProgressionInterval P r K).hi : ℝ)) u := by
  rw [← weightedMeanGreenBudget_complete P x hP u]
  exact weightedMeanGreenBudget_mono P x hP _ _ u (fun r hr =>
    (elementaryProgressionInterval_contains P r K hP (Finset.mem_Icc.mp hr).1).2)

/-- The same fixed depth works at every period and cutoff. This controls the
relative certification loss; it does not assert a uniform bound for the objective. -/
theorem upper_meanGreenBudget_le_factor (P x K : ℕ) (hP : 0 < P) (hK : 0 < K)
    (u : ℕ → ℝ) :
    weightedMeanGreenBudget P x
        (fun r => ((elementaryProgressionInterval P r K).hi : ℝ)) u ≤
      (1 + 1 / (K : ℝ)^2) * meanGreenBudget P x u := by
  calc
    _ ≤ weightedMeanGreenBudget P x
        (fun r => (1 + 1 / (K : ℝ)^2) * progressionWeight P r) u := by
      apply weightedMeanGreenBudget_mono P x hP
      intro r hr
      obtain ⟨hr1, hrP⟩ := Finset.mem_Icc.mp hr
      exact (elementaryProgressionInterval_upper_relative P r K hP hr1
        (by omega) hK).2
    _ = _ := by rw [weightedMeanGreenBudget_smul, weightedMeanGreenBudget_complete P x hP]

/-- Exact rational atom synthesis; all signs of the trial are retained. -/
def rationalAtomSynthesis (P x : ℕ) (u : ℕ → ℚ) (r : ℕ) : ℚ :=
  ∑ d ∈ upperDivisors P x, u d *
    (((Finset.Icc 1 r).filter (fun n => Nat.gcd n P = d)).card : ℚ)

theorem rationalAtomSynthesis_cast (P x : ℕ) (u : ℕ → ℚ) (r : ℕ) :
    (rationalAtomSynthesis P x u r : ℝ) =
      synthesis P (upperDivisors P x) (fun d => (u d : ℝ)) r := by
  simp [rationalAtomSynthesis, synthesis, atom]

/-- A finite rational upper certificate for the entire combined objective.
All infinite progression tails are enclosed by the certified upper weights. -/
def rationalMeanGreenBudget (P x K : ℕ) (u : ℕ → ℚ) : ℚ :=
  (∑ r ∈ Finset.Icc 1 (P-1), (elementaryProgressionInterval P r K).hi *
    (rationalTarget P r - rationalAtomSynthesis P x u r)^2) +
    ∑ i ∈ Finset.range (freePositions P x).card,
      ∑ r ∈ Finset.Ico (occurrenceBoundary P x i) (occurrenceBoundary P x (i+1)),
        (elementaryProgressionInterval P r K).hi *
          ((rationalTarget P (occurrenceBoundary P x (i+1)-1) - rationalTarget P r) *
            (rationalTarget P r - rationalTarget P (occurrenceBoundary P x i)))

theorem rationalMeanGreenBudget_cast (P x K : ℕ) (u : ℕ → ℚ) :
    (rationalMeanGreenBudget P x K u : ℝ) =
      weightedMeanGreenBudget P x
        (fun r => ((elementaryProgressionInterval P r K).hi : ℝ))
        (fun d => (u d : ℝ)) := by
  simp only [rationalMeanGreenBudget, weightedMeanGreenBudget, energy, Pi.sub_apply,
    Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_sub,
    rationalTarget_cast, rationalAtomSynthesis_cast]

theorem rationalMeanGreenBudget_sound (P x K : ℕ) (hP : 0 < P) (u : ℕ → ℚ) :
    meanGreenBudget P x (fun d => (u d : ℝ)) ≤ (rationalMeanGreenBudget P x K u : ℝ) := by
  rw [rationalMeanGreenBudget_cast]
  exact meanGreenBudget_le_upper P x K hP _

/-- Uniform two-sided multiplicative enclosure, with no coefficient-error term. -/
theorem rationalMeanGreenBudget_relative (P x K : ℕ) (hP : 0 < P) (hK : 0 < K)
    (u : ℕ → ℚ) :
    meanGreenBudget P x (fun d => (u d : ℝ)) ≤ (rationalMeanGreenBudget P x K u : ℝ) ∧
      (rationalMeanGreenBudget P x K u : ℝ) ≤
        (1 + 1 / (K : ℝ)^2) * meanGreenBudget P x (fun d => (u d : ℝ)) := by
  rw [rationalMeanGreenBudget_cast]
  exact ⟨meanGreenBudget_le_upper P x K hP _,
    upper_meanGreenBudget_le_factor P x K hP hK _⟩

/-- At fixed positive depth, a prescribed rational correction family has a
bounded cofinal certificate exactly when its true combined budget is bounded.
The common bound itself is not supplied by this equivalence. -/
theorem cofinal_rationalMeanGreenBudget_iff (K : ℕ) (hK : 0 < K) (u : ℕ → ℕ → ℚ) :
    (∃ B : ℝ, ∀ J : ℕ, ∃ x, J ≤ x ∧
      (rationalMeanGreenBudget (greenPeriod x) x K (u x) : ℝ) ≤ B) ↔
    (∃ B : ℝ, ∀ J : ℕ, ∃ x, J ≤ x ∧
      meanGreenBudget (greenPeriod x) x (fun d => (u x d : ℝ)) ≤ B) := by
  constructor
  · rintro ⟨B, h⟩
    refine ⟨B, ?_⟩
    intro J
    obtain ⟨x, hx, hb⟩ := h J
    exact ⟨x, hx, (rationalMeanGreenBudget_sound _ _ K
      (lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x)) (u x)).trans hb⟩
  · rintro ⟨B, h⟩
    refine ⟨(1 + 1 / (K : ℝ)^2) * B, ?_⟩
    intro J
    obtain ⟨x, hx, hb⟩ := h J
    refine ⟨x, hx, (rationalMeanGreenBudget_relative _ _ K
      (lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x)) hK (u x)).2.trans ?_⟩
    exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- A finite rational inequality certifies an actual combined-budget upper bound. -/
theorem meanGreenBudget_le_of_rational_certificate (P x K : ℕ) (hP : 0 < P)
    (u : ℕ → ℚ) (B : ℚ) (h : rationalMeanGreenBudget P x K u ≤ B) :
    meanGreenBudget P x (fun d => (u d : ℝ)) ≤ (B : ℝ) :=
  (rationalMeanGreenBudget_sound P x K hP u).trans ((Rat.cast_le (K := ℝ)).2 h)

/-- Conditional RH consumer for full rational certificates at common cofinal stages.
This is not an assertion that a uniformly bounded family exists. -/
theorem riemannHypothesis_of_cofinal_rational_mean_green_budget
    (B : ℝ) (K : ℕ) (u : ℕ → ℕ → ℚ)
    (hdata : ∀ J : ℕ, ∃ x, J ≤ x ∧
      (rationalMeanGreenBudget (greenPeriod x) x K (u x) : ℝ) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_mean_green_budget B (fun x d => (u x d : ℝ))
  intro J
  obtain ⟨x, hx, hb⟩ := hdata J
  exact ⟨x, hx, (rationalMeanGreenBudget_sound _ _ K
    (lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x)) (u x)).trans hb⟩

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
