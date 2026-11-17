import RiemannResearch.Analysis.FiniteAtomConcentration
import RiemannResearch.RH.ExactHeadOccurrenceCriterion

/-!
# Correct atom budgets for the occurrence-reuse criterion

Source: repaired Lemma 14.6 of Christian Noack, `sdf_modified.pdf`.
All budgets refer to the actual occurrence optimizer and one shared atom
vector at each stage. The sum of the budgets is charged in full. The
cofinal budget provider is an open domain-specific hypothesis.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
open RiemannResearch.Analysis.FiniteAtomDispersion
open MobiusHeadGreen

/-- An allocated fiber budget controls actual reuse energy without a false shell scaling. -/
theorem reuseEnergy_le_fiber_budgets (P x : ℕ) (hP : 0 < P) (u b : ℕ → ℝ)
    (hb : ∀ d ∈ (freePositions P x).image (fun n => Nat.gcd n P),
      (∑ n ∈ fiber (freePositions P x) (fun n => Nat.gcd n P) d,
        (occurrenceCoefficients P x n - u d) ^ 2) ≤ b d) :
    reuseEnergy P x ≤ 5 * ∑ d ∈ (freePositions P x).image (fun n => Nat.gcd n P), b d := by
  exact (reuseEnergy_le_five_loss P x hP u).trans
    (mul_le_mul_of_nonneg_left
      (loss_le_fiber_budgets (freePositions P x) (fun n => Nat.gcd n P)
        (occurrenceCoefficients P x) u b hb) (by norm_num))

/-- Conditional RH reduction using the repaired total budget, at common cofinal stages.
No per-atom or Haar-uniform premise is silently used as a provider. -/
theorem riemannHypothesis_of_cofinal_fiber_budgets (B : ℝ) (u b : ℕ → ℕ → ℝ)
    (hdata : ∀ J : ℕ, ∃ x, J ≤ x ∧
      (∀ d ∈ (freePositions (greenPeriod x) x).image (fun n => Nat.gcd n (greenPeriod x)),
        (∑ n ∈ fiber (freePositions (greenPeriod x) x)
          (fun n => Nat.gcd n (greenPeriod x)) d,
          (occurrenceCoefficients (greenPeriod x) x n - u x d) ^ 2) ≤ b x d) ∧
      occurrenceEnergy (greenPeriod x) x +
        5 * (∑ d ∈ (freePositions (greenPeriod x) x).image
          (fun n => Nat.gcd n (greenPeriod x)), b x d) ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_bounded_occurrence_reuse B
  intro J
  obtain ⟨x, hx, hb, htotal⟩ := hdata J
  refine ⟨x, hx, ?_⟩
  exact (add_le_add le_rfl (reuseEnergy_le_fiber_budgets (greenPeriod x) x
    (lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x)) (u x) (b x) hb)).trans htotal

end RiemannResearch.RH.Pareto.ExactHeadOccurrenceProjection
