import RiemannResearch.Analysis.ActualInghamGabrielComparable
import RiemannResearch.Analysis.ActualInghamHorizontalBoundary
import RiemannResearch.Analysis.ActualInghamLittlewoodQuantitative

/-!
# Actual Littlewood count on intervals with a fixed or moving lower height

The horizontal Jensen bound and the undamped interpolated left moment are
applied to the same outward-perturbed rectangle, following the counting
scheme in Chourasiya and Simonič, <https://arxiv.org/html/2507.15184v2>.
-/

noncomputable section
open Set
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open InghamMollifier

theorem exists_actual_littlewood_comparable_count :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : ℕ}, 72 ≤ X → ∀ {H T σ : ℝ}, 4 ≤ H → H ≤ T →
      (X : ℝ) ≤ T → T ≤ 2 * (X : ℝ) → 1 ≤ Real.log T →
      1 / 2 + 2 / Real.log T ≤ σ → σ ≤ 1 →
      ∃ a ∈ Ioo (σ - 2 / Real.log T) (σ - 1 / Real.log T),
        let β := 1 + 1 / Real.log (X : ℝ)
        let θ := (a - 1 / 2) / (β - 1 / 2)
        let A := 3 * (1 - θ) / (3 - θ)
        rightInclusiveCount T σ - rightInclusiveCount H σ ≤
          C * Real.log T * (T ^ A * (Real.log T) ^ (1 + A) + Real.log T) := by
  obtain ⟨CM, hCM, hm⟩ := exists_actual_gabriel_comparable_moment
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 3)
  obtain ⟨CA, hCA, ha⟩ := exists_zetaDetector_horizontal_difference_bound
  exact littlewood_count_of_comparable_moment_and_argument hCM hCA hm ha

end RiemannResearch.Analysis.ActualZeroOrdinate
