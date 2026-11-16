import RiemannResearch.Analysis.NuclearSeries
import RiemannResearch.RH.WeilDampedPrimeOperator
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose

/-!
# Nuclear certificate for the actual damped prime operator, sigma > 1

Source: user-provided prime-side factorization continuation, Priorities 1--2.
We assemble the constructed synthesis map, exact support localization,
proved arithmetic tail majorant, and Hilbert-Schmidt product expansion.

The endpoint supplies an actual absolutely summable rank-one expansion of
the two-sided operator. This is the standard nuclear characterization of
trace class on Hilbert spaces. We do not build a separate singular-value
trace-norm API, assume positivity, or infer RH.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.RH.WeilDampedSynthesis
open RiemannResearch.Analysis.SquareSummableSynthesis
open WeilDampedWeights
set_option maxHeartbeats 800000

theorem primeOperator_nuclear_representation {κ : Type*} {σ r : ℝ}
    (hσ : 1 < σ) (φ : L2) (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0)
    (b : HilbertBasis κ ℂ L2) :
    ∃ p q : ℕ × (κ ⊕ κ) → Coeff ℕ,
      Summable (fun z => ‖p z‖ * ‖q z‖) ∧
      HasSum (fun z => rankOne (p z) (q z))
        (primeOperator (by linarith : 1 / 2 < σ) φ) := by
  classical
  let hs : 1 / 2 < σ := by linarith
  have hrep (n : ℕ) :
      ∃ p q : κ → Coeff ℕ,
        Summable (fun k => ‖p k‖ * ‖q k‖) ∧
        (∑' k, ‖p k‖ * ‖q k‖) ≤
          ‖columns hs φ‖ * ‖mask (tailSet r (Real.log n)) (columns hs φ)‖ ∧
        HasSum (fun k => rankOne (p k) (q k)) (compression hs φ (Real.log n)) := by
    rw [compression_localized hs φ hφ]
    exact product_nuclear_representation (columns hs φ)
      (mask (tailSet r (Real.log n)) (columns hs φ)) (shift (-Real.log n)) b
  choose p q hc hb hpq using hrep
  have hsym (n : ℕ) := symmetrized_nuclear_representation
    (compression hs φ (Real.log n)) (p n) (q n) (hc n) (hpq n) (primePowerWeight_nonneg n)
  choose u v huv hcosteq hterm using hsym
  have hcost : Summable (fun n => ∑' k, ‖u n k‖ * ‖v n k‖) := by
    have hmajor := ((weighted_tail_summable hσ φ r).mul_left ‖columns hs φ‖).mul_left 2
    apply Summable.of_nonneg_of_le (fun n => tsum_nonneg (fun k =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _))) (fun n => ?_) hmajor
    rw [hcosteq n]
    calc
      _ ≤ 2 * primePowerWeight n *
          (‖columns hs φ‖ * ‖mask (tailSet r (Real.log n)) (columns hs φ)‖) :=
        mul_le_mul_of_nonneg_left (hb n) (mul_nonneg (by norm_num) (primePowerWeight_nonneg n))
      _ = _ := by ring
  have hflat := nuclear_series_flatten u v (primeTerm hs φ) huv hcost hterm
  exact ⟨fun z => u z.1 z.2, fun z => v z.1 z.2, hflat.1, hflat.2⟩


/-- Basis-free existence of an absolute rank-one expansion of the actual
two-sided separated prime operator. This is its nuclear trace-class certificate. -/
theorem primeOperator_nuclear {σ r : ℝ}
    (hσ : 1 < σ) (φ : L2) (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) :
    ∃ s : Set L2, ∃ p q : ℕ × (s ⊕ s) → Coeff ℕ,
      Summable (fun z => ‖p z‖ * ‖q z‖) ∧
      HasSum (fun z => rankOne (p z) (q z))
        (primeOperator (by linarith : 1 / 2 < σ) φ) := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ L2
  obtain ⟨p, q, hc, ht⟩ := primeOperator_nuclear_representation hσ φ hφ b
  exact ⟨s, p, q, hc, ht⟩

end RiemannResearch.RH.WeilDampedSynthesis
