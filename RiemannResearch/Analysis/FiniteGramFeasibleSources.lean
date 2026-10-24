import RiemannResearch.Analysis.FiniteGramMultipleConstraint
import RiemannResearch.Analysis.FiniteFeasibleGramRepair
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arbitrary feasible source constraints, including singular systems

Source: user-requested continuation of the Ramanujan dual structure,
23 October 2026. This extends the multiple-source optimizer to dependent
constraint rows. Feasibility supplies a source-Gram normal solution.
The original dictionary remains independent, so its optimizing coefficient
array is unique even when the source multipliers are not unique.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteGramFeasibleSources
open FiniteHilbertGram FiniteHilbertConstraints FiniteGramCapacity
open FiniteGramMultipleConstraint FiniteFeasibleGramRepair

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A source normal solution produces actual dictionary coefficients. -/
def normalCoefficients {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (f : H) (d : κ → ℝ) : ι → ℝ :=
  inverseCoeff hv f + rowLift hv B d

theorem normalCoefficients_synthesis {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (f : H) (d : κ → ℝ) :
    Fintype.linearCombination ℝ v (normalCoefficients hv B f d) =
      Fintype.linearCombination ℝ v (inverseCoeff hv f) +
        Fintype.linearCombination ℝ (sourceRows hv B) d := by
  rw [normalCoefficients, map_add, rowLift_synthesis]

/-- Feasibility constructs a normal solution without row independence. -/
theorem normal_exists {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (f : H) (t : κ → ℝ)
    (hf : ∃ c : ι → ℝ, ∀ j, (∑ i, c i * B j i) = t j) :
    ∃ d : κ → ℝ, ∀ j,
      inner ℝ (sourceRows hv B j)
        (Fintype.linearCombination ℝ (sourceRows hv B) d) = mismatch hv B f t j := by
  obtain ⟨c, hc⟩ := hf
  apply exists_normal_of_feasible (sourceRows hv B) (mismatch hv B f t)
    (Fintype.linearCombination ℝ v (c - inverseCoeff hv f))
  intro j
  rw [sourceRows_pairing]
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hc, mismatch]

theorem normalCoefficients_source {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (f : H) (t d : κ → ℝ)
    (hd : ∀ j, inner ℝ (sourceRows hv B j)
      (Fintype.linearCombination ℝ (sourceRows hv B) d) = mismatch hv B f t j)
    (j : κ) : (∑ i, normalCoefficients hv B f d i * B j i) = t j := by
  rw [← sourceRows_pairing hv B _ j, normalCoefficients_synthesis,
    inner_add_right, sourceRows_pairing, hd]
  unfold mismatch
  ring

/-- The signed normal pairing is the exact nonnegative constrained cost. -/
theorem normalCoefficients_energy {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (f : H) (t d : κ → ℝ)
    (hd : ∀ j, inner ℝ (sourceRows hv B j)
      (Fintype.linearCombination ℝ (sourceRows hv B) d) = mismatch hv B f t j) :
    ‖f - Fintype.linearCombination ℝ v (normalCoefficients hv B f d)‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ v (inverseCoeff hv f)‖ ^ 2 +
        ∑ j, d j * mismatch hv B f t j := by
  rw [residual_completion hv f]
  have he : normalCoefficients hv B f d - inverseCoeff hv f = rowLift hv B d := by
    unfold normalCoefficients
    abel
  rw [he, rowLift_synthesis, normal_energy (sourceRows hv B) (mismatch hv B f t) d hd]

/-- Full constrained completion is valid even for redundant or zero rows. -/
theorem normalCoefficients_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (f : H) (t d : κ → ℝ)
    (hd : ∀ j, inner ℝ (sourceRows hv B j)
      (Fintype.linearCombination ℝ (sourceRows hv B) d) = mismatch hv B f t j)
    (c : ι → ℝ) (hc : ∀ j, (∑ i, c i * B j i) = t j) :
    ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ v (normalCoefficients hv B f d)‖ ^ 2 +
        ‖Fintype.linearCombination ℝ v (c - normalCoefficients hv B f d)‖ ^ 2 := by
  have hobs : ∀ j, inner ℝ (sourceRows hv B j)
      (Fintype.linearCombination ℝ v (c - inverseCoeff hv f)) = mismatch hv B f t j := by
    intro j
    rw [sourceRows_pairing]
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hc, mismatch]
  have he := feasible_completion (sourceRows hv B) (mismatch hv B f t) d hd
    (Fintype.linearCombination ℝ v (c - inverseCoeff hv f)) hobs
  have hrem : Fintype.linearCombination ℝ v (c - inverseCoeff hv f) -
      Fintype.linearCombination ℝ (sourceRows hv B) d =
        Fintype.linearCombination ℝ v (c - normalCoefficients hv B f d) := by
    rw [map_sub, map_sub, normalCoefficients_synthesis]
    abel
  rw [hrem, normal_energy (sourceRows hv B) (mismatch hv B f t) d hd] at he
  rw [residual_completion hv f c, he, normalCoefficients_energy hv B f t d hd]
  ring

theorem normalCoefficients_unique {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (f : H) (t d : κ → ℝ)
    (hd : ∀ j, inner ℝ (sourceRows hv B j)
      (Fintype.linearCombination ℝ (sourceRows hv B) d) = mismatch hv B f t j)
    (c : ι → ℝ) (hc : ∀ j, (∑ i, c i * B j i) = t j)
    (he : ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ v (normalCoefficients hv B f d)‖ ^ 2) :
    c = normalCoefficients hv B f d := by
  have ht := normalCoefficients_completion hv B f t d hd c hc
  have hz : ‖Fintype.linearCombination ℝ v (c - normalCoefficients hv B f d)‖ ^ 2 = 0 := by
    linarith
  have hz' := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hcoeff : c - normalCoefficients hv B f d = 0 := by
    apply hv.fintypeLinearCombination_injective
    simpa only [map_zero] using hz'
  exact sub_eq_zero.mp hcoeff

end RiemannResearch.Analysis.FiniteGramFeasibleSources
