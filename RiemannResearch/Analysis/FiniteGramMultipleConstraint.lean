import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.FiniteGramCapacity
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertConstraints
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Several prescribed sources in a finite Gram problem

Source: user-requested continuation of the Ramanujan dual structure,
23 October 2026. This generalizes the scalar constraint to an arbitrary
finite system. All signed inverse-Gram entries and the complete error
remainder are retained. Completeness of the ambient space is unnecessary.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteGramMultipleConstraint
open FiniteHilbertGram FiniteHilbertConstraints FiniteGramCapacity

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The restricted Riesz rows for an arbitrary finite source matrix. -/
def sourceRows {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (j : κ) : H := minimumVector hv (B j)

theorem sourceRows_pairing {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (c : ι → ℝ) (j : κ) :
    inner ℝ (sourceRows hv B j) (Fintype.linearCombination ℝ v c) =
      ∑ i, c i * B j i := by
  rw [real_inner_comm]
  exact inner_synthesis_minimumVector hv (B j) c

/-- The complete source Gram is `B H⁻¹ Bᵀ`; this is an entrywise identity. -/
theorem sourceRows_gram {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (i j : κ) :
    inner ℝ (sourceRows hv B i) (sourceRows hv B j) =
      ∑ k, inverseSource hv (B j) k * B i k := by
  exact sourceRows_pairing hv B (inverseSource hv (B j)) i

/-- Explicit legal coordinate-unit interpolants discharge all row-rank assumptions. -/
theorem sourceRows_independent_of_interpolants [DecidableEq κ]
    {v : ι → H} (hv : LinearIndependent ℝ v) (B : κ → ι → ℝ)
    (hd : ∀ j : κ, ∃ c : ι → ℝ,
      ∀ i : κ, (∑ k, c k * B i k) = if i = j then 1 else 0) :
    LinearIndependent ℝ (sourceRows hv B) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  obtain ⟨c, hc⟩ := hd j
  change Fintype.linearCombination ℝ (sourceRows hv B) a = 0 at ha
  have hz : inner ℝ (Fintype.linearCombination ℝ (sourceRows hv B) a)
      (Fintype.linearCombination ℝ v c) = 0 := by rw [ha, inner_zero_left]
  rw [inner_synthesis_left] at hz
  simp_rw [sourceRows_pairing, hc] at hz
  simpa using hz

/-- Lift a source multiplier through the actual inverse dictionary Gram. -/
def rowLift {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (d : κ → ℝ) : ι → ℝ :=
  ∑ j, d j • inverseSource hv (B j)

theorem rowLift_synthesis {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (d : κ → ℝ) :
    Fintype.linearCombination ℝ v (rowLift hv B d) =
      Fintype.linearCombination ℝ (sourceRows hv B) d := by
  simp only [rowLift, map_sum, map_smul, Fintype.linearCombination_apply,
    sourceRows, minimumVector, inverseSource, Finset.smul_sum]

def mismatch {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (f : H) (t : κ → ℝ) (j : κ) : ℝ :=
  t j - ∑ i, inverseCoeff hv f i * B j i

/-- The exact coefficient optimizer for arbitrary prescribed observations. -/
def coefficients {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (hB : LinearIndependent ℝ (sourceRows hv B))
    (f : H) (t : κ → ℝ) : ι → ℝ :=
  inverseCoeff hv f + rowLift hv B (inverseSource hB (mismatch hv B f t))

theorem coefficients_synthesis {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (hB : LinearIndependent ℝ (sourceRows hv B))
    (f : H) (t : κ → ℝ) :
    Fintype.linearCombination ℝ v (coefficients hv B hB f t) =
      Fintype.linearCombination ℝ v (inverseCoeff hv f) +
        minimumVector hB (mismatch hv B f t) := by
  rw [coefficients, map_add, rowLift_synthesis]
  rfl

theorem coefficients_source {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (hB : LinearIndependent ℝ (sourceRows hv B))
    (f : H) (t : κ → ℝ) (j : κ) :
    (∑ i, coefficients hv B hB f t i * B j i) = t j := by
  rw [← sourceRows_pairing hv B _ j, coefficients_synthesis, inner_add_right,
    sourceRows_pairing, minimumVector_observation]
  unfold mismatch
  ring

/-- The full cost of a finite constraint vector is its actual inverse source Gram. -/
theorem coefficients_energy {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (hB : LinearIndependent ℝ (sourceRows hv B))
    (f : H) (t : κ → ℝ) :
    ‖f - Fintype.linearCombination ℝ v (coefficients hv B hB f t)‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ v (inverseCoeff hv f)‖ ^ 2 +
        capacity hB (mismatch hv B f t) := by
  rw [residual_completion hv f]
  have hd : coefficients hv B hB f t - inverseCoeff hv f =
      rowLift hv B (inverseSource hB (mismatch hv B f t)) := by
    unfold coefficients
    abel
  rw [hd, rowLift_synthesis, capacity_eq_norm_sq]
  rfl

/-- The exact Pythagorean identity for every feasible coefficient array. -/
theorem coefficients_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (hB : LinearIndependent ℝ (sourceRows hv B))
    (f : H) (t : κ → ℝ) (c : ι → ℝ)
    (hc : ∀ j, (∑ i, c i * B j i) = t j) :
    ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ v (coefficients hv B hB f t)‖ ^ 2 +
        ‖Fintype.linearCombination ℝ v (c - coefficients hv B hB f t)‖ ^ 2 := by
  have hd : ∀ j, inner ℝ (sourceRows hv B j)
      (Fintype.linearCombination ℝ v (c - inverseCoeff hv f)) =
        mismatch hv B f t j := by
    intro j
    rw [sourceRows_pairing]
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hc, mismatch]
  have he := feasible_norm_sq_completion hB (mismatch hv B f t)
    (Fintype.linearCombination ℝ v (c - inverseCoeff hv f)) hd
  have hrem : Fintype.linearCombination ℝ v (c - inverseCoeff hv f) -
      minimumVector hB (mismatch hv B f t) =
        Fintype.linearCombination ℝ v (c - coefficients hv B hB f t) := by
    rw [map_sub, map_sub, coefficients_synthesis]
    abel
  rw [hrem, ← capacity_eq_norm_sq] at he
  rw [residual_completion hv f c, he, coefficients_energy]
  ring

theorem coefficients_isLeast {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (hB : LinearIndependent ℝ (sourceRows hv B))
    (f : H) (t : κ → ℝ) :
    IsLeast {E : ℝ | ∃ c : ι → ℝ, (∀ j, (∑ i, c i * B j i) = t j) ∧
      ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 = E}
      (‖f - Fintype.linearCombination ℝ v (coefficients hv B hB f t)‖ ^ 2) := by
  constructor
  · exact ⟨coefficients hv B hB f t, coefficients_source hv B hB f t, rfl⟩
  · rintro E ⟨c, hc, rfl⟩
    rw [coefficients_completion hv B hB f t c hc]
    exact le_add_of_nonneg_right (sq_nonneg _)

theorem coefficients_unique {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : κ → ι → ℝ) (hB : LinearIndependent ℝ (sourceRows hv B))
    (f : H) (t : κ → ℝ) (c : ι → ℝ)
    (hc : ∀ j, (∑ i, c i * B j i) = t j)
    (he : ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ v (coefficients hv B hB f t)‖ ^ 2) :
    c = coefficients hv B hB f t := by
  have ht := coefficients_completion hv B hB f t c hc
  have hz : ‖Fintype.linearCombination ℝ v (c - coefficients hv B hB f t)‖ ^ 2 = 0 := by
    linarith
  have hz' := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hcoeff : c - coefficients hv B hB f t = 0 := by
    apply hv.fintypeLinearCombination_injective
    simpa only [map_zero] using hz'
  exact sub_eq_zero.mp hcoeff

end RiemannResearch.Analysis.FiniteGramMultipleConstraint
