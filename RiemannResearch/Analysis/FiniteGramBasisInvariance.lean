import RiemannResearch.Analysis.FiniteGramCapacity

/-!
# Capacity is unchanged by an exact change of observation basis

Source: user-provided Ramanujan change-of-basis argument, 22 September 2026.
This module supplies the capacity-invariance step for the Pareto q_N calculation.
Both capacities use the existing Hilbert Gram inverse.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.Analysis.FiniteHilbertConstraints

variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem capacity_eq_of_same_observations
    {v : ι → H} {w : κ → H}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (a : ι → ℝ) (b : κ → ℝ)
    (hobs : ∀ z : H,
      (∀ i, inner ℝ (v i) z = a i) ↔
      (∀ j, inner ℝ (w j) z = b j)) :
    capacity hv a = capacity hw b := by
  rw [capacity_eq_norm_sq, capacity_eq_norm_sq]
  apply le_antisymm
  · exact minimumVector_minimizes hv a (minimumVector hw b)
      ((hobs _).mpr (minimumVector_observation hw b))
  · exact minimumVector_minimizes hw b (minimumVector hv a)
      ((hobs _).mp (minimumVector_observation hv a))

omit [Fintype ι] in
theorem observation_of_mem_span
    (v : ι → H) (ℓ : H →ₗ[ℝ] ℝ) (z : H)
    (hz : ∀ i, inner ℝ (v i) z = ℓ (v i))
    {x : H} (hx : x ∈ Submodule.span ℝ (Set.range v)) :
    inner ℝ x z = ℓ x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hz i
  | zero => simp
  | add x y hx hy hix hiy =>
      simp only [inner_add_left, map_add, hix, hiy]
  | smul c x hx hi =>
      simp only [real_inner_smul_left, map_smul, smul_eq_mul, hi]

theorem capacity_evaluation_eq_of_span_eq
    {v : ι → H} {w : κ → H}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w)
    (ℓ : H →ₗ[ℝ] ℝ)
    (hspan : Submodule.span ℝ (Set.range v) =
      Submodule.span ℝ (Set.range w)) :
    capacity hv (fun i => ℓ (v i)) =
      capacity hw (fun j => ℓ (w j)) := by
  apply capacity_eq_of_same_observations hv hw
  intro z
  constructor
  · intro hz j
    apply observation_of_mem_span v ℓ z hz
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self j)
  · intro hz i
    apply observation_of_mem_span w ℓ z hz
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)

end RiemannResearch.Analysis.FiniteGramCapacity
