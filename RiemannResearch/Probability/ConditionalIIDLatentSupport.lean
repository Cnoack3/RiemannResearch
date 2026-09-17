/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Probability.ConditionalIIDPrimeRows

/-! Simultaneous support bounds for the actual shared-environment infinite matrix. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID

theorem path_all_coordinates_support (k : ℕ) :
    ∀ᵐ x ∂pathLaw k, ∀ i, 1 ≤ x i ∧ x i ≤ k + 1 := by
  apply ae_all_iff.mpr
  intro i
  have hm : Measure.map (fun x : Path => x i) (pathLaw k) = uniformLaw k :=
    Measure.infinitePi_map_eval _ i
  have h : ∀ᵐ n ∂Measure.map (fun x : Path => x i) (pathLaw k),
      n ∈ Finset.Icc 1 (k + 1) := by rw [hm]; exact uniformLaw_support k
  have he := (ae_map_iff (measurable_pi_apply i).aemeasurable
    (Set.to_countable {n : ℕ | n ∈ Finset.Icc 1 (k + 1)}).measurableSet).mp h
  simpa only [Finset.mem_Icc] using he

/-- One almost-sure event controls all infinitely many rows by the same latent endpoint. -/
theorem all_coordinates_support :
    ∀ᵐ ω ∂probability, ∀ i, 1 ≤ coordinate i ω ∧ coordinate i ω ≤ endpoint ω := by
  have hT : Measurable endpoint :=
    (measurable_of_countable (fun k : ℕ => k + 1)).comp latentIndex_measurable
  have hmeas : MeasurableSet {ω : Omega |
      ∀ i, 1 ≤ coordinate i ω ∧ coordinate i ω ≤ endpoint ω} := by
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_le measurable_const (coordinate_measurable i)).inter
      (measurableSet_le (coordinate_measurable i) hT)
  unfold probability
  apply Measure.ae_compProd_of_ae_ae hmeas
  apply ae_of_all
  intro k
  exact path_all_coordinates_support k

/-- On each realization only finitely many prime columns of the entire matrix can be active. -/
theorem ae_finitely_many_active_columns :
    ∀ᵐ ω ∂probability, ∃ S : Finset ℕ, ∀ i p, p ∉ S → primeRow i ω p = 0 := by
  filter_upwards [all_coordinates_support] with ω hω
  refine ⟨Finset.range (2 * endpoint ω + 1), ?_⟩
  intro i p hp
  have hlarge : 2 * endpoint ω < p := by
    simp only [Finset.mem_range] at hp
    omega
  have hsmall : 2 * coordinate i ω < p :=
    lt_of_le_of_lt (Nat.mul_le_mul_left 2 (hω i).2) hlarge
  exact Nat.factorization_eq_zero_of_lt hsmall

/-- The original integers are at least two on one common almost-sure event. -/
theorem original_integers_ge_two :
    ∀ᵐ ω ∂probability, ∀ i, 2 ≤ 2 * coordinate i ω := by
  filter_upwards [all_coordinates_support] with ω hω
  intro i
  have h := (hω i).1
  omega

/-- Prime factorization reconstructs every original integer simultaneously almost surely. -/
theorem ae_primeRows_reconstruction :
    ∀ᵐ ω ∂probability, ∀ i,
      ((2 * coordinate i ω).factorization.prod fun p e => p ^ e) = 2 * coordinate i ω := by
  filter_upwards [original_integers_ge_two] with ω hω
  intro i
  exact Nat.factorization_prod_pow_eq_self (by have := hω i; omega)

end RiemannResearch.Probability.ConditionalIID
