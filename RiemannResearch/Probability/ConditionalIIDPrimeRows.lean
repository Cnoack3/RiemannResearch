/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Probability.ConditionalIIDUniformMoments
import Mathlib.Data.Nat.Factorization.Basic

/-! Conditional independence of measurable row functions, including full exponent vectors. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID

/-- Conditioning on the positive endpoint is exactly conditioning on its predecessor index. -/
theorem endpoint_sigma_eq :
    MeasurableSpace.comap endpoint (inferInstance : MeasurableSpace ℕ) = latentSigma := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(fun n : ℕ => n + 1) ⁻¹' t, (Set.to_countable _).measurableSet, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Nat.pred ⁻¹' t, (Set.to_countable _).measurableSet, ?_⟩
    ext ω
    simp [endpoint, latentIndex]

/-- Conditional independence is preserved by a measurable transformation of each whole row. -/
theorem coordinate_functions_iCondIndepFun {β : ℕ → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)]
    (F : ∀ i, ℕ → β i) (hF : ∀ i, Measurable (F i)) :
    iCondIndepFun latentSigma latentSigma_le
      (fun i ω => F i (coordinate i ω)) probability := by
  apply (iCondIndepFun_iff_condExp_inter_preimage_eq_mul
    (fun i => mβ i) (fun i ω => F i (coordinate i ω))
    (fun i => (hF i).comp (coordinate_measurable i))).2
  intro I sets hsets
  have h := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul
    (fun _ : ℕ => inferInstance) coordinate coordinate_measurable).1
      coordinates_iCondIndepFun I
      (sets := fun i => F i ⁻¹' sets i) (fun i hi => (hsets i hi).preimage (hF i))
  exact h

/-- Full prime-exponent row of the original integer N = 2K (nonprime columns are zero). -/
def exponentRow (n : ℕ) : ℕ → ℕ := (2 * n).factorization

abbrev primeRow (i : ℕ) (ω : Omega) : ℕ → ℕ := exponentRow (coordinate i ω)

theorem exponentRow_measurable : Measurable exponentRow := measurable_of_countable _

theorem primeRow_measurable (i : ℕ) : Measurable (primeRow i) :=
  exponentRow_measurable.comp (coordinate_measurable i)

/-- Every exponent row is finitely supported, without any distributional assumption. -/
theorem exponentRow_finite_support (n : ℕ) : (Function.support (exponentRow n)).Finite :=
  (2 * n).factorization.finite_support

/-- Actual conditional independence of the entire infinite exponent vectors. -/
theorem primeRows_iCondIndepFun :
    iCondIndepFun latentSigma latentSigma_le primeRow probability :=
  coordinate_functions_iCondIndepFun (fun _ => exponentRow) (fun _ => exponentRow_measurable)

/-- Identical conditional event laws for full exponent rows; no independence of prime columns. -/
theorem primeRow_conditional_event (i : ℕ) (B : Set (ℕ → ℕ)) (hB : MeasurableSet B) :
    probability[(primeRow i ⁻¹' B).indicator (fun _ : Omega => (1 : ℝ)) | latentSigma]
      =ᵐ[probability] (fun ω => (uniformLaw (latentIndex ω)).real (exponentRow ⁻¹' B)) := by
  exact conditional_coordinate_event i (exponentRow ⁻¹' B)

/-- The formal conditional iid statement is unchanged when the conditioning variable is T itself. -/
theorem primeRows_iCondIndepFun_endpoint :
    iCondIndepFun (MeasurableSpace.comap endpoint (inferInstance : MeasurableSpace ℕ))
      (by rw [endpoint_sigma_eq]; exact latentSigma_le) primeRow probability := by
  simpa only [endpoint_sigma_eq] using primeRows_iCondIndepFun

end RiemannResearch.Probability.ConditionalIID
