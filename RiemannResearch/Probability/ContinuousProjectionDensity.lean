import RiemannResearch.Probability.ContinuousProjectionLaw
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Normalization of continuous projection determinantal measures

The squared Slater determinant of a finite orthonormal family integrates to
`n!`. The proof expands both determinants, uses Fubini on coordinate products,
and then cancels the off-diagonal permutations by orthogonality. This proves
normalization of the continuous projection law without assuming it.

Source: the finite-rank projection construction in Hough, Krishnapur, Peres,
and Virág, *Determinantal Processes and Independence*, Probability Surveys 3
(2006), Section 2, https://doi.org/10.1214/154957806000000078. The proof below
is a direct finite determinant expansion and product-integration argument.
-/

noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace ProbabilityTheory.ContinuousProjectionDPP

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ] {n : ℕ}

private def permutationSign (σ : Equiv.Perm (Fin n)) : ℂ :=
  ((Equiv.Perm.sign σ : ℤ) : ℂ)

private def permutationCross (ψ : Fin n → X → ℂ)
    (σ τ : Equiv.Perm (Fin n)) (x : Fin n → X) : ℂ :=
  ∏ j, conj (ψ (σ j) (x j)) * ψ (τ j) (x j)

private theorem squaredDet_expansion (ψ : Fin n → X → ℂ) (x : Fin n → X) :
    (squaredDet ψ x : ℂ) = ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      (permutationSign σ * permutationSign τ) * permutationCross ψ σ τ x := by
  have hnorm : (squaredDet ψ x : ℂ) =
      conj (evalMatrix ψ x).det * (evalMatrix ψ x).det := by
    simp [squaredDet, Complex.conj_mul', Complex.ofReal_pow]
  rw [hnorm]
  simp only [Matrix.det_apply', map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  simp only [map_mul, map_intCast, map_prod, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  simp only [permutationSign, permutationCross, evalMatrix, Finset.prod_mul_distrib]
  ring

private theorem integrable_permutationCross (ψ : Fin n → X → ℂ)
    (hc : ∀ i j, Integrable (fun t => conj (ψ i t) * ψ j t) μ)
    (σ τ : Equiv.Perm (Fin n)) :
    Integrable (permutationCross ψ σ τ) (Measure.pi fun _ : Fin n => μ) :=
  Integrable.fintype_prod (fun j => hc (σ j) (τ j))

private theorem integral_permutationCross (ψ : Fin n → X → ℂ)
    (ho : ∀ i j, (∫ t, conj (ψ i t) * ψ j t ∂μ) = if i = j then 1 else 0)
    (σ τ : Equiv.Perm (Fin n)) :
    (∫ x, permutationCross ψ σ τ x ∂(Measure.pi fun _ : Fin n => μ)) =
      if σ = τ then 1 else 0 := by
  classical
  unfold permutationCross
  rw [integral_fintype_prod_eq_prod (fun j t => conj (ψ (σ j) t) * ψ (τ j) t)]
  simp_rw [ho]
  by_cases h : σ = τ
  · subst τ
    simp
  · obtain ⟨j, hj⟩ : ∃ j, σ j ≠ τ j := by
      by_contra hn
      push Not at hn
      exact h (Equiv.ext hn)
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

private theorem integrable_squaredDet_complex (ψ : Fin n → X → ℂ)
    (hc : ∀ i j, Integrable (fun t => conj (ψ i t) * ψ j t) μ) :
    Integrable (fun x => (squaredDet ψ x : ℂ)) (Measure.pi fun _ : Fin n => μ) := by
  simp_rw [squaredDet_expansion]
  apply integrable_finsetSum
  intro σ hσ
  apply integrable_finsetSum
  intro τ hτ
  exact (integrable_permutationCross ψ hc σ τ).const_mul _

/-- Integrability of the squared determinant follows from integrability of all
cross-products of the feature functions. -/
theorem integrable_squaredDet_of_cross (ψ : Fin n → X → ℂ)
    (hc : ∀ i j, Integrable (fun t => conj (ψ i t) * ψ j t) μ) :
    Integrable (squaredDet ψ) (Measure.pi fun _ : Fin n => μ) := by
  simpa using (integrable_squaredDet_complex ψ hc).re

private theorem integral_squaredDet_complex (ψ : Fin n → X → ℂ)
    (hc : ∀ i j, Integrable (fun t => conj (ψ i t) * ψ j t) μ)
    (ho : ∀ i j, (∫ t, conj (ψ i t) * ψ j t ∂μ) = if i = j then 1 else 0) :
    (∫ x, (squaredDet ψ x : ℂ) ∂(Measure.pi fun _ : Fin n => μ)) = n.factorial := by
  classical
  simp_rw [squaredDet_expansion]
  rw [integral_finsetSum]
  · calc
      _ = ∑ _σ : Equiv.Perm (Fin n), (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [integral_finsetSum]
        · simp_rw [integral_const_mul, integral_permutationCross ψ ho]
          simp only [mul_ite, mul_one, mul_zero]
          rw [Finset.sum_eq_single σ]
          · simp only [ite_true, permutationSign]
            have hs := congrArg (fun u : ℤˣ => ((u : ℤ) : ℂ))
              (Int.units_mul_self (Equiv.Perm.sign σ))
            simpa only [Units.val_mul, Int.cast_mul, Units.val_one, Int.cast_one] using hs
          · intro τ hτ hne
            simp [Ne.symm hne]
          · simp
        · intro τ hτ
          exact (integrable_permutationCross ψ hc σ τ).const_mul _
      _ = n.factorial := by simp [Fintype.card_perm]
  · intro σ hσ
    apply integrable_finsetSum
    intro τ hτ
    exact (integrable_permutationCross ψ hc σ τ).const_mul _

/-- The Slater determinant of an orthonormal family has squared integral `n!`.
This is the orthonormal case of Andréief's identity. -/
theorem integral_squaredDet_of_cross (ψ : Fin n → X → ℂ)
    (hc : ∀ i j, Integrable (fun t => conj (ψ i t) * ψ j t) μ)
    (ho : ∀ i j, (∫ t, conj (ψ i t) * ψ j t ∂μ) = if i = j then 1 else 0) :
    (∫ x, squaredDet ψ x ∂(Measure.pi fun _ : Fin n => μ)) = n.factorial := by
  have hi := integral_squaredDet_complex ψ hc ho
  rw [integral_complex_ofReal] at hi
  exact_mod_cast hi

/-- The mixed products required by determinant expansion are integrable by
Hölder with exponents two and two. -/
theorem integrable_cross_of_memLp (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ) (i j : Fin n) :
    Integrable (fun t => conj (ψ i t) * ψ j t) μ := by
  have hi : MemLp (fun t => conj (ψ i t)) 2 μ :=
    (hψ i).congr_norm
      (Complex.continuous_conj.comp_aestronglyMeasurable (hψ i).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => (Complex.norm_conj (ψ i t)).symm)
  exact hi.integrable_mul (hψ j)

/-- The squared Slater determinant of square-integrable features is integrable. -/
theorem integrable_squaredDet (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ) :
    Integrable (squaredDet ψ) (Measure.pi fun _ : Fin n => μ) :=
  integrable_squaredDet_of_cross ψ (integrable_cross_of_memLp ψ hψ)

/-- Actual determinant normalization for an orthonormal square-integrable family. -/
theorem integral_squaredDet (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ t, conj (ψ i t) * ψ j t ∂μ) = if i = j then 1 else 0) :
    (∫ x, squaredDet ψ x ∂(Measure.pi fun _ : Fin n => μ)) = n.factorial :=
  integral_squaredDet_of_cross ψ (integrable_cross_of_memLp ψ hψ) ho

/-- Every finite orthonormal square-integrable family defines an actual
continuous projection determinantal probability measure. -/
theorem isProbabilityMeasure_law_of_orthonormal (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ t, conj (ψ i t) * ψ j t ∂μ) = if i = j then 1 else 0) :
    IsProbabilityMeasure (law μ ψ) :=
  isProbabilityMeasure_law (integrable_squaredDet ψ hψ) (integral_squaredDet ψ hψ ho)

end ProbabilityTheory.ContinuousProjectionDPP
