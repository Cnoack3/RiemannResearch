/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTorusHomogeneous
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

import RiemannResearch.Analysis.PrimeTorusFourierProducts
import RiemannResearch.Analysis.PrimeTorusPlancherel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-! # Homogeneous prime-torus moments

Source: user-provided Montgomery handoff, Section 3. Character orthogonality
and Parseval evaluate the fourth moment and preserve all even homogeneous
moments under the existing signed axis density. The tuple expansion includes
all repeated modes; no independence assumption is imposed on actual zeros.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
namespace RiemannResearch.Analysis.PrimeTorusHaar
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem single_one_injective :
    Function.Injective (fun i : ι => (Pi.single i (1 : ℤ) : ι → ℤ)) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  simpa [Pi.single_apply, hij, Ne.symm hij] using hi

theorem single_one_add_eq_iff (i j k l : ι) :
    (Pi.single i (1 : ℤ) + Pi.single j 1 : ι → ℤ) =
      Pi.single k 1 + Pi.single l 1 ↔
      (i=k ∧ j=l) ∨ (i=l ∧ j=k) := by
  constructor
  · intro h
    have hi := congrFun h i
    have hj := congrFun h j
    by_cases hik : i=k <;> by_cases hil : i=l <;>
      by_cases hjk : j=k <;> by_cases hjl : j=l <;>
      by_cases hij : i=j <;>
      simp_all [Pi.single_apply, eq_comm, single_one_injective.eq_iff]
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · exact add_comm _ _

theorem character_add (k l : ι → ℤ) :
    character (k+l) = character k * character l := by
  simp only [character_eq_mFourier]
  ext x
  exact UnitAddTorus.mFourier_add

theorem haarIntegral_character_mul_star (k l : ι → ℤ) :
    haarIntegral (character k * star (character l)) = if k=l then 1 else 0 := by
  rw [character_mul_star, haarIntegral_character_eq]
  simp only [sub_eq_zero]

theorem haarIntegral_finite_gram {κ : Type*} [Fintype κ]
    (b : κ → ℂ) (k : κ → ι → ℤ) :
    haarIntegral ((∑ i, b i • character (k i)) * star (∑ i, b i • character (k i))) =
      ∑ i, ∑ j, if k i = k j then b i * conj (b j) else 0 := by
  classical
  simp only [star_sum, star_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, map_sum, map_smul, smul_eq_mul,
    haarIntegral_character_mul_star, Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> simp_all [mul_comm]

def linearPolynomial (b : ι → ℂ) : C(Torus ι, ℂ) :=
  ∑ i, b i • character (Pi.single i 1)

theorem linearPolynomial_square (b : ι → ℂ) :
    (linearPolynomial b)^2 =
      ∑ ij : ι × ι, (b ij.1*b ij.2) •
        character (Pi.single ij.1 1 + Pi.single ij.2 1) := by
  rw [linearPolynomial, pow_two, Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul, character_add]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [mul_comm]


theorem haar_fourth_moment_algebra (b : ι → ℂ) :
    haarIntegral ((linearPolynomial b)^2 * star ((linearPolynomial b)^2)) =
      2 * (∑ i, b i * conj (b i))^2 - ∑ i, (b i * conj (b i))^2 := by
  have entry (i j k l : ι) :
      (if (i=k ∧ j=l) ∨ (i=l ∧ j=k)
        then (b i*b j)*conj (b k*b l) else 0) =
      (if k=i then if l=j then (b i*conj (b i))*(b j*conj (b j)) else 0 else 0) +
      (if k=j then if l=i then (b i*conj (b i))*(b j*conj (b j)) else 0 else 0) -
      (if i=j then if k=i then if l=i then (b i*conj (b i))^2 else 0 else 0 else 0) := by
    by_cases hik : i=k <;> by_cases hil : i=l <;>
      by_cases hjk : j=k <;> by_cases hjl : j=l <;> by_cases hij : i=j <;>
      simp_all [eq_comm, map_mul] <;> ring
  rw [linearPolynomial_square, haarIntegral_finite_gram]
  simp only [Fintype.sum_prod_type, single_one_add_eq_iff]
  simp_rw [entry]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem haar_fourth_moment (b : ι → ℂ) :
    haarIntegral ((linearPolynomial b)^2 * star ((linearPolynomial b)^2)) =
      ((2 * (∑ i, ‖b i‖^2)^2 - ∑ i, ‖b i‖^4 : ℝ) : ℂ) := by
  rw [haar_fourth_moment_algebra]
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring


theorem haarIntegral_homogeneous_family_density_zero {κ : Type*} [Fintype κ]
    (c a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1)
    (b : κ → ℂ) (k : κ → ι → ℤ) (d : ℤ) (hd : ∀ j, ∑ i, k j i = d) :
    haarIntegral ((∑ j, b j • character (k j)) *
      star (∑ j, b j • character (k j)) * density c a) = 0 := by
  classical
  simp only [star_sum, star_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro l hl
  rw [haarIntegral_character_mul_star_density_of_degree c a ha ha1 (k l) (k j)
    ((hd l).trans (hd j).symm)]
  simp

theorem character_sum {κ : Type*} (s : Finset κ) (k : κ → ι → ℤ) :
    character (∑ j ∈ s, k j) = ∏ j ∈ s, character (k j) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext x; simp [character_apply, fourier_zero]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj, character_add, ih]

theorem polynomial_power_expansion {κ : Type*} [Fintype κ]
    (b : κ → ℂ) (k : κ → ι → ℤ) (r : ℕ) :
    (∑ j, b j • character (k j))^r =
      ∑ u : Fin r → κ, (∏ j, b (u j)) • character (∑ j, k (u j)) := by
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.prod_smul, character_sum]

theorem haarIntegral_homogeneous_power_density_zero {κ : Type*} [Fintype κ]
    (c a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1)
    (b : κ → ℂ) (k : κ → ι → ℤ) (d : ℤ)
    (hd : ∀ j, ∑ i, k j i = d) (r : ℕ) :
    let P := ∑ j, b j • character (k j)
    haarIntegral (P^r * star (P^r) * density c a) = 0 := by
  dsimp only
  rw [polynomial_power_expansion]
  apply haarIntegral_homogeneous_family_density_zero c a ha ha1 _ _ ((r : ℤ)*d)
  intro u
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  simp [hd]

theorem haarIntegral_homogeneous_power_parseval {κ : Type*} [Fintype κ]
    (c a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1)
    (b : κ → ℂ) (k : κ → ι → ℤ) (d : ℤ)
    (hd : ∀ j, ∑ i, k j i = d) (r : ℕ) :
    let P := ∑ j, b j • character (k j)
    haarIntegral (P^r * star (P^r) * (1 + density c a)) =
      ((∑' n : ι → ℤ, ‖FiniteTorusWiener.coeff (P^r) n‖^2 : ℝ) : ℂ) := by
  dsimp only
  rw [mul_add, mul_one, map_add,
    haarIntegral_homogeneous_power_density_zero c a ha ha1 b k d hd r,
    add_zero, haarIntegral_mul_star_self]

theorem haar_fourth_moment_with_density (b : ι → ℂ)
    (c a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1) :
    haarIntegral ((linearPolynomial b)^2 * star ((linearPolynomial b)^2) *
      (1 + density c a)) =
      ((2 * (∑ i, ‖b i‖^2)^2 - ∑ i, ‖b i‖^4 : ℝ) : ℂ) := by
  rw [mul_add, mul_one, map_add]
  have hz := haarIntegral_homogeneous_power_density_zero c a ha ha1 b
    (fun j => Pi.single j (1 : ℤ)) 1 (fun j => by simp) 2
  change haarIntegral ((linearPolynomial b)^2 * star ((linearPolynomial b)^2)) +
    haarIntegral ((linearPolynomial b)^2 * star ((linearPolynomial b)^2) * density c a) = _
  change haarIntegral ((linearPolynomial b)^2 * star ((linearPolynomial b)^2) *
    density c a) = 0 at hz
  rw [hz, add_zero, haar_fourth_moment]

end RiemannResearch.Analysis.PrimeTorusHaar
