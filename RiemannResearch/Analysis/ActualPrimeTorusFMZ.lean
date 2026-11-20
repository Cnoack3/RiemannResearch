/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalFMZLimits
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.FinitePrimeModeArithmetic
import RiemannResearch.Analysis.PrimeTorusHaarSpecialization
import RiemannResearch.Analysis.PrimePhaseTorus

/-!
# Actual finite prime-torus FMZ sampling

The actual positive-height zeta zeros, their analytic multiplicities, the exact
product-Haar centering and the actual prime-phase map are used throughout.
The rational Landau coefficients are derived from the proved contour theorem.
The unconditional horizontal estimate gives convergence for every character
and finite polynomial, including all mixed prime frequencies.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualPrimeTorusFMZ
open ActualZeroOrdinate PrimePhaseTorus PrimeTorusHaar

def sampleFunctional (P : Finset ℕ) (T : ℝ) : C(Torus P, ℂ) →ₗ[ℂ] ℂ where
  toFun f := sum T (fun ρ => f (primeOrbit P ρ.im))
  map_add' f g := by
    simp only [ContinuousMap.add_apply, sum_add]
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    calc
      sum T (fun ρ => c * f (primeOrbit P ρ.im)) =
          sum T (fun ρ => f (primeOrbit P ρ.im) * c) := by
        congr 1
        funext ρ
        ring
      _ = sum T (fun ρ => f (primeOrbit P ρ.im)) * c := sum_mul_const _ _ _
      _ = _ := mul_comm _ _

@[simp] theorem sampleFunctional_apply (P : Finset ℕ) (T : ℝ)
    (f : C(Torus P, ℂ)) :
    sampleFunctional P T f = sum T (fun ρ => f (primeOrbit P ρ.im)) := rfl

theorem character_primeOrbit_eq_phase (P : Finset ℕ) (k : ℕ → ℤ) (t : ℝ) :
    character (fun p : P => k p) (primeOrbit P t) =
      ZeroOrdinate.phase (primeFrequency P k) t := by
  rw [character_primeOrbit, finite_prime_phase_character]
  unfold ZeroOrdinate.phase primeFrequency
  congr 1
  ring

theorem sampleFunctional_character (P : Finset ℕ) (k : ℕ → ℤ) (T : ℝ) :
    sampleFunctional P T (character (fun p : P => k p)) =
      ordinateSum T (primeFrequency P k) := by
  simp only [sampleFunctional_apply, character_primeOrbit_eq_phase, ordinateSum]

theorem restrictedMode_eq_zero_iff (P : Finset ℕ) (k : ℕ → ℤ) :
    (fun p : P => k p) = 0 ↔ ∀ p ∈ P, k p = 0 := by
  constructor
  · intro h p hp
    exact congrFun h ⟨p, hp⟩
  · intro h
    funext p
    exact h p p.property

theorem centered_character_eq_rational (P : Finset ℕ) (k : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) (T : ℝ) :
    sampleFunctional P T (character (fun p : P => k p)) -
        (Ncount 0 T : ℂ) * haarIntegral (character (fun p : P => k p)) =
      centeredRationalOrdinate T (primeNumerator P k) (primeDenominator P k) := by
  rw [sampleFunctional_character, haarIntegral_character_eq]
  unfold centeredRationalOrdinate
  rw [prime_log_ratio_eq_frequency P k hP]
  have heq : ((fun p : P => k p) = 0) ↔
      primeNumerator P k = primeDenominator P k :=
    (restrictedMode_eq_zero_iff P k).trans
      (primeNumerator_eq_denominator_iff P k hP).symm
  by_cases hk : (fun p : P => k p) = 0
  · simp [hk, heq.mp hk]
  · have hr : primeNumerator P k ≠ primeDenominator P k :=
      fun h => hk (heq.mpr h)
    simp [hk, hr]

/-- Every actual prime-torus character has its arithmetic FMZ limit. The
constant character is removed by exact product-Haar centering. -/
theorem tendsto_centered_character_div (P : Finset ℕ) (k : ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P T (character (fun p : P => k p)) -
        (Ncount 0 T : ℂ) * haarIntegral (character (fun p : P => k p))) / (T : ℂ))
      atTop (𝓝 (rationalFMZMain (primeNumerator P k) (primeDenominator P k))) := by
  simp_rw [centered_character_eq_rational P k hP]
  apply tendsto_centeredRationalOrdinate_div
  · exact primeProduct_pos P (fun p => (k p).toNat) hP
  · exact primeProduct_pos P (fun p => (-k p).toNat) hP

def polynomial {ι : Type*} (P : Finset ℕ) (s : Finset ι)
    (a : ι → ℂ) (k : ι → ℕ → ℤ) : C(Torus P, ℂ) :=
  ∑ i ∈ s, a i • character (fun p : P => k i p)

/-- Complete finite prime-torus synthesis, retaining every mixed mode and
the original signed coefficients. -/
theorem tendsto_centered_polynomial_div {ι : Type*}
    (P : Finset ℕ) (s : Finset ι) (a : ι → ℂ) (k : ι → ℕ → ℤ)
    (hP : ∀ p ∈ P, p.Prime) :
    Tendsto (fun T : ℝ =>
      (sampleFunctional P T (polynomial P s a k) -
        (Ncount 0 T : ℂ) * haarIntegral (polynomial P s a k)) / (T : ℂ))
      atTop (𝓝 (∑ i ∈ s,
        a i * rationalFMZMain (primeNumerator P (k i)) (primeDenominator P (k i)))) := by
  have h := tendsto_finsetSum s (fun i hi =>
    (tendsto_centered_character_div P (k i) hP).const_mul (a i))
  convert h using 1
  funext T
  simp only [polynomial, map_sum, map_smul, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end RiemannResearch.Analysis.ActualPrimeTorusFMZ
