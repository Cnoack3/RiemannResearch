/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCofinalVKDisplacement
import RiemannResearch.RH.QDisplacementSignCounts

/-!
# Cofinal sign counts at the Vinogradov–Korobov scale

The Mertens saving is an explicit arithmetic input, as in Lee–Leong,
arXiv:2208.06141v5, Theorem 1.1. The sign-count estimate uses the complete
energy of the physical displacement. The rarer sign may vary with the cutoff.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity

open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert

/-- The Cauchy–Schwarz loss of a square root doubles the admissible
exponent when testing counts in place of one-sided harmonic masses. -/
theorem riemannHypothesis_of_cofinal_vk_sign_count (a b C D : ℝ)
    (hb : 0 ≤ b) (hba : b < 2 * (a * (1 / 2 : ℝ) ^ (3 / 5 : ℝ)))
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * vkProfile x)) * x)
    (hgood : ∃ᶠ X : ℕ in atTop, ∃ ε : ℝ, |ε| = 1 ∧
      ((displacementSignSupport ε X).card : ℝ) ≤ D * Real.exp (b * vkProfile X)) :
    RiemannHypothesis := by
  let A := a * (1 / 2 : ℝ) ^ (3 / 5 : ℝ)
  change b < 2 * A at hba
  let c := (b / 2 + A) / 2
  have hc : 0 ≤ c := by dsimp only [c]; linarith
  have hcA : c < A := by dsimp only [c]; linarith
  have hgap : 0 < 2 * c - b := by dsimp only [c]; linarith
  let T := ∑' n : ℕ, (qSequence displacement n / (n : ℝ)) ^ 2
  have hT : 0 ≤ T := tsum_nonneg (fun _ => sq_nonneg _)
  have hPhi : Tendsto (fun X : ℕ => vkProfile (X : ℝ)) atTop atTop :=
    vkProfile_tendsto_atTop.comp tendsto_natCast_atTop_atTop
  have hg := (Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hgap hPhi)).eventually
    (eventually_ge_atTop (D * T))
  apply riemannHypothesis_of_cofinal_vk_harmonic_prefix a c C hc hcA hM
  apply (hgood.and_eventually hg).mono
  rintro X ⟨⟨ε, hε, hcount⟩, hx⟩
  change D * T ≤ Real.exp ((2 * c - b) * vkProfile (X : ℝ)) at hx
  have hside : minimumHarmonicPrefix X ≤ harmonicSide ε X := by
    rcases le_total 0 ε with h | h
    · have he : ε = 1 := (abs_of_nonneg h).symm.trans hε
      rw [he]
      exact min_le_left _ _
    · rw [abs_of_nonpos h] at hε
      have he : ε = -1 := by linarith
      rw [he]
      exact min_le_right _ _
  apply hside.trans
  apply le_of_sq_le_sq _ (Real.exp_pos _).le
  calc
    (harmonicSide ε X) ^ 2 ≤ ((displacementSignSupport ε X).card : ℝ) * T :=
      harmonicSide_sq_le_sign_count ε hε X
    _ ≤ (D * Real.exp (b * vkProfile X)) * T := mul_le_mul_of_nonneg_right hcount hT
    _ = (D * T) * Real.exp (b * vkProfile X) := by ring
    _ ≤ Real.exp ((2 * c - b) * vkProfile X) * Real.exp (b * vkProfile X) :=
      mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = (Real.exp (c * vkProfile X)) ^ 2 := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
