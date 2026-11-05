/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensExponentialCutoffPairing
import RiemannResearch.RH.MertensCriticalEnvelope
import RiemannResearch.Analysis.VKSecondProfile
import RiemannResearch.RH.MertensVKFirstMoment

/-!
# Signed first moments at the secondary and critical Mertens rates

The envelope for the finite Möbius error transfers both the secondary
coefficient and a smaller correction at the critical value.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity

private def vkPairingExponent (A b t x : ℝ) : ℝ :=
  -A * vkProfile x - b * vkSecondProfile x - t * Real.sqrt (vkProfile x)

private theorem residual_zero_of_vk_exponent_envelope (A a s b t : ℝ)
    (hA : 0 < A) (ha : 0 ≤ a) (hs : 0 ≤ s) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ Real.exp (vkPairingExponent A a s x) * x)
    (henv : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      errorEnvelope N n (Real.exp (vkPairingExponent A a s N)) ≤
        2 + K * ((n : ℝ) * Real.exp (vkPairingExponent A b t n)))
    (hd : Summable (fun n : ℕ => positiveQWeight n *
      ((n : ℝ) * Real.exp (vkPairingExponent A b t n)) * |qSequence displacement n|)) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  have hS : ∀ᶠ x : ℝ in atTop, 0 ≤ vkSecondProfile x := by
    filter_upwards [sqrt_vk_le_mul_secondProfile 1 (by norm_num)] with x hx
    simpa only [one_mul] using (Real.sqrt_nonneg _).trans hx
  refine residual_zero_of_exponential_cutoff_moment (vkPairingExponent A a s)
    (fun n => (n : ℝ) * Real.exp (vkPairingExponent A b t n)) ?_ ?_ hM henv ?_ hd
  · apply tendsto_atBot.2
    intro B
    filter_upwards [(Tendsto.const_mul_atTop hA vkProfile_tendsto_atTop).eventually
      (eventually_ge_atTop (-B)), hS] with x hx hSx
    change -B ≤ A * vkProfile x at hx
    dsimp only [vkPairingExponent]
    linarith only [hx, mul_nonneg ha hSx, mul_nonneg hs (Real.sqrt_nonneg (vkProfile x))]
  · filter_upwards [vkProfile_eventually_mono, vkSecondProfile_eventually_mono] with x hp hq y hxy
    dsimp only [vkPairingExponent]
    linarith only [mul_le_mul_of_nonneg_left (hp y hxy) hA.le,
      mul_le_mul_of_nonneg_left (hq y hxy) ha,
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hp y hxy)) hs]
  · apply (summable_vk_first_moment_constant A hA).of_norm_bounded_eventually_nat
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hnat.eventually hS] with n hSn
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (positiveQWeight_nonneg n)
      (mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le))]
    apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg n)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    apply Real.exp_le_exp.mpr
    dsimp only [vkPairingExponent]
    linarith only [mul_nonneg hb hSn, mul_nonneg ht (Real.sqrt_nonneg (vkProfile n))]

/-- Preserve both the leading and secondary coefficients in the first moment, using
a square-root saving to control the change of cutoff. -/
theorem residual_zero_of_critical_displacement_moment (A b t : ℝ) (hA : 0 < A)
    (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤
      Real.exp (-A * vkProfile x - b * vkSecondProfile x -
        (2 * (t + 2)) * Real.sqrt (vkProfile x)) * x)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-A * vkProfile n - b * vkSecondProfile n - t * Real.sqrt (vkProfile n))) *
        |qSequence displacement n|)) :
    ZetaTwoOptimizerStage.limitingResidual = 0 :=
  residual_zero_of_vk_exponent_envelope A b (2 * (t + 2)) b t hA hb
    (by positivity) hb ht hM (errorEnvelope_eventually_le_vk_critical A b t hA hb ht) hd

end RiemannResearch.RH.QMertensFirstMoment
