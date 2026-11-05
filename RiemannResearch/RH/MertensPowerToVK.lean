/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeVKDisplacement

/-!
# A power saving for Mertens implies every fixed VK rate

Gerhold, *Acta Arithmetica* 142 (2010), Proposition 3, supplies a
power-saving estimate on paper from a fixed zero-free half-plane. The
power saving is an explicit hypothesis in the results below.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeMertensProfileCriterion

open RiemannResearch.Analysis
open RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity

/-- A fixed power saving on the summatory Möbius function gives any
prescribed positive VK coefficient, with eventual prefactor one. -/
theorem mertens_vk_of_power_saving (s C a : ℝ) (hs : s < 1) (hC : 0 ≤ C)
    (ha : 0 < a) (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ C * x ^ s) :
    ∀ᶠ x : ℝ in atTop, |M x| ≤ Real.exp (-a * vkProfile x) * x := by
  let A := a + 1
  have hA : 0 < A := by dsimp [A]; linarith
  have hδ : 0 < (1 - s) / A := div_pos (sub_pos.mpr hs) hA
  obtain ⟨X, hX⟩ := (vkProfile_eventual_log_increment _ hδ).exists
  let K := A * vkProfile X - (1 - s) * Real.log X
  apply mertens_vk_absorb_constant A a (C * Real.exp K) (by dsimp [A]; linarith)
  filter_upwards [hM, eventually_ge_atTop X, eventually_gt_atTop (0 : ℝ)] with x hx hXx hx0
  have hinc := mul_le_mul_of_nonneg_left (hX x hXx) hA.le
  have hcancel : A * ((1 - s) / A) = 1 - s := by field_simp [hA.ne']
  rw [← mul_assoc, hcancel] at hinc
  have hexp : Real.log x * s ≤ K + (-A * vkProfile x) + Real.log x := by
    dsimp only [K]
    linarith only [hinc]
  calc
    |M x| ≤ C * x ^ s := hx
    _ = C * Real.exp (Real.log x * s) := by rw [Real.rpow_def_of_pos hx0]
    _ ≤ C * Real.exp (K + (-A * vkProfile x) + Real.log x) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hC
    _ = ((C * Real.exp K) * Real.exp (-A * vkProfile x)) * x := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hx0]
      ring

/-- Once a power saving is available, every fixed positive VK growth
coefficient for the actual displacement suffices. -/
theorem riemannHypothesis_of_mertens_power_saving_and_vk_displacement
    (s C b D : ℝ) (hs : s < 1) (hC : 0 ≤ C) (hb : 0 < b)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ C * x ^ s)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (b * vkProfile (n : ℝ))) : RiemannHypothesis := by
  have ha : 0 < 2 * b + 1 := by linarith
  exact riemannHypothesis_of_vk_exponential_displacement (2*b+1) b D ha hb
    (by linarith) (mertens_vk_of_power_saving s C _ hs hC ha hM) hd

end RiemannResearch.RH.QSquarefreeMertensProfileCriterion
