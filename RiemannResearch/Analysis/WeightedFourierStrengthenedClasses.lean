/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ArithmeticWeightedFourierEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Arbitrarily slow improvements of weighted Wiener classes

Source: Section 7 of `FRZ_Strengthening_2026-11-10.pdf`. The finite-tail
condition in ArithmeticWeightedFourierEndpoint follows from finite height
sublevels and any positive multiplier Φ tending to infinity. No positive
power gain is required. This also records the saturated Fourier sum bound.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Fourier

/-- Any multiplier diverging with arithmetic height gives the precise
finite-tail condition needed for uniform convergence. -/
theorem tight_weight_of_diverging_multiplier {ι : Type*}
    (b w : ι → ℝ) (Φ : ℝ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hfinite : ∀ B : ℝ, Set.Finite {i | b i ≤ B})
    (hΦ : Tendsto Φ atTop atTop) :
    ∀ η : ℝ, 0 < η → ∃ F : Finset ι,
      ∀ i ∉ F, w i ≤ η * (w i * Φ (b i)) := by
  classical
  intro η hη
  obtain ⟨B, hB⟩ := eventually_atTop.1 ((tendsto_atTop.1 hΦ) (1 / η))
  refine ⟨(hfinite B).toFinset, ?_⟩
  intro i hi
  have hbi : B ≤ b i := by
    have hnot : ¬ b i ≤ B := by simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hi
    exact (lt_of_not_ge hnot).le
  have hphi := hB (b i) hbi
  have hsmall : 1 ≤ η * Φ (b i) := by
    have := (div_le_iff₀ hη).1 hphi
    nlinarith
  have := mul_le_mul_of_nonneg_left hsmall (hw i)
  nlinarith

/-- Uniform convergence for w·Φ(height) balls, with Φ allowed to diverge
arbitrarily slowly. -/
theorem eventually_uniform_weightedFourier_multiplierBall {ι τ : Type*} {l : Filter τ}
    (e : τ → ι → ℂ) (b w : ι → ℝ) (Φ : ℝ → ℝ) (C : ℝ)
    (hC : 0 < C) (hw : ∀ i, 0 < w i) (hΦpos : ∀ i, 0 < Φ (b i))
    (hfinite : ∀ B : ℝ, Set.Finite {i | b i ≤ B})
    (hΦ : Tendsto Φ atTop atTop)
    (hpt : ∀ i, Tendsto (fun t => e t i) l (𝓝 0))
    (hb : ∀ᶠ t in l, ∀ i, ‖e t i‖ ≤ C * w i)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in l, ∀ c : ι → ℂ,
      Summable (fun i => ‖c i‖ * (w i * Φ (b i))) →
      weightedFourierMass c (fun i => w i * Φ (b i)) ≤ 1 →
      ‖weightedFourierPairing c (e t)‖ ≤ ε := by
  exact eventually_uniform_weightedFourier_unitBall e w (fun i => w i * Φ (b i)) C
    hC (fun i => mul_pos (hw i) (hΦpos i)) hpt hb
    (tight_weight_of_diverging_multiplier b w Φ (fun i => (hw i).le) hfinite hΦ) ε hε

/-- Absolute summability at the endpoint suffices for the full saturated
sum envelope. High frequencies are bounded with the quadratic, low frequencies
with the quartic part of the same envelope. -/
theorem weightedFourier_saturated_norm_le {ι : Type*}
    (c e : ι → ℂ) (w : ι → ℝ) (C L : ℝ) (hL : 0 < L)
    (hc : Summable (fun i => ‖c i‖ * w i ^ 2))
    (hb : ∀ i, ‖e i‖ ≤ (C * w i ^ 2 / L) * min 1 (w i ^ 2 / L ^ 2)) :
    ‖weightedFourierPairing c e‖ ≤ (C / L) *
      ∑' i, ‖c i‖ * w i ^ 2 * min 1 (w i ^ 2 / L ^ 2) := by
  have hs : Summable (fun i => ‖c i‖ * (w i ^ 2 * min 1 (w i ^ 2 / L ^ 2))) := by
    apply hc.of_norm_bounded
    intro i
    have hm0 : 0 ≤ min 1 (w i ^ 2 / L ^ 2) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hh := mul_le_mul_of_nonneg_left (min_le_left 1 (w i ^ 2 / L ^ 2))
      (show 0 ≤ ‖c i‖ * w i ^ 2 by positivity)
    nlinarith
  have hm : ∀ i, ‖e i‖ ≤ (C / L) * (w i ^ 2 * min 1 (w i ^ 2 / L ^ 2)) := by
    intro i
    convert hb i using 1 <;> ring
  have h := weightedFourierRemainder_norm_le c e
    (fun i => w i ^ 2 * min 1 (w i ^ 2 / L ^ 2)) C L hs hm
  simpa only [weightedFourierPairing, weightedFourierMass, mul_assoc] using h

/-- Interpolation in a form which keeps the ratio w/L visible. For δ=s−2
this is exactly the A_s envelope, 0≤δ≤2. -/
theorem saturated_mode_interpolation (z : ℂ) (C w L δ : ℝ)
    (hC : 0 ≤ C) (hw : 0 ≤ w) (hL : 0 < L)
    (hδ : 0 ≤ δ) (hδ₂ : δ ≤ 2)
    (hb : ‖z‖ ≤ (C * w ^ 2 / L) * min 1 (w ^ 2 / L ^ 2)) :
    ‖z‖ ≤ (C * w ^ 2 / L) * (w / L) ^ δ := by
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := min_one_sq_le_rpow (w / L) δ (div_nonneg hw hL.le) hδ hδ₂
  simpa only [div_pow] using h

end RiemannResearch.Fourier
