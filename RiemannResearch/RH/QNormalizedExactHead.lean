/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.NormalizedEnergy
import RiemannResearch.RH.QExactHeadSubpolynomial
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Nonzero exact-head normalization
The head constants may vary and may tend to zero: nonvanishing suffices.
The normalized subpolynomial estimate remains an explicit hypothesis.
-/

open Filter
open scoped Topology

namespace RiemannResearch.RH.QNormalizedExactHead
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open RiemannResearch.Analysis.NormalizedEnergy
theorem riemannHypothesis_of_normalized_subpolynomial
    (F : ℕ → QHilbert) (n : ℕ → ℕ) (c : ℕ → ℝ)
    (hn : Tendsto (fun j => (n j : ℝ)) atTop atTop)
    (hc : ∀ j, c j ≠ 0)
    (hlegal : ∀ j, F j ∈ qSquarefreeCRTSpan)
    (hhead : ∀ j k, 0 < k → k < n j → qSequence (F j) k = c j)
    (hsub : Tendsto (fun j =>
      Real.log (1 + ‖F j‖ ^ 2 / |c j| ^ 2) / Real.log (n j : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  let G : ℕ → QHilbert := fun j => (c j)⁻¹ • F j
  have hnorm (j : ℕ) : ‖G j‖ ^ 2 = ‖F j‖ ^ 2 / |c j| ^ 2 :=
    norm_inv_smul_sq (c j) (F j)
  have hsubG : Tendsto (fun j => Real.log (1 + ‖G j‖ ^ 2) /
      Real.log (n j : ℝ)) atTop (𝓝 0) := by
    simpa only [hnorm] using hsub
  apply QExactHeadSubpolynomial.riemannHypothesis_of_cofinal_exact_head_subpolynomial
    G n (fun j => ‖qOne - G j‖ ^ 2) hn
  · exact fun j => qSquarefreeCRTSpan.smul_mem _ (hlegal j)
  · intro j k hk hkn
    change qSequenceLinear ((c j)⁻¹ • F j) k = 1
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    change (c j)⁻¹ * qSequence (F j) k = 1
    rw [hhead j k hk hkn, inv_mul_cancel₀ (hc j)]
  · exact fun j => sq_nonneg _
  · intro j
    linarith
  · exact subpolynomial_residual qOne G (fun j => (n j : ℝ)) hn hsubG
end RiemannResearch.RH.QNormalizedExactHead

namespace RiemannResearch.RH.QNormalizedExactHead
open ZetaTwoHilbert ZetaTwoProbability
/-- Only eventual nonvanishing is needed; no liminf bound is required. -/
theorem riemannHypothesis_of_eventually_nonzero_normalized_subpolynomial
    (F : ℕ → QHilbert) (n : ℕ → ℕ) (c : ℕ → ℝ)
    (hn : Tendsto (fun j => (n j : ℝ)) atTop atTop)
    (hc : ∀ᶠ j in atTop, c j ≠ 0)
    (hlegal : ∀ j, F j ∈ qSquarefreeCRTSpan)
    (hhead : ∀ j k, 0 < k → k < n j → qSequence (F j) k = c j)
    (hsub : Tendsto (fun j =>
      Real.log (1 + ‖F j‖ ^ 2 / |c j| ^ 2) / Real.log (n j : ℝ))
      atTop (𝓝 0)) : RiemannHypothesis := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hc
  have hshift : Tendsto (fun j : ℕ => j + N) atTop atTop :=
    tendsto_atTop_mono (fun j => by dsimp only [id]; omega) tendsto_id
  apply riemannHypothesis_of_normalized_subpolynomial
    (fun j => F (j + N)) (fun j => n (j + N)) (fun j => c (j + N))
    (hn.comp hshift)
  · intro j
    exact hN (j + N) (by omega)
  · exact fun j => hlegal (j + N)
  · exact fun j => hhead (j + N)
  · exact hsub.comp hshift
end RiemannResearch.RH.QNormalizedExactHead
