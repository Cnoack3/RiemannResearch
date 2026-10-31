/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SubpolynomialWindowGrowth
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Normalized energy and bounded perturbations
Source: the user's normalized exact-head and full-support construction requests,
30 October 2026. These lemmas retain the complete norm and do not assert an
unproved arithmetic growth estimate.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis.NormalizedEnergy
theorem norm_sub_sq_le {E : Type*} [NormedAddCommGroup E]
    (u v : E) : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := norm_sub_le u v
  nlinarith [norm_nonneg (u - v), norm_nonneg u, norm_nonneg v,
    sq_nonneg (‖u‖ - ‖v‖)]

theorem norm_inv_smul_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f : E) : ‖c⁻¹ • f‖ ^ 2 = ‖f‖ ^ 2 / |c| ^ 2 := by
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, mul_pow, inv_pow]
  ring

theorem subpolynomial_residual {E : Type*} [NormedAddCommGroup E]
    (u : E) (F : ℕ → E) (H : ℕ → ℝ)
    (hH : Tendsto H atTop atTop)
    (hF : Tendsto (fun j => Real.log (1 + ‖F j‖ ^ 2) / Real.log (H j))
      atTop (𝓝 0)) :
    Tendsto (fun j => Real.log (1 + ‖u - F j‖ ^ 2) / Real.log (H j))
      atTop (𝓝 0) := by
  apply SubpolynomialWindow.relativeLog_tendsto_zero_of_scaled_budget
    (fun j => ‖u - F j‖ ^ 2) (fun j => ‖F j‖ ^ 2) H (3 + 2 * ‖u‖ ^ 2)
  · nlinarith [sq_nonneg ‖u‖]
  · exact fun j => sq_nonneg _
  · exact fun j => sq_nonneg _
  · exact hH
  · filter_upwards [] with j
    have hb := norm_sub_sq_le u (F j)
    nlinarith [sq_nonneg ‖F j‖, mul_nonneg (sq_nonneg ‖u‖) (sq_nonneg ‖F j‖)]
  · exact hF

theorem subpolynomial_of_bounded_perturbation {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (H : ℕ → ℝ) (K : ℝ) (_hK : 0 ≤ K)
    (hH : Tendsto H atTop atTop)
    (hclose : ∀ᶠ j in atTop, ‖G j - F j‖ ≤ K)
    (hF : Tendsto (fun j => Real.log (1 + ‖F j‖ ^ 2) / Real.log (H j))
      atTop (𝓝 0)) :
    Tendsto (fun j => Real.log (1 + ‖G j‖ ^ 2) / Real.log (H j))
      atTop (𝓝 0) := by
  apply SubpolynomialWindow.relativeLog_tendsto_zero_of_scaled_budget
    (fun j => ‖G j‖ ^ 2) (fun j => ‖F j‖ ^ 2) H (3 + 2 * K ^ 2)
  · nlinarith [sq_nonneg K]
  · exact fun j => sq_nonneg _
  · exact fun j => sq_nonneg _
  · exact hH
  · filter_upwards [hclose] with j hj
    have htri : ‖G j‖ ≤ K + ‖F j‖ := by
      calc
        ‖G j‖ = ‖(G j - F j) + F j‖ := by rw [sub_add_cancel]
        _ ≤ ‖G j - F j‖ + ‖F j‖ := norm_add_le _ _
        _ ≤ K + ‖F j‖ := by linarith
    have hb : ‖G j‖ ^ 2 ≤ 2 * K ^ 2 + 2 * ‖F j‖ ^ 2 := by
      nlinarith [norm_nonneg (G j), norm_nonneg (F j), sq_nonneg (K - ‖F j‖)]
    nlinarith [sq_nonneg ‖F j‖, mul_nonneg (sq_nonneg K) (sq_nonneg ‖F j‖)]
  · exact hF

theorem nonzero_scalar_mem_iff {E : Type*} [AddCommGroup E] [Module ℝ E]
    (V : Submodule ℝ E) (u : E) :
    (∃ c : ℝ, c ≠ 0 ∧ c • u ∈ V) ↔ u ∈ V := by
  constructor
  · rintro ⟨c, hc, hcu⟩
    have h := V.smul_mem c⁻¹ hcu
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h
  · intro hu
    exact ⟨1, one_ne_zero, by simpa using hu⟩
end RiemannResearch.Analysis.NormalizedEnergy

namespace RiemannResearch.Analysis.NormalizedEnergy
open Filter
open scoped Topology
theorem norm_sq_le_of_dist_le {E : Type*} [NormedAddCommGroup E]
    (f g : E) (K : ℝ) (hK : 0 ≤ K) (hclose : ‖g - f‖ ≤ K) :
    ‖g‖ ^ 2 ≤ 2 * ‖f‖ ^ 2 + 2 * K ^ 2 := by
  have htri : ‖g‖ ≤ ‖f‖ + K := by
    have h := norm_add_le (g - f) f
    rw [sub_add_cancel] at h
    linarith
  nlinarith [norm_nonneg f, norm_nonneg g, sq_nonneg (‖f‖ - K)]

theorem sublinear_of_bounded_perturbation {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (H : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : Tendsto H atTop atTop)
    (hclose : ∀ᶠ j in atTop, ‖G j - F j‖ ≤ K)
    (hF : Tendsto (fun j => ‖F j‖ ^ 2 / H j) atTop (𝓝 0)) :
    Tendsto (fun j => ‖G j‖ ^ 2 / H j) atTop (𝓝 0) := by
  have hupper : Tendsto (fun j => 2 * (‖F j‖ ^ 2 / H j) + (2 * K ^ 2) / H j)
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (hF.const_mul 2).add (hH.const_div_atTop (2 * K ^ 2))
  have hpos := hH.eventually (eventually_gt_atTop (0 : ℝ))
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hpos] with j hj
    exact div_nonneg (sq_nonneg _) hj.le
  · filter_upwards [hclose, hpos] with j hc hj
    have hb := div_le_div_of_nonneg_right (norm_sq_le_of_dist_le (F j) (G j) K hK hc) hj.le
    simpa only [add_div, mul_div_assoc] using hb
end RiemannResearch.Analysis.NormalizedEnergy
