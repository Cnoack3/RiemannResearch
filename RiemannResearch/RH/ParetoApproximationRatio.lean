import RiemannResearch.RH.ParetoNoiseSignal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Approximation of one and arbitrarily small noise/signal ratio

Verified continuation of the preserved 9 September 2026 candidate.

Source: RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md, section 9.
This proves a proposed bridge inside the actual Pareto norm, for any class
closed under scalar multiplication. It does not prove a Nyman--Beurling
criterion, construct an approximating sequence, or establish RH.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

theorem paretoError_eq_variance_add_bias_sq {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) :
    paretoError f = paretoVariance f + (1 - paretoMean f)^2 := by
  have h := paretoError_scale hf 1
  simp only [one_mul, one_pow] at h
  rw [h]
  ring

/-- Normalizing by the actual nonzero mean gives exactly the noise/signal
ratio as approximation error. This is not optimal scaling; it fixes mean one. -/
theorem paretoError_mean_normalization {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hm : paretoMean f ≠ 0) :
    paretoError (fun k => (paretoMean f)⁻¹ * f k) = noiseSignalRatio f := by
  rw [paretoError_scale hf]
  unfold noiseSignalRatio
  field_simp [hm]
  <;> ring

/-- In a scalar-closed class, arbitrarily good approximations of one are
equivalent to arbitrarily small actual noise/signal ratios. Each selected
function is bounded, as is every finite legal packet combination. -/
theorem arbitrarily_small_error_iff_noiseSignalRatio
    (P : (ℕ → ℝ) → Prop)
    (hscale : ∀ f, P f → ∀ a : ℝ, P (fun k => a * f k)) :
    (∀ ε : ℝ, 0 < ε → ∃ f C, (∀ k, |f k| ≤ C) ∧ P f ∧
      paretoError f < ε) ↔
    (∀ ε : ℝ, 0 < ε → ∃ f C, (∀ k, |f k| ≤ C) ∧ P f ∧
      paretoMean f ≠ 0 ∧ noiseSignalRatio f < ε) := by
  constructor
  · intro h ε hε
    let δ : ℝ := min (1 / 4) (ε / 8)
    have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by norm_num))
    obtain ⟨f, C, hf, hP, herr⟩ := h δ hδ
    have hdecomp := paretoError_eq_variance_add_bias_sq hf
    have hv := paretoVariance_nonneg f
    have hδquarter : δ ≤ 1 / 4 := min_le_left _ _
    have hδε : δ ≤ ε / 8 := min_le_right _ _
    have hbias : (1 - paretoMean f)^2 < (1 : ℝ) / 4 := by
      nlinarith
    have hmpos : (1 : ℝ) / 2 < paretoMean f := by
      by_contra hn
      have hmle := le_of_not_gt hn
      nlinarith [sq_nonneg (paretoMean f - 1 / 2)]
    have hm : paretoMean f ≠ 0 := ne_of_gt (by linarith)
    have hm2 : (1 : ℝ) / 4 < (paretoMean f)^2 := by
      nlinarith [sq_nonneg (paretoMean f - 1 / 2)]
    have hvε : paretoVariance f < ε / 8 := by
      nlinarith [sq_nonneg (1 - paretoMean f)]
    refine ⟨f, C, hf, hP, hm, ?_⟩
    unfold noiseSignalRatio
    apply (div_lt_iff₀ (sq_pos_of_ne_zero hm)).mpr
    have hprod := mul_lt_mul_of_pos_left hm2 hε
    nlinarith
  · intro h ε hε
    obtain ⟨f, C, hf, hP, hm, hratio⟩ := h ε hε
    refine ⟨(fun k => (paretoMean f)⁻¹ * f k), |(paretoMean f)⁻¹| * C,
      bounded_const_mul hf _, hscale f hP _, ?_⟩
    rw [paretoError_mean_normalization hf hm]
    exact hratio

end
end RiemannResearch.RH.Pareto
