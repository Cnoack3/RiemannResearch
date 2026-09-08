import RiemannResearch.RH.ParetoCovariance
import RiemannResearch.LinearAlgebra.NoiseSignalQuadratic
import Mathlib.Tactic.FieldSimp

/-!
# Actual Pareto variance and the noise-to-signal ratio

Source: user-provided argument, `RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`,
§§2 and 3.2. Every expectation is the complete infinite Pareto sum.
Boundedness discharges summability for all finite arithmetic packet sums.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def paretoVariance (f : ℕ → ℝ) : ℝ :=
  paretoInner (fun k => f k - paretoMean f) (fun k => f k - paretoMean f)

def paretoError (f : ℕ → ℝ) : ℝ :=
  paretoInner (fun k => 1 - f k) (fun k => 1 - f k)

/-- The ratio is used only when the mean is nonzero. -/
def noiseSignalRatio (f : ℕ → ℝ) : ℝ := paretoVariance f / (paretoMean f)^2

theorem paretoInner_one_right (f : ℕ → ℝ) :
    paretoInner f (fun _ => 1) = paretoMean f := by
  simp [paretoInner, paretoMean]

theorem paretoInner_one_left (f : ℕ → ℝ) :
    paretoInner (fun _ => 1) f = paretoMean f := by
  rw [paretoInner_comm, paretoInner_one_right]

theorem paretoInner_one : paretoInner (fun _ => 1) (fun _ => 1) = 1 := by
  simpa [paretoInner] using positiveWeight_tsum

theorem paretoMean_one : paretoMean (fun _ => 1) = 1 := by
  simpa [paretoMean] using positiveWeight_tsum

theorem paretoVariance_nonneg (f : ℕ → ℝ) : 0 ≤ paretoVariance f :=
  paretoInner_self_nonneg _

theorem paretoVariance_eq {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) :
    paretoVariance f = paretoInner f f - (paretoMean f)^2 := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  have h := paretoInner_residual_polynomial hf h1 (paretoMean f)
  simp only [mul_one, paretoInner_one_right, paretoInner_one, paretoMean_one] at h
  unfold paretoVariance
  rw [h]
  ring

theorem paretoError_scale {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (a : ℝ) :
    paretoError (fun k => a * f k) =
      1 - 2*a*paretoMean f + a^2*(paretoVariance f + (paretoMean f)^2) := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  unfold paretoError
  rw [paretoInner_residual_polynomial h1 hf a, paretoInner_one,
    paretoInner_one_left, paretoVariance_eq hf]
  ring

theorem paretoError_scale_completion {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hm : paretoMean f ≠ 0) (a : ℝ) :
    paretoError (fun k => a * f k) =
      paretoVariance f / (paretoVariance f + (paretoMean f)^2) +
      (paretoVariance f + (paretoMean f)^2) *
        (a - paretoMean f / (paretoVariance f + (paretoMean f)^2))^2 := by
  have hden : paretoVariance f + (paretoMean f)^2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (paretoVariance_nonneg f) (sq_pos_of_ne_zero hm))
  rw [paretoError_scale hf]
  exact RiemannResearch.LinearAlgebra.NoiseSignalQuadratic.scale_error_completion
    (paretoVariance f) (paretoMean f) a hden

theorem paretoError_at_optimal_scale {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hm : paretoMean f ≠ 0) :
    paretoError (fun k => (paretoMean f /
      (paretoVariance f + (paretoMean f)^2)) * f k) =
      noiseSignalRatio f / (1 + noiseSignalRatio f) := by
  rw [paretoError_scale_completion hf hm]
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  unfold noiseSignalRatio
  have hm2 : (paretoMean f)^2 ≠ 0 := pow_ne_zero 2 hm
  have hd : paretoVariance f + (paretoMean f)^2 ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (paretoVariance_nonneg f) (sq_pos_of_ne_zero hm))
  exact RiemannResearch.LinearAlgebra.NoiseSignalQuadratic.noise_ratio_conversion
    (paretoVariance f) (paretoMean f) hm hd

theorem paretoError_optimal_scale_minimizes {f : ℕ → ℝ} {C : ℝ}
    (hf : ∀ k, |f k| ≤ C) (hm : paretoMean f ≠ 0) (a : ℝ) :
    noiseSignalRatio f / (1 + noiseSignalRatio f) ≤
      paretoError (fun k => a * f k) := by
  rw [← paretoError_at_optimal_scale hf hm]
  rw [paretoError_scale_completion hf hm, paretoError_scale_completion hf hm]
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  have hn : 0 ≤ (paretoVariance f + (paretoMean f)^2) *
      (a - paretoMean f / (paretoVariance f + (paretoMean f)^2))^2 :=
    mul_nonneg (add_nonneg (paretoVariance_nonneg f) (sq_nonneg _)) (sq_nonneg _)
  linarith

theorem primePowerCombination_noiseSignal_floor (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, ∃ p a, p.Prime ∧ q = p^a)
    (hm : paretoMean (fun k => ∑ q ∈ s, c q * ramanujanPacket q k) ≠ 0) :
    (1 : ℝ)/91 ≤ noiseSignalRatio (fun k => ∑ q ∈ s, c q * ramanujanPacket q k) := by
  let f : ℕ → ℝ := fun k => ∑ q ∈ s, c q * ramanujanPacket q k
  obtain ⟨C, hC⟩ := packetCombination_bounded s c
  let a : ℝ := paretoMean f / (paretoVariance f + (paretoMean f)^2)
  have hbound := primePowerCombination_full_error_floor s (fun q => a * c q) hs
  have heq : (fun k => ∑ q ∈ s, (a * c q) * ramanujanPacket q k) =
      (fun k => a * f k) := by
    funext k
    simp only [f, Finset.mul_sum, mul_assoc]
  simp_rw [congrFun heq] at hbound
  have herr : (1 : ℝ)/92 ≤ paretoError (fun k => a * f k) := by
    change (1 : ℝ)/92 ≤ ∑' k, positiveWeight k * ((1 - a*f k)*(1 - a*f k))
    simp only [← sq]
    linarith
  have hop := paretoError_scale_completion (f := f) hC hm a
  change paretoError (fun k => a * f k) = _ at hop
  simp only [a, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hop
  rw [hop] at herr
  have hmpos : 0 < (paretoMean f)^2 := sq_pos_of_ne_zero hm
  have hdpos : 0 < paretoVariance f + (paretoMean f)^2 :=
    add_pos_of_nonneg_of_pos (paretoVariance_nonneg f) hmpos
  have hb := (le_div_iff₀ hdpos).mp herr
  change (1 : ℝ)/91 ≤ paretoVariance f / (paretoMean f)^2
  apply (le_div_iff₀ hmpos).mpr
  nlinarith

end
end RiemannResearch.RH.Pareto
