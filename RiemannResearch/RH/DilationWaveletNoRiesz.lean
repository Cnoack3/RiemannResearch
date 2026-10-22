import RiemannResearch.Analysis.NormalizedPairObstruction
import RiemannResearch.RH.DilationWaveletNearbyEnergy
import RiemannResearch.RH.DilationWaveletBinaryNorm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp

/-!
# Actual normalized binary wavelets have arbitrarily close adjacent pairs

The complete nearby-dilation energy estimate proves the full adjacent-pair
limit and rules out a positive lower Riesz bound. This does not assert the
sharper logarithmic asymptotic in the research report.
-/

open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto
noncomputable section

theorem binary_wavelet_hilbert_ne_zero (m : ℕ) (hm : 0 < m) :
    dilationWaveletHilbert 2 m (by omega) hm ≠ 0 := by
  have hs : 0 < ‖dilationWaveletHilbert 2 m (by omega) hm‖ ^ 2 := by
    rw [binary_wavelet_hilbert_norm_sq m hm]
    positivity
  intro hz
  simp [hz] at hs

def normalizedBinaryWavelet (m : ℕ) (hm : 0 < m) : ThresholdHilbert :=
  NormedSpace.normalize (dilationWaveletHilbert 2 m (by omega) hm)

theorem normalizedBinaryWavelet_norm (m : ℕ) (hm : 0 < m) :
    ‖normalizedBinaryWavelet m hm‖ = 1 :=
  NormedSpace.norm_normalize (binary_wavelet_hilbert_ne_zero m hm)

theorem normalizedBinaryWavelet_nearby_bound (m J : ℕ) (hm : 0 < m) (hJ : 0 < J) :
    ‖normalizedBinaryWavelet m hm - normalizedBinaryWavelet (m+1) (by omega)‖ ^ 2 ≤
      (64 / Real.pi) * ((J : ℝ) / ((m : ℝ) + 1) + 1 / (J : ℝ)) := by
  have hn := Analysis.NormalizedPairObstruction.normalize_difference_sq_le
    (dilationWaveletHilbert 2 m (by omega) hm)
    (dilationWaveletHilbert 2 (m+1) (by omega) (by omega))
    (binary_wavelet_hilbert_ne_zero m hm) (binary_wavelet_hilbert_ne_zero (m+1) (by omega))
  rw [binary_wavelet_hilbert_norm_sq m hm] at hn
  have hb := binary_wavelet_nearby_hilbert_energy_bound m J hm hJ
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hJ0 : (J : ℝ) ≠ 0 := by positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  calc
    _ ≤ 4 * ‖dilationWaveletHilbert 2 m (by omega) hm -
        dilationWaveletHilbert 2 (m+1) (by omega) (by omega)‖ ^ 2 /
        (Real.pi / (4 * (m : ℝ))) := hn
    _ ≤ (4 * (4 * ((J : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) +
        1 / ((m : ℝ) * (J : ℝ))))) / (Real.pi / (4 * (m : ℝ))) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by
      field_simp [hm0, hJ0, hm1, ne_of_gt Real.pi_pos]
      <;> ring

/-- The normalized adjacent-pair energy tends to zero along all positive
integer dilations; this is not merely a sparse-subsequence statement. -/
theorem normalizedBinaryWavelet_adjacent_tendsto_zero :
    Tendsto (fun n : ℕ => ‖normalizedBinaryWavelet (n+1) (by omega) -
      normalizedBinaryWavelet (n+2) (by omega)‖ ^ 2) atTop (𝓝 0) := by
  apply Analysis.NormalizedPairObstruction.tendsto_zero_of_cutoff_bound _ (64 / Real.pi)
    (fun _ => sq_nonneg _)
  intro n J hJ
  have hb := normalizedBinaryWavelet_nearby_bound (n+1) J (by omega) hJ
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hden : (n : ℝ) + 1 ≤ (n : ℝ) + 1 + 1 := by linarith
  have hle := div_le_div_of_nonneg_left (Nat.cast_nonneg J) hn0 hden
  push_cast at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add hle le_rfl

/-- Consequently the actual norm-one wavelet family has no positive lower
Riesz bound for all finite signed coefficient families. -/
theorem normalizedBinaryWavelet_no_uniformLowerRiesz :
    ¬ ∃ c : ℝ, 0 < c ∧ Analysis.NormalizedPairObstruction.UniformLowerRieszBound
      (fun n : ℕ => normalizedBinaryWavelet (n+1) (by omega)) c := by
  apply Analysis.NormalizedPairObstruction.no_uniformLowerRiesz_of_close_pairs
    (fun n : ℕ => normalizedBinaryWavelet (n+1) (by omega))
    (fun n => n) (fun n => n+1) (fun n => by omega)
  exact normalizedBinaryWavelet_adjacent_tendsto_zero

end
end RiemannResearch.RH.Pareto
