import RiemannResearch.RH.ReciprocalChargeDilationNorm
import RiemannResearch.RH.ReciprocalChargeDilationSeries
import RiemannResearch.RH.ReciprocalChargeNormLimit
import RiemannResearch.RH.PrimeReciprocalChargeCorrelation

/-!
# Signed correlation of actual dilated reciprocal-charge vectors

Source: the arithmetic kernel construction developed in this continuation of
`ReciprocalChargeNormLimit20260924.md`. No mathematical novelty is claimed.
The correlation is obtained by exact Hilbert-space polarization; all scalar
limits and arithmetic reindexings are supplied by the imported proofs.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- The entire signed correlation survives in an absolutely convergent Möbius series. -/
theorem reciprocalChargeRiesz_dilation_inner_tendsto (h : ℕ) (hh : 0 < h) :
    Tendsto (fun N => inner ℝ (reciprocalChargeRiesz N) (reciprocalChargeRiesz (h * N)))
      atTop (𝓝 ((1 / (h : ℝ)) * ∑' d : ℕ, mobiusDilationCorrelation h d)) := by
  have hmul : Tendsto (fun N : ℕ => h * N) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    nlinarith
  have hsum := reciprocalChargeRiesz_add_dilation_norm_sq_tendsto h hh
  rw [dilationMobiusCoefficient_square_tsum h hh] at hsum
  have hsecond := reciprocalChargeRiesz_norm_sq_tendsto.comp hmul
  have ht := ((hsum.sub reciprocalChargeRiesz_norm_sq_tendsto).sub hsecond).div_const 2
  have heval : ((30 / Real.pi ^ 2 + (2 / (h : ℝ)) *
      ∑' d : ℕ, mobiusDilationCorrelation h d) - 15 / Real.pi ^ 2 - 15 / Real.pi ^ 2) / 2 =
      (1 / (h : ℝ)) * ∑' d : ℕ, mobiusDilationCorrelation h d := by ring
  rw [heval] at ht
  have he (N : ℕ) :
      (‖reciprocalChargeRiesz N + reciprocalChargeRiesz (h * N)‖ ^ 2 -
        ‖reciprocalChargeRiesz N‖ ^ 2 - ‖reciprocalChargeRiesz (h * N)‖ ^ 2) / 2 =
      inner ℝ (reciprocalChargeRiesz N) (reciprocalChargeRiesz (h * N)) := by
    rw [norm_add_sq_real]
    ring
  simpa only [Function.comp_def, he] using ht


/-- At a prime dilation, the signed limit has an explicit rational Euler factor. -/
theorem reciprocalChargeRiesz_prime_dilation_inner_tendsto (p : ℕ) (hp : Nat.Prime p) :
    Tendsto (fun N => inner ℝ (reciprocalChargeRiesz N) (reciprocalChargeRiesz (p * N)))
      atTop (𝓝 (-(15 * (p : ℝ)) / (((p : ℝ) ^ 2 + 1) * Real.pi ^ 2))) := by
  have ht := reciprocalChargeRiesz_dilation_inner_tendsto p hp.pos
  rw [← dilationMobiusCoefficient_mixed_tsum p,
    prime_dilation_mobius_mixed_tsum_exact p hp] at ht
  exact ht

theorem reciprocalChargeRiesz_two_dilation_inner_tendsto :
    Tendsto (fun N => inner ℝ (reciprocalChargeRiesz N) (reciprocalChargeRiesz (2 * N)))
      atTop (𝓝 (-6 / Real.pi ^ 2)) := by
  have ht := reciprocalChargeRiesz_dilation_inner_tendsto 2 (by decide)
  rw [← dilationMobiusCoefficient_mixed_tsum 2, two_dilation_mobius_mixed_tsum] at ht
  exact ht

theorem reciprocalChargeRiesz_three_dilation_inner_tendsto :
    Tendsto (fun N => inner ℝ (reciprocalChargeRiesz N) (reciprocalChargeRiesz (3 * N)))
      atTop (𝓝 (-9 / (2 * Real.pi ^ 2))) := by
  have ht := reciprocalChargeRiesz_dilation_inner_tendsto 3 (by decide)
  rw [← dilationMobiusCoefficient_mixed_tsum 3, three_dilation_mobius_mixed_tsum] at ht
  exact ht

end RiemannResearch.RH.Pareto
