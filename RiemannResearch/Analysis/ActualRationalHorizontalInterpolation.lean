/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualRationalHorizontalSaturation
import RiemannResearch.Analysis.WeightedFourierStrengthenedClasses

/-!
# The full intermediate Wiener scale for actual horizontal corrections

Source: Section 6 of `FRZ_Strengthening_2026-11-10.pdf`. Saturation gives one
simultaneous estimate for every real regularity exponent 2≤s≤4:
||Σ c_k R_T(k)|| ≤ C (log T)^(1−s) Σ |c_k| w(k)^s.
The constant and height threshold are independent of s and the test. The
fixed A₂ little-oh refinement is in ActualRationalHorizontalEndpoint.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Fourier

theorem saturated_mode_interpolation_rpow (z : ℂ) (C w L s : ℝ)
    (hC : 0 ≤ C) (hw : 0 < w) (hL : 0 < L) (hs : 2 ≤ s) (hs4 : s ≤ 4)
    (hb : ‖z‖ ≤ (C * w ^ 2 / L) * min 1 (w ^ 2 / L ^ 2)) :
    ‖z‖ ≤ (C / L ^ (s - 1)) * w ^ s := by
  have h := saturated_mode_interpolation z C w L (s - 2) hC hw.le hL
    (by linarith) (by linarith) hb
  apply h.trans_eq
  rw [Real.div_rpow hw.le hL.le]
  have hwexp : w ^ s = w ^ 2 * w ^ (s - 2) := by
    conv_lhs => rw [show s = 2 + (s - 2) by ring]
    rw [Real.rpow_add hw]
    norm_num
  have hLexp : L ^ (s - 1) = L * L ^ (s - 2) := by
    conv_lhs => rw [show s - 1 = 1 + (s - 2) by ring]
    rw [Real.rpow_add hL, Real.rpow_one]
  rw [hwexp, hLexp]
  ring

end RiemannResearch.Fourier
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- One constant serves every exponent and every rational mode. -/
theorem eventually_correctedRationalRemainder_interpolation
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ s : ℝ, 2 ≤ s → s ≤ 4 →
      ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      ‖correctedRationalRemainder T n m‖ ≤
        (K / (Real.log T) ^ (s - 1)) * rationalModeWeight n m ^ s := by
  obtain ⟨K, hK, hb⟩ := eventually_correctedRationalRemainder_saturated hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with T hT hT1
  intro s hs hs4 n m hn hm
  have hw : 0 < rationalModeWeight n m := by dsimp [rationalModeWeight]; positivity
  exact Fourier.saturated_mode_interpolation_rpow _ _ _ _ _ hK.le hw
    (Real.log_pos hT1) hs hs4 (hT n m hn hm)

/-- Actual infinite Fourier interpolation, uniformly over the full interval
2≤s≤4. The coefficients and rational frequencies may depend on height. -/
theorem eventually_correctedRationalFourier_interpolation {ι : Type*}
    (hD : UniformSelbergDensity (1 / 4)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ s : ℝ, 2 ≤ s → s ≤ 4 →
      ∀ (c : ι → ℂ) (n m : ι → ℕ),
      (∀ i, 1 ≤ n i) → (∀ i, 1 ≤ m i) →
      Summable (fun i => ‖c i‖ * rationalModeWeight (n i) (m i) ^ s) →
      ‖∑' i, c i * correctedRationalRemainder T (n i) (m i)‖ ≤
        (K / (Real.log T) ^ (s - 1)) *
          Fourier.weightedFourierMass c (fun i => rationalModeWeight (n i) (m i) ^ s) := by
  obtain ⟨K, hK, hb⟩ := eventually_correctedRationalRemainder_interpolation hD
  refine ⟨K, hK, hb.mono ?_⟩
  intro T hT s hs hs4 c n m hn hm hc
  exact Fourier.weightedFourierRemainder_norm_le c
    (fun i => correctedRationalRemainder T (n i) (m i))
    (fun i => rationalModeWeight (n i) (m i) ^ s) K ((Real.log T) ^ (s - 1)) hc
    (fun i => hT s hs hs4 (n i) (m i) (hn i) (hm i))

end RiemannResearch.Analysis.ActualZeroOrdinate
