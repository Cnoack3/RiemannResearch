import RiemannResearch.RH.NymanBroadPrimeSquareCompensation
import RiemannResearch.RH.NymanBroadCorrelationScaling
import RiemannResearch.RH.NymanBroadSquareAsymptotic
import RiemannResearch.RH.NymanBroadCorrectionLimits

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# The positive prime slope for the actual normalized broad Nyman family

The exact identity retains the signed square sector, the complete higher-power
constant, and both displacement corrections. Their proved actual-family limits
then give a bounded prime-sector error and the asserted positive linear slope.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.RH

open RiemannResearch.Analysis SignedWeilCorrelation PrimeCompensationLimits

noncomputable def nymanBroadPrimeSector (n : ℕ) (φ : ℝ → ℝ) (R : ℝ) : ℝ :=
  primeCorrelationSector (realAutocorrelation (nymanNormalizedBroadTest n φ R))

theorem nymanBroad_prime_slope_pos {φ : ℝ → ℝ} {a b : ℝ}
    (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hmass : (∫ x, φ x) ≠ 0) :
    0 < ((∫ x, φ x)^2 / (∫ x, φ x^2)) / 2 := by
  exact div_pos (div_pos (sq_pos_of_ne_zero hmass)
    (broadProfile_integral_sq_pos_of_integral_ne_zero hφ
      (broadProfile_hasCompactSupport_of_bounds ha hb) hmass)) (by norm_num)

/-- Before taking any limit, both complete corrections and the whole square
sector occur in the exact prime-sector identity of the actual broad tests. -/
theorem eventually_nymanBroad_prime_compensation (n : ℕ) (hn : 2 ≤ n)
    {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hmass : (∫ x, φ x) ≠ 0) :
    ∀ᶠ R : ℝ in atTop,
      nymanBroadPrimeSector n φ R =
        -primeSquareSector (nymanBroadCorrelation n φ R) R +
        (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + Real.log 2 + Real.pi / 2 +
          higherPrimePowerDiagonal) -
        higherPrimePowerCorrection (nymanBroadCorrelation n φ R) R -
        gammaDisplacementCorrection (nymanBroadCorrelation n φ R) R := by
  letI : NeZero n := ⟨by omega⟩
  have hc := broadProfile_hasCompactSupport_of_bounds ha hb
  obtain ⟨V,B,hV,hB,hbounds⟩ := eventually_nymanBroadCorrelation_uniform_bounds n hn hφ hc hmass
  filter_upwards [hbounds,eventually_gt_atTop (0 : ℝ)] with R hboundsR hR
  have hzero := hboundsR.2.2.2.2.2.1
  have hC : realAutocorrelation (nymanNormalizedBroadTest n φ R) =
      fun t => nymanBroadCorrelation n φ R (t / R) := by
    funext t
    exact realAutocorrelation_nymanNormalizedBroadTest n (by omega) hφ ha hb hR t
  have h := primeCorrelationSector_nymanNormalizedBroadTest_compensation n hφ ha hb hR
  dsimp only at h
  change nymanBroadPrimeSector n φ R = _ at h
  rw [h]
  rw [hC]
  simp only [zero_div, hzero, mul_one, primeSquareSector, div_one,
    higherPrimePowerDisplacementCorrection, higherPrimePowerCorrection,
    gammaDisplacementCorrection, displacementKernel_eq_weilGammaKernel, positiveMeasure]

/-- The prime-plus-square value tends to the complete retained diagonal
constant; neither square discrepancy nor any prime power was discarded. -/
theorem tendsto_nymanBroad_prime_add_square (n : ℕ) (hn : 2 ≤ n)
    {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hmass : (∫ x, φ x) ≠ 0) :
    Tendsto (fun R : ℝ => nymanBroadPrimeSector n φ R +
      primeSquareSector (nymanBroadCorrelation n φ R) R) atTop
      (𝓝 (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + Real.log 2 + Real.pi / 2 +
        higherPrimePowerDiagonal)) := by
  have hc := broadProfile_hasCompactSupport_of_bounds ha hb
  have h3 := tendsto_higherPrimePowerDisplacement_nymanBroadCorrelation n hn hφ hc hmass
  have hg := tendsto_gammaDisplacement_nymanBroadCorrelation n hn hφ hc hmass
  have ht := ((tendsto_const_nhds : Tendsto (fun _ : ℝ =>
    Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + Real.log 2 + Real.pi / 2 +
      higherPrimePowerDiagonal) atTop _).sub h3).sub hg
  apply (show Tendsto (fun R : ℝ =>
      (Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + Real.log 2 + Real.pi / 2 +
        higherPrimePowerDiagonal) - higherPrimePowerCorrection (nymanBroadCorrelation n φ R) R -
          gammaDisplacementCorrection (nymanBroadCorrelation n φ R) R) atTop _ by
    simpa only [sub_zero] using ht).congr'
  filter_upwards [eventually_nymanBroad_prime_compensation n hn hφ ha hb hmass] with R hR
  rw [hR]
  ring

/-- The actual prime sector has the claimed positive linear main term with
a proved bounded error, for the specified varying normalized arithmetic family. -/
theorem eventually_nymanBroad_prime_linear_error (n : ℕ) (hn : 2 ≤ n)
    {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hmass : (∫ x, φ x) ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ R : ℝ in atTop,
      |nymanBroadPrimeSector n φ R - (R / 2) * ((∫ x, φ x)^2 / (∫ x, φ x^2))| ≤ C := by
  obtain ⟨C,hC,hbound⟩ := eventually_nymanBroad_primeSquare_linear_error n hn hφ ha hb hmass
  let κ := Real.eulerMascheroniConstant + Real.log (4 * Real.pi) + Real.log 2 + Real.pi / 2 +
    higherPrimePowerDiagonal
  have hlim := tendsto_nymanBroad_prime_add_square n hn hφ ha hb hmass
  have he := (Metric.tendsto_nhds.1 hlim) 1 (by norm_num)
  refine ⟨1 + |κ| + C, by positivity, ?_⟩
  filter_upwards [hbound,he] with R hS hR
  have hsmall : |nymanBroadPrimeSector n φ R +
      primeSquareSector (nymanBroadCorrelation n φ R) R - κ| ≤ 1 := by
    exact le_of_lt (by simpa only [Real.dist_eq, κ] using hR)
  have hsum : |nymanBroadPrimeSector n φ R +
      primeSquareSector (nymanBroadCorrelation n φ R) R| ≤ 1 + |κ| := by
    calc
      _ = |(nymanBroadPrimeSector n φ R +
          primeSquareSector (nymanBroadCorrelation n φ R) R - κ) + κ| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hsmall le_rfl)
  calc
    _ = |(nymanBroadPrimeSector n φ R + primeSquareSector (nymanBroadCorrelation n φ R) R) -
        (primeSquareSector (nymanBroadCorrelation n φ R) R +
          (R / 2) * ((∫ x, φ x)^2 / (∫ x, φ x^2)))| := by congr 1; ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add hsum hS)

/-- The linear prime slope is the opposite of the actual square slope. -/
theorem tendsto_nymanBroad_prime_div (n : ℕ) (hn : 2 ≤ n)
    {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (ha : ∀ x < a, φ x = 0) (hb : ∀ x > b, φ x = 0) (hmass : (∫ x, φ x) ≠ 0) :
    Tendsto (fun R : ℝ => nymanBroadPrimeSector n φ R / R) atTop
      (𝓝 (((∫ x, φ x)^2 / (∫ x, φ x^2)) / 2)) := by
  have hsum := tendsto_nymanBroad_prime_add_square n hn hφ ha hb hmass
  have hs := tendsto_nymanBroad_primeSquare_div n hn hφ ha hb hmass
  have ht := (hsum.mul tendsto_inv_atTop_zero).sub hs
  apply (show Tendsto (fun R : ℝ =>
      (nymanBroadPrimeSector n φ R + primeSquareSector (nymanBroadCorrelation n φ R) R) * R⁻¹ -
        primeSquareSector (nymanBroadCorrelation n φ R) R / R) atTop _ by
    simpa only [mul_zero, zero_sub, neg_div, neg_neg] using ht).congr'
  exact Filter.Eventually.of_forall fun R => by ring

end RiemannResearch.RH
