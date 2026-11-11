/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.RamanujanFRZSignal
import RiemannResearch.Analysis.ActualRationalLandauLogPowers

/-!
# Arbitrary fixed-order FRZ correction in the actual inverse Gram metric

Source: FRZ_Strengthening_2026-11-10, Section 8 (First and Fifth).
Retaining horizontal moments through degree 2J gives source error
O((log T)^(-2J-1)) and a squared inverse-Gram budget of order
(log T)^(-4J-2), with explicit frequency weights and the actual Pareto
inverse matrix. J is fixed; constants and the height threshold depend on J.
The classical Selberg density premise remains explicit and is not RH.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.RamanujanFRZSignal
open RiemannResearch.Analysis ActualZeroOrdinate
open FiniteGramSignalStability RamanujanZeroSignal

def higherSignalWeight (J : ℕ) (B C a : ℝ) (q : ℕ) : ℝ :=
  (2 * Real.pi * Real.sqrt (q : ℝ)) *
    (B + (2 / a) ^ (2 * (J + 1)) * (2 * C / 3) *
      (Real.log (q : ℝ)) ^ (2 * (J + 1)))

theorem higherSignalWeight_nonneg (J : ℕ) (B C a : ℝ) (q : ℕ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) : 0 ≤ higherSignalWeight J B C a q := by
  unfold higherSignalWeight
  simp only [pow_mul]
  positivity

theorem horizontalTaylorError_inverse_log_power
    (J : ℕ) (T u C a : ℝ) (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hu : |u| ≤ a * Real.log T / 2) (hD : SelbergDensityBound T C a) :
    ‖horizontalTaylorError T u J / (T : ℂ)‖ ≤
      ((2 / a) ^ (2 * (J + 1)) * (2 * C / 3) * u ^ (2 * (J + 1))) /
        (Real.log T) ^ (2 * J + 1) := by
  apply (normalized_horizontalTaylorError_of_selberg T u C a J hT hC ha hu hD).trans_eq
  have hL : 0 < Real.log T := Real.log_pos hT
  have hup : |u| ^ (2 * (J + 1)) = u ^ (2 * (J + 1)) := by
    rw [pow_mul, sq_abs, ← pow_mul]
  simp only [div_pow, mul_pow, hup]
  have hexp : 2 * (J + 1) = (2 * J + 1) + 1 := by omega
  rw [hexp]
  simp only [pow_succ]
  field_simp

/-- Actual source error at every fixed correction order, uniform over all
integers in the stated growing logarithmic band. -/
theorem eventually_correctedSignal_error_all_orders (J : ℕ)
    (a : ℝ) (ha : 0 < a) (hD : UniformSelbergDensity a) :
    ∃ B C : ℝ, 0 < B ∧ 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ q : ℕ,
      1 < q → Real.log (q : ℝ) ≤ Real.log T / 8 →
      Real.log (q : ℝ) ≤ a * Real.log T / 2 →
      |correctedSignal J q T - ArithmeticFunction.vonMangoldt q| ≤
        higherSignalWeight J B C a q / (Real.log T) ^ (2 * J + 1) := by
  obtain ⟨B, hB, hL⟩ := eventually_rational_landau_error_le_inv_log_pow (2 * J + 1)
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hD
  refine ⟨B, C, hB, hC, ?_⟩
  filter_upwards [hL, eventually_ge_atTop T₀] with T hL hT
  intro q hq hqL hqa
  have hT1 : 1 < T := hT₀.trans_le hT
  have hu : |Real.log (q : ℝ)| ≤ a * Real.log T / 2 := by
    rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q)))]
    exact hqa
  have hl := hL q 1 (by norm_num) hq hqL
  simp only [Nat.cast_one, div_one] at hl
  have hh := horizontalTaylorError_inverse_log_power J T (Real.log (q : ℝ))
    C a hT1 hC ha hu (hD T hT)
  have h := correctedSignal_error_abs_le J q hq T _ _
    (ne_of_gt (by linarith : 0 < T)) hl hh
  apply h.trans_eq
  unfold higherSignalWeight
  ring

/-- A uniform finite-support certificate with the full inverse matrix and
every prime-power coordinate retained. No growing-order uniformity is claimed. -/
theorem eventually_corrected_metric_all_orders (J : ℕ)
    (a : ℝ) (ha : 0 < a) (hD : UniformSelbergDensity a) :
    ∃ B C : ℝ, 0 < B ∧ 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (s : Finset ℕ) (hs : ∀ q ∈ s, 1 < q),
      (∀ q ∈ s, Real.log (q : ℝ) ≤ Real.log T / 8) →
      (∀ q ∈ s, Real.log (q : ℝ) ≤ a * Real.log T / 2) →
      inverseNorm (family_independent s hs) (correctedVector J s T - signal s) ^ 2 ≤
        inverseGramWeightBudget s (higherSignalWeight J B C a) /
          (Real.log T) ^ (4 * J + 2) := by
  obtain ⟨B, C, hB, hC, he⟩ := eventually_correctedSignal_error_all_orders J a ha hD
  refine ⟨B, C, hB, hC, ?_⟩
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with T he hT
  intro s hs hband hbandA
  have hL : 0 < Real.log T := Real.log_pos hT
  have h := corrected_metric_sq_le J s hs T (1 / (Real.log T) ^ (2 * J + 1))
    (higherSignalWeight J B C a) (by positivity)
    (fun q _ => higherSignalWeight_nonneg J B C a q hB.le hC)
    (fun q hq => by
      simpa only [mul_one_div] using he q (hs q hq) (hband q hq) (hbandA q hq))
  apply h.trans_eq
  rw [div_pow, one_pow, ← pow_mul,
    show (2 * J + 1) * 2 = 4 * J + 2 by omega]
  ring

end RiemannResearch.RH.RamanujanFRZSignal
