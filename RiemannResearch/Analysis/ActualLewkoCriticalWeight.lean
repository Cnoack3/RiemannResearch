/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualCriticalFarStrip
import RiemannResearch.Analysis.ActualLewkoDensity

/-!
# Critical exponential mass strictly beyond quarter displacement

The right branch of Lewko's verified density curve is uniform on every
closed strip of fixed positive distance from three quarters. It reduces
the displacement threshold for both critical-weight estimates to 1/4.
The endpoint 1/4 is deliberately absent. At fixed zero-free support B the
power exponent is the exact maximum of the two endpoint exponents.
-/

noncomputable section
open Filter Set Zeta23

namespace RiemannResearch.Analysis.ActualZeroOrdinate

def lewkoCriticalWeightExponent (σ₀ B : ℝ) : ℝ :=
  max (bourgainWeightedExcess σ₀) (bourgainWeightedExcess B)

theorem lewkoCriticalWeightExponent_neg {σ₀ B : ℝ} (h₀ : 3 / 4 < σ₀)
    (h₀B : σ₀ ≤ B) (hB : B < 1) : lewkoCriticalWeightExponent σ₀ B < 0 := by
  have hn {x : ℝ} (hx : 3 / 4 < x) (hx' : x < 1) : bourgainWeightedExcess x < 0 := by
    apply mul_neg_of_neg_of_pos _ (sub_pos.mpr hx')
    apply sub_neg.mpr ((div_lt_iff₀ (by linarith : 0 < 2 * x)).mpr ?_)
    linarith only [hx]
  exact max_lt (hn h₀ (h₀B.trans_lt hB)) (hn (h₀.trans_le h₀B) hB)

/-- The all-heights constant precedes every abscissa on this compact strip. -/
theorem weighted_compact_count_of_lewko (hL : LewkoDensityHypothesis)
    {σ₀ B ε : ℝ} (h₀ : 3 / 4 < σ₀) (h₀B : σ₀ ≤ B) (hB : B ≤ 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∀ σ ∈ Icc σ₀ B,
      rightInclusiveCount T σ * T ^ (2 * (σ - 1 / 2)) ≤
        C * T ^ (1 + (lewkoCriticalWeightExponent σ₀ B + ε)) := by
  obtain ⟨C, hC, hc⟩ := uniform_lewko_density_away_from_boundary hL (sub_pos.mpr h₀) hε
  refine ⟨C, hC, ?_⟩
  intro T hT σ hσ
  have hTp : 0 < T := by linarith
  have hgt := h₀.trans_le hσ.1
  have hcoef : lewkoDensityCoefficient σ = 3 / (2 * σ) := by
    have h₁ : ¬ σ ≤ 9 / 13 := by linarith only [hgt]
    have h₂ : ¬ σ ≤ 5 / 7 := by linarith only [hgt]
    simp [lewkoDensityCoefficient, h₁, h₂, not_le.mpr hgt]
  have h := hc σ ⟨by linarith only [hgt], hσ.2.trans hB⟩
    (Or.inr (by linarith only [hσ.1])) T hT
  rw [hcoef] at h
  have hex := bourgainWeightedExcess_le_endpoints (by linarith only [h₀]) hσ.1 hσ.2
  change (3 / (2 * σ) - 2) * (1 - σ) ≤ lewkoCriticalWeightExponent σ₀ B at hex
  calc
    _ ≤ (C * T ^ (3 / (2 * σ) * (1 - σ) + ε)) * T ^ (2 * (σ - 1 / 2)) :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hTp.le _)
    _ = C * T ^ ((3 / (2 * σ) * (1 - σ) + ε) + 2 * (σ - 1 / 2)) := by
      rw [mul_assoc, ← Real.rpow_add hTp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith)
      (by linarith only [hex])) hC.le

/-- Under any fixed zero-free half-plane, the exact upper support and
the fixed lower endpoint determine the optimized b = 2 power saving. -/
theorem normalized_critical_weight_of_lewko {B σ₀ : ℝ}
    (hZ : ZetaZeroFreeHalfPlane B) (hL : LewkoDensityHypothesis)
    (h₀ : 3 / 4 < σ₀) (h₀B : σ₀ ≤ B) (hB : B ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      badWeightedSum T (σ₀ - 1 / 2) (fun t => Real.exp (2 * Real.log T * t)) /
        (Ncount 0 T : ℝ) ≤ C * T ^ (lewkoCriticalWeightExponent σ₀ B + ε) := by
  apply normalized_critical_weight_of_compact_count hZ (by linarith only [h₀]) h₀B hB
  obtain ⟨C, hC, hc⟩ := weighted_compact_count_of_lewko hL h₀ h₀B hB hε
  exact ⟨C, hC, (eventually_ge_atTop (2 : ℝ)).mono fun T hT => hc T hT⟩

theorem normalized_critical_weight_power_saving_of_lewko
    (hZ : ContinuumContactNonvanishing) (hL : LewkoDensityHypothesis)
    {δ : ℝ} (hδ : 1 / 4 < δ) (hB : 1 / 2 + δ ≤ continuumContact) :
    0 < -lewkoCriticalWeightExponent (1 / 2 + δ) continuumContact ∧
    ∀ η : ℝ, 0 < η → η < -lewkoCriticalWeightExponent (1 / 2 + δ) continuumContact →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
        badWeightedSum T δ (fun t => Real.exp (2 * Real.log T * t)) / (Ncount 0 T : ℝ) ≤ C * T ^ (-η) := by
  have hlo : 3 / 4 < 1 / 2 + δ := by linarith only [hδ]
  have hhi : continuumContact < 1 := by linarith only [continuumContact_mem.2]
  have hm := lewkoCriticalWeightExponent_neg hlo hB hhi
  refine ⟨neg_pos.mpr hm, ?_⟩
  intro η _hη heta
  let ε := -lewkoCriticalWeightExponent (1 / 2 + δ) continuumContact - η
  have he := normalized_critical_weight_of_lewko hZ hL hlo hB hhi.le (show 0 < ε from sub_pos.mpr heta)
  have hh : lewkoCriticalWeightExponent (1 / 2 + δ) continuumContact + ε = -η := by
    dsimp [ε]; ring
  simpa only [hh, add_sub_cancel_left] using he

/-- The same threshold gives every logarithmic saving without a fixed
zero-free half-plane. Here Bellotti's eventual per-ordinate theorem is
the zero-free input, and Huxley treats the moving rightmost part. -/
theorem normalized_critical_weight_superlog_of_lewko
    (hL : LewkoDensityHypothesis) (hH : HuxleyDensityHypothesis)
    (hv : BellottiKorobovVinogradovNonvanishing) {δ : ℝ} (hδ : δ ∈ Ioc (1 / 4 : ℝ) (1 / 2))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      badWeightedSum T δ (fun t => Real.exp (2 * Real.log T * t)) / (Ncount 0 T : ℝ) ≤
        C * (Real.log T) ^ (-A) := by
  by_cases hhigh : 1 / 3 < δ
  · exact normalized_critical_weight_superlog_of_huxley hH (bellotti_count_of_nonvanishing hv)
      ⟨hhigh, hδ.2⟩ A hA
  let lo := 1 / 2 + δ
  let hi := (7 / 8 : ℝ)
  have hlo : 3 / 4 < lo := by dsimp [lo]; linarith only [hδ.1]
  have hgap : lo ≤ hi := by dsimp [lo, hi]; linarith only [le_of_not_gt hhigh]
  let E := lewkoCriticalWeightExponent lo hi
  have hE : E < 0 := lewkoCriticalWeightExponent_neg hlo hgap (by norm_num [hi])
  have he : E / 2 < 0 := by linarith
  apply normalized_critical_weight_superlog_of_compact_count ⟨by linarith only [hδ.1], hδ.2⟩ he _
    hH (bellotti_count_of_nonvanishing hv) A hA
  obtain ⟨C, hC, hc⟩ := weighted_compact_count_of_lewko hL hlo hgap (by norm_num [hi] : hi ≤ 1)
    (show 0 < -E / 2 by linarith)
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
  have h := hc T hT
  have hh : 1 + (lewkoCriticalWeightExponent lo hi + -E / 2) = 1 + E / 2 := by
    change 1 + (E + -E / 2) = 1 + E / 2
    ring
  simpa only [hh] using h

end RiemannResearch.Analysis.ActualZeroOrdinate
