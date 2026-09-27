/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.IncreasingStretchedWeights
import RiemannResearch.RH.DampedMobiusHalfHilbertLoglogStretchedRate
import RiemannResearch.RH.DampedMobiusUniformHalfRange

/-!
The optimized half-endpoint error profile transfers to a moving subhalf
band of width c*(L*log L)^(1/11)/L, L=6+log(M+1), for every fixed c below
the endpoint decay constant. The complete signed vector converges.
No finite energy at any fixed epsilon below one half is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Quantitative moving-band transfer at the full optimized profile. -/
theorem dampedMobius_loglog_stretched_subhalf_band_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c → c < a →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, ∀ ε : ℝ, ε ≤ (1 / 2 : ℝ) →
        ((1 / 2 : ℝ) - ε) * (6 + Real.log ((M + 1 : ℕ) : ℝ)) ≤
          c * logProductPower (1 / 11) (6 + Real.log ((M + 1 : ℕ) : ℝ)) →
        ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M -
          dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
            C * Real.exp (-(a - c) * logProductPower (1 / 11)
              (6 + Real.log ((M + 1 : ℕ) : ℝ))) + B * ((1 / 2 : ℝ) - ε) := by
  obtain ⟨a, ha, C, hC, herror⟩ := dampedMobius_half_cutoffs_loglog_stretched_rate
  refine ⟨a, ha, C, hC, fun c hc hca => ?_⟩
  let u := fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m
  let f := dampedMobiusHalfRangeLimit (1 / 2) le_rfl
  have he (n : ℕ) : ‖signedVectorPrefix u n - f‖ ≤
      C * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log ((n + 1 : ℕ) : ℝ))) := by
    simpa only [u, f, signedVectorPrefix, Finset.sum_neg_distrib,
      arithmeticFloorHilbertPartial] using herror n
  obtain ⟨B, hB, hb⟩ := signedVector_logProductPower_band_bound u f C a c (1 / 11)
    hC hc hca (by norm_num) (by norm_num) he
  refine ⟨B, hB, fun M ε hε hband => ?_⟩
  have h := hb M ((1 / 2 : ℝ) - ε) (sub_nonneg.mpr hε) hband
  rw [dampedMobiusPartial_from_half]
  simpa only [u, f, show -(ε - 1 / 2) = (1 / 2 : ℝ) - ε by ring] using h

/-- Every fixed coefficient below the verified endpoint decay constant
gives full Hilbert convergence in the optimized moving band. -/
theorem dampedMobius_loglog_stretched_subhalf_band_tendsto :
    ∃ a : ℝ, 0 < a ∧ ∀ c : ℝ, 0 ≤ c → c < a →
      ∀ (ε : ℕ → ℝ), (∀ j, ε j ≤ (1 / 2 : ℝ)) →
      ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
      (∀ᶠ j in atTop,
        ((1 / 2 : ℝ) - ε j) * (6 + Real.log ((M j + 1 : ℕ) : ℝ)) ≤
          c * logProductPower (1 / 11) (6 + Real.log ((M j + 1 : ℕ) : ℝ))) →
      Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
        atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
  obtain ⟨a, ha, C, hC, herror⟩ := dampedMobius_half_cutoffs_loglog_stretched_rate
  refine ⟨a, ha, fun c hc hca ε hε M hM hband => ?_⟩
  let u := fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m
  let f := dampedMobiusHalfRangeLimit (1 / 2) le_rfl
  have he (n : ℕ) : ‖signedVectorPrefix u n - f‖ ≤
      C * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log ((n + 1 : ℕ) : ℝ))) := by
    simpa only [u, f, signedVectorPrefix, Finset.sum_neg_distrib,
      arithmeticFloorHilbertPartial] using herror n
  have h := signedVector_logProductPower_band_tendsto u f C a c (1 / 11)
    hC hc hca (by norm_num) (by norm_num) he M hM
    (fun j => (1 / 2 : ℝ) - ε j) (fun j => sub_nonneg.mpr (hε j)) hband
  convert h using 1
  funext j
  rw [dampedMobiusPartial_from_half]
  simp only [u, f, show -(ε j - 1 / 2) = (1 / 2 : ℝ) - ε j by ring]

/-- Membership in the optimized conductor band; subhalf damping is
quantified separately in the convergence statements. -/
def dampedMobiusLoglogStretchedBand (c : ℝ) (M : ℕ) (ε : ℝ) : Prop :=
  ((1 / 2 : ℝ) - ε) * (6 + Real.log ((M + 1 : ℕ) : ℝ)) ≤
    c * logProductPower (1 / 11) (6 + Real.log ((M + 1 : ℕ) : ℝ))

/-- One endpoint decay constant works simultaneously for every smaller
fixed moving-band coefficient. Energy means the whole signed Hilbert
norm squared, including all off-diagonal contributions. -/
structure DampedMobiusLoglogStretchedBandPackage (a C : ℝ) : Prop where
  endpoint : ∀ M : ℕ,
    ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
      dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
        C * Real.exp (-a * logProductPower (1 / 11)
          (6 + Real.log ((M + 1 : ℕ) : ℝ)))
  quantitative : ∀ c : ℝ, 0 ≤ c → c < a →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, ∀ ε : ℝ, ε ≤ (1 / 2 : ℝ) →
      dampedMobiusLoglogStretchedBand c M ε →
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
          C * Real.exp (-(a - c) * logProductPower (1 / 11)
            (6 + Real.log ((M + 1 : ℕ) : ℝ))) + B * ((1 / 2 : ℝ) - ε)
  norm_tendsto : ∀ c : ℝ, 0 ≤ c → c < a →
    ∀ (ε : ℕ → ℝ), (∀ j, ε j ≤ (1 / 2 : ℝ)) →
    ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    (∀ᶠ j in atTop, dampedMobiusLoglogStretchedBand c (M j) (ε j)) →
    Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
      atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl))
  norm_uniform : ∀ c : ℝ, 0 ≤ c → c < a →
    ∀ η : ℝ, 0 < η → ∃ J : ℕ, ∀ M : ℕ, J ≤ M → ∀ ε : ℝ,
      ε ≤ (1 / 2 : ℝ) → dampedMobiusLoglogStretchedBand c M ε →
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤ η
  energy_tendsto : ∀ c : ℝ, 0 ≤ c → c < a →
    ∀ (ε : ℕ → ℝ), (∀ j, ε j ≤ (1 / 2 : ℝ)) →
    ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
    (∀ᶠ j in atTop, dampedMobiusLoglogStretchedBand c (M j) (ε j)) →
    Tendsto (fun j => ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j)‖ ^ 2)
      atTop (𝓝 (∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
          (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ^ 2))
  energy_uniform : ∀ c : ℝ, 0 ≤ c → c < a →
    ∀ η : ℝ, 0 < η → ∃ J : ℕ, ∀ M : ℕ, J ≤ M → ∀ ε : ℝ,
      ε ≤ (1 / 2 : ℝ) → dampedMobiusLoglogStretchedBand c M ε →
      |‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ^ 2 -
        ‖dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ^ 2| ≤ η

/-- Shared constants for the endpoint rate and the complete sequential
and uniform moving-band norm/energy conclusions. -/
theorem dampedMobius_loglog_stretched_subhalf_band_package :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧
      DampedMobiusLoglogStretchedBandPackage a C := by
  obtain ⟨a, ha, C, hC, herror⟩ := dampedMobius_half_cutoffs_loglog_stretched_rate
  let u := fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m
  let f := dampedMobiusHalfRangeLimit (1 / 2) le_rfl
  have he (n : ℕ) : ‖signedVectorPrefix u n - f‖ ≤
      C * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log ((n + 1 : ℕ) : ℝ))) := by
    simpa only [u, f, signedVectorPrefix, Finset.sum_neg_distrib,
      arithmeticFloorHilbertPartial] using herror n
  have hseq : ∀ c : ℝ, 0 ≤ c → c < a →
      ∀ (ε : ℕ → ℝ), (∀ j, ε j ≤ (1 / 2 : ℝ)) →
      ∀ (M : ℕ → ℕ), Tendsto M atTop atTop →
      (∀ᶠ j in atTop, dampedMobiusLoglogStretchedBand c (M j) (ε j)) →
      Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
        atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
    intro c hc hca ε hε M hM hband
    have h := signedVector_logProductPower_band_tendsto u f C a c (1 / 11)
      hC hc hca (by norm_num) (by norm_num) he M hM
      (fun j => (1 / 2 : ℝ) - ε j) (fun j => sub_nonneg.mpr (hε j)) hband
    convert h using 1
    funext j
    rw [dampedMobiusPartial_from_half]
    simp only [u, f, show -(ε j - 1 / 2) = (1 / 2 : ℝ) - ε j by ring]
  refine ⟨a, ha, C, hC, ?_⟩
  refine ⟨herror, ?_, hseq, ?_, ?_, ?_⟩
  · intro c hc hca
    obtain ⟨B, hB, hb⟩ := signedVector_logProductPower_band_bound u f C a c (1 / 11)
      hC hc hca (by norm_num) (by norm_num) he
    refine ⟨B, hB, fun M ε hε hband => ?_⟩
    have h := hb M ((1 / 2 : ℝ) - ε) (sub_nonneg.mpr hε) hband
    rw [dampedMobiusPartial_from_half]
    simpa only [u, f, show -(ε - 1 / 2) = (1 / 2 : ℝ) - ε by ring] using h
  · intro c hc hca η hη
    by_contra h
    push Not at h
    choose M hMJ ε hε hband hbad using h
    have hM : Tendsto M atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop b] with j hj
      exact hj.trans (hMJ j)
    have hv := hseq c hc hca ε hε M hM (Eventually.of_forall hband)
    obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hv η hη
    have hgood : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε J)) (M J) -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ < η := by
      simpa only [dist_eq_norm] using hJ J le_rfl
    linarith [hbad J]
  · intro c hc hca ε hε M hM hband
    have h := (hseq c hc hca ε hε M hM hband).norm.pow 2
    simpa only [hilbert_norm_weighted_sq,
      (dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl).1] using h
  · intro c hc hca η hη
    by_contra h
    push Not at h
    choose M hMJ ε hε hband hbad using h
    have hM : Tendsto M atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [eventually_ge_atTop b] with j hj
      exact hj.trans (hMJ j)
    have hv := (hseq c hc hca ε hε M hM (Eventually.of_forall hband)).norm.pow 2
    obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hv η hη
    have hgood : |‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε J)) (M J)‖ ^ 2 -
        ‖dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ^ 2| < η := by
      simpa only [dist_eq_norm, Real.norm_eq_abs] using hJ J le_rfl
    linarith [hbad J]

end RiemannResearch.RH.Pareto
