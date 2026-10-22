/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.SpectralDiagonalRealization

/-!
# Source mass, spectral polarization, and a stable cutoff

Source: independently developed continuation of the source-weighted two-seed
spectral problem, 15 September 2026. The existing cutoff convention retains
eigenvalues at least the threshold, so omitted mass is strictly below it.
The new estimates distinguish concentration near the spectral endpoints from
the unknown amount of source mass near zero. They give no arithmetic decay.
-/

open scoped BigOperators
namespace RiemannResearch.LinearAlgebra.SpectralCutoff
noncomputable section

/-- Spectral distance from the two endpoints, weighted by the actual source. -/
def polarizationTerm (lam μ : ℝ) : ℝ := lam * (1 - lam) * μ

private theorem scaled_omitted_lower {τ lam μ : ℝ}
    (hτ : 0 < τ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hμ : 0 ≤ μ) :
    τ * (optimalTerm lam μ - omittedTerm τ lam μ) ≤ polarizationTerm lam μ := by
  unfold optimalTerm omittedTerm polarizationTerm
  split_ifs with h
  · have hm := mul_le_mul_of_nonneg_right h (mul_nonneg (sub_nonneg.mpr hlam1) hμ)
    nlinarith
  · have hp := mul_nonneg (mul_nonneg hlam0 (sub_nonneg.mpr hlam1)) hμ
    have hn := mul_nonneg hτ.le (mul_nonneg hlam0 hμ)
    nlinarith

private theorem scaled_omitted_upper {τ lam μ : ℝ}
    (hτ1 : τ < 1) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hμ : 0 ≤ μ) :
    (1 - τ) * (omittedTerm τ lam μ - optimalTerm lam μ) ≤ polarizationTerm lam μ := by
  unfold optimalTerm omittedTerm polarizationTerm
  split_ifs with h
  · have hp := mul_nonneg (mul_nonneg hlam0 (sub_nonneg.mpr hlam1)) hμ
    have hn := mul_nonneg (sub_nonneg.mpr hτ1.le)
      (mul_nonneg (sub_nonneg.mpr hlam1) hμ)
    nlinarith
  · have hlt : lam < τ := lt_of_not_ge h
    have hm := mul_nonneg (sub_nonneg.mpr hlt.le) (mul_nonneg hlam0 hμ)
    nlinarith

private theorem scaled_cutoff_tail {τ lam μ : ℝ}
    (hτ : 0 < τ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hμ : 0 ≤ μ) :
    τ ^ 2 * (errorTerm τ lam μ - omittedTerm τ lam μ) ≤ polarizationTerm lam μ := by
  unfold errorTerm omittedTerm polarizationTerm
  split_ifs with h
  · have hp : 0 < lam := hτ.trans_le h
    have hn : lam ≠ 0 := ne_of_gt hp
    have he : lam * ((lam⁻¹ - 1) * μ) = (1 - lam) * μ := by
      field_simp [hn]
    have htail : 0 ≤ (lam⁻¹ - 1) * μ := by
      have hi : 1 ≤ lam⁻¹ := (one_le_inv₀ hp).mpr hlam1
      exact mul_nonneg (sub_nonneg.mpr hi) hμ
    have hs : τ ^ 2 ≤ lam ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hs htail
    nlinarith [congrArg (fun x : ℝ => lam * x) he]
  · simpa using mul_nonneg (mul_nonneg hlam0 (sub_nonneg.mpr hlam1)) hμ

private theorem scaled_cutoff_norm {τ lam μ : ℝ}
    (hτ : 0 < τ) (hμ : 0 ≤ μ) : τ * normTerm τ lam μ ≤ μ := by
  unfold normTerm
  split_ifs with h
  · have hp : 0 < lam := hτ.trans_le h
    have hi : 0 ≤ lam⁻¹ * μ := mul_nonneg (inv_nonneg.mpr hp.le) hμ
    have hm := mul_le_mul_of_nonneg_right h hi
    simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hp), one_mul] using hm
  · simpa using hμ

variable {ι : Type*}

def polarization (s : Finset ι) (lam μ : ι → ℝ) : ℝ :=
  ∑ i ∈ s, polarizationTerm (lam i) (μ i)

/-- A quantitative comparison with ordinary projection error at every finite stage. -/
theorem omittedMass_bounds (s : Finset ι) {τ : ℝ} (lam μ : ι → ℝ)
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (hlam0 : ∀ i ∈ s, 0 ≤ lam i) (hlam1 : ∀ i ∈ s, lam i ≤ 1)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    optimalError s lam μ - polarization s lam μ / τ ≤ omittedMass s τ lam μ ∧
      omittedMass s τ lam μ ≤
        optimalError s lam μ + polarization s lam μ / (1 - τ) := by
  have hlo : τ * (optimalError s lam μ - omittedMass s τ lam μ) ≤
      polarization s lam μ := by
    simpa only [optimalError, omittedMass, polarization, Finset.mul_sum,
      Finset.sum_sub_distrib, mul_sub] using
      (Finset.sum_le_sum fun i hi => scaled_omitted_lower hτ
        (hlam0 i hi) (hlam1 i hi) (hμ i hi))
  have hhi : (1 - τ) * (omittedMass s τ lam μ - optimalError s lam μ) ≤
      polarization s lam μ := by
    simpa only [optimalError, omittedMass, polarization, Finset.mul_sum,
      Finset.sum_sub_distrib, mul_sub] using
      (Finset.sum_le_sum fun i hi => scaled_omitted_upper hτ1
        (hlam0 i hi) (hlam1 i hi) (hμ i hi))
  have hl : optimalError s lam μ - omittedMass s τ lam μ ≤ polarization s lam μ / τ :=
    (le_div_iff₀ hτ).mpr (by simpa only [mul_comm] using hlo)
  have hu : omittedMass s τ lam μ - optimalError s lam μ ≤
      polarization s lam μ / (1 - τ) :=
    (le_div_iff₀ (sub_pos.mpr hτ1)).mpr (by simpa only [mul_comm] using hhi)
  constructor <;> linarith

/-- The half-cutoff source mass differs from the defect by at most twice the leakage. -/
theorem half_mass_defect_bound (s : Finset ι) (lam μ : ι → ℝ)
    (hlam0 : ∀ i ∈ s, 0 ≤ lam i) (hlam1 : ∀ i ∈ s, lam i ≤ 1)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    |omittedMass s (1 / 2) lam μ - optimalError s lam μ| ≤
      2 * polarization s lam μ := by
  obtain ⟨hl, hu⟩ := omittedMass_bounds s lam μ (τ := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) hlam0 hlam1 hμ
  norm_num at hl hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Stable cutoff error uses omitted mass and the complete boundary leakage. -/
theorem cutoffError_le_mass_add_polarization (s : Finset ι) {τ : ℝ} (lam μ : ι → ℝ)
    (hτ : 0 < τ)
    (hlam0 : ∀ i ∈ s, 0 ≤ lam i) (hlam1 : ∀ i ∈ s, lam i ≤ 1)
    (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    cutoffError s τ lam μ ≤ omittedMass s τ lam μ + polarization s lam μ / τ ^ 2 := by
  have hs : τ ^ 2 * (cutoffError s τ lam μ - omittedMass s τ lam μ) ≤
      polarization s lam μ := by
    simpa only [cutoffError, omittedMass, polarization, Finset.mul_sum,
      Finset.sum_sub_distrib, mul_sub] using
      (Finset.sum_le_sum fun i hi => scaled_cutoff_tail hτ
        (hlam0 i hi) (hlam1 i hi) (hμ i hi))
  have hd : cutoffError s τ lam μ - omittedMass s τ lam μ ≤
      polarization s lam μ / τ ^ 2 :=
    (le_div_iff₀ (sq_pos_of_pos hτ)).mpr (by simpa only [mul_comm] using hs)
  linarith

/-- A fixed positive cutoff bounds the complete synthesis norm uniformly. -/
theorem cutoffNorm_le_mass_div (s : Finset ι) {τ : ℝ} (lam μ : ι → ℝ)
    (hτ : 0 < τ) (hμ : ∀ i ∈ s, 0 ≤ μ i) :
    cutoffNorm s 0 τ lam μ ≤ targetMass s μ / τ := by
  apply (le_div_iff₀ hτ).mpr
  simp only [cutoffNorm, zero_add, targetMass, Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => by
    simpa only [mul_comm] using scaled_cutoff_norm hτ (hμ i hi)

/-- Small polarization alone gives no small omitted mass, even in a single mode. -/
theorem arbitrarily_small_polarization_full_omission {ε : ℝ} (hε : 0 < ε) :
    ∃ lam : ℝ, 0 < lam ∧ lam < 1 / 2 ∧
      polarizationTerm lam 1 < ε ∧ omittedTerm (1 / 2) lam 1 = 1 := by
  let lam : ℝ := min (ε / 2) (1 / 4)
  have hp : 0 < lam := lt_min (by positivity) (by norm_num)
  have hl : lam ≤ 1 / 4 := min_le_right _ _
  have he : lam ≤ ε / 2 := min_le_left _ _
  have hh : lam < 1 / 2 := by linarith
  refine ⟨lam, hp, hh, ?_, ?_⟩
  · unfold polarizationTerm
    nlinarith [sq_nonneg lam]
  · simp only [omittedTerm, if_neg (not_le.mpr hh)]

end
end RiemannResearch.LinearAlgebra.SpectralCutoff
