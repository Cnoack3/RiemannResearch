/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualAbsoluteZeroDensityCount
import RiemannResearch.Analysis.ActualGuthMaynardFixedStrip

/-!
# Lewko's independently verified density curve and the published envelope

The Palomar registration PALOMAR-2026-10-11-000010 v1 records the
all-height statements `global_uniform` and `uniform_away_boundary` in
Mark Lewko's `mrklwk/zeta-density-39-over-17-lean` at commit
`ee2a8a32be49a4f73c7386e9dffdea24d7e3d8c0`. Its Lean 4.35.0-rc2
kernel comparison, nanoda and con-ron checks were recorded on October 9,
2026. This module types those two results as explicit source inputs and
proves the transfer to this repository's positive-ordinate cutoff. The
strongest branch is open at three quarters.

Source: https://palomar-registry.org/entry?id=PALOMAR-2026-10-11-000010&version=1 .
-/

noncomputable section
open Filter Set Zeta23

namespace RiemannResearch.Analysis.ActualZeroOrdinate

def lewkoDensityCoefficient (σ : ℝ) : ℝ :=
  if σ ≤ 9 / 13 then 3 / (2 - σ)
  else if σ ≤ 5 / 7 then 18 / (7 * σ + 3)
  else if σ ≤ 3 / 4 then 9 / 4
  else 3 / (2 * σ)

structure LewkoDensityHypothesis : Prop where
  global_uniform : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (1 / 2 : ℝ) 1,
    ∀ T : ℝ, 2 ≤ T → AbsoluteZeroCountBound σ T (C * T ^ ((39 / 17) * (1 - σ) + ε))
  uniform_away_boundary : ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ σ ∈ Icc (1 / 2 : ℝ) 1, (σ ≤ 3 / 4 ∨ 3 / 4 + δ ≤ σ) → ∀ T : ℝ, 2 ≤ T →
      AbsoluteZeroCountBound σ T (C * T ^ (lewkoDensityCoefficient σ * (1 - σ) + ε))

theorem uniform_lewko_density_global (h : LewkoDensityHypothesis) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (1 / 2 : ℝ) 1, ∀ T : ℝ, 2 ≤ T →
      rightInclusiveCount T σ ≤ C * T ^ ((39 / 17) * (1 - σ) + ε) := by
  obtain ⟨C, hC, hh⟩ := h.global_uniform ε hε
  exact ⟨C, hC, fun σ hσ T hT => rightInclusiveCount_le_of_absoluteZeroCountBound (hh σ hσ T hT)⟩

theorem uniform_lewko_density_away_from_boundary (h : LewkoDensityHypothesis)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Icc (1 / 2 : ℝ) 1, (σ ≤ 3 / 4 ∨ 3 / 4 + δ ≤ σ) →
      ∀ T : ℝ, 2 ≤ T →
        rightInclusiveCount T σ ≤ C * T ^ (lewkoDensityCoefficient σ * (1 - σ) + ε) := by
  obtain ⟨C, hC, hh⟩ := h.uniform_away_boundary δ ε hδ hε
  exact ⟨C, hC, fun σ hσ hg T hT => rightInclusiveCount_le_of_absoluteZeroCountBound
    (hh σ hσ hg T hT)⟩

theorem fixed_lewko_density (h : LewkoDensityHypothesis) {σ ε : ℝ}
    (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      rightInclusiveCount T σ ≤ C * T ^ (lewkoDensityCoefficient σ * (1 - σ) + ε) := by
  by_cases hb : σ ≤ 3 / 4
  · obtain ⟨C, hC, hc⟩ := uniform_lewko_density_away_from_boundary h (δ := 1) zero_lt_one hε
    exact ⟨C, hC, hc σ hσ (Or.inl hb)⟩
  · obtain ⟨C, hC, hc⟩ := uniform_lewko_density_away_from_boundary h
      (δ := σ - 3 / 4) (sub_pos.mpr (lt_of_not_ge hb)) hε
    exact ⟨C, hC, hc σ hσ (Or.inr (by linarith))⟩

/-- The best pointwise coefficient from the published Guth–Maynard
curve and Lewko's registered result. The exact maximum is attained at 9/13.
The endpoint three quarters uses Guth–Maynard. -/
def lewkoGuthMaynardCoefficient (σ : ℝ) : ℝ := min (lewkoDensityCoefficient σ) (15 / (3 + 5 * σ))

theorem lewkoGuthMaynardCoefficient_eq {σ : ℝ} (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    lewkoGuthMaynardCoefficient σ =
      if σ ≤ 9 / 13 then 3 / (2 - σ)
      else if σ ≤ 5 / 7 then 18 / (7 * σ + 3)
      else if σ ≤ 11 / 15 then 9 / 4
      else if σ ≤ 3 / 4 then 15 / (3 + 5 * σ)
      else 3 / (2 * σ) := by
  have hg : 0 < 3 + 5 * σ := by linarith only [hσ.1]
  have hi : 0 < 2 - σ := by linarith only [hσ.2]
  have hm : 0 < 7 * σ + 3 := by linarith only [hσ.1]
  have hr : 0 < 2 * σ := by linarith only [hσ.1]
  unfold lewkoGuthMaynardCoefficient lewkoDensityCoefficient
  by_cases h₁ : σ ≤ 9 / 13
  · simp only [if_pos h₁]
    exact min_eq_left ((div_le_div_iff₀ hi hg).mpr (by linarith only [h₁]))
  by_cases h₂ : σ ≤ 5 / 7
  · simp only [if_neg h₁, if_pos h₂]
    exact min_eq_left ((div_le_div_iff₀ hm hg).mpr (by linarith only [lt_of_not_ge h₁]))
  by_cases h₃ : σ ≤ 11 / 15
  · have h₄ : σ ≤ 3 / 4 := by linarith only [h₃]
    simp only [if_neg h₁, if_neg h₂, if_pos h₃, if_pos h₄]
    exact min_eq_left ((le_div_iff₀ hg).mpr (by linarith only [h₃]))
  by_cases h₄ : σ ≤ 3 / 4
  · simp only [if_neg h₁, if_neg h₂, if_neg h₃, if_pos h₄]
    exact min_eq_right ((div_le_iff₀ hg).mpr (by linarith only [lt_of_not_ge h₃]))
  simp only [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄]
  exact min_eq_left ((div_le_div_iff₀ hr hg).mpr (by linarith only [lt_of_not_ge h₄]))

theorem lewkoGuthMaynardCoefficient_max {σ : ℝ} (hσ : σ ∈ Icc (1 / 2 : ℝ) 1) :
    lewkoGuthMaynardCoefficient σ ≤ 39 / 17 ∧
      lewkoGuthMaynardCoefficient (9 / 13) = 39 / 17 := by
  constructor
  · rw [lewkoGuthMaynardCoefficient_eq hσ]
    split_ifs with h₁ h₂ h₃ h₄
    · apply (div_le_iff₀ (by linarith only [hσ.2] : 0 < 2 - σ)).mpr
      linarith only [h₁]
    · apply (div_le_iff₀ (by linarith only [hσ.1] : 0 < 7 * σ + 3)).mpr
      linarith only [lt_of_not_ge h₁]
    · norm_num
    · apply (div_le_iff₀ (by linarith only [hσ.1] : 0 < 3 + 5 * σ)).mpr
      linarith only [lt_of_not_ge h₃]
    · apply (div_le_iff₀ (by linarith only [hσ.1] : 0 < 2 * σ)).mpr
      linarith only [lt_of_not_ge h₄]
  · norm_num [lewkoGuthMaynardCoefficient, lewkoDensityCoefficient]

/-- All three complete majorants remain available at a fixed abscissa.
In particular the locally proved Ingham logarithm survives in the minimum. -/
theorem exists_ingham_guthMaynard_lewko_count (hG : GuthMaynardDensityHypothesis)
    (hL : LewkoDensityHypothesis) :
    ∃ B : ℝ, 0 < B ∧ ∀ σ ∈ Icc (1 / 2 : ℝ) 1, ∀ ε : ℝ, 0 < ε →
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ᶠ T : ℝ in atTop,
        let q := 3 * (1 - σ) / (2 - σ)
        rightInclusiveCount T σ ≤ min (D * T ^ (lewkoDensityCoefficient σ * (1 - σ) + ε))
          (min (B * min (T * Real.log T) (T ^ q * (Real.log T) ^ (2 + q)))
            (C * T ^ (guthMaynardExponent σ + ε))) := by
  obtain ⟨B, hB, hi⟩ := exists_ingham_guthMaynard_count hG
  refine ⟨B, hB, ?_⟩
  intro σ hσ ε hε
  obtain ⟨C, hC, hc⟩ := hi σ hσ ε hε
  obtain ⟨D, hD, hd⟩ := fixed_lewko_density hL hσ hε
  refine ⟨C, D, hC, hD, ?_⟩
  filter_upwards [hc, eventually_ge_atTop (2 : ℝ)] with T hT hT₂
  exact le_min (hd T hT₂) hT

end RiemannResearch.Analysis.ActualZeroOrdinate
