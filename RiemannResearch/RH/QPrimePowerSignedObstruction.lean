/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerSignedSieve
import RiemannResearch.RH.QPrimePowerSieveUniform
import RiemannResearch.RH.PrimePowerTargetMellinLower
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Arbitrary finite signed sieve obstruction

Source: user-provided QParityHeadContinuationResearch20261020.md, Section 5,
for the proposed multi-stage deduction. Exact Mellin drift is retained before
cancellation. Uniform Euler decay and the existing complete-Q head-tail bound
discharge the arithmetic hypotheses. No RH or closure hypothesis is used.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability QMellinTransfer PrimePowerTarget

theorem signedSieveVector_mellin_exact (p : ℕ) (hp : p.Prime)
    (S : Finset ℕ) (w : ℕ → ℝ) (hcut : ∀ H ∈ S, p ≤ H)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ ≠ 1) :
    (σ : ℂ) * qMellin (signedSieveVector p S w) σ =
      riemannZeta σ * ((∑ H ∈ S,
        w H * (primePowerEulerFactor p H σ - sieveSlope (primorial H) p) : ℝ) : ℂ) := by
  have hm : qMellin (signedSieveVector p S w) σ =
      ∑ H ∈ S, (w H : ℂ) * qMellin (sieveVector (primorial H) p) σ := by
    change qMellinContinuous σ (by simpa using hσ) (∑ H ∈ S, w H • _) = _
    simp only [map_sum, map_smul, qMellinContinuous_apply, Complex.real_smul]
  rw [hm, Finset.mul_sum]
  calc
    _ = ∑ H ∈ S, (w H : ℂ) * ((σ : ℂ) *
        qMellin (sieveVector (primorial H) p) σ) := by
      apply Finset.sum_congr rfl
      intro H hH
      ring
    _ = _ := by
      simp_rw [Complex.ofReal_sum, Complex.ofReal_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro H hH
      rw [sieveVector_primorial_mellin_exact p H hp (hcut H hH) σ hσ hσ1]
      ring

theorem signedSieveVector_balanced_mellin_exact (p : ℕ) (hp : p.Prime)
    (S : Finset ℕ) (w : ℕ → ℝ) (hcut : ∀ H ∈ S, p ≤ H)
    (hdrift : ∑ H ∈ S, w H * sieveSlope (primorial H) p = 0)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ ≠ 1) :
    (σ : ℂ) * qMellin (signedSieveVector p S w) σ =
      riemannZeta σ * ((∑ H ∈ S, w H * primePowerEulerFactor p H σ : ℝ) : ℂ) := by
  rw [signedSieveVector_mellin_exact p hp S w hcut σ hσ hσ1]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hdrift, sub_zero]

theorem signedSieveVector_mellin_bound (p : ℕ) (hp : p.Prime)
    (S : Finset ℕ) (w : ℕ → ℝ) (hcut : ∀ H ∈ S, p ≤ H)
    (hdrift : ∑ H ∈ S, w H * sieveSlope (primorial H) p = 0)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ ≠ 1)
    (δ : ℝ) (hEuler : ∀ H ∈ S, |primePowerEulerFactor p H σ| ≤ δ) :
    ‖(σ : ℂ) * qMellin (signedSieveVector p S w) σ‖ ≤
      ‖riemannZeta σ‖ * ((∑ H ∈ S, |w H|) * δ) := by
  rw [signedSieveVector_balanced_mellin_exact p hp S w hcut hdrift σ hσ hσ1,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    |∑ H ∈ S, w H * primePowerEulerFactor p H σ| ≤
        ∑ H ∈ S, |w H * primePowerEulerFactor p H σ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ H ∈ S, |w H| * δ := by
      apply Finset.sum_le_sum
      intro H hH
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hEuler H hH) (abs_nonneg _)
    _ = _ := (Finset.sum_mul S (fun H => |w H|) δ).symm

theorem primePowerEulerFactor_uniform_decay (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    ∀ ε > 0, ∃ N : ℕ, p ≤ N ∧ ∀ H ≥ N, |primePowerEulerFactor p H σ| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (primePowerEulerFactor_scaled_tendsto_zero p hp σ hσ hσ1) ε hε
  refine ⟨max p (max N 1), le_max_left _ _, ?_⟩
  intro H hH
  have hHN : N ≤ H := (le_max_left N 1).trans ((le_max_right p (max N 1)).trans hH)
  have hH1 : 1 ≤ H := (le_max_right N 1).trans ((le_max_right p (max N 1)).trans hH)
  have hpow : 1 ≤ (H : ℝ) ^ (1 - σ) :=
    Real.one_le_rpow (by exact_mod_cast hH1) (by linarith)
  have he := primePowerEulerFactor_pos p H hp.pos σ hσ
  have hb := hN H hHN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hb
  rw [abs_of_pos he]
  nlinarith

theorem signedSieveVector_mellin_uniform (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε > 0, ∃ N : ℕ, p ≤ N ∧
      ∀ (S : Finset ℕ) (w : ℕ → ℝ),
      (∀ H ∈ S, N ≤ H) →
      (∑ H ∈ S, w H * sieveSlope (primorial H) p = 0) →
      (∑ H ∈ S, |w H| ≤ M) →
      ‖(σ : ℂ) * qMellin (signedSieveVector p S w) σ‖ < ε := by
  intro ε hε
  let δ := ε / ((‖riemannZeta (σ : ℂ)‖ + 1) * (M + 1))
  have hz := norm_nonneg (riemannZeta (σ : ℂ))
  have hd : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hpN, hN⟩ := primePowerEulerFactor_uniform_decay p hp σ (by linarith) hσ1 δ hd
  refine ⟨N, hpN, ?_⟩
  intro S w hcut hdrift hvar
  have hb := signedSieveVector_mellin_bound p hp S w
    (fun H hH => hpN.trans (hcut H hH)) hdrift σ hσ (ne_of_lt hσ1)
    δ (fun H hH => (hN H (hcut H hH)).le)
  have hv := mul_le_mul_of_nonneg_right hvar hd.le
  have hh := mul_le_mul_of_nonneg_left hv hz
  have he : δ * ((‖riemannZeta (σ : ℂ)‖ + 1) * (M + 1)) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  nlinarith

theorem signedSieveVector_quantitative_lower (p : ℕ) (hp : p.Prime)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ N : ℕ, p ≤ N ∧ ∀ H ≥ N, ∀ (S : Finset ℕ) (w : ℕ → ℝ),
      (∀ K ∈ S, H ≤ K) →
      (∑ K ∈ S, w K = 1) →
      (∑ K ∈ S, w K * sieveSlope (primorial K) p = 0) →
      (∑ K ∈ S, |w K| ≤ M) →
      ((2 * σ - 1) / (4 * zetaTwo * σ ^ 2 * ((p : ℝ) ^ σ - 1) ^ 2)) *
        (H : ℝ) ^ (2 * σ - 1) ≤ ‖signedSieveVector p S w - qTarget p hp.one_lt‖ ^ 2 := by
  have hden : 0 < (p : ℝ) ^ σ - 1 := sub_pos.mpr
    (Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith))
  obtain ⟨N, hpN, hN⟩ := signedSieveVector_mellin_uniform p hp σ hσ hσ1 M hM
    (1 / (2 * ((p : ℝ) ^ σ - 1))) (by positivity)
  refine ⟨N, hpN, ?_⟩
  intro H hH S w hcut hmass hdrift hvar
  apply qTarget_head_match_quantitative_lower p hp.one_lt (signedSieveVector p S w)
    σ hσ H (by have := hp.two_le; omega)
  · intro n hn
    exact signedSieveVector_head_of_balanced p hp S w H n
      (fun K hK => max_le ((hpN.trans hH).trans (hcut K hK)) (hcut K hK))
      hn hmass hdrift
  · exact (hN S w (fun K hK => hH.trans (hcut K hK)) hdrift hvar).le

/-- A common positive head-error lower bound forces complete norm divergence. -/
theorem norm_tendsto_atTop_of_head_lower
    (p : ℕ) (hp : 1 < p) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ)
    (H : ℕ → ℕ) (v : ℕ → QHilbert) (hH : Tendsto H atTop atTop)
    (hbound : ∀ᶠ j in atTop,
      ((2 * σ - 1) / (4 * zetaTwo * σ ^ 2 * ((p : ℝ) ^ σ - 1) ^ 2)) *
        (H j : ℝ) ^ (2 * σ - 1) ≤ ‖v j - qTarget p hp‖ ^ 2) :
    Tendsto (fun j => ‖v j‖) atTop atTop := by
  let c : ℝ := (2 * σ - 1) /
    (4 * zetaTwo * σ ^ 2 * ((p : ℝ) ^ σ - 1) ^ 2)
  have hc : 0 < c := qTarget_obstruction_constant_pos p hp σ hσ
  have hpower : Tendsto (fun j : ℕ => (H j : ℝ) ^ (2 * σ - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 2 * σ - 1)).comp
      (tendsto_natCast_atTop_atTop.comp hH)
  apply tendsto_atTop.2
  intro b
  let B : ℝ := max b 0 + ‖qTarget p hp‖
  have hB : 0 ≤ B := add_nonneg (le_max_right b 0) (norm_nonneg _)
  filter_upwards [hbound,
    hpower.eventually (eventually_ge_atTop (B ^ 2 / c))] with j hj hpow
  have hscaled : B ^ 2 ≤ c * (H j : ℝ) ^ (2 * σ - 1) := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hpow
  have herr : B ≤ ‖v j - qTarget p hp‖ := by
    have he0 := norm_nonneg (v j - qTarget p hp)
    change c * (H j : ℝ) ^ (2 * σ - 1) ≤ _ at hj
    have hsq := hscaled.trans hj
    nlinarith
  have htri := norm_sub_le (v j) (qTarget p hp)
  have hb := le_max_left b 0
  dsimp only [B] at herr
  linarith

/-- Arbitrary row length is allowed, including lengths tending to infinity. -/
theorem signedSieveVector_norm_tendsto_atTop
    (p : ℕ) (hp : p.Prime) (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) (hσ1 : σ < 1)
    (H : ℕ → ℕ) (S : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hH : Tendsto H atTop atTop)
    (hcut : ∀ᶠ j in atTop, ∀ K ∈ S j, H j ≤ K)
    (hmass : ∀ᶠ j in atTop, ∑ K ∈ S j, w j K = 1)
    (hdrift : ∀ᶠ j in atTop, ∑ K ∈ S j, w j K * sieveSlope (primorial K) p = 0)
    (hvar : ∀ᶠ j in atTop, ∑ K ∈ S j, |w j K| ≤ M) :
    Tendsto (fun j => ‖signedSieveVector p (S j) (w j)‖) atTop atTop := by
  obtain ⟨N, _, hN⟩ := signedSieveVector_quantitative_lower p hp σ hσ hσ1 M hM
  apply norm_tendsto_atTop_of_head_lower p hp.one_lt σ hσ H
    (fun j => signedSieveVector p (S j) (w j)) hH
  filter_upwards [hH.eventually (eventually_ge_atTop N), hcut, hmass, hdrift, hvar]
    with j hj hcutj hmassj hdriftj hvarj
  exact hN (H j) hj (S j) (w j) hcutj hmassj hdriftj hvarj

end RiemannResearch.RH.QPrimePowerSieve
