/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualHyperbolicHarmonicTail
import RiemannResearch.Analysis.ActualLewkoDensity

/-!
# Count-only bounds for the signed bad correction

Subtract the masked phase Gram from the signed hyperbolic Gram after
centering both operators at the same scalar. The existing finite harmonic
cap then bounds both actual operator norms by that cap times the unweighted
strict tail fraction. Combining the multiplicity-aware count with the
Riemann–von Mangoldt lower bound improves the admissible dimension powers.
-/

noncomputable section
open Filter Complex Set Zeta23
open scoped BigOperators InnerProductSpace

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate HorizontalEuclideanMoments HorizontalPhaseBootstrap
open ZeroOrdinate ContinuousLinearMap FiniteHyperbolicHarmonicCap

/-- The phase Gram restricted to the strict bad copies, with the original
full-cutoff normalizer. -/
def badPhaseGram (T : ℝ) (d : ℕ) (δ : ℝ) : Space d →L[ℂ] Space d :=
  (Ncount 0 T : ℝ)⁻¹ • ∑ c : Copies T, badRealWeight δ c.1.1 •
    InnerProductSpace.rankOne ℂ (copyPhaseVector d c.1.1) (copyPhaseVector d c.1.1)

theorem badCorrection_eq_signed_sub_phase (T : ℝ) (d : ℕ) (δ : ℝ) :
    badCorrection T d δ = signedBadHyperbolic T d δ - badPhaseGram T d δ := by
  apply euclideanEntry_ext
  intro n m
  rw [badCorrection_eq_copy_sum, euclideanEntry_sub, signedBadHyperbolic_entry, badPhaseGram,
    euclideanEntry_real_smul, euclideanEntry_real_smul, sum_eq_copies]
  simp only [← euclideanEntryCLM_apply, map_sum]
  simp only [euclideanEntryCLM_apply, euclideanEntry_real_smul, euclideanEntry_rankOne,
    copyPhaseVector_kernel, copyCoshCorrection_entry, badRealWeight_coe]
  push_cast
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem badPhaseGram_center_norm_le (T : ℝ) (d : ℕ) (δ : ℝ) :
    ‖badPhaseGram T d δ - (((strictTail T δ / (Ncount 0 T : ℝ)) * (d : ℝ)) / 2) •
      (1 : Space d →L[ℂ] Space d)‖ ≤ (strictTail T δ / (Ncount 0 T : ℝ)) * (d : ℝ) / 2 := by
  let w := fun c : Copies T => badRealWeight δ c.1.1
  let P := fun c : Copies T =>
    InnerProductSpace.rankOne ℂ (copyPhaseVector d c.1.1) (copyPhaseVector d c.1.1)
  let κ := (Ncount 0 T : ℝ)⁻¹
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hw := badRealWeight_copy_sum T δ
  have hs : (∑ c : Copies T, (w c * (d : ℝ) / 2)) = strictTail T δ * (d : ℝ) / 2 := by
    rw [← Finset.sum_div, ← Finset.sum_mul, hw]
  have hcenter :
      badPhaseGram T d δ - (((strictTail T δ / (Ncount 0 T : ℝ)) * (d : ℝ)) / 2) •
        (1 : Space d →L[ℂ] Space d) =
      κ • ∑ c : Copies T, (w c • P c - (w c * (d : ℝ) / 2) • (1 : Space d →L[ℂ] Space d)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hs, smul_sub, smul_smul]
    unfold badPhaseGram
    congr 2
    dsimp [κ]
    ring
  rw [hcenter, norm_smul, Real.norm_eq_abs, abs_of_nonneg hκ]
  calc
    _ ≤ κ * ∑ c : Copies T, ‖w c • P c - (w c * (d : ℝ) / 2) • (1 : Space d →L[ℂ] Space d)‖ :=
      mul_le_mul_of_nonneg_left (_root_.norm_sum_le _ _) hκ
    _ ≤ κ * ∑ c : Copies T, (w c * (d : ℝ) / 2) := by
      apply mul_le_mul_of_nonneg_left _ hκ
      apply Finset.sum_le_sum
      intro c _
      simpa only [copyRankOne_norm] using rankOne_real_smul_center_norm_le
        (copyPhaseVector d c.1.1) (w c) (badRealWeight_nonneg _ _)
    _ = _ := by rw [hs]; dsimp [κ]; ring

/-- The count-only harmonic budget holds for the complete signed correction.
Both centering shifts are exactly the same, including at empty cutoffs. -/
theorem badCorrection_norm_le_harmonic (T : ℝ) (d : ℕ) (δ : ℝ) :
    ‖badCorrection T d δ‖ ≤ strictTail T δ / (Ncount 0 T : ℝ) * harmonicHyperbolicCap d := by
  let r := strictTail T δ / (Ncount 0 T : ℝ)
  let A := ((r * (d : ℝ)) / 2) • (1 : Space d →L[ℂ] Space d)
  have hh := signedBadHyperbolic_center_norm_le_harmonic T d δ
  have hp := badPhaseGram_center_norm_le T d δ
  rw [badCorrection_eq_signed_sub_phase, show signedBadHyperbolic T d δ - badPhaseGram T d δ =
    (signedBadHyperbolic T d δ - A) - (badPhaseGram T d δ - A) by abel]
  exact (norm_sub_le _ _).trans (by linarith only [hh, hp])

/-- Powered dimensions consume only the unweighted zero-count exponent.
This counts every actual zero copy and retains both signed operators. -/
theorem exceptional_norms_of_fixed_density {δ q b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hD : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, rightInclusiveCount T (1/2 + δ) ≤ C * T ^ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ T ^ b →
      max ‖badCorrection T d δ‖ ‖signedBadHyperbolic T d δ‖ ≤ C * T ^ (b + q - 1) := by
  obtain ⟨C, hC, hct⟩ := hD
  let k : ℝ := 1 / (16 * Real.pi)
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨2*C*(1+b)/k, by positivity, ?_⟩
  filter_upwards [hct, eventually_count_ge_log, eventually_gt_atTop (Real.exp 1)] with T hct' hN hT
  intro d hd hdT
  have hTp := (Real.exp_pos _).trans hT
  have hL : 1 < Real.log T := by simpa using Real.log_lt_log (Real.exp_pos _) hT
  have hLp := zero_lt_one.trans hL
  have hdR : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog := Real.log_le_log (zero_lt_one.trans_le hdR) hdT
  rw [Real.rpow_def_of_pos hTp, Real.log_exp] at hlog
  have hcap : harmonicHyperbolicCap d ≤ T ^ b * ((1+b) * Real.log T) := by
    apply (harmonicHyperbolicCap_le_card_log d hd).trans
    exact mul_le_mul hdT (by linarith only [hlog, hL]) (by linarith [Real.log_nonneg hdR])
      (Real.rpow_nonneg hTp.le _)
  have hfrac : strictTail T δ / (Ncount 0 T : ℝ) ≤ 2*C*T^q/(k*T*Real.log T) := by
    have hn := (show 0 < k*T*Real.log T by positivity).trans_le hN
    exact div_le_div₀ (show 0 ≤ 2*C*T^q by positivity)
      ((strictTail_le_twice_inclusive T δ hδ).trans (by linarith only [hct']))
      (by positivity) hN
  apply (max_le (badCorrection_norm_le_harmonic T d δ) (signedBadHyperbolic_norm_le_harmonic T d δ)).trans
  calc
    _ ≤ (2*C*T^q/(k*T*Real.log T)) * (T^b*((1+b)*Real.log T)) :=
      mul_le_mul hfrac hcap (harmonicHyperbolicCap_nonneg d) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub hTp, Real.rpow_add hTp, Real.rpow_one]
      field_simp [hTp.ne', hk.ne', hLp.ne']

/-- Guth–Maynard at the exact quarter yields all dimension powers b < 4/9. -/
theorem exceptional_quarter_harmonic_power (hG : GuthMaynardDensityHypothesis)
    {b η : ℝ} (hb : 0 ≤ b) (hη : η < 4 / 9 - b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ T ^ b →
      max ‖badCorrection T d (1/4)‖ ‖signedBadHyperbolic T d (1/4)‖ ≤ C * T ^ (-η) := by
  let ε := 4/9 - b - η
  have hε : 0 < ε := sub_pos.mpr hη
  have hc := hG (3/4) ⟨by norm_num, by norm_num⟩ ε hε
  rw [guthMaynard_gain_three_quarters.1] at hc
  have h := exceptional_norms_of_fixed_density (δ := 1/4) (q := 5/9 + ε) (by norm_num) hb (by
    simpa only [show (1/2 + 1/4 : ℝ) = 3/4 by norm_num] using hc)
  simpa only [show b + (5/9 + ε) - 1 = -η by dsimp [ε]; ring] using h

/-- The sharper right-hand density branch improves the dimension power on
every fixed strip strictly beyond three quarters. At σ = 4/5 the threshold
is 5/8. -/
theorem exceptional_fixed_strip_harmonic_power (hLw : LewkoDensityHypothesis)
    {σ b η : ℝ} (hσ : σ ∈ Ioc (3/4 : ℝ) 1) (hb : 0 ≤ b)
    (hη : η < 1 - 3/(2*σ)*(1-σ) - b) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ T ^ b →
      max ‖badCorrection T d (σ - 1/2)‖ ‖signedBadHyperbolic T d (σ - 1/2)‖ ≤ C * T ^ (-η) := by
  let q := 3/(2*σ)*(1-σ)
  let ε := 1 - q - b - η
  have hε : 0 < ε := sub_pos.mpr hη
  have hc := fixed_lewko_density hLw ⟨by linarith only [hσ.1], hσ.2⟩ hε
  have hcoef : lewkoDensityCoefficient σ = 3/(2*σ) := by
    simp [lewkoDensityCoefficient, not_le.mpr hσ.1,
      show ¬ σ ≤ 9/13 by linarith only [hσ.1], show ¬ σ ≤ 5/7 by linarith only [hσ.1]]
  rw [hcoef] at hc
  obtain ⟨C, hC, hc⟩ := hc
  have h := exceptional_norms_of_fixed_density (δ := σ - 1/2) (q := q + ε)
    (by linarith only [hσ.1]) hb (by
      refine ⟨C, hC, ?_⟩
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with T hT
      simpa only [show 1 / 2 + (σ - 1 / 2) = σ by ring] using hc T hT)
  simpa only [show b + (q + ε) - 1 = -η by dsimp [ε]; ring] using h

end RiemannResearch.Analysis.ActualZeroPhaseMoments
