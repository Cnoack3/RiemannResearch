/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualUniformRationalLandau
import RiemannResearch.Analysis.ActualZeroPhaseOperators
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.PrimePowerCovarianceConjugation
import RiemannResearch.Analysis.LandauGrowingSupport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual signed Landau operator residual and growing-support convergence

The actual rational Landau provider is assembled in the Euclidean operator
norm on the same Fin d space as the phase Gram. The negative prime-power
main term retains every integer and composite-frequency interaction.
The exact diagonal, reflection symmetry, original Ncount and full signed
residual are explicit. Square-root-log support gives residual norm tending
to zero for every fixed coefficient c. No density, simplicity or RH premise
is used for this residual result. The main arithmetic operator is retained;
this result alone does not assert a frame gap or physical Pareto saturation.
Source for the analytic contour strategy: Gonek (1985), Theorem 1,
https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf .
The sufficient fixed-c=2 provider and exact operator assembly are repository
proofs; the sharper published Landau--Gonek error is not imported.
-/

noncomputable section
open Complex Zeta23
open scoped BigOperators InnerProductSpace Matrix

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate RiemannResearch.Fourier

@[simp] theorem landauSum_zero (T : ℝ) : landauSum T 0 = (Ncount 0 T : ℂ) := by
  simp [landauSum]

/-- Reflection pairing makes the centered Landau sum Hermitian in frequency. -/
theorem landauSum_neg (T u : ℝ) : landauSum T (-u) = star (landauSum T u) := by
  rw [landauSum_eq_cosh, landauSum_eq_cosh]
  simp [sum, phase_neg, Real.cosh_neg, -Complex.ofReal_cosh]

/-- Exact identification of the scalar resonance with the full integer kernel.
    The pair n,m may themselves be composite. -/
theorem two_pi_mul_rationalLandauMain_eq_covariance {n m : ℕ}
    (hm : 1 ≤ m) (hmn : m < n) :
    (2 * Real.pi) * rationalLandauMain n m =
      primePowerCovarianceSymmetricEntry n m := by
  have hm0 : 0 < m := by omega
  have hn0 : 0 < n := by omega
  rw [rationalLandauMain_eq_vonMangoldt_div_sqrt hm hmn,
    primePowerCovarianceSymmetricEntry_symm n m hn0 hm0]
  by_cases hd : m ∣ n
  · rw [if_pos hd,
      primePowerCovarianceSymmetricEntry_eq_of_lt_of_dvd m n hm0 hmn hd]
    have hmp : (0 : ℝ) < m := by exact_mod_cast hm0
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn0
    have hq : ((n / m : ℕ) : ℝ) = (n : ℝ) / (m : ℝ) := by
      apply (eq_div_iff hmp.ne').mpr
      exact_mod_cast Nat.div_mul_cancel hd
    rw [hq]
    have hs : Real.sqrt ((n : ℝ) / (m : ℝ)) ≠ 0 :=
      (Real.sqrt_pos.mpr (div_pos hnp hmp)).ne'
    field_simp [Real.pi_ne_zero, hs]
  · have hnd : ¬ n ∣ m := by
      intro h
      have hh := Nat.le_of_dvd hm0 h
      omega
    rw [if_neg hd, mul_zero,
      primePowerCovarianceSymmetricEntry_eq_zero_of_nondvd m n hd hnd]

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate HorizontalEuclideanMoments ContinuousLinearMap
open RiemannResearch.Fourier

/-- The complete integer covariance, realized on the same Fin d space as landauGram.
    This avoids silently using the differently indexed Ioc operator. -/
def finPrimePowerMainOperator (d : ℕ) : Space d →L[ℂ] Space d :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (fun n m =>
    (primePowerCovarianceSymmetricEntry (n.val + 1) (m.val + 1) : ℂ))

@[simp] theorem finPrimePowerMainOperator_entry (d : ℕ) (n m : Fin d) :
    euclideanEntry (finPrimePowerMainOperator d) n m =
      (primePowerCovarianceSymmetricEntry (n.val + 1) (m.val + 1) : ℂ) :=
  euclideanEntry_toEuclideanCLM _ _ _

def actualLandauResidual (T : ℝ) (d : ℕ) : Space d →L[ℂ] Space d :=
  landauGram T d - 1 +
    (T / ((2 * Real.pi) * (Ncount 0 T : ℝ))) • finPrimePowerMainOperator d

theorem frequencyGap_eq_log_ratio {d : ℕ} (n m : Fin d) :
    frequencyGap n m = Real.log (((n.val + 1 : ℕ) : ℝ) /
      ((m.val + 1 : ℕ) : ℝ)) := by
  rw [Real.log_div (by positivity) (by positivity)]
  rfl

theorem actualLandauResidual_entry_of_lt (T : ℝ) (d : ℕ)
    (hN : 0 < Ncount 0 T) (n m : Fin d) (hmn : m.val < n.val) :
    euclideanEntry (actualLandauResidual T d) n m =
      (Ncount 0 T : ℂ)⁻¹ *
        (landauSum T (Real.log (((n.val + 1 : ℕ) : ℝ) /
          ((m.val + 1 : ℕ) : ℝ))) +
        ((T * rationalLandauMain (n.val + 1) (m.val + 1) : ℝ) : ℂ)) := by
  have hne : n ≠ m := by intro h; subst n; omega
  have hnR : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hnC : (Ncount 0 T : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcov := two_pi_mul_rationalLandauMain_eq_covariance
    (n := n.val + 1) (m := m.val + 1) (by omega) (by omega)
  unfold actualLandauResidual
  rw [euclideanEntry_add, euclideanEntry_sub, landauGram_entry,
    euclideanEntry_one, if_neg hne, sub_zero, euclideanEntry_real_smul,
    finPrimePowerMainOperator_entry, ← hcov, frequencyGap_eq_log_ratio]
  push_cast
  field_simp [hnR, hnC, Real.pi_ne_zero]

theorem actualLandauResidual_entry_diag (T : ℝ) (d : ℕ)
    (hN : 0 < Ncount 0 T) (n : Fin d) :
    euclideanEntry (actualLandauResidual T d) n n = 0 := by
  have hnC : (Ncount 0 T : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [actualLandauResidual, frequencyGap, landauSum_zero,
    primePowerCovarianceSymmetricEntry_diag (n.val + 1) (by omega), hnC]

theorem actualLandauResidual_entry_star (T : ℝ) (d : ℕ) (n m : Fin d) :
    euclideanEntry (actualLandauResidual T d) n m =
      star (euclideanEntry (actualLandauResidual T d) m n) := by
  have hgap : frequencyGap n m = -frequencyGap m n := by
    unfold frequencyGap
    ring
  have hcov := primePowerCovarianceSymmetricEntry_symm
    (n.val + 1) (m.val + 1) (by omega) (by omega)
  unfold actualLandauResidual
  rw [euclideanEntry_add, euclideanEntry_sub, landauGram_entry,
    euclideanEntry_one, euclideanEntry_real_smul, finPrimePowerMainOperator_entry,
    euclideanEntry_add, euclideanEntry_sub, landauGram_entry,
    euclideanEntry_one, euclideanEntry_real_smul, finPrimePowerMainOperator_entry,
    hgap, landauSum_neg, hcov]
  by_cases hnm : n = m
  · subst n
    simp
  · simp [hnm, Ne.symm hnm]

def landauScalarEnvelope (T : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) ^ (5 / 2 : ℝ) +
    (d : ℝ) ^ (3 / 2 : ℝ) * (Real.log (T + 3)) ^ 2 +
    (d : ℝ) * Real.log (T + 3)

/-- Genuine Euclidean operator residual assembly from the checked actual scalar provider.
    The arithmetic main sign, all composite pairs and the original Ncount remain. -/
theorem exists_actualLandauResidual_norm_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (d : ℕ),
      9 ≤ T → 0 < Ncount 0 T →
      ‖actualLandauResidual T d‖ ≤
        (d : ℝ) * C * landauScalarEnvelope T d / (Ncount 0 T : ℝ) := by
  obtain ⟨C, hC, hscalar⟩ := exists_uniform_rational_landau_rpow_bound
  refine ⟨C, hC, ?_⟩
  intro T d hT hN
  have hNr : (0 : ℝ) < Ncount 0 T := by exact_mod_cast hN
  have hL : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
  have henv : 0 ≤ landauScalarEnvelope T d := by
    unfold landauScalarEnvelope
    positivity
  have hupper (n m : Fin d) (hmn : m.val < n.val) :
      ‖euclideanEntry (actualLandauResidual T d) n m‖ ≤
        C * landauScalarEnvelope T d / (Ncount 0 T : ℝ) := by
    have hb := hscalar T (d : ℝ) (n.val + 1) (m.val + 1)
      hT (by omega) (by omega) (by exact_mod_cast Nat.succ_le_of_lt n.isLt)
    rw [actualLandauResidual_entry_of_lt T d hN n m hmn,
      norm_mul, norm_inv, Complex.norm_natCast]
    calc
      _ ≤ (Ncount 0 T : ℝ)⁻¹ * (C * landauScalarEnvelope T d) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  have hentry (n m : Fin d) :
      ‖euclideanEntry (actualLandauResidual T d) n m‖ ≤
        C * landauScalarEnvelope T d / (Ncount 0 T : ℝ) := by
    rcases lt_trichotomy m.val n.val with hmn | heq | hnm
    · exact hupper n m hmn
    · have h : n = m := Fin.ext heq.symm
      subst n
      rw [actualLandauResidual_entry_diag T d hN, norm_zero]
      positivity
    · rw [actualLandauResidual_entry_star T d n m, norm_star]
      exact hupper m n hnm
  have hb := norm_le_card_mul_of_euclideanEntry_le (actualLandauResidual T d)
    (C * landauScalarEnvelope T d / (Ncount 0 T : ℝ)) (by positivity) hentry
  simpa only [mul_div_assoc, mul_assoc] using hb

end RiemannResearch.Analysis.ActualZeroPhaseMoments

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open Filter Zeta23

/-- The original actual zero count eventually dominates height itself. -/
theorem eventually_count_ge_height_add_three :
    ∀ᶠ T : ℝ in atTop, T + 3 ≤ (Ncount 0 T : ℝ) := by
  filter_upwards [eventually_count_ge_log, eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (32 * Real.pi)] with T hN hT hL
  have hscaled : 2 ≤ (1 / (16 * Real.pi)) * Real.log T := by
    calc
      2 = (1 / (16 * Real.pi)) * (32 * Real.pi) := by field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hscaled (by linarith : 0 ≤ T)
  nlinarith only [hN, hT, hmul]

end RiemannResearch.Analysis.ActualZeroOrdinate

namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open Filter Zeta23 ActualZeroOrdinate LandauGrowth

/-- The full signed Landau residual vanishes for every fixed square-root-log
support coefficient. This theorem has no density or RH premise. It keeps the
exact prime-power main operator inside actualLandauResidual. -/
theorem actualLandauResidual_norm_tendsto_zero_sqrt_support
    (d : ℝ → ℕ) (c : ℝ)
    (hsupport : ∀ᶠ T : ℝ in atTop,
      1 ≤ d T ∧ Real.log (d T : ℝ) ≤ c * Real.sqrt (Real.log (T + 3))) :
    Tendsto (fun T : ℝ => ‖actualLandauResidual T (d T)‖) atTop (nhds 0) := by
  obtain ⟨C, hC, hbound⟩ := exists_actualLandauResidual_norm_bound
  have hplus : Tendsto (fun T : ℝ => T + 3) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with T hT
    linarith
  have hlog := Real.tendsto_log_atTop.comp hplus
  have hmajor : Tendsto (fun T : ℝ =>
      C * matrixEnvelope (Real.log (T + 3)) (c * Real.sqrt (Real.log (T + 3))))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((matrixEnvelope_sqrt_tendsto_zero c).const_mul C).comp hlog
  apply squeeze_zero'
  · exact Eventually.of_forall (fun T => norm_nonneg _)
  · filter_upwards [eventually_count_ge_height_add_three,
      eventually_ge_atTop (9 : ℝ), hsupport] with T hNheight hT hs
    have hY : 0 < T + 3 := by linarith
    have hNr : (0 : ℝ) < (Ncount 0 T : ℝ) := lt_of_lt_of_le hY hNheight
    have hN : 0 < Ncount 0 T := by exact_mod_cast hNr
    have hd : (0 : ℝ) < (d T : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs.1)
    have hL : 0 ≤ Real.log (T + 3) := Real.log_nonneg (by linarith)
    have henv : 0 ≤ landauScalarEnvelope T (d T) := by
      unfold landauScalarEnvelope
      positivity
    calc
      _ ≤ (d T : ℝ) * C * landauScalarEnvelope T (d T) /
          (Ncount 0 T : ℝ) := hbound T (d T) hT hN
      _ ≤ (d T : ℝ) * C * landauScalarEnvelope T (d T) / (T + 3) :=
        div_le_div_of_nonneg_left (by positivity) hY hNheight
      _ = C * matrixEnvelope (Real.log (T + 3)) (Real.log (d T : ℝ)) := by
        rw [matrixEnvelope_eq_rpow hY hd]
        unfold landauScalarEnvelope
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (matrixEnvelope_mono hL hs.2) hC.le
  · exact hmajor

end RiemannResearch.Analysis.ActualZeroPhaseMoments
