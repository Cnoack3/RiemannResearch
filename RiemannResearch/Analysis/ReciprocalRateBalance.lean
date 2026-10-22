import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Exact scalar balancing for the quantitative reciprocal-polynomial estimate.
This module contains no zeta-zero sampling hypothesis: it verifies the optimizer
exponents and positive-base power identities used after the analytic estimates.
The optimized cutoff is real-valued; its integer floor is handled separately.
-/

open Filter Real

namespace RiemannResearch.Analysis.ReciprocalRateBalance

noncomputable def cutoffPower (σ : ℝ) : ℝ := 2 / (3 - 2 * σ)

noncomputable def cutoffLogPower (σ : ℝ) : ℝ := 3 / (3 - 2 * σ)

noncomputable def reciprocalPower (σ : ℝ) : ℝ := (2 * σ - 1) / (3 - 2 * σ)

noncomputable def reciprocalLogPower (σ : ℝ) : ℝ := 6 * (1 - σ) / (3 - 2 * σ)

noncomputable def optimizedCutoff (σ L : ℝ) : ℝ :=
  L ^ cutoffPower σ * (Real.log L) ^ cutoffLogPower σ

noncomputable def logPowerEnvelope (a b L : ℝ) : ℝ :=
  L ^ (-a) * (Real.log L) ^ b

noncomputable def reciprocalRate (σ L : ℝ) : ℝ :=
  logPowerEnvelope (reciprocalPower σ) (reciprocalLogPower σ) L

theorem denominator_gt_one {σ : ℝ} (hσ : σ < 1) : 1 < 3 - 2 * σ := by
  linarith

theorem denominator_pos {σ : ℝ} (hσ : σ < 1) : 0 < 3 - 2 * σ := by
  linarith [denominator_gt_one hσ]

theorem cutoffPower_pos {σ : ℝ} (hσ : σ < 1) : 0 < cutoffPower σ := by
  exact div_pos (by norm_num) (denominator_pos hσ)

theorem cutoffPower_lt_two {σ : ℝ} (hσ : σ < 1) : cutoffPower σ < 2 := by
  unfold cutoffPower
  rw [div_lt_iff₀ (denominator_pos hσ)]
  linarith

theorem cutoffLogPower_pos {σ : ℝ} (hσ : σ < 1) : 0 < cutoffLogPower σ := by
  exact div_pos (by norm_num) (denominator_pos hσ)

theorem reciprocalPower_pos {σ : ℝ} (hhalf : (1 : ℝ) / 2 < σ) (hσ : σ < 1) :
    0 < reciprocalPower σ := by
  exact div_pos (by linarith) (denominator_pos hσ)

theorem reciprocalLogPower_pos {σ : ℝ} (hσ : σ < 1) :
    0 < reciprocalLogPower σ := by
  exact div_pos (by linarith) (denominator_pos hσ)

theorem reciprocalPower_lt_tailPower {σ : ℝ}
    (hhalf : (1 : ℝ) / 2 < σ) (hσ : σ < 1) :
    reciprocalPower σ < 2 * σ - 1 := by
  unfold reciprocalPower
  rw [div_lt_iff₀ (denominator_pos hσ)]
  have hprod : 0 < (2 * σ - 1) * ((3 - 2 * σ) - 1) :=
    mul_pos (by linarith) (by linarith [denominator_gt_one hσ])
  nlinarith

theorem cutoff_diagonal_exponent {σ : ℝ} (hσ : σ < 1) :
    cutoffPower σ * ((1 : ℝ) / 2 - σ) = -reciprocalPower σ := by
  have hD : 3 - 2 * σ ≠ 0 := ne_of_gt (denominator_pos hσ)
  unfold cutoffPower reciprocalPower
  field_simp [hD]
  ring

theorem cutoff_covariance_exponent {σ : ℝ} (hσ : σ < 1) :
    cutoffPower σ * (2 - 2 * σ) - 1 = -reciprocalPower σ := by
  have hD : 3 - 2 * σ ≠ 0 := ne_of_gt (denominator_pos hσ)
  unfold cutoffPower reciprocalPower
  field_simp [hD]
  ring

theorem log_diagonal_exponent {σ : ℝ} (hσ : σ < 1) :
    cutoffLogPower σ * ((1 : ℝ) / 2 - σ) + (3 : ℝ) / 2 =
      reciprocalLogPower σ := by
  have hD : 3 - 2 * σ ≠ 0 := ne_of_gt (denominator_pos hσ)
  unfold cutoffLogPower reciprocalLogPower
  field_simp [hD]
  ring

theorem log_covariance_exponent {σ : ℝ} (hσ : σ < 1) :
    cutoffLogPower σ * (2 - 2 * σ) = reciprocalLogPower σ := by
  have hD : 3 - 2 * σ ≠ 0 := ne_of_gt (denominator_pos hσ)
  unfold cutoffLogPower reciprocalLogPower
  field_simp [hD]
  ring

/-- Exact balance for arbitrary positive bases, before choosing the second
    base to be log L. The log-J factor has already been bounded by a constant
    multiple of log L in the analytic estimate. -/
theorem diagonal_term_balances {σ L B : ℝ} (hσ : σ < 1)
    (hL : 0 < L) (hB : 0 < B) :
    (L ^ cutoffPower σ * B ^ cutoffLogPower σ) ^ ((1 : ℝ) / 2 - σ) *
        B ^ ((3 : ℝ) / 2) =
      L ^ (-reciprocalPower σ) * B ^ reciprocalLogPower σ := by
  rw [Real.mul_rpow (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hB.le _)]
  rw [← Real.rpow_mul hL.le, ← Real.rpow_mul hB.le]
  rw [cutoff_diagonal_exponent hσ, mul_assoc, ← Real.rpow_add hB]
  rw [log_diagonal_exponent hσ]

theorem covariance_term_balances {σ L B : ℝ} (hσ : σ < 1)
    (hL : 0 < L) (hB : 0 < B) :
    (L ^ cutoffPower σ * B ^ cutoffLogPower σ) ^ (2 - 2 * σ) / L =
      L ^ (-reciprocalPower σ) * B ^ reciprocalLogPower σ := by
  rw [Real.mul_rpow (Real.rpow_nonneg hL.le _) (Real.rpow_nonneg hB.le _)]
  rw [← Real.rpow_mul hL.le, ← Real.rpow_mul hB.le]
  rw [log_covariance_exponent hσ]
  have hpow : L ^ (cutoffPower σ * (2 - 2 * σ)) / L =
      L ^ (-reciprocalPower σ) := by
    calc
      L ^ (cutoffPower σ * (2 - 2 * σ)) / L =
          L ^ (cutoffPower σ * (2 - 2 * σ)) / L ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = L ^ (cutoffPower σ * (2 - 2 * σ) - 1) :=
        (Real.rpow_sub hL _ _).symm
      _ = L ^ (-reciprocalPower σ) := by rw [cutoff_covariance_exponent hσ]
  calc
    (L ^ (cutoffPower σ * (2 - 2 * σ)) * B ^ reciprocalLogPower σ) / L =
        (L ^ (cutoffPower σ * (2 - 2 * σ)) / L) * B ^ reciprocalLogPower σ := by
          ring
    _ = L ^ (-reciprocalPower σ) * B ^ reciprocalLogPower σ := by rw [hpow]

theorem optimized_diagonal_term {σ L : ℝ} (hσ : σ < 1) (hL : 1 < L) :
    optimizedCutoff σ L ^ ((1 : ℝ) / 2 - σ) * (Real.log L) ^ ((3 : ℝ) / 2) =
      reciprocalRate σ L := by
  exact diagonal_term_balances hσ (by linarith) (Real.log_pos hL)

theorem optimized_covariance_term {σ L : ℝ} (hσ : σ < 1) (hL : 1 < L) :
    optimizedCutoff σ L ^ (2 - 2 * σ) / L = reciprocalRate σ L := by
  exact covariance_term_balances hσ (by linarith) (Real.log_pos hL)

theorem pure_reciprocal_power_tendsto_zero {σ : ℝ}
    (hhalf : (1 : ℝ) / 2 < σ) (hσ : σ < 1) :
    Tendsto (fun L : ℝ => L ^ (-reciprocalPower σ)) atTop (nhds 0) := by
  exact tendsto_rpow_neg_atTop (reciprocalPower_pos hhalf hσ)

/-- A logarithmic factor never prevents a positive reciprocal power from
    vanishing. This proves the complete optimized scalar envelope, rather
    than only its power component, converges to zero. -/
theorem logPowerEnvelope_tendsto_zero {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (logPowerEnvelope a b) atTop (nhds 0) := by
  have hlim : Tendsto (fun L : ℝ => (Real.log L) ^ b / L ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop b ha).tendsto_div_nhds_zero
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  dsimp [logPowerEnvelope]
  rw [Real.rpow_neg hL.le]
  ring

theorem reciprocalRate_tendsto_zero {σ : ℝ}
    (hhalf : (1 : ℝ) / 2 < σ) (hσ : σ < 1) :
    Tendsto (reciprocalRate σ) atTop (nhds 0) := by
  exact logPowerEnvelope_tendsto_zero (reciprocalPower_pos hhalf hσ)
    (reciprocalLogPower σ)

end RiemannResearch.Analysis.ReciprocalRateBalance
