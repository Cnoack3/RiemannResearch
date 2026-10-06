/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in LICENSE.
-/
import RiemannResearch.RH.CompensatedTwoCoefficientCriterion
import RiemannResearch.RH.ResidueSchurLimits

/-!
# Exact compensated two-coefficient Schur increments

Source: user-provided RH_Dyadic_Coefficient_Bridge_Next_Steps.md,
equations (G)--(I). The actual projection and complete inverse screening
are supplied by ResidueProjectionSchur. Absolute coefficient variation is
already established in ResidueSchurLimits; it does not supply saturation.

Stage n contains every conductor 2,...,n+1. The signed mixed term and
negative innovation square are retained. The cofinal arithmetic provider
remains open.
-/

open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open ProjectionSchur
def twoThreeFunctional : ThresholdHilbert →L[ℝ] ℝ :=
  (3 : ℝ) • coefficientCLM 2 + coefficientCLM 3
def twoThreeModeCharge (n : ℕ) : ℝ := twoThreeFunctional (residueMode n)
def twoThreeSignedIncrement (n : ℕ) : ℝ :=
  modeAlpha n * twoThreeModeCharge n - (23 / 24 : ℝ) * (modeAlpha n)^2
theorem twoThreeCompensated_succ (n : ℕ) :
    twoThreeCompensated (n+1) = twoThreeCompensated n + twoThreeSignedIncrement n := by
  have he : energy (n+1) = energy n - (modeAlpha n)^2 := by
    rw [energy_schur_step, schur_gain_eq_mode_sq]
  have h2 : coefficient (n+1) 2 = coefficient n 2 +
      modeAlpha n * coefficientCLM 2 (residueMode n) := by
    unfold coefficient
    rw [projection_succ_mode, map_add, map_smul]
    rfl
  have h3 : coefficient (n+1) 3 = coefficient n 3 +
      modeAlpha n * coefficientCLM 3 (residueMode n) := by
    unfold coefficient
    rw [projection_succ_mode, map_add, map_smul]
    rfl
  simp only [twoThreeCompensated, twoThreeSignedIncrement, twoThreeModeCharge,
    twoThreeFunctional, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [h2,h3,he]
  ring
theorem twoThreeCompensated_eq_signed_sum (n : ℕ) :
    twoThreeCompensated n = -(73 / 24 : ℝ) +
      ∑ k ∈ Finset.range n, twoThreeSignedIncrement k := by
  induction n with
  | zero =>
    simp [twoThreeCompensated, coefficient, projection_eq_mode_sum,
      energy_eq_one_sub_mode_sum]
    <;> norm_num
  | succ n ih =>
    rw [twoThreeCompensated_succ, ih, Finset.sum_range_succ]
    ring
theorem twoThreeCompensated_schur_increment (n : ℕ) :
    twoThreeCompensated (n+1) - twoThreeCompensated n =
      (schurEta n * twoThreeFunctional (innovation n) -
        (23 / 24 : ℝ) * (schurEta n)^2) / schurSigma n := by
  rw [twoThreeCompensated_succ]
  simp only [add_sub_cancel_left, twoThreeSignedIncrement,
    twoThreeModeCharge, innovation_eq_scale_mode, map_smul,
    smul_eq_mul, eta_eq_scale_alpha, sigma_eq_scale_sq]
  field_simp [ne_of_gt (residueModeScale_pos n)]
  <;> ring
theorem twoThreeFunctional_innovation_screened (n : ℕ) (hn : 2 ≤ n) :
    twoThreeFunctional (innovation n) =
      -(3 * eliminated n ⟨0, by omega⟩ + eliminated n ⟨1, by omega⟩) := by
  have h0 := innovation_old_coefficient n (⟨0, by omega⟩ : Fin n)
  have h1 := innovation_old_coefficient n (⟨1, by omega⟩ : Fin n)
  simp only [Nat.zero_add, Nat.reduceAdd] at h0 h1
  simp only [twoThreeFunctional, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [h0,h1]
  ring
/-- Complete old-stage screening, with the signed mixed term kept. -/
theorem twoThreeCompensated_screened_increment (n : ℕ) (hn : 2 ≤ n) :
    twoThreeCompensated (n+1) - twoThreeCompensated n =
      (-(schurEta n) *
        (3 * eliminated n ⟨0, by omega⟩ + eliminated n ⟨1, by omega⟩) -
        (23/24 : ℝ) * (schurEta n)^2) / schurSigma n := by
  rw [twoThreeCompensated_schur_increment,
    twoThreeFunctional_innovation_screened n hn]
  ring

theorem twoThreeCompensated_after_two (n : ℕ) :
    twoThreeCompensated (n+2) = twoThreeCompensated 2 +
      ∑ k ∈ Finset.range n, twoThreeSignedIncrement (k+2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, twoThreeCompensated_succ, ih,
      Finset.sum_range_succ]
    ring

theorem twoThreeSignedIncrement_eq_mode (n : ℕ) :
    twoThreeSignedIncrement n =
      3 * (modeAlpha n * modeCoefficient 2 n) +
        modeAlpha n * modeCoefficient 3 n -
        (23 / 24 : ℝ) * (modeAlpha n)^2 := by
  simp only [twoThreeSignedIncrement, twoThreeModeCharge,
    twoThreeFunctional, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, modeCoefficient]
  ring

theorem twoThreeSignedIncrement_norm_summable :
    Summable (fun n => ‖twoThreeSignedIncrement n‖) := by
  have hs := (((mode_coefficient_series_norm_summable 2).mul_left (3 : ℝ)).add
    (mode_coefficient_series_norm_summable 3)).add
    (modeAlpha_sq_hasSum.summable.mul_left (23 / 24 : ℝ))
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hs
  rw [twoThreeSignedIncrement_eq_mode]
  have hb := (norm_sub_le
    (3 * (modeAlpha n * modeCoefficient 2 n) + modeAlpha n * modeCoefficient 3 n)
    ((23 / 24 : ℝ) * (modeAlpha n)^2)).trans
    (add_le_add
      (norm_add_le (3 * (modeAlpha n * modeCoefficient 2 n))
        (modeAlpha n * modeCoefficient 3 n))
      (le_refl ‖(23 / 24 : ℝ) * (modeAlpha n)^2‖))
  simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (modeAlpha n))] using hb

theorem twoThreeSignedIncrement_hasSum :
    HasSum twoThreeSignedIncrement (twoThreeCompensatedLimit + 73/24) := by
  apply twoThreeSignedIncrement_norm_summable.of_norm.hasSum_iff_tendsto_nat.mpr
  have he (n : ℕ) :
      (∑ k ∈ Finset.range n, twoThreeSignedIncrement k) =
        twoThreeCompensated n + 73/24 := by
    have h := twoThreeCompensated_eq_signed_sum n
    linarith
  simpa only [he] using
    (twoThreeCompensated_tendsto.add tendsto_const_nhds)

/-- Open arithmetic budget; this is an equivalent consumer, not its provider. -/
def TwoThreeSignedCofinal : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ n : ℕ, max N 2 ≤ n ∧
      (73/24 : ℝ) - ε < ∑ k ∈ Finset.range n, twoThreeSignedIncrement k

theorem twoThreeSigned_cofinal_iff_compensated :
    TwoThreeSignedCofinal ↔ TwoThreeCompensatedCofinal := by
  constructor
  · intro h ε hε N
    obtain ⟨n, hn, hs⟩ := h ε hε N
    refine ⟨n, hn, ?_⟩
    rw [twoThreeCompensated_eq_signed_sum]
    linarith
  · intro h ε hε N
    obtain ⟨n, hn, hs⟩ := h ε hε N
    refine ⟨n, hn, ?_⟩
    rw [twoThreeCompensated_eq_signed_sum] at hs
    linarith

theorem riemannHypothesis_of_twoThreeSigned_cofinal
    (h : TwoThreeSignedCofinal) : RiemannHypothesis :=
  riemannHypothesis_of_twoThreeCompensated_cofinal
    (twoThreeSigned_cofinal_iff_compensated.mp h)

end RiemannResearch.RH.Pareto.CoefficientStabilization
