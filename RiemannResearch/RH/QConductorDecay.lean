/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QConductorEstimates
import RiemannResearch.RH.QBoundedResidueProjection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalized high-conductor atoms: weak decay and reciprocal smoothing

Source: the elementary normalized-atom estimates in
LegalSubspaceProjectionObstruction.md. Their norm remains bounded away from
zero, but every bounded physical test has a vanishing pairing and their
reciprocal-smoothed norm tends to zero.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.ZetaTwoHilbert
open ZetaTwoProbability QShiftedReciprocal QBoundedSubspaceEvaluation QBoundedResidueProjection

def normalizedConductor (d : ℕ) : QHilbert := Real.sqrt (d : ℝ) • qResidue d

theorem normalizedConductor_norm_sq (d : ℕ) :
    ‖normalizedConductor d‖ ^ 2 = (d : ℝ) * ‖qResidue d‖ ^ 2 := by
  rw [normalizedConductor, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (Nat.cast_nonneg d)]

theorem normalizedConductor_norm_sq_le (d : ℕ) (hd : 2 ≤ d) :
    ‖normalizedConductor d‖ ^ 2 ≤ 2 / zetaTwo := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [normalizedConductor_norm_sq]
  calc
    _ ≤ (d : ℝ) * (2 / (zetaTwo * d)) :=
      mul_le_mul_of_nonneg_left (qResidue_norm_sq_le_two_div d hd) hdp.le
    _ = _ := by field_simp [hdp.ne', zetaTwo_pos.ne']

theorem normalizedConductor_norm_sq_ge (d : ℕ) (hd : 0 < d) :
    ((d : ℝ) - 1) / (zetaTwo * d) ≤ ‖normalizedConductor d‖ ^ 2 := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  rw [normalizedConductor_norm_sq]
  calc
    _ = (d : ℝ) * (((d : ℝ) - 1) / (zetaTwo * (d : ℝ) ^ 2)) := by
      field_simp [hdp.ne', zetaTwo_pos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (qResidue_norm_sq_ge_head d hd) hdp.le

theorem B_normalizedConductor_norm_le (d : ℕ) (hd : 0 < d) :
    ‖B (normalizedConductor d)‖ ≤ 1 / Real.sqrt (d : ℝ) := by
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hsp : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdp
  rw [normalizedConductor, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (d : ℝ) * (1 / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left (B_qResidue_norm_le d hd) (Real.sqrt_nonneg _)
    _ = _ := by
      field_simp [hdp.ne', hsp.ne']
      exact Real.sq_sqrt hdp.le

theorem B_normalizedConductor_norm_tendsto_zero :
    Tendsto (fun d : ℕ => ‖B (normalizedConductor d)‖) atTop (𝓝 0) := by
  have ht : Tendsto (fun d : ℕ => 1 / Real.sqrt (d : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero' (Eventually.of_forall (fun d => norm_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with d hd
  exact B_normalizedConductor_norm_le d hd

theorem sqrt_mul_qResidue_mean_tendsto_zero :
    Tendsto (fun d : ℕ => Real.sqrt (d : ℝ) * inner ℝ qOne (qResidue d))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun d : ℕ => Real.log (d : ℝ) / Real.sqrt (d : ℝ))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      ((isLittleO_log_rpow_atTop (show 0 < (1 / (2 : ℝ)) by norm_num)).tendsto_div_nhds_zero).comp hnat
  have hinv : Tendsto (fun d : ℕ => 1 / Real.sqrt (d : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp hnat)
  have hmajor : Tendsto (fun d : ℕ =>
      (2 + Real.log (d : ℝ)) / (zetaTwo * Real.sqrt (d : ℝ))) atTop (𝓝 0) := by
    have h := ((hinv.const_mul 2).add hlog).div_const zetaTwo
    convert h using 1
    · funext d
      ring
    · simp only [mul_zero, zero_add, zero_div]
  apply squeeze_zero' (Eventually.of_forall (fun d =>
    mul_nonneg (Real.sqrt_nonneg _) (qResidue_mean_nonnegative d))) _ hmajor
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with d hd
  have hdp : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hsp : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdp
  calc
    _ ≤ Real.sqrt (d : ℝ) * ((2 + Real.log (d : ℝ)) / (zetaTwo * d)) :=
      mul_le_mul_of_nonneg_left (qResidue_mean_le_log_div d hd) (Real.sqrt_nonneg _)
    _ = _ := by
      field_simp [hdp.ne', hsp.ne', zetaTwo_pos.ne']
      nlinarith [Real.sq_sqrt hdp.le]

/-- The normalized atoms have a uniform complete-Q norm bound. -/
theorem normalizedConductor_norm_le (d : ℕ) (hd : 2 ≤ d) :
    ‖normalizedConductor d‖ ≤ Real.sqrt (2 / zetaTwo) := by
  have hz := zetaTwo_pos
  have hsq := normalizedConductor_norm_sq_le d hd
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 / zetaTwo)
  nlinarith [Real.sqrt_nonneg (2 / zetaTwo), norm_nonneg (normalizedConductor d)]

/-- Reciprocal energy vanishes even though the unsmoothed norm stays positive. -/
theorem normalizedConductor_reciprocal_energy_tendsto_zero :
    Tendsto (fun d : ℕ => inner ℝ (normalizedConductor d) (B (normalizedConductor d)))
      atTop (𝓝 0) := by
  have ht := B_normalizedConductor_norm_tendsto_zero.const_mul (Real.sqrt (2 / zetaTwo))
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun d => B_positive _)) _ ht
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with d hd
  exact (real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (normalizedConductor_norm_le d hd) (norm_nonneg _))

/-- The first moment formulation is exactly the Q-L1 formulation for the
nonnegative residue atoms. -/
theorem sqrt_mul_qResidue_qL1_tendsto_zero :
    Tendsto (fun d : ℕ => Real.sqrt (d : ℝ) * qL1 (qResidue d))
      atTop (𝓝 0) := by
  simpa only [qResidue_qL1_eq_mean] using sqrt_mul_qResidue_mean_tendsto_zero

/-- Every fixed bounded physical test sees the normalized atoms tend to zero. -/
theorem normalizedConductor_inner_tendsto_zero
    (f : QHilbert) (C : ℝ)
    (hf : ∀ n : ℕ, |qSequence f n| ≤ C) :
    Tendsto (fun d : ℕ => inner ℝ f (normalizedConductor d)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  change Tendsto (fun d : ℕ => |inner ℝ f (normalizedConductor d)|) atTop (𝓝 0)
  have ht := sqrt_mul_qResidue_qL1_tendsto_zero.const_mul C
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun d => abs_nonneg _)) _ ht
  apply Eventually.of_forall
  intro d
  rw [normalizedConductor, real_inner_smul_right, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt (d : ℝ) * (C * qL1 (qResidue d)) :=
      mul_le_mul_of_nonneg_left
        (abs_inner_le_physical_bound_mul_qL1 f (qResidue d) C hf)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- A complete bounded physical subspace captures vanishing normalized mass. -/
theorem sqrt_mul_qResidue_projection_norm_tendsto_zero
    (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖) :
    Tendsto (fun d : ℕ => Real.sqrt (d : ℝ) * ‖U.starProjection (qResidue d)‖)
      atTop (𝓝 0) := by
  have ht := sqrt_mul_qResidue_qL1_tendsto_zero.const_mul C
  simp only [mul_zero] at ht
  apply squeeze_zero' (Eventually.of_forall (fun d =>
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))) _ ht
  apply Eventually.of_forall
  intro d
  calc
    _ ≤ Real.sqrt (d : ℝ) * (C * qL1 (qResidue d)) :=
      mul_le_mul_of_nonneg_left
        (projection_norm_le_qL1 U C hC hbound (qResidue d)) (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Projection loss is little-o of the conductor atom's natural squared norm. -/
theorem mul_qResidue_projection_norm_sq_tendsto_zero
    (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ C * ‖u‖) :
    Tendsto (fun d : ℕ => (d : ℝ) * ‖U.starProjection (qResidue d)‖ ^ 2)
      atTop (𝓝 0) := by
  have h := (sqrt_mul_qResidue_projection_norm_tendsto_zero U C hC hbound).pow 2
  simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), zero_pow (by decide : 2 ≠ 0)] using h

/-- Any fixed additive constant in the logarithm is negligible on the square-root scale. -/
theorem add_log_div_sqrt_tendsto_zero (c : ℝ) :
    Tendsto (fun d : ℕ => (c + Real.log (d : ℝ)) / Real.sqrt (d : ℝ))
      atTop (𝓝 0) := by
  have hnat : Tendsto (fun d : ℕ => (d : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun d : ℕ => Real.log (d : ℝ) / Real.sqrt (d : ℝ))
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      ((isLittleO_log_rpow_atTop (show 0 < (1 / (2 : ℝ)) by norm_num)).tendsto_div_nhds_zero).comp hnat
  have hinv : Tendsto (fun d : ℕ => 1 / Real.sqrt (d : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp hnat)
  have he : (fun d : ℕ => (c + Real.log (d : ℝ)) / Real.sqrt (d : ℝ)) =
      (fun d : ℕ => c * (1 / Real.sqrt (d : ℝ)) +
        Real.log (d : ℝ) / Real.sqrt (d : ℝ)) := by
    funext d
    ring
  rw [he]
  simpa only [mul_zero, zero_add] using (hinv.const_mul c).add hlog

theorem add_log_sq_div_tendsto_zero (c : ℝ) :
    Tendsto (fun d : ℕ => (c + Real.log (d : ℝ)) ^ 2 / (d : ℝ))
      atTop (𝓝 0) := by
  have h := (add_log_div_sqrt_tendsto_zero c).pow 2
  simpa only [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), zero_pow (by decide : 2 ≠ 0)] using h

end RiemannResearch.RH.ZetaTwoHilbert
