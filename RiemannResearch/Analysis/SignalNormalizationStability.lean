/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Stability of normalization by an exact signal

Source: the user-directed Ramanujan/zero-equidistribution calculation,
21 October 2026; standard Hilbert-space normalization and orthogonal
decomposition supply the proof. The intended inverse-Gram specialization
is in Analysis/FiniteGramSignalStability. No convergence of a growing
arithmetic capacity is asserted.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.SignalNormalizationStability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

def normalized (u v : E) : E := (⟪u, v⟫)⁻¹ • v

theorem normalized_signal (u v : E) (h : ⟪u, v⟫ ≠ 0) :
    ⟪u, normalized u v⟫ = 1 := by
  simp only [normalized, real_inner_smul_right, inv_mul_cancel₀ h]

theorem normalized_energy (u v : E) :
    ‖normalized u v‖ ^ 2 = ‖v‖ ^ 2 / ⟪u, v⟫ ^ 2 := by
  simp only [normalized, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [inv_pow]
  ring

theorem normalized_pythagoras (u v : E) (hu : 0 < ‖u‖ ^ 2)
    (h : ⟪u, v⟫ ≠ 0) :
    ‖normalized u v‖ ^ 2 =
      1 / ‖u‖ ^ 2 + ‖normalized u v - normalized u u‖ ^ 2 := by
  have hu0 : ‖u‖ ^ 2 ≠ 0 := ne_of_gt hu
  have hun : 0 < ‖u‖ := by nlinarith [norm_nonneg u]
  have hun0 := ne_of_gt hun
  have huu : ⟪u, u⟫ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  have hsym : ⟪v, u⟫ = ⟪u, v⟫ := (real_inner_comm v u).symm
  have hcross : ⟪normalized u v, normalized u u⟫ = (‖u‖ ^ 2)⁻¹ := by
    simp only [normalized, real_inner_smul_left, real_inner_smul_right, hsym, huu]
    field_simp [h, hu0, hun0]
  have hself : ‖normalized u u‖ ^ 2 = 1 / ‖u‖ ^ 2 := by
    rw [normalized_energy, huu]
    field_simp [hu0, hun0]
  rw [norm_sub_sq_real, hcross, hself]
  ring

theorem normalized_error_exact (u e : E) (hu : 0 < ‖u‖ ^ 2)
    (h : ⟪u, u + e⟫ ≠ 0) :
    ‖normalized u (u + e) - normalized u u‖ ^ 2 =
      (‖u‖ ^ 2 * ‖e‖ ^ 2 - ⟪u, e⟫ ^ 2) /
        (‖u‖ ^ 2 * ⟪u, u + e⟫ ^ 2) := by
  have hu0 : ‖u‖ ^ 2 ≠ 0 := ne_of_gt hu
  have hun : 0 < ‖u‖ := by nlinarith [norm_nonneg u]
  have hun0 := ne_of_gt hun
  have hp := normalized_pythagoras u (u + e) hu h
  have he : ‖normalized u (u + e) - normalized u u‖ ^ 2 =
      ‖normalized u (u + e)‖ ^ 2 - 1 / ‖u‖ ^ 2 := by linarith
  rw [he, normalized_energy, norm_add_sq_real, inner_add_right,
    real_inner_self_eq_norm_sq]
  have hden : ‖u‖ ^ 2 + ⟪u, e⟫ ≠ 0 := by
    simpa only [inner_add_right, real_inner_self_eq_norm_sq] using h
  field_simp [hu0, hun0, hden]
  ring

theorem pairing_lower (u e : E) {ε : ℝ}
    (he : ‖e‖ ≤ ε * ‖u‖) :
    (1 - ε) * ‖u‖ ^ 2 ≤ ⟪u, u + e⟫ := by
  have hc := (abs_le.mp (abs_real_inner_le_norm u e)).1
  have hm := mul_le_mul_of_nonneg_left he (norm_nonneg u)
  rw [inner_add_right, real_inner_self_eq_norm_sq]
  nlinarith

theorem pairing_pos (u e : E) (hu : 0 < ‖u‖ ^ 2) {ε : ℝ}
    (hε : ε < 1) (he : ‖e‖ ≤ ε * ‖u‖) :
    0 < ⟪u, u + e⟫ := by
  have hl := pairing_lower u e he
  have hp : 0 < (1 - ε) * ‖u‖ ^ 2 := mul_pos (sub_pos.mpr hε) hu
  exact hp.trans_le hl

theorem normalized_error_le (u e : E) (hu : 0 < ‖u‖ ^ 2) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε < 1) (he : ‖e‖ ≤ ε * ‖u‖) :
    ‖normalized u (u + e) - normalized u u‖ ^ 2 ≤
      ε ^ 2 / (‖u‖ ^ 2 * (1 - ε) ^ 2) := by
  have hd := pairing_pos u e hu hε he
  have hl := pairing_lower u e he
  have hu0 := ne_of_gt hu
  have hun : 0 < ‖u‖ := by nlinarith [norm_nonneg u]
  have hun0 := ne_of_gt hun
  have hεp : 0 < 1 - ε := sub_pos.mpr hε
  have he2 : ‖e‖ ^ 2 ≤ ε ^ 2 * ‖u‖ ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr he)
      (add_nonneg (mul_nonneg hε0 (norm_nonneg u)) (norm_nonneg e))
    nlinarith
  have hds : ‖u‖ ^ 4 * (1 - ε) ^ 2 ≤ ⟪u, u + e⟫ ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hl)
      (add_nonneg hd.le (mul_nonneg (sub_nonneg.mpr hε.le) hu.le))
    nlinarith
  have hεn : 1 - ε ≠ 0 := ne_of_gt (sub_pos.mpr hε)
  calc
    _ = (‖u‖ ^ 2 * ‖e‖ ^ 2 - ⟪u, e⟫ ^ 2) /
        (‖u‖ ^ 2 * ⟪u, u + e⟫ ^ 2) :=
      normalized_error_exact u e hu hd.ne'
    _ ≤ (‖u‖ ^ 2 * ‖e‖ ^ 2) /
        (‖u‖ ^ 2 * ⟪u, u + e⟫ ^ 2) :=
      div_le_div_of_nonneg_right (sub_le_self _ (sq_nonneg _)) (by positivity)
    _ = ‖e‖ ^ 2 / ⟪u, u + e⟫ ^ 2 := by field_simp [hu0, hun0]
    _ ≤ (ε ^ 2 * ‖u‖ ^ 2) / ⟪u, u + e⟫ ^ 2 :=
      div_le_div_of_nonneg_right he2 (sq_nonneg _)
    _ ≤ (ε ^ 2 * ‖u‖ ^ 2) / (‖u‖ ^ 4 * (1 - ε) ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hds
    _ = ε ^ 2 / (‖u‖ ^ 2 * (1 - ε) ^ 2) := by
      field_simp [hu0, hun0, hεn]

theorem normalized_tendsto (u : E) (hu : 0 < ‖u‖ ^ 2)
    {α : Type*} {l : Filter α} {v : α → E}
    (hv : Tendsto v l (𝓝 u)) :
    Tendsto (fun i => normalized u (v i)) l (𝓝 (normalized u u)) := by
  have hi : Tendsto (fun i => ⟪u, v i⟫) l (𝓝 ⟪u, u⟫) :=
    tendsto_const_nhds.inner hv
  have hn : ⟪u, u⟫ ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact ne_of_gt hu
  have hc := (tendsto_const_nhds :
      Tendsto (fun _ : α => (1 : ℝ)) l (𝓝 1)).div hi hn
  simpa only [normalized, Pi.div_apply, one_div] using hc.smul hv

/-- The component of the sampling error orthogonal to the exact signal. -/
def orthogonalError (u e : E) : E :=
  e - (⟪u, e⟫ / ‖u‖ ^ 2) • u

theorem orthogonalError_pairing (u e : E) (hu : 0 < ‖u‖ ^ 2) :
    ⟪u, orthogonalError u e⟫ = 0 := by
  have hun : ‖u‖ ≠ 0 := by
    intro h
    rw [h] at hu
    norm_num at hu
  simp only [orthogonalError, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp [hun]
  ring

theorem orthogonalError_norm_sq (u e : E) (hu : 0 < ‖u‖ ^ 2) :
    ‖orthogonalError u e‖ ^ 2 =
      (‖u‖ ^ 2 * ‖e‖ ^ 2 - ⟪u, e⟫ ^ 2) / ‖u‖ ^ 2 := by
  have hun : ‖u‖ ≠ 0 := by
    intro h
    rw [h] at hu
    norm_num at hu
  have hsym : ⟪e, u⟫ = ⟪u, e⟫ := real_inner_comm u e
  simp only [orthogonalError, norm_sub_sq_real, real_inner_smul_right,
    hsym, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp [hun]
  ring

/-- Exact normalization discards every error parallel to the true signal. -/
theorem normalized_error_orthogonal (u e : E) (hu : 0 < ‖u‖ ^ 2)
    (h : ⟪u, u + e⟫ ≠ 0) :
    ‖normalized u (u + e) - normalized u u‖ ^ 2 =
      ‖orthogonalError u e‖ ^ 2 / ⟪u, u + e⟫ ^ 2 := by
  rw [normalized_error_exact u e hu h, orthogonalError_norm_sq u e hu]
  ring

end RiemannResearch.Analysis.SignalNormalizationStability
