/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QConductorEstimates
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QBoundedResidueProjection
import RiemannResearch.Analysis.SingleDirectionProjection
import RiemannResearch.Analysis.ConductorLogEnvelope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A single high conductor over a fixed bounded physical subspace

Source: `SingleConductorProjectionBound.md`. The smoothed-residual estimate
is strengthened from the constant target to every Hilbert-space input. Its
constant is uniform over conductor and physical site but may depend on the
fixed low-conductor space. This does not give a bound uniform over growing
canonical stages.
-/

noncomputable section
namespace RiemannResearch.RH.QSingleConductorProjection
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QBoundedSubspaceEvaluation QBoundedResidueProjection
open RiemannResearch.Analysis.SingleDirectionProjection
open RiemannResearch.Analysis.ConductorLogEnvelope

private theorem physical_sub (u v : QHilbert) (n : ℕ) :
    qSequence (u - v) n = qSequence u n - qSequence v n := by
  change qSequenceLinear (u - v) n = _
  rw [map_sub]
  rfl

private theorem physical_add_smul (u v : QHilbert) (a : ℝ) (n : ℕ) :
    qSequence (u + a • v) n = qSequence u n + a * qSequence v n := by
  change qSequenceLinear (u + a • v) n = _
  rw [map_add, map_smul]
  rfl

/-- Explicit quantitative response bound once the residual conductor keeps
one quarter of its natural squared-norm scale. -/
theorem response_bound_of_residual_lower
    (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ u : QHilbert, u ∈ U →
      ∀ n : ℕ, |qSequence u n| ≤ M * ‖u‖)
    (d : ℕ) (hd : 2 ≤ d)
    [(U ⊔ Submodule.span ℝ ({qResidue d} : Set QHilbert)).HasOrthogonalProjection]
    (hG : 1 / (4 * zetaTwo * d) ≤
      ‖qResidue d - U.starProjection (qResidue d)‖ ^ 2)
    (f : QHilbert) (n : ℕ) (hn : 0 < n) :
    |qSequence ((U ⊔ Submodule.span ℝ ({qResidue d} : Set QHilbert)).starProjection
      (B (f - (U ⊔ Submodule.span ℝ ({qResidue d} : Set QHilbert)).starProjection f))) n| ≤
      (M + 4 * (zetaTwo + M) * (2 + 4 * M ^ 2 / zetaTwo)) *
        ‖f‖ * (1 + Real.log (n : ℝ)) := by
  let W := U ⊔ Submodule.span ℝ ({qResidue d} : Set QHilbert)
  let u := qResidue d - U.starProjection (qResidue d)
  let r := f - W.starProjection f
  let ell := 2 + Real.log (d : ℝ)
  let z := zetaTwo * (d : ℝ)
  let K := 4 * (zetaTwo + M)
  let A := 4 * M ^ 2 / zetaTwo
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hz : 0 < z := mul_pos zetaTwo_pos hdpos
  have hell : 2 ≤ ell := by dsimp [ell]; linarith [Real.log_nonneg hd1]
  have hell0 : 0 ≤ ell := by linarith
  have hzeta := zetaTwo_pos
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hGl : 1 / (4 * z) ≤ ‖u‖ ^ 2 := by
    simpa only [u, z, mul_assoc] using hG
  have hGp : 0 < ‖u‖ ^ 2 := lt_of_lt_of_le (by positivity) hGl
  have hu : u ≠ 0 := by intro he; simp [he] at hGp
  have hUnorm : ‖U.starProjection (qResidue d)‖ ≤ M * (ell / z) :=
    qResidue_projection_norm_le_log_div U M hM hbound d hd
  have hUphysical (k : ℕ) :
      |qSequence (U.starProjection (qResidue d)) k| ≤ M ^ 2 * (ell / z) :=
    qResidue_projection_physical_le_log_div U M hM hbound d hd k
  have hBu : ‖B u‖ ≤ (zetaTwo + M) * ell / z := by
    calc
      _ = ‖B (qResidue d) - B (U.starProjection (qResidue d))‖ := by
        simp only [u, map_sub]
      _ ≤ ‖B (qResidue d)‖ + ‖B (U.starProjection (qResidue d))‖ := norm_sub_le _ _
      _ ≤ 1 / (d : ℝ) + M * (ell / z) := add_le_add
        (B_qResidue_norm_le d (by omega)) ((B_norm_le _).trans hUnorm)
      _ ≤ _ := by
        have he : 1 / (d : ℝ) = zetaTwo / z := by
          dsimp [z]
          field_simp [hdpos.ne', zetaTwo_pos.ne']
        rw [he, ← mul_div_assoc, ← add_div]
        apply div_le_div_of_nonneg_right _ hz.le
        nlinarith [zetaTwo_pos]
  let beta := inner ℝ (B r) u / ‖u‖ ^ 2
  have hbeta : |beta| ≤ K * ell * ‖f‖ := by
    calc
      _ ≤ ‖B u‖ * ‖f‖ / ‖u‖ ^ 2 :=
        smoothing_coefficient_le W B B_symmetric u f
      _ ≤ ((zetaTwo + M) * ell / z) * ‖f‖ / ‖u‖ ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBu (norm_nonneg _)) hGp.le
      _ ≤ K * ell * ‖f‖ := by
        apply (div_le_iff₀ hGp).mpr
        have hm := mul_le_mul_of_nonneg_left hGl
          (mul_nonneg (mul_nonneg hK hell0) (norm_nonneg f))
        have he : (K * ell * ‖f‖) * (1 / (4 * z)) =
            ((zetaTwo + M) * ell / z) * ‖f‖ := by
          dsimp [K]
          field_simp [hz.ne']
          <;> ring
        rw [he] at hm
        exact hm
  have hPu (x : QHilbert) : ‖U.starProjection x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖U.starProjection‖ * ‖x‖ := U.starProjection.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le U) (norm_nonneg _)
      _ = _ := one_mul _
  have hlow : |qSequence (U.starProjection (B r)) n| ≤ M * ‖f‖ := by
    apply (hbound _ (U.starProjection_apply_mem _) n).trans
    apply mul_le_mul_of_nonneg_left _ hM
    exact (hPu _).trans ((B_norm_le _).trans (residual_norm_le W f))
  have huq : |qSequence u n| ≤ qSequence (qResidue d) n + M ^ 2 * (ell / z) := by
    dsimp only [u]
    rw [physical_sub]
    rw [sub_eq_add_neg]
    apply (abs_add_le _ _).trans
    rw [abs_neg]
    exact (by
      rw [abs_of_nonneg (qResidue_physical_nonneg d n)]
      exact add_le_add le_rfl (hUphysical n))
  have hfirst : ell * qSequence (qResidue d) n ≤ 2 + Real.log (n : ℝ) :=
    log_mul_qResidue_le_physical_log d n hd hn
  have hsecond : ell * (M ^ 2 * (ell / z)) ≤ A := by
    calc
      _ = (M ^ 2 / zetaTwo) * (ell ^ 2 / (d : ℝ)) := by
        dsimp [z]
        ring
      _ ≤ (M ^ 2 / zetaTwo) * 4 :=
        mul_le_mul_of_nonneg_left (two_add_log_sq_div_le_four (d : ℝ) hd1)
          (div_nonneg (sq_nonneg M) zetaTwo_pos.le)
      _ = _ := by dsimp [A]; ring
  have hhigh : |beta * qSequence u n| ≤
      K * ‖f‖ * (2 + Real.log (n : ℝ) + A) := by
    rw [abs_mul]
    calc
      _ ≤ (K * ell * ‖f‖) *
          (qSequence (qResidue d) n + M ^ 2 * (ell / z)) :=
        mul_le_mul hbeta huq (abs_nonneg _) (by positivity)
      _ = (K * ‖f‖) * (ell * qSequence (qResidue d) n +
          ell * (M ^ 2 * (ell / z))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
        (mul_nonneg hK (norm_nonneg _))
  have hnlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hscalar : M + K * (2 + Real.log (n : ℝ) + A) ≤
      (M + K * (2 + A)) * (1 + Real.log (n : ℝ)) := by
    have hp : 0 ≤ (M + K * (1 + A)) * Real.log (n : ℝ) := by positivity
    nlinarith
  change |qSequence (W.starProjection (B r)) n| ≤ _
  rw [projection_extension_eq U (qResidue d) (B r) hu, physical_add_smul]
  change |qSequence (U.starProjection (B r)) n + beta * qSequence u n| ≤ _
  calc
    _ ≤ M * ‖f‖ + K * ‖f‖ * (2 + Real.log (n : ℝ) + A) :=
      (abs_add_le _ _).trans (add_le_add hlow hhigh)
    _ = ‖f‖ * (M + K * (2 + Real.log (n : ℝ) + A)) := by ring
    _ ≤ ‖f‖ * ((M + K * (2 + A)) * (1 + Real.log (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hscalar (norm_nonneg _)
    _ = _ := by dsimp [K, A]; ring

end RiemannResearch.RH.QSingleConductorProjection
