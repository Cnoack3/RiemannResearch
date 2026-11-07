/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ParetoWeights
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Isometric transport of Q/P distances and projections

Source: the user's isometric-distance transport argument, 6 November 2026.
The two weighted spaces have the same normalized real lp realization.
The identity on encoded coordinates therefore represents physical
multiplication by sqrt(Q/P), not the sequence-preserving toPareto map.

The physical multiplier is proved explicitly before the transport API.
The image subspace A(V) must not be identified with the original physical
Pareto space V. Mathlib supplies the general isometry-distance and projection
conjugacy theorems; the full-conductor consumer is QFullIsometricTransport.
-/

noncomputable section
namespace RiemannResearch.RH.QParetoIsometricTransport
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QShiftedReciprocal

/-- The weight isometry; its nontrivial physical action is given by A_physical. -/
def A : QHilbert ≃ₗᵢ[ℝ] ThresholdHilbert := LinearIsometryEquiv.refl ℝ _

/-- The same encoded coordinate decodes with different physical weights. -/
theorem A_sequence_ratio (f : QHilbert) (n : ℕ) :
    hilbertSequence (A f) (n+1) =
      (Real.sqrt (qWeight n) / Real.sqrt (paretoWeight n)) * qSequence f (n+1) := by
  change f n / Real.sqrt (paretoWeight n) =
    (Real.sqrt (qWeight n) / Real.sqrt (paretoWeight n)) *
      (f n / Real.sqrt (qWeight n))
  field_simp [(Real.sqrt_pos.mpr (qWeight_pos n)).ne',
    (Real.sqrt_pos.mpr (paretoWeight_pos n)).ne']

/-- Exact ratio of the probability weights at physical site n+1. -/
theorem qWeight_div_paretoWeight (n : ℕ) :
    qWeight n / paretoWeight n = ((n : ℝ)+2) / (zetaTwo*((n : ℝ)+1)) := by
  have h1 : (n : ℝ)+1 ≠ 0 := by positivity
  have h2 : (n : ℝ)+2 ≠ 0 := by positivity
  simp only [qWeight, positiveQWeight, paretoWeight, Nat.cast_add, Nat.cast_one]
  field_simp [zetaTwo_pos.ne', h1, h2]

/-- Physical A multiplies by sqrt((n+1)/(zeta(2)*n)), with positive sites shifted. -/
theorem A_physical (f : QHilbert) (n : ℕ) :
    hilbertSequence (A f) (n+1) =
      Real.sqrt (((n : ℝ)+2)/(zetaTwo*((n : ℝ)+1))) * qSequence f (n+1) := by
  rw [← qWeight_div_paretoWeight, Real.sqrt_div (qWeight_pos n).le]
  exact A_sequence_ratio f n

/-- Transport of the smoothed vector retains the reciprocal multiplier. -/
theorem A_reciprocal_physical (f : QHilbert) (n : ℕ) :
    hilbertSequence (A (B f)) (n+1) =
      Real.sqrt (((n : ℝ)+2)/(zetaTwo*((n : ℝ)+1))) *
        qSequence f (n+1) / ((n : ℝ)+2) := by
  rw [A_physical, qSequence_B]
  push_cast
  ring

/-- The inverse isometry multiplies by the inverse square-root weight ratio. -/
theorem A_symm_sequence_ratio (f : ThresholdHilbert) (n : ℕ) :
    qSequence (A.symm f) (n+1) =
      (Real.sqrt (paretoWeight n) / Real.sqrt (qWeight n)) * hilbertSequence f (n+1) := by
  change f n / Real.sqrt (qWeight n) =
    (Real.sqrt (paretoWeight n) / Real.sqrt (qWeight n)) *
      (f n / Real.sqrt (paretoWeight n))
  field_simp [(Real.sqrt_pos.mpr (qWeight_pos n)).ne',
    (Real.sqrt_pos.mpr (paretoWeight_pos n)).ne']

/-- Exact inverse weight ratio. -/
theorem paretoWeight_div_qWeight (n : ℕ) :
    paretoWeight n / qWeight n = zetaTwo*((n : ℝ)+1)/((n : ℝ)+2) := by
  have h1 : (n : ℝ)+1 ≠ 0 := by positivity
  have h2 : (n : ℝ)+2 ≠ 0 := by positivity
  simp only [qWeight, positiveQWeight, paretoWeight, Nat.cast_add, Nat.cast_one]
  field_simp [zetaTwo_pos.ne', h1, h2]

/-- Physical inverse A multiplies by sqrt(zeta(2)*n/(n+1)). -/
theorem A_symm_physical (f : ThresholdHilbert) (n : ℕ) :
    qSequence (A.symm f) (n+1) =
      Real.sqrt (zetaTwo*((n : ℝ)+1)/((n : ℝ)+2)) * hilbertSequence f (n+1) := by
  rw [← paretoWeight_div_qWeight, Real.sqrt_div (paretoWeight_pos n).le]
  exact A_symm_sequence_ratio f n

/-- The actual isometric image, not the same-physical-sequence Pareto image. -/
def imageSubmodule (S : Submodule ℝ QHilbert) : Submodule ℝ ThresholdHilbert :=
  S.map A.toLinearEquiv.toLinearMap

instance imageSubmodule_hasOrthogonalProjection (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] : (imageSubmodule S).HasOrthogonalProjection := by
  unfold imageSubmodule
  infer_instance

/-- Distance is preserved when both the vector and the subspace are transported. -/
theorem infDist_A_image (S : Submodule ℝ QHilbert) (f : QHilbert) :
    Metric.infDist (A f) (imageSubmodule S : Set ThresholdHilbert) =
      Metric.infDist f (S : Set QHilbert) := by
  change Metric.infDist (A f) (A '' (S : Set QHilbert)) = _
  exact Metric.infDist_image A.isometry

/-- Leaving the target in P introduces the inverse isometry on the Q side. -/
theorem infDist_image_eq_inverse (S : Submodule ℝ QHilbert) (f : ThresholdHilbert) :
    Metric.infDist f (imageSubmodule S : Set ThresholdHilbert) =
      Metric.infDist (A.symm f) (S : Set QHilbert) := by
  simpa only [A.apply_symm_apply] using infDist_A_image S (A.symm f)

/-- The correct distance identity for the user's reciprocal approximants. -/
theorem infDist_reciprocal_transport (S : Submodule ℝ QHilbert) (g : QHilbert) :
    Metric.infDist (B g) (S : Set QHilbert) =
      Metric.infDist (A (B g)) (imageSubmodule S : Set ThresholdHilbert) :=
  (infDist_A_image S (B g)).symm

/-- The proposed alternate distance involves A inverse, not the reciprocal R. -/
theorem infDist_same_sequence_image (S : Submodule ℝ QHilbert) (g : QHilbert) :
    Metric.infDist (toPareto g) (imageSubmodule S : Set ThresholdHilbert) =
      Metric.infDist (A.symm (toPareto g)) (S : Set QHilbert) :=
  infDist_image_eq_inverse S (toPareto g)

/-- The transported projection is onto A(S), not onto the original physical S. -/
theorem projection_conjugacy (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] (f : ThresholdHilbert) :
    (imageSubmodule S).starProjection f = A (S.starProjection (A.symm f)) :=
  Submodule.starProjection_map_apply A S f

/-- Apply projection conjugacy to a transported vector. -/
theorem projection_A (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] (f : QHilbert) :
    (imageSubmodule S).starProjection (A f) = A (S.starProjection f) := by
  rw [projection_conjugacy, A.symm_apply_apply]

/-- Exact conjugacy of the residual vector. -/
theorem projection_defect_A (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] (f : QHilbert) :
    A f - (imageSubmodule S).starProjection (A f) = A (f - S.starProjection f) := by
  rw [projection_A, map_sub]

/-- Exact equality of projection-error norms under the isometry. -/
theorem projection_defect_norm (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] (f : QHilbert) :
    ‖A f - (imageSubmodule S).starProjection (A f)‖ = ‖f - S.starProjection f‖ := by
  rw [projection_defect_A, A.norm_map]

end RiemannResearch.RH.QParetoIsometricTransport
