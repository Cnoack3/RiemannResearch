/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParityProjectionDefect
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Exact legal capture of parity leakage

Source: the user-provided RH/CRT continuation agenda, 20 October 2026, Priority 2.
These identities identify exactly what an actual legal extension captures from
the parity-conditioned optimizer. No lower bound for the arithmetic gain is
assumed or asserted. The complete unapproximated norm-square term is retained.
-/

noncomputable section
namespace RiemannResearch.RH.QParityProjectionDefect
open ZetaTwoHilbert QDivisorLegality

variable (V W : Submodule ℝ QHilbert)
variable [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]

/-- The parity target is an exact affine combination of the constant and g₂. -/
theorem parity_optimizer_affine (h2 : qResidue 2 ∈ V) :
    paritySpace.starProjection (V.starProjection qOne) =
      (1 - 4 * ‖qOne - V.starProjection qOne‖ ^ 2) • qOne +
        (8 * ‖qOne - V.starProjection qOne‖ ^ 2) • qResidue 2 := by
  rw [parity_projection_optimizer V h2, qDivisor_two_eq]
  module

/-- Its residual against any legal test space containing g₂ is the same
constant residual with its exact scalar factor. -/
theorem parity_optimizer_residual (h2V : qResidue 2 ∈ V)
    (h2W : qResidue 2 ∈ W) :
    paritySpace.starProjection (V.starProjection qOne) -
        W.starProjection (paritySpace.starProjection (V.starProjection qOne)) =
      (1 - 4 * ‖qOne - V.starProjection qOne‖ ^ 2) •
        (qOne - W.starProjection qOne) := by
  rw [parity_optimizer_affine V h2V, map_add, map_smul, map_smul,
    Submodule.starProjection_eq_self_iff.mpr h2W]
  module

/-- Exact full-Q distance of the parity target from the extension space. -/
theorem parity_optimizer_distance_sq (h2V : qResidue 2 ∈ V)
    (h2W : qResidue 2 ∈ W) :
    ‖paritySpace.starProjection (V.starProjection qOne) -
        W.starProjection (paritySpace.starProjection (V.starProjection qOne))‖ ^ 2 =
      (1 - 4 * ‖qOne - V.starProjection qOne‖ ^ 2) ^ 2 *
        ‖qOne - W.starProjection qOne‖ ^ 2 := by
  rw [parity_optimizer_residual V W h2V h2W, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]

/-- The actual innovation of the parity target is exactly the constant innovation. -/
theorem parity_optimizer_innovation (h2V : qResidue 2 ∈ V)
    (h2W : qResidue 2 ∈ W) :
    W.starProjection (paritySpace.starProjection (V.starProjection qOne)) -
        V.starProjection (paritySpace.starProjection (V.starProjection qOne)) =
      (1 - 4 * ‖qOne - V.starProjection qOne‖ ^ 2) •
        (W.starProjection qOne - V.starProjection qOne) := by
  rw [parity_optimizer_affine V h2V, map_add, map_add,
    map_smul, map_smul, map_smul, map_smul,
    Submodule.starProjection_eq_self_iff.mpr h2W,
    Submodule.starProjection_eq_self_iff.mpr h2V]
  module

/-- A legal parity gain measures the same unknown arithmetic gain, with no
discarded norm-square remainder. -/
theorem parity_optimizer_gain_exact (hVW : V ≤ W) (h2 : qResidue 2 ∈ V) :
    ‖W.starProjection (paritySpace.starProjection (V.starProjection qOne)) -
        V.starProjection (paritySpace.starProjection (V.starProjection qOne))‖ ^ 2 =
      (1 - 4 * ‖qOne - V.starProjection qOne‖ ^ 2) ^ 2 *
        (‖qOne - V.starProjection qOne‖ ^ 2 -
          ‖qOne - W.starProjection qOne‖ ^ 2) := by
  rw [parity_optimizer_innovation V W h2 (hVW h2), norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  have h := RiemannResearch.Analysis.ExhaustiveWalk.nested_projection_energy V W hVW qOne
  change ‖qOne - V.starProjection qOne‖ ^ 2 =
    ‖qOne - W.starProjection qOne‖ ^ 2 +
      ‖W.starProjection qOne - V.starProjection qOne‖ ^ 2 at h
  congr 1
  linarith

/-- The old space already captures exactly 4D times the parity leakage energy.
This capture must not be mistaken for an innovation from new conductors. -/
theorem old_space_parity_leakage_exact (h2 : qResidue 2 ∈ V) :
    ‖V.starProjection (V.starProjection qOne -
        paritySpace.starProjection (V.starProjection qOne))‖ ^ 2 =
      4 * (‖qOne - V.starProjection qOne‖ ^ 2) ^ 2 *
        (1 - 4 * ‖qOne - V.starProjection qOne‖ ^ 2) := by
  let l := V.starProjection qOne - paritySpace.starProjection (V.starProjection qOne)
  have hpy := RiemannResearch.Analysis.ProjectionCompression.projection_pythagoras V l
  have hr : l - V.starProjection l =
      -(paritySpace.starProjection (V.starProjection qOne) -
        V.starProjection (paritySpace.starProjection (V.starProjection qOne))) := by
    dsimp [l]
    rw [map_sub, Submodule.starProjection_eq_self_iff.mpr
      (V.starProjection_apply_mem qOne)]
    abel
  rw [hr, norm_neg, parity_optimizer_distance_sq V V h2 h2] at hpy
  have hl := optimizer_parity_leakage_exact V h2
  change ‖l‖ ^ 2 = _ at hl
  change ‖V.starProjection l‖ ^ 2 = _
  rw [hl] at hpy
  nlinarith [hpy]

end RiemannResearch.RH.QParityProjectionDefect
