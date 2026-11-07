/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoIsometricTransport
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullCofinalHarmonic
import RiemannResearch.RH.QFullReciprocalLimits
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace

/-!
# Full-conductor RH defect under isometric transport

Source: the user's change-of-measure distance question, 6 November 2026.
The target transports from 1 to A(1), and the subspace transports from V
to A(V). All integer conductors are retained. The vanishing transported
projection defect is an explicit Open hypothesis in the RH implication.
No invariance of the original physical space under A is asserted.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QFullIsometricTransport
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QShiftedReciprocal
open QFullResidueProjection QFullDisplacement QFullReciprocalLimits QParetoIsometricTransport

/-- Isometric image of the actual full-conductor Q closure. -/
abbrev transportedClosure : Submodule ℝ ThresholdHilbert := imageSubmodule closure

/-- Transport changes both the target and the projection subspace. -/
theorem transported_projection_target :
    transportedClosure.starProjection (A qOne) = A (closure.starProjection qOne) :=
  projection_A closure qOne

/-- The Q residual becomes the P residual for target A(1) and subspace A(V). -/
theorem transported_residual :
    A qOne - transportedClosure.starProjection (A qOne) = A qResidual :=
  projection_defect_A closure qOne

/-- The precise reciprocal defect transported to the Pareto metric. -/
theorem transported_defect_eq (g : QHilbert) :
    A (B g) - transportedClosure.starProjection (A (B g)) =
      A (B g - closure.starProjection (B g)) :=
  projection_defect_A closure (B g)

/-- Zero displacement iff the additional transported defect vanishes. -/
theorem displacement_eq_zero_iff_transported_defect {G : ℕ → QHilbert}
    (h : Tendsto G atTop (𝓝 displacement)) :
    displacement = 0 ↔
      Tendsto (fun M => A (B (G M)) - transportedClosure.starProjection (A (B (G M))))
        atTop (𝓝 0) := by
  have he : (fun M => A (B (G M)) -
      transportedClosure.starProjection (A (B (G M)))) =
      (fun M => A (B (G M) - closure.starProjection (B (G M)))) :=
    funext (fun M => transported_defect_eq (G M))
  rw [he]
  change displacement = 0 ↔ Tendsto
    (fun M => B (G M) - closure.starProjection (B (G M))) atTop (𝓝 0)
  exact displacement_eq_zero_iff_defect_tendsto_zero h

/-- Conditional RH reduction; the zero-defect estimate remains Open. -/
theorem riemannHypothesis_of_transported_defect {G : ℕ → QHilbert}
    (h : Tendsto G atTop (𝓝 displacement))
    (hz : Tendsto
      (fun M => A (B (G M)) - transportedClosure.starProjection (A (B (G M))))
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_displacement_eq_zero
    ((displacement_eq_zero_iff_transported_defect h).mpr hz)

end RiemannResearch.RH.QFullIsometricTransport
