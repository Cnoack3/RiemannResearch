/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QTriangularTargetDirection
import RiemannResearch.RH.QSquarefreeHeadSchedule
import RiemannResearch.RH.QSquarefreeAffineHead
import Mathlib.NumberTheory.Divisors
import Lean.Elab.Tactic.Omega

/-!
# Primorial triangular directions lose the constant target

Source: the independently developed October 19 Gram-direction investigation,
recorded in QTriangularDirectionEscapeResearch20261019.md. The imported
primorial schedule supplies all finite dictionary and escape data.

For every nontrivial divisor of primorial(max 3 (n+1)), form the actual
inverse-Gram fit of v_d=1-1/d. Its best scalar approximation of qOne has
captured energy tending to zero and squared error tending to one.
This rules out one proposed synthesis route; it does not obstruct the
whole squarefree legal span or assert any result about RH itself.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.QTriangularCharge
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QCovarianceInverse QCovarianceInvertibility
open RiemannResearch.LinearAlgebra.CenteredNormalEquations
open QSquarefreeAffineHead QSquarefreeHeadSchedule
def primorialConductor (n : ℕ) :
    ↥(conductors (period (n + 1))) → ℕ := fun i => i
theorem primorialConductor_gt_one (n : ℕ) (i : ↥(conductors (period (n + 1)))) :
    1 < primorialConductor n i :=
  conductor_gt_one _ i i.property
theorem primorialConductor_injective (n : ℕ) : Function.Injective (primorialConductor n) :=
  Subtype.val_injective
theorem primorial_directionFit_norm_tendsto_atTop :
    Tendsto (fun n => ‖directionFit (primorialConductor n)‖) atTop atTop := by
  apply directionFit_norm_tendsto_atTop primorialConductor
    primorialConductor_gt_one primorialConductor_injective
    (fun n => ⟨anchor n, (anchor_spec n).1⟩)
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop B] with n hn
  have ha := (anchor_spec n).2.1
  change B ≤ anchor n
  omega
theorem primorialConductor_retained (m : ℕ) (i : ↥(conductors (period (m + 1)))) :
    ∀ᶠ n in atTop, ∃ j, primorialConductor n j = primorialConductor m i := by
  filter_upwards [eventually_ge_atTop m] with n hn
  have hi := Finset.mem_filter.mp i.property
  have hdiv : i.val ∣ period (n + 1) :=
    dvd_trans (Nat.mem_divisors.mp hi.1).1 (period_nested (by omega))
  refine ⟨⟨i.val, Finset.mem_filter.mpr ⟨?_, hi.2⟩⟩, rfl⟩
  exact Nat.mem_divisors.mpr ⟨hdiv, ne_of_gt (period_pos (n + 1))⟩
theorem primorial_rayleighGain_tendsto_zero :
    Tendsto (fun n => rayleighGain (primorialConductor n)) atTop (𝓝 0) :=
  rayleighGain_tendsto_zero primorialConductor
    primorialConductor_gt_one primorialConductor_injective
    primorial_directionFit_norm_tendsto_atTop primorialConductor_retained
theorem primorial_rayleighFit_error_tendsto_one :
    Tendsto (fun n => ‖qOne - rayleighFit (primorialConductor n)‖ ^ 2)
      atTop (𝓝 1) := by
  simpa only [rayleighFit_error _ (primorialConductor_gt_one _)
    (primorialConductor_injective _), rayleighGain, sub_zero]
    using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      primorial_rayleighGain_tendsto_zero

end RiemannResearch.RH.QTriangularCharge
