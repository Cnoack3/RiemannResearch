/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoInverseGramDual
import RiemannResearch.RH.ResidueGramMobiusCorrection

/-!
# The exact dual pairing in the inverse-Gram Mobius correction

Source: user-requested attempt to prove decay of the actual inverse-Gram
correction. These identities retain the entire Hilbert norm. They isolate
an actual mixed pairing; its decay is not assumed or asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection

/-- Residual of the finite, uncorrected negative-Mobius synthesis. -/
def naturalResidual (n : ℕ) : ThresholdHilbert :=
  hilbertOne + ∑ j : Fin n, mobiusVector n j • residueAtom j.val

/-- The part of the actual coefficient dual missed by the finite legal span. -/
def dualResidual (n i : ℕ) : ThresholdHilbert :=
  coefficientDual i - (finiteSpace n).starProjection (coefficientDual i)

theorem coefficientDual_inner (x : ThresholdHilbert) (i : ℕ) :
    inner ℝ x (coefficientDual i) = coefficientCLM (i + 2) x := by
  rw [coefficientDual, inner_neg_right, real_inner_comm, mobiusRieszHilbert_inner]
  rfl

theorem mobiusSynthesis_mem (n : ℕ) :
    (∑ j : Fin n, mobiusVector n j • residueAtom j.val) ∈ finiteSpace n := by
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨j, rfl⟩

/-- The natural residual already annihilates each full finite-support dual
whose coordinate is present. This is not annihilation of its projection. -/
theorem naturalResidual_inner_dual (n : ℕ) (i : Fin n) :
    inner ℝ (naturalResidual n) (coefficientDual i.val) = 0 := by
  rw [coefficientDual_inner]
  simp only [naturalResidual, map_add]
  rw [coefficient_finite_sum]
  simp only [coefficientCLM, neg_apply, mobius_coordinate_one (i.val + 2) (by omega),
    mobiusVector, neg_add_cancel]

/-- The desired inverse-Gram correction is an actual projected-dual pairing. -/
theorem correction_eq_projected_dual_pairing (n : ℕ) (i : Fin n) :
    correction n (i.val + 2) =
      inner ℝ (naturalResidual n)
        ((finiteSpace n).starProjection (coefficientDual i.val)) := by
  rw [← Submodule.inner_starProjection_left_eq_right]
  simp only [naturalResidual, map_add]
  rw [Submodule.starProjection_eq_self_iff.mpr (mobiusSynthesis_mem n),
    inner_add_left, coefficientDual_inner, coefficientDual_inner,
    coefficient_finite_sum]
  rfl

/-- Exact signed pairing which has to tend to zero. -/
theorem correction_eq_neg_dualResidual_pairing (n : ℕ) (i : Fin n) :
    correction n (i.val + 2) =
      -inner ℝ (naturalResidual n) (dualResidual n i.val) := by
  rw [dualResidual, inner_sub_right, naturalResidual_inner_dual, zero_sub, neg_neg]
  exact correction_eq_projected_dual_pairing n i

/-- An exact energy identity retaining the signed interaction with the missed
part of the coefficient dual. No cross term has been discarded. -/
theorem correction_twice_eq_energy_difference (n : ℕ) (i : Fin n) :
    2 * correction n (i.val + 2) =
      ‖naturalResidual n‖ ^ 2 + ‖coefficientDual i.val‖ ^ 2 -
        residueInverseEntry n i i -
        ‖naturalResidual n + dualResidual n i.val‖ ^ 2 := by
  have hd := residueInverseEntry_diagonal n i
  change ‖dualResidual n i.val‖ ^ 2 = _ at hd
  have ha := norm_add_sq_real (naturalResidual n) (dualResidual n i.val)
  have hc := correction_eq_neg_dualResidual_pairing n i
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
