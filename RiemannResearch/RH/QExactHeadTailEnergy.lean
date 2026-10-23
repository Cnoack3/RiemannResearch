/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QFullHeadControllability
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.Analysis.DenseProjectionTesting
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact tail-energy cost of legal head interpolation

Source: Section 7 of the user-provided uniform dual bound continuation,
22 October 2026. The exact signed identity precedes its Cauchy--Schwarz bound.
This module supplies no unconditional uniform interpolation-energy bound.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QExactHeadTailEnergy
open ZetaTwoHilbert QFiniteSupportDualCriterion QAnnihilatorTailEscape

/-- Matching the head leaves precisely the energy outside that head. -/
theorem remainder_energy (M : ℕ) (f : QHilbert)
    (hf : finiteHead M f = finiteHead M qOne) :
    ‖f - finiteHead M qOne‖ ^ 2 = ‖f‖ ^ 2 - ‖finiteHead M qOne‖ ^ 2 := by
  have h := finiteHead_norm_sq_split M f
  rw [hf] at h
  linarith

/-- The complete signed tail pairing exactly cancels the head mean. -/
theorem annihilator_head_tail_identity (M : ℕ) (f u : QHilbert)
    (hfV : f ∈ QFullResidueProjection.closure)
    (hf : finiteHead M f = finiteHead M qOne)
    (hu : u ∈ QFullResidueProjection.closureᗮ) :
    inner ℝ qOne (finiteHead M u) =
      -inner ℝ (f - finiteHead M qOne) (tail M u) := by
  have hz := Submodule.inner_right_of_mem_orthogonal hfV hu
  have hhead : inner ℝ f (finiteHead M u) =
      inner ℝ qOne (finiteHead M u) := by
    rw [← finiteHead_inner, hf, finiteHead_inner]
  have hzero : inner ℝ (finiteHead M qOne) (tail M u) = 0 :=
    inner_finiteHead_tail M qOne u
  rw [inner_sub_left, hzero, sub_zero, tail, inner_sub_right, hz, hhead]
  ring

/-- The prescribed head energy is subtracted before estimating the tail. -/
theorem annihilator_head_energy_bound (M : ℕ) (f u : QHilbert)
    (hfV : f ∈ QFullResidueProjection.closure)
    (hf : finiteHead M f = finiteHead M qOne)
    (hu : u ∈ QFullResidueProjection.closureᗮ) :
    (inner ℝ qOne (finiteHead M u)) ^ 2 ≤
      (‖f‖ ^ 2 - ‖finiteHead M qOne‖ ^ 2) * ‖tail M u‖ ^ 2 := by
  have hc := abs_real_inner_le_norm (f - finiteHead M qOne) (tail M u)
  have hs := mul_self_le_mul_self (abs_nonneg
    (inner ℝ (f - finiteHead M qOne) (tail M u))) hc
  have hi := annihilator_head_tail_identity M f u hfV hf hu
  have he := remainder_energy M f hf
  rw [hi, neg_sq, ← he]
  nlinarith [sq_abs (inner ℝ (f - finiteHead M qOne) (tail M u))]

theorem actualResidual_head_energy_bound (M : ℕ) (f : QHilbert)
    (hfV : f ∈ QFullResidueProjection.closure)
    (hf : finiteHead M f = finiteHead M qOne) :
    (inner ℝ qOne (finiteHead M actualResidual)) ^ 2 ≤
      (‖f‖ ^ 2 - ‖finiteHead M qOne‖ ^ 2) * ‖tail M actualResidual‖ ^ 2 :=
  annihilator_head_energy_bound M f actualResidual hfV hf
    actualResidual_mem_orthogonal

/-- A nonzero full-span annihilator has a nonzero tail at every head. -/
theorem annihilator_tail_ne_zero (M : ℕ) (u : QHilbert)
    (hu : u ∈ QFullResidueProjection.closureᗮ) (hne : u ≠ 0) :
    tail M u ≠ 0 := by
  intro hz
  have he : u = finiteHead M u := sub_eq_zero.mp hz
  have hp : QFullResidueProjection.closure.starProjection (finiteHead M u) = 0 := by
    rw [← he]
    have hmem := QFullResidueProjection.closure.starProjection_apply_mem u
    have hzero := Submodule.inner_right_of_mem_orthogonal hmem hu
    rw [RiemannResearch.Analysis.DenseProjectionTesting.inner_eq_projected_test
      QFullResidueProjection.closure hmem u, real_inner_self_eq_norm_sq] at hzero
    have hn := norm_nonneg (QFullResidueProjection.closure.starProjection u)
    exact norm_eq_zero.mp (by nlinarith)
  have hh := (QFullHeadControllability.finiteHead_projection_eq_zero_iff M u).mp hp
  exact hne (he.trans hh)

end RiemannResearch.RH.QExactHeadTailEnergy
