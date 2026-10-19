/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/

import RiemannResearch.RH.QTriangularCoefficientProbe
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.RH.SquarefreeMobiusProjection
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
/-!
# Ambient completeness of the triangular Q dual dictionary

Source: continuation of the user's Balazard triangular dual refinement.
The exact coefficient probes and separation of Mobius coordinates imply
density of the whole triangular Riesz family in the actual Q Hilbert space.
This is ambient dual density. No residue-span membership or legal
approximation-energy bound is inferred from it.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QTriangularCharge
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QParetoEquivalence
open SquarefreeMobiusProjection
open RiemannResearch.Analysis.ExhaustiveWalk
theorem q_eq_zero_of_all_coefficients_zero (h : QHilbert)
    (hz : ∀ i, qCoefficientCLM (i + 2) h = 0) : h = 0 := by
  apply paretoEquiv.injective
  change toPareto h = toParetoLinear 0
  rw [map_zero]
  apply eq_zero_of_mobius_coordinates_zero
  intro m hm
  have hh := hz (m - 2)
  have he : m - 2 + 2 = m := by omega
  rw [he] at hh
  change -mobiusDifferenceCLM m (toPareto h) = 0 at hh
  exact neg_eq_zero.mp hh
theorem triangular_dictionaryClosure_eq_top :
    dictionaryClosure riesz = ⊤ := by
  let K : Submodule ℝ QHilbert := dictionaryClosure riesz
  have hr (n : ℕ) : riesz n ∈ K := by
    apply Submodule.le_topologicalClosure
    exact Submodule.subset_span ⟨n, rfl⟩
  have hp (n : ℕ) : coefficientProbe n ∈ K := by
    unfold coefficientProbe
    exact K.smul_mem _ (K.sub_mem
      (K.sub_mem (K.smul_mem _ (K.smul_mem _ (hr (n + 1))))
        (K.smul_mem _ (hr n))) (K.smul_mem _ (hr (n + 2))))
  apply top_unique
  intro x hx
  let r : QHilbert := x - K.starProjection x
  have ho : r ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hz : r = 0 := by
    apply q_eq_zero_of_all_coefficients_zero
    intro i
    have hh := (K.mem_orthogonal r).mp ho (coefficientProbe (i + 1)) (hp (i + 1))
    rw [coefficientProbe_inner] at hh
    exact hh
  have he : x = K.starProjection x := sub_eq_zero.mp hz
  rw [he]
  exact K.starProjection_apply_mem x
theorem triangular_projection_tendsto (x : QHilbert) :
    Tendsto (fun n => (walkSpan riesz id n).starProjection x)
      atTop (𝓝 x) := by
  have ht := walkProjection_tendsto riesz id Function.surjective_id x
  have he : (⊤ : Submodule ℝ QHilbert).starProjection x = x :=
    Submodule.starProjection_eq_self_iff.mpr (by trivial)
  simpa only [triangular_dictionaryClosure_eq_top, he] using ht
end RiemannResearch.RH.QTriangularCharge
