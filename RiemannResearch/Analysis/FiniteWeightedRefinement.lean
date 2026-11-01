/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteWeightedPushforward
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
/-!
# Exact finite weighted refinement maps

Source: user-provided Cesàro weighted-CRT manuscript, 1 November 2026,
"Isometric pullback and its exact adjoint". The actual Q residue maps
consume these general identities. Arithmetic growth estimates are separate.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteWeightedRefinement
open FiniteWeightedPushforward
def pairing {ι : Type*} [Fintype ι] (w f g : ι → ℝ) : ℝ :=
  ∑ i, w i * f i * g i
def energy {ι : Type*} [Fintype ι] (w f : ι → ℝ) : ℝ :=
  ∑ i, w i * f i ^ 2
def average {α β : Type*} [Fintype β] [DecidableEq α]
    (w : β → ℝ) (π : β → α) (F : β → ℝ) (a : α) : ℝ :=
  pushWeight (fun b => w b * F b) π a / pushWeight w π a
theorem pullback_energy {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (w : β → ℝ) (π : β → α) (f : α → ℝ) :
    energy w (f ∘ π) = energy (pushWeight w π) f := by
  simpa only [energy, Function.comp_apply, tsum_fintype] using (integral_pushWeight w π ((hasSum_fintype w).summable) (fun a => f a ^ 2)).symm
theorem pullback_pairing {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (w : β → ℝ) (π : β → α) (f g : α → ℝ) :
    pairing w (f ∘ π) (g ∘ π) = pairing (pushWeight w π) f g := by
  simpa only [pairing, Function.comp_apply, mul_assoc, tsum_fintype] using
    (integral_pushWeight w π ((hasSum_fintype w).summable) (fun a => f a * g a)).symm
end RiemannResearch.Analysis.FiniteWeightedRefinement
