/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteWeightedPushforward
import Mathlib.Tactic.Linarith
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
open FiniteWeightedPushforward
theorem average_pullback {α β : Type*} [Fintype β] [DecidableEq α]
    (w : β → ℝ) (π : β → α)
    (hm : ∀ a, pushWeight w π a ≠ 0) (f : α → ℝ) (a : α) :
    average w π (f ∘ π) a = f a := by
  have hn : pushWeight (fun b => w b * (f ∘ π) b) π a =
      pushWeight w π a * f a := by
    unfold pushWeight
    rw [← tsum_mul_right]
    apply tsum_congr
    intro b
    by_cases hb : π b = a <;> simp [Function.comp_apply, hb]
  unfold average
  rw [hn]
  field_simp [hm a]

theorem adjoint_identity {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (w : β → ℝ) (π : β → α) (hm : ∀ a, pushWeight w π a ≠ 0)
    (f : α → ℝ) (F : β → ℝ) :
    pairing w (f ∘ π) F = pairing (pushWeight w π) f (average w π F) := by
  have hi := integral_pushWeight (fun b => w b * F b) π
    ((hasSum_fintype (fun b => w b * F b)).summable) f
  rw [tsum_fintype] at hi
  calc
    _ = ∑ a, pushWeight (fun b => w b * F b) π a * f a := by
      rw [hi]
      unfold pairing
      apply Finset.sum_congr rfl
      intro b _
      simp only [Function.comp_apply]
      ring
    _ = _ := by
      unfold pairing
      apply Finset.sum_congr rfl
      intro a _
      unfold average
      field_simp [hm a]
open FiniteWeightedPushforward
theorem energy_sub_exact {ι : Type*} [Fintype ι] (w F P : ι → ℝ) :
    energy w (fun i => F i - P i) =
      energy w F + energy w P - 2 * pairing w P F := by
  unfold energy pairing
  calc
    _ = ∑ i, (w i * F i ^ 2 + w i * P i ^ 2 - 2 * (w i * P i * F i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
theorem pythagorean {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    (w : β → ℝ) (π : β → α) (hm : ∀ a, pushWeight w π a ≠ 0)
    (F : β → ℝ) :
    energy w F = energy (pushWeight w π) (average w π F) +
      energy w (fun b => F b - average w π F (π b)) := by
  have hi := adjoint_identity w π hm (average w π F) F
  have hself : pairing (pushWeight w π) (average w π F) (average w π F) =
      energy (pushWeight w π) (average w π F) := by
    unfold pairing energy
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hself] at hi
  have he := energy_sub_exact w F (average w π F ∘ π)
  rw [pullback_energy, hi] at he
  simp only [Function.comp_apply] at he
  linarith
open FiniteWeightedPushforward
theorem average_tower {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq γ] (w : β → ℝ) (π : β → α) (τ : α → γ)
    (hm : ∀ a, pushWeight w π a ≠ 0) (F : β → ℝ) :
    average (pushWeight w π) τ (average w π F) = average w (τ ∘ π) F := by
  have he : (fun a => pushWeight w π a * average w π F a) =
      pushWeight (fun b => w b * F b) π := by
    funext a
    unfold average
    field_simp [hm a]
  funext c
  change pushWeight (fun a => pushWeight w π a * average w π F a) τ c /
      pushWeight (pushWeight w π) τ c =
    pushWeight (fun b => w b * F b) (τ ∘ π) c / pushWeight w (τ ∘ π) c
  rw [he, pushWeight_comp _ π τ ((hasSum_fintype _).summable),
    pushWeight_comp _ π τ ((hasSum_fintype _).summable)]
end RiemannResearch.Analysis.FiniteWeightedRefinement
