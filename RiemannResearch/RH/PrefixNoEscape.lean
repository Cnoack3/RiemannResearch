/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrefixExpansion

/-! # Escape through the children of one prime prefix

When every fixed nonroot subtree mass tends to zero, the signed sum over the
children outside *any* fixed cutoff has explicit limit minus the local charge.
A local tightness hypothesis rules out this escape. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QPrimeSubtreeBudget
open Pareto ZetaTwoHilbert QSquarefreeDisplacementRigidity

/-- The immediate nonroot children visible through a conductor cutoff. -/
def childrenThrough (r H : ℕ) : Finset ℕ :=
  (Finset.Icc 2 H).filter (fun c => parent c = r)

/-- Signed mass of the immediate children visible at horizon H but past cutoff K. -/
def escapingChildMass (b : ℕ → ℝ) (r K H : ℕ) : ℝ :=
  ∑ c ∈ childrenThrough r H \ childrenThrough r K, subtree b H c

/-- Coordinate convergence to zero identifies exactly what escapes past every
fixed child cutoff. The limit can be nonzero. -/
theorem escapingChildMass_tendsto (b : ℕ → ℝ) (r K : ℕ) (hr : 2 ≤ r)
    (hnet : ∀ s : ℕ, 2 ≤ s → Tendsto (fun H : ℕ => subtree b H s) atTop (𝓝 0)) :
    Tendsto (escapingChildMass b r K) atTop (𝓝 (-(b r / (r : ℝ)))) := by
  classical
  have hnear : Tendsto (fun H : ℕ => ∑ c ∈ childrenThrough r K, subtree b H c)
      atTop (𝓝 0) := by
    simpa using (tendsto_finsetSum (childrenThrough r K)
      (fun c hc => hnet c (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1))
  have ht := ((hnet r hr).sub_const (b r / (r : ℝ))).sub hnear
  simp only [zero_sub, sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (max K r)] with H hH
  have hK : K ≤ H := (le_max_left _ _).trans hH
  have hrH : r ≤ H := (le_max_right _ _).trans hH
  have hsub : childrenThrough r K ⊆ childrenThrough r H := by
    intro c hc
    obtain ⟨hc', hp⟩ := Finset.mem_filter.mp hc
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hc'
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hlo, hhi.trans hK⟩, hp⟩
  have hs := Finset.sum_sdiff (f := fun c => subtree b H c) hsub
  have hc := subtree_eq_node_add_children b H r (Finset.mem_Icc.mpr ⟨hr, hrH⟩)
  change subtree b H r = b r / (r : ℝ) + ∑ c ∈ childrenThrough r H, subtree b H c at hc
  change (subtree b H r - b r / (r : ℝ)) -
    (∑ c ∈ childrenThrough r K, subtree b H c) =
      ∑ c ∈ childrenThrough r H \ childrenThrough r K, subtree b H c
  linarith

/-- At a given vertex, local tightness of the *signed* child sum suffices. -/
theorem charge_zero_of_no_escape (b : ℕ → ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hnet : ∀ s : ℕ, 2 ≤ s → Tendsto (fun H : ℕ => subtree b H s) atTop (𝓝 0))
    (hesc : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, r ≤ K ∧
      ∀ᶠ H : ℕ in atTop, |escapingChildMass b r K H| ≤ ε) : b r = 0 := by
  by_contra hb
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have ha := abs_pos.mpr (div_ne_zero hb hr')
  obtain ⟨K, _, hK⟩ := hesc (|b r / (r : ℝ)| / 2) (by linarith)
  have hle := le_of_tendsto (escapingChildMass_tendsto b r K hr hnet).abs hK
  rw [abs_neg] at hle
  linarith

/-- The local no-escape condition at every nonroot vertex, together with
vanishing of every fixed subtree, implies RH for the matched displacement. -/
theorem rh_of_no_escape
    (hnet : ∀ s : ℕ, 2 ≤ s →
      Tendsto (fun H : ℕ => subtree (charge displacement) H s) atTop (𝓝 0))
    (hesc : ∀ r : ℕ, 2 ≤ r → ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, r ≤ K ∧
      ∀ᶠ H : ℕ in atTop, |escapingChildMass (charge displacement) r K H| ≤ ε) :
    RiemannHypothesis := by
  have hz (r : ℕ) (hr : 2 ≤ r) : charge displacement r = 0 :=
    charge_zero_of_no_escape _ r hr hnet (hesc r hr)
  have hT (H r : ℕ) (hr : 2 ≤ r) : subtree (charge displacement) H r = 0 := by
    unfold subtree
    apply Finset.sum_eq_zero
    intro m _
    split_ifs with h
    · simp [hz m (hr.trans (prefix_bounds h).2)]
    · rfl
  apply rh_of_subtree_budget 1 0 (by norm_num) le_rfl
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro H
  apply le_of_eq
  unfold budget
  apply Finset.sum_eq_zero
  intro r hr
  simp [hT H r (Finset.mem_Icc.mp hr).1]

end RiemannResearch.RH.QPrimeSubtreeBudget
