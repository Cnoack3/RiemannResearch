/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Uniform oscillation within residue classes

Source: user-provided Full_Conductor_RH_Projection_Machinery.pdf, task D5
and Section 10.1 (6 November 2026), for the question and CRT terminology.
The elementary proofs below identify the fixed-modulus quantifier needed
for passing from finite periodic approximants to a limit.
The RH consumer is QFullCRTDisplacement.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ResidueOscillation

/-- A single bound for every pair of positive sites in the same residue class. -/
def Bound (f : ℕ → ℝ) (L : ℕ) (C : ℝ) : Prop :=
  ∀ n m : ℕ, 0 < n → 0 < m → n % L = m % L → |f n - f m| ≤ C

/-- Finite oscillation at one positive modulus already gives physical boundedness. -/
theorem exists_uniform_bound (f : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (C : ℝ) (h : Bound f L C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, |f n| ≤ D := by
  let S : ℝ := ∑ r ∈ Finset.range (2 * L), |f r|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨|f 0| + |C| + S, by positivity, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    linarith [abs_nonneg C]
  have hnp : 0 < n := Nat.pos_of_ne_zero hn
  let r := n % L + L
  have hrp : 0 < r := by dsimp [r]; omega
  have hrlt : r < 2 * L := by
    dsimp [r]
    have := Nat.mod_lt n hL
    omega
  have hmod : n % L = r % L := by simp [r, Nat.add_mod]
  have hd := h n r hnp hrp hmod
  have hr : |f r| ≤ S :=
    Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_range.mpr hrlt)
  have ht : |f n| ≤ |f n - f r| + |f r| := by
    simpa only [sub_add_cancel] using abs_add_le (f n - f r) (f r)
  linarith [le_abs_self C, abs_nonneg (f 0)]

/-- The modulus and bound must be fixed as the approximation index increases. -/
theorem bound_of_pointwise_limit (F : ℕ → ℕ → ℝ) (f : ℕ → ℝ)
    (L : ℕ) (C : ℝ) (hlim : ∀ n, Tendsto (fun j => F j n) atTop (𝓝 (f n)))
    (hb : ∀ᶠ j : ℕ in atTop, Bound (F j) L C) : Bound f L C := by
  intro n m hn hm hnm
  exact le_of_tendsto (((hlim n).sub (hlim m)).abs)
    (hb.mono (fun j hj => hj n m hn hm hnm))

/-- A uniform approximation error gives a CRT modulus; a Hilbert error alone does not. -/
theorem bound_of_uniform_approximation (f g : ℕ → ℝ) (L : ℕ) (ε : ℝ)
    (hg : ∀ n m, n % L = m % L → g n = g m)
    (he : ∀ n, |f n - g n| ≤ ε) : Bound f L (2 * ε) := by
  intro n m _ _ hnm
  have hsame := hg n m hnm
  have hrep : f n - f m = (f n - g n) - (f m - g m) := by rw [hsame]; ring
  rw [hrep]
  have ht := abs_sub_le (f n - g n) 0 (f m - g m)
  simp only [sub_zero, zero_sub, abs_neg] at ht
  exact ht.trans (by linarith [he n, he m])

/-- Only a cofinal physical head must be controlled at each stage.
The residue modulus and numerical bound remain fixed. -/
theorem bound_of_expanding_head_limit (F : ℕ → ℕ → ℝ) (f : ℕ → ℝ)
    (L : ℕ) (C : ℝ) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (hlim : ∀ n, Tendsto (fun j => F j n) atTop (𝓝 (f n)))
    (hb : ∀ j n m, 0 < n → 0 < m → n ≤ H j → m ≤ H j →
      n % L = m % L → |F j n - F j m| ≤ C) : Bound f L C := by
  intro n m hn hm hnm
  apply le_of_tendsto (((hlim n).sub (hlim m)).abs)
  filter_upwards [hH.eventually (eventually_ge_atTop n),
    hH.eventually (eventually_ge_atTop m)] with j hjn hjm
  exact hb j n m hn hm hjn hjm hnm

end RiemannResearch.Analysis.ResidueOscillation
