/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith

/-!
# Additive gain budgets with summable error

Source: user-provided signed-tail continuation agenda, 20 October 2026,
Priority 2. The concrete consumer is QRationalGainProvider. The finite
identities retain the terminal residual, and the lower provider is explicit.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.GainBudget

/-- A finite gain budget retains the terminal residual. -/
theorem finite_provider_budget
    {R a c e : ℕ → ℝ} {r : ℝ}
    (hc : ∀ j, 0 ≤ c j) (hr : ∀ j, r ≤ R j)
    (hprovider : ∀ j, c j * R j - e j ≤ a j)
    (hbudget : ∀ N, ∑ j ∈ Finset.range N, a j ≤ R 0 - R N)
    (N : ℕ) :
    r * (∑ j ∈ Finset.range N, c j) ≤
      R 0 - R N + ∑ j ∈ Finset.range N, e j := by
  have hpoint (j : ℕ) : r * c j ≤ a j + e j := by
    have hmul := mul_le_mul_of_nonneg_left (hr j) (hc j)
    nlinarith [hprovider j]
  have hs := Finset.sum_le_sum (fun j (_hj : j ∈ Finset.range N) => hpoint j)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  linarith [hbudget N]

/-- The same finite budget gives a quantitative terminal estimate, before
taking a limit. -/
theorem finite_provider_terminal_budget
    {R a c e : ℕ → ℝ}
    (hc : ∀ j, 0 ≤ c j) (hmono : Antitone R)
    (hprovider : ∀ j, c j * R j - e j ≤ a j)
    (hbudget : ∀ N, ∑ j ∈ Finset.range N, a j ≤ R 0 - R N)
    (N : ℕ) :
    (1 + ∑ j ∈ Finset.range N, c j) * R N ≤
      R 0 + ∑ j ∈ Finset.range N, e j := by
  have hpoint (j : ℕ) (hj : j ∈ Finset.range N) :
      R N * c j ≤ a j + e j := by
    have hRN := hmono (Nat.le_of_lt (Finset.mem_range.mp hj))
    have hmul := mul_le_mul_of_nonneg_left hRN (hc j)
    nlinarith [hprovider j]
  have hs := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hs
  nlinarith [hbudget N]

/-- A nonnegative scalar multiplying divergent partial sums cannot remain bounded. -/
theorem eq_zero_of_divergent_weighted_budget
    {c : ℕ → ℝ} {r B : ℝ} (hr : 0 ≤ r)
    (hdiv : Tendsto (fun N => ∑ j ∈ Finset.range N, c j) atTop atTop)
    (hbudget : ∀ N, r * (∑ j ∈ Finset.range N, c j) ≤ B) : r = 0 := by
  by_contra hne
  have hpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hne)
  obtain ⟨N, _, hN⟩ := exists_le_of_tendsto_atTop hdiv 0 (B / r + 1)
  have hstrict : B / r < ∑ j ∈ Finset.range N, c j := by linarith
  have hstrict' := (div_lt_iff₀ hpos).mp hstrict
  nlinarith [hbudget N]

/-- Conditional consumer: the lower estimate `hprovider` is the arithmetic obligation. -/
theorem lower_bound_eq_zero_of_provider
    {R a c e : ℕ → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hR : ∀ j, 0 ≤ R j)
    (hc : ∀ j, 0 ≤ c j) (he : ∀ j, 0 ≤ e j)
    (hr : ∀ j, r ≤ R j)
    (hprovider : ∀ j, c j * R j - e j ≤ a j)
    (hbudget : ∀ N, ∑ j ∈ Finset.range N, a j ≤ R 0 - R N)
    (hdiv : Tendsto (fun N => ∑ j ∈ Finset.range N, c j) atTop atTop)
    (hsum : Summable e) : r = 0 := by
  apply eq_zero_of_divergent_weighted_budget hr0 hdiv (B := R 0 + ∑' j, e j)
  intro N
  have hfinite := finite_provider_budget hc hr hprovider hbudget N
  have hecap : (∑ j ∈ Finset.range N, e j) ≤ ∑' j, e j :=
    Summable.sum_le_tsum (Finset.range N) (fun j _ => he j) hsum
  linarith [hR N]

/-- The monotone limit version keeps the provider hypothesis explicit. -/
theorem limit_eq_zero_of_provider
    {R a c e : ℕ → ℝ} {r : ℝ}
    (hR : ∀ j, 0 ≤ R j) (hmono : Antitone R)
    (hlim : Tendsto R atTop (𝓝 r))
    (hc : ∀ j, 0 ≤ c j) (he : ∀ j, 0 ≤ e j)
    (hprovider : ∀ j, c j * R j - e j ≤ a j)
    (hbudget : ∀ N, ∑ j ∈ Finset.range N, a j ≤ R 0 - R N)
    (hdiv : Tendsto (fun N => ∑ j ∈ Finset.range N, c j) atTop atTop)
    (hsum : Summable e) : r = 0 := by
  apply lower_bound_eq_zero_of_provider (ge_of_tendsto' hlim hR)
    hR hc he _ hprovider hbudget hdiv hsum
  intro j
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨j, fun n hn => hmono hn⟩)

end RiemannResearch.Analysis.GainBudget
