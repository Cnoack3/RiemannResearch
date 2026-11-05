/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeOrderedMobius
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeRoughBound
import RiemannResearch.RH.PrefixNoEscape

/-! # Reciprocal Möbius escape in the actual ordered prime tree

Source: Prime Trees, Carries and Zeta Zeros (5 November 2026), §7.2,
using the cofinite case of T. Tao's prime semigroup result.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
open RiemannResearch.RH.QPrimeSubtreeBudget

private theorem prefix_dvd {r m : ℕ} (h : r ∈ prefixes m) : r ∣ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [prefixes] at h
    split at h
    next hm =>
      rcases Finset.mem_insert.mp h with he | hp
      · rw [he]
      · exact (ih _ (parent_spec m hm).2.1 hp).trans (parent_spec m hm).2.2
    next hm => simp at h

private theorem ordered_weight_succ {r : ℕ} (hr : 2 ≤ r) (N : ℕ) :
    orderedSubtree r (N+1) = orderedSubtree r N +
      (if r ∈ prefixes (N+1) then (ArithmeticFunction.moebius (N+1) : ℝ) else 0) := by
  classical
  simp [orderedSubtree, Finset.sum_range_succ, show r ≠ 1 by omega]

private theorem rough_weight_succ (B : Finset ℕ) (N : ℕ) :
    roughSum B (N+1) = roughSum B N + coefficient B (N+1) := Finset.sum_range_succ _ _

/-- Exact reciprocal cylinder on every fixed squarefree nonroot vertex. -/
theorem mobius_subtree_eq_rough {r : ℕ} (hr : 2 ≤ r) (hs : Squarefree r) (N : ℕ) :
    subtree (fun m => (ArithmeticFunction.moebius m : ℝ)) N r =
      ((ArithmeticFunction.moebius r : ℝ)/(r : ℝ)) *
        roughReciprocal (forbiddenThroughRoot r) (N/r) := by
  classical
  let B := forbiddenThroughRoot r
  let μ (m : ℕ) : ℝ := ArithmeticFunction.moebius m
  have h0 : 0 < r := by omega
  have hR : (r : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
  have hc (n : ℕ) : orderedSubtree r n = μ r * roughSum B (n/r) :=
    (orderedSubtree_eq_cylinder hs n).trans (cylinder_eq_roughSum B (forbidden_spec hs).2 n)
  change subtree μ N r = (μ r / (r : ℝ))*roughReciprocal B (N/r)
  induction N with
  | zero => simp [subtree, roughReciprocal]
  | succ N ih =>
    have hstep : subtree μ (N+1) r = subtree μ N r +
        (if r ∈ prefixes (N+1) then μ (N+1) else 0) / ((N+1 : ℕ) : ℝ) := by
      rw [subtree, Finset.sum_Icc_succ_top (by omega)]
      change subtree μ N r + _ = _
      by_cases ht : r ∈ prefixes (N+1) <;> simp [ht]
    rw [hstep, ih]
    have hdif := ordered_weight_succ hr N
    rw [hc (N+1), hc N] at hdif
    change μ r * roughSum B ((N+1)/r) = μ r * roughSum B (N/r) +
      (if r ∈ prefixes (N+1) then μ (N+1) else 0) at hdif
    by_cases hd : r ∣ N+1
    · have hdiv := Nat.succ_div_of_dvd hd
      rw [hdiv, rough_weight_succ] at hdif
      have hv : (if r ∈ prefixes (N+1) then μ (N+1) else 0) =
          μ r * coefficient B (N/r+1) := by linarith
      have hm : ((N+1 : ℕ) : ℝ) = (r : ℝ) * ((N/r+1 : ℕ) : ℝ) := by
        exact_mod_cast (show N+1 = r*(N/r+1) by rw [← hdiv, Nat.mul_div_cancel' hd])
      have hrec : roughReciprocal B (N/r+1) = roughReciprocal B (N/r) +
          coefficient B (N/r+1) / ((N/r+1 : ℕ) : ℝ) := Finset.sum_range_succ _ _
      rw [hv, hdiv, hrec, hm]
      field_simp [hR]
      <;> ring
    · rw [Nat.succ_div_of_not_dvd hd] at hdif ⊢
      have hv : (if r ∈ prefixes (N+1) then μ (N+1) else 0) = 0 := by linarith
      rw [hv, zero_div, add_zero]

private theorem nonsquarefree_mobius_subtree {r : ℕ} (hr : ¬Squarefree r) (N : ℕ) :
    subtree (fun m => (ArithmeticFunction.moebius m : ℝ)) N r = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro m _
  split_ifs with h
  · have hm : ¬Squarefree m := fun hs => hr (hs.squarefree_of_dvd (prefix_dvd h))
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hm]
  · rfl

/-- Every fixed subtree tends to zero, including the squareful indices
which have no Möbius-supported descendants. -/
theorem mobius_subtree_tendsto (r : ℕ) (hr : 2 ≤ r) :
    Tendsto (fun H => subtree (fun m => (ArithmeticFunction.moebius m : ℝ)) H r) atTop (𝓝 0) := by
  by_cases hs : Squarefree r
  · have hdiv : Tendsto (fun H : ℕ => H/r) atTop atTop := by
      apply tendsto_atTop.2
      intro k
      filter_upwards [eventually_ge_atTop (k*r)] with H hH
      exact (Nat.le_div_iff_mul_le (by omega)).mpr hH
    have ht := ((roughReciprocal_tendsto _ (forbidden_spec hs).1).comp hdiv).const_mul
      ((ArithmeticFunction.moebius r : ℝ)/(r : ℝ))
    simpa only [Function.comp_def, mul_zero, mobius_subtree_eq_rough hr hs] using ht
  · simpa only [nonsquarefree_mobius_subtree hs] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem mobius_subtree_abs_le (r H : ℕ) (hr : 2 ≤ r) :
    |subtree (fun m => (ArithmeticFunction.moebius m : ℝ)) H r| ≤ 1/(r : ℝ) := by
  by_cases hs : Squarefree r
  · rw [mobius_subtree_eq_rough hr hs, abs_mul, abs_div,
      abs_of_nonneg (Nat.cast_nonneg r : 0 ≤ (r : ℝ))]
    have hmu : |(ArithmeticFunction.moebius r : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r)
    have ht := roughReciprocal_abs_le_one _ (forbidden_spec hs).1 (H/r)
    exact (mul_le_mul_of_nonneg_left ht (div_nonneg (abs_nonneg _) (Nat.cast_nonneg r))).trans
      (by simpa using div_le_div_of_nonneg_right hmu (Nat.cast_nonneg r))
  · rw [nonsquarefree_mobius_subtree hs, abs_zero]
    positivity

/-- The sharp counterexample to interchanging the child and horizon cutoffs. -/
theorem mobius_two_escaping_tendsto (K : ℕ) :
    Tendsto (escapingChildMass (fun m => (ArithmeticFunction.moebius m : ℝ)) 2 K)
      atTop (𝓝 (1/2 : ℝ)) := by
  have ht := escapingChildMass_tendsto (fun m => (ArithmeticFunction.moebius m : ℝ))
    2 K (by decide) mobius_subtree_tendsto
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two] at ht ⊢
  exact ht

/-- In the opposite order in (32), the escaping sum is identically zero
as soon as the child cutoff reaches the fixed physical horizon. -/
theorem escapingChildMass_eq_zero_of_horizon_le (b : ℕ → ℝ) (r K H : ℕ) (hHK : H ≤ K) :
    escapingChildMass b r K H = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro c hc
  obtain ⟨hH, hK⟩ := Finset.mem_sdiff.mp hc
  obtain ⟨hc', hp⟩ := Finset.mem_filter.mp hH
  obtain ⟨hl, hu⟩ := Finset.mem_Icc.mp hc'
  exact (hK (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hl,hu.trans hHK⟩,hp⟩)).elim

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
