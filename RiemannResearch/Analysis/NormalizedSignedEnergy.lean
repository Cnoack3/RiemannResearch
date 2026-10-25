/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SignedEnergyAverages
import RiemannResearch.Analysis.QuantitativeBlockAverages
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The exact normalized signed correlation criterion

Source: the user-provided squarefree capacity and energy certificates note,
24 October 2026, research proposal 2. The diagonal tends to zero when
reciprocal certificate mass diverges. Consequently the complete signed cross
term, normalized by that mass squared, is the exact remaining obstruction.
No arithmetic control of that term or mass divergence is asserted here.
-/

open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def reciprocalEnergyDiagonal
    (u : ℕ → E) (A : ℕ → ℝ) (m : ℕ) : ℝ :=
  ((∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹) ^ 2 *
    ∑ i ∈ Finset.range m, ‖(A i)⁻¹ • u i‖ ^ 2

noncomputable def reciprocalEnergyCross
    (u : ℕ → E) (A : ℕ → ℝ) (m : ℕ) : ℝ :=
  2 * prefixCross (fun i => (A i)⁻¹ • u i) m *
    ((∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹) ^ 2

theorem reciprocalEnergyDiagonal_nonneg
    (u : ℕ → E) (A : ℕ → ℝ) (m : ℕ) :
    0 ≤ reciprocalEnergyDiagonal u A m := by
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem norm_sq_reciprocalEnergyAverage_exact
    (u : ℕ → E) (A : ℕ → ℝ) (m : ℕ) :
    ‖reciprocalEnergyAverage u A m‖ ^ 2 =
      reciprocalEnergyDiagonal u A m + reciprocalEnergyCross u A m := by
  unfold reciprocalEnergyAverage reciprocalEnergyDiagonal reciprocalEnergyCross
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_sq_sum_range_eq_diagonal_add_cross]
  ring

theorem reciprocalEnergyDiagonal_le_mass_inv
    (u : ℕ → E) (A : ℕ → ℝ) (hA : ∀ i, 0 < A i)
    (henergy : ∀ i, ‖u i‖ ^ 2 ≤ A i) (m : ℕ) :
    reciprocalEnergyDiagonal u A m ≤
      (∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹ := by
  let S : ℝ := ∑ i ∈ Finset.range m, (A i)⁻¹
  have hd (i : ℕ) : ‖(A i)⁻¹ • u i‖ ^ 2 ≤ (A i)⁻¹ := by
    calc
      _ = ((A i)⁻¹) ^ 2 * ‖u i‖ ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ ≤ ((A i)⁻¹) ^ 2 * A i :=
        mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg _)
      _ = _ := by field_simp [ne_of_gt (hA i)]
  have hdiag : (∑ i ∈ Finset.range m, ‖(A i)⁻¹ • u i‖ ^ 2) ≤ S :=
    Finset.sum_le_sum (fun i _ => hd i)
  change (S⁻¹)^2 * (∑ i ∈ Finset.range m, ‖(A i)⁻¹ • u i‖ ^ 2) ≤ S⁻¹
  calc
    _ ≤ (S⁻¹)^2 * S := mul_le_mul_of_nonneg_left hdiag (sq_nonneg _)
    _ = _ := by
      by_cases hS : S = 0
      · simp [hS]
      · field_simp [hS]

/-- A legal error floor forces positive aggregate signed correlations if
reciprocal mass is large. This is a lower bound on the actual cross term,
not a lower bound deduced from an upper energy certificate alone. -/
theorem reciprocalEnergyCross_ge_gap
    (u : ℕ → E) (A : ℕ → ℝ) (hA : ∀ i, 0 < A i)
    (henergy : ∀ i, ‖u i‖ ^ 2 ≤ A i) (m : ℕ) (δ : ℝ)
    (hfloor : δ ≤ ‖reciprocalEnergyAverage u A m‖ ^ 2) :
    δ - (∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹ ≤ reciprocalEnergyCross u A m := by
  have he := norm_sq_reciprocalEnergyAverage_exact u A m
  have hd := reciprocalEnergyDiagonal_le_mass_inv u A hA henergy m
  linarith

/-- Signed normalized cross budgets tending to zero suffice. In particular,
the unnormalized cross sum need not remain bounded. -/
theorem reciprocalEnergyAverage_tendsto_of_cross_budget
    (u : ℕ → E) (A : ℕ → ℝ) (hA : ∀ i, 0 < A i)
    (henergy : ∀ i, ‖u i‖ ^ 2 ≤ A i) (b : ℕ → ℝ)
    (hcross : ∀ᶠ m in atTop, reciprocalEnergyCross u A m ≤ b m)
    (hbudget : Tendsto b atTop (𝓝 0))
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop) :
    Tendsto (reciprocalEnergyAverage u A) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => (∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹)
      atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hmass
  apply tendsto_zero_of_norm_sq_le_budget _
    (fun m => (∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹ + b m)
  · filter_upwards [hcross] with m hm
    rw [norm_sq_reciprocalEnergyAverage_exact]
    exact add_le_add (reciprocalEnergyDiagonal_le_mass_inv u A hA henergy m) hm
  · simpa using hi.add hbudget

/-- With divergent reciprocal mass, strong convergence is equivalent to
vanishing normalized signed correlations, since the diagonal already vanishes. -/
theorem reciprocalEnergyAverage_tendsto_iff_cross
    (u : ℕ → E) (A : ℕ → ℝ) (hA : ∀ i, 0 < A i)
    (henergy : ∀ i, ‖u i‖ ^ 2 ≤ A i)
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop) :
    Tendsto (reciprocalEnergyAverage u A) atTop (𝓝 0) ↔
      Tendsto (reciprocalEnergyCross u A) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => (∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹)
      atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hmass
  have hd : Tendsto (reciprocalEnergyDiagonal u A) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hi
      (reciprocalEnergyDiagonal_nonneg u A)
      (reciprocalEnergyDiagonal_le_mass_inv u A hA henergy)
  constructor
  · intro hv
    have he : reciprocalEnergyCross u A = fun m =>
        ‖reciprocalEnergyAverage u A m‖ ^ 2 - reciprocalEnergyDiagonal u A m := by
      funext m
      linarith [norm_sq_reciprocalEnergyAverage_exact u A m]
    rw [he]
    simpa using (hv.norm.pow 2).sub hd
  · intro hx
    exact reciprocalEnergyAverage_tendsto_of_cross_budget u A hA henergy
      (reciprocalEnergyCross u A) (Filter.Eventually.of_forall fun _ => le_rfl) hx hmass

end RiemannResearch.Analysis
