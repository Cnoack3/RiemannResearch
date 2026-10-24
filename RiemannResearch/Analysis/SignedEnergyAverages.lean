/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.BoundedMomentAverages
import RiemannResearch.Analysis.QuantitativeBlockAverages
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Averaging with signed energy budgets and reciprocal-energy weights

Source: user-provided `RH_Averaging_Limit_Research_Agenda_2026-10-24`,
Priority 3, for the weaker signed block hypotheses. The reciprocal-energy
weights and their quantitative bound are derived here. No arithmetic energy
bound or reciprocal-energy divergence is asserted for a legal RH family.
-/

open Filter
open scoped Topology BigOperators

namespace RiemannResearch.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A complete signed energy budget suffices; no pointwise uniform bound on
individual residual norms is required. -/
theorem norm_sq_block_average_le_energy_budgets
    (u : ℕ → E) (a m : ℕ) (D X : ℝ)
    (hdiag : (∑ i ∈ Finset.range m, ‖u (a + i)‖ ^ 2) ≤ D)
    (hcross : prefixCross (fun i => u (a + i)) m ≤ X) :
    ‖((m : ℝ)⁻¹) • (∑ i ∈ Finset.range m, u (a + i))‖ ^ 2 ≤
      ((m : ℝ)⁻¹) ^ 2 * (D + 2 * X) := by
  rw [norm_sq_block_average_exact]
  exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)

omit [InnerProductSpace ℝ E] in
/-- A scalar upper bound on the squared norm tending to zero gives strong
convergence. The budget need not have a separately supplied positivity proof. -/
theorem tendsto_zero_of_norm_sq_le_budget
    (v : ℕ → E) (b : ℕ → ℝ)
    (hbound : ∀ᶠ m in atTop, ‖v m‖ ^ 2 ≤ b m)
    (hbudget : Tendsto b atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hb := hbudget.eventually
    (Metric.ball_mem_nhds (0 : ℝ) (sq_pos_of_pos hε))
  filter_upwards [hbound, hb] with m hm hbm
  have hsmall : |b m| < ε ^ 2 := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hbm
  rw [dist_zero_right]
  nlinarith [le_abs_self (b m), norm_nonneg (v m)]

/-- Moving blocks converge whenever their entire signed upper energy budget
vanishes after division by the square of their length. Signed cancellation
between the diagonal and mixed terms is retained in this formulation. -/
theorem block_average_tendsto_of_signed_budget
    (u : ℕ → E) (a : ℕ → ℕ) (D X : ℕ → ℝ)
    (hdiag : ∀ m, (∑ i ∈ Finset.range m, ‖u (a m + i)‖ ^ 2) ≤ D m)
    (hcross : ∀ m, prefixCross (fun i => u (a m + i)) m ≤ X m)
    (hbudget : Tendsto (fun m : ℕ => ((m : ℝ)⁻¹) ^ 2 * (D m + 2 * X m))
      atTop (𝓝 0)) :
    Tendsto (fun m : ℕ => ((m : ℝ)⁻¹) •
      (∑ i ∈ Finset.range m, u (a m + i))) atTop (𝓝 0) := by
  apply tendsto_zero_of_norm_sq_le_budget _ _ _ hbudget
  exact Filter.Eventually.of_forall fun m : ℕ =>
    norm_sq_block_average_le_energy_budgets u (a m) m (D m) (X m)
      (hdiag m) (hcross m)

/-- The familiar separate little-o conditions on diagonal and mixed budgets
are sufficient, but are stronger than the combined signed-budget hypothesis. -/
theorem block_average_tendsto_of_separate_budgets
    (u : ℕ → E) (a : ℕ → ℕ) (D X : ℕ → ℝ)
    (hdiag : ∀ m, (∑ i ∈ Finset.range m, ‖u (a m + i)‖ ^ 2) ≤ D m)
    (hcross : ∀ m, prefixCross (fun i => u (a m + i)) m ≤ X m)
    (hD : Tendsto (fun m : ℕ => ((m : ℝ)⁻¹) ^ 2 * D m) atTop (𝓝 0))
    (hX : Tendsto (fun m : ℕ => ((m : ℝ)⁻¹) ^ 2 * X m) atTop (𝓝 0)) :
    Tendsto (fun m : ℕ => ((m : ℝ)⁻¹) •
      (∑ i ∈ Finset.range m, u (a m + i))) atTop (𝓝 0) := by
  apply block_average_tendsto_of_signed_budget u a D X hdiag hcross
  have hh := hD.add (hX.const_mul 2)
  have he : (fun m : ℕ => ((m : ℝ)⁻¹) ^ 2 * (D m + 2 * X m)) =
      (fun m : ℕ => ((m : ℝ)⁻¹) ^ 2 * D m + 2 * (((m : ℝ)⁻¹) ^ 2 * X m)) := by
    funext m
    ring
  rw [he]
  simpa using hh

/-- Positive energy certificates permit inverse-energy weighting. A complete
signed cross bound for the weighted residuals is the only pairing input. -/
theorem norm_sq_reciprocal_energy_average_le
    (u : ℕ → E) (A : ℕ → ℝ) (hA : ∀ i, 0 < A i)
    (henergy : ∀ i, ‖u i‖ ^ 2 ≤ A i) (m : ℕ) (B : ℝ)
    (hcross : prefixCross (fun i => (A i)⁻¹ • u i) m ≤ B) :
    ‖((∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹) •
      (∑ i ∈ Finset.range m, (A i)⁻¹ • u i)‖ ^ 2 ≤
      (∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹ +
        2 * B * ((∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹) ^ 2 := by
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
  have hsum : ‖∑ i ∈ Finset.range m, (A i)⁻¹ • u i‖ ^ 2 ≤ S + 2 * B := by
    rw [norm_sq_sum_range_eq_diagonal_add_cross]
    linarith
  change ‖S⁻¹ • (∑ i ∈ Finset.range m, (A i)⁻¹ • u i)‖ ^ 2 ≤
    S⁻¹ + 2 * B * (S⁻¹) ^ 2
  calc
    _ = (S⁻¹) ^ 2 * ‖∑ i ∈ Finset.range m, (A i)⁻¹ • u i‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    _ ≤ (S⁻¹) ^ 2 * (S + 2 * B) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by
      by_cases hS : S = 0
      · simp [hS]
      · field_simp [hS]

/-- Reciprocal-energy mass tending to infinity forces weighted convergence,
provided the complete signed cross sums of the weighted vectors stay bounded.
No uniform bound on the unweighted individual energies is assumed. -/
theorem reciprocal_energy_average_tendsto
    (u : ℕ → E) (A : ℕ → ℝ) (hA : ∀ i, 0 < A i)
    (henergy : ∀ i, ‖u i‖ ^ 2 ≤ A i) (B : ℝ)
    (hcross : ∀ m, prefixCross (fun i => (A i)⁻¹ • u i) m ≤ B)
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop) :
    Tendsto (fun m : ℕ => ((∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹) •
      (∑ i ∈ Finset.range m, (A i)⁻¹ • u i)) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => (∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹)
      atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hmass
  apply tendsto_zero_of_norm_sq_le_budget _ _
    (Filter.Eventually.of_forall fun m : ℕ =>
      norm_sq_reciprocal_energy_average_le u A hA henergy m B (hcross m))
  simpa using hi.add ((hi.pow 2).const_mul (2 * B))

end RiemannResearch.Analysis

namespace RiemannResearch.Analysis

/-- Divergent reciprocal mass guarantees a finite tail endpoint for every
fixed starting index and target mass. No computational search is postulated
to terminate: termination follows from the displayed divergence hypothesis. -/
theorem exists_reciprocal_energy_tail_mass_ge
    (A : ℕ → ℝ)
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop)
    (a : ℕ) (L : ℝ) :
    ∃ m : ℕ, L ≤ ∑ i ∈ Finset.range m, (A (a + i))⁻¹ := by
  have hs : ∀ᶠ b : ℕ in atTop,
      L + (∑ i ∈ Finset.range a, (A i)⁻¹) ≤
        ∑ i ∈ Finset.range b, (A i)⁻¹ :=
    hmass.eventually (eventually_ge_atTop _)
  obtain ⟨b, hba, hb⟩ := ((eventually_ge_atTop a).and hs).exists
  have hsplit (m : ℕ) : (∑ i ∈ Finset.range (a + m), (A i)⁻¹) =
      (∑ i ∈ Finset.range a, (A i)⁻¹) +
        ∑ i ∈ Finset.range m, (A (a + i))⁻¹ := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Nat.add_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
        ring
  have he := hsplit (b - a)
  rw [Nat.add_sub_of_le hba] at he
  refine ⟨b - a, ?_⟩
  linarith

/-- The least certified tail length. For rational positive A this specifies a
finite sequential search using rational arithmetic. -/
noncomputable def reciprocalEnergyTailLength
    (A : ℕ → ℝ)
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop)
    (a : ℕ) (L : ℝ) : ℕ := by
  classical
  exact Nat.find (exists_reciprocal_energy_tail_mass_ge A hmass a L)

theorem reciprocalEnergyTailLength_spec
    (A : ℕ → ℝ)
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop)
    (a : ℕ) (L : ℝ) :
    L ≤ ∑ i ∈ Finset.range (reciprocalEnergyTailLength A hmass a L),
      (A (a + i))⁻¹ := by
  classical
  exact Nat.find_spec (exists_reciprocal_energy_tail_mass_ge A hmass a L)

theorem reciprocalEnergyTailLength_min
    (A : ℕ → ℝ)
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop)
    (a : ℕ) (L : ℝ) {m : ℕ}
    (hm : L ≤ ∑ i ∈ Finset.range m, (A (a + i))⁻¹) :
    reciprocalEnergyTailLength A hmass a L ≤ m := by
  classical
  exact Nat.find_min' (exists_reciprocal_energy_tail_mass_ge A hmass a L) hm

end RiemannResearch.Analysis

namespace RiemannResearch.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A normalized finite inverse-energy synthesis, defined also at length zero. -/
noncomputable def reciprocalEnergyAverage (F : ℕ → E) (A : ℕ → ℝ) (m : ℕ) : E :=
  (∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹ •
    ∑ i ∈ Finset.range m, (A i)⁻¹ • F i

/-- Positive energy certificates make the reciprocal mass nonzero on every
nonempty block, so the finite coefficients sum to one. -/
theorem reciprocalEnergyMass_pos (A : ℕ → ℝ) (hA : ∀ i, 0 < A i)
    {m : ℕ} (hm : 0 < m) :
    0 < ∑ i ∈ Finset.range m, (A i)⁻¹ := by
  apply Finset.sum_pos
  · intro i _
    exact inv_pos.mpr (hA i)
  · exact ⟨0, Finset.mem_range.mpr hm⟩

/-- Exact affine identity: normalized averaging commutes with subtraction of
a fixed target as soon as the reciprocal mass is nonzero. -/
theorem reciprocalEnergyAverage_sub (F : ℕ → E) (A : ℕ → ℝ) (x : E)
    (m : ℕ) (hmass : (∑ i ∈ Finset.range m, (A i)⁻¹) ≠ 0) :
    reciprocalEnergyAverage (fun i => F i - x) A m =
      reciprocalEnergyAverage F A m - x := by
  unfold reciprocalEnergyAverage
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  rw [smul_smul, inv_mul_cancel₀ hmass, one_smul]

/-- Every finite weighted synthesis remains in the given legal submodule. -/
theorem reciprocalEnergyAverage_mem (S : Submodule ℝ E) (F : ℕ → E)
    (A : ℕ → ℝ) (hF : ∀ i, F i ∈ S) (m : ℕ) :
    reciprocalEnergyAverage F A m ∈ S := by
  exact S.smul_mem _ (S.sum_mem fun i _ => S.smul_mem _ (hF i))

end RiemannResearch.Analysis
