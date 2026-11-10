/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryHorizontalBessel
import RiemannResearch.Analysis.ActualZeroOrdinate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field

/-! # The all-frequency positive horizontal budget obstruction

Source: the user's requested assumption audit of the Montgomery
horizontal transfer. This is an elementary deduction from the actual
multiplicity-indexed budget, not a new zero-density hypothesis.

For a fixed off-line zero with displacement d, the fixed frequency 1/d
makes its exponential factor exactly T. Its single copy therefore
prevents the normalized positive budget from vanishing. This audits
this sufficient positive-majorant route; it does not assert that every
possible signed raw-ordinate transfer requires the same hypothesis.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryHorizontalObstruction
open MontgomeryHorizontalBessel ActualZeroOrdinate

/-- A fixed off-line zero has a fixed Fourier frequency at which the positive
horizontal budget is bounded below after every sufficiently high cutoff. -/
theorem fixed_zero_budget_lower {ρ : ℂ} {T : ℝ}
    (hρ : ρ ∈ cutoff T) (hd : ρ.re - 1/2 ≠ 0) (hT : 4 ≤ T) :
    1 ≤ horizontalBudget T ((1/(ρ.re-1/2))*Real.log T) / T := by
  let i : Copies T := ⟨⟨ρ,hρ⟩, ⟨0,multiplicity_pos hρ⟩⟩
  have hh : ((Real.exp (((1/(ρ.re-1/2))*Real.log T)*(ρ.re-1/2))-1)^2 +
      (ρ.re-1/2)^2) ≤ horizontalBudget T ((1/(ρ.re-1/2))*Real.log T) := by
    let q : Copies T → ℝ := fun j =>
      (Real.exp (((1/(ρ.re-1/2))*Real.log T)*(j.1.1.re-1/2))-1)^2 +
        (j.1.1.re-1/2)^2
    have hq : q i ≤ ∑ j, q j :=
      Finset.single_le_sum (fun j _ => by dsimp [q]; positivity) (Finset.mem_univ i)
    simpa only [q,i,horizontalBudget] using hq
  have he : ((1/(ρ.re-1/2))*Real.log T)*(ρ.re-1/2) = Real.log T := by
    rw [one_div]
    calc
      _ = ((ρ.re-1/2) * (ρ.re-1/2)⁻¹) * Real.log T := by ring
      _ = _ := by rw [mul_inv_cancel₀ hd, one_mul]
  rw [he, Real.exp_log (by linarith : 0 < T)] at hh
  apply (le_div_iff₀ (by linarith : 0 < T)).mpr
  nlinarith [sq_nonneg (ρ.re-1/2)]

/-- The all-frequency positive-budget route cannot bypass the critical-line
assertion for any actual positive zero. This is an assumption audit. -/
theorem all_frequency_budget_vanishing_iff :
    (∀ α : ℝ, Tendsto
      (fun T => horizontalBudget T (α*Real.log T) / T) atTop (nhds 0)) ↔
      ∀ ρ : PositiveZero, ρ.1.re = 1/2 := by
  constructor
  · intro h ρ
    by_contra hn
    have hd : ρ.1.re-1/2 ≠ 0 := sub_ne_zero.mpr hn
    have hv := (h (1/(ρ.1.re-1/2))).eventually_lt_const (by norm_num : (0:ℝ)<1)
    obtain ⟨T,hT,hval⟩ := ((eventually_ge_atTop (max 4 ρ.1.im)).and hv).exists
    have hmem : ρ.1 ∈ cutoff T :=
      mem_cutoff_iff_zeta.mpr ⟨ρ.2.1,ρ.2.2,(le_max_right _ _).trans hT⟩
    have hl := fixed_zero_budget_lower hmem hd ((le_max_left _ _).trans hT)
    exact (not_lt_of_ge hl) hval
  · intro h α
    have hz (T : ℝ) : horizontalBudget T (α*Real.log T) = 0 := by
      unfold horizontalBudget
      apply Finset.sum_eq_zero
      intro i hi
      obtain ⟨hzi,hpi,_⟩ := mem_cutoff_iff_zeta.mp i.1.2
      have he := h ⟨i.1.1,hzi,hpi⟩
      change i.1.1.re = 1/2 at he
      rw [he]
      norm_num
    simp_rw [hz, zero_div]
    exact tendsto_const_nhds

end RiemannResearch.Analysis.MontgomeryHorizontalObstruction
