/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A geometric orthogonal model with a positive affine cost floor

Source: the signed prime-head mixing attempt for the user's sparse power-cost
program, 17 October 2026. This concrete finite Gram model illustrates the
inverse-energy phenomenon of OrthogonalAffineSeries.lean.

The model diagonal is 4^(i+1), all cross entries are zero, and assigned
sparse heads are 16^(i+1). Diagonal energy divided by the head tends to zero,
yet every finite signed affine combination has energy at least three.
This refutes a generic geometric shortcut, not the actual squarefree
arithmetic provider.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.OrthogonalAffineCostObstruction

def modelEnergy (m : ℕ) (b : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, ((2 : ℝ) ^ (i + 1) * b i) ^ 2

theorem reciprocal_square_sum (m : ℕ) :
    (∑ i ∈ Finset.range m, ((1 / 2 : ℝ) ^ (i + 1)) ^ 2) =
      (1 - (1 / 4 : ℝ) ^ m) / 3 := by
  have he (i : ℕ) : ((1 / 2 : ℝ) ^ (i + 1)) ^ 2 = (1 / 4 : ℝ) ^ (i + 1) := by
    rw [pow_two, ← mul_pow]
    norm_num
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, he, pow_succ]
    ring

/-- Perfectly zero cross terms still do not make the affine cost vanish:
the diagonal energies grow geometrically and their reciprocal sum is finite. -/
theorem affine_cost_lower (m : ℕ) (b : ℕ → ℝ)
    (hb : ∑ i ∈ Finset.range m, b i = 1) :
    3 ≤ modelEnergy m b := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m)
    (fun i => (2 : ℝ) ^ (i + 1) * b i)
    (fun i => (1 / 2 : ℝ) ^ (i + 1))
  have hprod (i : ℕ) :
      ((2 : ℝ) ^ (i + 1) * b i) * (1 / 2 : ℝ) ^ (i + 1) = b i := by
    calc
      _ = ((2 : ℝ) * (1 / 2)) ^ (i + 1) * b i := by rw [mul_pow]; ring
      _ = _ := by norm_num
  simp_rw [hprod] at hc
  rw [hb] at hc
  have hw : (∑ i ∈ Finset.range m, ((1 / 2 : ℝ) ^ (i + 1)) ^ 2) ≤ 1 / 3 := by
    rw [reciprocal_square_sum]
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num) m]
  have hE : 0 ≤ modelEnergy m b := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hup := mul_le_mul_of_nonneg_left hw hE
  change (1 : ℝ) ^ 2 ≤ modelEnergy m b *
    (∑ i ∈ Finset.range m, ((1 / 2 : ℝ) ^ (i + 1)) ^ 2) at hc
  nlinarith


/-- The model's diagonal energies are sublinear in the assigned sparse heads. -/
theorem model_diagonal_sublinear :
    Tendsto (fun i : ℕ => ((2 : ℝ) ^ (i + 1)) ^ 2 / (16 : ℝ) ^ (i + 1))
      atTop (𝓝 0) := by
  have he (i : ℕ) :
      ((2 : ℝ) ^ (i + 1)) ^ 2 / (16 : ℝ) ^ (i + 1) =
        (1 / 4 : ℝ) ^ (i + 1) := by
    rw [pow_two, ← mul_pow, ← div_pow]
    norm_num
  simp_rw [he]
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).comp (tendsto_add_atTop_nat 1)

end RiemannResearch.Analysis.OrthogonalAffineCostObstruction
