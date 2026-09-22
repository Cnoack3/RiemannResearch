/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Contractive Neumann reconstruction with an exact finite remainder

Source: independently developed continuation of the user's Pareto first-head
projection-defect argument, 2026-09-22. No novelty is claimed.
The concrete consumer is RH/ParetoResidualDilation.
The finite identity needs no contraction; the norm and limit theorems retain
their explicit global squared-contraction hypotheses.
-/

open scoped BigOperators Topology
open Filter

namespace ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_neumann_reconstruction
    (A : E →L[ℝ] E) (x y : E) (hy : y = x - A x) (M : ℕ) :
    x - ∑ j ∈ Finset.range M, (A ^ j) y = (A ^ M) x := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hAy : (A ^ M) y = (A ^ M) x - (A ^ (M + 1)) x := by
        rw [hy, map_sub, pow_succ]
        rfl
      rw [Finset.sum_range_succ, hAy, ← ih]
      abel

theorem pow_norm_sq_le_of_sq_contraction
    (A : E →L[ℝ] E) (q : ℝ) (hq : 0 ≤ q)
    (hA : ∀ z : E, ‖A z‖ ^ 2 ≤ q * ‖z‖ ^ 2)
    (x : E) (M : ℕ) :
    ‖(A ^ M) x‖ ^ 2 ≤ q ^ M * ‖x‖ ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
      calc
        ‖(A ^ (M + 1)) x‖ ^ 2 = ‖A ((A ^ M) x)‖ ^ 2 := by
          rw [pow_succ' A M]
          rfl
        _ ≤ q * ‖(A ^ M) x‖ ^ 2 := hA _
        _ ≤ q * (q ^ M * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (M + 1) * ‖x‖ ^ 2 := by rw [pow_succ]; ring

theorem neumann_reconstruction_error_sq
    (A : E →L[ℝ] E) (q : ℝ) (hq : 0 ≤ q)
    (hA : ∀ z : E, ‖A z‖ ^ 2 ≤ q * ‖z‖ ^ 2)
    (x y : E) (hy : y = x - A x) (M : ℕ) :
    ‖x - ∑ j ∈ Finset.range M, (A ^ j) y‖ ^ 2 ≤ q ^ M * ‖x‖ ^ 2 := by
  rw [finite_neumann_reconstruction A x y hy M]
  exact pow_norm_sq_le_of_sq_contraction A q hq hA x M

theorem tendsto_neumann_reconstruction
    (A : E →L[ℝ] E) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hA : ∀ z : E, ‖A z‖ ^ 2 ≤ q * ‖z‖ ^ 2)
    (x y : E) (hy : y = x - A x) :
    Tendsto (fun M => ∑ j ∈ Finset.range M, (A ^ j) y) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hp : Tendsto (fun M : ℕ => q ^ M * ‖x‖ ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const (‖x‖ ^ 2)
  have he := (tendsto_order.mp hp).2 (ε ^ 2) (sq_pos_of_pos hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  have hb := neumann_reconstruction_error_sq A q hq hA x y hy n
  have hs := hN n hn
  nlinarith [norm_nonneg (x - ∑ j ∈ Finset.range n, (A ^ j) y)]
end ContinuousLinearMap
