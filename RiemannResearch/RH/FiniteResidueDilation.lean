/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.FiniteDyadicDefect

/-!
# Exact finite two-scale identities for the full Pareto residual

Source: the user's finite dyadic residual argument and its exact square-term
completion, October 2026.

At stage k, finiteSpace k contains g₂,...,g_(k+1).
Doubling the conductor cutoff therefore gives stage 2*k+1.

The repository's hilbertDilation 2 is twice the unscaled floor dilation.
Consequently the unscaled operator is
  (1 / 2 : ℝ) • hilbertDilation 2.

The final identity retains the entire nonnegative square term.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.RH.ArithmeticCumulative

theorem projectionResidual_inner_dilation_one (k : ℕ) :
    inner ℝ (hilbertOne - projection (2 * k + 1))
        (hilbertDilation 2 (by omega) hilbertOne) =
      inner ℝ (hilbertOne - projection (2 * k + 1))
        (hilbertDilation 2 (by omega) (hilbertOne - projection k)) := by
  have hm :
      hilbertDilation 2 (by omega) (projection k) ∈
        finiteSpace (2 * k + 1) :=
    by
      have h := doubleDilation_mem_double
        ((finiteSpace k).starProjection_apply_mem hilbertOne)
      change hilbertDilation 2 (by omega) (projection k) ∈ finiteSpace (2 * k + 1) at h
      exact h
  have ho :
      inner ℝ (hilbertOne - projection (2 * k + 1))
        (hilbertDilation 2 (by omega) (projection k)) = 0 := by
    rw [real_inner_comm]
    exact ((finiteSpace (2 * k + 1)).mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal hilbertOne) _ hm
  have hd :
      hilbertDilation 2 (by omega) hilbertOne =
        hilbertDilation 2 (by omega) (hilbertOne - projection k) +
          hilbertDilation 2 (by omega) (projection k) := by
    change (hilbertDilationContinuous 2 (by omega)) hilbertOne =
      (hilbertDilationContinuous 2 (by omega))
          (hilbertOne - projection k) +
        (hilbertDilationContinuous 2 (by omega)) (projection k)
    rw [← map_add]
    congr 1
    abel
  rw [hd, inner_add_right, ho, add_zero]

theorem projectionResidual_first_cross (k : ℕ) :
    hilbertSequence (hilbertOne - projection (2 * k + 1)) 1 / 2 =
      energy (2 * k + 1) -
        inner ℝ (hilbertOne - projection (2 * k + 1))
          (hilbertDilation 2 (by omega) (hilbertOne - projection k)) / 2 := by
  have hOne : inner ℝ (hilbertOne - projection (2 * k + 1)) hilbertOne =
      energy (2 * k + 1) := by
    change inner ℝ (projectionResidual (2 * k + 1)) hilbertOne = energy (2 * k + 1)
    exact projectionResidual_inner_one (2 * k + 1)
  have h := congrArg
    (fun f => inner ℝ (hilbertOne - projection (2 * k + 1)) f)
    firstPoint_eq_dilation_difference
  rw [inner_paretoPoint, hilbertGibbsPhysical_eq,
    inner_sub_right, inner_smul_right, hOne,
    projectionResidual_inner_dilation_one] at h
  rw [show paretoWeight 0 = (1 / 2 : ℝ) by
    norm_num [paretoWeight]] at h
  change (1 / 2 : ℝ) *
      hilbertSequence (hilbertOne - projection (2 * k + 1)) 1 =
    energy (2 * k + 1) -
      (1 / 2 : ℝ) *
        inner ℝ (hilbertOne - projection (2 * k + 1))
          (hilbertDilation 2 _ (hilbertOne - projection k)) at h
  linarith

/-- Exact finite identity, including the full nonnegative square. -/
theorem projectionResidual_first_exact_dyadic (k : ℕ) :
    hilbertSequence (hilbertOne - projection (2 * k + 1)) 1 =
      energy (2 * k + 1) - energy k / 2 +
        ‖(hilbertOne - projection (2 * k + 1)) -
          (1 / 2 : ℝ) •
            hilbertDilation 2 (by omega) (hilbertOne - projection k)‖ ^ 2 := by
  have h := projectionResidual_first_cross k
  rw [norm_sub_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, hilbertDilation_norm_sq]
  change hilbertSequence (hilbertOne - projection (2 * k + 1)) 1 =
    energy (2 * k + 1) - energy k / 2 +
      (energy (2 * k + 1) -
        2 * ((1 / 2 : ℝ) *
          inner ℝ (hilbertOne - projection (2 * k + 1))
            (hilbertDilation 2 (by omega) (hilbertOne - projection k))) +
        |(1 / 2 : ℝ)| ^ 2 * (2 * energy k))
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

theorem projectionResidual_first_dyadic_lower (k : ℕ) :
    energy (2 * k + 1) - energy k / 2 ≤
      hilbertSequence (hilbertOne - projection (2 * k + 1)) 1 := by
  rw [projectionResidual_first_exact_dyadic]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RiemannResearch.RH.Pareto.CoefficientStabilization
