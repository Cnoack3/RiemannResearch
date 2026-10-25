/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GeometricHeadSelection
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Geometric head selection exhausts amplitude-derived reciprocal certificates

Source: the user's five-attempt squarefree-capacity agenda, 24 October 2026.
This independently derived obstruction concerns the crude certificates obtained
from a head-zero residual and a uniform physical amplitude. It says nothing
about summability of the reciprocals of the actual residual energies.
The prime-balanced arithmetic family has amplitude U(N) = N + anchorPrime N,
which satisfies the displayed linear lower bound on U.
-/

noncomputable section

namespace RiemannResearch.Analysis

/-- The complete Pareto energy certificate furnished by amplitude and exact head. -/
def selectedAmplitudeTailCertificate (U : ℕ → ℕ) (j : ℕ) : ℝ :=
  (U (exactHeadSelection U j) : ℝ) ^ 2 /
    ((exactHeadSelection U j : ℝ) + 1)

theorem exactHeadSelection_ge_four_pow (U : ℕ → ℕ) (hU : 1 ≤ U 1) (j : ℕ) :
    (4 : ℝ) ^ j ≤ (exactHeadSelection U j : ℝ) := by
  cases j with
  | zero => simp
  | succ j =>
      have hd := exactHeadSelection_dominates_earlier_amplitude U
        (Nat.zero_lt_succ j)
      simp only [exactHeadSelection_zero] at hd
      have hdR : (4 : ℝ) ^ (j + 2) * (U 1 : ℝ) ^ 2 ≤
          (exactHeadSelection U (j + 1) : ℝ) := by
        exact_mod_cast hd
      have hUreal : (1 : ℝ) ≤ U 1 := by exact_mod_cast hU
      have hUsq : (1 : ℝ) ≤ (U 1 : ℝ) ^ 2 := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hUsq
        (by positivity : (0 : ℝ) ≤ 4 ^ (j + 2))
      rw [mul_one] at hh
      have hstep : (4 : ℝ) ^ (j + 1) ≤ (4 : ℝ) ^ (j + 2) := by
        calc
          (4 : ℝ) ^ (j + 1) ≤ (4 : ℝ) ^ (j + 1) * 4 := by
            have hp : (0 : ℝ) ≤ 4 ^ (j + 1) := by positivity
            nlinarith
          _ = (4 : ℝ) ^ (j + 2) := (pow_succ (4 : ℝ) (j + 1)).symm
      exact hstep.trans (hh.trans hdR)

theorem selectedAmplitudeTailCertificate_ge_head
    (U : ℕ → ℕ) (hU : ∀ N, 2 * N ≤ U N) (j : ℕ) :
    (exactHeadSelection U j : ℝ) ≤ selectedAmplitudeTailCertificate U j := by
  have hn : 1 ≤ exactHeadSelection U j := by
    simpa only [exactHeadSelection_zero] using
      (exactHeadSelection_strictMono U).monotone (Nat.zero_le j)
  have hnR : (1 : ℝ) ≤ exactHeadSelection U j := by exact_mod_cast hn
  have huR : 2 * (exactHeadSelection U j : ℝ) ≤
      (U (exactHeadSelection U j) : ℝ) := by
    exact_mod_cast hU (exactHeadSelection U j)
  have hs := mul_self_le_mul_self (by positivity :
    (0 : ℝ) ≤ 2 * (exactHeadSelection U j : ℝ)) huR
  unfold selectedAmplitudeTailCertificate
  apply (le_div_iff₀ (by positivity :
    (0 : ℝ) < (exactHeadSelection U j : ℝ) + 1)).2
  nlinarith [mul_nonneg (Nat.cast_nonneg (exactHeadSelection U j) :
    (0 : ℝ) ≤ exactHeadSelection U j) (sub_nonneg.mpr hnR)]

/-- These readily available certificates cannot provide divergent reciprocal
mass for the constructive averaging criterion. Actual energies may be smaller. -/
theorem selectedAmplitudeTailCertificate_reciprocal_summable
    (U : ℕ → ℕ) (hU : ∀ N, 2 * N ≤ U N) :
    Summable (fun j => (selectedAmplitudeTailCertificate U j)⁻¹) := by
  have hU1 : 1 ≤ U 1 := by have := hU 1; omega
  have hge (j : ℕ) : (4 : ℝ) ^ j ≤ selectedAmplitudeTailCertificate U j :=
    (exactHeadSelection_ge_four_pow U hU1 j).trans
      (selectedAmplitudeTailCertificate_ge_head U hU j)
  have hpos (j : ℕ) : 0 < selectedAmplitudeTailCertificate U j :=
    (pow_pos (by norm_num : (0 : ℝ) < 4) j).trans_le (hge j)
  have hbound (j : ℕ) : (selectedAmplitudeTailCertificate U j)⁻¹ ≤
      (1 / 4 : ℝ) ^ j := by
    calc
      _ ≤ ((4 : ℝ) ^ j)⁻¹ :=
        (inv_le_inv₀ (hpos j) (pow_pos (by norm_num) j)).2 (hge j)
      _ = (1 / 4 : ℝ) ^ j := by simp [one_div]
  exact Summable.of_nonneg_of_le (fun j => (inv_pos.mpr (hpos j)).le) hbound
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

end RiemannResearch.Analysis
