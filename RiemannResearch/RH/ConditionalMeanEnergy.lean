/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.MellinCesaroSummability
import RiemannResearch.RH.ThresholdLegalIntegrability

/-!
# Conditional-mean energy and exact-head averaging

Reusable definitions and summability facts separated from the zeta-obstruction
and RH criteria. These declarations preserve the exact conditional weights,
energy, and approximation error used by those applications.

Source: existing `ConditionalMeanRHBridge` and `ConditionalMeanHeadObstruction`
declarations, moved without changing their statements or proofs.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID ArithmeticCumulative

/-- Error in the weaker, exact conditional-mean Hilbert norm. -/
def conditionalMeanError (g : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, mixtureWeight (k + 1) * (1 - cesaro g (k + 1)) ^ 2

theorem conditionalMeanError_nonneg (g : ℕ → ℝ) : 0 ≤ conditionalMeanError g :=
  tsum_nonneg (fun k => mul_nonneg (mixtureWeight_nonneg _) (sq_nonneg _))

/-- The full conditional-mean squared norm, rather than the approximation error. -/
def conditionalMeanSquare (g : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, conditionalWeight k * (cesaro g (k + 1)) ^ 2

theorem conditionalMeanSquare_nonneg (g : ℕ → ℝ) : 0 ≤ conditionalMeanSquare g :=
  tsum_nonneg (fun k => mul_nonneg (conditionalWeight_pos k).le (sq_nonneg _))

/-- Averaging preserves a constant exact positive head. -/
theorem mean_eq_one_of_head (F : ℕ → ℂ) (N : ℕ) (hN : 0 < N)
    (hhead : ∀ n, 0 < n → n ≤ N → F n = 1) : mean F N = 1 := by
  have hp : partialSum F N = (N : ℂ) := by
    unfold partialSum
    calc
      _ = ∑ k ∈ Finset.range N, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hhead (k + 1) (Nat.succ_pos _) (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
      _ = _ := by simp
  rw [mean, hp, div_self (by exact_mod_cast ne_of_gt hN)]

theorem legal_conditionalMeanSquare_summable (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {g : ℕ → ℝ} (hg : g ∈ legalSeedSpan A) :
    Summable (fun k : ℕ => conditionalWeight k * (cesaro g (k + 1)) ^ 2) := by
  obtain ⟨B, hB⟩ := legalSeedSpan_bounded A hA hg
  have h := bounded_mean_energy_summable (fun n => (g n : ℂ)) B
    (fun n hn => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hB n)
  simpa only [mean_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

end RiemannResearch.RH.Pareto
