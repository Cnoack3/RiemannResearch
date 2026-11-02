/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CesaroMeanEnergy
import RiemannResearch.RH.ConditionalMeanEnergy
import RiemannResearch.RH.ConditionalMeanTailNonattainment
import RiemannResearch.Analysis.LowerLogGrowthComparability
import Mathlib.Tactic.Linarith

/-!
# Exact finite-prefix energy and normalized lower logarithmic growth

Source: prior-chat finite-cutoff recovery handoff of 1 November 2026,
for the split and intended tail-budget reduction. The existing finite-prefix
definition is moved here from MultiRangeCertificateConvergence without
changing its meaning. Summability is explicit in every infinite split.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID
open RiemannResearch.Analysis.SubpolynomialWindow

/-- The signed arithmetic candidate is fixed before squaring its conditional means. -/
def conditionalMeanPrefix (F : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, conditionalWeight k * (cesaro F (k + 1)) ^ 2

theorem conditionalMeanPrefix_nonneg (g : ℕ → ℝ) (N : ℕ) :
    0 ≤ conditionalMeanPrefix g N :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (conditionalWeight_pos _).le (sq_nonneg _))

theorem conditionalMeanSquare_eq_prefix_add_tail (g : ℕ → ℝ) (N : ℕ)
    (hg : Summable (fun k : ℕ => conditionalWeight k * cesaro g (k + 1) ^ 2)) :
    conditionalMeanSquare g =
      conditionalMeanPrefix g N + conditionalMeanTailSquare N g := by
  exact (hg.sum_add_tsum_nat_add N).symm

theorem conditionalMeanPrefix_le (g : ℕ → ℝ) (N : ℕ)
    (hg : Summable (fun k : ℕ => conditionalWeight k * cesaro g (k + 1) ^ 2)) :
    conditionalMeanPrefix g N ≤ conditionalMeanSquare g := by
  rw [conditionalMeanSquare_eq_prefix_add_tail g N hg]
  exact le_add_of_nonneg_right (conditionalMeanTailSquare_nonneg N g)

/-- A fixed normalized tail budget preserves zero lower logarithmic growth
when the exact complete energy is replaced by its finite prefix. -/
theorem normalized_lowerLogGrowth_zero_iff_finitePrefix
    (g : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (H c : ℕ → ℝ) (K : ℝ)
    (hH : Tendsto H atTop atTop)
    (hg : ∀ j, Summable (fun k : ℕ => conditionalWeight k * cesaro (g j) (k + 1) ^ 2))
    (htail : ∀ᶠ j in atTop, conditionalMeanTailSquare (N j) (g j) / |c j| ^ 2 ≤ K) :
    lowerLogGrowth (fun j => conditionalMeanSquare (g j) / |c j| ^ 2) H = 0 ↔
      lowerLogGrowth (fun j => conditionalMeanPrefix (g j) (N j) / |c j| ^ 2) H = 0 := by
  have hfull : ∀ j, 0 ≤ conditionalMeanSquare (g j) / |c j| ^ 2 :=
    fun j => div_nonneg (conditionalMeanSquare_nonneg _) (sq_nonneg _)
  have hprefix : ∀ j, 0 ≤ conditionalMeanPrefix (g j) (N j) / |c j| ^ 2 :=
    fun j => div_nonneg (conditionalMeanPrefix_nonneg _ _) (sq_nonneg _)
  constructor
  · intro hzero
    apply lowerLogGrowth_eq_zero_of_eventually_le_mul _ _ H 1 hH hprefix hfull ?_ hzero
    exact Filter.Eventually.of_forall (fun j => by
      simpa only [one_mul] using div_le_div_of_nonneg_right
        (conditionalMeanPrefix_le (g j) (N j) (hg j)) (sq_nonneg |c j|))
  · intro hzero
    apply lowerLogGrowth_eq_zero_of_eventually_le_add_mul _ _ H K 1 hH hfull hprefix ?_ hzero
    filter_upwards [htail] with j hj
    rw [conditionalMeanSquare_eq_prefix_add_tail (g j) (N j) (hg j), add_div]
    linarith

end RiemannResearch.RH.Pareto
