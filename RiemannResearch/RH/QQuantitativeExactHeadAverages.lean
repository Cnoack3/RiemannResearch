/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.QuantitativeBlockAverages
import RiemannResearch.RH.QExactHeadAverages

/-!
# Explicit quantitative Q averages with growing exact heads

Source: user-provided `RH_Constructive_Approximants_Research_Agenda_2026-10-24`,
Section 8, for the averaging construction. The block-offset improvement is
provided by `Analysis.QuantitativeBlockAverages`.

These are conditional research reductions in the actual complete Q Hilbert
space. The arithmetic provider of bounded exact heads and the geometric
pairwise estimate remain explicit hypotheses.
-/

open scoped BigOperators

namespace RiemannResearch.RH.QExactHeadAverages

open ZetaTwoHilbert
open RiemannResearch.Analysis

/-- Any selected block has the finite geometric error bound, without dropping
the signed cross terms before applying the stated pairwise estimates. -/
theorem shifted_average_error_le_of_pairwise_geometric
    (F : ℕ → QHilbert) (q : ℕ → ℕ) {B C : ℝ}
    (hbound : ∀ i, ‖qOne - F (q i)‖ ^ 2 ≤ B)
    (hcross : ∀ i j, i < j →
      inner ℝ (qOne - F (q i)) (qOne - F (q j)) ≤
        C * (1 / 2 : ℝ) ^ (j + 1))
    (a : ℕ) {m : ℕ} (hm : 0 < m) :
    ‖qOne - average F (fun i => q (a + i)) m‖ ^ 2 ≤
      B / m + 2 * C * (1 / 2 : ℝ) ^ a *
        (1 - ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m) / (m : ℝ) ^ 2 := by
  rw [residual_average F (fun i => q (a + i)) hm]
  exact norm_sq_block_average_le_of_pairwise_geometric
    (fun i => qOne - F (q i)) hbound hcross a hm

/-- The moving exact-head block enjoys an exponentially smaller mixed-term
budget than the initial average. No arithmetic uniform bound is inferred. -/
theorem blockAverage_error_le_of_pairwise_geometric
    (F : ℕ → QHilbert) (q : ℕ → ℕ) {B C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i, ‖qOne - F (q i)‖ ^ 2 ≤ B)
    (hcross : ∀ i j, i < j →
      inner ℝ (qOne - F (q i)) (qOne - F (q j)) ≤
        C * (1 / 2 : ℝ) ^ (j + 1))
    {m : ℕ} (hm : 0 < m) :
    ‖qOne - blockAverage F q m‖ ^ 2 ≤
      B / m + 2 * C * (1 / 2 : ℝ) ^ m / (m : ℝ) ^ 2 := by
  change ‖qOne - average F (fun i => q (m + i)) m‖ ^ 2 ≤ _
  rw [residual_average F (fun i => q (m + i)) hm]
  exact norm_sq_block_average_le_simple
    (fun i => qOne - F (q i)) hC hbound hcross m hm

/-- The block preserves the entire first selected physical head, not merely
the averaging length. Monotonicity of the selection is sufficient. -/
theorem blockAverage_head_through_first
    (F : ℕ → QHilbert) (q : ℕ → ℕ) (hq : Monotone q)
    (hhead : ∀ N k, 0 < k → k ≤ N → qSequence (F N) k = 1)
    {m k : ℕ} (hm : 0 < m) (hk : 0 < k) (hkm : k ≤ q m) :
    qSequence (blockAverage F q m) k = 1 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hv (i : ℕ) : qSequence (F (q (m + i))) k = 1 :=
    hhead _ _ hk (hkm.trans (hq (Nat.le_add_right m i)))
  change qSequenceLinear (((m : ℝ)⁻¹) •
    ∑ i ∈ Finset.range m, F (q (m + i))) k = 1
  simp only [map_smul, map_sum, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  change (m : ℝ)⁻¹ *
    (∑ i ∈ Finset.range m, qSequence (F (q (m + i))) k) = 1
  simp [hv, hm']

end RiemannResearch.RH.QExactHeadAverages
