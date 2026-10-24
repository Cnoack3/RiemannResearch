/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GeometricHeadSelection
import RiemannResearch.Analysis.QuantitativeBlockAverages
import RiemannResearch.Analysis.BoundedMomentAverages
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import RiemannResearch.Analysis.SignedEnergyAverages
import RiemannResearch.RH.ParetoExactHeadPairings

/-!
# Executable exact-head selection with reciprocal-energy averaging

Source: user-provided `RH_Averaging_Limit_Research_Agenda_2026-10-24`,
Priority 3. The existing online selector supplies complete pairings for
inverse-energy scaled residuals without any uniform bound on the original
energies. Divergence of reciprocal-energy mass along the selected heads
remains an explicit arithmetic hypothesis.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto

open RiemannResearch.Analysis

/-- The online selector controls weighted complete mixed sums automatically.
The selected individual energy certificates may grow without bound. -/
theorem online_reciprocal_energy_prefixCross_le
    (r : ℕ → ThresholdHilbert) (U : ℕ → ℕ) (A : ℕ → ℝ)
    (hA : ∀ i, 1 ≤ A i)
    (henergy : ∀ i, ‖r (exactHeadSelection U i)‖ ^ 2 ≤ A i)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (r N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (r N) n = 0)
    (a m : ℕ) :
    prefixCross (fun i => (A (a + i))⁻¹ •
      r (exactHeadSelection U (a + i))) m ≤ (1 / 2 : ℝ) ^ a := by
  let v : ℕ → ThresholdHilbert := fun i => (A i)⁻¹ • r (exactHeadSelection U i)
  have hpos (i : ℕ) : 0 < A i := lt_of_lt_of_le zero_lt_one (hA i)
  have hinv (i : ℕ) : (A i)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (hpos i)).mpr (hA i)
  have hnorm (i : ℕ) : ‖v i‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    calc
      ‖v i‖ ^ 2 = ((A i)⁻¹) ^ 2 * ‖r (exactHeadSelection U i)‖ ^ 2 := by
        simp only [v, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      _ ≤ ((A i)⁻¹) ^ 2 * A i :=
        mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg _)
      _ = (A i)⁻¹ := by field_simp [ne_of_gt (hpos i)]
      _ ≤ (1 : ℝ) ^ 2 := by simpa using hinv i
  have hseq (i n : ℕ) : hilbertSequence (v i) n =
      (A i)⁻¹ * hilbertSequence (r (exactHeadSelection U i)) n := by
    change hilbertSequenceLinear ((A i)⁻¹ • r (exactHeadSelection U i)) n = _
    rw [map_smul]
    rfl
  have hvphysical (i n : ℕ) (hn : 0 < n) :
      |hilbertSequence (v i) n| ≤ (U (exactHeadSelection U i) : ℝ) := by
    rw [hseq, abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt (hpos i)))]
    calc
      _ ≤ (A i)⁻¹ * (U (exactHeadSelection U i) : ℝ) :=
        mul_le_mul_of_nonneg_left (hphysical _ n hn) (inv_nonneg.mpr (le_of_lt (hpos i)))
      _ ≤ 1 * (U (exactHeadSelection U i) : ℝ) :=
        mul_le_mul_of_nonneg_right (hinv i) (Nat.cast_nonneg _)
      _ = _ := one_mul _
  have hvhead (i n : ℕ) (hn : 0 < n) (hni : n ≤ exactHeadSelection U i) :
      hilbertSequence (v i) n = 0 := by
    rw [hseq, hhead _ n hn hni, mul_zero]
  have hp : ∀ i j, i < j →
      inner ℝ (v i) (v j) ≤ (1 : ℝ) * (1 / 2 : ℝ) ^ (j + 1) := by
    intro i j hij
    exact (le_abs_self _).trans
      (selected_exact_head_pairings v (exactHeadSelection U)
        (fun i => (U (exactHeadSelection U i) : ℝ)) 1 (by norm_num)
        (fun i => Nat.cast_nonneg _) hnorm hvphysical hvhead
        (fun _ _ h => exactHeadSelection_real_certificate U h) i j hij)
  have hc := prefixCross_shift_le_of_pairwise_geometric v 1 hp a m
  simp only [one_mul] at hc
  change prefixCross (fun i => v (a + i)) m ≤ (1 / 2 : ℝ) ^ a
  apply hc.trans
  have hfac : 1 - ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m ≤ 1 := by
    have hnonneg : 0 ≤ ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by positivity
    linarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ a)

/-- Prefix version of the complete signed cross bound. -/
theorem online_reciprocal_energy_prefixCross_le_one
    (r : ℕ → ThresholdHilbert) (U : ℕ → ℕ) (A : ℕ → ℝ)
    (hA : ∀ i, 1 ≤ A i)
    (henergy : ∀ i, ‖r (exactHeadSelection U i)‖ ^ 2 ≤ A i)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (r N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (r N) n = 0)
    (m : ℕ) :
    prefixCross (fun i => (A i)⁻¹ • r (exactHeadSelection U i)) m ≤ 1 := by
  simpa only [zero_add, pow_zero] using
    online_reciprocal_energy_prefixCross_le r U A hA henergy hphysical hhead 0 m

/-- An arbitrary weighted tail block has a complete error estimate. Its
original legal functions preserve the physical head at the block's first index. -/
theorem online_reciprocal_energy_block_bound
    (r : ℕ → ThresholdHilbert) (U : ℕ → ℕ) (A : ℕ → ℝ)
    (hA : ∀ i, 1 ≤ A i)
    (henergy : ∀ i, ‖r (exactHeadSelection U i)‖ ^ 2 ≤ A i)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (r N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (r N) n = 0)
    (a m : ℕ) :
    ‖((∑ i ∈ Finset.range m, (A (a + i))⁻¹)⁻¹) •
      (∑ i ∈ Finset.range m, (A (a + i))⁻¹ •
        r (exactHeadSelection U (a + i)))‖ ^ 2 ≤
      (∑ i ∈ Finset.range m, (A (a + i))⁻¹)⁻¹ +
        2 * (1 / 2 : ℝ) ^ a *
          ((∑ i ∈ Finset.range m, (A (a + i))⁻¹)⁻¹) ^ 2 := by
  exact norm_sq_reciprocal_energy_average_le
    (fun i => r (exactHeadSelection U (a + i))) (fun i => A (a + i))
    (fun i => lt_of_lt_of_le zero_lt_one (hA (a + i)))
    (fun i => henergy (a + i)) m ((1 / 2 : ℝ) ^ a)
    (online_reciprocal_energy_prefixCross_le r U A hA henergy hphysical hhead a m)

/-- An actual complete-P bound without a global energy constant. The weights
are inverses of positive selected energy certificates. -/
theorem online_reciprocal_energy_average_bound
    (r : ℕ → ThresholdHilbert) (U : ℕ → ℕ) (A : ℕ → ℝ)
    (hA : ∀ i, 1 ≤ A i)
    (henergy : ∀ i, ‖r (exactHeadSelection U i)‖ ^ 2 ≤ A i)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (r N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (r N) n = 0)
    (m : ℕ) :
    ‖((∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹) •
      (∑ i ∈ Finset.range m, (A i)⁻¹ • r (exactHeadSelection U i))‖ ^ 2 ≤
      (∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹ +
        2 * ((∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹) ^ 2 := by
  simpa only [mul_one] using norm_sq_reciprocal_energy_average_le
    (fun i => r (exactHeadSelection U i)) A
    (fun i => lt_of_lt_of_le zero_lt_one (hA i)) henergy m 1
    (online_reciprocal_energy_prefixCross_le_one r U A hA henergy hphysical hhead m)

/-- Reciprocal-energy divergence is a sufficient arithmetic replacement for
a global energy bound. The selector is the existing explicit integer recurrence;
no search for small pairings or additional termination premise is used. -/
theorem online_reciprocal_energy_average_tendsto
    (r : ℕ → ThresholdHilbert) (U : ℕ → ℕ) (A : ℕ → ℝ)
    (hA : ∀ i, 1 ≤ A i)
    (henergy : ∀ i, ‖r (exactHeadSelection U i)‖ ^ 2 ≤ A i)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (r N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (r N) n = 0)
    (hmass : Tendsto (fun m : ℕ => ∑ i ∈ Finset.range m, (A i)⁻¹) atTop atTop) :
    Tendsto (fun m : ℕ => ((∑ i ∈ Finset.range m, (A i)⁻¹)⁻¹) •
      (∑ i ∈ Finset.range m, (A i)⁻¹ • r (exactHeadSelection U i)))
      atTop (𝓝 0) := by
  exact reciprocal_energy_average_tendsto (fun i => r (exactHeadSelection U i)) A
    (fun i => lt_of_lt_of_le zero_lt_one (hA i)) henergy 1
    (online_reciprocal_energy_prefixCross_le_one r U A hA henergy hphysical hhead) hmass

end RiemannResearch.RH.Pareto
