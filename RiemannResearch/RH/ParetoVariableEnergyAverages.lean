/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GeometricHeadSelection
import RiemannResearch.Analysis.QuantitativeBlockAverages
import RiemannResearch.Analysis.BoundedMomentAverages
import RiemannResearch.RH.ParetoExactHeadPairings
import RiemannResearch.Analysis.SignedEnergyAverages
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact-head averaging with a varying diagonal energy

Source: user-provided RH averaging-limit agenda, 24 October 2026, Priority 3.
The existing executable selector controls the complete mixed terms without
any uniform norm bound. Only the energies of the current finite block enter.
No arithmetic growth bound on those block energies is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- The original selector bounds each pairing using the later vector's own
norm. There is no uniform complete-energy assumption. -/
theorem online_exact_head_pairing_variable
    (r : ℕ → ThresholdHilbert) (U : ℕ → ℕ)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (r N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (r N) n = 0)
    {i j : ℕ} (hij : i < j) :
    |inner ℝ (r (exactHeadSelection U i)) (r (exactHeadSelection U j))| ≤
      ‖r (exactHeadSelection U j)‖ * (1 / 2 : ℝ) ^ (j + 1) := by
  exact exact_head_pairing_le_geometric _ _ _ _ _ _
    (Nat.cast_nonneg _) (norm_nonneg _) (hphysical _) (hhead _) le_rfl
    (exactHeadSelection_real_certificate U hij)

/-- A block-local norm bound controls only the mixed term. The diagonal
sum is retained exactly, instead of replaced by m times a global bound. -/
theorem online_exact_head_block_diagonal_bound
    (r : ℕ → ThresholdHilbert) (U : ℕ → ℕ)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (r N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (r N) n = 0)
    (a m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ i < m, ‖r (exactHeadSelection U (a + i))‖ ≤ C) :
    ‖((m : ℝ)⁻¹) • ∑ i ∈ Finset.range m,
        r (exactHeadSelection U (a + i))‖ ^ 2 ≤
      ((m : ℝ)⁻¹) ^ 2 *
        ((∑ i ∈ Finset.range m, ‖r (exactHeadSelection U (a + i))‖ ^ 2) +
          2 * C * (1 / 2 : ℝ) ^ a) := by
  let u : ℕ → ThresholdHilbert := fun i =>
    if i < m then r (exactHeadSelection U (a + i)) else 0
  have hc : ∀ i j, i < j → inner ℝ (u i) (u j) ≤
      (C * (1 / 2 : ℝ) ^ a) * (1 / 2 : ℝ) ^ (j + 1) := by
    intro i j hij
    by_cases hj : j < m
    · have hi : i < m := hij.trans hj
      simp only [u, if_pos hi, if_pos hj]
      calc
        _ ≤ |inner ℝ (r (exactHeadSelection U (a + i)))
            (r (exactHeadSelection U (a + j)))| := le_abs_self _
        _ ≤ ‖r (exactHeadSelection U (a + j))‖ *
            (1 / 2 : ℝ) ^ (a + j + 1) :=
          online_exact_head_pairing_variable r U hphysical hhead (by omega)
        _ ≤ C * (1 / 2 : ℝ) ^ (a + j + 1) :=
          mul_le_mul_of_nonneg_right (hlocal j hj) (by positivity)
        _ = _ := by rw [show a + j + 1 = a + (j + 1) by omega, pow_add]; ring
    · simp only [u, if_neg hj, inner_zero_right]
      positivity
  have hp := prefixCross_shift_le_of_pairwise_geometric u
    (C * (1 / 2 : ℝ) ^ a) hc 0 m
  simp only [zero_add, pow_zero, mul_one] at hp
  have hfac : 1 - ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m ≤ 1 := by
    have : 0 ≤ ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m := by positivity
    linarith
  have hp' : prefixCross u m ≤ C * (1 / 2 : ℝ) ^ a :=
    hp.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hfac (by positivity : 0 ≤ C * (1 / 2 : ℝ) ^ a))
  have he : (∑ i ∈ Finset.range m, u i) =
      ∑ i ∈ Finset.range m, r (exactHeadSelection U (a + i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [u, if_pos (Finset.mem_range.mp hi)]
  have hd : (∑ i ∈ Finset.range m, ‖u i‖ ^ 2) =
      ∑ i ∈ Finset.range m, ‖r (exactHeadSelection U (a + i))‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [u, if_pos (Finset.mem_range.mp hi)]
  rw [← he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_sq_sum_range_eq_diagonal_add_cross, hd]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  linarith

/-- Complete diagonal energy of the selected finite block. -/
def selectedBlockEnergy (r : ℕ → ThresholdHilbert) (U : ℕ → ℕ) (a m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, ‖r (exactHeadSelection U (a + i))‖ ^ 2

/-- The block's own diagonal energy supplies its local bound. In particular,
subquadratic diagonal growth suffices without a global norm bound. -/
theorem online_exact_head_block_energy_bound
    (r : ℕ → ThresholdHilbert) (U : ℕ → ℕ)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (r N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (r N) n = 0)
    (a m : ℕ) :
    ‖((m : ℝ)⁻¹) • ∑ i ∈ Finset.range m,
        r (exactHeadSelection U (a + i))‖ ^ 2 ≤
      ((m : ℝ)⁻¹) ^ 2 * (selectedBlockEnergy r U a m +
        2 * Real.sqrt (selectedBlockEnergy r U a m) * (1 / 2 : ℝ) ^ a) := by
  apply online_exact_head_block_diagonal_bound r U hphysical hhead a m
    (Real.sqrt (selectedBlockEnergy r U a m)) (Real.sqrt_nonneg _)
  intro i hi
  have hE : 0 ≤ selectedBlockEnergy r U a m :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hE]
  exact Finset.single_le_sum
    (f := fun j => ‖r (exactHeadSelection U (a + j))‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr hi)

/-- The original online selector needs only subquadratic total diagonal
energy along the selected blocks. No additional mixed-term assumption remains. -/
theorem online_exact_head_block_tendsto_of_subquadratic_diagonal
    (r : ℕ → ThresholdHilbert) (U : ℕ → ℕ) (a : ℕ → ℕ)
    (hphysical : ∀ N n, 0 < n → |hilbertSequence (r N) n| ≤ (U N : ℝ))
    (hhead : ∀ N n, 0 < n → n ≤ N → hilbertSequence (r N) n = 0)
    (hdiag : Tendsto (fun m : ℕ => ((m : ℝ)⁻¹) ^ 2 *
      selectedBlockEnergy r U (a m) m) atTop (𝓝 0)) :
    Tendsto (fun m : ℕ => ((m : ℝ)⁻¹) • ∑ i ∈ Finset.range m,
      r (exactHeadSelection U (a m + i))) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => ((m : ℝ)⁻¹) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, zero_pow (by norm_num : 2 ≠ 0)] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have hb : Tendsto (fun m : ℕ =>
      3 * (((m : ℝ)⁻¹) ^ 2 * selectedBlockEnergy r U (a m) m) +
        2 * ((m : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using (hdiag.const_mul 3).add (hi.const_mul 2)
  apply tendsto_zero_of_norm_sq_le_budget _ _ _ hb
  apply Filter.Eventually.of_forall
  intro m
  have hE : 0 ≤ selectedBlockEnergy r U (a m) m :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs : Real.sqrt (selectedBlockEnergy r U (a m) m) ≤
      selectedBlockEnergy r U (a m) m + 1 := by
    nlinarith [Real.sq_sqrt hE,
      sq_nonneg (Real.sqrt (selectedBlockEnergy r U (a m) m) - 1)]
  have hg : (1 / 2 : ℝ) ^ (a m) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hcross : 2 * Real.sqrt (selectedBlockEnergy r U (a m) m) *
      (1 / 2 : ℝ) ^ (a m) ≤ 2 * (selectedBlockEnergy r U (a m) m + 1) := by
    calc
      _ ≤ 2 * Real.sqrt (selectedBlockEnergy r U (a m) m) * 1 :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ ≤ _ := by linarith
  calc
    _ ≤ ((m : ℝ)⁻¹) ^ 2 * (selectedBlockEnergy r U (a m) m +
        2 * Real.sqrt (selectedBlockEnergy r U (a m) m) * (1 / 2 : ℝ) ^ (a m)) :=
      online_exact_head_block_energy_bound r U hphysical hhead (a m) m
    _ ≤ ((m : ℝ)⁻¹) ^ 2 * (3 * selectedBlockEnergy r U (a m) m + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ = _ := by ring

end RiemannResearch.RH.Pareto
