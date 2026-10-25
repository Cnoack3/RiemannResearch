/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DensePrimeHeadSignedCriterion
import RiemannResearch.RH.ParetoAmplitudeCertificates
import RiemannResearch.RH.PrimeHeadRefinedCertificates
import RiemannResearch.RH.QPrimeBalancedExactHead
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.Analysis.NormalizedSignedEnergy
import RiemannResearch.Analysis.SignedEnergyAverages
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Localization of the harmonic signed cross term

Source: the user's request to prove the actual signed cross term tends to
zero, 25 October 2026. The elementary finite sums and Pareto tail bound
are developed here without an arithmetic correlation hypothesis.

The physical residual tends to zero at every fixed coordinate. Its first
K coordinates cost at most 9K/H_m², and its complete tail beyond m² costs
at most 9/H_m². The signed cross term differs from the remaining finite
physical energy by a quantity tending to zero. Vanishing of that finite
energy is still an open arithmetic input; the RH consumer is conditional.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QPrimeBalancedExactHead
open Pareto Pareto.AmplitudeCertificates

def harmonicMass (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ))⁻¹

def harmonicResidual (m n : ℕ) : ℝ :=
  (harmonicMass m)⁻¹ *
    ∑ j ∈ Finset.range m, (((j + 1 : ℕ) : ℝ))⁻¹ * nextPrimeResidual (j + 1) n

theorem harmonicMass_nonneg (m : ℕ) : 0 ≤ harmonicMass m := by
  exact Finset.sum_nonneg (fun j _ => by positivity)

theorem harmonicMass_pos (m : ℕ) (hm : 0 < m) : 0 < harmonicMass m := by
  have h := Finset.single_le_sum
    (s := Finset.range m) (f := fun j : ℕ => (((j + 1 : ℕ) : ℝ))⁻¹)
    (fun j _ => by positivity) (Finset.mem_range.mpr hm)
  norm_num at h
  simpa only [harmonicMass, Nat.cast_add, Nat.cast_one] using zero_lt_one.trans_le h

theorem harmonicMass_tendsto : Tendsto harmonicMass atTop atTop := by
  apply tendsto_atTop_mono (fun m => ?_) dense_linear_mass_tendsto
  rw [dense_linear_mass_eq]
  change (9 : ℝ)⁻¹ * harmonicMass m ≤ harmonicMass m
  have := harmonicMass_nonneg m
  norm_num
  linarith

theorem harmonicMass_inv_tendsto :
    Tendsto (fun m => (harmonicMass m)⁻¹) atTop (𝓝 (0 : ℝ)) :=
  tendsto_inv_atTop_zero.comp harmonicMass_tendsto

theorem nextPrimeResidual_abs_le_three_mul (N n : ℕ) (hN : 0 < N) :
    |nextPrimeResidual N n| ≤ 3 * (N : ℝ) := by
  have h := nextPrimeHead_amplitude N n hN
  have hanchor := anchorPrime_le_two_mul N hN
  have hc : ((N + anchorPrime N : ℕ) : ℝ) ≤ 3 * (N : ℝ) := by
    exact_mod_cast (show N + anchorPrime N ≤ 3 * N by omega)
  exact h.trans hc

theorem weighted_nextPrimeResidual_abs_le_three (j n : ℕ) :
    |(((j + 1 : ℕ) : ℝ))⁻¹ * nextPrimeResidual (j + 1) n| ≤ 3 := by
  have hN : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  calc
    |(((j + 1 : ℕ) : ℝ))⁻¹ * nextPrimeResidual (j + 1) n| =
        (((j + 1 : ℕ) : ℝ))⁻¹ * |nextPrimeResidual (j + 1) n| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hN)]
    _ ≤ (((j + 1 : ℕ) : ℝ))⁻¹ * (3 * ((j + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (nextPrimeResidual_abs_le_three_mul (j + 1) n (by omega)) (by positivity)
    _ = 3 := by field_simp

theorem weighted_nextPrimeResidual_prefix_abs_le (k n : ℕ) :
    |∑ j ∈ Finset.range k,
      (((j + 1 : ℕ) : ℝ))⁻¹ * nextPrimeResidual (j + 1) n| ≤ 3 * (k : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range k,
        |(((j + 1 : ℕ) : ℝ))⁻¹ * nextPrimeResidual (j + 1) n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, (3 : ℝ) :=
      Finset.sum_le_sum (fun j _ => weighted_nextPrimeResidual_abs_le_three j n)
    _ = 3 * (k : ℝ) := by simp; ring

theorem harmonicResidual_amplitude (m n : ℕ) :
    |harmonicResidual m n| ≤ 3 * (m : ℝ) * (harmonicMass m)⁻¹ := by
  rw [harmonicResidual, abs_mul, abs_of_nonneg (inv_nonneg.mpr (harmonicMass_nonneg m))]
  calc
    _ ≤ (harmonicMass m)⁻¹ * (3 * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left (weighted_nextPrimeResidual_prefix_abs_le m n)
        (inv_nonneg.mpr (harmonicMass_nonneg m))
    _ = _ := by ring

/-- For a positive physical coordinate, all terms whose head has reached it vanish. -/
theorem harmonicResidual_truncated (m n : ℕ) (hn : 0 < n) :
    harmonicResidual m n = (harmonicMass m)⁻¹ *
      ∑ j ∈ Finset.range (min m (n - 1)),
        (((j + 1 : ℕ) : ℝ))⁻¹ * nextPrimeResidual (j + 1) n := by
  unfold harmonicResidual
  congr 1
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.min_le_left m (n - 1)))
  intro j hj hjnot
  have hjm := Finset.mem_range.mp hj
  have hnot : ¬ j < min m (n - 1) := by simpa using hjnot
  have hnj : n ≤ j + 1 := by omega
  simp only [nextPrimeResidual, nextPrimeHead_exact (j + 1) n hn hnj,
    sub_self, mul_zero]

/-- An unconditional coordinate bound, independent of the outer averaging length. -/
theorem harmonicResidual_coordinate_bound (m n : ℕ) (hn : 0 < n) :
    |harmonicResidual m n| ≤ 3 * ((n - 1 : ℕ) : ℝ) * (harmonicMass m)⁻¹ := by
  rw [harmonicResidual_truncated m n hn, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (harmonicMass_nonneg m))]
  have hk : ((min m (n - 1) : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.min_le_right m (n - 1)
  calc
    _ ≤ (harmonicMass m)⁻¹ * (3 * ((min m (n - 1) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (weighted_nextPrimeResidual_prefix_abs_le (min m (n - 1)) n)
        (inv_nonneg.mpr (harmonicMass_nonneg m))
    _ ≤ (harmonicMass m)⁻¹ * (3 * ((n - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (inv_nonneg.mpr (harmonicMass_nonneg m))
    _ = _ := by ring

theorem harmonicResidual_pointwise_tendsto (n : ℕ) (hn : 0 < n) :
    Tendsto (fun m => harmonicResidual m n) atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero_norm
    (fun m => by simpa only [Real.norm_eq_abs] using harmonicResidual_coordinate_bound m n hn)
  simpa only [mul_zero] using
    harmonicMass_inv_tendsto.const_mul (3 * ((n - 1 : ℕ) : ℝ))

/-- The first K physical coordinates contribute at most 9K/H_m². -/
theorem harmonicResidual_head_le (m K : ℕ) :
    head (harmonicResidual m) K ≤ 9 * (K : ℝ) * ((harmonicMass m)⁻¹) ^ 2 := by
  have hH : 0 ≤ (harmonicMass m)⁻¹ := inv_nonneg.mpr (harmonicMass_nonneg m)
  unfold head
  calc
    _ ≤ ∑ _n ∈ Finset.range K, 9 * ((harmonicMass m)⁻¹) ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      have ha : |harmonicResidual m (n + 1)| ≤
          3 * (n : ℝ) * (harmonicMass m)⁻¹ := by
        simpa only [Nat.add_sub_cancel] using
          harmonicResidual_coordinate_bound m (n + 1) (by omega)
      have hs : (harmonicResidual m (n + 1)) ^ 2 ≤
          (3 * (n : ℝ) * (harmonicMass m)⁻¹) ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr ha
      have hw : paretoWeight n * (n : ℝ) ^ 2 ≤ 1 := by
        unfold paretoWeight
        rw [div_mul_eq_mul_div, one_mul]
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      calc
        _ ≤ paretoWeight n * (3 * (n : ℝ) * (harmonicMass m)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left hs (paretoWeight_pos n).le
        _ = (9 * ((harmonicMass m)⁻¹) ^ 2) * (paretoWeight n * (n : ℝ) ^ 2) := by ring
        _ ≤ 9 * ((harmonicMass m)⁻¹) ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hw
            (by positivity : 0 ≤ 9 * ((harmonicMass m)⁻¹) ^ 2)]
    _ = _ := by simp; ring


open RiemannResearch.Analysis

def harmonicResidualVector (m : ℕ) : ThresholdHilbert :=
  (harmonicMass m)⁻¹ • ∑ j ∈ Finset.range m,
    (((j + 1 : ℕ) : ℝ))⁻¹ • (paretoNextPrimeHead (j + 1) - hilbertOne)

theorem harmonicResidualVector_sequence (m n : ℕ) :
    hilbertSequence (harmonicResidualVector m) (n + 1) = harmonicResidual m (n + 1) := by
  change hilbertSequenceLinear (harmonicResidualVector m) (n + 1) = _
  unfold harmonicResidualVector harmonicResidual
  simp only [map_smul, map_sum, map_sub, Pi.smul_apply, Pi.sub_apply,
    Finset.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  change _ * (hilbertSequence (paretoNextPrimeHead (j + 1)) (n + 1) -
    hilbertSequence hilbertOne (n + 1)) = _
  rw [paretoNextPrimeHead_sequence, hilbertOne_sequence]
  simp only [zeroAnchor, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
  rfl

theorem harmonicResidual_energy_eq (m : ℕ) :
    energy (harmonicResidual m) = ‖harmonicResidualVector m‖ ^ 2 := by
  rw [hilbert_norm_sq]
  unfold energy
  apply tsum_congr
  intro n
  rw [← hilbertSequence_weighted_square, harmonicResidualVector_sequence]
  have hw : paretoWeight n = positiveWeight (n + 1) := by
    unfold paretoWeight positiveWeight
    push_cast
    ring
  rw [hw]

theorem harmonicResidualVector_eq_reciprocal (m : ℕ) :
    harmonicResidualVector m =
    reciprocalEnergyAverage (fun j => paretoNextPrimeHead (j + 1) - hilbertOne)
      (fun j => 9 * ((j + 1 : ℕ) : ℝ)) m := by
  unfold reciprocalEnergyAverage
  rw [dense_linear_mass_eq, mul_inv_rev, inv_inv]
  have hsum :
      (∑ j ∈ Finset.range m, (9 * ((j + 1 : ℕ) : ℝ))⁻¹ •
        (paretoNextPrimeHead (j + 1) - hilbertOne)) =
      (9 : ℝ)⁻¹ • (∑ j ∈ Finset.range m,
        (((j + 1 : ℕ) : ℝ))⁻¹ • (paretoNextPrimeHead (j + 1) - hilbertOne)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [smul_smul, mul_inv_rev, mul_comm]
  rw [hsum, smul_smul, mul_assoc,
    mul_inv_cancel₀ (by norm_num : (9 : ℝ) ≠ 0), mul_one]
  rfl

def harmonicCross (m : ℕ) : ℝ :=
  reciprocalEnergyCross (fun j => paretoNextPrimeHead (j + 1) - hilbertOne)
    (fun j => 9 * ((j + 1 : ℕ) : ℝ)) m

def harmonicDiagonal (m : ℕ) : ℝ :=
  reciprocalEnergyDiagonal (fun j => paretoNextPrimeHead (j + 1) - hilbertOne)
    (fun j => 9 * ((j + 1 : ℕ) : ℝ)) m

theorem harmonicResidual_energy_exact (m : ℕ) :
    energy (harmonicResidual m) = harmonicDiagonal m + harmonicCross m := by
  rw [harmonicResidual_energy_eq, harmonicResidualVector_eq_reciprocal]
  exact norm_sq_reciprocalEnergyAverage_exact _ _ _

theorem harmonicDiagonal_le (m : ℕ) :
    harmonicDiagonal m ≤ 9 * (harmonicMass m)⁻¹ :=
  dense_linear_diagonal_le m

theorem harmonicDiagonal_tendsto :
    Tendsto harmonicDiagonal atTop (𝓝 0) := by
  have hb : Tendsto (fun m => 9 * (harmonicMass m)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa using harmonicMass_inv_tendsto.const_mul 9
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun m => reciprocalEnergyDiagonal_nonneg _ _ m) harmonicDiagonal_le

theorem harmonicResidual_quadratic_tail_le (m : ℕ) :
    tail (harmonicResidual m) (m ^ 2) ≤ 9 * ((harmonicMass m)⁻¹) ^ 2 := by
  have hb : 0 ≤ 3 * (harmonicMass m)⁻¹ :=
    mul_nonneg (by norm_num) (inv_nonneg.mpr (harmonicMass_nonneg m))
  have h := quadratic_tail_le (harmonicResidual m) m
    (3 * (harmonicMass m)⁻¹) hb (fun n => by
      nlinarith [harmonicResidual_amplitude m (n + 1)])
  nlinarith

theorem harmonicResidual_quadratic_tail_tendsto :
    Tendsto (fun m => tail (harmonicResidual m) (m ^ 2)) atTop (𝓝 0) := by
  have hb : Tendsto (fun m => 9 * ((harmonicMass m)⁻¹) ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using (harmonicMass_inv_tendsto.pow 2).const_mul 9
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun m => tail_nonneg _ _) harmonicResidual_quadratic_tail_le

/-- The difference between the signed cross term and a finite nonnegative
physical energy is exactly the far tail minus the diagonal. -/
theorem harmonicCross_sub_quadratic_head_exact (m : ℕ) :
    harmonicCross m - head (harmonicResidual m) (m ^ 2) =
      tail (harmonicResidual m) (m ^ 2) - harmonicDiagonal m := by
  have he := head_add_tail_exact (harmonicResidual m)
    (3 * (m : ℝ) * (harmonicMass m)⁻¹)
    (mul_nonneg (by positivity) (inv_nonneg.mpr (harmonicMass_nonneg m)))
    (fun n => harmonicResidual_amplitude m (n + 1)) (m ^ 2)
  linarith [harmonicResidual_energy_exact m]

theorem harmonicCross_quadratic_head_bounds (m : ℕ) :
    head (harmonicResidual m) (m ^ 2) - 9 * (harmonicMass m)⁻¹ ≤ harmonicCross m ∧
    harmonicCross m ≤
      head (harmonicResidual m) (m ^ 2) + 9 * ((harmonicMass m)⁻¹) ^ 2 := by
  have he := harmonicCross_sub_quadratic_head_exact m
  have hd := harmonicDiagonal_le m
  have hdn : 0 ≤ harmonicDiagonal m := reciprocalEnergyDiagonal_nonneg _ _ _
  have ht := harmonicResidual_quadratic_tail_le m
  have htn := tail_nonneg (harmonicResidual m) (m ^ 2)
  constructor <;> linarith

/-- Unconditional: the infinite tail and the diagonal both disappear. -/
theorem harmonicCross_sub_quadratic_head_tendsto :
    Tendsto (fun m => harmonicCross m - head (harmonicResidual m) (m ^ 2))
      atTop (𝓝 0) := by
  simp_rw [harmonicCross_sub_quadratic_head_exact]
  simpa using harmonicResidual_quadratic_tail_tendsto.sub harmonicDiagonal_tendsto

/-- The remaining arithmetic condition is a growing finite physical window. -/
theorem harmonicCross_tendsto_iff_quadratic_head :
    Tendsto harmonicCross atTop (𝓝 0) ↔
    Tendsto (fun m => head (harmonicResidual m) (m ^ 2)) atTop (𝓝 0) := by
  have he := harmonicCross_sub_quadratic_head_tendsto
  constructor
  · intro hx
    have hh := hx.sub he
    simpa only [sub_sub_cancel, sub_zero] using hh
  · intro hh
    have hx := he.add hh
    simpa only [sub_add_cancel, add_zero] using hx

/-- Conditional RH consumer. The displayed finite-window limit is still open. -/
theorem riemannHypothesis_of_harmonic_quadratic_window
    (hwindow : Tendsto (fun m => head (harmonicResidual m) (m ^ 2))
      atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_dense_harmonic_cross_budget harmonicCross
    (Filter.Eventually.of_forall fun _ => le_rfl)
    (harmonicCross_tendsto_iff_quadratic_head.mpr hwindow)

/-- Identification with the actual harmonic average minus the target. -/
theorem harmonicResidualVector_eq_average_sub (m : ℕ) (hm : 0 < m) :
    harmonicResidualVector m =
      (harmonicMass m)⁻¹ • (∑ j ∈ Finset.range m,
        (((j + 1 : ℕ) : ℝ))⁻¹ • paretoNextPrimeHead (j + 1)) - hilbertOne := by
  rw [harmonicResidualVector_eq_reciprocal,
    reciprocalEnergyAverage_sub _ _ hilbertOne m
      (ne_of_gt (reciprocalEnergyMass_pos
        (fun j => 9 * ((j + 1 : ℕ) : ℝ)) (fun j => by positivity) hm)),
    dense_reciprocalEnergyAverage_eq_harmonic]
  rfl

theorem harmonicResidual_fixed_head_tendsto (K : ℕ) :
    Tendsto (fun m => head (harmonicResidual m) K) atTop (𝓝 0) := by
  have hb : Tendsto (fun m => 9 * (K : ℝ) * ((harmonicMass m)⁻¹) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (harmonicMass_inv_tendsto.pow 2).const_mul (9 * (K : ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun m => Finset.sum_nonneg fun n _ =>
      mul_nonneg (paretoWeight_pos n).le (sq_nonneg _))
    (fun m => harmonicResidual_head_le m K)

end RiemannResearch.RH.QPrimeBalancedExactHead
