/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ReciprocalCellAbel
import RiemannResearch.RH.PowerCellMassSummation
import Mathlib.Tactic.FieldSimp

/-!
# The exact weighted power-cell envelope

Source: the discrete Q-witness refinement recorded in
`BurnolQWitnessRefinement20261018.md`, motivated by Burnol (2001),
arXiv:math/0103058v2. The proof uses the existing exact power-cell calculus.

This establishes the exact B(beta)/(2 beta - 1) envelope arising in the
actual Q dual norm, including genuine summability and the vanishing Abel
boundary. It does not assume a zeta zero or a Nyman--Beurling criterion.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.SpectralObstruction

open RiemannResearch.Analysis.ReciprocalCellAbel

def reciprocalPowerProfile (β : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (1 - 2 * β)

def weightedPowerCellMass (β : ℝ) (n : ℕ) : ℝ :=
  boundaryFactor (n + 1) * powerCellMass β 1 n

def reciprocalPowerEnvelope (β : ℝ) : ℝ :=
  ∑' n : ℕ, cellWeight n * reciprocalPowerProfile β n

theorem reciprocalPowerProfile_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ reciprocalPowerProfile β n := by
  exact Real.rpow_nonneg (by positivity) _

/-- Profile boundedness follows directly from positive cell masses. -/
theorem reciprocalPowerProfile_le_one (β : ℝ) (hβ : (1 / 2 : ℝ) < β) (N : ℕ) :
    reciprocalPowerProfile β N ≤ 1 := by
  have ha : 0 < 2 * β - 1 := by linarith
  have hid := powerCellMass_sum_range β 1 hβ (by norm_num) N
  rw [Real.one_rpow] at hid
  change (∑ n ∈ Finset.range N, powerCellMass β 1 n) =
    (1 - reciprocalPowerProfile β N) / (2 * β - 1) at hid
  have hsum : 0 ≤ ∑ n ∈ Finset.range N, powerCellMass β 1 n :=
    Finset.sum_nonneg (fun n hn => powerCellMass_nonneg β 1 (by norm_num) n)
  have hmul := (eq_div_iff ha.ne').mp hid
  nlinarith [mul_nonneg hsum ha.le]

theorem reciprocalPowerProfile_tendsto_zero (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    Tendsto (reciprocalPowerProfile β) atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (1 - 2 * β)) atTop (𝓝 0)
  have hx : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hh := (tendsto_rpow_neg_atTop (show 0 < 2 * β - 1 by linarith)).comp hx
  simpa only [Function.comp_def, reciprocalPowerProfile,
    show -(2 * β - 1) = 1 - 2 * β by ring] using hh

theorem reciprocalPowerProfile_boundary_tendsto_zero
    (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    Tendsto (fun N => boundaryFactor N * reciprocalPowerProfile β N) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun N => mul_nonneg (boundaryFactor_nonneg N) (reciprocalPowerProfile_nonneg β N))
    (fun N => ?_) (reciprocalPowerProfile_tendsto_zero β hβ)
  have hp := reciprocalPowerProfile_nonneg β N
  have hh := mul_nonneg (sub_nonneg.mpr (boundaryFactor_le_one N)) hp
  nlinarith

theorem cellWeight_eq_powerCellMass_one (n : ℕ) :
    cellWeight n = powerCellMass 1 1 n := by
  rw [powerCellMass_eq 1 1 (by norm_num) (by norm_num)]
  norm_num only [mul_one, one_mul, show (1 : ℝ) - 2 = -1 by norm_num,
    show (2 : ℝ) - 1 = 1 by norm_num, div_one, Real.rpow_neg_one]
  unfold cellWeight
  field_simp [show (n : ℝ) + 1 ≠ 0 by positivity,
    show (n : ℝ) + 2 ≠ 0 by positivity,
    show (n : ℝ) + 1 + 1 ≠ 0 by positivity]
  <;> ring

theorem reciprocalCellWeight_summable : Summable cellWeight := by
  have h := powerCellMass_summable 1 1 (by norm_num) (by norm_num)
  have hid : cellWeight = powerCellMass 1 1 := funext cellWeight_eq_powerCellMass_one
  rwa [← hid] at h

theorem reciprocalPowerEnvelope_summable (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    Summable (fun n => cellWeight n * reciprocalPowerProfile β n) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (cellWeight_nonneg n) (reciprocalPowerProfile_nonneg β n))
    (fun n => ?_) reciprocalCellWeight_summable
  have h := mul_le_mul_of_nonneg_left (reciprocalPowerProfile_le_one β hβ n)
    (cellWeight_nonneg n)
  simpa only [mul_one] using h

theorem weightedPowerCellMass_nonneg (β : ℝ) (n : ℕ) :
    0 ≤ weightedPowerCellMass β n := by
  exact mul_nonneg (boundaryFactor_nonneg _) (powerCellMass_nonneg β 1 (by norm_num) n)

theorem weightedPowerCellMass_le (β : ℝ) (n : ℕ) :
    weightedPowerCellMass β n ≤ powerCellMass β 1 n := by
  have hp := powerCellMass_nonneg β 1 (by norm_num) n
  have h := mul_nonneg (sub_nonneg.mpr (boundaryFactor_le_one (n + 1))) hp
  unfold weightedPowerCellMass
  nlinarith

theorem weightedPowerCellMass_summable (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    Summable (weightedPowerCellMass β) := by
  exact Summable.of_nonneg_of_le (weightedPowerCellMass_nonneg β)
    (weightedPowerCellMass_le β) (powerCellMass_summable β 1 hβ (by norm_num))

theorem weightedPowerCellMass_eq_cellDifference
    (β : ℝ) (hβ : (1 / 2 : ℝ) < β) (n : ℕ) :
    weightedPowerCellMass β n =
      cellDifference (reciprocalPowerProfile β) n / (2 * β - 1) := by
  rw [weightedPowerCellMass, powerCellMass_eq β 1 hβ (by norm_num)]
  simp only [cellDifference, reciprocalPowerProfile, Nat.cast_add, Nat.cast_one]
  ring

theorem reciprocalPowerProfile_cellDifference_summable
    (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    Summable (cellDifference (reciprocalPowerProfile β)) := by
  have ha : 2 * β - 1 ≠ 0 := by linarith
  have hs := (weightedPowerCellMass_summable β hβ).mul_left (2 * β - 1)
  have hid : (fun n => (2 * β - 1) * weightedPowerCellMass β n) =
      cellDifference (reciprocalPowerProfile β) := by
    funext n
    rw [weightedPowerCellMass_eq_cellDifference β hβ]
    field_simp [ha]
  rwa [hid] at hs

/-- The exact compressed-cell factor, with no residual boundary hypothesis. -/
theorem weightedPowerCellMass_tsum (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    (∑' n : ℕ, weightedPowerCellMass β n) =
      reciprocalPowerEnvelope β / (2 * β - 1) := by
  calc
    (∑' n : ℕ, weightedPowerCellMass β n) =
        ∑' n : ℕ, cellDifference (reciprocalPowerProfile β) n / (2 * β - 1) := by
      apply tsum_congr
      exact weightedPowerCellMass_eq_cellDifference β hβ
    _ = (∑' n : ℕ, cellDifference (reciprocalPowerProfile β) n) / (2 * β - 1) := by
      rw [tsum_div_const]
    _ = reciprocalPowerEnvelope β / (2 * β - 1) := by
      rw [tsum_cellDifference (reciprocalPowerProfile β)
        (reciprocalPowerProfile_cellDifference_summable β hβ)
        (reciprocalPowerEnvelope_summable β hβ)
        (reciprocalPowerProfile_boundary_tendsto_zero β hβ)]
      rfl

/-- The Abel coefficient is the conventional term `n^(-2 beta)/(n+1)`
after shifting the physical index from `n+1` to `n`. -/
theorem reciprocalPowerEnvelope_term_eq (β : ℝ) (n : ℕ) :
    cellWeight n * reciprocalPowerProfile β n =
      ((n : ℝ) + 1) ^ (-2 * β) / ((n : ℝ) + 2) := by
  unfold cellWeight reciprocalPowerProfile
  rw [show 1 - 2 * β = 1 + (-2 * β) by ring,
    Real.rpow_add (by positivity : 0 < (n : ℝ) + 1), Real.rpow_one]
  field_simp [show (n : ℝ) + 1 ≠ 0 by positivity,
    show (n : ℝ) + 2 ≠ 0 by positivity]
  <;> ring

theorem reciprocalPowerEnvelope_eq (β : ℝ) :
    reciprocalPowerEnvelope β =
      ∑' n : ℕ, ((n : ℝ) + 1) ^ (-2 * β) / ((n : ℝ) + 2) := by
  exact tsum_congr (reciprocalPowerEnvelope_term_eq β)

theorem reciprocalPowerEnvelope_conventional_summable
    (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 * β) / ((n : ℝ) + 2)) := by
  exact (reciprocalPowerEnvelope_summable β hβ).congr
    (reciprocalPowerEnvelope_term_eq β)

theorem reciprocalCellWeight_tsum : (∑' n : ℕ, cellWeight n) = 1 := by
  calc
    (∑' n : ℕ, cellWeight n) = ∑' n : ℕ, powerCellMass 1 1 n :=
      tsum_congr cellWeight_eq_powerCellMass_one
    _ = 1 := by
      rw [powerCellMass_tsum 1 1 (by norm_num) (by norm_num)]
      norm_num

/-- Keeping the first two positive terms gives a strict lower bound. -/
theorem reciprocalPowerEnvelope_two_term_lower
    (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    1 / 2 + (1 / 6) * (2 : ℝ) ^ (1 - 2 * β) ≤ reciprocalPowerEnvelope β := by
  have hh := Summable.sum_le_tsum ({0, 1} : Finset ℕ)
    (fun n hn => mul_nonneg (cellWeight_nonneg n) (reciprocalPowerProfile_nonneg β n))
    (reciprocalPowerEnvelope_summable β hβ)
  change (∑ n ∈ ({0, 1} : Finset ℕ), cellWeight n * reciprocalPowerProfile β n) ≤
    reciprocalPowerEnvelope β at hh
  norm_num [cellWeight, reciprocalPowerProfile] at hh
  exact hh

theorem reciprocalPowerEnvelope_half_lt
    (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    (1 / 2 : ℝ) < reciprocalPowerEnvelope β := by
  have h := reciprocalPowerEnvelope_two_term_lower β hβ
  have hp : 0 < (2 : ℝ) ^ (1 - 2 * β) := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith

theorem reciprocalPowerEnvelope_half_le
    (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    (1 / 2 : ℝ) ≤ reciprocalPowerEnvelope β :=
  (reciprocalPowerEnvelope_half_lt β hβ).le

theorem reciprocalPowerEnvelope_pos
    (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    0 < reciprocalPowerEnvelope β := by
  have h := reciprocalPowerEnvelope_half_lt β hβ
  linarith

/-- Retaining just the physical index two yields an explicit strict
improvement over the global Pareto-to-Q norm comparison. -/
theorem reciprocalPowerEnvelope_le_retained_gap
    (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    reciprocalPowerEnvelope β ≤ 1 - (1 - (2 : ℝ) ^ (1 - 2 * β)) / 6 := by
  let gap : ℕ → ℝ := fun n => cellWeight n - cellWeight n * reciprocalPowerProfile β n
  have hgap : Summable gap :=
    reciprocalCellWeight_summable.sub (reciprocalPowerEnvelope_summable β hβ)
  have hgap_nonneg (n : ℕ) : 0 ≤ gap n := by
    have h := mul_le_mul_of_nonneg_left (reciprocalPowerProfile_le_one β hβ n)
      (cellWeight_nonneg n)
    dsimp only [gap]
    nlinarith
  have hgap_sum : (∑' n : ℕ, gap n) = 1 - reciprocalPowerEnvelope β := by
    dsimp only [gap]
    rw [reciprocalCellWeight_summable.tsum_sub (reciprocalPowerEnvelope_summable β hβ),
      reciprocalCellWeight_tsum]
    rfl
  have hgap_one : gap 1 = (1 - (2 : ℝ) ^ (1 - 2 * β)) / 6 := by
    dsimp only [gap, cellWeight, reciprocalPowerProfile]
    norm_num
    ring
  have hh := Summable.sum_le_tsum ({1} : Finset ℕ)
    (fun n hn => hgap_nonneg n) hgap
  simp only [Finset.sum_singleton] at hh
  rw [hgap_sum, hgap_one] at hh
  linarith

theorem reciprocalPowerEnvelope_lt_one
    (β : ℝ) (hβ : (1 / 2 : ℝ) < β) :
    reciprocalPowerEnvelope β < 1 := by
  have h := reciprocalPowerEnvelope_le_retained_gap β hβ
  have hp : (2 : ℝ) ^ (1 - 2 * β) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

end RiemannResearch.RH.Pareto.SpectralObstruction
