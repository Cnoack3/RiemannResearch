/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteWeightedVariance
import RiemannResearch.RH.QSquarefreePrefixAbel
import RiemannResearch.RH.QSquarefreeShortHeadResponse
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact Abel dispersion for canonical squarefree short-head responses

Source: the user-requested continuation of `SquarefreeShortHeadLean20261031.md`.
The finite weighted-variance identity is standard; its actual prefix application
keeps the endpoint and all signed prefix values. Its RH consumer is
`QSquarefreePrefixCriterion`. The uniform arithmetic estimate remains Open.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreePrefixAbel
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeShortHeadResponse
open RiemannResearch.Analysis.FiniteWeightedVariance

/-- Positive Abel weights on the H interior prefixes plus the retained endpoint. -/
def abelWeight (H n i : ℕ) : ℝ :=
  if i < H then 1 / ((i : ℝ) + 3)
  else ((H : ℝ) + 1) * (1 / ((H : ℝ) + 2) - 1 / ((n : ℝ) + 1))

/-- Actual normalized signed prefixes; the last entry records the endpoint. -/
def abelValue (N H n i : ℕ) : ℝ :=
  if i < H then prefixResponse N n (i + 1) / ((i : ℝ) + 2)
  else prefixResponse N n H / ((H : ℝ) + 1)

def abelMass (H n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (H + 1), abelWeight H n i

def abelEnergy (N H n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (H + 1), abelWeight H n i * abelValue N H n i ^ 2

/-- The exact dispersion discarded by weighted Cauchy--Schwarz. -/
def abelDispersion (N H n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range (H + 1), ∑ j ∈ Finset.range (H + 1),
    abelWeight H n i * abelWeight H n j *
      (abelValue N H n i - abelValue N H n j) ^ 2) / 2

theorem response_eq_abel_moment (N H n : ℕ) :
    response N H n =
      ∑ i ∈ Finset.range (H + 1), abelWeight H n i * abelValue N H n i := by
  rw [Finset.sum_range_succ, response_abel_exact]
  have hs : (∑ i ∈ Finset.range H, abelWeight H n i * abelValue N H n i) =
      ∑ i ∈ Finset.range H,
        prefixResponse N n (i + 1) / (((i : ℝ) + 2) * ((i : ℝ) + 3)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [abelWeight, abelValue, if_pos (Finset.mem_range.mp hi),
      div_eq_mul_inv, mul_inv]
    ring
  rw [hs]
  simp only [abelWeight, abelValue, lt_self_iff_false, if_false]
  have hH : (H : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem abelWeight_nonneg (H n i : ℕ) (hn : H < n) :
    0 ≤ abelWeight H n i := by
  unfold abelWeight
  split_ifs with hi
  · positivity
  · apply mul_nonneg (by positivity)
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    have hc : (H : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith

theorem response_energy_dispersion_exact (N H n : ℕ) :
    response N H n ^ 2 + abelDispersion N H n =
      abelMass H n * abelEnergy N H n := by
  rw [response_eq_abel_moment]
  exact pairwise_moment_exact (Finset.range (H + 1))
    (abelWeight H n) (abelValue N H n)

theorem abelDispersion_nonneg (N H n : ℕ) (hn : H < n) :
    0 ≤ abelDispersion N H n := by
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (mul_nonneg (abelWeight_nonneg H n i hn)
    (abelWeight_nonneg H n j hn)) (sq_nonneg _)

theorem response_sq_le_abel_energy (N H n : ℕ) (hn : H < n) :
    response N H n ^ 2 ≤ abelMass H n * abelEnergy N H n := by
  linarith [response_energy_dispersion_exact N H n, abelDispersion_nonneg N H n hn]

theorem abelMass_exact (H n : ℕ) :
    abelMass H n = (∑ i ∈ Finset.range H, 1 / ((i : ℝ) + 3)) +
      ((H : ℝ) + 1) / ((H : ℝ) + 2) - ((H : ℝ) + 1) / ((n : ℝ) + 1) := by
  unfold abelMass
  rw [Finset.sum_range_succ]
  have hs : (∑ i ∈ Finset.range H, abelWeight H n i) =
      ∑ i ∈ Finset.range H, 1 / ((i : ℝ) + 3) :=
    Finset.sum_congr rfl (fun i hi => by
      simp only [abelWeight, if_pos (Finset.mem_range.mp hi)])
  rw [hs]
  simp only [abelWeight, lt_self_iff_false, if_false]
  ring

theorem abelMass_le (H n : ℕ) :
    abelMass H n ≤ 1 + ∑ i ∈ Finset.range H, 1 / ((i : ℝ) + 3) := by
  rw [abelMass_exact]
  have hfrac : ((H : ℝ) + 1) / ((H : ℝ) + 2) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hnonneg : 0 ≤ ((H : ℝ) + 1) / ((n : ℝ) + 1) := by positivity
  linarith

/-- The complete block equality retains every pairwise prefix loss. -/
theorem block_energy_dispersion_exact (N H M : ℕ) :
    (∑ i ∈ Finset.range M, response N H (M + i + 1) ^ 2) +
      (∑ i ∈ Finset.range M, abelDispersion N H (M + i + 1)) =
    ∑ i ∈ Finset.range M, abelMass H (M + i + 1) * abelEnergy N H (M + i + 1) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i hi => response_energy_dispersion_exact N H (M + i + 1))

open QSquarefreeShortHeadResponse

/-- A single separated pair of actual normalized prefixes certifies strictly
positive Cauchy loss. This is a finite certificate, not an asymptotic estimate. -/
theorem abelDispersion_pos_of_pair (N H n i j : ℕ) (hn : H < n)
    (hi : i ∈ Finset.range (H + 1)) (hj : j ∈ Finset.range (H + 1))
    (hwi : 0 < abelWeight H n i) (hwj : 0 < abelWeight H n j)
    (hij : abelValue N H n i ≠ abelValue N H n j) :
    0 < abelDispersion N H n := by
  apply div_pos _ (by norm_num)
  apply Finset.sum_pos'
  · intro a ha
    exact Finset.sum_nonneg (fun b hb =>
      mul_nonneg (mul_nonneg (abelWeight_nonneg H n a hn)
        (abelWeight_nonneg H n b hn)) (sq_nonneg _))
  · refine ⟨i, hi, ?_⟩
    apply Finset.sum_pos'
    · intro b hb
      exact mul_nonneg (mul_nonneg hwi.le (abelWeight_nonneg H n b hn)) (sq_nonneg _)
    · exact ⟨j, hj, mul_pos (mul_pos hwi hwj) (sq_pos_of_ne_zero (sub_ne_zero.mpr hij))⟩

theorem response_sq_lt_abel_energy_of_pair (N H n i j : ℕ) (hn : H < n)
    (hi : i ∈ Finset.range (H + 1)) (hj : j ∈ Finset.range (H + 1))
    (hwi : 0 < abelWeight H n i) (hwj : 0 < abelWeight H n j)
    (hij : abelValue N H n i ≠ abelValue N H n j) :
    response N H n ^ 2 < abelMass H n * abelEnergy N H n := by
  linarith [response_energy_dispersion_exact N H n,
    abelDispersion_pos_of_pair N H n i j hn hi hj hwi hwj hij]
theorem compensated_le_exact_source_variance (N H n : ℕ) :
    abelMass H n * abelEnergy N H n - abelDispersion N H n ≤
      ‖QSquarefreeCorrectionKernel.kernel N n‖ ^ 2 *
        (QSquarefreeShortHeadResponse.variance N H n -
          ‖QSquarefreeShortHeadResponse.loss N H n‖ ^ 2) := by
  have he := response_energy_dispersion_exact N H n
  have hb := QSquarefreeShortHeadResponse.response_sq_le N H n
  linarith

end RiemannResearch.RH.QSquarefreePrefixAbel
