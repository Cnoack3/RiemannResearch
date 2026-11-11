/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.OddGapPrimeCorrelation
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.Field

/-! # Exact even-gap reduction at the variance scale

The odd raw prime pairs have a logarithmic bound. Their one-point terms
are retained exactly, instead of replacing a uniform o(N) by zero before
triangular averaging. The complete boundary correction is retained.

Source: the centered expansion in Montgomery--Soundararajan,
Primes in short intervals (2004), https://arxiv.org/abs/math/0409258,
equations (18)--(19). The finite parity reduction and bound below are
direct consequences of the repository's actual odd-gap estimate.
No even-gap asymptotic is assumed by the unconditional declarations.
-/

noncomputable section
open scoped BigOperators Topology
open Finset Filter
namespace RiemannResearch.Analysis.EvenGapPrimeReduction
open ShortIntervalVariance ShortIntervalBoundary OddGapPrimeCorrelation

def triangleWeight (H h : ℕ) : ℝ := (H - (h + 1) : ℕ)

def oddWeight (H : ℕ) : ℝ :=
  ∑ h ∈ range H, if (h + 1) % 2 = 1 then triangleWeight H h else 0

def oddRaw (N H : ℕ) : ℝ :=
  2 * ∑ h ∈ range H, if (h + 1) % 2 = 1 then
    triangleWeight H h * rawGapCorrelation N (h + 1) else 0

def evenSigned (N H : ℕ) : ℝ :=
  2 * ∑ h ∈ range H, if (h + 1) % 2 = 1 then 0 else
    triangleWeight H h * gapCorrelation centeredMangoldt N (h + 1)

/-- All odd-gap one-point means and their shifted endpoint differences. -/
def oddMean (N H : ℕ) : ℝ :=
  2 * ∑ h ∈ range H, if (h + 1) % 2 = 1 then
    triangleWeight H h *
      (2 * mangoldtMass N - N + mangoldtMassBoundary N (h + 1)) else 0

/-- The precise remaining even-gap target, including the complete endpoint correction. -/
def evenResidual (N H : ℕ) : ℝ :=
  evenSigned N H - oddMean N H + boundaryCorrection centeredMangoldt N H +
    (H : ℝ) * N * Real.log H

theorem triangular_parity_exact (N H : ℕ) :
    triangularCorrelation centeredMangoldt N H =
      evenSigned N H - oddMean N H + oddRaw N H := by
  unfold triangularCorrelation evenSigned oddMean oddRaw
  rw [← mul_sub, ← mul_add, ← sum_sub_distrib, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro h hh
  by_cases ho : (h + 1) % 2 = 1
  · simp only [if_pos ho, triangleWeight]
    rw [centered_gap_raw_exact]
    ring
  · simp [ho, triangleWeight]

/-- Exact identity; the positive odd exception is not silently discarded. -/
theorem offDiagonal_even_exact (N H : ℕ) :
    centeredOffDiagonal N H + (H : ℝ) * N * Real.log H =
      evenResidual N H + oddRaw N H := by
  rw [centeredOffDiagonal_boundary_exact, triangular_parity_exact]
  unfold evenResidual
  ring

theorem prefix_even_exact (N H : ℕ) :
    2 * ∑ k ∈ range H, primePrefixError N k +
      boundaryCorrection centeredMangoldt N H = evenResidual N H + oddRaw N H := by
  rw [← centeredOffDiagonal_prefix_error_exact, offDiagonal_even_exact]

theorem oddRaw_nonneg (N H : ℕ) : 0 ≤ oddRaw N H := by
  unfold oddRaw
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro h hh
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (rawGapCorrelation_nonneg _ _)
  · exact le_rfl

theorem oddWeight_nonneg (H : ℕ) : 0 ≤ oddWeight H := by
  unfold oddWeight
  apply sum_nonneg
  intro h hh
  split_ifs <;> simp [triangleWeight]

theorem triangleWeight_sum (H : ℕ) :
    (∑ h ∈ range H, triangleWeight H h) = (H : ℝ) * ((H : ℝ) - 1) / 2 := by
  have ht := triangle_prefix (fun _ => (1 : ℝ)) H
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at ht
  exact ht.trans (range_linear_sum H)

theorem oddWeight_le_triangle (H : ℕ) :
    oddWeight H ≤ (H : ℝ) * ((H : ℝ) - 1) / 2 := by
  rw [← triangleWeight_sum]
  apply sum_le_sum
  intro h hh
  split_ifs <;> simp [triangleWeight]

theorem oddRaw_le (N H : ℕ) :
    oddRaw N H ≤ 4 * oddWeight H * (Real.log ((N + H + 2 : ℕ) : ℝ)) ^ 2 := by
  let L : ℝ := Real.log ((N + H + 2 : ℕ) : ℝ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + H + 2 by omega))
  have hterm (h : ℕ) (hh : h ∈ range H) :
      (if (h + 1) % 2 = 1 then
        triangleWeight H h * rawGapCorrelation N (h + 1) else 0) ≤
      (if (h + 1) % 2 = 1 then triangleWeight H h else 0) * (2 * L ^ 2) := by
    by_cases ho : (h + 1) % 2 = 1
    · simp only [if_pos ho]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      have hlog : Real.log ((N + (h + 1) + 2 : ℕ) : ℝ) ≤ L := by
        apply Real.log_le_log
        · exact_mod_cast (show 0 < N + (h + 1) + 2 by omega)
        · exact_mod_cast (show N + (h + 1) + 2 ≤ N + H + 2 by
            have := mem_range.mp hh
            omega)
      have hl0 : 0 ≤ Real.log ((N + (h + 1) + 2 : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + (h + 1) + 2 by omega))
      exact (odd_raw_le_log_sq N (h + 1) ho).trans (by nlinarith)
    · simp [ho]
  unfold oddRaw
  calc
    _ ≤ 2 * ∑ h ∈ range H,
        (if (h + 1) % 2 = 1 then triangleWeight H h else 0) * (2 * L ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by norm_num)
    _ = _ := by rw [← sum_mul]; unfold oddWeight; ring

theorem oddRaw_le_quadratic (N H : ℕ) :
    oddRaw N H ≤ 2 * (H : ℝ) ^ 2 * (Real.log ((N + H + 2 : ℕ) : ℝ)) ^ 2 := by
  have hw := oddWeight_le_triangle H
  have hH := Nat.cast_nonneg (α := ℝ) H
  have hlog := sq_nonneg (Real.log ((N + H + 2 : ℕ) : ℝ))
  have hm := mul_le_mul_of_nonneg_right hw hlog
  have hh := mul_nonneg hH hlog
  have hb := oddRaw_le N H
  nlinarith

/-- A two-sided enclosure with a completely explicit nonnegative error. -/
theorem evenResidual_enclosure (N H : ℕ) :
    evenResidual N H ≤ centeredOffDiagonal N H + (H : ℝ) * N * Real.log H ∧
    centeredOffDiagonal N H + (H : ℝ) * N * Real.log H ≤
      evenResidual N H + 4 * oddWeight H * (Real.log ((N + H + 2 : ℕ) : ℝ)) ^ 2 := by
  rw [offDiagonal_even_exact]
  constructor
  · linarith [oddRaw_nonneg N H]
  · linarith [oddRaw_le N H]

/-- Positivity of the complete variance supplies a rigorous one-sided constraint. -/
theorem evenResidual_lower (N H : ℕ) :
    (H : ℝ) * N * Real.log H - centeredDiagonal N H -
      4 * oddWeight H * (Real.log ((N + H + 2 : ℕ) : ℝ)) ^ 2 ≤ evenResidual N H := by
  have hv : 0 ≤ centeredVariance N H :=
    sum_nonneg (fun _ _ => sq_nonneg _)
  rw [centeredVariance_exact] at hv
  have he := offDiagonal_even_exact N H
  have hb := oddRaw_le N H
  linarith

/-- General-scale reduction. The only hypothesis is smallness of an elementary explicit budget. -/
theorem evenResidual_tendsto_iff (H : ℕ → ℕ) (q : ℕ → ℝ)
    (hq : ∀ᶠ N in atTop, 0 < q N)
    (hbudget : Tendsto (fun N : ℕ =>
      (2 * (H N : ℝ) ^ 2 * (Real.log ((N + H N + 2 : ℕ) : ℝ)) ^ 2) / q N)
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (centeredOffDiagonal N (H N) + (H N : ℝ) * N * Real.log (H N)) / q N)
      atTop (𝓝 0) ↔
    Tendsto (fun N : ℕ => evenResidual N (H N) / q N) atTop (𝓝 0) := by
  have ho : Tendsto (fun N => oddRaw N (H N) / q N) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hbudget
    · filter_upwards [hq] with N hqN
      exact div_nonneg (oddRaw_nonneg _ _) hqN.le
    · filter_upwards [hq] with N hqN
      exact div_le_div_of_nonneg_right (oddRaw_le_quadratic _ _) hqN.le
  constructor
  · intro ht
    have hh := ht.sub ho
    simpa only [offDiagonal_even_exact, add_div, add_sub_cancel_right, sub_zero] using hh
  · intro ht
    have hh := ht.add ho
    simpa only [offDiagonal_even_exact, add_div, add_zero] using hh

end RiemannResearch.Analysis.EvenGapPrimeReduction
