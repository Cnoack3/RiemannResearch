/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ShortIntervalVariance
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
/-! # Exact endpoint corrections and signed gap prefixes

The short-interval off-diagonal is rewritten as a triangular average of
fixed-base additive correlations, with both endpoint corrections retained.
A second exact identity expresses that triangular average through signed
gap prefixes. The endpoint bound is unconditional for the actual von
Mangoldt coefficients. No prime-pair asymptotic is assumed or proved.

Source: the centered arithmetic expansion in Montgomery--Soundararajan,
*Primes in short intervals* (2004), equations (18)--(19),
https://arxiv.org/abs/math/0409258, and the centering step in Chan,
*A note on Primes in Short Intervals* (2005), Lemma 1,
https://arxiv.org/abs/math/0503441. These references support the arithmetic
interpretation and the use of averaged errors. The finite endpoint and
prefix formulas below are proved directly.

The remaining high-support obligation is a signed bound for the actual
prefix errors. Neither Euler-product convergence nor multiplicative
homogeneous cancellation supplies such an additive estimate.
-/

open scoped BigOperators
open Finset
namespace RiemannResearch.Analysis.ShortIntervalBoundary
theorem sum_shift_exact (f : ℕ → ℝ) (N j : ℕ) :
    (∑ x ∈ range N, f (x + j)) =
    (∑ x ∈ range N, f x) +
      ∑ x ∈ range j, (f (N + x) - f x) := by
  have h1 := Finset.sum_range_add f N j
  have h2 := Finset.sum_range_add f j N
  rw [Nat.add_comm j N] at h2
  simp_rw [Nat.add_comm j] at h2
  rw [Finset.sum_sub_distrib]
  linarith
theorem triangle_prefix (f : ℕ → ℝ) (H : ℕ) :
    (∑ h ∈ range H, ∑ _j ∈ range (H - (h + 1)), f (h + 1)) =
    ∑ k ∈ range H, ∑ h ∈ range k, f (h + 1) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.1 + x.2 + 1,x.1⟩)
    (fun y => ⟨y.2,y.1 - y.2 - 1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨h,j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · rintro ⟨k,h⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    omega
  · rintro ⟨h,j⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only
    congr 1
    omega
  · rintro ⟨k,h⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp only
    congr 1
    omega
  · rintro ⟨h,j⟩ hx
    rfl

noncomputable def gapCorrelation (a : ℕ → ℝ) (N h : ℕ) : ℝ :=
  ∑ x ∈ range N, a (x + 2) * a (x + 2 + h)

noncomputable def gapBoundary (a : ℕ → ℝ) (N j h : ℕ) : ℝ :=
  ∑ x ∈ range j, (a (N + x + 2) * a (N + x + 2 + h) - a (x + 2) * a (x + 2 + h))

theorem shifted_gap_exact (a : ℕ → ℝ) (N j h : ℕ) :
    (∑ x ∈ range N, a (x + j + 2) * a (x + j + 2 + h)) =
      gapCorrelation a N h + gapBoundary a N j h := by
  simpa [gapCorrelation, gapBoundary, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using
    sum_shift_exact (fun x => a (x + 2) * a (x + 2 + h)) N j

noncomputable def triangularCorrelation (a : ℕ → ℝ) (N H : ℕ) : ℝ :=
  2 * ∑ h ∈ range H, ((H - (h + 1) : ℕ) : ℝ) * gapCorrelation a N (h + 1)

noncomputable def boundaryCorrection (a : ℕ → ℝ) (N H : ℕ) : ℝ :=
  2 * ∑ h ∈ range H, ∑ j ∈ range (H - (h + 1)), gapBoundary a N j (h + 1)

theorem offDiagonal_exact (a : ℕ → ℝ) (N H : ℕ) :
    (2 * ∑ h ∈ range H, ∑ j ∈ range (H - (h + 1)), ∑ x ∈ range N,
      a (x + j + 2) * a (x + j + 2 + (h + 1))) =
      triangularCorrelation a N H + boundaryCorrection a N H := by
  simp_rw [shifted_gap_exact]
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
  unfold triangularCorrelation boundaryCorrection
  ring

noncomputable def prefixCorrelation (a : ℕ → ℝ) (N k : ℕ) : ℝ :=
  ∑ h ∈ range k, gapCorrelation a N (h + 1)

theorem triangular_eq_prefix (a : ℕ → ℝ) (N H : ℕ) :
    triangularCorrelation a N H =
      2 * ∑ k ∈ range H, prefixCorrelation a N k := by
  unfold triangularCorrelation prefixCorrelation
  congr 1
  simpa only [sum_const, card_range, nsmul_eq_mul] using
    triangle_prefix (gapCorrelation a N) H

theorem range_linear_sum (H : ℕ) :
    (∑ j ∈ range H, (j : ℝ)) = (H: ℝ) * ((H: ℝ) - 1) / 2 := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

theorem range_triangle_linear_sum (H : ℕ) :
    (∑ k ∈ range H, ∑ j ∈ range k, (j : ℝ)) =
      (H: ℝ) * ((H: ℝ) - 1) * ((H: ℝ) - 2) / 6 := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ, ih, range_linear_sum]
    push_cast
    ring

theorem boundary_count (H : ℕ) :
    (∑ h ∈ range H, ∑ j ∈ range (H - (h + 1)), (j : ℝ)) =
      (H: ℝ) * ((H: ℝ) - 1) * ((H: ℝ) - 2) / 6 := by
  rw [← ShortIntervalVariance.triangle_by_gap (fun j _ => (j : ℝ))]
  exact range_triangle_linear_sum H

theorem gapBoundary_abs_le (a : ℕ → ℝ) (N H h j : ℕ)
    (hj : j < H - (h + 1)) {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ n, 1 ≤ n → n ≤ N + H → |a n| ≤ M) :
    |gapBoundary a N j (h + 1)| ≤ 2 * (j: ℝ) * M ^ 2 := by
  unfold gapBoundary
  calc
    _ ≤ ∑ x ∈ range j,
        |a (N + x + 2) * a (N + x + 2 + (h + 1)) - a (x + 2) * a (x + 2 + (h + 1))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ range j, (M ^ 2 + M ^ 2) := by
      apply sum_le_sum
      intro x hx
      have hxj : x < j := mem_range.mp hx
      have ha1 := ha (N + x + 2) (by omega) (by omega)
      have ha2 := ha (N + x + 2 + (h + 1)) (by omega) (by omega)
      have ha3 := ha (x + 2) (by omega) (by omega)
      have ha4 := ha (x + 2 + (h + 1)) (by omega) (by omega)
      apply (abs_sub _ _).trans
      gcongr
      · rw [abs_mul, pow_two]
        exact mul_le_mul ha1 ha2 (abs_nonneg _) hM
      · rw [abs_mul, pow_two]
        exact mul_le_mul ha3 ha4 (abs_nonneg _) hM
    _ = _ := by simp; ring

theorem boundaryCorrection_abs_le (a : ℕ → ℝ) (N H : ℕ) {M : ℝ}
    (hM : 0 ≤ M)
    (ha : ∀ n, 1 ≤ n → n ≤ N + H → |a n| ≤ M) :
    |boundaryCorrection a N H| ≤
      (2 / 3: ℝ) * (H: ℝ) * ((H: ℝ) - 1) * ((H: ℝ) - 2) * M ^ 2 := by
  unfold boundaryCorrection
  rw [abs_mul, abs_of_pos (by norm_num : (0: ℝ)<2)]
  calc
    _ ≤ 2 * ∑ h ∈ range H, ∑ j ∈ range (H - (h + 1)),
          |gapBoundary a N j (h + 1)| := by
      gcongr
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun h hh => abs_sum_le_sum_abs _ _)
    _ ≤ 2 * ∑ h ∈ range H, ∑ j ∈ range (H - (h + 1)), 2 * (j: ℝ) * M ^ 2 := by
      gcongr with h hh j hj
      exact gapBoundary_abs_le a N H h j (mem_range.mp hj) hM ha
    _ = 4 * M ^ 2 * (∑ h ∈ range H, ∑ j ∈ range (H - (h + 1)), (j: ℝ)) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro h hh
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [boundary_count]; ring

open ShortIntervalVariance
theorem centeredOffDiagonal_boundary_exact (N H : ℕ) :
    centeredOffDiagonal N H =
      triangularCorrelation centeredMangoldt N H +
      boundaryCorrection centeredMangoldt N H :=
  offDiagonal_exact centeredMangoldt N H

theorem centeredMangoldt_abs_le (n L : ℕ) (hn : 1 ≤ n) (hnL : n ≤ L) :
    |centeredMangoldt n| ≤ Real.log (L + 2) + 1 := by
  unfold centeredMangoldt
  have hnon := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hlog := ArithmeticFunction.vonMangoldt_le_log (n := n)
  have hmono : Real.log (n: ℝ) ≤ Real.log (L + 2) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0<n by omega)
    · exact_mod_cast (show n ≤ L + 2 by omega)
  have hp : 0 ≤ Real.log (L + 2) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    linarith)
  apply abs_le.mpr
  constructor <;> linarith

/-- A proved endpoint budget for the actual von Mangoldt sequence. -/
theorem centered_boundary_bound (N H : ℕ) :
    |boundaryCorrection centeredMangoldt N H| ≤
      (2 / 3: ℝ) * (H: ℝ) * ((H: ℝ) - 1) * ((H: ℝ) - 2) * (Real.log (N + H + 2) + 1) ^ 2 := by
  apply boundaryCorrection_abs_le
  · have hlog : 0 ≤ Real.log (N + H + 2) := Real.log_nonneg (by
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
      linarith)
    linarith
  · intro n hn hnL
    simpa only [Nat.cast_add] using centeredMangoldt_abs_le n (N + H) hn hnL

noncomputable def logIncrement (k : ℕ) : ℝ :=
  (k + 1: ℝ) * Real.log (k + 1) - (k: ℝ) * Real.log k

theorem logIncrement_sum (H : ℕ) :
    (∑ k ∈ range H, logIncrement k) = (H: ℝ) * Real.log H := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ, ih]
    unfold logIncrement
    push_cast
    ring

noncomputable def primePrefixError (N k : ℕ) : ℝ :=
  prefixCorrelation centeredMangoldt N k + (N: ℝ) / 2 * logIncrement k

/-- Exact signed arithmetic error; no endpoint or singleton term is dropped. -/
theorem centeredOffDiagonal_prefix_error_exact (N H : ℕ) :
    centeredOffDiagonal N H + (H: ℝ) * N * Real.log H =
      2 * ∑ k ∈ range H, primePrefixError N k +
      boundaryCorrection centeredMangoldt N H := by
  rw [centeredOffDiagonal_boundary_exact, triangular_eq_prefix]
  simp only [primePrefixError, sum_add_distrib, ← mul_sum, logIncrement_sum]
  ring

theorem centeredVariance_prefix_error_exact (N H : ℕ) :
    centeredVariance N H - (H: ℝ) * N * (Real.log N - Real.log H) =
      (centeredDiagonal N H - (H: ℝ) * N * Real.log N) +
      2 * ∑ k ∈ range H, primePrefixError N k +
      boundaryCorrection centeredMangoldt N H := by
  rw [centeredVariance_error_identity, centeredOffDiagonal_prefix_error_exact]
  ring


theorem centeredOffDiagonal_prefix_bound (N H : ℕ) :
    |centeredOffDiagonal N H + (H: ℝ) * N * Real.log H| ≤
      2 * (∑ k ∈ range H, |primePrefixError N k|) +
      (2 / 3: ℝ) * (H: ℝ) * ((H: ℝ) - 1) * ((H: ℝ) - 2) * (Real.log (N + H + 2) + 1) ^ 2 := by
  rw [centeredOffDiagonal_prefix_error_exact]
  calc
    _ ≤ |2 * ∑ k ∈ range H, primePrefixError N k| +
        |boundaryCorrection centeredMangoldt N H| := abs_add_le _ _
    _ ≤ 2 * (∑ k ∈ range H, |primePrefixError N k|) +
        (2 / 3: ℝ) * (H: ℝ) * ((H: ℝ) - 1) * ((H: ℝ) - 2) * (Real.log (N + H + 2) + 1) ^ 2 := by
      apply add_le_add
      · rw [abs_mul, abs_of_pos (by norm_num : (0: ℝ)<2)]
        exact mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by norm_num)
      · exact centered_boundary_bound N H

theorem centeredVariance_prefix_bound (N H : ℕ) :
    |centeredVariance N H - (H: ℝ) * N * (Real.log N - Real.log H)| ≤
      |centeredDiagonal N H - (H: ℝ) * N * Real.log N| +
      2 * (∑ k ∈ range H, |primePrefixError N k|) +
      (2 / 3: ℝ) * (H: ℝ) * ((H: ℝ) - 1) * ((H: ℝ) - 2) * (Real.log (N + H + 2) + 1) ^ 2 := by
  rw [centeredVariance_error_identity]
  have he := centeredOffDiagonal_prefix_bound N H
  calc
    _ ≤ |centeredDiagonal N H - (H: ℝ) * N * Real.log N| +
      |centeredOffDiagonal N H + (H: ℝ) * N * Real.log H| := abs_add_le _ _
    _ ≤ _ := by linarith

open scoped ArithmeticFunction
noncomputable def mangoldtMass (N : ℕ) : ℝ :=
  ∑ x ∈ range N, Λ (x + 2)

noncomputable def mangoldtMassBoundary (N h : ℕ) : ℝ :=
  ∑ x ∈ range h, (Λ (N + x + 2) - Λ (x + 2))

noncomputable def rawGapCorrelation (N h : ℕ) : ℝ :=
  ∑ x ∈ range N, Λ (x + 2) * Λ (x + 2 + h)

/-- Conversion to raw prime-pair correlations, with the mean and its endpoint shift. -/
theorem centered_gap_raw_exact (N h : ℕ) :
    gapCorrelation centeredMangoldt N h =
      rawGapCorrelation N h - 2 * mangoldtMass N + N -
        mangoldtMassBoundary N h := by
  have hshift : (∑ x ∈ range N, Λ (x + 2 + h)) =
      mangoldtMass N + mangoldtMassBoundary N h := by
    simpa [mangoldtMass, mangoldtMassBoundary, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using sum_shift_exact (fun x => Λ (x + 2)) N h
  unfold gapCorrelation centeredMangoldt
  simp_rw [show ∀ x : ℕ, (Λ (x + 2) - 1) * (Λ (x + 2 + h) - 1) =
    Λ (x + 2) * Λ (x + 2 + h) - Λ (x + 2) - Λ (x + 2 + h) + 1 by intro x; ring]
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_range,
    nsmul_eq_mul, mul_one]
  rw [hshift]
  unfold rawGapCorrelation mangoldtMass
  ring

end RiemannResearch.Analysis.ShortIntervalBoundary
