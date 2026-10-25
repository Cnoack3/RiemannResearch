/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFiniteSupportDualCriterion
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import RiemannResearch.Analysis.DiscreteTailHardy
import RiemannResearch.RH.QSmoothedResidueAsymptotic
import RiemannResearch.RH.QDivisibilityDensity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Joint square-summability of smoothed residue forcing errors

Source: direct dual discrete Hardy argument developed from the user-provided
signed regularity handoff. Finite triangular sums are estimated first; physical
head convergence then supplies the complete Q inner products. No RH, projection,
or inverse-Gram regularity hypothesis occurs.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QSmoothedResidueAsymptotic
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QFiniteSupportDualCriterion
open RiemannResearch.Analysis.DiscreteTailHardy

private theorem error_coordinate_zero (d n : ℕ) (hn : n < d) :
    atomError (d + 1) n = 0 := by
  have hz := atomError_sequence_eq_zero (d + 1) (n + 1) (Nat.succ_pos d) (by omega)
  have hne : Real.sqrt (qWeight n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n))
  simpa only [qSequence_succ, div_eq_zero_iff, hne, or_false] using hz

/-- Exact inverse-square normalization puts all error coordinates under the
same triangular Hardy kernel. -/
private theorem error_coordinate_scaled_abs_le (d n : ℕ) :
    |Real.sqrt zetaTwo * atomError (d + 1) n| ≤ 1 / ((n : ℝ) + 2) := by
  have hsqrt : 0 < Real.sqrt (qWeight n) := Real.sqrt_pos.mpr (qWeight_pos n)
  have hzeta : 0 ≤ Real.sqrt zetaTwo := Real.sqrt_nonneg _
  have hs := atomError_sequence_abs_le_ratio (d + 1) (n + 1) (Nat.succ_pos d)
  rw [qSequence_succ, abs_div, abs_of_pos hsqrt] at hs
  rw [abs_mul, abs_of_nonneg hzeta]
  calc
    Real.sqrt zetaTwo * |atomError (d + 1) n| =
        (Real.sqrt (qWeight n) * Real.sqrt zetaTwo) *
          (|atomError (d + 1) n| / Real.sqrt (qWeight n)) := by
      field_simp [ne_of_gt hsqrt]
    _ ≤ (Real.sqrt (qWeight n) * Real.sqrt zetaTwo) *
        (((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hsqrt.le hzeta)
    _ = 1 / ((n : ℝ) + 2) := by
      rw [QDivisibilityDensity.sqrt_qWeight_mul_sqrt_zetaTwo]
      push_cast
      field_simp
      ring

private theorem finiteHead_error_bessel (r : QHilbert) (D M : ℕ) (hDM : D ≤ M) :
    zetaTwo * (∑ d ∈ Finset.range D,
      (inner ℝ (finiteHead M r) (atomError (d + 1))) ^ 2) ≤ 4 * ‖r‖ ^ 2 := by
  let K : ℕ → ℕ → ℝ := fun d n => Real.sqrt zetaTwo * atomError (d + 1) n
  have hkzero : ∀ d n : ℕ, n < d → K d n = 0 := by
    intro d n hn
    simp only [K, error_coordinate_zero d n hn, mul_zero]
  have hkernel : ∀ d n : ℕ, |K d n| ≤ 1 / ((n : ℝ) + 2) :=
    error_coordinate_scaled_abs_le
  have hh := triangular_matrix_bessel (fun n => r n) K M D hDM hkzero hkernel
  have hp (d : ℕ) :
      Real.sqrt zetaTwo * inner ℝ (finiteHead M r) (atomError (d + 1)) =
        ∑ n ∈ Finset.range M, r n * K d n := by
    rw [real_inner_comm, inner_finiteHead_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [K]
    ring
  have he : zetaTwo * (∑ d ∈ Finset.range D,
      (inner ℝ (finiteHead M r) (atomError (d + 1))) ^ 2) =
      ∑ d ∈ Finset.range D, (∑ n ∈ Finset.range M, r n * K d n) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← hp d, mul_pow, Real.sq_sqrt zetaTwo_pos.le]
  have hnorm : (∑ n ∈ Finset.range M, (r n) ^ 2) = ‖finiteHead M r‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_finiteHead_eq_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteHead_apply_of_lt M r n (Finset.mem_range.mp hn)]
    ring
  have hnle : ‖finiteHead M r‖ ^ 2 ≤ ‖r‖ ^ 2 := by
    have ht := finiteHead_norm_sq_split M r
    nlinarith [sq_nonneg ‖r - finiteHead M r‖]
  rw [he]
  calc
    _ ≤ 4 * ∑ n ∈ Finset.range M, (r n) ^ 2 := hh
    _ = 4 * ‖finiteHead M r‖ ^ 2 := by rw [hnorm]
    _ ≤ 4 * ‖r‖ ^ 2 := mul_le_mul_of_nonneg_left hnle (by norm_num)

/-- The complete error family is Bessel, uniformly in the conductor cutoff.
No residual projection hypothesis and no RH hypothesis are used. -/
theorem atomError_finite_bessel (r : QHilbert) (D : ℕ) :
    zetaTwo * (∑ d ∈ Finset.range D, (inner ℝ r (atomError (d + 1))) ^ 2) ≤
      4 * ‖r‖ ^ 2 := by
  have ht : Tendsto (fun M : ℕ => zetaTwo *
      (∑ d ∈ Finset.range D, (inner ℝ (finiteHead M r) (atomError (d + 1))) ^ 2))
      atTop (𝓝 (zetaTwo *
        (∑ d ∈ Finset.range D, (inner ℝ r (atomError (d + 1))) ^ 2))) := by
    apply Tendsto.const_mul
    apply tendsto_finsetSum
    intro d hd
    exact ((finiteHead_tendsto r).inner tendsto_const_nhds).pow 2
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop D] with M hM
  exact finiteHead_error_bessel r D M hM

/-- Joint weighted forcing control at the endpoint missed by summing the
individual conductor-decay bounds. -/
theorem signed_forcing_finite_bessel (r : QHilbert) (D : ℕ) :
    zetaTwo * (∑ d ∈ Finset.range D,
      (((d + 1 : ℕ) : ℝ) * inner ℝ r (B (qResidue (d + 1))) -
        inner ℝ r leading) ^ 2) ≤ 4 * ‖r‖ ^ 2 := by
  simp_rw [signed_forcing_expansion]
  exact atomError_finite_bessel r D


theorem atomError_pairing_square_summable (r : QHilbert) :
    Summable (fun d : ℕ => (inner ℝ r (atomError (d + 1))) ^ 2) := by
  apply summable_of_sum_range_le (fun d => sq_nonneg _)
    (c := 4 * ‖r‖ ^ 2 / zetaTwo)
  intro D
  apply (le_div_iff₀ zetaTwo_pos).mpr
  simpa only [mul_comm] using atomError_finite_bessel r D

/-- Complete conductor sum, with the same dimension-independent constant. -/
theorem atomError_bessel (r : QHilbert) :
    zetaTwo * (∑' d : ℕ, (inner ℝ r (atomError (d + 1))) ^ 2) ≤
      4 * ‖r‖ ^ 2 := by
  apply le_of_tendsto
    ((atomError_pairing_square_summable r).hasSum.tendsto_sum_nat.const_mul zetaTwo)
  exact Filter.Eventually.of_forall (atomError_finite_bessel r)

end RiemannResearch.RH.QSmoothedResidueAsymptotic
