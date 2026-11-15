/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QFloorDilationEnergy
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Explicit full-conductor repair by dilated Möbius heads

Source: the user's reciprocal-head growth investigation, 7 November 2026.
The construction below combines the existing complete-Q Möbius heads with
the existing legal floor dilation. The exact head and complete Gram identity
precede the Cauchy--Schwarz trace estimate. No estimate for the actual residual
tail is assumed, and no product-decay or RH conclusion is asserted.

The scalar Cauchy--Schwarz step uses Mathlib's
`Finset.sum_mul_sq_le_sq_mul_sq`, in
Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QFullDilatedMobiusRepair
open ZetaTwoHilbert QFullResidueProjection QFloorDilation QMobiusExactHead

/-- The kth physical step, reproduced on the first N sites by a finite legal
vector. The index k here is zero-based; the dilation is k+1. -/
def dilatedMobiusStep (N k : ℕ) : QHilbert :=
  floorDilation (k + 1) (Nat.succ_pos k) (exactHead (N / (k + 1)))

theorem dilatedMobiusStep_mem (N k : ℕ) :
    dilatedMobiusStep N k ∈ legalSpan :=
  floorDilation_mem_legalSpan (k + 1) (Nat.succ_pos k) _
    (exactHead_mem_legalSpan (N / (k + 1)))

/-- The physical head of the dilated Möbius vector is exactly a step. -/
theorem dilatedMobiusStep_head (N k n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    qSequence (dilatedMobiusStep N k) n = if k < n then 1 else 0 := by
  rw [dilatedMobiusStep, floorDilation_sequence]
  change qSequence (exactHead (N / (k + 1))) (n / (k + 1)) =
    if k < n then 1 else 0
  by_cases hkn : k < n
  · rw [if_pos hkn]
    apply exactHead_exact
    · exact Nat.div_pos (by omega) (Nat.succ_pos k)
    · exact Nat.div_le_div_right hnN
  · rw [if_neg hkn, Nat.div_eq_of_lt (show n < k + 1 by omega), qSequence_zero]

/-- This is a complete Hilbert norm estimate, including the infinite tail. -/
theorem dilatedMobiusStep_norm_sq_le (N k : ℕ) :
    ‖dilatedMobiusStep N k‖ ^ 2 ≤
      ‖exactHead (N / (k + 1))‖ ^ 2 / ((k + 1 : ℕ) : ℝ) :=
  floorDilation_norm_sq_le_sharp (k + 1) (Nat.succ_pos k) _

/-- Exact nonnegative block remainder behind the sharp dilation estimate. -/
theorem dilatedMobiusStep_norm_sq_defect (N k : ℕ) :
    ‖exactHead (N / (k + 1))‖ ^ 2 / ((k + 1 : ℕ) : ℝ) -
        ‖dilatedMobiusStep N k‖ ^ 2 =
      ∑' j, qBlockDefect (k + 1) j *
        (qSequence (exactHead (N / (k + 1))) j) ^ 2 :=
  floorDilation_norm_sq_defect (k + 1) (Nat.succ_pos k) _

/-- A completely explicit finite legal repair of arbitrary physical data.
The value at zero is subtracted; use u 0 = 0 for exact interpolation. -/
def repair (N : ℕ) (u : ℕ → ℝ) : QHilbert :=
  ∑ k ∈ Finset.range N, (u (k + 1) - u k) • dilatedMobiusStep N k

theorem repair_mem (N : ℕ) (u : ℕ → ℝ) : repair N u ∈ legalSpan := by
  classical
  unfold repair
  exact legalSpan.sum_mem fun k _ =>
    legalSpan.smul_mem _ (dilatedMobiusStep_mem N k)

theorem repair_sequence (N : ℕ) (u : ℕ → ℝ) (n : ℕ) :
    qSequence (repair N u) n =
      ∑ k ∈ Finset.range N,
        (u (k + 1) - u k) * qSequence (dilatedMobiusStep N k) n := by
  change qSequenceLinear
    (∑ k ∈ Finset.range N, (u (k + 1) - u k) • dilatedMobiusStep N k) n = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

private theorem sum_forward_difference (u : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (u (k + 1) - u k)) = u n - u 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The head is exact, by a finite telescoping identity. -/
theorem repair_head_sub (N : ℕ) (u : ℕ → ℝ) (n : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) :
    qSequence (repair N u) n = u n - u 0 := by
  classical
  rw [repair_sequence]
  simp_rw [dilatedMobiusStep_head N _ n hn hnN]
  simp only [mul_ite, mul_one, mul_zero]
  have hfilter : (Finset.range N).filter (fun k => k < n) = Finset.range n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hfilter]
  exact sum_forward_difference u n

theorem repair_head (N : ℕ) (u : ℕ → ℝ) (hu : u 0 = 0) (n : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) : qSequence (repair N u) n = u n := by
  simpa only [hu, sub_zero] using repair_head_sub N u n hn hnN

/-- Exact full Q Gram energy. Every mixed summand and the complete tail remain. -/
theorem repair_norm_sq_exact (N : ℕ) (u : ℕ → ℝ) :
    ‖repair N u‖ ^ 2 =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        (u (i + 1) - u i) * (u (j + 1) - u j) *
          inner ℝ (dilatedMobiusStep N i) (dilatedMobiusStep N j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [repair]
  rw [sum_inner]
  simp only [real_inner_smul_left, inner_sum, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The full Gram trace bounds the complete synthesis energy. -/
theorem repair_norm_sq_le_trace (N : ℕ) (u : ℕ → ℝ) :
    ‖repair N u‖ ^ 2 ≤
      (∑ k ∈ Finset.range N, (u (k + 1) - u k) ^ 2) *
        (∑ k ∈ Finset.range N, ‖dilatedMobiusStep N k‖ ^ 2) := by
  have htri : ‖repair N u‖ ≤
      ∑ k ∈ Finset.range N, |u (k + 1) - u k| * ‖dilatedMobiusStep N k‖ := by
    simpa only [repair, norm_smul, Real.norm_eq_abs] using
      norm_sum_le (Finset.range N)
        (fun k => (u (k + 1) - u k) • dilatedMobiusStep N k)
  have hnonneg : 0 ≤
      ∑ k ∈ Finset.range N, |u (k + 1) - u k| * ‖dilatedMobiusStep N k‖ :=
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hsq := (sq_le_sq₀ (norm_nonneg (repair N u)) hnonneg).mpr htri
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun k => |u (k + 1) - u k|) (fun k => ‖dilatedMobiusStep N k‖)
  simpa only [sq_abs] using hsq.trans hCS

/-- Explicit finite-stage upper budget in existing complete Möbius-head norms. -/
theorem repair_norm_sq_le_dilation_budget (N : ℕ) (u : ℕ → ℝ) :
    ‖repair N u‖ ^ 2 ≤
      (∑ k ∈ Finset.range N, (u (k + 1) - u k) ^ 2) *
        (∑ k ∈ Finset.range N,
          ‖exactHead (N / (k + 1))‖ ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  apply (repair_norm_sq_le_trace N u).trans
  apply mul_le_mul_of_nonneg_left
  · exact Finset.sum_le_sum fun k _ => dilatedMobiusStep_norm_sq_le N k
  · exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- The target-specific reciprocal repair to which the published residual-tail
identity applies. Its norm is not asserted to be uniformly bounded. -/
def reciprocalRepair (N : ℕ) (f : QHilbert) : QHilbert :=
  repair N (qSequence (QShiftedReciprocal.B f))

theorem reciprocalRepair_mem (N : ℕ) (f : QHilbert) :
    reciprocalRepair N f ∈ legalSpan := repair_mem N _

theorem reciprocalRepair_physical_head (N : ℕ) (f : QHilbert) (n : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) :
    qSequence (reciprocalRepair N f) n = qSequence (QShiftedReciprocal.B f) n :=
  repair_head N _ (qSequence_zero _) n hn hnN

/-- Exact agreement in the encoded coordinates used by the RH consumers. -/
theorem reciprocalRepair_head (N : ℕ) (f : QHilbert) (n : ℕ) (hn : n < N) :
    reciprocalRepair N f n = QShiftedReciprocal.B f n := by
  have hp := reciprocalRepair_physical_head N f (n + 1) (Nat.succ_pos n) (by omega)
  simp only [qSequence_succ] at hp
  exact (div_left_inj'
    (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n)))).mp hp

end RiemannResearch.RH.QFullDilatedMobiusRepair
