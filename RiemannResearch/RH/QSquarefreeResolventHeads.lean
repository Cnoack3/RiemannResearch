/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeDisplacementResolvent
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QSievePrimeJump
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Physical heads of the centered squarefree resolvent

Source: user-provided coordinate-evaluation argument, 28 October 2026,
applied to commit d9ceacb7d4783447af945c8df671a8a31a294f98.
The statements and proof strategy use the existing exact signed resolvent
remainder and the actual Q-Hilbert evaluation bound. `Nat.clog 3 N` is the
integer ceiling logarithm. No physical-coordinate tail is truncated.

Uniform logarithmic-depth head control is a conditional research reduction:
it is equivalent to physical boundedness of the actual displacement, and
therefore to vanishing of the squarefree residual. Its arithmetic provider
remains open. Finite iteration depth still uses the closed projection.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeResolventHeads
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QSquarefreeDisplacementRigidity QSquarefreeDisplacementResolvent

/-- Physical-coordinate form of the geometric Hilbert remainder. The site
zero is the conventional zero extension; positive sites are the physical ones. -/
theorem resolvent_error_physical_le (k n : ℕ) :
    |qSequence displacement n - qSequence (resolventApprox k) n| ≤
      Real.sqrt zetaTwo * (n : ℝ) * (1 / 3 : ℝ) ^ k * ‖displacement‖ := by
  have he : qSequence (displacement - resolventApprox k) n =
      qSequence displacement n - qSequence (resolventApprox k) n := by
    change qSequenceLinear (displacement - resolventApprox k) n = _
    rw [map_sub]
    rfl
  rw [← he]
  calc
    _ ≤ Real.sqrt zetaTwo * (n : ℝ) * ‖displacement - resolventApprox k‖ :=
      QPrimePowerSieve.qSequence_abs_le _ _
    _ ≤ Real.sqrt zetaTwo * (n : ℝ) *
        ((1 / 3 : ℝ) ^ k * ‖displacement‖) :=
      mul_le_mul_of_nonneg_left (resolvent_error_norm_le k) (by positivity)
    _ = _ := by ring

/-- Integer logarithmic depth, including an arbitrary extra accuracy margin. -/
def headDepth (N m : ℕ) : ℕ := Nat.clog 3 N + m

theorem headDepth_scale_le (N m : ℕ) :
    (N : ℝ) * (1 / 3 : ℝ) ^ headDepth N m ≤ (1 / 3 : ℝ) ^ m := by
  have hN : (N : ℝ) ≤ (3 : ℝ) ^ Nat.clog 3 N := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (3 : ℕ)) N
  have hcancel : (3 : ℝ) ^ Nat.clog 3 N *
      (1 / 3 : ℝ) ^ Nat.clog 3 N = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((N : ℝ) * (1 / 3 : ℝ) ^ Nat.clog 3 N) * (1 / 3 : ℝ) ^ m := by
      rw [headDepth, pow_add]
      ring
    _ ≤ (1 : ℝ) * (1 / 3 : ℝ) ^ m := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ (3 : ℝ) ^ Nat.clog 3 N * (1 / 3 : ℝ) ^ Nat.clog 3 N :=
          mul_le_mul_of_nonneg_right hN (by positivity)
        _ = 1 := hcancel
    _ = _ := one_mul _

/-- Simultaneous error bound on the complete physical head through N. -/
theorem resolvent_error_head_le (N m n : ℕ) (hn : n ≤ N) :
    |qSequence displacement n - qSequence (resolventApprox (headDepth N m)) n| ≤
      Real.sqrt zetaTwo * (1 / 3 : ℝ) ^ m * ‖displacement‖ := by
  have hs : (n : ℝ) * (1 / 3 : ℝ) ^ headDepth N m ≤ (1 / 3 : ℝ) ^ m := by
    calc
      _ ≤ (N : ℝ) * (1 / 3 : ℝ) ^ headDepth N m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by positivity)
      _ ≤ _ := headDepth_scale_le N m
  calc
    _ ≤ Real.sqrt zetaTwo * (n : ℝ) *
        (1 / 3 : ℝ) ^ headDepth N m * ‖displacement‖ :=
      resolvent_error_physical_le _ _
    _ = Real.sqrt zetaTwo *
        ((n : ℝ) * (1 / 3 : ℝ) ^ headDepth N m) * ‖displacement‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)) (norm_nonneg _)

/-- The unresolved uniform bound on logarithmic-depth heads. -/
def UniformHeadBound (m : ℕ) (C : ℝ) : Prop :=
  ∀ N n : ℕ, n ≤ N →
    |qSequence (resolventApprox (headDepth N m)) n| ≤ C

/-- A head bound supplies a physical bound for the actual displacement. -/
theorem displacement_bounded_of_head_bound (m : ℕ) (C : ℝ)
    (hC : UniformHeadBound m C) (n : ℕ) :
    |qSequence displacement n| ≤
      C + Real.sqrt zetaTwo * (1 / 3 : ℝ) ^ m * ‖displacement‖ := by
  have ht := abs_add_le
    (qSequence displacement n - qSequence (resolventApprox (headDepth n m)) n)
    (qSequence (resolventApprox (headDepth n m)) n)
  rw [sub_add_cancel] at ht
  calc
    _ ≤ _ := ht
    _ ≤ _ := by
      have he := resolvent_error_head_le n m n le_rfl
      have hb := hC n n le_rfl
      linarith

/-- Conversely, bounded displacement controls every logarithmic-depth head. -/
theorem head_bound_of_displacement_bounded (m : ℕ) (C : ℝ)
    (hC : ∀ n : ℕ, |qSequence displacement n| ≤ C) :
    UniformHeadBound m
      (C + Real.sqrt zetaTwo * (1 / 3 : ℝ) ^ m * ‖displacement‖) := by
  intro N n hn
  have ht := abs_add_le
    (qSequence (resolventApprox (headDepth N m)) n - qSequence displacement n)
    (qSequence displacement n)
  rw [sub_add_cancel, abs_sub_comm] at ht
  have he := resolvent_error_head_le N m n hn
  have hb := hC n
  linarith

/-- This reduction is equivalent to the existing displacement-boundedness
criterion, rather than a weaker regularity hypothesis. -/
theorem uniform_head_bound_iff_displacement_bounded (m : ℕ) :
    (∃ C : ℝ, UniformHeadBound m C) ↔
      ∃ C : ℝ, ∀ n : ℕ, |qSequence displacement n| ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨_, displacement_bounded_of_head_bound m C hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨_, head_bound_of_displacement_bounded m C hC⟩

theorem uniform_head_bound_iff_residual_zero (m : ℕ) :
    (∃ C : ℝ, UniformHeadBound m C) ↔ limitingResidual = 0 := by
  rw [uniform_head_bound_iff_displacement_bounded,
    ← residual_eq_zero_iff_displacement_physically_bounded]

/-- Conditional research reduction. The uniform head hypothesis is OPEN. -/
theorem riemannHypothesis_of_uniform_head_bound (m : ℕ) (C : ℝ)
    (hC : UniformHeadBound m C) : RiemannHypothesis := by
  exact riemannHypothesis_of_displacement_bounded _
    (displacement_bounded_of_head_bound m C hC)

/-- The same conditional criterion stated only at positive physical sites. -/
theorem riemannHypothesis_of_positive_head_bound (m : ℕ) (C : ℝ)
    (hC0 : 0 ≤ C)
    (hC : ∀ N n : ℕ, 0 < n → n ≤ N →
      |qSequence (resolventApprox (headDepth N m)) n| ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_uniform_head_bound m C
  intro N n hn
  by_cases hzero : n = 0
  · simpa [hzero] using hC0
  · exact hC N n (Nat.pos_of_ne_zero hzero) hn

end RiemannResearch.RH.QSquarefreeResolventHeads
