/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroTailLayerCake
import Mathlib.Tactic.Linarith

/-!
# Exact reflection of actual strict bad tails

The reflected left and right families have equal actual multiplicity.
The conventional inclusive half-plane density count dominates the strict
right tail, preserving the strict bad boundary used by the layer cake.
The inclusive convention agrees with Chourasiya--Simonič,
"An explicit form of Ingham's zero density estimate", Section 1:
https://arxiv.org/html/2507.15184v2 . This file proves finite identities only.
-/

noncomputable section
open Zeta23
open scoped BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

theorem realSum_reflect (T : ℝ) (f : ℂ → ℝ) :
    realSum T (fun ρ => f (reflect ρ)) = realSum T f := by
  classical
  unfold realSum
  apply Finset.sum_bij (fun ρ _ => reflect ρ)
  · exact fun ρ hρ => reflect_mem hρ
  · intro a ha b hb hab
    simpa only [reflect_reflect] using congrArg reflect hab
  · intro ρ hρ
    exact ⟨reflect ρ, reflect_mem hρ, reflect_reflect ρ⟩
  · intro ρ hρ
    rw [zetaSeam.mult_reflect ρ (mem_cutoff.mp hρ).1]

theorem realSum_add (T : ℝ) (f g : ℂ → ℝ) :
    realSum T (fun ρ => f ρ + g ρ) = realSum T f + realSum T g := by
  simp only [realSum, mul_add, Finset.sum_add_distrib]

def rightStrictTail (T t : ℝ) : ℝ :=
  realSum T (fun ρ => if 1 / 2 + t < ρ.re then 1 else 0)

/-- The conventional density count uses an inclusive real-part threshold. -/
def rightInclusiveCount (T σ : ℝ) : ℝ :=
  realSum T (fun ρ => if σ ≤ ρ.re then 1 else 0)

theorem abs_tail_indicator_eq (t : ℝ) (ht : 0 ≤ t) (ρ : ℂ) :
    (if t < |ρ.re - 1 / 2| then (1 : ℝ) else 0) =
      (if 1 / 2 + t < ρ.re then 1 else 0) +
        (if 1 / 2 + t < (reflect ρ).re then 1 else 0) := by
  have hright : 1 / 2 + t < ρ.re ↔ t < ρ.re - 1 / 2 := by
    constructor <;> intro h <;> linarith
  have hleft : 1 / 2 + t < (reflect ρ).re ↔ t < -(ρ.re - 1 / 2) := by
    rw [reflect_re]
    constructor <;> intro h <;> linarith
  simp only [hright, hleft]
  by_cases ha : 0 ≤ ρ.re - 1 / 2
  · rw [abs_of_nonneg ha]
    have hneg : ¬t < -(ρ.re - 1 / 2) := by linarith
    simp only [if_neg hneg, add_zero]
  · have ha0 : ρ.re - 1 / 2 ≤ 0 := (lt_of_not_ge ha).le
    rw [abs_of_nonpos ha0]
    have hneg : ¬t < ρ.re - 1 / 2 := by linarith
    simp only [if_neg hneg, zero_add]

/-- For every nonnegative displacement threshold, all actual bad copies form
equal left and right families, counting their analytic multiplicities. -/
theorem strictTail_eq_twice_right (T t : ℝ) (ht : 0 ≤ t) :
    strictTail T t = 2 * rightStrictTail T t := by
  rw [strictTail_eq_realSum]
  have heq : (fun ρ : ℂ => if t < |ρ.re - 1 / 2| then (1 : ℝ) else 0) =
      (fun ρ => (if 1 / 2 + t < ρ.re then 1 else 0) +
        (if 1 / 2 + t < (reflect ρ).re then 1 else 0)) := by
    funext ρ
    exact abs_tail_indicator_eq t ht ρ
  rw [heq, realSum_add]
  have hreflect : realSum T (fun ρ =>
      if 1 / 2 + t < (reflect ρ).re then (1 : ℝ) else 0) =
      realSum T (fun ρ => if 1 / 2 + t < ρ.re then (1 : ℝ) else 0) :=
    realSum_reflect T (fun ρ => if 1 / 2 + t < ρ.re then (1 : ℝ) else 0)
  rw [hreflect]
  unfold rightStrictTail
  ring

theorem rightStrictTail_le_inclusive (T t : ℝ) :
    rightStrictTail T t ≤ rightInclusiveCount T (1 / 2 + t) := by
  apply realSum_mono
  intro ρ hρ
  by_cases h : 1 / 2 + t < ρ.re
  · simp only [if_pos h, if_pos h.le, le_refl]
  · simp only [if_neg h]
    split_ifs <;> norm_num

theorem strictTail_le_twice_inclusive (T t : ℝ) (ht : 0 ≤ t) :
    strictTail T t ≤ 2 * rightInclusiveCount T (1 / 2 + t) := by
  rw [strictTail_eq_twice_right T t ht]
  exact mul_le_mul_of_nonneg_left (rightStrictTail_le_inclusive T t) (by norm_num)

theorem rightStrictTail_le_half_count (T t : ℝ) (ht : 0 ≤ t) :
    rightStrictTail T t ≤ (Ncount 0 T : ℝ) / 2 := by
  have h := strictTail_le_count T t
  rw [strictTail_eq_twice_right T t ht] at h
  linarith

end RiemannResearch.Analysis.ActualZeroOrdinate
