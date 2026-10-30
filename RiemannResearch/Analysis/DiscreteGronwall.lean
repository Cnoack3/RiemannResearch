/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A conditional discrete Gronwall route to subpolynomial energy

Source: user-provided innovation-space research agenda, Milestone 4.
The finite estimates and the relative-logarithmic implication are generic.
The arithmetic recurrence and its two growth providers remain explicit
hypotheses; this module does not supply them for the actual RH optimizer.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.DiscreteGronwall

/-- Finite discrete Gronwall inequality with a nonnegative initial value.
Nonnegativity of the later values of E is not required for this upper bound. -/
theorem energy_le_exp_cumulative
    (E α β : ℕ → ℝ)
    (hE0 : 0 ≤ E 0)
    (hα : ∀ n, 0 ≤ α n) (hβ : ∀ n, 0 ≤ β n)
    (hstep : ∀ n, E (n + 1) ≤ (1 + α n) * E n + β n)
    (N : ℕ) :
    E N ≤ (E 0 + ∑ i ∈ Finset.range N, β i) *
      Real.exp (∑ i ∈ Finset.range N, α i) := by
  induction N with
  | zero => simp
  | succ n ih =>
    let A : ℝ := ∑ i ∈ Finset.range n, α i
    let C : ℝ := E 0 + ∑ i ∈ Finset.range n, β i
    have hA : 0 ≤ A := Finset.sum_nonneg (fun i _ => hα i)
    have hC : 0 ≤ C := add_nonneg hE0
      (Finset.sum_nonneg (fun i _ => hβ i))
    have hfactor : 0 ≤ 1 + α n := by linarith [hα n]
    have hlinear : 1 + α n ≤ Real.exp (α n) := by
      linarith [Real.add_one_le_exp (α n)]
    have hExp : 1 ≤ Real.exp (A + α n) := by
      linarith [Real.add_one_le_exp (A + α n), hα n]
    have hih : E n ≤ C * Real.exp A := ih
    have hbound : E (n + 1) ≤ (C + β n) * Real.exp (A + α n) := by
      calc
        E (n + 1) ≤ (1 + α n) * E n + β n := hstep n
        _ ≤ (1 + α n) * (C * Real.exp A) + β n :=
          add_le_add (mul_le_mul_of_nonneg_left hih hfactor) le_rfl
        _ ≤ Real.exp (α n) * (C * Real.exp A) + β n :=
          add_le_add (mul_le_mul_of_nonneg_right hlinear
            (mul_nonneg hC (Real.exp_nonneg _))) le_rfl
        _ = C * Real.exp (A + α n) + β n := by
          rw [Real.exp_add]
          ring
        _ ≤ (C + β n) * Real.exp (A + α n) := by
          nlinarith [mul_nonneg (hβ n) (sub_nonneg.mpr hExp)]
    simpa only [A, C, Finset.sum_range_succ, ← add_assoc] using hbound

/-- Shifted form useful for logarithms. All recurrence coefficients are the
original alpha and beta; adding one only improves the recurrence by alpha. -/
theorem one_add_energy_le_exp_cumulative
    (E α β : ℕ → ℝ)
    (hE0 : 0 ≤ E 0)
    (hα : ∀ n, 0 ≤ α n) (hβ : ∀ n, 0 ≤ β n)
    (hstep : ∀ n, E (n + 1) ≤ (1 + α n) * E n + β n)
    (N : ℕ) :
    1 + E N ≤ (1 + E 0 + ∑ i ∈ Finset.range N, β i) *
      Real.exp (∑ i ∈ Finset.range N, α i) := by
  apply energy_le_exp_cumulative (fun n => 1 + E n) α β
    (by linarith) hα hβ
  intro n
  nlinarith [hstep n, hα n]

/-- A separated logarithmic estimate. The additive forcing contributes only
the logarithm of its cumulative sum; the multiplicative forcing contributes
its cumulative sum itself. -/
theorem log_one_add_energy_le
    (E α β : ℕ → ℝ)
    (hE : ∀ n, 0 ≤ E n)
    (hα : ∀ n, 0 ≤ α n) (hβ : ∀ n, 0 ≤ β n)
    (hstep : ∀ n, E (n + 1) ≤ (1 + α n) * E n + β n)
    (N : ℕ) :
    Real.log (1 + E N) ≤ Real.log (1 + E 0) +
      Real.log (1 + ∑ i ∈ Finset.range N, β i) +
      ∑ i ∈ Finset.range N, α i := by
  let A : ℝ := ∑ i ∈ Finset.range N, α i
  let B : ℝ := ∑ i ∈ Finset.range N, β i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hβ i)
  have hE0 : 0 < 1 + E 0 := by linarith [hE 0]
  have hB1 : 0 < 1 + B := by linarith
  have hEN : 0 < 1 + E N := by linarith [hE N]
  have hproduct : 1 + E 0 + B ≤ (1 + E 0) * (1 + B) := by
    nlinarith [mul_nonneg (hE 0) hB]
  have hbound : 1 + E N ≤ ((1 + E 0) * (1 + B)) * Real.exp A := by
    calc
      _ ≤ (1 + E 0 + B) * Real.exp A :=
        one_add_energy_le_exp_cumulative E α β (hE 0) hα hβ hstep N
      _ ≤ _ := mul_le_mul_of_nonneg_right hproduct (Real.exp_nonneg _)
  have hlog := Real.log_le_log hEN hbound
  rw [Real.log_mul (ne_of_gt (mul_pos hE0 hB1))
      (ne_of_gt (Real.exp_pos A)),
    Real.log_mul (ne_of_gt hE0) (ne_of_gt hB1), Real.log_exp] at hlog
  exact hlog

/-- Conditional growth template from the innovation-space agenda.

The recurrence is a separate arithmetic obligation. So are the two growth
hypotheses: cumulative alpha is o(log scale), and the logarithm of cumulative
beta is o(log scale). The conclusion alone does not discharge these providers.
-/
theorem relativeLog_tendsto_zero
    (E α β L : ℕ → ℝ)
    (hE : ∀ n, 0 ≤ E n)
    (hα : ∀ n, 0 ≤ α n) (hβ : ∀ n, 0 ≤ β n)
    (hstep : ∀ n, E (n + 1) ≤ (1 + α n) * E n + β n)
    (hL : Tendsto L atTop atTop)
    (hlogα : Tendsto
      (fun N => (∑ i ∈ Finset.range N, α i) / Real.log (L N))
      atTop (𝓝 0))
    (hlogβ : Tendsto
      (fun N => Real.log (1 + ∑ i ∈ Finset.range N, β i) / Real.log (L N))
      atTop (𝓝 0)) :
    Tendsto (fun N => Real.log (1 + E N) / Real.log (L N))
      atTop (𝓝 0) := by
  have hlogL : Tendsto (fun n => Real.log (L n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hconstant : Tendsto
      (fun n => Real.log (1 + E 0) / Real.log (L n)) atTop (𝓝 0) :=
    hlogL.const_div_atTop _
  have hupper : Tendsto
      (fun n => Real.log (1 + E 0) / Real.log (L n) +
        Real.log (1 + ∑ i ∈ Finset.range n, β i) / Real.log (L n) +
        (∑ i ∈ Finset.range n, α i) / Real.log (L n))
      atTop (𝓝 0) := by
    simpa only [add_zero] using (hconstant.add hlogβ).add hlogα
  have hL2 : ∀ᶠ n : ℕ in atTop, 2 ≤ L n :=
    hL.eventually (eventually_ge_atTop 2)
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hL2] with n hn
    have hl : 0 ≤ Real.log (L n) := Real.log_nonneg (by linarith)
    have he : 0 ≤ Real.log (1 + E n) := Real.log_nonneg (by linarith [hE n])
    exact ha.trans_le (div_nonneg he hl)
  · intro b hb
    filter_upwards [hL2, hupper.eventually (gt_mem_nhds hb)] with n hn hup
    have hl : 0 < Real.log (L n) := Real.log_pos (by linarith)
    have hh := log_one_add_energy_le E α β hE hα hβ hstep n
    have hratio :
        Real.log (1 + E n) / Real.log (L n) ≤
          Real.log (1 + E 0) / Real.log (L n) +
          Real.log (1 + ∑ i ∈ Finset.range n, β i) / Real.log (L n) +
          (∑ i ∈ Finset.range n, α i) / Real.log (L n) := by
      calc
        _ ≤ (Real.log (1 + E 0) +
          Real.log (1 + ∑ i ∈ Finset.range n, β i) +
          ∑ i ∈ Finset.range n, α i) / Real.log (L n) := by
            simpa only [div_eq_mul_inv] using
              mul_le_mul_of_nonneg_right hh (inv_nonneg.mpr hl.le)
        _ = _ := by ring
    exact hratio.trans_lt hup

end RiemannResearch.Analysis.DiscreteGronwall
