/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusOneStepCapacity
import RiemannResearch.RH.CanonicalMobiusWindowMinimum
import RiemannResearch.RH.CanonicalMobiusCapacityDensity

/-!
# Exact canonical-window capacity recursion and telescoping

Source: user-provided affine-exhaustion handoff, Section 12. This applies
the complete-tail one-vector Schur identity to the actual windows N,...,M.
The sum of signed gains is exact; no asymptotic lower bound is assumed.
-/

noncomputable section
open Filter
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance

def windowCapacity (N M : ℕ) (hN : 0 < N) : ℝ :=
  capacity N (canonicalWindowIndex N M) (canonicalWindowIndex_pos N M hN)

def windowGain (N M : ℕ) (hN : 0 < N) : ℝ :=
  (oneStepDefect N (canonicalWindowIndex N M)
    (canonicalWindowIndex_pos N M hN) (M + 1)) ^ 2 /
      oneStepSchur N (canonicalWindowIndex N M) (M + 1)

/-- The diagonal window has the single canonical vector as its optimizer. -/
theorem windowCapacity_diagonal (N : ℕ) (hN : 0 < N) :
    windowCapacity N N hN = (‖hilbertTailShift (canonicalMobiusHilbert N) N‖ ^ 2)⁻¹ := by
  obtain ⟨x, hx, hhead, he⟩ :=
    (canonicalWindow_tail_isLeast_all_legal N N hN le_rfl).1
  rw [exact_head_eq_canonical_at_diagonal N x hx hhead] at he
  change ‖hilbertTailShift (canonicalMobiusHilbert N) N‖ ^ 2 =
    (windowCapacity N N hN)⁻¹ at he
  rw [he, inv_inv]

theorem windowGain_nonneg (N M : ℕ) (hN : 0 < N) :
    0 ≤ windowGain N M hN := by
  unfold windowGain oneStepSchur
  positivity

theorem windowCapacity_succ (N M : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    windowCapacity N (M + 1) hN = windowCapacity N M hN + windowGain N M hN := by
  let k := canonicalWindowIndex N M
  let l := oneStepConductors k (M + 1)
  let hk := canonicalWindowIndex_pos N M hN
  let hl := oneStepConductors_pos k (M + 1) hk (by omega)
  let q := canonicalWindowIndex N (M + 1)
  let hq := canonicalWindowIndex_pos N (M + 1) hN
  let e : (Fin (M - N + 1) ⊕ Unit) → Fin (M + 1 - N + 1) :=
    fun j => Sum.elim (fun i => ⟨i.val, by omega⟩)
      (fun _ => ⟨M + 1 - N, by omega⟩) j
  have he : ∀ j, l j = q (e j) := by
    intro j
    cases j with
    | inl i => rfl
    | inr u => simp only [l, q, e, oneStepConductors, Sum.elim_inr, canonicalWindowIndex]; omega
  let d : Fin (M + 1 - N + 1) → (Fin (M - N + 1) ⊕ Unit) := fun j =>
    if hj : j.val < M - N + 1 then Sum.inl ⟨j.val, hj⟩ else Sum.inr ()
  have hd : ∀ j, q j = l (d j) := by
    intro j
    dsimp [d]
    split_ifs with hj
    · rfl
    · simp only [q, l, oneStepConductors, Sum.elim_inr, canonicalWindowIndex]
      omega
  have hc : capacity N l hl = capacity N q hq := le_antisymm
    (capacity_mono_of_family_map N l q hl hq e he)
    (capacity_mono_of_family_map N q l hq hl d hd)
  have hi := capacity_oneStep_increment N k (M + 1) hk (by omega)
  change capacity N l hl - windowCapacity N M hN = windowGain N M hN at hi
  change capacity N q hq = _
  rw [← hc]
  linarith

/-- All conductor gains telescope with their complete signed Schur terms. -/
theorem windowCapacity_telescope (N M L : ℕ) (hN : 0 < N) (hNM : N ≤ M) :
    windowCapacity N (M + L) hN = windowCapacity N M hN +
      ∑ j ∈ Finset.range L, windowGain N (M + j) hN := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [show M + (L + 1) = (M + L) + 1 by omega,
      windowCapacity_succ N (M + L) hN (by omega), ih, Finset.sum_range_succ]
    ring

theorem windowCapacity_eq_base_add_gains (N L : ℕ) (hN : 0 < N) :
    windowCapacity N (N + L) hN =
      (‖hilbertTailShift (canonicalMobiusHilbert N) N‖ ^ 2)⁻¹ +
      ∑ j ∈ Finset.range L, windowGain N (N + j) hN := by
  rw [windowCapacity_telescope N N L hN le_rfl, windowCapacity_diagonal]

/-- Conditional research reduction: divergent sums of the actual signed gains
at every fixed positive head imply Mathlib RH. The divergence is unproved. -/
theorem riemannHypothesis_of_window_gain_divergence
    (h : ∀ N : ℕ, ∀ hN : 0 < N,
      Tendsto (fun L => ∑ j ∈ Finset.range L, windowGain N (N + j) hN)
        atTop atTop) : RiemannHypothesis := by
  apply riemannHypothesis_of_all_fixed_head_capacity_divergence
  intro N hN
  apply tendsto_atTop.2
  intro C
  obtain ⟨L, hL⟩ := ((tendsto_atTop.1 (h N hN)) C).exists
  have hbase : 0 ≤ (‖hilbertTailShift (canonicalMobiusHilbert N) N‖ ^ 2)⁻¹ := by
    positivity
  have hcap : C ≤ windowCapacity N (N + L) hN := by
    rw [windowCapacity_eq_base_add_gains]
    linarith
  filter_upwards [eventually_ge_atTop (N + L)] with M hM
  exact hcap.trans (canonicalWindow_capacity_mono N hN hM)

end RiemannResearch.RH.Pareto.CoefficientStabilization.SignedCovariance
