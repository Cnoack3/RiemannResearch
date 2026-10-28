/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.NormalizedResidueExactHeadCharges
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QSquarefreeExactHeadAverages
import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Complete-Q Gram minimization of the explicit CRT seed

Source: user-directed investigation of signed exact-head corrections,
28 October 2026. This assembles the existing exhaustive affine-space and
Gram-inverse theorems with the actual coprime-counting CRT seed.
The target-zero optimizer minimizes norm, whereas target qOne minimizes
approximation error. The two complete objectives must not be conflated.
No uniform energy bound or new unconditional RH implication is asserted.
Numerical and rational-arithmetic experiments are recorded separately in
CRTGramMinimizersResearch20261028.md; those intervals are not Lean theorems.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTGramMinimizer
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeLatticePackets
open QResidueHeadSpace QCRTCoprimeApproximation
open QSquarefreeAffineHead (conductors conductor_gt_one divisorStage_eq_dictionary)
open RiemannResearch.Analysis.FiniteHilbertGram

theorem period_mem (L : ℕ) (hL : 1 < L) : L ∈ conductors L := by
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨dvd_refl L, by omega⟩, hL⟩

def optimizer (H L : ℕ) (hL : 1 < L) (t : QHilbert) : QHilbert :=
  affineOptimizer (conductors L) (conductor_gt_one L) H L (period_mem L hL)
    (coprimeApprox L) t

def energy (H L : ℕ) (hL : 1 < L) : ℝ := ‖optimizer H L hL 0‖ ^ 2

theorem seed_mem_dictionary (L : ℕ) (hL : 1 < L) :
    coprimeApprox L ∈ dictionary (conductors L) := by
  rw [← divisorStage_eq_dictionary L (by omega)]
  exact coprimeApprox_mem_divisorStage L

theorem optimizer_feasible (H L : ℕ) (hH : 0 < H) (hL : 1 < L)
    (hHL : H < L) (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ L)
    (t : QHilbert) :
    optimizer H L hL t ∈ divisorStage L ∧
      ∀ n, 0 < n → n ≤ H → qSequence (optimizer H L hL t) n = 1 := by
  have he := affineOptimizer_feasible (conductors L) (conductor_gt_one L)
    H L hH (period_mem L hL) hHL (coprimeApprox L) t
    (seed_mem_dictionary L hL)
    (fun n hn hnH => coprimeApprox_exact_head L H n (by omega) hcover hHL hn hnH)
  simpa only [optimizer, ← divisorStage_eq_dictionary L (by omega : 0 < L)] using he

/-- Every legal competitor is covered, not only a prescribed coefficient ansatz. -/
theorem completion (H L : ℕ) (hH : 0 < H) (hL : 1 < L)
    (hHL : H < L) (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ L)
    (t f : QHilbert) (hf : f ∈ divisorStage L)
    (hhead : ∀ n, 0 < n → n ≤ H → qSequence f n = 1) :
    ‖t - f‖ ^ 2 = ‖t - optimizer H L hL t‖ ^ 2 +
      ‖f - optimizer H L hL t‖ ^ 2 := by
  exact affineOptimizer_error_decomposition (conductors L) (conductor_gt_one L)
    H L hH (period_mem L hL) hHL (coprimeApprox L) t
    (seed_mem_dictionary L hL)
    (fun n hn hnH => coprimeApprox_exact_head L H n (by omega) hcover hHL hn hnH)
    f (by simpa only [← divisorStage_eq_dictionary L (by omega : 0 < L)] using hf)
    hhead

theorem norm_completion (H L : ℕ) (hH : 0 < H) (hL : 1 < L)
    (hHL : H < L) (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ L)
    (f : QHilbert) (hf : f ∈ divisorStage L)
    (hhead : ∀ n, 0 < n → n ≤ H → qSequence f n = 1) :
    ‖f‖ ^ 2 = energy H L hL + ‖f - optimizer H L hL 0‖ ^ 2 := by
  simpa only [zero_sub, norm_neg, energy] using
    completion H L hH hL hHL hcover 0 f hf hhead

/-- The exact reduction in the divergent CRT seed's complete energy. -/
theorem seed_energy_gain (H L : ℕ) (hH : 0 < H) (hL : 1 < L)
    (hHL : H < L) (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ L) :
    ‖coprimeApprox L‖ ^ 2 = energy H L hL +
      ‖coprimeApprox L - optimizer H L hL 0‖ ^ 2 := by
  exact norm_completion H L hH hL hHL hcover _ (coprimeApprox_mem_divisorStage L)
    (fun n hn hnH => coprimeApprox_exact_head L H n (by omega) hcover hHL hn hnH)

theorem energy_le_seed (H L : ℕ) (hH : 0 < H) (hL : 1 < L)
    (hHL : H < L) (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ L) :
    energy H L hL ≤ ‖coprimeApprox L‖ ^ 2 := by
  rw [seed_energy_gain H L hH hL hHL hcover]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- The full signed Schur expression; the inverse is constructed from independence. -/
theorem energy_schur (H L : ℕ) (hL : 1 < L) :
    let v := fun d : freeConductors (conductors L) H L => compensatedResidue (d : ℕ) L
    let hv := compensated_linearIndependent (conductors L) (conductor_gt_one L)
      H L (period_mem L hL)
    energy H L hL = ‖coprimeApprox L‖ ^ 2 -
      ∑ d, inverseCoeff hv (-coprimeApprox L) d * cross v (-coprimeApprox L) d := by
  simpa only [zero_sub, norm_neg, energy, optimizer] using
    affineOptimizer_error_formula (conductors L) (conductor_gt_one L)
      H L (period_mem L hL) (coprimeApprox L) 0

/-- Switching from least norm to least error has an exact positive energy cost. -/
theorem objective_norm_gap (H L : ℕ) (hH : 0 < H) (hL : 1 < L)
    (hHL : H < L) (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ L) :
    ‖optimizer H L hL qOne‖ ^ 2 = energy H L hL +
      ‖optimizer H L hL qOne - optimizer H L hL 0‖ ^ 2 := by
  have hf := optimizer_feasible H L hH hL hHL hcover qOne
  exact norm_completion H L hH hL hHL hcover _ hf.1 hf.2

/-- The same displacement is the exact error cost of minimizing norm instead. -/
theorem objective_error_gap (H L : ℕ) (hH : 0 < H) (hL : 1 < L)
    (hHL : H < L) (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ L) :
    ‖qOne - optimizer H L hL 0‖ ^ 2 =
      ‖qOne - optimizer H L hL qOne‖ ^ 2 +
      ‖optimizer H L hL qOne - optimizer H L hL 0‖ ^ 2 := by
  have hf := optimizer_feasible H L hH hL hHL hcover 0
  simpa only [norm_sub_rev] using
    completion H L hH hL hHL hcover qOne _ hf.1 hf.2

open QFiniteSupportDualCriterion

/-- The objective displacement is bounded by the actual target tail.
The hypotheses are the two exact affine completion identities. -/
theorem optimizer_gap_le_tail_of_completions
    (H : ℕ) (u v : QHilbert)
    (hu : ∀ n, 0 < n → n ≤ H → qSequence u n = 1)
    (hv : ∀ n, 0 < n → n ≤ H → qSequence v n = 1)
    (hzero : ‖v‖ ^ 2 = ‖u‖ ^ 2 + ‖v - u‖ ^ 2)
    (hone : ‖qOne - u‖ ^ 2 = ‖qOne - v‖ ^ 2 + ‖u - v‖ ^ 2) :
    ‖v - u‖ ^ 2 ≤ ‖qOne - finiteHead H qOne‖ ^ 2 := by
  have hone' : ‖qOne - u‖ ^ 2 = ‖qOne - v‖ ^ 2 + ‖v - u‖ ^ 2 := by
    simpa only [norm_sub_rev u v] using hone
  have hpair : inner ℝ qOne (v - u) = ‖v - u‖ ^ 2 := by
    rw [inner_sub_right]
    rw [norm_sub_sq_real, norm_sub_sq_real] at hone'
    nlinarith [hzero]
  have hhead : inner ℝ v (finiteHead H qOne) =
      inner ℝ u (finiteHead H qOne) := by
    apply inner_finiteHead_eq_of_matching_head H v u qOne
    intro n hn hnH
    rw [hv n hn hnH, hu n hn hnH]
  have horth : inner ℝ (finiteHead H qOne) (v - u) = 0 := by
    rw [real_inner_comm, inner_sub_left, hhead, sub_self]
  have htail : inner ℝ (qOne - finiteHead H qOne) (v - u) =
      ‖v - u‖ ^ 2 := by
    rw [inner_sub_left, horth, sub_zero, hpair]
  have hc := abs_real_inner_le_norm (qOne - finiteHead H qOne) (v - u)
  rw [htail, abs_of_nonneg (sq_nonneg _)] at hc
  by_cases hz : ‖v - u‖ = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _
  · have hp : 0 < ‖v - u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hn : ‖v - u‖ ≤ ‖qOne - finiteHead H qOne‖ := by
      nlinarith
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2


/-- Unconditional closeness of the two actual optimizers; no energy budget assumed. -/
theorem objective_gap_le_tail (H L : ℕ) (hH : 0 < H) (hL : 1 < L)
    (hHL : H < L) (hcover : ∀ p : ℕ, p.Prime → p ≤ H → p ∣ L) :
    ‖optimizer H L hL qOne - optimizer H L hL 0‖ ^ 2 ≤
      ‖qOne - finiteHead H qOne‖ ^ 2 := by
  apply optimizer_gap_le_tail_of_completions H
  · exact (optimizer_feasible H L hH hL hHL hcover 0).2
  · exact (optimizer_feasible H L hH hL hHL hcover qOne).2
  · exact objective_norm_gap H L hH hL hHL hcover
  · simpa only [norm_sub_rev] using objective_error_gap H L hH hL hHL hcover

/-- Normal equations in the actual complete-Q compensated basis. -/
theorem optimizer_normal (H L : ℕ) (hL : 1 < L) (t : QHilbert)
    (d : freeConductors (conductors L) H L) :
    inner ℝ (compensatedResidue (d : ℕ) L) (t - optimizer H L hL t) = 0 := by
  unfold optimizer affineOptimizer
  rw [sub_add_eq_sub_sub, inner_sub_right]
  have he := inverseCoeff_normal
    (compensated_linearIndependent (conductors L) (conductor_gt_one L)
      H L (period_mem L hL)) (t - coprimeApprox L) d
  dsimp only [cross] at he
  rw [he, sub_self]

/-- An omitted prime forces the next value to be two for every exact-head competitor. -/
theorem missing_prime_value (L p : ℕ) (hL : 0 < L) (hp : p.Prime)
    (hmiss : ¬ p ∣ L) (f : QHilbert) (hf : f ∈ divisorStage L)
    (hhead : ∀ n, 0 < n → n < p → qSequence f n = 1) :
    qSequence f p = 2 := by
  rw [divisorStage_eq_dictionary L hL] at hf
  obtain ⟨c, hc⟩ := (mem_dictionary_iff (conductors L) f).mp hf
  have hnot : p ∉ conductors L := by
    intro hm
    exact hmiss (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hm).1)
  have he := Pareto.residueFraction_exact_head_next_coefficient
    (conductors L) c p hp.one_lt (by
      intro n hn hnp
      rw [← synthesis_sequence, hc]
      exact hhead n hn hnp)
  rw [if_neg hnot, ArithmeticFunction.moebius_apply_prime hp] at he
  rw [← synthesis_sequence, hc] at he
  norm_num at he
  linarith

/-- A uniform bound on the true norm objective supplies the existing RH consumer.
The final hbudget hypothesis is the open arithmetic estimate. -/
theorem riemannHypothesis_of_bounded_energy (L : ℕ → ℕ)
    (hL : ∀ N, 1 < L N) (hsf : ∀ N, Squarefree (L N))
    (hhead : ∀ N, N + 1 < L N)
    (hcover : ∀ N p : ℕ, p.Prime → p ≤ N + 1 → p ∣ L N)
    (B : ℝ) (hbudget : ∀ N, energy (N + 1) (L N) (hL N) ≤ B) :
    RiemannHypothesis := by
  let F : ℕ → QHilbert := fun N => optimizer (N + 1) (L N) (hL N) 0
  have hf (N : ℕ) := optimizer_feasible (N + 1) (L N) (Nat.succ_pos N)
    (hL N) (hhead N) (hcover N) 0
  have hlegal : ∀ N, F N ∈ qSquarefreeCRTSpan := by
    intro N
    exact divisorStage_le_squarefreeSpan (L N) (by have := hL N; omega)
      (hsf N) (hf N).1
  have hbound : ∀ N, ‖qOne - F N‖ ^ 2 ≤ 2 + 2 * B := by
    intro N
    have hn := norm_sub_le qOne (F N)
    rw [qOne_norm] at hn
    have hb : ‖F N‖ ^ 2 ≤ B := hbudget N
    nlinarith [norm_nonneg (qOne - F N), norm_nonneg (F N), sq_nonneg (‖F N‖ - 1)]
  have hh : ∀ N n, 0 < n → n ≤ N → qSequence (F N) n = 1 := by
    intro N n hn hnN
    exact (hf N).2 n hn (by omega)
  exact (QSquarefreeExactHeadAverages.squarefree_closure_capacity_and_rh_of_bounded_exact_heads
    F hlegal hbound hh).2.2

end RiemannResearch.RH.QCRTGramMinimizer
