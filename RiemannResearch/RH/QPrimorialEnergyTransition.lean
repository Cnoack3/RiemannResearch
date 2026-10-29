/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.AffineEnergyTransition
import RiemannResearch.RH.QPrimorialOptimizerCoalescence
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreeExactHeadResidualBarrier
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
/-!
# Projection gains for the actual prime-head minimum-energy family

Source: user-provided Minimum Energy Optimizer Research Agenda, 29 October
2026, Sections 4--7. The earlier QCRTPeriodHeadBalance already supplies a
two-stage signed recurrence. Here the gain is identified with the actual
enlarged tangent projection, the correction is characterized by its normal
equations, and the agenda's prime-head implementation is identified with
the existing minimumAt family.

The transition identities, feasibility, cofinality, and metric comparisons
are unconditional. All RH conclusions below are conditional research
reductions: bounded signed sums or summable positive increments are Open.
No arithmetic provider for either hypothesis is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QPrimorialEnergyTransition
open ZetaTwoHilbert QResidueHeadSpace QSquarefreeLatticePackets
open RiemannResearch.Analysis.AffineEnergyTransition
open ZetaTwoProbability ZetaTwoParetoTransfer
open QSquarefreeExactHeadResidualBarrier
open QSquarefreeCanonicalFeasibility QPrimorialOptimizerCoalescence QAffineEnergyMinimizers

theorem primeAnchor_monotone : Monotone primeAnchor := by
  intro i j hij
  apply Nat.find_min' (Nat.exists_infinite_primes (i + 2))
  exact ⟨by have := primeAnchor_lower j; omega, primeAnchor_prime j⟩

theorem primeHead_monotone : Monotone primeHead := by
  intro i j hij
  exact Nat.sub_le_sub_right (primeAnchor_monotone hij) 1

def enlargedTangent (H J : ℕ) : Submodule ℝ QHilbert :=
  divisorStage (primorial (J + 1)) ⊓ headNull H

instance enlargedTangent_finiteDimensional (H J : ℕ) :
    FiniteDimensional ℝ (enlargedTangent H J) := by
  let s := (primorial (J + 1)).divisors
  let : FiniteDimensional ℝ (dictionary s) := by
    change FiniteDimensional ℝ (Submodule.span ℝ (Set.range fun d : s => qResidue (d : ℕ)))
    exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
  have hstage : divisorStage (primorial (J + 1)) ≤ dictionary s := by
    apply Submodule.span_le.mpr
    rintro f ⟨d, hd, rfl⟩
    exact Submodule.subset_span
      ⟨⟨d, Nat.mem_divisors.mpr ⟨hd, ne_of_gt (primorial_pos _)⟩⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le
    (show enlargedTangent H J ≤ dictionary s from fun f hf => hstage hf.1)

theorem tangent_le_enlarged (H J : ℕ) (hHJ : H ≤ J) :
    tangent J ≤ enlargedTangent H J := by
  intro f hf
  exact ⟨hf.1, fun n hn hnH => hf.2 n hn (hnH.trans hHJ)⟩

theorem old_mem_new_stage (H J : ℕ) (hHJ : H ≤ J) (hsf : Squarefree (H + 1)) :
    qOptimizer H ∈ divisorStage (primorial (J + 1)) :=
  divisorStage_mono (primorial_dvd_primorial (Nat.add_le_add_right hHJ 1))
    (qOptimizer_mem_stage H hsf)

theorem next_sub_old_mem (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) (hJ : Squarefree (J + 1)) :
    qOptimizer J - qOptimizer H ∈ enlargedTangent H J := by
  refine ⟨Submodule.sub_mem _ (qOptimizer_mem_stage J hJ)
    (old_mem_new_stage H J hHJ hH), ?_⟩
  intro n hn hnH
  change qSequenceLinear (qOptimizer J - qOptimizer H) n = 0
  simp only [map_sub, Pi.sub_apply]
  change qSequence (qOptimizer J) n - qSequence (qOptimizer H) n = 0
  rw [qOptimizer_exact_head J n hn (hnH.trans hHJ),
    qOptimizer_exact_head H n hn hnH, sub_self]


/-- Old-head minimum after the dictionary has been enlarged. -/
def enlargedMinimum (H J : ℕ) : QHilbert :=
  minimumOff (enlargedTangent H J) (qOptimizer H)

/-- The actual energy saved by dictionary enlargement. -/
def enlargementVector (H J : ℕ) : QHilbert :=
  (enlargedTangent H J).starProjection (qOptimizer H)

/-- The least correction from the enlarged old-head minimum to the new minimum. -/
def extensionCorrection (H J : ℕ) : QHilbert :=
  qOptimizer J - enlargedMinimum H J

theorem enlargedMinimum_mem_stage (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) :
    enlargedMinimum H J ∈ divisorStage (primorial (J + 1)) :=
  Submodule.sub_mem _ (old_mem_new_stage H J hHJ hH)
    ((enlargedTangent H J).starProjection_apply_mem (qOptimizer H)).1

theorem enlargedMinimum_exact_head (H J n : ℕ) (hn : 0 < n) (hnH : n ≤ H) :
    qSequence (enlargedMinimum H J) n = 1 := by
  have hz := ((enlargedTangent H J).starProjection_apply_mem
    (qOptimizer H)).2 n hn hnH
  change qSequenceLinear (_ - _) n = 1
  simp only [map_sub, Pi.sub_apply]
  change qSequence (qOptimizer H) n -
    qSequence ((enlargedTangent H J).starProjection (qOptimizer H)) n = 1
  rw [qOptimizer_exact_head H n hn hnH, hz, sub_zero]

theorem extensionCorrection_mem (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) (hJ : Squarefree (J + 1)) :
    extensionCorrection H J ∈ enlargedTangent H J := by
  have he : extensionCorrection H J =
      (qOptimizer J - qOptimizer H) + enlargementVector H J := by
    unfold extensionCorrection enlargedMinimum minimumOff enlargementVector
    abel
  rw [he]
  exact (enlargedTangent H J).add_mem (next_sub_old_mem H J hHJ hH hJ)
    ((enlargedTangent H J).starProjection_apply_mem (qOptimizer H))

theorem extensionCorrection_normal (H J : ℕ) (hHJ : H ≤ J) :
    ∀ u ∈ tangent J, inner ℝ u (extensionCorrection H J) = 0 := by
  intro u hu
  change inner ℝ u (qOptimizer J - enlargedMinimum H J) = 0
  rw [inner_sub_right]
  have hnew : inner ℝ u (qOptimizer J) = 0 :=
    minimumOff_normal (tangent J) (QMobiusExactHead.exactHead J) u hu
  have hold : inner ℝ u (enlargedMinimum H J) = 0 :=
    minimumOff_normal (enlargedTangent H J) (qOptimizer H) u
      (tangent_le_enlarged H J hHJ hu)
  rw [hnew, hold, sub_self]

/-- Minimum-norm correction with all dependent physical constraints retained. -/
theorem extensionCorrection_minimizes (H J : ℕ) (hHJ : H ≤ J) :
    ∀ u ∈ tangent J,
      ‖extensionCorrection H J‖ ^ 2 ≤ ‖extensionCorrection H J + u‖ ^ 2 :=
  (RiemannResearch.Analysis.AffineEnergyMinimum.minimum_iff_normal
    (tangent J) (extensionCorrection H J)).mpr
      (extensionCorrection_normal H J hHJ)

theorem extensionCorrection_new_head (H J n : ℕ) (hn : 0 < n) (hnJ : n ≤ J) :
    qSequence (extensionCorrection H J) n =
      1 - qSequence (enlargedMinimum H J) n := by
  change qSequenceLinear (_ - _) n = _
  simp only [map_sub, Pi.sub_apply]
  change qSequence (qOptimizer J) n - qSequence (enlargedMinimum H J) n = _
  rw [qOptimizer_exact_head J n hn hnJ]

theorem enlargement_energy_exact (H J : ℕ) :
    ‖qOptimizer H‖ ^ 2 =
      ‖enlargedMinimum H J‖ ^ 2 + ‖enlargementVector H J‖ ^ 2 :=
  enlargement_energy (enlargedTangent H J) (qOptimizer H)

/-- Unconditional exact identity for any two nested feasible prime-type heads. -/
theorem optimizer_energy_transition (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) (hJ : Squarefree (J + 1)) :
    ‖qOptimizer J‖ ^ 2 - ‖qOptimizer H‖ ^ 2 =
      ‖extensionCorrection H J‖ ^ 2 - ‖enlargementVector H J‖ ^ 2 :=
  feasible_energy_transition (enlargedTangent H J)
    (qOptimizer H) (qOptimizer J) (next_sub_old_mem H J hHJ hH hJ)

/-- The signed cross term is exactly the enlargement/extension difference. -/
theorem optimizer_signed_correction (H J : ℕ) (hHJ : H ≤ J)
    (hH : Squarefree (H + 1)) (hJ : Squarefree (J + 1)) :
    2 * inner ℝ (qOptimizer H) (qOptimizer J - qOptimizer H) +
      ‖qOptimizer J - qOptimizer H‖ ^ 2 =
        ‖extensionCorrection H J‖ ^ 2 - ‖enlargementVector H J‖ ^ 2 := by
  have h := optimizer_energy_transition H J hHJ hH hJ
  have he : qOptimizer J = qOptimizer H + (qOptimizer J - qOptimizer H) := by abel
  have hn := congrArg (fun x : QHilbert => ‖x‖ ^ 2) he
  rw [norm_add_sq_real] at hn
  linarith


/-- The prime-head optimizer is the existing complete-energy minimum in
the identical dictionary. This identifies the two implementations. -/
theorem qOptimizer_eq_minimumAt (H : ℕ) (hH : 1 ≤ H)
    (hsf : Squarefree (H + 1)) :
    qOptimizer H = QCRTPeriodHeadBalance.minimumAt (H - 1) H := by
  have hindex : H - 1 + 2 = H + 1 := by omega
  have hfeas : H ≤ H - 1 + 1 := by omega
  have hmem : qOptimizer H ∈ divisorStage (primorial ((H - 1) + 2)) := by
    rw [hindex]
    exact qOptimizer_mem_stage H hsf
  have hc := QCRTPeriodHeadBalance.minimumAt_completion (H - 1) H hfeas
    (qOptimizer H) hmem (qOptimizer_exact_head H)
  have hm := qOptimizer_minimizes H hsf
    (QCRTPeriodHeadBalance.minimumAt (H - 1) H)
    (by simpa only [hindex] using QCRTPeriodHeadBalance.minimumAt_mem (H - 1) H)
    (QCRTPeriodHeadBalance.minimumAt_head (H - 1) H hfeas)
  have hz : ‖qOptimizer H - QCRTPeriodHeadBalance.minimumAt (H - 1) H‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖qOptimizer H - QCRTPeriodHeadBalance.minimumAt (H - 1) H‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

def energy (j : ℕ) : ℝ := ‖qOptimizer (primeHead j)‖ ^ 2

def netIncrement (j : ℕ) : ℝ :=
  ‖extensionCorrection (primeHead j) (primeHead (j + 1))‖ ^ 2 -
    ‖enlargementVector (primeHead j) (primeHead (j + 1))‖ ^ 2

theorem primeHead_squarefree (j : ℕ) : Squarefree (primeHead j + 1) := by
  rw [primeHead_add_one]
  exact (primeAnchor_prime j).squarefree

theorem energy_step (j : ℕ) : energy (j + 1) - energy j = netIncrement j :=
  optimizer_energy_transition _ _ (primeHead_monotone (Nat.le_succ j))
    (primeHead_squarefree j) (primeHead_squarefree (j + 1))

theorem energy_telescope (N : ℕ) :
    energy N = energy 0 + ∑ j ∈ Finset.range N, netIncrement j := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ← energy_step, ih]
      ring

theorem energy_bounded_iff_net_sums_bounded :
    (∃ C : ℝ, ∀ N, energy N ≤ C) ↔
      ∃ C : ℝ, ∀ N, (∑ j ∈ Finset.range N, netIncrement j) ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C - energy 0, ?_⟩
    intro N
    have he := energy_telescope N
    have hb := hC N
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨energy 0 + C, ?_⟩
    intro N
    rw [energy_telescope]
    exact add_le_add le_rfl (hC N)

/-- Even a bounded cofinal subsequence kills the actual residual. -/
theorem residual_eq_zero_of_frequently_bounded (C : ℝ)
    (hC : ∃ᶠ j in atTop, energy j ≤ C) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  exact residual_eq_zero_of_frequently_bounded_exact_head_energies
      primeHead primeHead_tendsto (fun j => qOptimizer (primeHead j))
      (fun j => (prime_schedule_legal j).1)
      (fun j => qOptimizer_exact_head (primeHead j)) C hC

theorem residual_eq_zero_of_net_sums_bounded
    (hbound : ∃ C : ℝ, ∀ N, (∑ j ∈ Finset.range N, netIncrement j) ≤ C) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  obtain ⟨C, hC⟩ := energy_bounded_iff_net_sums_bounded.mpr hbound
  exact residual_eq_zero_of_frequently_bounded C (Eventually.of_forall hC).frequently

theorem energy_bound_of_summable_positive_increments
    (h : Summable (fun j => max (netIncrement j) 0)) (N : ℕ) :
    energy N ≤ energy 0 + ∑' j, max (netIncrement j) 0 := by
  rw [energy_telescope]
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ j ∈ Finset.range N, max (netIncrement j) 0 :=
      Finset.sum_le_sum (fun j _ => le_max_left _ _)
    _ ≤ ∑' j, max (netIncrement j) 0 :=
      h.sum_le_tsum _ (fun j _ => le_max_right _ _)

/-- Conditional research reduction: the signed cumulative bound remains Open. -/
theorem riemannHypothesis_of_net_sums_bounded
    (hbound : ∃ C : ℝ, ∀ N, (∑ j ∈ Finset.range N, netIncrement j) ≤ C) :
    RiemannHypothesis := by
  have hr := residual_eq_zero_of_net_sums_bounded hbound
  have hp : qOne = ZetaTwoOptimizerStage.closure.starProjection qOne :=
    sub_eq_zero.mp hr
  have hm : qOne ∈ ZetaTwoOptimizerStage.closure := by
    rw [hp]
    exact ZetaTwoOptimizerStage.closure.starProjection_apply_mem qOne
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure] at hm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_squarefree_closure.mpr hm)

theorem riemannHypothesis_of_summable_positive_increments
    (h : Summable (fun j => max (netIncrement j) 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_net_sums_bounded
  apply energy_bounded_iff_net_sums_bounded.mp
  exact ⟨energy 0 + ∑' j, max (netIncrement j) 0,
    energy_bound_of_summable_positive_increments h⟩

/-- The actual Q and P minima retain the complete metric comparison. -/
theorem prime_minimum_measure_bounds (j : ℕ) :
    zetaTwo * energy j ≤ 2 * ‖toPareto (pOptimizer (primeHead j))‖ ^ 2 ∧
      ‖toPareto (pOptimizer (primeHead j))‖ ^ 2 ≤ zetaTwo * energy j := by
  have hsf := primeHead_squarefree j
  have hq := qOptimizer_minimizes (primeHead j) hsf (pOptimizer (primeHead j))
    (pOptimizer_mem_stage _ hsf) (pOptimizer_exact_head _)
  have hp := pOptimizer_minimizes (primeHead j) hsf (qOptimizer (primeHead j))
    (qOptimizer_mem_stage _ hsf) (qOptimizer_exact_head _)
  constructor
  · exact (mul_le_mul_of_nonneg_left hq zetaTwo_pos.le).trans
      (zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq _)
  · exact hp.trans (toPareto_norm_sq_le _)

end RiemannResearch.RH.QPrimorialEnergyTransition
