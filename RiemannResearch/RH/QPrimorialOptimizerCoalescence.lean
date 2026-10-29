/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.QSquarefreeCanonicalFeasibility
import RiemannResearch.RH.QAffineEnergyMinimizers
import RiemannResearch.RH.QExactHeadOptimizerCoalescence
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Infinite
import Lean.Elab.Tactic.Omega

/-!
# Actual primorial exact-head optimizers coalesce

Source: the user-provided CRT/Ramanujan/Pareto agenda, Priority 3.
The minimizers below are explicit orthogonal corrections of the canonical
Mobius exact-head vector. For squarefree normalization conductor `H+1`,
they are the actual Q and Pareto minimum-energy vectors in the same finite
primorial dictionary with head one. Their difference tends to zero, even
at the weighted squared scale `H * ‖pOptimizer H - qOptimizer H‖²`.

All energy estimates use the existing unconditional complete-energy PNT
provider. No boundedness of the optimizer energies or RH is asserted.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimorialOptimizerCoalescence
open ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer QSquarefreeLatticePackets
open QSquarefreeCanonicalFeasibility QAffineEnergyMinimizers
open QExactHeadOptimizerCoalescence

/-- Q minimum on the explicit affine space with zero-head primorial tangent. -/
def qOptimizer (H : ℕ) : QHilbert :=
  qMin (tangent H) (QMobiusExactHead.exactHead H)

/-- Pareto minimum on the very same physical affine space. -/
def pOptimizer (H : ℕ) : QHilbert :=
  pMin (tangent H) (QMobiusExactHead.exactHead H)

theorem qOptimizer_mem_stage (H : ℕ) (hsf : Squarefree (H + 1)) :
    qOptimizer H ∈ divisorStage (primorial (H + 1)) := by
  have hc := exactHead_mem_primorialStage H hsf
  have hd := base_sub_qMin_mem (tangent H) (QMobiusExactHead.exactHead H)
  have he : qOptimizer H = QMobiusExactHead.exactHead H -
      (QMobiusExactHead.exactHead H - qOptimizer H) := by abel
  rw [he]
  exact Submodule.sub_mem _ hc hd.1

theorem pOptimizer_mem_stage (H : ℕ) (hsf : Squarefree (H + 1)) :
    pOptimizer H ∈ divisorStage (primorial (H + 1)) := by
  have hc := exactHead_mem_primorialStage H hsf
  have hd := pMin_sub_base_mem (tangent H) (QMobiusExactHead.exactHead H)
  have he : pOptimizer H = (pOptimizer H - QMobiusExactHead.exactHead H) +
      QMobiusExactHead.exactHead H := by abel
  rw [he]
  exact Submodule.add_mem _ hd.1 hc

theorem qOptimizer_legal (H : ℕ) (hsf : Squarefree (H + 1)) :
    qOptimizer H ∈ qSquarefreeCRTSpan :=
  divisorStage_le_squarefreeSpan _ (primorial_pos _) (squarefree_primorial _)
    (qOptimizer_mem_stage H hsf)

theorem pOptimizer_legal (H : ℕ) (hsf : Squarefree (H + 1)) :
    pOptimizer H ∈ qSquarefreeCRTSpan :=
  divisorStage_le_squarefreeSpan _ (primorial_pos _) (squarefree_primorial _)
    (pOptimizer_mem_stage H hsf)

theorem qOptimizer_exact_head (H n : ℕ) (hn : 0 < n) (hnH : n ≤ H) :
    qSequence (qOptimizer H) n = 1 := by
  have h := (base_sub_qMin_mem (tangent H)
    (QMobiusExactHead.exactHead H)).2 n hn hnH
  change qSequenceLinear (QMobiusExactHead.exactHead H - qOptimizer H) n = 0 at h
  simp only [map_sub, Pi.sub_apply] at h
  change qSequence (QMobiusExactHead.exactHead H) n - qSequence (qOptimizer H) n = 0 at h
  rw [QMobiusExactHead.exactHead_exact H n hn hnH] at h
  linarith

theorem pOptimizer_exact_head (H n : ℕ) (hn : 0 < n) (hnH : n ≤ H) :
    qSequence (pOptimizer H) n = 1 := by
  have h := (pMin_sub_base_mem (tangent H)
    (QMobiusExactHead.exactHead H)).2 n hn hnH
  change qSequenceLinear (pOptimizer H - QMobiusExactHead.exactHead H) n = 0 at h
  simp only [map_sub, Pi.sub_apply] at h
  change qSequence (pOptimizer H) n - qSequence (QMobiusExactHead.exactHead H) n = 0 at h
  rw [QMobiusExactHead.exactHead_exact H n hn hnH] at h
  linarith

/-- These are genuine attained minima of the finite exact-head problem. -/
theorem qOptimizer_minimizes (H : ℕ) (hsf : Squarefree (H + 1))
    (F : QHilbert) (hF : F ∈ divisorStage (primorial (H + 1)))
    (hhead : ∀ n, 0 < n → n ≤ H → qSequence F n = 1) :
    ‖qOptimizer H‖ ^ 2 ≤ ‖F‖ ^ 2 := by
  have hdiff := sub_mem_tangent H F (qOptimizer H) hF
    (qOptimizer_mem_stage H hsf) hhead (qOptimizer_exact_head H)
  have h := qMin_minimizes (tangent H) (QMobiusExactHead.exactHead H)
    (F - qOptimizer H) hdiff
  change ‖qOptimizer H‖ ^ 2 ≤ ‖qOptimizer H + (F - qOptimizer H)‖ ^ 2 at h
  have he : qOptimizer H + (F - qOptimizer H) = F := by abel
  simpa only [he] using h

theorem pOptimizer_minimizes (H : ℕ) (hsf : Squarefree (H + 1))
    (F : QHilbert) (hF : F ∈ divisorStage (primorial (H + 1)))
    (hhead : ∀ n, 0 < n → n ≤ H → qSequence F n = 1) :
    ‖toPareto (pOptimizer H)‖ ^ 2 ≤ ‖toPareto F‖ ^ 2 := by
  have hdiff := sub_mem_tangent H F (pOptimizer H) hF
    (pOptimizer_mem_stage H hsf) hhead (pOptimizer_exact_head H)
  have h := pMin_minimizes (tangent H) (QMobiusExactHead.exactHead H)
    (F - pOptimizer H) hdiff
  change ‖toPareto (pOptimizer H)‖ ^ 2 ≤
    ‖toPareto (pOptimizer H + (F - pOptimizer H))‖ ^ 2 at h
  have he : pOptimizer H + (F - pOptimizer H) = F := by abel
  simpa only [he] using h

/-- Complete-energy comparison with an explicit arithmetic competitor. -/
theorem optimizer_displacement_bound (H : ℕ) :
    4 * ((H : ℝ) + 1) * ((H : ℝ) + 2) *
      ‖pOptimizer H - qOptimizer H‖ ^ 2 ≤
        ‖QMobiusExactHead.exactHead H‖ ^ 2 :=
  actual_minimizers_competitor_bound H (tangent H)
    (QMobiusExactHead.exactHead H) (tangent_coordinates_zero H)

/-- Unconditional weighted coalescence; no unknown energy premise remains. -/
theorem scaled_optimizer_coalescence :
    Tendsto (fun H : ℕ => (H : ℝ) * ‖pOptimizer H - qOptimizer H‖ ^ 2)
      atTop (𝓝 0) :=
  scaled_displacement_tendsto_zero id tendsto_id
    (fun H => pOptimizer H - qOptimizer H) optimizer_displacement_bound

/-- Unconditional norm coalescence of the two explicitly defined optimizers. -/
theorem optimizer_coalescence :
    Tendsto (fun H : ℕ => ‖pOptimizer H - qOptimizer H‖) atTop (𝓝 0) :=
  displacement_norm_tendsto_zero id tendsto_id
    (fun H => pOptimizer H - qOptimizer H) optimizer_displacement_bound

/-- Any cofinal schedule, including prime anchors, inherits the weighted limit. -/
theorem cofinal_scaled_optimizer_coalescence
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    Tendsto (fun j => (H j : ℝ) * ‖pOptimizer (H j) - qOptimizer (H j)‖ ^ 2)
      atTop (𝓝 0) := by
  simpa only [Function.comp_def] using scaled_optimizer_coalescence.comp hH

/-- Prime anchors make both outputs finite squarefree legal vectors. -/
theorem prime_anchor_legal (H : ℕ) (hp : Nat.Prime (H + 1)) :
    qOptimizer H ∈ qSquarefreeCRTSpan ∧ pOptimizer H ∈ qSquarefreeCRTSpan :=
  ⟨qOptimizer_legal H hp.squarefree, pOptimizer_legal H hp.squarefree⟩

/-- The least prime anchor at least `j+2`, with a proved cofinal lower bound. -/
def primeAnchor (j : ℕ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes (j + 2))

theorem primeAnchor_lower (j : ℕ) : j + 2 ≤ primeAnchor j :=
  (Nat.find_spec (Nat.exists_infinite_primes (j + 2))).1

theorem primeAnchor_prime (j : ℕ) : Nat.Prime (primeAnchor j) :=
  (Nat.find_spec (Nat.exists_infinite_primes (j + 2))).2

def primeHead (j : ℕ) : ℕ := primeAnchor j - 1

theorem primeHead_add_one (j : ℕ) : primeHead j + 1 = primeAnchor j := by
  unfold primeHead
  have h := primeAnchor_lower j
  omega

theorem primeHead_tendsto : Tendsto primeHead atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with j hj
  have hp := primeAnchor_lower j
  unfold primeHead
  omega

/-- A fixed cofinal family of actual finite squarefree legal minimizers. -/
theorem prime_schedule_legal (j : ℕ) :
    qOptimizer (primeHead j) ∈ qSquarefreeCRTSpan ∧
      pOptimizer (primeHead j) ∈ qSquarefreeCRTSpan := by
  apply prime_anchor_legal
  rw [primeHead_add_one]
  exact primeAnchor_prime j

/-- No unknown hypothesis remains in the prime-schedule weighted limit. -/
theorem prime_schedule_scaled_coalescence :
    Tendsto (fun j => (primeHead j : ℝ) *
      ‖pOptimizer (primeHead j) - qOptimizer (primeHead j)‖ ^ 2)
      atTop (𝓝 0) :=
  cofinal_scaled_optimizer_coalescence primeHead primeHead_tendsto

theorem prime_schedule_coalescence :
    Tendsto (fun j => ‖pOptimizer (primeHead j) - qOptimizer (primeHead j)‖)
      atTop (𝓝 0) := by
  simpa only [Function.comp_def] using optimizer_coalescence.comp primeHead_tendsto

end RiemannResearch.RH.QPrimorialOptimizerCoalescence
