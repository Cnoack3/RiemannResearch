/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimorialMatchedDisplacement
import RiemannResearch.RH.QUniformTail
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Uniform refinement of canonical primorial pairing certificates

Source: user-provided *Squarefree projection displacement and infinite CRT
carries*, 9 November 2026, Sections 6 and 12.1. These estimates strengthen
the finite-stage detector using uniform complete tails of the convergent
canonical residual family. They require no RH or projection convergence rate.
Small cofinal upper bounds on the actual signed pairings remain Open.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimorialMatchedDisplacement
open ZetaTwoHilbert ZetaTwoParetoTransfer QSquarefreeFiniteDisplacement
open QAnnihilatorTailEscape QSquarefreeDisplacementRigidity

theorem normalizedPairing_energy_bound (n m : ℕ) (hm : 0 < m)
    (hmem : qResidue m ∈ QSquarefreePrimorialCofinality.primorialStage n) :
    |pError n - normalizedPairing n m| ≤
      Real.sqrt (1 / (m : ℝ)) * ‖toPareto (qOne - pOptimizer n)‖ :=
  (normalizedPairing_tail_bound n m hm hmem).trans
    (mul_le_mul_of_nonneg_left (toPareto_tail_norm_le (m - 1) _)
      (Real.sqrt_nonneg _))

theorem pError_le_of_normalizedPairing_nonpos (n m : ℕ) (hm : 0 < m)
    (hmem : qResidue m ∈ QSquarefreePrimorialCofinality.primorialStage n)
    (hneg : normalizedPairing n m ≤ 0) :
    pError n ≤ 1 / (m : ℝ) := by
  have h := (le_abs_self _).trans (normalizedPairing_energy_bound n m hm hmem)
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1 / (m : ℝ))
  unfold pError at *
  have hn := norm_nonneg (toPareto (qOne - pOptimizer n))
  have hs := Real.sqrt_nonneg (1 / (m : ℝ))
  have hle : ‖toPareto (qOne - pOptimizer n)‖ ≤ Real.sqrt (1 / (m : ℝ)) := by
    nlinarith
  nlinarith

theorem pError_le_twice_pairing_add_inv (n m : ℕ) (hm : 0 < m)
    (hmem : qResidue m ∈ QSquarefreePrimorialCofinality.primorialStage n) :
    pError n ≤ 2 * normalizedPairing n m + 1 / (m : ℝ) := by
  have h := (le_abs_self _).trans (normalizedPairing_energy_bound n m hm hmem)
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1 / (m : ℝ))
  have hnn := sq_nonneg
    (‖toPareto (qOne - pOptimizer n)‖ - Real.sqrt (1 / (m : ℝ)))
  unfold pError at *
  nlinarith


/-- The square-root scaled defect is bounded by the complete moving residual tail. -/
theorem normalizedPairing_scaled_tail_bound (n m : ℕ) (hm : 0 < m)
    (hmem : qResidue m ∈ QSquarefreePrimorialCofinality.primorialStage n) :
    Real.sqrt (m : ℝ) * |pError n - normalizedPairing n m| ≤
      ‖toPareto (tail (m - 1) (qOne - pOptimizer n))‖ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : Real.sqrt (m : ℝ) * Real.sqrt (1 / (m : ℝ)) = 1 := by
    rw [← Real.sqrt_mul hmR.le, mul_one_div_cancel hmR.ne', Real.sqrt_one]
  have h := mul_le_mul_of_nonneg_left (normalizedPairing_tail_bound n m hm hmem)
    (Real.sqrt_nonneg (m : ℝ))
  simpa only [← mul_assoc, hs, one_mul] using h

/-- Uniform little-o improvement over all canonical stages, without a rate
for either projection or any restriction on the stage index. -/
theorem normalizedPairing_uniform_scaled_defect (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ n : ℕ,
      qResidue m ∈ QSquarefreePrimorialCofinality.primorialStage n →
      Real.sqrt (m : ℝ) * |pError n - normalizedPairing n m| < ε := by
  have hs : 0 < Real.sqrt ZetaTwoProbability.zetaTwo :=
    Real.sqrt_pos.mpr ZetaTwoProbability.zetaTwo_pos
  have hf : Tendsto (fun n => qOne - pOptimizer n) atTop (𝓝 pResidual) :=
    tendsto_const_nhds.sub pOptimizer_tendsto
  obtain ⟨H, hH⟩ := uniform_tail_tightness_of_tendsto
    (fun n => qOne - pOptimizer n) pResidual hf
    (ε / Real.sqrt ZetaTwoProbability.zetaTwo) (div_pos hε hs)
  refine ⟨H + 1, ?_⟩
  intro m hm n hmem
  have htail := hH (m - 1) (by omega) n
  have hlt : Real.sqrt ZetaTwoProbability.zetaTwo *
      ‖tail (m - 1) (qOne - pOptimizer n)‖ < ε :=
    by simpa only [mul_comm] using (lt_div_iff₀ hs).mp htail
  exact ((normalizedPairing_scaled_tail_bound n m (by omega) hmem).trans
    (toPareto_norm_le _)).trans_lt hlt

/-- Even an arbitrary choice of stages has a vanishing scaled defect,
provided the tested conductors grow and remain legal. -/
theorem normalizedPairing_scaled_defect_tendsto (N m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop)
    (hmem : ∀ᶠ j in atTop,
      qResidue (m j) ∈ QSquarefreePrimorialCofinality.primorialStage (N j)) :
    Tendsto (fun j => Real.sqrt (m j : ℝ) *
      |pError (N j) - normalizedPairing (N j) (m j)|) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun j =>
      ha.trans_le (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
  · intro ε hε
    obtain ⟨M, hM⟩ := normalizedPairing_uniform_scaled_defect ε hε
    filter_upwards [hm.eventually (eventually_ge_atTop M), hmem] with j hj hjmem
    exact hM (m j) hj (N j) hjmem

end RiemannResearch.RH.QPrimorialMatchedDisplacement
