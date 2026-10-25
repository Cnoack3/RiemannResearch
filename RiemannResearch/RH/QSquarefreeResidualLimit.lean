/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeWeakCompactness
import Mathlib.Topology.Order.Basic
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QDivisibilityDensity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Data.Nat.Factorial.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Limits and progression obstructions for squarefree projection residuals

Source: the user's squarefree residual convergence question, 25 October 2026.
The strong-limit input is the existing exhaustive projection theorem. The
progression identity is independently derived from the complete Q-Hilbert
divisibility moments; it is elementary orthogonal decomposition, with no
novelty claim.

Zero convergence is equivalent to squarefree closure and implies Mathlib's RH.
Neither closure nor an L2 counterexample is proved here. Finite-stage positive
error and failure of uniform convergence do not refute L2 convergence.
The masked stages exhaust exactly the squarefree conductors; selecting the
stage immediately after each nonzero atom gives the first-n-atom formulation.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeResidualLimit
open ZetaTwoHilbert ZetaTwoOptimizerStage QDivisibilityDensity
open ArithmeticCumulative
open RiemannResearch.Analysis.ExhaustiveWalk

/-- The actual vector-valued zero limit is exactly the unresolved target membership. -/
theorem residual_tendsto_zero_iff_mem :
    Tendsto residual atTop (𝓝 0) ↔ qOne ∈ closure := by
  constructor
  · intro hz
    have heq : limitingResidual = 0 := tendsto_nhds_unique residual_tendsto hz
    have hproj : closure.starProjection qOne = qOne :=
      (sub_eq_zero.mp heq).symm
    exact Submodule.starProjection_eq_self_iff.mp hproj
  · intro hm
    have hproj : closure.starProjection qOne = qOne :=
      Submodule.starProjection_eq_self_iff.mpr hm
    simpa only [limitingResidual, hproj, sub_self] using residual_tendsto

/-- Every vector in a stage vanishes at each common multiple of its legal conductors. -/
theorem stage_coordinate_zero_of_dvd (n L : ℕ)
    (hdiv : ∀ i : Fin n, Squarefree (i.val + 2) → i.val + 2 ∣ L)
    (v : QHilbert) (hv : v ∈ stage n) :
    qSequence v L = 0 := by
  unfold stage walkSpan at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      change qSequence (squarefreeAtom i.val) L = 0
      by_cases hs : Squarefree (i.val + 2)
      · rw [squarefreeAtom, if_pos hs, qSequence_qResidue]
        simp [residueFraction, Nat.mod_eq_zero_of_dvd (hdiv i hs)]
      · rw [squarefreeAtom, if_neg hs]
        change qSequenceLinear 0 _ = 0
        rw [map_zero]
        rfl
  | zero =>
      change qSequenceLinear 0 _ = 0
      rw [map_zero]
      rfl
  | add x y hx hy ihx ihy =>
      change qSequenceLinear (x + y) _ = 0
      rw [map_add]
      change qSequence x _ + qSequence y _ = 0
      rw [ihx, ihy, add_zero]
  | smul c x hx ih =>
      change qSequenceLinear (c • x) _ = 0
      rw [map_smul]
      change c * qSequence x _ = 0
      rw [ih, mul_zero]

/-- The target residual equals one at every positive common multiple. -/
theorem residual_coordinate_one_of_dvd (n L : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin n, Squarefree (i.val + 2) → i.val + 2 ∣ L) :
    qSequence (residual n) L = 1 := by
  have hp := stage_coordinate_zero_of_dvd n L hdiv (optimizer n)
    ((stage n).starProjection_apply_mem qOne)
  change qSequenceLinear (qOne - optimizer n) _ = 1
  rw [map_sub]
  change qSequence qOne _ - qSequence (optimizer n) _ = 1
  rw [qSequence_qOne, hp]
  simp [qOneSequence, Nat.ne_of_gt hL]

/-- The complete divisibility indicator annihilates the finite legal stage. -/
theorem qDivisor_mem_stage_orthogonal (n L : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin n, Squarefree (i.val + 2) → i.val + 2 ∣ L) :
    qDivisor L ∈ (stage n)ᗮ := by
  apply ((stage n).mem_orthogonal _).mpr
  intro v hv
  unfold stage walkSpan at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      change inner ℝ (squarefreeAtom i.val) (qDivisor L) = 0
      by_cases hs : Squarefree (i.val + 2)
      · rw [squarefreeAtom, if_pos hs]
        exact qResidue_inner_qDivisor_eq_zero (i.val + 2) L hL (hdiv i hs)
      · simp [squarefreeAtom, hs]
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_left, ihx, ihy]
  | smul c x hx ih => simp [real_inner_smul_left, ih]

/-- Exact residual pairing with the complete common-multiple progression. -/
theorem residual_inner_qDivisor (n L : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin n, Squarefree (i.val + 2) → i.val + 2 ∣ L) :
    inner ℝ (residual n) (qDivisor L) = 1 / (L : ℝ)^2 := by
  have hp := ((stage n).mem_orthogonal _).mp
    (qDivisor_mem_stage_orthogonal n L hL hdiv) (optimizer n)
    ((stage n).starProjection_apply_mem qOne)
  rw [ZetaTwoOptimizerStage.residual, inner_sub_left, qOne_inner_qDivisor L hL, hp, sub_zero]

/-- The complete residual energy retains progression mass and its orthogonal remainder. -/
theorem error_eq_progression_mass_add (n L : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin n, Squarefree (i.val + 2) → i.val + 2 ∣ L) :
    error n = 1 / (L : ℝ)^2 + ‖residual n - qDivisor L‖^2 := by
  have hpair := residual_inner_qDivisor n L hL hdiv
  have hnorm := qDivisor_norm_sq L hL
  have hpair' : inner ℝ (qDivisor L) (residual n) = 1/(L : ℝ)^2 := by
    rw [real_inner_comm]
    exact hpair
  have hsq : ‖residual n - qDivisor L‖^2 =
      ‖residual n‖^2 - 1/(L : ℝ)^2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      inner_sub_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      hpair, hpair', hnorm]
    ring
  unfold error
  linarith

/-- Finite-stage lower bound from all common multiples, not a truncated sum. -/
theorem error_ge_progression_mass (n L : ℕ) (hL : 0 < L)
    (hdiv : ∀ i : Fin n, Squarefree (i.val + 2) → i.val + 2 ∣ L) :
    1 / (L : ℝ)^2 ≤ error n := by
  rw [error_eq_progression_mass_add n L hL hdiv]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- No finite-stage residual has uniform absolute bound strictly less than one. -/
theorem residual_not_uniformly_small (n : ℕ) (ε : ℝ) (hε : ε < 1) :
    ¬ ∀ k : ℕ, 0 < k → |qSequence (residual n) k| ≤ ε := by
  intro h
  have hr : qSequence (residual n) ((n+2).factorial) = 1 := by
    apply residual_coordinate_one_of_dvd n _ (Nat.factorial_pos _)
    intro i _
    exact Nat.dvd_factorial (by omega) (by omega)
  have he := h ((n+2).factorial) (Nat.factorial_pos _)
  rw [hr, abs_one] at he
  exact (not_le_of_gt hε) he

/-- Conditional research reduction: the unresolved premise is actual residual convergence. -/
theorem riemannHypothesis_of_residual_tendsto_zero
    (h : Tendsto residual atTop (𝓝 0)) : RiemannHypothesis := by
  apply QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
  apply QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr
  exact residual_tendsto_zero_iff_mem.mp h

/-- The user's full epsilon formulation is exactly target membership, still Open. -/
theorem epsilon_approximation_iff_mem :
    (∀ ε : ℝ, 0 < ε → ∃ M0 : ℕ, ∀ M, M0 ≤ M → error M ≤ ε) ↔
      qOne ∈ closure := by
  rw [← error_tendsto_zero_iff_mem_closure]
  constructor
  · intro h
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun M => ha.trans_le (sq_nonneg ‖residual M‖))
    · intro b hb
      obtain ⟨M0, hM0⟩ := h (b / 2) (by linarith)
      exact Filter.eventually_atTop.2
        ⟨M0, fun M hM => (hM0 M hM).trans_lt (by linarith)⟩
  · intro h ε hε
    obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.1
      (h.eventually (Iio_mem_nhds hε))
    exact ⟨M0, fun M hM => (hM0 M hM).le⟩

/-- Unconditional convergence retains the complete limiting residual energy. -/
theorem eventual_error_le_limitingResidual_add (ε : ℝ) (hε : 0 < ε) :
    ∃ M0 : ℕ, ∀ M, M0 ≤ M → error M ≤ ‖limitingResidual‖ ^ 2 + ε := by
  have ht : Tendsto error atTop (𝓝 (‖limitingResidual‖ ^ 2)) :=
    residual_tendsto.norm.pow 2
  have hb : ‖limitingResidual‖ ^ 2 < ‖limitingResidual‖ ^ 2 + ε := by linarith
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.1
    (ht.eventually (Iio_mem_nhds hb))
  exact ⟨M0, fun M hM => (hM0 M hM).le⟩

/-- Any finite legal competitor bounds every subsequent optimizer. -/
theorem later_error_le_competitor (N M : ℕ) (hNM : N ≤ M)
    (f : QHilbert) (hf : f ∈ stage N) :
    error M ≤ ‖qOne - f‖ ^ 2 := by
  have hfm : f ∈ stage M :=
    walkSpan_mono squarefreeAtom id hNM hf
  have he := QSquarefreeWeakCompactness.optimizer_error_decomposition M f hfm
  change ‖residual M‖ ^ 2 ≤ ‖qOne - f‖ ^ 2
  linarith [sq_nonneg ‖optimizer M - f‖]

end RiemannResearch.RH.QSquarefreeResidualLimit
