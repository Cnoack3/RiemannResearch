/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticCoreInertia
import RiemannResearch.RH.ParetoLegalApproximationClosure

/-!
# Conditional RH criterion for the actual squarefree arithmetic core

Finite arithmetic identities, nonsingularity, ordinary mean-one optimization,
and exact error evaluation are proved dependencies. The hypotheses below are
the unproved arithmetic saturation input. No saturation or RH is asserted.
The final implication to Mathlib's RiemannHypothesis uses the existing proved
legal Pareto approximation, Hilbert closure, and Mellin separation chain.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ArithmeticCoreRHCriterion
open RiemannResearch.RH.Pareto
open PhysicalPacketCore ArithmeticCoreInertia

/-- Every positive nontrivial packet is legal when all positive seeds are allowed. -/
theorem packet_mem_positiveSeedSpan (q : ℕ) (hq : 1 < q) :
    ramanujanPacket q ∈ legalSeedSpan {n : ℕ | 0 < n} := by
  obtain ⟨p, hp, m, hm⟩ := Nat.exists_prime_and_dvd (show q ≠ 1 by omega)
  have hmpos : 0 < m := by
    by_contra h
    have hmzero : m = 0 := by omega
    simp [hmzero] at hm
    omega
  rw [hm]
  exact ramanujanPacket_seed_multiple_mem _ p hp hp.pos m hmpos

/-- Actual finite synthesis is legal; no limiting interchange is involved. -/
theorem synthesis_mem_positiveSeedSpan (s : Finset ℕ) (c : s → ℝ)
    (hs : ∀ q ∈ s, 1 < q) :
    synthesis s c ∈ legalSeedSpan {n : ℕ | 0 < n} := by
  classical
  have hm : (∑ q : s, c q • ramanujanPacket q.val) ∈
      legalSeedSpan {n : ℕ | 0 < n} := by
    apply (legalSeedSpan {n : ℕ | 0 < n}).sum_mem
    intro q _
    exact (legalSeedSpan {n : ℕ | 0 < n}).smul_mem (c q)
      (packet_mem_positiveSeedSpan q.val (hs q.val q.property))
  convert hm using 1
  ext k
  simp [synthesis, FiniteSchur.combination, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Arbitrarily small exact constrained minima suffice for RH.
The displayed epsilon condition remains the arithmetic research problem. -/
theorem riemannHypothesis_of_squarefree_arithmeticMinima
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ,
      2 < L ∧ Squarefree L ∧
        1 + 4 * Real.pi / arithmeticInverseCharge L (divisorPackets L) < ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_legal_paretoError {n : ℕ | 0 < n}
    (fun _ h => h)
  intro ε hε
  obtain ⟨L, hL, hsq, herr⟩ := happrox ε hε
  refine ⟨synthesis (divisorPackets L)
    (arithmeticConstrainedOptimizer L (divisorPackets L)),
    synthesis_mem_positiveSeedSpan _ _ (divisorPackets_legal L), ?_⟩
  rw [(squarefree_stage_optimizer L hL hsq).2.1]
  exact herr

/-- Vanishing complete physical optimizer errors imply RH; no rate is required. -/
theorem riemannHypothesis_of_squarefree_optimizer_error_tendsto
    (L : ℕ → ℕ) (hL : ∀ j, 2 < L j) (hsq : ∀ j, Squarefree (L j))
    (hlim : Filter.Tendsto
      (fun j => 1 + 4 * Real.pi / arithmeticInverseCharge (L j) (divisorPackets (L j)))
      Filter.atTop (nhds 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_squarefree_arithmeticMinima
  intro ε hε
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨L j, hL j, hsq j, hj⟩

/-- The proposed endpoint gives RH conditionally. The endpoint itself is unproved. -/
theorem riemannHypothesis_of_squarefree_inverseCharge_tendsto
    (L : ℕ → ℕ) (hL : ∀ j, 2 < L j) (hsq : ∀ j, Squarefree (L j))
    (hlim : Filter.Tendsto
      (fun j => arithmeticInverseCharge (L j) (divisorPackets (L j)))
      Filter.atTop (nhds (-4 * Real.pi))) : RiemannHypothesis := by
  apply riemannHypothesis_of_squarefree_optimizer_error_tendsto L hL hsq
  have hden : (-4 * Real.pi : ℝ) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)
  have hfrac : Filter.Tendsto
      (fun j => 4 * Real.pi / arithmeticInverseCharge (L j) (divisorPackets (L j)))
      Filter.atTop (nhds (4 * Real.pi / (-4 * Real.pi))) :=
    tendsto_const_nhds.div hlim hden
  have ht := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
    Filter.atTop (nhds 1)).add hfrac
  have hv : (1 : ℝ) + 4 * Real.pi / (-4 * Real.pi) = 0 := by
    field_simp [ne_of_gt Real.pi_pos]
    ring
  simpa only [hv] using ht

end RiemannResearch.RH.Pareto.ArithmeticCoreRHCriterion
