/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.SquarefreeSignedCorrelationCriterion
import RiemannResearch.RH.SquarefreePrimeHeadStage
import RiemannResearch.RH.PrimeHeadRefinedCertificates
import RiemannResearch.RH.QPrimeBalancedExactHead
import RiemannResearch.Analysis.NormalizedSignedEnergy
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Actual least-prime heads: signed correlation and reciprocal-mass criterion

Source: user-provided capacity and energy agenda, 24 October 2026.
All finite-legality and complete-energy certificate hypotheses are discharged
for the specified arithmetic family. The two remaining analytic inputs are
divergent reciprocal mass and a vanishing normalized signed cross budget.
Neither input is supplied unconditionally here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QPrimeBalancedExactHead
open Pareto RiemannResearch.Analysis
open SquarefreePacketCapacity

theorem anchorPrime_monotone : Monotone anchorPrime := by
  intro m n hmn
  have hn := anchorPrime_spec n
  change Nat.find (Nat.exists_infinite_primes (m+1)) ≤ anchorPrime n
  exact Nat.find_min' _ ⟨by omega, hn.2⟩

theorem nextPrimeResidual_energy_pos (N : ℕ) :
    0 < Pareto.AmplitudeCertificates.energy (nextPrimeResidual N) := by
  rw [nextPrimeResidual_energy_eq]
  have hf := legal_error_floor (anchorPrime N-1) (paretoNextPrimeHead N)
    (paretoNextPrimeHead_mem_stage N)
  have hk := (kappa_bounds (anchorPrime N-1)).2
  linarith

theorem nextPrimeCertificate_ge_one (N : ℕ) (hN : 0 < N) :
    1 ≤ nextPrimeCertificate N :=
  (le_max_left _ _).trans (nextPrimeCertificate_bounds N hN).1

/-- Certified mass diverges exactly when regularized actual-energy mass does.
The finite computation needed for each certificate loses at most a factor two. -/
theorem nextPrimeCertificate_mass_tendsto_iff
    (N : ℕ → ℕ) (hN : ∀ j, 0 < N j) :
    Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m, (nextPrimeCertificate (N j))⁻¹)
      atTop atTop ↔
    Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m,
      (max 1 (‖hilbertOne - paretoNextPrimeHead (N j)‖ ^ 2))⁻¹) atTop atTop := by
  classical
  have hc := summable_iff_not_tendsto_nat_atTop_of_nonneg
    (fun j => inv_nonneg.mpr
      (zero_le_one.trans (nextPrimeCertificate_ge_one (N j) (hN j))))
  have he := summable_iff_not_tendsto_nat_atTop_of_nonneg
    (fun j => inv_nonneg.mpr
      (zero_le_one.trans (le_max_left 1 (‖hilbertOne - paretoNextPrimeHead (N j)‖ ^ 2))))
  have hs := nextPrimeCertificate_reciprocal_summable_iff N hN
  simpa only [not_not] using not_congr (hc.symm.trans (hs.trans he))

/-- Actual-family conditional RH reduction. Positivity, full P energies and
the exact finite squarefree packet stage are proved internally. -/
theorem riemannHypothesis_of_nextPrime_signed_correlation_budget
    (N : ℕ → ℕ) (hN : Monotone N) (hpos : ∀ j, 0 < N j) (b : ℕ → ℝ)
    (hcross : ∀ᶠ m in atTop,
      reciprocalEnergyCross (fun j => paretoNextPrimeHead (N j) - hilbertOne)
        (fun j => nextPrimeCertificate (N j)) m ≤ b m)
    (hbudget : Tendsto b atTop (𝓝 0))
    (hmass : Tendsto (fun m : ℕ =>
      ∑ j ∈ Finset.range m, (nextPrimeCertificate (N j))⁻¹) atTop atTop) :
    RiemannHypothesis := by
  have hstage : Monotone (fun j => anchorPrime (N j) - 1) := by
    intro i j hij
    exact Nat.sub_le_sub_right (anchorPrime_monotone (hN hij)) 1
  have hA (j : ℕ) : 0 < nextPrimeCertificate (N j) :=
    zero_lt_one.trans_le (nextPrimeCertificate_ge_one (N j) (hpos j))
  have henergy (j : ℕ) :
      ‖paretoNextPrimeHead (N j) - hilbertOne‖ ^ 2 ≤ nextPrimeCertificate (N j) := by
    rw [norm_sub_rev]
    exact (le_max_right _ _).trans (nextPrimeCertificate_bounds (N j) (hpos j)).1
  exact riemannHypothesis_of_signed_correlation_budget
    (fun j => anchorPrime (N j)-1) hstage (fun j => paretoNextPrimeHead (N j))
    (fun j => paretoNextPrimeHead_mem_stage (N j)) (fun j => nextPrimeCertificate (N j))
    hA henergy b hcross hbudget hmass

/-- The same actual-family criterion can state its mass hypothesis using the
true complete errors; the finite certification introduces no new divergence
obligation. The signed correlations still use the specified certified weights. -/
theorem riemannHypothesis_of_nextPrime_actual_energy_mass
    (N : ℕ → ℕ) (hN : Monotone N) (hpos : ∀ j, 0 < N j) (b : ℕ → ℝ)
    (hcross : ∀ᶠ m in atTop,
      reciprocalEnergyCross (fun j => paretoNextPrimeHead (N j) - hilbertOne)
        (fun j => nextPrimeCertificate (N j)) m ≤ b m)
    (hbudget : Tendsto b atTop (𝓝 0))
    (hmass : Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m,
      (max 1 (‖hilbertOne - paretoNextPrimeHead (N j)‖ ^ 2))⁻¹) atTop atTop) :
    RiemannHypothesis :=
  riemannHypothesis_of_nextPrime_signed_correlation_budget N hN hpos b hcross hbudget
    ((nextPrimeCertificate_mass_tendsto_iff N hpos).mpr hmass)

end RiemannResearch.RH.QPrimeBalancedExactHead
