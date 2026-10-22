/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SignedAveragedSquareDamping
import RiemannResearch.RH.DampedMobiusSignedAbelGrowth
import RiemannResearch.RH.BurnolFiniteEnergyReduction

/-!
# Canonical damped energy from averaged signed raw prefixes

The Dini hypothesis is on the norms of the complete signed raw Hilbert sums.
It is not a termwise absolute coefficient estimate. Abel summation provides
frequently bounded damped cutoffs, and the existing scalar coordinate limits
then give finite energy of the actual canonical centered discrepancy.

No vanishing-boundary hypothesis is required for this finite-energy theorem.
No full natural-order convergence is asserted from Dini summability alone.
The Dini input remains an open arithmetic cancellation condition in the
unresolved damping range.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Arithmetic version of the averaged Abel bound, retaining the full signed
raw residue prefix before its norm is taken. -/
theorem arithmeticFloorHilbertPartial_power_damping_frequently_bounded
    (w : ℕ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hdini : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^(-ε - 1) *
      ‖arithmeticFloorHilbertPartial w (n + 1)‖)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ᶠ N : ℕ in atTop,
      ‖arithmeticFloorHilbertPartial
        (fun d => w d * (d : ℝ)^(-ε)) (N + 1)‖ ≤ B := by
  have hd : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^(-ε - 1) *
      ‖RiemannResearch.Analysis.signedVectorPrefix (arithmeticResidueTerm w) (n + 1)‖) := by
    simpa only [arithmeticFloorHilbertPartial, norm_neg,
      RiemannResearch.Analysis.signedVectorPrefix] using hdini
  obtain ⟨B, hB, hfreq⟩ :=
    RiemannResearch.Analysis.signedVector_power_damped_frequently_bounded_of_dini
      (arithmeticResidueTerm w) hε hd
  refine ⟨B, hB, hfreq.mono ?_⟩
  intro N hN
  simpa only [arithmeticFloorHilbertPartial, norm_neg,
    arithmeticResidueTerm_power_damping] using hN

/-- A sparse bounded subsequence of damped Hilbert norms already gives the
actual canonical finite energy by the unconditional scalar coordinate limit.
The exact squared bound survives the limit without a comparison loss. -/
theorem dampedMobius_energy_of_frequently_bounded_cutoff_norm
    {ε B : ℝ} (hε : 0 < ε) (hB : 0 ≤ B)
    (hfreq : ∃ᶠ N : ℕ in atTop,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (N + 1)‖ ≤ B) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2) ∧
    (∑' n : ℕ, positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2) ≤ B^2 := by
  have hb (H : ℕ) : (∑ n ∈ Finset.range H, positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2) ≤ B^2 := by
    have ht := (dampedMobius_partial_head_tendsto hε H).comp
      (tendsto_add_atTop_nat 1)
    have hf : ∃ᶠ N : ℕ in atTop, paretoHeadPairing H
        (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (N + 1))
        (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (N + 1)) ≤ B^2 := by
      apply hfreq.mono
      intro N hN
      apply (paretoHeadPairing_self_le H _).trans
      nlinarith [norm_nonneg (arithmeticFloorHilbertPartial
        (dampedMobiusWeight ε) (N + 1))]
    by_contra hn
    have hlt := lt_of_not_ge hn
    obtain ⟨N, hle, hgt⟩ :=
      (hf.and_eventually (ht.eventually (lt_mem_nhds hlt))).exists
    exact (not_lt_of_ge hle) hgt
  have hn (n : ℕ) : 0 ≤ positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2 :=
    mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩

/-- Averaged signed raw-prefix cancellation suffices for actual finite energy
at a fixed positive damping. All arithmetic content is explicit in `hdini`.
Unlike an ordered-convergence criterion, there is no extra boundary limit. -/
theorem dampedMobius_energy_of_raw_signed_dini
    {ε : ℝ} (hε : 0 < ε)
    (hdini : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ)^(-ε - 1) *
      ‖arithmeticFloorHilbertPartial
        (fun d => (ArithmeticFunction.moebius d : ℝ)) (n + 1)‖)) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2) := by
  obtain ⟨B, hB, hfreq⟩ :=
    arithmeticFloorHilbertPartial_power_damping_frequently_bounded
      (fun d => (ArithmeticFunction.moebius d : ℝ)) hε.le hdini
  exact (dampedMobius_energy_of_frequently_bounded_cutoff_norm hε hB hfreq).1

/-- Summable logarithmically weighted raw signed energies imply canonical
finite energy at positive damping, without a pointwise bound on cutoffs. -/
theorem dampedMobius_energy_of_log_weighted_raw_signed_sq
    {ε q : ℝ} (hε : 0 < ε) (hq : 1 < q)
    (henergy : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ)^(-2 * ε - 1) *
        Real.log (2 * ((n + 1 : ℕ) : ℝ))^q *
          ‖arithmeticFloorHilbertPartial
            (fun d => (ArithmeticFunction.moebius d : ℝ)) (n + 1)‖^2)) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2) := by
  apply dampedMobius_energy_of_raw_signed_dini hε
  have he : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ)^(-2 * ε - 1) *
        Real.log (2 * ((n + 1 : ℕ) : ℝ))^q *
          ‖RiemannResearch.Analysis.signedVectorPrefix
            (arithmeticResidueTerm (fun d => (ArithmeticFunction.moebius d : ℝ)))
              (n + 1)‖^2) := by
    simpa only [arithmeticFloorHilbertPartial, norm_neg,
      RiemannResearch.Analysis.signedVectorPrefix] using henergy
  simpa only [arithmeticFloorHilbertPartial, norm_neg,
    RiemannResearch.Analysis.signedVectorPrefix] using
      RiemannResearch.Analysis.signedVector_dini_of_log_weighted_sq
        (arithmeticResidueTerm (fun d => (ArithmeticFunction.moebius d : ℝ))) hq he



/-- Conditional RH consequence: the complete signed raw Dini sums need only
be finite separately at positive dampings approaching zero. No common bound
across damping stages is assumed. The Dini hypotheses remain open. -/
theorem riemannHypothesis_of_raw_signed_dini_sequence
    (ε : ℕ → ℝ) (hpos : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0))
    (hdini : ∀ j, Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ)^(-ε j - 1) *
        ‖arithmeticFloorHilbertPartial
          (fun d => (ArithmeticFunction.moebius d : ℝ)) (n + 1)‖)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_centered_damped_square_summable ε hpos hlim
  intro j
  exact ⟨(1 / riemannZeta (1 + (ε j : ℂ))).re,
    dampedMobius_energy_of_raw_signed_dini (hpos j) (hdini j)⟩

end RiemannResearch.RH.Pareto
