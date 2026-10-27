/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ConductorLogEnvelope
import RiemannResearch.RH.QLegalMixedConductorReciprocal
import RiemannResearch.RH.QLegalMixedConductorPhysical
import RiemannResearch.RH.ResidueMidpointIncrement
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

/-!
# Unbounded actual prime-two increments inside legal squarefree subspaces

Source: LegalSubspaceProjectionObstruction.md. The coefficient and remainder
premises of the deterministic midpoint estimate are discharged by the actual
Q-Hilbert-space moment and projection theorems. These subspaces tie two legal
coefficients together; this result does not refute the canonical initial spans.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QLegalMixedConductor
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open ResidueMidpointIncrement

def midpointIncrement (d : ℕ) : ℝ :=
  |qSequence (actualCorrection d) (2 * ((d + 1) / 2)) -
    qSequence (actualCorrection d) ((d + 1) / 2)|

/-- Unconditional eventual lower bound for the actual correction at every
large odd conductor, not merely for an assumed scalar decomposition. -/
theorem midpointIncrement_lower_eventually :
    ∀ᶠ d : ℕ in atTop, d % 2 = 1 →
      ((7 / (36 * 303 ^ 2 : ℝ)) * 10 / 4) * Real.sqrt (d : ℝ) - 8 ≤
        midpointIncrement d := by
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    correctionCoefficient_lower_eventually, physicalRemainder_bounded_eventually]
    with d hd hβ hw
  intro hodd
  have hb (n : ℕ) : qSequence (actualCorrection d) n =
      correctionCoefficient d * 10 * Real.sqrt (d : ℝ) *
        ArithmeticCumulative.residueFraction d n + physicalRemainder d n := by
    simpa only [mul_assoc] using actualCorrection_decomposition d n (by omega)
  have h := increment_lower_of_sqrt_decomposition d hd hodd
    (qSequence (actualCorrection d)) (physicalRemainder d)
    (correctionCoefficient d) (7 / (36 * 303 ^ 2)) 4
    (by norm_num) hβ hb hw
  simpa only [midpointIncrement, show (2 : ℝ) * 4 = 8 by norm_num] using h

theorem midpointIncrement_large_eventually (M : ℝ) :
    ∀ᶠ d : ℕ in atTop, d % 2 = 1 → M ≤ midpointIncrement d := by
  let c : ℝ := (7 / (36 * 303 ^ 2 : ℝ)) * 10 / 4
  have hc : 0 < c := by norm_num [c]
  have hsqrt : Tendsto (fun d : ℕ => Real.sqrt (d : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [midpointIncrement_lower_eventually,
    (tendsto_atTop.1 hsqrt) ((M + 8) / c)] with d hlow hlarge
  intro hodd
  have hm : M + 8 ≤ c * Real.sqrt (d : ℝ) := by
    have hh := (div_le_iff₀ hc).mp hlarge
    simpa only [mul_comm] using hh
  have hl := hlow hodd
  change c * Real.sqrt (d : ℝ) - 8 ≤ midpointIncrement d at hl
  linarith only [hm, hl]

/-- Arbitrarily large physical increments occur for arbitrarily large prime
conductors in the actual legal mixed-conductor family. -/
theorem exists_prime_actualCorrection_large_increment (M : ℝ) (N : ℕ) :
    ∃ d : ℕ, d.Prime ∧ N ≤ d ∧ 3 < d ∧ M ≤ midpointIncrement d := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (midpointIncrement_large_eventually M)
  obtain ⟨d, hdge, hp⟩ := Nat.exists_infinite_primes (max (max T N) 4)
  have hdT : T ≤ d := (le_trans (le_max_left T N) (le_max_left (max T N) 4)).trans hdge
  have hdN : N ≤ d := (le_trans (le_max_right T N) (le_max_left (max T N) 4)).trans hdge
  have hd4 : 4 ≤ d := (le_max_right (max T N) 4).trans hdge
  have hodd : d % 2 = 1 := by
    have hm := Nat.mod_lt d (by norm_num : 0 < 2)
    by_contra h
    have he : d % 2 = 0 := by omega
    have heq := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero he)
    rcases heq with heq | heq <;> omega
  exact ⟨d, hp, hdN, by omega, hT d hdT hodd⟩

/-- No uniform physical prime-two increment bound holds over all members of
this legal squarefree family. Canonical-stage stability remains a different
question because these spaces are not the canonical increasing spans. -/
theorem no_uniform_prime_midpoint_increment :
    ¬ ∃ C : ℝ, ∀ d : ℕ, d.Prime → 3 < d → midpointIncrement d ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨d, hp, _, hd, hm⟩ := exists_prime_actualCorrection_large_increment (C + 1) 0
  have hu := hC d hp hd
  linarith

open RiemannResearch.Analysis.ConductorLogEnvelope

theorem midpointIncrement_exceeds_polylog_eventually (m : ℕ) (L : ℝ) :
    ∀ᶠ d : ℕ in atTop, d % 2 = 1 →
      L * Real.log 2 * (6 + Real.log ((d : ℝ) + 1)) ^ m < midpointIncrement d := by
  let c : ℝ := (7 / (36 * 303 ^ 2 : ℝ)) * 10 / 4
  have hc : 0 < c := by norm_num [c]
  have hinv : Tendsto (fun d : ℕ => 1 / Real.sqrt (d : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hratio : Tendsto (fun d : ℕ =>
      (L * Real.log 2 * (6 + Real.log ((d : ℝ) + 1)) ^ m + 8) /
        Real.sqrt (d : ℝ)) atTop (𝓝 0) := by
    have h := ((shifted_log_power_div_sqrt_tendsto_zero m).const_mul
      (L * Real.log 2)).add (hinv.const_mul 8)
    convert h using 1
    · funext d
      ring
    · ring
  filter_upwards [midpointIncrement_lower_eventually,
    eventually_ge_atTop (1 : ℕ), hratio.eventually (Iio_mem_nhds hc)]
    with d hlower hd hratio
  intro hodd
  have hdpos : 0 < d := by omega
  have hsp : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hdpos)
  have hm := (div_lt_iff₀ hsp).mp hratio
  have hl := hlower hodd
  change c * Real.sqrt (d : ℝ) - 8 ≤ midpointIncrement d at hl
  nlinarith only [hm, hl]

/-- Every fixed logarithmic allowance is violated by an arbitrarily large
prime conductor for the actual projected residual of this legal family. -/
theorem exists_prime_actualCorrection_exceeds_polylog
    (m : ℕ) (L : ℝ) (N : ℕ) :
    ∃ d : ℕ, d.Prime ∧ N ≤ d ∧ 3 < d ∧
      L * Real.log 2 * (6 + Real.log ((d : ℝ) + 1)) ^ m < midpointIncrement d := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (midpointIncrement_exceeds_polylog_eventually m L)
  obtain ⟨d, hdge, hp⟩ := Nat.exists_infinite_primes (max (max T N) 4)
  have hdT : T ≤ d := (le_trans (le_max_left T N) (le_max_left (max T N) 4)).trans hdge
  have hdN : N ≤ d := (le_trans (le_max_right T N) (le_max_left (max T N) 4)).trans hdge
  have hd4 : 4 ≤ d := (le_max_right (max T N) 4).trans hdge
  have hodd : d % 2 = 1 := by
    have hm := Nat.mod_lt d (by norm_num : 0 < 2)
    by_contra h
    have he : d % 2 = 0 := by omega
    have heq := hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero he)
    rcases heq with heq | heq <;> omega
  exact ⟨d, hp, hdN, by omega, hT d hdT hodd⟩

theorem no_uniform_prime_midpoint_polylog_increment (m : ℕ) :
    ¬ ∃ L : ℝ, ∀ d : ℕ, d.Prime → 3 < d →
      midpointIncrement d ≤ L * Real.log 2 * (6 + Real.log ((d : ℝ) + 1)) ^ m := by
  rintro ⟨L, hL⟩
  obtain ⟨d, hp, _, hd, hm⟩ := exists_prime_actualCorrection_exceeds_polylog m L 0
  exact (not_lt_of_ge (hL d hp hd)) hm

end RiemannResearch.RH.QLegalMixedConductor
