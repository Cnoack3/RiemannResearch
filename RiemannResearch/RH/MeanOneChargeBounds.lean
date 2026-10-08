/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.MeanOneSix
import RiemannResearch.RH.PhysicalCoreMonotonicity
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Unconditional actual mean-one charge bounds from conductor six

Every nonzero multiple of six contains the exact physical conductor-six
optimizer. The complete error therefore stays below its exact error, and
the negative inverse-core charge is bounded between -8*sqrt(3) and -4*pi.
These bounds and monotonicity do not prove limiting saturation.

-/

noncomputable section
open Matrix
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.MeanOneChargeBounds
open PhysicalPacketCore PhysicalCoreMonotonicity

theorem divisorPackets_six : divisorPackets 6 = MeanOneSix.packetSet := by
  decide

private theorem divisorPackets_six_odd :
    ∃ p ∈ divisorPackets 6, p.Prime ∧ 2 < p := by
  rw [divisorPackets_six]
  exact ⟨3, by simp [MeanOneSix.packetSet], by norm_num, by norm_num⟩

/-- Lower charge bound from the internally verified conductor-six optimizer.
Squarefreeness is unnecessary for this finite comparison. -/
theorem inverseCharge_ge_six (L : ℕ) (h6L : 6 ∣ L) (hL : 2 < L) :
    -8 * Real.sqrt 3 ≤ inverseCharge (divisorPackets L) := by
  have hmono := inverseCharge_mono (divisorPackets 6) (divisorPackets L)
    (divisorPackets_subset_of_dvd 6 L h6L (by omega))
    (divisorPackets_legal 6) (divisorPackets_legal L) divisorPackets_six_odd
  rw [divisorPackets_six, MeanOneSix.inverseCharge_six] at hmono
  exact hmono

/-- The complete physical interval is unconditional for every conductor
multiple of six; its upper endpoint remains strict at every finite stage. -/
theorem inverseCharge_bounds_of_six_dvd (L : ℕ) (h6L : 6 ∣ L) (hL : 2 < L) :
    -8 * Real.sqrt 3 ≤ inverseCharge (divisorPackets L) ∧
      inverseCharge (divisorPackets L) < -4 * Real.pi := by
  have hodd : ∃ p ∈ divisorPackets L, p.Prime ∧ 2 < p :=
    odd_prime_mono (divisorPackets 6) (divisorPackets L)
      (divisorPackets_subset_of_dvd 6 L h6L (by omega)) divisorPackets_six_odd
  exact ⟨inverseCharge_ge_six L h6L hL,
    inverseCharge_lt_neg_four_pi (divisorPackets L) (divisorPackets_legal L)
      hodd L (by omega) (divisorPackets_period L)⟩

/-- Exact physical complete error upper bound from conductor six. -/
theorem constrained_error_le_six (L : ℕ) (h6L : 6 ∣ L) (hL : 2 < L) :
    paretoError (synthesis (divisorPackets L) (constrainedOptimizer (divisorPackets L))) ≤
      1 - Real.pi / (2 * Real.sqrt 3) := by
  have he := constrained_physical_error_antitone (divisorPackets 6) (divisorPackets L)
    (divisorPackets_subset_of_dvd 6 L h6L (by omega))
    (divisorPackets_legal 6) (divisorPackets_legal L) divisorPackets_six_odd
  rw [divisorPackets_six, ← MeanOneSix.coefficients_eq_optimizer,
    MeanOneSix.minimum_error_six] at he
  exact he

/-- The same upper error bound expressed entirely through the actual charge. -/
theorem inverseCharge_error_le_six (L : ℕ) (h6L : 6 ∣ L) (hL : 2 < L) :
    1 + 4 * Real.pi / inverseCharge (divisorPackets L) ≤
      1 - Real.pi / (2 * Real.sqrt 3) := by
  have hodd : ∃ p ∈ divisorPackets L, p.Prime ∧ 2 < p :=
    odd_prime_mono (divisorPackets 6) (divisorPackets L)
      (divisorPackets_subset_of_dvd 6 L h6L (by omega)) divisorPackets_six_odd
  rw [← constrainedOptimizer_error (divisorPackets L) (divisorPackets_legal L) hodd]
  exact constrained_error_le_six L h6L hL

/-- Every nested divisor chain containing conductor six has an actual bounded
monotone charge. No squarefreeness assumption is required. -/
theorem divisor_chain_charge_monotone (L : ℕ → ℕ)
    (hdiv : ∀ n m : ℕ, n ≤ m → L n ∣ L m)
    (h6 : ∀ n : ℕ, 6 ∣ L n) (hL : ∀ n : ℕ, 2 < L n) :
    Monotone (fun n => inverseCharge (divisorPackets (L n))) := by
  intro n m hnm
  have hodd : ∃ p ∈ divisorPackets (L n), p.Prime ∧ 2 < p :=
    odd_prime_mono (divisorPackets 6) (divisorPackets (L n))
      (divisorPackets_subset_of_dvd 6 (L n) (h6 n) (by have := hL n; omega))
      divisorPackets_six_odd
  exact inverseCharge_mono (divisorPackets (L n)) (divisorPackets (L m))
    (divisorPackets_subset_of_dvd (L n) (L m) (hdiv n m hnm)
      (by have := hL m; omega))
    (divisorPackets_legal (L n)) (divisorPackets_legal (L m)) hodd

/-- Actual charge convergence to a limit in the closed finite interval.
The saturation endpoint `-4*pi` is not identified with this limit. -/
theorem exists_charge_limit_of_divisor_chain (L : ℕ → ℕ)
    (hdiv : ∀ n m : ℕ, n ≤ m → L n ∣ L m)
    (h6 : ∀ n : ℕ, 6 ∣ L n) (hL : ∀ n : ℕ, 2 < L n) :
    ∃ C : ℝ, C ∈ Set.Icc (-8 * Real.sqrt 3) (-4 * Real.pi) ∧
      Tendsto (fun n => inverseCharge (divisorPackets (L n))) atTop (𝓝 C) := by
  let f : ℕ → ℝ := fun n => inverseCharge (divisorPackets (L n))
  have hmono : Monotone f := divisor_chain_charge_monotone L hdiv h6 hL
  have hbound (n : ℕ) : -8 * Real.sqrt 3 ≤ f n ∧ f n < -4 * Real.pi :=
    inverseCharge_bounds_of_six_dvd (L n) (h6 n) (hL n)
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨-4 * Real.pi, ?_⟩
    rintro x ⟨n, rfl⟩
    exact (hbound n).2.le
  refine ⟨⨆ n, f n, ⟨?_, ?_⟩, ?_⟩
  · exact (hbound 0).1.trans (le_ciSup hbdd 0)
  · exact ciSup_le (fun n => (hbound n).2.le)
  · exact tendsto_atTop_ciSup hmono hbdd

end RiemannResearch.RH.Pareto.MeanOneChargeBounds
