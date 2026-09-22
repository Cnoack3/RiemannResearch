/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.IsolatedPrimeReciprocalSum
import RiemannResearch.RH.CanonicalMobiusConditionalHead

/-!
# Every positive finite reciprocal Möbius sum is nonzero

Source: the structural continuation requested in Section 11 of the user's
Pareto capacity handoff. This discharges finite nonvanishing by Bertrand's
postulate and integer denominator clearing. It does not assert the PNT limit.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory

/-- Every positive finite reciprocal Möbius sum is nonzero. No PNT or RH
hypothesis is required. -/
theorem mobiusReciprocalSum_ne_zero {N : ℕ} (hN : 0 < N) :
    mobiusReciprocalSum N ≠ 0 := by
  by_cases hN1 : N = 1
  · subst N
    norm_num [mobiusReciprocalSum]
  obtain ⟨p, hp, hpN, hN2p⟩ := exists_prime_upper_half (by omega : 2 ≤ N)
  apply reciprocal_sum_ne_zero_of_isolated_prime (Finset.Icc 1 N)
    ArithmeticFunction.moebius p hp
  · exact Finset.mem_Icc.mpr ⟨hp.pos, hpN⟩
  · intro d hd
    exact (Finset.mem_Icc.mp hd).1
  · intro d hd hpd
    obtain ⟨k, hk⟩ := hpd
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
    have hkpos : 0 < k := by nlinarith
    have hklt : k < 2 := by nlinarith
    have hk1 : k = 1 := by omega
    simpa [hk1] using hk
  · exact ArithmeticFunction.moebius_apply_prime hp

end RiemannResearch.RH.Pareto
