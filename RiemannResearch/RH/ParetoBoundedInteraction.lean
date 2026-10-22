/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.Linarith

/-!
# Bounded distinct-prime interaction cannot converge pointwise

Source: user-provided argument RH_Pareto_CRT_Enlargement_and_Dual_Obstruction_2026-09-07.md,
§6. We construct squarefree witnesses of arbitrarily large prime support
using Euclid's theorem. For each fixed interaction order, every allowed
packet combination has zero witness pairing; pointwise convergence to 1
would give a nonzero limit pairing. No norm or RH assumption is used.
-/

open scoped BigOperators
open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem exists_squarefree_large_prime_support (r : ℕ) :
    ∃ m : ℕ, 1 < m ∧ Squarefree m ∧ m.primeFactors.card = r+2 := by
  induction r with
  | zero =>
    refine ⟨6, by decide, ?_, ?_⟩
    · exact (Nat.squarefree_mul (by decide : Nat.Coprime 2 3)).mpr
        ⟨(show Nat.Prime 2 by decide).squarefree, (show Nat.Prime 3 by decide).squarefree⟩
    · rw [show 6 = 2*3 by rfl, Nat.primeFactors_mul (by decide) (by decide),
        (show Nat.Prime 2 by decide).primeFactors, (show Nat.Prime 3 by decide).primeFactors]
      decide
  | succ r ih =>
    obtain ⟨m, hm, hs, hc⟩ := ih
    obtain ⟨p, hlarge, hp⟩ := Nat.exists_infinite_primes (m+1)
    have hnd : ¬ p ∣ m := by
      intro h
      have := Nat.le_of_dvd (by omega : 0 < m) h
      omega
    have hnot : p ∉ m.primeFactors := by
      intro h
      have := Nat.le_of_mem_primeFactors h
      omega
    refine ⟨p*m, ?_, (Nat.squarefree_mul (hp.coprime_iff_not_dvd.mpr hnd)).mpr
      ⟨hp.squarefree, hs⟩, ?_⟩
    · have := hp.two_le
      nlinarith
    · rw [Nat.primeFactors_mul hp.ne_zero (by omega), hp.primeFactors]
      simp [hnot, hc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem mobiusDifference_tendsto {f : ℕ → ℕ → ℝ} {g : ℕ → ℝ}
    (m : ℕ) (h : ∀ k, Tendsto (fun t => f t k) atTop (nhds (g k))) :
    Tendsto (fun t => mobiusDifference m (f t)) atTop (nhds (mobiusDifference m g)) := by
  unfold mobiusDifference
  apply tendsto_finsetSum
  intro d _
  exact tendsto_const_nhds.mul ((h d).sub (h (d-1)))

theorem boundedPrimeSupport_no_pointwise_limit (r : ℕ)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
    (hs : ∀ t q, q ∈ s t → 0 < q ∧ q.primeFactors.card ≤ r) :
    ¬ (∀ k > 0, Tendsto (fun t => ∑ q ∈ s t, c t q*ramanujanPacket q k)
      atTop (nhds 1)) := by
  intro hlimit
  obtain ⟨m, hm, hsf, hcard⟩ := exists_squarefree_large_prime_support r
  let f : ℕ → ℕ → ℝ := fun t k => ∑ q ∈ s t, c t q*ramanujanPacket q k
  have hz (t : ℕ) : mobiusDifference m (f t) = 0 :=
    boundedPrimeSupport_dual_zero m r (s t) (c t) hm (by omega) (hs t)
  have hf0 (t : ℕ) : f t 0 = 0 := by simp [f, ramanujanPacket, residue]
  have hpoint (k : ℕ) : Tendsto (fun t => f t k) atTop
      (nhds (if k = 0 then 0 else 1)) := by
    by_cases hk : k = 0
    · subst k
      simpa only [hf0, ↓reduceIte] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (nhds 0))
    · simpa only [if_neg hk] using hlimit k (by omega)
  have hl := mobiusDifference_tendsto m hpoint
  rw [mobiusDifference_one m (by omega)] at hl
  simp only [hz] at hl
  have he : (0:ℝ) = ArithmeticFunction.moebius m := tendsto_nhds_unique tendsto_const_nhds hl
  have hn : ArithmeticFunction.moebius m ≠ 0 :=
    ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsf
  exact hn (by exact_mod_cast he.symm)

end
end RiemannResearch.RH.Pareto
