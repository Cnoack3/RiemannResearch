/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeResampling
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QPrimeResamplingFormula
import RiemannResearch.RH.PrimeResamplingCore
import RiemannResearch.Analysis.InvariantProjectionCommutation
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Actual distinct-prime resampling commutes

The proof uses arithmetic covariance of replacement along a different
prime, followed by exact orthogonal-projection geometry. There is no
independence provider and no finite truncation of the geometric average.
-/

noncomputable section
namespace RiemannResearch.RH.QPrimeResampling
open ZetaTwoHilbert PrimeResampling
open RiemannResearch.Analysis.InvariantProjectionCommutation

/-- Averaging one prime preserves invariance in a distinct prime coordinate. -/
theorem C_preserves_primeInvariant (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (f : QHilbert) (hf : f ∈ primeInvariant q) :
    C p f ∈ primeInvariant q := by
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · rw [qSequence_C p (q * n) hp (mul_ne_zero hq.ne_zero hn), qSequence_C p n hp hn]
    apply tsum_congr
    intro k
    rw [replaceValuation_mul_other_prime p q n k hp hq hpq hn, hf]

/-- Full-countable resampling projections commute for all primes. -/
theorem C_commute (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (f : QHilbert) :
    C p (C q f) = C q (C p f) := by
  by_cases hpq : p = q
  · subst q
    rfl
  · exact map_starProjection_eq (primeInvariant q) (C p) (C_selfAdjoint p)
      (C_preserves_primeInvariant p q hp hq hpq) f

end RiemannResearch.RH.QPrimeResampling
