/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ParetoPacketGreenGram
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite Ramanujan inversion with the conductor-one term

Source: S. Ramanujan, "On certain trigonometrical sums and their applications
in the theory of numbers", Trans. Cambridge Philos. Soc. 22 (1918), 259--276,
section 2, equations (2.6)--(2.7), for the divisor/Mobius transform; section 16
for cumulative Ramanujan sums.
https://ramanujan.sirinudi.org/Volumes/published/ram21.html

These exact finite identities support priority 14.6 of the user-provided
categorical atom/carry agenda. The cumulative identity explicitly retains
the conductor-one term. They do not assert weighted orthogonality.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

theorem ramanujanSum_divisor_sum (d n : ℕ) (hd : 0 < d) :
    (∑ q ∈ d.divisors, ramanujanSum q n) =
      if d ∣ n then (d : ℝ) else 0 := by
  exact (mobius_inversion (fun q => ramanujanSum q n)
    (fun q => if q ∣ n then (q : ℝ) else 0)).mpr
      (by intro q hq; rfl) d hd

theorem ramanujanPacket_prefix_with_constant (q k : ℕ) (hq : 0 < q) :
    ramanujanPacket q k = (if q = 1 then (k : ℝ) else 0) -
      ∑ m ∈ Finset.Ico 1 (k + 1), ramanujanSum q m := by
  by_cases hq1 : q = 1
  · subst q
    simp [ramanujanPacket, ramanujanSum, Pareto.residue, Nat.mod_one]
  · simpa [hq1] using ramanujanPacket_prefix q k (by omega)

end RiemannResearch.RH.Pareto
