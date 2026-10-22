/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.InverseSquareAbelTail
import RiemannResearch.Analysis.PeriodicWeightedMean
import RiemannResearch.RH.QSignedEnergyCertificate
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Mean-retaining complete-Q energy certificates

Independently developed in the authorized continuation, 18 October 2026.
Combines the exact Q energy split with the inverse-square Abel remainder.
The prefix, signed mean contribution, and complete centered infinite tail
are all retained. An application must supply the actual centered primitive
bound; this module assumes no unproved uniform arithmetic estimate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QMeanTailEnergyCertificate
open ZetaTwoHilbert ZetaTwoProbability QSignedEnergyCertificate
open RiemannResearch.Analysis.InverseSquareAbelTail
open RiemannResearch.Analysis.PeriodicWeightedMean

theorem energy_difference_centered_tail (f g : QHilbert) (K : ℕ) (μ B : ℝ)
    (hb : ∀ n,
      |partialSum (fun k => signedEnergy f g (k + K + 1) - μ) n| ≤ B) :
    |zetaTwo * (‖f‖^2 - ‖g‖^2) -
        (∑ n ∈ Finset.range (K + 1), signedEnergy f g n / (n : ℝ)^2) -
        μ * (∑' k, weight K k)| ≤ B / ((K + 1 : ℕ) : ℝ)^2 := by
  have hs : Summable (fun k => signedEnergy f g (k + K + 1) * weight K k) := by
    have h := (summable_nat_add_iff (K + 1)).mpr (signedEnergy_summable f g)
    simpa only [weight, mul_one_div, Nat.add_assoc] using h
  have h := centered_error_bound (fun k => signedEnergy f g (k + K + 1)) K μ B hs hb
  rw [energy_difference_prefix_tail f g K]
  simpa only [weight, mul_one_div, add_sub_cancel_left, Nat.add_assoc] using h

end RiemannResearch.RH.QMeanTailEnergyCertificate
