/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/

import RiemannResearch.Analysis.PositiveArithmeticPrefix
import RiemannResearch.RH.DyadicFourierAnalyticTargets
import RiemannResearch.RH.DyadicNormalizationElementaryBounds

/-!
# Exact finite arithmetic before the uniform discrepancy estimate

Source: continuation of the user-provided
`FourierBridgeLeanVerification20260910(1).md`. The finite Abel formula is
standard summation by parts, rather than a new analytic estimate.

The identities here use the actual Möbius coefficients, preserve the atom at
one, and preserve the continuous compensator beginning at one. The finite
Abel identity isolates genuine ordinary Mertens partial sums before any
analytic bound is invoked. No quantitative Mertens theorem or final uniform
arithmetic discrepancy estimate is asserted.
-/

open scoped BigOperators
open RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The actual damped Möbius summatory function at an integer cutoff. -/
def dampedMobiusSummatory (ε : ℝ) (N : ℕ) : ℝ :=
  positiveArithmeticPrefix (dampedMobiusWeight ε) N

/-- The ordinary Mertens function agrees exactly with the positive prefix
at integer cutoffs. -/
theorem classicalMertensFunction_natCast (N : ℕ) :
    classicalMertensFunction (N : ℝ) =
      positiveArithmeticPrefix (fun n => (ArithmeticFunction.moebius n : ℝ)) N := by
  simp [classicalMertensFunction, positiveArithmeticPrefix]

/-- Actual weighted partial summation: the remaining arithmetic cancellation
is expressed in ordinary Mertens partial sums, with the endpoint intact. -/
theorem dampedMobiusSummatory_eq_mertens_abel (ε : ℝ) (N : ℕ) :
    dampedMobiusSummatory ε N =
      classicalMertensFunction (N : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-ε) +
        ∑ n ∈ Finset.range N,
          classicalMertensFunction ((n + 1 : ℕ) : ℝ) *
            (((n + 1 : ℕ) : ℝ) ^ (-ε) - ((n + 2 : ℕ) : ℝ) ^ (-ε)) := by
  simp_rw [classicalMertensFunction_natCast]
  exact positiveArithmeticPrefix_weighted_abel
    (fun n => (ArithmeticFunction.moebius n : ℝ))
    (fun n => (n : ℝ) ^ (-ε)) N

/-- The divisor-convolution prefix, now with the same positive-index
convention as the discrepancy target. -/
theorem dampedMobiusPrefix_eq_positive_coefficient_sum (ε : ℝ) (N : ℕ) :
    dampedMobiusPrefix ε N =
      ∑ n ∈ Finset.range N, dampedDivisorCoefficient ε (n + 1) := by
  rw [dampedMobiusPrefix_eq_sum_divisors]
  change (∑ n ∈ Finset.range (N + 1), dampedDivisorCoefficient ε n) = _
  rw [Finset.sum_range_succ']
  simp

/-- Summation of the actual signed coefficients subtracts precisely one atom
at every positive integer cutoff. -/
theorem normalizedSignedCoefficient_sum_prefix (ε A : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.range N, normalizedSignedCoefficient ε A (n + 1)) =
      A * dampedMobiusPrefix ε N - 1 := by
  simp only [normalizedSignedCoefficient, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [← dampedMobiusPrefix_eq_positive_coefficient_sum]
  have hdelta : (∑ n ∈ Finset.range N, (if n + 1 = 1 then (1 : ℝ) else 0)) = 1 := by
    simp [show 0 < N by omega]
  rw [hdelta]

/-- Exact reduction of the discrepancy to the genuine floor convolution.
Both the signed atom and the compensator's lower endpoint remain visible. -/
theorem dyadicSignedArithmeticDiscrepancy_eq_prefix (ε : ℝ) {x : ℝ}
    (hx : 1 ≤ x) :
    dyadicSignedArithmeticDiscrepancy ε x =
      dyadicRegularizationNormalization ε * dampedMobiusPrefix ε (Nat.floor x) -
        1 - dyadicSignedArithmeticPoleResidue ε * (x - 1) := by
  have hfloor : 1 ≤ Nat.floor x := by
    simpa using Nat.floor_mono hx
  unfold dyadicSignedArithmeticDiscrepancy
  rw [normalizedSignedCoefficient_sum_prefix ε _ hfloor]

/-- The exact relation between the real normalization and the continuous
residue; no complex zeta identification is needed. -/
theorem dyadicRegularizationNormalization_eq_zeta_mul_residue (ε : ℝ) :
    dyadicRegularizationNormalization ε =
      regularizationZetaSeries ε * dyadicSignedArithmeticPoleResidue ε := by
  unfold dyadicRegularizationNormalization dyadicSignedArithmeticPoleResidue
  ring

/-- The arithmetic core is centered at the integer conductor. The fractional
cutoff correction, endpoint compensator, and atom are all explicit. -/
theorem dyadicSignedArithmeticDiscrepancy_eq_centered_prefix {ε : ℝ}
    (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    dyadicSignedArithmeticDiscrepancy ε x =
      dyadicRegularizationNormalization ε *
        (dampedMobiusPrefix ε (Nat.floor x) -
          (Nat.floor x : ℝ) / regularizationZetaSeries ε) +
        dyadicSignedArithmeticPoleResidue ε * ((Nat.floor x : ℝ) - x + 1) - 1 := by
  have hZ : regularizationZetaSeries ε ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (one_le_regularizationZetaSeries hε))
  rw [dyadicSignedArithmeticDiscrepancy_eq_prefix ε hx,
    dyadicRegularizationNormalization_eq_zeta_mul_residue]
  field_simp [hZ]
  ring

/-- The exact compensator has nonnegative mass bounded by the damping. -/
theorem dyadicSignedArithmeticPoleResidue_bounds {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ dyadicSignedArithmeticPoleResidue ε ∧
      dyadicSignedArithmeticPoleResidue ε ≤ ε := by
  have hL : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hfactor := dampedPrimeFactor_bounds hε (show Nat.Prime 3 by decide)
  have hlog := dampedPrimeFactor_le_mul_log ε (show Nat.Prime 3 by decide)
  constructor
  · exact div_nonneg hfactor.1 hL.le
  · exact (div_le_iff₀ hL).mpr hlog

/-- The difference between the real cutoff and its integer floor leaves a
positive endpoint factor at most one. -/
theorem signedArithmeticCutoffFactor_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 < (Nat.floor x : ℝ) - x + 1 ∧
      (Nat.floor x : ℝ) - x + 1 ≤ 1 := by
  have hlo := Nat.floor_le (show 0 ≤ x by linarith)
  have hhi := Nat.lt_floor_add_one x
  constructor <;> linarith

/-- The complete endpoint correction includes the negative atom. Its sign
and its uniform interval are retained before taking an absolute value. -/
theorem dyadicSignedArithmeticEndpointCorrection_bounds {ε x : ℝ}
    (hε : 0 ≤ ε) (hx : 1 ≤ x) :
    -1 ≤ dyadicSignedArithmeticPoleResidue ε * ((Nat.floor x : ℝ) - x + 1) - 1 ∧
      dyadicSignedArithmeticPoleResidue ε * ((Nat.floor x : ℝ) - x + 1) - 1 ≤ ε - 1 := by
  obtain ⟨hκ0, hκε⟩ := dyadicSignedArithmeticPoleResidue_bounds hε
  obtain ⟨hF0, hF1⟩ := signedArithmeticCutoffFactor_bounds hx
  constructor
  · nlinarith [mul_nonneg hκ0 hF0.le]
  · have hmul := mul_le_mul_of_nonneg_left hF1 hκ0
    linarith

/-- The real-cutoff discrepancy differs from the genuine centered integer
prefix by at most one throughout the admissible damping range. -/
theorem dyadicSignedArithmeticDiscrepancy_centered_prefix_error {ε x : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hx : 1 ≤ x) :
    |dyadicSignedArithmeticDiscrepancy ε x -
      dyadicRegularizationNormalization ε *
        (dampedMobiusPrefix ε (Nat.floor x) -
          (Nat.floor x : ℝ) / regularizationZetaSeries ε)| ≤ 1 := by
  rw [dyadicSignedArithmeticDiscrepancy_eq_centered_prefix hε hx]
  have hc := dyadicSignedArithmeticEndpointCorrection_bounds hε.le hx
  apply abs_le.mpr
  constructor <;> linarith

/-- For every nonnegative damping, the actual weighted Möbius prefix is
bounded by any common bound for its ordinary Mertens prefixes. The estimate
is uniform in the damping and contains no factor `1/ε`. -/
theorem dampedMobiusSummatory_bound_of_mertens_prefix {ε : ℝ} (hε : 0 ≤ ε)
    (N : ℕ) (B : ℝ)
    (hM : ∀ n : ℕ, n ≤ N → |classicalMertensFunction (n : ℝ)| ≤ B) :
    |dampedMobiusSummatory ε N| ≤ B := by
  have hA : ∀ n : ℕ, n ≤ N →
      |positiveArithmeticPrefix (fun n => (ArithmeticFunction.moebius n : ℝ)) n| ≤ B := by
    intro n hn
    simpa only [classicalMertensFunction_natCast] using hM n hn
  have hg : 0 ≤ ((N + 1 : ℕ) : ℝ) ^ (-ε) := Real.rpow_nonneg (by positivity) _
  have hmono : ∀ n : ℕ, n < N →
      ((n + 2 : ℕ) : ℝ) ^ (-ε) ≤ ((n + 1 : ℕ) : ℝ) ^ (-ε) := by
    intro n hn
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · exact_mod_cast (show n + 1 ≤ n + 2 by omega)
    · exact neg_nonpos.mpr hε
  change |positiveArithmeticPrefix
    (fun n => (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-ε)) N| ≤ B
  simpa only [Nat.cast_one, Real.one_rpow, mul_one] using positiveArithmeticPrefix_weighted_bound
      (fun n => (ArithmeticFunction.moebius n : ℝ))
      (fun n => (n : ℝ) ^ (-ε)) N B hA hg hmono

end
end RiemannResearch.RH.Pareto
