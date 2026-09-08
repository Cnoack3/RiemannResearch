import RiemannResearch.Analysis.PeriodicSquareBound
import RiemannResearch.RH.ThresholdSeedPowerCertificate5040
import RiemannResearch.RH.ThresholdInfiniteCertificate
import RiemannResearch.RH.ParetoProgressionTails
import RiemannResearch.RH.ThresholdDilationAlgebra
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic.IntervalCases

/-!
# An unconditional infinite weighted-error certificate

New rational seed-power dilation certificate, 8 September 2026.
Adapted from the previously verified period-36 analytic bridge.
This supplies an explicit legal witness for
the upper bound, with every positive index and the complete infinite tail.
It does not assert optimality or certify the constrained lower bound.
-/

open scoped BigOperators

namespace RiemannResearch.RH.TwoSeedThreshold

open Pareto

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The witness belongs to the actual two-seed finite legal span. -/
theorem legalWitness5040_mem_legalSeedSpan :
    legalWitness5040 ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  let L := legalSeedSpan ({2, 3} : Set ℕ)
  have hm (a m : ℕ) (ha : a ∈ ({2, 3} : Set ℕ)) (hm : 0 < m) :
      certificateGenerator a m ∈ L := by
    have he : certificateGenerator a m = dilation m (residue a) := by
      funext k
      exact certificateGenerator_eq_dilation a m k
    rw [he]
    exact dilation_generator_mem _ ha hm
  have he : legalWitness5040 = (1 / 10000 : ℝ) •
      ((5783 : ℝ) • certificateGenerator 2 1 +
       (1136 : ℝ) • certificateGenerator 2 2 +
       (-91 : ℝ) • certificateGenerator 2 3 +
       (604 : ℝ) • certificateGenerator 2 4 +
       (-618 : ℝ) • certificateGenerator 2 5 +
       (491 : ℝ) • certificateGenerator 2 6 +
       (-275 : ℝ) • certificateGenerator 2 7 +
       (462 : ℝ) • certificateGenerator 2 8 +
       (198 : ℝ) • certificateGenerator 2 9 +
       (-6 : ℝ) • certificateGenerator 2 10 +
       (19 : ℝ) • certificateGenerator 2 12 +
       (-135 : ℝ) • certificateGenerator 2 14 +
       (225 : ℝ) • certificateGenerator 2 15 +
       (39 : ℝ) • certificateGenerator 2 18 +
       (-39 : ℝ) • certificateGenerator 2 20 +
       (69 : ℝ) • certificateGenerator 2 21 +
       (20 : ℝ) • certificateGenerator 2 24 +
       (-39 : ℝ) • certificateGenerator 2 28 +
       (-27 : ℝ) • certificateGenerator 2 30 +
       (84 : ℝ) • certificateGenerator 2 35 +
       (71 : ℝ) • certificateGenerator 2 36 +
       (-63 : ℝ) • certificateGenerator 2 40 +
       (-14 : ℝ) • certificateGenerator 2 42 +
       (-34 : ℝ) • certificateGenerator 2 45 +
       (-25 : ℝ) • certificateGenerator 2 56 +
       (-2 : ℝ) • certificateGenerator 2 60 +
       (-9 : ℝ) • certificateGenerator 2 63 +
       (7 : ℝ) • certificateGenerator 2 70 +
       (-8 : ℝ) • certificateGenerator 2 72 +
       (7 : ℝ) • certificateGenerator 2 84 +
       (7 : ℝ) • certificateGenerator 2 90 +
       (-33 : ℝ) • certificateGenerator 2 105 +
       (12 : ℝ) • certificateGenerator 2 120 +
       (4 : ℝ) • certificateGenerator 2 126 +
       (5 : ℝ) • certificateGenerator 2 140 +
       (-13 : ℝ) • certificateGenerator 2 168 +
       (-8 : ℝ) • certificateGenerator 2 180 +
       (13 : ℝ) • certificateGenerator 2 210 +
       (-13 : ℝ) • certificateGenerator 2 252 +
       (7 : ℝ) • certificateGenerator 2 280 +
       (5 : ℝ) • certificateGenerator 2 315 +
       (-4 : ℝ) • certificateGenerator 2 360 +
       (-1 : ℝ) • certificateGenerator 2 420 +
       (4 : ℝ) • certificateGenerator 2 504 +
       (-3 : ℝ) • certificateGenerator 2 630 +
       (0 : ℝ) • certificateGenerator 2 840 +
       (1 : ℝ) • certificateGenerator 2 1260 +
       (0 : ℝ) • certificateGenerator 2 2520 +
       (3712 : ℝ) • certificateGenerator 3 1 +
       (700 : ℝ) • certificateGenerator 3 3 +
       (-378 : ℝ) • certificateGenerator 3 5 +
       (-167 : ℝ) • certificateGenerator 3 7 +
       (-48 : ℝ) • certificateGenerator 3 15 +
       (-80 : ℝ) • certificateGenerator 3 21 +
       (72 : ℝ) • certificateGenerator 3 35 +
       (10 : ℝ) • certificateGenerator 3 105) := by
    funext k
    simp only [legalWitness5040, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [he]
  apply L.smul_mem
  repeat' apply L.add_mem
  all_goals apply L.smul_mem
  all_goals apply hm <;> norm_num

/-- Periodicity supplies a finite uniform error bound without enumerating residues. -/
theorem legalWitness5040_error_bound (k : ℕ) :
    (1-legalWitness5040 k)^2 ≤
      ∑ r : Fin 5040, (1-legalWitness5040 r.val)^2 := by
  exact RiemannResearch.Analysis.periodic_square_error_bound
    legalWitness5040 5040 (by norm_num) legalWitness5040_periodic k

theorem legalWitness5040_add_multiple (r j : ℕ) :
    legalWitness5040 (r + 5040*j) = legalWitness5040 r := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : r + 5040 * (j + 1) = (r + 5040*j) + 5040 := by omega
    rw [h, legalWitness5040_periodic, ih]

/-- All positive indices are summable; the zero index is not silently dropped. -/
theorem legalWitness5040_error_summable :
    Summable (fun k : ℕ => positiveWeight (k+1) *
      (1 - legalWitness5040 (k+1)) ^ 2) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k+1)) :=
    positiveWeight_summable.comp_injective (by intro a b h; exact Nat.add_right_cancel h)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (legalWitness5040_error_bound _)
      (positiveWeight_nonneg _))
    (hw.mul_right _)

/-- Exact regrouping by the 5040 positive residue representatives `1,...,5040`.
The representative 5040 includes the full zero congruence class. -/
theorem legalWitness5040_exact_error :
    (∑' k : ℕ, positiveWeight (k+1) * (1 - legalWitness5040 (k+1)) ^ 2) =
      ∑ r : Fin 5040, progressionWeight 5040 (r.val+1) *
        (1 - legalWitness5040 (r.val+1)) ^ 2 := by
  rw [Nat.sumByResidueClasses legalWitness5040_error_summable 5040]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ∑' j : ℕ, positiveWeight ((r.val+1)+5040*j) *
        (1 - legalWitness5040 (r.val+1)) ^ 2 := by
      apply tsum_congr
      intro j
      have h : r.val + 5040*j + 1 = (r.val+1)+5040*j := by omega
      rw [h, legalWitness5040_add_multiple]
    _ = _ := by rw [tsum_mul_right]; rfl

/-- The complete weighted sequence squared error is strictly below `0.039`.
This is unconditional: the analytic progression tails and periodic regrouping
have been discharged, not supplied as hypotheses. -/
theorem legalWitness5040_full_error_lt :
    (∑' k : ℕ, positiveWeight (k+1) * (1 - legalWitness5040 (k+1)) ^ 2) <
      (39 : ℝ) / 1000 := by
  rw [legalWitness5040_exact_error]
  apply legalWitness5040_error_lt_of_weights
  intro r
  have h := progressionWeight_upper_two 5040 (r.val+1) (by norm_num)
  convert h using 1 <;>
    simp only [residueUpper5040, positiveWeight, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] <;> ring

end RiemannResearch.RH.TwoSeedThreshold
