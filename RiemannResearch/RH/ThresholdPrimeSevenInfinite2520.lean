import RiemannResearch.Analysis.PeriodicSquareBound
import RiemannResearch.RH.ThresholdPrimeSevenCertificate2520
import RiemannResearch.RH.ThresholdInfiniteCertificate
import RiemannResearch.RH.ParetoProgressionTails
import RiemannResearch.RH.ThresholdDilationAlgebra
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic.IntervalCases

/-!
# An unconditional infinite weighted-error certificate

New rational prime-seven dilation certificate, 8 September 2026.
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
theorem legalWitness2520_mem_legalSeedSpan :
    legalWitness2520 ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  let L := legalSeedSpan ({2, 3} : Set ℕ)
  have hm (a m : ℕ) (ha : a ∈ ({2, 3} : Set ℕ)) (hm : 0 < m) :
      certificateGenerator a m ∈ L := by
    have he : certificateGenerator a m = dilation m (residue a) := by
      funext k
      exact certificateGenerator_eq_dilation a m k
    rw [he]
    exact dilation_generator_mem _ ha hm
  have he : legalWitness2520 = (1 / 10000 : ℝ) •
      ((5653 : ℝ) • certificateGenerator 2 1 +
       (1043 : ℝ) • certificateGenerator 2 2 +
       (-47 : ℝ) • certificateGenerator 2 3 +
       (451 : ℝ) • certificateGenerator 2 4 +
       (-613 : ℝ) • certificateGenerator 2 5 +
       (487 : ℝ) • certificateGenerator 2 6 +
       (-162 : ℝ) • certificateGenerator 2 7 +
       (349 : ℝ) • certificateGenerator 2 9 +
       (-15 : ℝ) • certificateGenerator 2 10 +
       (42 : ℝ) • certificateGenerator 2 12 +
       (-140 : ℝ) • certificateGenerator 2 14 +
       (186 : ℝ) • certificateGenerator 2 15 +
       (23 : ℝ) • certificateGenerator 2 18 +
       (-32 : ℝ) • certificateGenerator 2 20 +
       (75 : ℝ) • certificateGenerator 2 21 +
       (-25 : ℝ) • certificateGenerator 2 28 +
       (-49 : ℝ) • certificateGenerator 2 30 +
       (45 : ℝ) • certificateGenerator 2 35 +
       (63 : ℝ) • certificateGenerator 2 36 +
       (-17 : ℝ) • certificateGenerator 2 42 +
       (-53 : ℝ) • certificateGenerator 2 45 +
       (-5 : ℝ) • certificateGenerator 2 60 +
       (-31 : ℝ) • certificateGenerator 2 63 +
       (18 : ℝ) • certificateGenerator 2 70 +
       (2 : ℝ) • certificateGenerator 2 84 +
       (13 : ℝ) • certificateGenerator 2 90 +
       (-23 : ℝ) • certificateGenerator 2 105 +
       (6 : ℝ) • certificateGenerator 2 126 +
       (6 : ℝ) • certificateGenerator 2 140 +
       (-7 : ℝ) • certificateGenerator 2 180 +
       (8 : ℝ) • certificateGenerator 2 210 +
       (-9 : ℝ) • certificateGenerator 2 252 +
       (6 : ℝ) • certificateGenerator 2 315 +
       (-1 : ℝ) • certificateGenerator 2 420 +
       (-1 : ℝ) • certificateGenerator 2 630 +
       (1 : ℝ) • certificateGenerator 2 1260 +
       (3810 : ℝ) • certificateGenerator 3 1 +
       (734 : ℝ) • certificateGenerator 3 3 +
       (-251 : ℝ) • certificateGenerator 3 5 +
       (-113 : ℝ) • certificateGenerator 3 7 +
       (-47 : ℝ) • certificateGenerator 3 15 +
       (-37 : ℝ) • certificateGenerator 3 21 +
       (51 : ℝ) • certificateGenerator 3 35 +
       (1 : ℝ) • certificateGenerator 3 105) := by
    funext k
    simp only [legalWitness2520, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [he]
  apply L.smul_mem
  repeat' apply L.add_mem
  all_goals apply L.smul_mem
  all_goals apply hm <;> norm_num

/-- Periodicity supplies a finite uniform error bound without enumerating residues. -/
theorem legalWitness2520_error_bound (k : ℕ) :
    (1-legalWitness2520 k)^2 ≤
      ∑ r : Fin 2520, (1-legalWitness2520 r.val)^2 := by
  exact RiemannResearch.Analysis.periodic_square_error_bound
    legalWitness2520 2520 (by norm_num) legalWitness2520_periodic k

theorem legalWitness2520_add_multiple (r j : ℕ) :
    legalWitness2520 (r + 2520*j) = legalWitness2520 r := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : r + 2520 * (j + 1) = (r + 2520*j) + 2520 := by omega
    rw [h, legalWitness2520_periodic, ih]

/-- All positive indices are summable; the zero index is not silently dropped. -/
theorem legalWitness2520_error_summable :
    Summable (fun k : ℕ => positiveWeight (k+1) *
      (1 - legalWitness2520 (k+1)) ^ 2) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k+1)) :=
    positiveWeight_summable.comp_injective (by intro a b h; exact Nat.add_right_cancel h)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (legalWitness2520_error_bound _)
      (positiveWeight_nonneg _))
    (hw.mul_right _)

/-- Exact regrouping by the 2520 positive residue representatives `1,...,2520`.
The representative 2520 includes the full zero congruence class. -/
theorem legalWitness2520_exact_error :
    (∑' k : ℕ, positiveWeight (k+1) * (1 - legalWitness2520 (k+1)) ^ 2) =
      ∑ r : Fin 2520, progressionWeight 2520 (r.val+1) *
        (1 - legalWitness2520 (r.val+1)) ^ 2 := by
  rw [Nat.sumByResidueClasses legalWitness2520_error_summable 2520]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ∑' j : ℕ, positiveWeight ((r.val+1)+2520*j) *
        (1 - legalWitness2520 (r.val+1)) ^ 2 := by
      apply tsum_congr
      intro j
      have h : r.val + 2520*j + 1 = (r.val+1)+2520*j := by omega
      rw [h, legalWitness2520_add_multiple]
    _ = _ := by rw [tsum_mul_right]; rfl

/-- The complete weighted sequence squared error is strictly below `0.0421`.
This is unconditional: the analytic progression tails and periodic regrouping
have been discharged, not supplied as hypotheses. -/
theorem legalWitness2520_full_error_lt :
    (∑' k : ℕ, positiveWeight (k+1) * (1 - legalWitness2520 (k+1)) ^ 2) <
      (421 : ℝ) / 10000 := by
  rw [legalWitness2520_exact_error]
  apply legalWitness2520_error_lt_of_weights
  intro r
  have h := progressionWeight_upper_two 2520 (r.val+1) (by norm_num)
  convert h using 1 <;>
    simp only [residueUpper2520, positiveWeight, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] <;> ring

end RiemannResearch.RH.TwoSeedThreshold
