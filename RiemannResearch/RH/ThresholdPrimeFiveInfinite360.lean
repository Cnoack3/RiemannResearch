import RiemannResearch.Analysis.PeriodicSquareBound
import RiemannResearch.RH.ThresholdPrimeFiveCertificate360
import RiemannResearch.RH.ThresholdInfiniteCertificate
import RiemannResearch.RH.ParetoProgressionTails
import RiemannResearch.RH.ThresholdDilationAlgebra
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic.IntervalCases

/-!
# An unconditional infinite weighted-error certificate

New rational prime-five dilation certificate, 8 September 2026.
Adapted from the previously verified period-36 analytic bridge.
This supplies an explicit legal witness for
the upper bound, with every positive index and the complete infinite tail.
It does not assert optimality or certify the constrained lower bound.
-/

open scoped BigOperators

namespace RiemannResearch.RH.TwoSeedThreshold

open Pareto

set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

/-- The witness belongs to the actual two-seed finite legal span. -/
theorem legalWitness360_mem_legalSeedSpan :
    legalWitness360 ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  let L := legalSeedSpan ({2, 3} : Set ℕ)
  have hm (a m : ℕ) (ha : a ∈ ({2, 3} : Set ℕ)) (hm : 0 < m) :
      certificateGenerator a m ∈ L := by
    have he : certificateGenerator a m = dilation m (residue a) := by
      funext k
      exact certificateGenerator_eq_dilation a m k
    rw [he]
    exact dilation_generator_mem _ ha hm
  have he : legalWitness360 = (1 / 1000 : ℝ) •
      ((570 : ℝ) • certificateGenerator 2 1 +
       (112 : ℝ) • certificateGenerator 2 2 +
       (1 : ℝ) • certificateGenerator 2 3 +
       (52 : ℝ) • certificateGenerator 2 4 +
       (-59 : ℝ) • certificateGenerator 2 5 +
       (36 : ℝ) • certificateGenerator 2 6 +
       (25 : ℝ) • certificateGenerator 2 9 +
       (-6 : ℝ) • certificateGenerator 2 10 +
       (-2 : ℝ) • certificateGenerator 2 12 +
       (6 : ℝ) • certificateGenerator 2 15 +
       (3 : ℝ) • certificateGenerator 2 18 +
       (-2 : ℝ) • certificateGenerator 2 20 +
       (-4 : ℝ) • certificateGenerator 2 30 +
       (6 : ℝ) • certificateGenerator 2 36 +
       (-3 : ℝ) • certificateGenerator 2 45 +
       (372 : ℝ) • certificateGenerator 3 1 +
       (62 : ℝ) • certificateGenerator 3 3 +
       (-26 : ℝ) • certificateGenerator 3 5 +
       (-2 : ℝ) • certificateGenerator 3 15) := by
    funext k
    simp only [legalWitness360, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [he]
  apply L.smul_mem
  repeat' apply L.add_mem
  all_goals apply L.smul_mem
  all_goals apply hm <;> norm_num

/-- Periodicity supplies a finite uniform error bound without enumerating residues. -/
theorem legalWitness360_error_bound (k : ℕ) :
    (1-legalWitness360 k)^2 ≤
      ∑ r : Fin 360, (1-legalWitness360 r.val)^2 := by
  exact RiemannResearch.Analysis.periodic_square_error_bound
    legalWitness360 360 (by norm_num) legalWitness360_periodic k

theorem legalWitness360_add_multiple (r j : ℕ) :
    legalWitness360 (r + 360*j) = legalWitness360 r := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : r + 360 * (j + 1) = (r + 360*j) + 360 := by omega
    rw [h, legalWitness360_periodic, ih]

/-- All positive indices are summable; the zero index is not silently dropped. -/
theorem legalWitness360_error_summable :
    Summable (fun k : ℕ => positiveWeight (k+1) *
      (1 - legalWitness360 (k+1)) ^ 2) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k+1)) :=
    positiveWeight_summable.comp_injective (by intro a b h; exact Nat.add_right_cancel h)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (legalWitness360_error_bound _)
      (positiveWeight_nonneg _))
    (hw.mul_right _)

/-- Exact regrouping by the 360 positive residue representatives `1,...,360`.
The representative 360 includes the full zero congruence class. -/
theorem legalWitness360_exact_error :
    (∑' k : ℕ, positiveWeight (k+1) * (1 - legalWitness360 (k+1)) ^ 2) =
      ∑ r : Fin 360, progressionWeight 360 (r.val+1) *
        (1 - legalWitness360 (r.val+1)) ^ 2 := by
  rw [Nat.sumByResidueClasses legalWitness360_error_summable 360]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ∑' j : ℕ, positiveWeight ((r.val+1)+360*j) *
        (1 - legalWitness360 (r.val+1)) ^ 2 := by
      apply tsum_congr
      intro j
      have h : r.val + 360*j + 1 = (r.val+1)+360*j := by omega
      rw [h, legalWitness360_add_multiple]
    _ = _ := by rw [tsum_mul_right]; rfl

/-- The complete weighted sequence squared error is strictly below `0.044`.
This is unconditional: the analytic progression tails and periodic regrouping
have been discharged, not supplied as hypotheses. -/
theorem legalWitness360_full_error_lt :
    (∑' k : ℕ, positiveWeight (k+1) * (1 - legalWitness360 (k+1)) ^ 2) <
      (11 : ℝ) / 250 := by
  rw [legalWitness360_exact_error]
  apply legalWitness360_error_lt_of_weights
  intro r
  have h := progressionWeight_upper_two 360 (r.val+1) (by norm_num)
  convert h using 1 <;>
    simp only [residueUpper360, positiveWeight, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] <;> ring

end RiemannResearch.RH.TwoSeedThreshold
