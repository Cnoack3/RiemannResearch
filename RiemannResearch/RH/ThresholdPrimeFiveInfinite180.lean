import RiemannResearch.Analysis.PeriodicSquareBound
import RiemannResearch.RH.ThresholdPrimeFiveCertificate180
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
theorem legalWitness180_mem_legalSeedSpan :
    legalWitness180 ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  let L := legalSeedSpan ({2, 3} : Set ℕ)
  have hm (a m : ℕ) (ha : a ∈ ({2, 3} : Set ℕ)) (hm : 0 < m) :
      certificateGenerator a m ∈ L := by
    have he : certificateGenerator a m = dilation m (residue a) := by
      funext k
      exact certificateGenerator_eq_dilation a m k
    rw [he]
    exact dilation_generator_mem _ ha hm
  have he : legalWitness180 = (1 / 10000 : ℝ) •
      ((5474 : ℝ) • certificateGenerator 2 1 +
       (935 : ℝ) • certificateGenerator 2 2 +
       (165 : ℝ) • certificateGenerator 2 3 +
       (-521 : ℝ) • certificateGenerator 2 5 +
       (326 : ℝ) • certificateGenerator 2 6 +
       (186 : ℝ) • certificateGenerator 2 9 +
       (-37 : ℝ) • certificateGenerator 2 10 +
       (36 : ℝ) • certificateGenerator 2 15 +
       (27 : ℝ) • certificateGenerator 2 18 +
       (-6 : ℝ) • certificateGenerator 2 30 +
       (1 : ℝ) • certificateGenerator 2 45 +
       (2 : ℝ) • certificateGenerator 2 90 +
       (3914 : ℝ) • certificateGenerator 3 1 +
       (804 : ℝ) • certificateGenerator 3 3 +
       (-175 : ℝ) • certificateGenerator 3 5 +
       (-22 : ℝ) • certificateGenerator 3 15) := by
    funext k
    simp only [legalWitness180, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [he]
  apply L.smul_mem
  repeat' apply L.add_mem
  all_goals apply L.smul_mem
  all_goals apply hm <;> norm_num

/-- Periodicity supplies a finite uniform error bound without enumerating residues. -/
theorem legalWitness180_error_bound (k : ℕ) :
    (1-legalWitness180 k)^2 ≤
      ∑ r : Fin 180, (1-legalWitness180 r.val)^2 := by
  exact RiemannResearch.Analysis.periodic_square_error_bound
    legalWitness180 180 (by norm_num) legalWitness180_periodic k

theorem legalWitness180_add_multiple (r j : ℕ) :
    legalWitness180 (r + 180*j) = legalWitness180 r := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : r + 180 * (j + 1) = (r + 180*j) + 180 := by omega
    rw [h, legalWitness180_periodic, ih]

/-- All positive indices are summable; the zero index is not silently dropped. -/
theorem legalWitness180_error_summable :
    Summable (fun k : ℕ => positiveWeight (k+1) *
      (1 - legalWitness180 (k+1)) ^ 2) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k+1)) :=
    positiveWeight_summable.comp_injective (by intro a b h; exact Nat.add_right_cancel h)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (legalWitness180_error_bound _)
      (positiveWeight_nonneg _))
    (hw.mul_right _)

/-- Exact regrouping by the 180 positive residue representatives `1,...,180`.
The representative 180 includes the full zero congruence class. -/
theorem legalWitness180_exact_error :
    (∑' k : ℕ, positiveWeight (k+1) * (1 - legalWitness180 (k+1)) ^ 2) =
      ∑ r : Fin 180, progressionWeight 180 (r.val+1) *
        (1 - legalWitness180 (r.val+1)) ^ 2 := by
  rw [Nat.sumByResidueClasses legalWitness180_error_summable 180]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ∑' j : ℕ, positiveWeight ((r.val+1)+180*j) *
        (1 - legalWitness180 (r.val+1)) ^ 2 := by
      apply tsum_congr
      intro j
      have h : r.val + 180*j + 1 = (r.val+1)+180*j := by omega
      rw [h, legalWitness180_add_multiple]
    _ = _ := by rw [tsum_mul_right]; rfl

/-- The complete weighted sequence squared error is strictly below `0.047`.
This is unconditional: the analytic progression tails and periodic regrouping
have been discharged, not supplied as hypotheses. -/
theorem legalWitness180_full_error_lt :
    (∑' k : ℕ, positiveWeight (k+1) * (1 - legalWitness180 (k+1)) ^ 2) <
      (47 : ℝ) / 1000 := by
  rw [legalWitness180_exact_error]
  apply legalWitness180_error_lt_of_weights
  intro r
  have h := progressionWeight_upper_two 180 (r.val+1) (by norm_num)
  convert h using 1 <;>
    simp only [residueUpper180, positiveWeight, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] <;> ring

end RiemannResearch.RH.TwoSeedThreshold
