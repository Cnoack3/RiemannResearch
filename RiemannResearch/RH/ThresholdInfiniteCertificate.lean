import RiemannResearch.RH.ThresholdFiniteCertificate
import RiemannResearch.RH.ParetoProgressionTails
import RiemannResearch.RH.ThresholdDilationAlgebra
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Data.Nat.Periodic
import Mathlib.Tactic.IntervalCases

/-!
# An unconditional infinite weighted-error certificate

Source: `RH_Two_Seed_Threshold.tex`, revised 7 September 2026, Section 10,
Proposition `crt-cost-example`. This supplies an explicit legal witness for
the upper bound, with every positive index and the complete infinite tail.
It does not assert optimality or certify the constrained lower bound.
-/

open scoped BigOperators

namespace RiemannResearch.RH.TwoSeedThreshold

open Pareto

/-- Link the certificate's exact residue differences to the project's genuine
integer dilation operators, with no restriction on the dilation parameter. -/
theorem certificateGenerator_eq_dilation (a m k : ℕ) :
    certificateGenerator a m k = dilation m (residue a) k := by
  rw [residue_mul_floor]
  simp only [certificateGenerator, residue, Nat.mul_comm]

/-- The witness belongs to the actual two-seed finite legal span. -/
theorem legalWitness36_mem_legalSeedSpan :
    legalWitness36 ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  let L := legalSeedSpan ({2, 3} : Set ℕ)
  have hm (a m : ℕ) (ha : a ∈ ({2, 3} : Set ℕ)) (hm : 0 < m) :
      certificateGenerator a m ∈ L := by
    have he : certificateGenerator a m = dilation m (residue a) := by
      funext k
      exact certificateGenerator_eq_dilation a m k
    rw [he]
    exact dilation_generator_mem _ ha hm
  have he : legalWitness36 = (1 / 1000 : ℝ) •
      ((556 : ℝ) • certificateGenerator 2 1 +
       (117 : ℝ) • certificateGenerator 2 2 +
        (18 : ℝ) • certificateGenerator 2 3 +
         (6 : ℝ) • certificateGenerator 2 6 +
         (7 : ℝ) • certificateGenerator 2 9 +
         (2 : ℝ) • certificateGenerator 2 18 +
       (367 : ℝ) • certificateGenerator 3 1 +
        (50 : ℝ) • certificateGenerator 3 3) := by
    funext k
    simp only [legalWitness36, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [he]
  apply L.smul_mem
  repeat' apply L.add_mem
  all_goals apply L.smul_mem
  all_goals apply hm <;> norm_num

theorem legalWitness36_error_le_four (k : ℕ) :
    (1 - legalWitness36 k) ^ 2 ≤ (4 : ℝ) := by
  have hp : Function.Periodic legalWitness36 36 := legalWitness36_periodic
  rw [← hp.map_mod_nat k]
  have hk : k % 36 < 36 := Nat.mod_lt k (by norm_num)
  generalize k % 36 = r at *
  interval_cases r <;>
    norm_num [legalWitness36, certificateGenerator]

theorem legalWitness36_add_multiple (r j : ℕ) :
    legalWitness36 (r + 36*j) = legalWitness36 r := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : r + 36 * (j + 1) = (r + 36*j) + 36 := by omega
    rw [h, legalWitness36_periodic, ih]

/-- All positive indices are summable; the zero index is not silently dropped. -/
theorem legalWitness36_error_summable :
    Summable (fun k : ℕ => positiveWeight (k+1) *
      (1 - legalWitness36 (k+1)) ^ 2) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k+1)) :=
    positiveWeight_summable.comp_injective (by intro a b h; exact Nat.add_right_cancel h)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (legalWitness36_error_le_four _)
      (positiveWeight_nonneg _))
    (hw.mul_right 4)

/-- Exact regrouping by the 36 positive residue representatives `1,...,36`.
The representative 36 includes the full zero congruence class. -/
theorem legalWitness36_exact_error :
    (∑' k : ℕ, positiveWeight (k+1) * (1 - legalWitness36 (k+1)) ^ 2) =
      ∑ r : Fin 36, progressionWeight 36 (r.val+1) *
        (1 - legalWitness36 (r.val+1)) ^ 2 := by
  rw [Nat.sumByResidueClasses legalWitness36_error_summable 36]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ∑' j : ℕ, positiveWeight ((r.val+1)+36*j) *
        (1 - legalWitness36 (r.val+1)) ^ 2 := by
      apply tsum_congr
      intro j
      have h : r.val + 36*j + 1 = (r.val+1)+36*j := by omega
      rw [h, legalWitness36_add_multiple]
    _ = _ := by rw [tsum_mul_right]; rfl

/-- The complete weighted sequence squared error is strictly below `0.053`.
This is unconditional: the analytic progression tails and periodic regrouping
have been discharged, not supplied as hypotheses. -/
theorem legalWitness36_full_error_lt :
    (∑' k : ℕ, positiveWeight (k+1) * (1 - legalWitness36 (k+1)) ^ 2) <
      (53 : ℝ) / 1000 := by
  rw [legalWitness36_exact_error]
  apply legalWitness36_error_lt_of_weights
  intro r
  have h := progressionWeight_upper_two 36 (r.val+1) (by norm_num)
  convert h using 1 <;>
    simp only [residueUpper36, positiveWeight, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat] <;> ring

end RiemannResearch.RH.TwoSeedThreshold
