/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.TruncatedGramEnvelope
import RiemannResearch.RH.CanonicalMobiusCovarianceMinimum
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.ParetoDilation
import RiemannResearch.RH.ThresholdHilbertAdjoint
import RiemannResearch.RH.ThresholdHilbertMean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certified finite inverse-Gram ceilings for canonical Möbius residuals

Source: user-requested cofinal squarefree inverse-Gram research. The finite
coefficient selection uses the augmented Gram construction, with the explicit
allowance (sum of squared pointwise amplitudes)/R for the complete infinite tail.
All signed mixed terms and the actual tail are retained in exact identities.
The constructed ceiling decreases as R grows for a fixed cutoff family.

The results apply to every finite positive canonical family, hence also when
all boundary conductors k i + 1 are squarefree. They do not assert a uniform
ceiling as the smallest cutoff grows; that arithmetic selection problem is open.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CanonicalTruncated
open RiemannResearch.Analysis.TruncatedGramEnvelope
open CoefficientStabilization.SignedCovariance
variable {ι : Type*} [Fintype ι]

def residual (k : ι → ℕ) (i : ι) (n : ℕ) : ℝ := 1 - canonicalMobiusHead (k i) n

def amplitude (k : ι → ℕ) (i : ι) : ℝ := 1 + 2 * (k i : ℝ)

def budget (k : ι → ℕ) : ℝ := ∑ i, amplitude k i ^ 2

omit [Fintype ι] in
theorem residual_abs_le (k : ι → ℕ) (hk : ∀ i, 0 < k i) (i : ι) (n : ℕ) :
    |residual k i n| ≤ amplitude k i := by
  calc
    _ ≤ |(1 : ℝ)| + |canonicalMobiusHead (k i) n| := by
      simpa only [residual, sub_eq_add_neg, abs_neg] using
        abs_add_le (1 : ℝ) (-canonicalMobiusHead (k i) n)
    _ ≤ _ := by simpa [amplitude] using
      add_le_add_left (canonicalMobiusHead_abs_le_two_mul (k i) (hk i) n) 1

def envelope (k : ι → ℕ) (R : ℕ) (a : ι → ℝ) : ℝ :=
  energy positiveWeight (residual k) (budget k / (R : ℝ)) R a

/-- Exact radius update before estimating any signed cross term. -/
theorem envelope_radius_difference (k : ι → ℕ) (R : ℕ) (hR : 0 < R) (a : ι → ℝ) :
    envelope k (R+1) a - envelope k R a =
      positiveWeight R * ((∑ i, a i * residual k i R) ^ 2 -
        budget k * ∑ i, a i ^ 2) := by
  unfold envelope
  rw [energy_succ_sub]
  have hr : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  have hr1 : (R : ℝ) + 1 ≠ 0 := by positivity
  unfold positiveWeight
  push_cast
  field_simp
  ring

theorem envelope_succ_le (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (R : ℕ) (hR : 0 < R) (a : ι → ℝ) :
    envelope k (R+1) a ≤ envelope k R a := by
  have hc := combination_sq_le (residual k) (amplitude k) a R (residual_abs_le k hk · R)
  have hn : (∑ i, a i * residual k i R) ^ 2 - budget k * ∑ i, a i ^ 2 ≤ 0 := by
    exact sub_nonpos.mpr hc
  have hm := mul_nonpos_of_nonneg_of_nonpos (positiveWeight_nonneg R) hn
  rw [← envelope_radius_difference k R hR a] at hm
  exact sub_nonpos.mp hm

theorem envelope_antitone_radius (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (R S : ℕ) (hR : 0 < R) (hRS : R ≤ S) (a : ι → ℝ) :
    envelope k S a ≤ envelope k R a := by
  induction S, hRS using Nat.le_induction with
  | base => exact le_rfl
  | succ S hRS ih => exact (envelope_succ_le k hk S (hR.trans_le hRS) a).trans ih

theorem residual_energy_summable (k : ι → ℕ) (hk : ∀ i, 0 < k i) (a : ι → ℝ) :
    Summable (fun n => positiveWeight n * (∑ i, a i * residual k i n) ^ 2) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
    (fun n => mul_le_mul_of_nonneg_left
      (combination_sq_le (residual k) (amplitude k) a n (residual_abs_le k hk · n))
      (positiveWeight_nonneg n))
  exact positiveWeight_summable.mul_right (budget k * ∑ i, a i ^ 2)

/-- The complete infinite complement is retained, with no truncation equality. -/
theorem residual_energy_split (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (R : ℕ) (a : ι → ℝ) :
    (∑' n, positiveWeight n * (∑ i, a i * residual k i n) ^ 2) =
      (∑ n ∈ Finset.range R, positiveWeight n * (∑ i, a i * residual k i n) ^ 2) +
      ∑' n, positiveWeight (n+R) * (∑ i, a i * residual k i (n+R)) ^ 2 :=
  ((residual_energy_summable k hk a).sum_add_tsum_nat_add R).symm

theorem residual_tail_le (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (R : ℕ) (hR : 0 < R) (a : ι → ℝ) :
    (∑' n, positiveWeight (n+R) * (∑ i, a i * residual k i (n+R)) ^ 2) ≤
      budget k / (R : ℝ) * ∑ i, a i ^ 2 := by
  have hs := (summable_nat_add_iff R).mpr (residual_energy_summable k hk a)
  have hw := (summable_nat_add_iff R).mpr positiveWeight_summable
  calc
    _ ≤ ∑' n, positiveWeight (n+R) * (budget k * ∑ i, a i ^ 2) := by
      apply Summable.tsum_le_tsum _ hs (hw.mul_right _)
      intro n
      exact mul_le_mul_of_nonneg_left
        (combination_sq_le (residual k) (amplitude k) a (n+R)
          (residual_abs_le k hk · (n+R))) (positiveWeight_nonneg _)
    _ = _ := by rw [tsum_mul_right, positiveWeight_tail_tsum R hR]; ring

theorem residual_energy_le_envelope (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (R : ℕ) (hR : 0 < R) (a : ι → ℝ) :
    (∑' n, positiveWeight n * (∑ i, a i * residual k i n) ^ 2) ≤ envelope k R a := by
  rw [residual_energy_split k hk R a]
  exact add_le_add le_rfl (residual_tail_le k hk R hR a)

theorem residual_norm_eq (k : ι → ℕ) (a : ι → ℝ) (ha : ∑ i, a i = 1) :
    ‖hilbertOne - combination k a‖ ^ 2 =
      ∑' n, positiveWeight n * (∑ i, a i * residual k i n) ^ 2 := by
  rw [hilbert_norm_weighted_sq]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn, positiveWeight]
  · rw [hilbertSequence_sub, Pi.sub_apply, hilbertOne_sequence, combination_sequence]
    simp only [zeroAnchor, hn, if_false]
    congr 2
    simp [residual, mul_sub, Finset.sum_sub_distrib, ha]

variable [Nonempty ι]

theorem budget_pos (k : ι → ℕ) : 0 < budget k := by
  apply Finset.sum_pos' (fun i _ => sq_nonneg (amplitude k i))
  exact ⟨Classical.choice ‹Nonempty ι›, Finset.mem_univ _,
    sq_pos_of_pos (by unfold amplitude; positivity)⟩

def selectedCoefficients (k : ι → ℕ) (R : ℕ) (hR : 0 < R) : ι → ℝ :=
  coefficients positiveWeight (residual k) (budget k / (R : ℝ)) R
    (div_pos (budget_pos k) (by exact_mod_cast hR))

def inverseCeiling (k : ι → ℕ) (R : ℕ) (hR : 0 < R) : ℝ :=
  ceiling positiveWeight (residual k) (budget k / (R : ℝ)) R
    (div_pos (budget_pos k) (by exact_mod_cast hR))

theorem selectedCoefficients_sum (k : ι → ℕ) (R : ℕ) (hR : 0 < R) :
    ∑ i, selectedCoefficients k R hR i = 1 := coefficients_sum _ _ _ _ _

theorem inverseCeiling_pos (k : ι → ℕ) (R : ℕ) (hR : 0 < R) :
    0 < inverseCeiling k R hR := ceiling_pos _ _ _ _ _

theorem inverseCeiling_antitone_radius (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (R S : ℕ) (hR : 0 < R) (hRS : R ≤ S) :
    inverseCeiling k S (hR.trans_le hRS) ≤ inverseCeiling k R hR := by
  apply ceiling_le_of_energy_le _ _ _ _ _ _ _ _ positiveWeight_nonneg
  exact envelope_antitone_radius k hk R S hR hRS

/-- An unconditional full Hilbert energy certificate for the constructed coefficients. -/
theorem selected_full_residual_le (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (R : ℕ) (hR : 0 < R) :
    ‖hilbertOne - combination k (selectedCoefficients k R hR)‖ ^ 2 ≤
      inverseCeiling k R hR := by
  rw [residual_norm_eq k _ (selectedCoefficients_sum k R hR)]
  exact (residual_energy_le_envelope k hk R hR _).trans
    (coefficients_energy positiveWeight (residual k) _ R _ positiveWeight_nonneg).le

theorem selected_exact (k : ι → ℕ) (R : ℕ) (hR : 0 < R) (H : ℕ)
    (hk : ∀ i, H ≤ k i) (n : ℕ) (hn : 0 < n) (hnH : n ≤ H) :
    hilbertSequence (combination k (selectedCoefficients k R hR)) n = 1 :=
  combination_exact H k _ hk (selectedCoefficients_sum k R hR) n hn hnH

end RiemannResearch.RH.Pareto.CanonicalTruncated
