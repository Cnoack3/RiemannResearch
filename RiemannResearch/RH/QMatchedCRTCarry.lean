/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QCRTCarry
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QSquarefreeDisplacementRegularity
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.QFiniteForcingData

/-! # The physical carry in the matched projection equations

Zero-drift Bézout representatives cancel the common Pareto residual energy.
They also give a zero initial segment of the carry, which localizes its
signed forcing to the physical residual tail.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage ZetaTwoParetoTransfer
open QCRTCarry QShiftedReciprocal QAnnihilatorTailEscape QFiniteSupportDualCriterion

/-- The signed deficit from the common finite Pareto residual energy.
For included m, full_conductor_forcing_deficit identifies it with a tail series. -/
def matchedGramDeficit (N m : ℕ) : ℝ :=
  ‖toPareto (qOne - finitePFit N)‖ ^ 2 -
    (zetaTwo * m) * inner ℝ (qResidue m) (finiteDisplacement N)

/-- At zero drift all copies of the common scalar cancel exactly. -/
theorem matched_carry_eq_deficits (N p q : ℕ) (a b : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hbez : (a : ℝ) * q + (b : ℝ) * p = 1) :
    (zetaTwo * ((p * q : ℕ) : ℝ)) * inner ℝ (qCarry p q a b) (finiteDisplacement N) =
      matchedGramDeficit N (p * q) -
        ((a : ℝ) * q) * matchedGramDeficit N p -
        ((b : ℝ) * p) * matchedGramDeficit N q := by
  rw [qCarry_eq_linear p q a b 0 hp hq (by simpa using hbez)]
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, matchedGramDeficit, Nat.cast_mul]
  linear_combination ‖toPareto (qOne - finitePFit N)‖ ^ 2 * hbez

/-- Dividing by pq exposes the coordinate differences. Taking a least
absolute inverse gives |a / p| ≤ 1 / 2. -/
theorem matched_carry_eq_differences (N p q : ℕ) (a b : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hbez : (a : ℝ) * q + (b : ℝ) * p = 1) :
    zetaTwo * inner ℝ (qCarry p q a b) (finiteDisplacement N) =
      (matchedGramDeficit N (p * q) - matchedGramDeficit N q) / ((p : ℝ) * q) -
      ((a : ℝ) / p) * (matchedGramDeficit N p - matchedGramDeficit N q) := by
  have h := matched_carry_eq_deficits N p q a b hp hq hbez
  rw [Nat.cast_mul] at h
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  linear_combination (norm := field_simp [hp', hq'] <;> ring)
    (1 / ((p : ℝ) * q)) * h - (matchedGramDeficit N q / ((p : ℝ) * q)) * hbez

private theorem zero_drift_carry_head (p q : ℕ) (a b : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hbez : (a : ℝ) * q + (b : ℝ) * p = 1) (n : ℕ) (hn : n < min p q) :
    qSequence (qCarry p q a b) n = 0 := by
  rw [qSequence_qCarry]
  change ((CRTCarryArithmetic.carry p q a b n : ℤ) : ℝ) = 0
  rw [CRTCarryArithmetic.carry_head p q a b 0 n hp hq
    (by simpa using hbez) (lt_min_iff.mp hn).1 (lt_min_iff.mp hn).2]
  simp

/-- A legal test supported above T pairs only with the residual above T,
and receives the reciprocal multiplier gain there. -/
theorem matched_row_tail_bound (N T : ℕ) (v : QHilbert) (hv : v ∈ stage N)
    (hz : ∀ k ≤ T, qSequence v k = 0) :
    ((T : ℝ) + 2) * |inner ℝ v (finiteDisplacement N)| ≤
      ‖v‖ * ‖tail T (qOne - finitePFit N)‖ := by
  let r := qOne - finitePFit N
  have hmatch := Submodule.inner_right_of_mem_orthogonal hv (finite_witness_mem_orthogonal N)
  rw [inner_sub_right] at hmatch
  have htail : inner ℝ (B v) r = inner ℝ (B v) (tail T r) := by
    simp only [qInner_weighted, qSequence_B]
    apply tsum_congr
    intro k
    by_cases hk : k ≤ T
    · simp [hz k hk]
    · cases k with
      | zero => omega
      | succ n =>
        have hsite : qSequence (tail T r) (n + 1) = qSequence r (n + 1) := by
          change (r n - finiteHead T r n) / Real.sqrt (qWeight n) = _
          rw [finiteHead_apply_eq_zero _ _ _ (by omega), sub_zero]
          rfl
        rw [hsite]
  have he : inner ℝ v (finiteDisplacement N) = inner ℝ (B v) (tail T r) := by
    rw [← sub_eq_zero.mp hmatch]
    exact (B_symmetric v r).symm.trans htail
  rw [he]
  calc
    _ ≤ ((T : ℝ) + 2) * (‖B v‖ * ‖tail T r‖) :=
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
    _ = (((T : ℝ) + 2) * ‖B v‖) * ‖tail T r‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (QSquarefreeDisplacementRegularity.scaled_B_norm_le_of_head v T hz) (norm_nonneg _)

/-- The actual zero-drift floor carry starts at the smaller conductor. -/
theorem matched_carry_tail_bound (N p q : ℕ) (a b : ℤ) (hp : 0 < p) (hq : 0 < q)
    (hbez : (a : ℝ) * q + (b : ℝ) * p = 1)
    (hpp : qResidue p ∈ stage N) (hqq : qResidue q ∈ stage N)
    (hpq : qResidue (p * q) ∈ stage N) :
    (((min p q : ℕ) : ℝ) + 1) * |inner ℝ (qCarry p q a b) (finiteDisplacement N)| ≤
      ‖qCarry p q a b‖ * ‖tail (min p q - 1) (qOne - finitePFit N)‖ := by
  have hv : qCarry p q a b ∈ stage N := by
    rw [qCarry_eq_linear p q a b 0 hp hq (by simpa using hbez)]
    exact (stage N).sub_mem ((stage N).add_mem ((stage N).smul_mem _ hpp)
      ((stage N).smul_mem _ hqq)) hpq
  have hm : 1 ≤ min p q := le_min hp hq
  have hh := matched_row_tail_bound N (min p q - 1) _ hv (fun k hk =>
    zero_drift_carry_head p q a b hp hq hbez k (by omega))
  have hcoeff : ((min p q - 1 : ℕ) : ℝ) + 2 = ((min p q : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hm, Nat.cast_one]
    ring
  rwa [hcoeff] at hh

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
