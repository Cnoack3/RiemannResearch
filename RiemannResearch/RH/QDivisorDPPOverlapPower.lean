/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QDivisorDPPOverlap
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Arbitrarily small power loss in Q divisor overlaps

Source: the finite-small-prime argument in the user-provided
QDPPMovingWindowsResearch20261014.md, Section 7, supports the statement.
The exact overlap is imported from QDivisorDPPOverlap and is not reproved.
The constant depends only on the positive real exponent; no RH input is used.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ZetaTwoHilbert
open ZetaTwoProbability

private theorem finset_prod_rpow {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (e : ℝ) :
    (∏ i ∈ S, f i) ^ e = ∏ i ∈ S, (f i) ^ e := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.mul_rpow (hf a (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

def overlapPowerPenalty (B p : ℕ) : ℝ := if p < B then 2 else 1

theorem overlapPowerPenalty_one_le (B p : ℕ) : 1 ≤ overlapPowerPenalty B p := by
  unfold overlapPowerPenalty; split_ifs <;> norm_num

theorem prod_overlapPowerPenalty_le (B : ℕ) (S : Finset ℕ) :
    (∏ p ∈ S, overlapPowerPenalty B p) ≤ (2 : ℝ) ^ B := by
  have hc : (S.filter (fun p => p < B)).card ≤ B := by
    calc
      _ ≤ (Finset.range B).card := Finset.card_le_card (by
        intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = B := Finset.card_range B
  have he : (∏ p ∈ S, overlapPowerPenalty B p) =
      (2 : ℝ) ^ (S.filter (fun p => p < B)).card := by
    simp [overlapPowerPenalty, Finset.prod_ite]
  rw [he]
  exact pow_le_pow_right₀ (by norm_num) hc

theorem localOverlapCorrection_rpow_budget_lt (e : ℝ) (he : 0 ≤ e)
    (B : ℕ) (hB : ∀ p : ℕ, B ≤ p → 2 ≤ (p : ℝ) ^ e)
    (p v w : ℕ) (hp : p.Prime) (hvw : v < w) :
    localOverlapCorrection p v w * (((p : ℝ) ^ v) ^ 2) ^ e ≤
      overlapPowerPenalty B p * ((p : ℝ) ^ v * (p : ℝ) ^ w) ^ e := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hC : 0 ≤ overlapPowerPenalty B p := (by norm_num : (0 : ℝ) ≤ 1).trans
    (overlapPowerPenalty_one_le B p)
  have hcp : 2 ≤ overlapPowerPenalty B p * (p : ℝ) ^ e := by
    unfold overlapPowerPenalty
    split_ifs with h
    · have hh := Real.one_le_rpow hp1 he
      linarith
    · simpa using hB p (Nat.le_of_not_gt h)
  have hpow : (p : ℝ) ^ (v + 1) ≤ (p : ℝ) ^ w :=
    pow_le_pow_right₀ hp1 (Nat.succ_le_of_lt hvw)
  have hb : ((p : ℝ) ^ v) ^ 2 * p ≤ (p : ℝ) ^ v * (p : ℝ) ^ w := by
    rw [pow_succ] at hpow
    nlinarith [mul_le_mul_of_nonneg_left hpow (pow_nonneg hp0 v)]
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ ((p : ℝ) ^ v) ^ 2 * p) hb he
  rw [Real.mul_rpow (sq_nonneg _) hp0] at hr
  calc
    _ ≤ 2 * (((p : ℝ) ^ v) ^ 2) ^ e :=
      mul_le_mul_of_nonneg_right (localOverlapCorrection_le_two p v w) (Real.rpow_nonneg (sq_nonneg _) _)
    _ ≤ (overlapPowerPenalty B p * (p : ℝ) ^ e) * (((p : ℝ) ^ v) ^ 2) ^ e :=
      mul_le_mul_of_nonneg_right hcp (Real.rpow_nonneg (sq_nonneg _) _)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hr hC]

theorem localOverlapCorrection_rpow_budget (e : ℝ) (he : 0 ≤ e)
    (B : ℕ) (hB : ∀ p : ℕ, B ≤ p → 2 ≤ (p : ℝ) ^ e)
    (p v w : ℕ) (hp : p.Prime) :
    localOverlapCorrection p v w * (((p : ℝ) ^ min v w) ^ 2) ^ e ≤
      overlapPowerPenalty B p * ((p : ℝ) ^ v * (p : ℝ) ^ w) ^ e := by
  rcases lt_trichotomy v w with h | h | h
  · simpa [min_eq_left h.le] using localOverlapCorrection_rpow_budget_lt e he B hB p v w hp h
  · subst w
    have hh := mul_le_mul_of_nonneg_right (overlapPowerPenalty_one_le B p)
      (Real.rpow_nonneg (sq_nonneg ((p : ℝ) ^ v)) e)
    simpa [localOverlapCorrection, pow_two] using hh
  · have hh : localOverlapCorrection p v w = localOverlapCorrection p w v := by
      simp only [localOverlapCorrection, eq_comm]
    simpa [hh, min_eq_right h.le, mul_comm] using
      localOverlapCorrection_rpow_budget_lt e he B hB p w v hp h

theorem overlapCorrection_rpow_budget (e : ℝ) (he : 0 ≤ e)
    (B : ℕ) (hB : ∀ p : ℕ, B ≤ p → 2 ≤ (p : ℝ) ^ e) (n m : ℕ+) :
    overlapCorrection n m * ((Nat.gcd (n : ℕ) (m : ℕ) : ℝ) ^ 2) ^ e ≤
      (2 : ℝ) ^ B * ((n : ℝ) * (m : ℝ)) ^ e := by
  let S := (n : ℕ).primeFactors ∪ (m : ℕ).primeFactors
  have hloc : (∏ p ∈ S,
      localOverlapCorrection p (primeValuation p n) (primeValuation p m) *
        (((p : ℝ) ^ min (primeValuation p n) (primeValuation p m)) ^ 2) ^ e) ≤
      ∏ p ∈ S, overlapPowerPenalty B p *
        ((p : ℝ) ^ primeValuation p n * (p : ℝ) ^ primeValuation p m) ^ e := by
    apply Finset.prod_le_prod
    · intro p hp
      have hpP : p.Prime := by
        rcases Finset.mem_union.mp hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
      exact mul_nonneg (localOverlapCorrection_nonneg p _ _ hpP) (Real.rpow_nonneg (sq_nonneg _) _)
    · intro p hp
      have hpP : p.Prime := by
        rcases Finset.mem_union.mp hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
      exact localOverlapCorrection_rpow_budget e he B hB p _ _ hpP
  rw [Finset.prod_mul_distrib, ← finset_prod_rpow S _ (fun _ _ => sq_nonneg _) e,
    Finset.prod_pow,
    prod_min_valuation n m S Finset.subset_union_left Finset.subset_union_right,
    Finset.prod_mul_distrib, ← finset_prod_rpow S _ (fun _ _ => by positivity) e,
    Finset.prod_mul_distrib,
    prod_valuation n S Finset.subset_union_left,
    prod_valuation m S Finset.subset_union_right] at hloc
  exact hloc.trans (mul_le_mul_of_nonneg_right (prod_overlapPowerPenalty_le B S)
    (Real.rpow_nonneg (by positivity) _))

end RiemannResearch.RH.ZetaTwoHilbert

namespace RiemannResearch.RH.QDivisorDPP
open ZetaTwoHilbert
theorem basisKernel_abs_le_rpow (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ N i j : ℕ,
      |basisKernel N i j| ≤ C *
        ((Nat.gcd (i+1) (j+1) : ℝ) ^ 2 /
          (((i+1 : ℕ) : ℝ) * ((j+1 : ℕ) : ℝ))) ^ (1 - e) := by
  have ht : Tendsto (fun p : ℕ => (p : ℝ) ^ e) atTop atTop :=
    (tendsto_rpow_atTop he).comp tendsto_natCast_atTop_atTop
  obtain ⟨B, hB⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop 2))
  refine ⟨2 ^ B, by positivity, ?_⟩
  intro N i j
  let g : ℝ := Nat.gcd (i+1) (j+1)
  let k : ℝ := ((i+1 : ℕ) : ℝ) * ((j+1 : ℕ) : ℝ)
  let F := overlapCorrection (basisIndex i) (basisIndex j)
  have hg : 0 < g := by dsimp [g]; exact_mod_cast Nat.gcd_pos_of_pos_left (j+1) (Nat.succ_pos i)
  have hk : 0 < k := by dsimp [k]; positivity
  have ha : 0 < g ^ 2/k := div_pos (sq_pos_of_pos hg) hk
  have hf : F * (g ^ 2) ^ e ≤ 2 ^ B * k ^ e :=
    overlapCorrection_rpow_budget e he.le B hB (basisIndex i) (basisIndex j)
  have hfe : F ≤ 2 ^ B / (g ^ 2/k) ^ e := by
    rw [Real.div_rpow (sq_nonneg _) hk.le]
    apply (le_div_iff₀ (div_pos (Real.rpow_pos_of_pos (sq_pos_of_pos hg) _) (Real.rpow_pos_of_pos hk _))).mpr
    rw [← mul_div_assoc]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hk _)).mpr hf
  calc
    _ ≤ g ^ 2/k * F := basisKernel_abs_le_overlap N i j
    _ ≤ g ^ 2/k * (2 ^ B / (g ^ 2/k) ^ e) := mul_le_mul_of_nonneg_left hfe ha.le
    _ = 2 ^ B * (g ^ 2/k) ^ (1 - e) := by
      rw [Real.rpow_sub ha, Real.rpow_one]
      ring

end RiemannResearch.RH.QDivisorDPP
