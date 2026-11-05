/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QMatchedCRTCarry
import RiemannResearch.RH.QPrimeCRTCarries
import Mathlib.Data.Nat.GCD.BigOperators

/-! # A single matched carry for any number of CRT factors

For a squarefree product m of the members of S, choose integral Bézout coefficients
with sum of a(p)/p equal to 1/m. The floor of their residue sum is one signed carry.
Its common Pareto energy cancels in the matched projection equations, and its physical
row vanishes below all conductors. The finite-sum identities only need the displayed
reciprocal relation, so they also apply to other factorizations supplying that relation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement

open ArithmeticCumulative ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open ZetaTwoParetoTransfer QAnnihilatorTailEscape QFiniteSupportDualCriterion

/-- Every nonempty finite set of primes supplies zero-drift integral coefficients. -/
theorem exists_finite_prime_bezout (S : Finset ℕ) :
    S.Nonempty → (∀ p ∈ S, Nat.Prime p) →
      ∃ a : ℕ → ℤ, (∑ p ∈ S, (a p : ℝ) / (p : ℝ)) = 1 / ((∏ p ∈ S, p : ℕ) : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hp ih =>
    intro _ hpr
    have hpp := hpr p (Finset.mem_insert_self p S)
    have hpS : ∀ q ∈ S, Nat.Prime q := fun q hq => hpr q (Finset.mem_insert_of_mem hq)
    by_cases hS : S.Nonempty
    · obtain ⟨b, hb⟩ := ih hS hpS
      let m : ℕ := ∏ q ∈ S, q
      have hm : 0 < m := Finset.prod_pos fun q hq => (hpS q hq).pos
      have hcop : Nat.Coprime p m := Nat.coprime_prod_right_iff.mpr (fun q hq =>
        (Nat.coprime_primes hpp (hpS q hq)).mpr fun he => hp (he.symm ▸ hq))
      let u := Nat.gcdB p m
      let v := Nat.gcdA p m
      have hz : (1 : ℤ) = (p : ℤ) * v + (m : ℤ) * u := by
        simpa only [u, v, hcop.gcd_eq_one, Nat.cast_one] using Nat.gcd_eq_gcd_ab p m
      have hreal : (1 : ℝ) = (p : ℝ) * (v : ℝ) + (m : ℝ) * (u : ℝ) := by exact_mod_cast hz
      let a (q : ℕ) : ℤ := if q = p then u else v * b q
      refine ⟨a, ?_⟩
      change (∑ q ∈ S, (b q : ℝ) / (q : ℝ)) = 1 / (m : ℝ) at hb
      have hsum : (∑ q ∈ S, (a q : ℝ) / (q : ℝ)) = (v : ℝ) * (1 / (m : ℝ)) := by
        rw [← hb, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        have hne : q ≠ p := fun he => hp (he ▸ hq)
        simp only [a, if_neg hne, Int.cast_mul]
        ring
      rw [Finset.sum_insert hp, Finset.prod_insert hp, hsum]
      change (a p : ℝ) / (p : ℝ) + (v : ℝ) * (1 / (m : ℝ)) = 1 / ((p * m : ℕ) : ℝ)
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.ne_zero
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      simp only [a, if_pos rfl, Nat.cast_mul]
      field_simp [hpR, hmR]
      linarith
    · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      exact ⟨fun _ => 1, by simp⟩

variable {ι : Type*} [Fintype ι]

/-- The common forcing energy disappears for every number of factors. -/
theorem finiteBezoutRow_deficits (p : ι → ℕ) (a : ι → ℤ) (m N : ℕ)
    (hm : 0 < m) (hp : ∀ i, 0 < p i)
    (hbez : (∑ i, (a i : ℝ) / (p i : ℝ)) = 1 / (m : ℝ)) :
    zetaTwo * inner ℝ (QPrimeCRTCarries.carryVector m p a) (finiteDisplacement N) =
      matchedGramDeficit N m / (m : ℝ) -
        ∑ i, (a i : ℝ) * matchedGramDeficit N (p i) / (p i : ℝ) := by
  let E := ‖toPareto (qOne - finitePFit N)‖ ^ 2
  let row := fun p => inner ℝ (qResidue p) (finiteDisplacement N)
  have hsum : (∑ i, (a i : ℝ) * matchedGramDeficit N (p i) / (p i : ℝ)) =
      E * (1 / (m : ℝ)) - zetaTwo * ∑ i, (a i : ℝ) * row (p i) := by
    rw [← hbez, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hn : (p i : ℝ) ≠ 0 := by exact_mod_cast (hp i).ne'
    dsimp only [matchedGramDeficit, E, row]
    field_simp [hn]
    <;> ring
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [QPrimeCRTCarries.carryVector, inner_sub_left, sum_inner, hsum]
  simp only [real_inner_smul_left, E, row, matchedGramDeficit]
  field_simp [hn]
  <;> ring

/-- The matched forcing for the existing literal carry is confined to the
physical residual above the smallest conductor. -/
theorem finiteBezoutRow_tail (p : ι → ℕ) (a : ι → ℤ) (m N T : ℕ)
    (hm : T < m) (hp : ∀ i, T < p i)
    (hbez : (∑ i, (a i : ℝ) / (p i : ℝ)) = 1 / (m : ℝ))
    (hv : qResidue m ∈ stage N) (hvS : ∀ i, qResidue (p i) ∈ stage N) :
    ((T : ℝ) + 2) * |inner ℝ (QPrimeCRTCarries.carryVector m p a) (finiteDisplacement N)| ≤
      ‖QPrimeCRTCarries.carryVector m p a‖ * ‖tail T (qOne - finitePFit N)‖ := by
  apply matched_row_tail_bound
  · exact (stage N).sub_mem ((stage N).sum_mem fun i _ =>
      (stage N).smul_mem _ (hvS i)) hv
  · intro k hk
    change qSequenceLinear ((∑ i, (a i : ℝ) • qResidue (p i)) - qResidue m) k = 0
    simp only [map_sub, map_sum, map_smul, Pi.sub_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    change (∑ i, (a i : ℝ) * qSequence (qResidue (p i)) k) - qSequence (qResidue m) k = 0
    simp only [qSequence_qResidue, residueFraction, Nat.mod_eq_of_lt (hk.trans_lt hm)]
    have hterm (i : ι) :
        (a i : ℝ) * (((k % p i : ℕ) : ℝ) / p i) = (k : ℝ) * ((a i : ℝ) / p i) := by
      rw [Nat.mod_eq_of_lt (hk.trans_lt (hp i))]
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, hbez]
    ring

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
