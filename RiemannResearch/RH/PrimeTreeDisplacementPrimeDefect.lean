/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimeSubtreeBudget
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QSquarefreeDisplacementRegularity
import RiemannResearch.RH.QSquarefreeCompatibleHeads
import RiemannResearch.RH.ExactHeadCharges
import RiemannResearch.RH.ParetoArithmeticRepair
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # The prime-deletion defect of the matched displacement
Source: direct algebraic analysis of the user-requested Mertens argument,
6 November 2026. The ordinary Möbius argument deletes a prime with an exact
sign change. The actual displacement charge has the signed defect below.
The final conditional rigidity theorem shows that imposing the same rule
on every prime would already force the actual matched displacement to vanish.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

theorem sum_divisors_coprime {p n : ℕ} (hpn : p.Coprime n) (F : ℕ → ℝ) :
    (∑ d ∈ (p*n).divisors, F d) = ∑ a ∈ p.divisors, ∑ b ∈ n.divisors, F (a*b) := by
  rw [hpn.divisors_mul, Finset.sum_map]
  change (∑ x ∈ (p.divisors ×ˢ n.divisors).attach, F (x.val.1*x.val.2)) = _
  rw [Finset.sum_attach (f := fun x : ℕ × ℕ => F (x.1*x.2)), Finset.sum_product]

/-- Multiplication by a new prime leaves a Möbius transform of the increments
at its multiples. For ordinary Möbius weights those increments vanish. -/
theorem mobiusDifference_prime_deletion_defect (f : ℕ → ℝ) {p n : ℕ}
    (hp : p.Prime) (hpn : ¬p ∣ n) :
    mobiusDifference (p*n) f + mobiusDifference n f =
      ∑ a ∈ n.divisors, (ArithmeticFunction.moebius (n/a) : ℝ) *
        (f (p*a) - f (p*a-1)) := by
  have hc : p.Coprime n := hp.coprime_iff_not_dvd.mpr hpn
  have hsum := sum_divisors_coprime hc
    (fun d => (ArithmeticFunction.moebius ((p*n)/d) : ℝ) * (f d-f (d-1)))
  rw [hp.divisors, Finset.sum_insert (by simp [hp.ne_one.symm]),
    Finset.sum_singleton] at hsum
  simp only [one_mul, Nat.mul_div_mul_left _ _ hp.pos] at hsum
  have hfirst : (∑ a ∈ n.divisors, (ArithmeticFunction.moebius ((p*n)/a) : ℝ) *
      (f a-f (a-1))) = -mobiusDifference n f := by
    rw [mobiusDifference, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have hd := Nat.dvd_of_mem_divisors ha
    have hfree : ¬p ∣ n/a := fun h => hpn (h.trans (Nat.div_dvd_of_dvd hd))
    rw [Nat.mul_div_assoc p hd, ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hp.coprime_iff_not_dvd.mpr hfree), ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  change (∑ d ∈ (p*n).divisors, _) + mobiusDifference n f = _
  rw [hsum, hfirst]
  ring

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.QPrimeSubtreeBudget
open Pareto ZetaTwoHilbert QSquarefreeDisplacementRigidity QSquarefreeDisplacementRegularity

/-- The exact additional term when the ordinary Möbius deletion rule is
applied to the coefficients of the actual matched displacement. -/
theorem displacement_prime_deletion_defect {p n : ℕ} (hp : p.Prime) (hpn : ¬p ∣ n) :
    charge displacement (p*n) + charge displacement n =
      ∑ a ∈ n.divisors, (ArithmeticFunction.moebius (n/a) : ℝ) *
        (qSequence displacement (p*a) - qSequence displacement (p*a-1)) :=
  mobiusDifference_prime_deletion_defect (qSequence displacement) hp hpn

/-- Conditional rigidity. The prime sign rule used for ordinary Möbius
weights, if proved for the actual displacement, forces both projections to
agree. Its premise is the arithmetic issue isolated by the defect identity. -/
theorem displacement_eq_zero_of_prime_deletion
    (hprime : ∀ p n : ℕ, p.Prime → ¬p ∣ n →
      charge displacement (p*n) = -charge displacement n) :
    displacement = 0 := by
  let c := charge displacement 1
  have hmu (n : ℕ) : charge displacement n = c * (ArithmeticFunction.moebius n : ℝ) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases h0 : n = 0
      · subst n
        simp [charge, mobiusDifference]
      by_cases h1 : n = 1
      · subst n
        simp [c]
      by_cases hs : Squarefree n
      · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
        let k := n/p
        have hprod : p*k = n := Nat.mul_div_cancel' hpd
        have hsmall : k < n := Nat.div_lt_self (Nat.pos_of_ne_zero h0) hp.one_lt
        have hs' : Squarefree (p*k) := hprod.symm ▸ hs
        have hfree : ¬p ∣ k := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs')
        have hmob : ArithmeticFunction.moebius (p*k) = -ArithmeticFunction.moebius k := by
          rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
            (hp.coprime_iff_not_dvd.mpr hfree), ArithmeticFunction.moebius_apply_prime hp,
            neg_one_mul]
        calc
          charge displacement n = -charge displacement k := by
            rw [← hprod]
            exact hprime p k hp hfree
          _ = -(c * (ArithmeticFunction.moebius k : ℝ)) := by rw [ih k hsmall]
          _ = c * (ArithmeticFunction.moebius n : ℝ) := by
            rw [← hprod, hmob, Int.cast_neg]
            ring
      · have hz := QSquarefreeCompatibleHeads.nonsquarefree_charge_zero
          (qSequence displacement) n (fun m hm _ => displacement_difference_radical m hm)
          n (by omega) le_rfl hs
        simp only [charge, hz, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs,
          Int.cast_zero, mul_zero]
  have hf : qSequence displacement = fun n : ℕ => c * (if n = 0 then 0 else 1) := by
    apply mobiusDifference_injective_anchored
    · simp [qSequence_zero]
    · intro n hn
      rw [mobiusDifference_const_mul_fn, mobiusDifference_one n hn]
      exact hmu n
  apply displacement_eq_zero_of_residual_eq_zero
  apply residual_eq_zero_of_displacement_physically_bounded |c|
  intro n
  rw [hf]
  change |c * (if n = 0 then 0 else 1)| ≤ |c|
  split_ifs <;> simp [abs_nonneg]

/-- For the actual matched displacement, the ordinary Möbius prime-deletion
rule is exactly equivalent to equality of the two projections. -/
theorem displacement_eq_zero_iff_prime_deletion :
    displacement = 0 ↔ ∀ p n : ℕ, p.Prime → ¬p ∣ n →
      charge displacement (p*n) = -charge displacement n := by
  constructor
  · intro hd p n _ _
    have hz : qSequence (0 : QHilbert) = 0 := map_zero qSequenceLinear
    simp [hd, charge, hz, mobiusDifference]
  · exact displacement_eq_zero_of_prime_deletion

end RiemannResearch.RH.QPrimeSubtreeBudget
