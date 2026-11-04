/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeFiniteDualClosure
import RiemannResearch.RH.QSquarefreeJumpDistance
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.PrimeValuationHilbertBasis
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.NumberTheory.RadicalFiberSeparation
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Legality of arbitrary single-prime valuation factors

Source: elementary deduction from the existing radical-jump and affine-divisor
obstructions, developed for the product-structure research agenda, 4 November
2026. This extends PrimeValuationClosureObstruction from the valuation itself
to every scalar function of one valuation. It does not prove constant legality.
-/

noncomputable section
namespace RiemannResearch.RH.QPrimeValuationFactorLegality
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity
open SquarefreeRadicalDifference QSquarefreeFiniteDualClosure
open QSquarefreeJumpDistance QDivisorLegality UniqueFactorizationMonoid
open PrimeValuationBasis

theorem prime_power_predecessor_factorization (p k : ℕ) (hp : p.Prime)
    (hk : k ≠ 0) : (p ^ k - 1).factorization p = 0 := by
  have hpow : 2 ≤ p ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have hpos : 1 ≤ p ^ j :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero j hp.ne_zero)
    rw [pow_succ]
    have := hp.two_le
    nlinarith
  have hpd : p ∣ p ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [pow_succ]
    exact dvd_mul_left _ _
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hprev
  have hone := Nat.dvd_sub hpd hprev
  rw [show p ^ k - (p ^ k - 1) = 1 by omega] at hone
  have := Nat.dvd_one.mp hone
  exact hp.ne_one this

/-- Radical compatibility collapses every positive valuation level to level one. -/
theorem positive_levels_equal (p : ℕ) (hp : p.Prime) (φ : ℕ → ℝ)
    (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n → qSequence x n = φ (n.factorization p))
    (hx : x ∈ radicalCompatible) (k : ℕ) (hk : k ≠ 0) : φ k = φ 1 := by
  have hp2 := hp.two_le
  have hpow : 2 ≤ p ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have hpos : 1 ≤ p ^ j :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero j hp.ne_zero)
    rw [pow_succ]
    nlinarith
  have h := hx (p ^ k) hpow
  rw [Nat.radical_pow_eq_of_squarefree hp2 hp.squarefree hk] at h
  unfold qDifference at h
  rw [hseq _ (by omega), hseq _ (by omega), hseq _ hp.pos,
    hseq _ (by omega), Nat.factorization_pow_self hp,
    prime_power_predecessor_factorization p k hp hk, hp.factorization_self,
    Nat.factorization_eq_zero_of_lt (by omega : p - 1 < p)] at h
  linarith

/-- Every radical-compatible valuation factor is an affine divisibility indicator. -/
theorem valuation_factor_binary (p : ℕ) (hp : p.Prime) (φ : ℕ → ℝ)
    (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n → qSequence x n = φ (n.factorization p))
    (hx : x ∈ radicalCompatible) :
    x = φ 0 • qOne + (φ 1 - φ 0) • qDivisor p := by
  apply qSequence_injective
  funext n
  have hadd := congrFun (qSequenceLinear.map_add
    (φ 0 • qOne) ((φ 1 - φ 0) • qDivisor p)) n
  have hsmul0 := congrFun (qSequenceLinear.map_smul (φ 0) qOne) n
  have hsmul1 := congrFun (qSequenceLinear.map_smul (φ 1 - φ 0) (qDivisor p)) n
  change qSequence (φ 0 • qOne + (φ 1 - φ 0) • qDivisor p) n =
    qSequence (φ 0 • qOne) n + qSequence ((φ 1 - φ 0) • qDivisor p) n at hadd
  change qSequence (φ 0 • qOne) n = φ 0 * qSequence qOne n at hsmul0
  change qSequence ((φ 1 - φ 0) • qDivisor p) n =
    (φ 1 - φ 0) * qSequence (qDivisor p) n at hsmul1
  change qSequence x n = qSequence (φ 0 • qOne + (φ 1 - φ 0) • qDivisor p) n
  rw [hadd, hsmul0, hsmul1]
  simp only [qSequence_qOne, qSequence_qDivisor, Pi.smul_apply, smul_eq_mul]
  by_cases hn : n = 0
  · subst n
    simp [qSequence_zero, qOneSequence, positiveDivisor]
  · rw [hseq n (Nat.pos_of_ne_zero hn)]
    by_cases hdiv : p ∣ n
    · have hv : n.factorization p ≠ 0 :=
        ne_of_gt (hp.factorization_pos_of_dvd hn hdiv)
      rw [positive_levels_equal p hp φ x hseq hx _ hv]
      simp [qOneSequence, positiveDivisor, hn, hdiv] <;> ring
    · rw [Nat.factorization_eq_zero_of_not_dvd hdiv]
      simp [qOneSequence, positiveDivisor, hn, hdiv]

/-- Every legal factor of a single odd-prime valuation is constant. -/
theorem odd_prime_legal_factor_constant (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (φ : ℕ → ℝ) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n → qSequence x n = φ (n.factorization p))
    (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure) :
    x = φ 0 • qOne := by
  have hb := valuation_factor_binary p hp φ x hseq
    (legalClosure_le_radicalCompatible hx)
  have hmem : φ 0 • qOne + (φ 1 - φ 0) • qDivisor p ∈
      qSquarefreeCRTSpan.topologicalClosure := by rw [← hb]; exact hx
  have hz := ((affine_qDivisor_mem_squarefreeClosure_iff p hp3
    (φ 0) (φ 1 - φ 0)).mp hmem).1
  simpa only [hz, zero_smul, add_zero] using hb

/-- A nonzero constant-level legal odd-prime factor supplies the target closure. -/
theorem target_mem_of_nonzero_odd_prime_legal_factor
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (φ : ℕ → ℝ)
    (hφ : φ 0 ≠ 0) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n → qSequence x n = φ (n.factorization p))
    (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  have he := odd_prime_legal_factor_constant p hp hp3 φ x hseq hx
  have hmem := qSquarefreeCRTSpan.topologicalClosure.smul_mem (φ 0)⁻¹ hx
  rw [he, smul_smul, inv_mul_cancel₀ hφ, one_smul] at hmem
  exact hmem

/-- The actual closed valuation subspace intersects legality only in constants
at every odd prime. This does not assume those constants are legal. -/
theorem valuationSpace_legal_constant (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (x : QHilbert) (hv : x ∈ valuationSpace p)
    (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure) :
    x = qSequence x 1 • qOne := by
  have he := odd_prime_legal_factor_constant p hp hp3
    (fun k => qSequence x (p ^ k)) x (fun n hn => hv n (ne_of_gt hn)) hx
  simpa only [pow_zero] using he

/-- The nonzero-vector condition is enough; no separately named amplitude is needed. -/
theorem target_mem_of_nonzero_valuationSpace_legal
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (x : QHilbert)
    (hv : x ∈ valuationSpace p) (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure)
    (hxn : x ≠ 0) : qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  have he := valuationSpace_legal_constant p hp hp3 x hv hx
  have hc : qSequence x 1 ≠ 0 := by
    intro hz
    apply hxn
    simpa only [hz, zero_smul] using he
  have hconstmem : qSequence x 1 • qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
    rw [← he]
    exact hx
  have hmem := qSquarefreeCRTSpan.topologicalClosure.smul_mem
    (qSequence x 1)⁻¹ hconstmem
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hmem
  exact hmem

/-- Conditional RH reduction: existence of a nonzero legal odd-prime valuation
factor remains the explicit arithmetic provider. -/
theorem riemannHypothesis_of_nonzero_valuationSpace_legal
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (x : QHilbert)
    (hv : x ∈ valuationSpace p) (hx : x ∈ qSquarefreeCRTSpan.topologicalClosure)
    (hxn : x ≠ 0) : RiemannHypothesis := by
  apply ZetaTwoParetoTransfer.riemannHypothesis_of_qOne_mem_squarefree_closure
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact target_mem_of_nonzero_valuationSpace_legal p hp hp3 x hv hx hxn

/-- Finite radical constraints alone force an odd-prime valuation factor
to be constant. No norm-closed legality premise is needed. -/
theorem odd_prime_compatible_factor_constant (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (φ : ℕ → ℝ) (x : QHilbert)
    (hseq : ∀ n : ℕ, 0 < n → qSequence x n = φ (n.factorization p))
    (hx : x ∈ radicalCompatible) : x = φ 0 • qOne := by
  have hb := valuation_factor_binary p hp φ x hseq hx
  have ha : 2 ≤ p - 1 := by omega
  have ha2 : 2 ≤ (p - 1) ^ 2 := by nlinarith
  have hsq := hx ((p - 1) ^ 2) ha2
  have hbase := hx (p - 1) ha
  rw [radical_pow (p - 1) (by decide : (2 : ℕ) ≠ 0)] at hsq
  have hj : qDifference x ((p - 1) ^ 2) - qDifference x (p - 1) = 0 := by
    linarith
  rw [hb, qDifference_add, qDifference_add,
    qDifference_smul, qDifference_smul, qDifference_smul, qDifference_smul,
    qDifference_qOne _ ha2, qDifference_qOne _ ha] at hj
  have hdiv := congrArg (fun t : ℝ => (φ 1 - φ 0) * t)
    (qDivisor_square_jump_defect p hp3)
  have hz : φ 1 - φ 0 = 0 := by nlinarith
  simpa only [hz, zero_smul, add_zero] using hb

/-- Exact intersection with the ambient single-prime valuation subspace. -/
theorem valuationSpace_radicalCompatible_iff_constant
    (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (x : QHilbert)
    (hv : x ∈ valuationSpace p) :
    x ∈ radicalCompatible ↔ x = qSequence x 1 • qOne := by
  constructor
  · intro hx
    simpa only [pow_zero] using odd_prime_compatible_factor_constant p hp hp3
      (fun k => qSequence x (p ^ k)) x (fun n hn => hv n (ne_of_gt hn)) hx
  · intro hx
    rw [hx]
    exact radicalCompatible.smul_mem _ qOne_mem_radicalCompatible

end RiemannResearch.RH.QPrimeValuationFactorLegality
