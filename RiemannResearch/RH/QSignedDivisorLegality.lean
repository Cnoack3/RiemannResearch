/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.EvenPeriodicSquareJump
import RiemannResearch.RH.QParityGeometry
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Classification of finite signed divisibility combinations

Every finite signed sum of positive-conductor divisibility indicators is
even and periodic as an integer sequence. The square-jump identities
therefore force it to depend only on parity. This gives an exact
classification of its membership in the squarefree legal closure:

* its positive physical sequence must be two-periodic;
* its even value must vanish, or qOne must belong to the legal closure.

The finite squarefree span requires the even value to vanish.
All signs are retained. No actual constant membership or RH is asserted.

Source: independently developed continuation of the user-provided
QDivisorLegality_Research_2026-10-16 handoff, agenda item 3, 16 October 2026.
The handoff supplies the square-jump obstruction and the classification
question; the periodic-reflection proof is developed here.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QSignedDivisorLegality

open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity
open QDivisorLegality SquarefreeRadicalDifference
open RiemannResearch.Analysis.EvenPeriodicSquareJump

/-- Integer extension; the value at zero is used only for modular arithmetic. -/
def integerDivisorSum (s : Finset ℕ) (b : ℕ → ℝ) (z : ℤ) : ℝ :=
  ∑ m ∈ s, b m * (if (m : ℤ) ∣ z then 1 else 0)

theorem integerDivisorSum_even (s : Finset ℕ) (b : ℕ → ℝ) (z : ℤ) :
    integerDivisorSum s b (-z) = integerDivisorSum s b z := by
  simp [integerDivisorSum]

theorem integerDivisorSum_modular (s : Finset ℕ) (b : ℕ → ℝ)
    (u v : ℤ) (h : ((∏ m ∈ s, m : ℕ) : ℤ) ∣ u - v) :
    integerDivisorSum s b u = integerDivisorSum s b v := by
  apply Finset.sum_congr rfl
  intro m hm
  have hd : (m : ℤ) ∣ u - v :=
    dvd_trans (Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem (fun m : ℕ => m) hm)) h
  have he : (m : ℤ) ∣ u ↔ (m : ℤ) ∣ v := by
    constructor
    · intro hu
      have hv := dvd_sub hu hd
      have he : u - (u - v) = v := by ring
      rwa [he] at hv
    · intro hv
      have hu := dvd_add hd hv
      have he : u - v + v = u := by ring
      rwa [he] at hu
  simp only [he]

theorem qSequence_sum_divisors_integer
    (s : Finset ℕ) (b : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    qSequence (∑ m ∈ s, b m • qDivisor m) n = integerDivisorSum s b (n : ℤ) := by
  change qSequenceLinear (∑ m ∈ s, b m • qDivisor m) n = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ m ∈ s, b m * qSequence (qDivisor m) n) = _
  simp [integerDivisorSum, qSequence_qDivisor, positiveDivisor, Nat.ne_of_gt hn,
    Int.natCast_dvd_natCast]

theorem square_jump_integer_of_identities
    (x : QHilbert) (hx : ∀ a : ℕ, 2 ≤ a → qDifference x (a ^ 2) = qDifference x a)
    (f : ℤ → ℝ) (hf : ∀ n : ℕ, 0 < n → qSequence x n = f (n : ℤ)) :
    ∀ n : ℤ, 2 ≤ n →
      f (n ^ 2) - f (n ^ 2 - 1) = f n - f (n - 1) := by
  intro n hn
  let k := n.toNat
  have hkcast : (k : ℤ) = n := by dsimp [k]; omega
  have hk : 2 ≤ k := by omega
  have hk2 : 4 ≤ k ^ 2 := by nlinarith
  have he := hx k hk
  unfold qDifference at he
  rw [hf (k ^ 2) (by omega), hf (k ^ 2 - 1) (by omega),
    hf k (by omega), hf (k - 1) (by omega)] at he
  rw [Int.natCast_sub (by omega : 1 ≤ k ^ 2),
    Int.natCast_sub (by omega : 1 ≤ k), Nat.cast_pow, Nat.cast_one, hkcast] at he
  exact he

theorem signed_divisor_two_periodic_of_square_jumps
    (s : Finset ℕ) (b : ℕ → ℝ) (hs : ∀ m ∈ s, 0 < m)
    (hx : ∀ a : ℕ, 2 ≤ a →
      qDifference (∑ m ∈ s, b m • qDivisor m) (a ^ 2) =
        qDifference (∑ m ∈ s, b m • qDivisor m) a)
    (n : ℕ) (hn : 0 < n) :
    qSequence (∑ m ∈ s, b m • qDivisor m) (n + 2) =
      qSequence (∑ m ∈ s, b m • qDivisor m) n := by
  have hL : 0 < (∏ m ∈ s, m) := Finset.prod_pos hs
  have h := even_periodic_square_jump_two_periodic
    (integerDivisorSum s b) (∏ m ∈ s, m : ℕ)
    (by exact_mod_cast hL)
    (integerDivisorSum_modular s b) (integerDivisorSum_even s b)
    (square_jump_integer_of_identities _ hx _ (qSequence_sum_divisors_integer s b))
    ((n : ℤ) + 1) (by omega)
  rw [qSequence_sum_divisors_integer s b (n + 2) (by omega),
    qSequence_sum_divisors_integer s b n hn]
  have hc1 : ((n + 2 : ℕ) : ℤ) = ((n : ℤ) + 1) + 1 := by omega
  have hc2 : ((n : ℤ) + 1) - 1 = (n : ℤ) := by ring
  simpa only [hc1, hc2] using h


/-- Closure membership forces a finite signed indicator sum to depend only on parity. -/
theorem signed_divisor_closure_two_periodic
    (s : Finset ℕ) (b : ℕ → ℝ) (hs : ∀ m ∈ s, 0 < m)
    (hx : (∑ m ∈ s, b m • qDivisor m) ∈ qSquarefreeCRTSpan.topologicalClosure)
    (n : ℕ) (hn : 0 < n) :
    qSequence (∑ m ∈ s, b m • qDivisor m) (n + 2) =
      qSequence (∑ m ∈ s, b m • qDivisor m) n :=
  signed_divisor_two_periodic_of_square_jumps s b hs
    (fun a ha => squarefree_closure_difference_square a ha _ hx) n hn

/-- On finite signed divisor sums, the square-jump tests characterize parity dependence. -/
theorem signed_divisor_square_jumps_iff_two_periodic
    (s : Finset ℕ) (b : ℕ → ℝ) (hs : ∀ m ∈ s, 0 < m) :
    (∀ a : ℕ, 2 ≤ a →
      qDifference (∑ m ∈ s, b m • qDivisor m) (a ^ 2) =
        qDifference (∑ m ∈ s, b m • qDivisor m) a) ↔
    (∀ n : ℕ, 0 < n →
      qSequence (∑ m ∈ s, b m • qDivisor m) (n + 2) =
        qSequence (∑ m ∈ s, b m • qDivisor m) n) := by
  constructor
  · exact signed_divisor_two_periodic_of_square_jumps s b hs
  · intro hp a ha
    have hg : qResidue 2 ∈ qSquarefreeCRTSpan :=
      Submodule.subset_span ⟨⟨2, ⟨by decide, Nat.prime_two.squarefree⟩⟩, rfl⟩
    rw [qHilbert_eq_parity_of_two_periodic _ hp]
    simp only [qDifference_add, qDifference_smul,
      qDifference_qOne (a ^ 2) (by nlinarith),
      qDifference_qOne a ha, squarefree_span_difference_square a ha (qResidue 2) hg]

theorem signed_divisor_closure_eq_parity
    (s : Finset ℕ) (b : ℕ → ℝ) (hs : ∀ m ∈ s, 0 < m)
    (hx : (∑ m ∈ s, b m • qDivisor m) ∈ qSquarefreeCRTSpan.topologicalClosure) :
    (∑ m ∈ s, b m • qDivisor m) =
      (qSequence (∑ m ∈ s, b m • qDivisor m) 2) • qOne +
      (2 * (qSequence (∑ m ∈ s, b m • qDivisor m) 1 -
        qSequence (∑ m ∈ s, b m • qDivisor m) 2)) • qResidue 2 :=
  qHilbert_eq_parity_of_two_periodic _ (signed_divisor_closure_two_periodic s b hs hx)

theorem scalar_qOne_mem_squarefreeClosure_iff (α : ℝ) :
    α • qOne ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      α = 0 ∨ qOne ∈ qSquarefreeCRTSpan.topologicalClosure := by
  constructor
  · intro h
    by_cases ha : α = 0
    · exact Or.inl ha
    · right
      have he := qSquarefreeCRTSpan.topologicalClosure.smul_mem α⁻¹ h
      simpa [smul_smul, ha] using he
  · rintro (rfl | h)
    · simp
    · exact qSquarefreeCRTSpan.topologicalClosure.smul_mem α h

theorem signed_divisor_mem_squarefreeClosure_iff
    (s : Finset ℕ) (b : ℕ → ℝ) (hs : ∀ m ∈ s, 0 < m) :
    (∑ m ∈ s, b m • qDivisor m) ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      (∀ n : ℕ, 0 < n →
        qSequence (∑ m ∈ s, b m • qDivisor m) (n + 2) =
          qSequence (∑ m ∈ s, b m • qDivisor m) n) ∧
      (qSequence (∑ m ∈ s, b m • qDivisor m) 2 = 0 ∨
        qOne ∈ qSquarefreeCRTSpan.topologicalClosure) := by
  have hg : qResidue 2 ∈ qSquarefreeCRTSpan.topologicalClosure :=
    qSquarefreeCRTSpan.le_topologicalClosure
      (Submodule.subset_span ⟨⟨2, ⟨by decide, Nat.prime_two.squarefree⟩⟩, rfl⟩)
  constructor
  · intro h
    have hp := signed_divisor_closure_two_periodic s b hs h
    refine ⟨hp, (scalar_qOne_mem_squarefreeClosure_iff _).mp ?_⟩
    have he := qSquarefreeCRTSpan.topologicalClosure.sub_mem h
      (qSquarefreeCRTSpan.topologicalClosure.smul_mem
        (2 * (qSequence (∑ m ∈ s, b m • qDivisor m) 1 -
          qSequence (∑ m ∈ s, b m • qDivisor m) 2)) hg)
    have heq := congrArg (fun y : QHilbert =>
      y - (2 * (qSequence (∑ m ∈ s, b m • qDivisor m) 1 -
        qSequence (∑ m ∈ s, b m • qDivisor m) 2)) • qResidue 2)
      (qHilbert_eq_parity_of_two_periodic _ hp)
    rw [add_sub_cancel_right] at heq
    exact heq ▸ he
  · rintro ⟨hp, hconstant⟩
    rw [qHilbert_eq_parity_of_two_periodic _ hp]
    exact qSquarefreeCRTSpan.topologicalClosure.add_mem
      ((scalar_qOne_mem_squarefreeClosure_iff _).mpr hconstant)
      (qSquarefreeCRTSpan.topologicalClosure.smul_mem _ hg)

/-- The finite squarefree span allows exactly parity sums with zero even value. -/
theorem signed_divisor_mem_squarefreeSpan_iff
    (s : Finset ℕ) (b : ℕ → ℝ) (hs : ∀ m ∈ s, 0 < m) :
    (∑ m ∈ s, b m • qDivisor m) ∈ qSquarefreeCRTSpan ↔
      (∀ n : ℕ, 0 < n →
        qSequence (∑ m ∈ s, b m • qDivisor m) (n + 2) =
          qSequence (∑ m ∈ s, b m • qDivisor m) n) ∧
      qSequence (∑ m ∈ s, b m • qDivisor m) 2 = 0 := by
  constructor
  · intro hx
    have hp := signed_divisor_closure_two_periodic s b hs
      (qSquarefreeCRTSpan.le_topologicalClosure hx)
    refine ⟨hp, ?_⟩
    have hsub : qSquarefreeCRTSpan ≤
        Submodule.span ℝ (qResidue '' {d : ℕ | 2 ≤ d}) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨d, rfl⟩
      exact Submodule.subset_span ⟨d.val, d.property.1, rfl⟩
    obtain ⟨L, hL, hv⟩ := residueSpan_vanishes_at_common_multiple
      {d : ℕ | 2 ≤ d} (fun _ hd => hd) _ (hsub hx)
    have hz := hv (2 * L) ⟨2, by ring⟩
    have he := values_of_two_periodic
      (qSequence (∑ m ∈ s, b m • qDivisor m)) hp (2 * L) (by omega)
    have hd : 2 ∣ 2 * L := ⟨L, rfl⟩
    rw [if_pos hd] at he
    exact he ▸ hz
  · rintro ⟨hp, hz⟩
    rw [qHilbert_eq_parity_of_two_periodic _ hp, hz, zero_smul, zero_add]
    exact qSquarefreeCRTSpan.smul_mem _
      (Submodule.subset_span ⟨⟨2, ⟨by decide, Nat.prime_two.squarefree⟩⟩, rfl⟩)

/-- Under constant membership the full criterion reduces exactly to parity dependence. -/
theorem signed_divisor_mem_squarefreeClosure_iff_of_qOne_mem
    (hOne : qOne ∈ qSquarefreeCRTSpan.topologicalClosure)
    (s : Finset ℕ) (b : ℕ → ℝ) (hs : ∀ m ∈ s, 0 < m) :
    (∑ m ∈ s, b m • qDivisor m) ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      ∀ n : ℕ, 0 < n →
        qSequence (∑ m ∈ s, b m • qDivisor m) (n + 2) =
          qSequence (∑ m ∈ s, b m • qDivisor m) n := by
  rw [signed_divisor_mem_squarefreeClosure_iff s b hs]
  simp only [hOne, or_true, and_true]

/-- If the constant is absent, finite signed sums gain no membership by closure. -/
theorem signed_divisor_mem_closure_iff_mem_span_of_qOne_not_mem
    (hOne : qOne ∉ qSquarefreeCRTSpan.topologicalClosure)
    (s : Finset ℕ) (b : ℕ → ℝ) (hs : ∀ m ∈ s, 0 < m) :
    (∑ m ∈ s, b m • qDivisor m) ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      (∑ m ∈ s, b m • qDivisor m) ∈ qSquarefreeCRTSpan := by
  rw [signed_divisor_mem_squarefreeClosure_iff s b hs,
    signed_divisor_mem_squarefreeSpan_iff s b hs]
  simp only [hOne, or_false]

end RiemannResearch.RH.QSignedDivisorLegality
