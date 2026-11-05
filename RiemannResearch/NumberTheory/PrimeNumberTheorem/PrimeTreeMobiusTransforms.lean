/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeMobiusSubtree
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # Two exact transforms for rough Möbius partial sums
Section 9 of *Prime trees, fractional parts, and zeta zeros*. The direct
transform expands the finite Euler factors. Its inverse sums over smooth
indices. The inverse also appears as (3.1) in K. Alladi, J. Number Theory
14 (1982), 86–98, doi:10.1016/0022-314X(82)90060-9. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder

/-- An alternating sum over products of subsets of the deleted primes. -/
theorem mertens_eq_rough_subset_sum (B : Finset ℕ) (hB : ∀ q ∈ B, q.Prime) (n : ℕ) :
    M (n : ℝ) = ∑ T ∈ B.powerset, (-1:ℝ)^T.card * roughSum B (n / ∏ q ∈ T, q) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [roughSum_empty]
  | @insert p B hfresh ih =>
    have hsmall := fun q (hq : q ∈ B) => hB q (Finset.mem_insert_of_mem hq)
    have hp := hB p (Finset.mem_insert_self ..)
    rw [ih hsmall, Finset.sum_powerset_insert hfresh, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro T hT
    have hT' : p ∉ T := fun ht => hfresh (Finset.mem_powerset.mp hT ht)
    rw [roughSum_delete_factor hsmall hp hfresh, Finset.card_insert_of_notMem hT',
      Finset.prod_insert hT', pow_succ, Nat.div_div_eq_div_mul,
      Nat.mul_comm p (∏ q ∈ T, q)]
    ring

/-- All prime factors of a smooth index lie in the finite prime set. -/
def Smooth (B : Finset ℕ) (a : ℕ) : Prop := ∀ q, q.Prime → q ∣ a → q ∈ B

private def smoothTransform (B : Finset ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact ∑ j ∈ Finset.range n, if Smooth B (j+1) then f (n/(j+1)) else 0

private theorem sum_multiples (p : ℕ) (g : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, if p ∣ j+1 then g ((j+1)/p) else 0) =
      ∑ j ∈ Finset.range (n/p), g (j+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hd : p ∣ n+1
    · rw [if_pos hd, Nat.succ_div_of_dvd hd, Finset.sum_range_succ]
    · simp [hd, Nat.succ_div_of_not_dvd hd]

private theorem smoothTransform_add_prime {p : ℕ} (hp : p.Prime) (B : Finset ℕ)
    (hfresh : p ∉ B) (f : ℕ → ℝ) (n : ℕ) :
    smoothTransform (insert p B) f n =
      smoothTransform B f n + smoothTransform (insert p B) f (n/p) := by
  classical
  let g (k : ℕ) := if Smooth (insert p B) k then f ((n/p)/k) else 0
  have hterm (a : ℕ) : (if Smooth (insert p B) a then f (n/a) else 0) =
      (if Smooth B a then f (n/a) else 0) + (if p ∣ a then g (a/p) else 0) := by
    by_cases hd : p ∣ a
    · have hprod : p * (a/p) = a := Nat.mul_div_cancel' hd
      have hnB : ¬Smooth B a := fun h => hfresh (h p hp hd)
      have hie : Smooth (insert p B) a ↔ Smooth (insert p B) (a/p) := by
        constructor
        · intro h q hq hdiv
          apply h q hq
          rw [← hprod]
          exact hdiv.mul_left p
        · intro h q hq hdiv
          rw [← hprod] at hdiv
          rcases hq.dvd_mul.mp hdiv with hqp | hqk
          · exact Finset.mem_insert.mpr (Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqp))
          · exact h q hq hqk
      have hh : (n/p)/(a/p) = n/a := by rw [Nat.div_div_eq_div_mul,hprod]
      simp only [g, if_neg hnB, if_pos hd, hie, zero_add, hh]
    · have hie : Smooth (insert p B) a ↔ Smooth B a := by
        constructor
        · intro h q hq hdiv
          rcases Finset.mem_insert.mp (h q hq hdiv) with he | hmem
          · exact (hd (he ▸ hdiv)).elim
          · exact hmem
        · intro h q hq hdiv
          exact Finset.mem_insert_of_mem (h q hq hdiv)
      simp only [hie,if_neg hd,add_zero]
  unfold smoothTransform
  calc
    _ = ∑ j ∈ Finset.range n, ((if Smooth B (j+1) then f (n/(j+1)) else 0)
        + (if p ∣ j+1 then g ((j+1)/p) else 0)) :=
      Finset.sum_congr rfl fun j _ => hterm (j+1)
    _ = _ := by rw [Finset.sum_add_distrib, sum_multiples]

open Classical in
/-- The inverse transform is a finite sum over all smooth indices up to the
cutoff, with their full multiplicity of prime powers. -/
theorem roughSum_eq_smooth_mertens (B : Finset ℕ) (hB : ∀ q ∈ B, q.Prime) (n : ℕ) :
    roughSum B n =
      ∑ j ∈ Finset.range n, if Smooth B (j+1) then M ((n/(j+1) : ℕ) : ℝ) else 0 := by
  classical
  change roughSum B n = smoothTransform B (fun k => M (k : ℝ)) n
  induction B using Finset.induction_on generalizing n with
  | empty =>
    have hz (a : ℕ) : Smooth ∅ a ↔ a = 1 := by
      constructor
      · intro h
        by_contra hne
        obtain ⟨q,hq,hqa⟩ := Nat.exists_prime_and_dvd hne
        exact Finset.notMem_empty q (h q hq hqa)
      · rintro rfl q hq hdiv
        exact (hq.not_dvd_one hdiv).elim
    cases n with
    | zero => simp [roughSum,smoothTransform]
    | succ n => simp [roughSum_empty,smoothTransform,hz]
  | @insert p B hfresh ih =>
    have hsmall := fun q (hq : q ∈ B) => hB q (Finset.mem_insert_of_mem hq)
    have hp := hB p (Finset.mem_insert_self ..)
    induction n using Nat.strong_induction_on with
    | h n rec =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [roughSum,smoothTransform]
      · let f : ℕ → ℝ := fun k => M (k : ℝ)
        have hrough := roughSum_delete_factor hsmall hp hfresh n
        have htrans := smoothTransform_add_prime hp B hfresh f n
        have hB' : roughSum B n = smoothTransform B f n := ih hsmall n
        have hrec := rec (n/p) (Nat.div_lt_self hn hp.one_lt)
        change roughSum (insert p B) n = smoothTransform (insert p B) f n
        linarith

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
