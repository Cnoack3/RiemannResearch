/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeTreeMobiusSubtree
import RiemannResearch.RH.QPrimeSubtreeBudget
import Mathlib.NumberTheory.PrimeCounting

/-! # The actual ordered prefix and the rough prime cylinder
Section 9 of *Prime trees, fractional parts, and zeta zeros*. On squarefree
conductors a root is a prefix exactly when all extra factors exceed its
largest prime. This connects the cylinder transfer to the recursive parent
from the displacement tree, including the exceptional empty prefix at 1. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
open RiemannResearch.RH.QPrimeSubtreeBudget

/-- The recursive prefix relation is equivalent to a factorization whose
remaining primes exceed the largest prime of the root. -/
theorem prefix_iff_factor {r y : ℕ} (hr : 1 < r) (hy : y.Prime)
    (hyr : y ∣ r) (hmax : ∀ q, q.Prime → q ∣ r → q ≤ y) (m : ℕ) (hs : Squarefree m) :
    r ∈ prefixes m ↔ ∃ k, m = r*k ∧ ∀ q ∈ Nat.primesLE y, ¬q ∣ k := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : 1 < m
    · let p := m.primeFactors.max' (Nat.nonempty_primeFactors.mpr hm)
      have hpMem : p ∈ m.primeFactors := Finset.max'_mem _ _
      have hp := Nat.prime_of_mem_primeFactors hpMem
      have hpdiv := Nat.dvd_of_mem_primeFactors hpMem
      have hparent : parent m = m/p := dif_pos hm
      obtain ⟨_, hlt, hdvd⟩ := parent_spec m hm
      have hprod : parent m * p = m := by rw [hparent, Nat.div_mul_cancel hpdiv]
      have hcop : ¬ p ∣ parent m := by
        have hs' : Squarefree (parent m * p) := by rwa [hprod]
        exact hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hs').symm
      have hrec := ih (parent m) hlt (hs.squarefree_of_dvd hdvd)
      have hpath : prefixes m = insert m (prefixes (parent m)) := by
        rw [prefixes]; simp [hm]
      rw [hpath, Finset.mem_insert]
      constructor
      · rintro (rfl | hprevious)
        · exact ⟨1, by simp, fun q hq => (Nat.prime_of_mem_primesLE hq).not_dvd_one⟩
        · obtain ⟨k, hk, hgood⟩ := hrec.mp hprevious
          have hrdiv : r ∣ parent m := ⟨k,hk⟩
          have hyd := hyr.trans hrdiv
          have hyle : y ≤ p := Finset.le_max' _ y (hy.mem_primeFactors (hyd.trans hdvd) hs.ne_zero)
          have hyne : y ≠ p := fun he => hcop (he ▸ hyd)
          have hyp := lt_of_le_of_ne hyle hyne
          refine ⟨k*p, ?_, ?_⟩
          · calc m = parent m * p := hprod.symm
                 _ = r*(k*p) := by rw [hk, Nat.mul_assoc]
          · intro q hq hdiv
            rcases (Nat.prime_of_mem_primesLE hq).dvd_mul.mp hdiv with hqk | hqp
            · exact hgood q hq hqk
            · have he := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primesLE hq) hp).mp hqp
              have hh := Nat.le_of_mem_primesLE hq
              omega
      · rintro ⟨k, hk, hgood⟩
        by_cases hk1 : k = 1
        · left; simpa [hk1] using hk.symm
        · right
          obtain ⟨q, hq, hqk⟩ := Nat.exists_prime_and_dvd hk1
          have hyq : y < q := by
            by_contra! hh
            exact hgood q (Nat.mem_primesLE.mpr ⟨hh,hq⟩) hqk
          have hqm : q ∣ m := by rw [hk]; exact hqk.mul_left r
          have hqp : q ≤ p := Finset.le_max' _ q (hq.mem_primeFactors hqm hs.ne_zero)
          have hnot : ¬ p ∣ r := fun hd => (not_le_of_gt (hyq.trans_le hqp)) (hmax p hp hd)
          have hpProd : p ∣ r*k := by rwa [← hk]
          obtain ⟨u,hu⟩ := (hp.dvd_mul.mp hpProd).resolve_left hnot
          apply hrec.mpr
          refine ⟨u, ?_, ?_⟩
          · have hform : m = p*(r*u) := by rw [hk,hu]; ring
            rw [hparent,hform,Nat.mul_div_cancel_left _ hp.pos]
          · intro a ha hau
            apply hgood a ha
            rw [hu]
            exact hau.mul_left p
    · constructor
      · intro hmem
        obtain ⟨_, hle⟩ := prefix_bounds hmem
        omega
      · rintro ⟨k,hk,_⟩
        have hdiv : r ∣ m := ⟨k,hk⟩
        have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) hdiv
        omega

/-- The initial prime list up to and including the maximum prime of the root. -/
def forbiddenThroughRoot (r : ℕ) : Finset ℕ :=
  if h : 1 < r then Nat.primesLE (r.primeFactors.max' (Nat.nonempty_primeFactors.mpr h)) else ∅

/-- The forbidden set consists of primes and contains every prime of the root. -/
theorem forbidden_spec {r : ℕ} (hr : Squarefree r) :
    (∀ p ∈ forbiddenThroughRoot r, p.Prime) ∧
      ∀ q, q.Prime → q ∣ r → q ∈ forbiddenThroughRoot r := by
  by_cases h : 1 < r
  · rw [forbiddenThroughRoot, dif_pos h]
    exact ⟨fun _ hp => Nat.prime_of_mem_primesLE hp, fun q hq hqr =>
      Nat.mem_primesLE.mpr ⟨Finset.le_max' _ q (hq.mem_primeFactors hqr hr.ne_zero),hq⟩⟩
  · have he : r = 1 := by have := hr.ne_zero; omega
    subst r
    constructor
    · intro q hq
      simp [forbiddenThroughRoot] at hq
    · intro q hq hq1
      exact (hq.not_dvd_one hq1).elim

/-- Sum of ordinary Möbius weights over the repository's actual recursive
prefixes. The empty root is included separately because `prefixes` lists only
nonroot vertices. -/
def orderedSubtree (r n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, if r = 1 ∨ r ∈ prefixes (j+1)
    then (ArithmeticFunction.moebius (j+1) : ℝ) else 0

theorem orderedSubtree_eq_cylinder {r : ℕ} (hr : Squarefree r) (n : ℕ) :
    orderedSubtree r n = cylinder r (forbiddenThroughRoot r) n := by
  classical
  by_cases h : 1 < r
  · let y := r.primeFactors.max' (Nat.nonempty_primeFactors.mpr h)
    have hym : y ∈ r.primeFactors := Finset.max'_mem _ _
    have hhigh (q : ℕ) (hq : q.Prime) (hd : q ∣ r) : q ≤ y :=
      Finset.le_max' _ _ (hq.mem_primeFactors hd hr.ne_zero)
    unfold orderedSubtree cylinder
    rw [forbiddenThroughRoot, dif_pos h]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hsq : Squarefree (j+1)
    · have h1 : r ≠ 1 := by omega
      have he : r ∈ prefixes (j+1) ↔ r ∣ j+1 ∧ ∀ q ∈ Nat.primesLE y, ¬q ∣ (j+1)/r := by
        rw [prefix_iff_factor h (Nat.prime_of_mem_primeFactors hym)
          (Nat.dvd_of_mem_primeFactors hym) hhigh (j+1) hsq]
        constructor
        · rintro ⟨k,hk,hgood⟩
          refine ⟨⟨k,hk⟩, ?_⟩
          simpa only [hk, Nat.mul_div_cancel_left _ (show 0 < r by omega)] using hgood
        · rintro ⟨hd,hgood⟩
          exact ⟨(j+1)/r, (Nat.mul_div_cancel' hd).symm, hgood⟩
      by_cases hmem : r ∈ prefixes (j+1)
      · rw [if_pos (Or.inr hmem), if_pos (he.mp hmem)]
      · have hno : ¬(r = 1 ∨ r ∈ prefixes (j+1)) := fun h' => h'.elim h1 hmem
        rw [if_neg hno, if_neg (mt he.mpr hmem)]
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  · have he : r = 1 := by have := hr.ne_zero; omega
    subst r
    simp [orderedSubtree,cylinder,forbiddenThroughRoot]

/-- At a prime root the ordered-tree sum is the explicit prime cylinder
appearing in the moving-root prime-counting formula. -/
theorem orderedSubtree_prime_eq_cylinder {p : ℕ} (hp : p.Prime) (n : ℕ) :
    orderedSubtree p n = cylinder p (Nat.primesLE p) n := by
  rw [orderedSubtree_eq_cylinder hp.squarefree]
  simp [forbiddenThroughRoot, hp.one_lt, hp.primeFactors]

theorem mertens_iff_orderedSubtree {r : ℕ} (hr : Squarefree r) {a : ℝ} (ha : 0 < a) :
    PowerBound a (fun n => M (n : ℝ)) ↔ PowerBound a (orderedSubtree r) := by
  rw [funext (orderedSubtree_eq_cylinder hr)]
  exact mertens_iff_cylinder hr (Nat.pos_of_ne_zero hr.ne_zero) _ (forbidden_spec hr).1
    (forbidden_spec hr).2 ha

/-- The natural-cutoff bound and the paper's bound at every real cutoff
agree because each summatory function is constant between consecutive integers. -/
theorem ordered_powerBound_iff_real_cutoffs (r : ℕ) {a : ℝ} (ha : 0 < a) :
    PowerBound a (orderedSubtree r) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X → |orderedSubtree r ⌊X⌋₊| ≤ C * X^a := by
  constructor
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC, fun X hX => ?_⟩
    exact (h ⌊X⌋₊).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
      (Nat.floor_le (zero_le_one.trans hX)) ha.le) hC)
  · rintro ⟨C,hC,h⟩
    refine ⟨C,hC,fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [orderedSubtree, Real.zero_rpow ha.ne']
    · simpa only [Nat.floor_natCast] using h (n:ℝ) (by exact_mod_cast hn)

/-- At root 6 the surviving squarefree nodes are exactly the multiples of 6. -/
theorem orderedSubtree_six (n : ℕ) :
    orderedSubtree 6 n = ∑ j ∈ Finset.range n,
      if 6 ∣ j+1 then (ArithmeticFunction.moebius (j+1) : ℝ) else 0 := by
  classical
  have h6 : Squarefree (6:ℕ) :=
    (Nat.squarefree_mul (by decide : Nat.Coprime 2 3)).mpr
      ⟨Nat.prime_two.squarefree,Nat.prime_three.squarefree⟩
  have hfac : (6:ℕ).primeFactors = {2,3} := by
    rw [show (6:ℕ) = 2*3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]
    decide
  have hn : 1 < (6:ℕ) := by decide
  have hmax : (6:ℕ).primeFactors.max' (Nat.nonempty_primeFactors.mpr hn) = 3 := by
    apply le_antisymm
    · apply Finset.max'_le
      intro q hq
      rw [hfac] at hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      omega
    · apply Finset.le_max'
      rw [hfac]
      simp
  have hex : forbiddenThroughRoot 6 = {2,3} := by
    rw [forbiddenThroughRoot, dif_pos hn, hmax]
    ext q
    simp only [Nat.mem_primesLE, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hle,hp⟩
      have := hp.two_le
      omega
    · rintro (rfl | rfl) <;> norm_num
  rw [orderedSubtree_eq_cylinder h6, cylinder, hex]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hdiv : 6 ∣ j+1
  · by_cases hs : Squarefree (j+1)
    · have hfree : ∀ q ∈ ({2,3}:Finset ℕ), ¬q ∣ (j+1)/6 := by
        intro q hq hqk
        have hcases : q = 2 ∨ q = 3 := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hq
        have hp : q.Prime := by rcases hcases with rfl | rfl <;> decide
        have hd : q ∣ 6 := by rcases hcases with rfl | rfl <;> decide
        have hs' : Squarefree (6*((j+1)/6)) := by rwa [Nat.mul_div_cancel' hdiv]
        exact Nat.squarefree_iff_prime_squarefree.mp hs' q hp (mul_dvd_mul hd hqk)
      simp only [if_pos (And.intro hdiv hfree), if_pos hdiv]
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  · simp [hdiv]

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
