/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PositiveTestMoments
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Lean.Elab.Tactic.Omega

/-!
# Fractional power moments from nonnegative prime remainders

The Bertrand prime bound provides finite tests that dominate the power weight on each finite head
and preserve a common global bound.
-/

noncomputable section

open scoped BigOperators

namespace RiemannResearch.Analysis.PrimeResidueMixture

/-- Finite Stieltjes mixture with the remaining mass placed in the final test. -/
def cutMix (h v : ℕ → ℝ) (J : ℕ) : ℝ :=
  (∑ j ∈ Finset.range J, (h j - h (j + 1)) * v j) + h J * v J

theorem cutMix_succ (h v : ℕ → ℝ) (J : ℕ) :
    cutMix h v (J + 1) = cutMix h v J + h (J + 1) * (v (J + 1) - v J) := by
  unfold cutMix
  rw [Finset.sum_range_succ]
  ring

theorem cutMix_mono (h v z : ℕ → ℝ) (hh : Antitone h) (h₀ : ∀ j, 0 ≤ h j)
    (hv : ∀ j, v j ≤ z j) (J : ℕ) : cutMix h v J ≤ cutMix h z J := by
  unfold cutMix
  apply add_le_add
  · exact Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hv j) (sub_nonneg.mpr (hh (Nat.le_succ j)))
  · exact mul_le_mul_of_nonneg_left (hv J) (h₀ J)

theorem cutMix_const_mul (h v : ℕ → ℝ) (c : ℝ) (J : ℕ) :
    cutMix h (fun j => c * v j) J = c * cutMix h v J := by
  induction J with
  | zero => simp only [cutMix, Finset.range_zero, Finset.sum_empty, zero_add]; ring
  | succ J ih =>
    rw [cutMix_succ h (fun j => c * v j) J, cutMix_succ h v J, ih]
    ring

/-- The comparison with the truncated identity has an exact primitive. -/
theorem cutMix_min (h : ℕ → ℝ) (n J : ℕ) :
    cutMix h (fun j => ((min n (j + 1) : ℕ) : ℝ)) J =
      ∑ k ∈ Finset.range (min n (J + 1)), h k := by
  induction J with
  | zero =>
    cases n <;> simp [cutMix]
  | succ J ih =>
    rw [cutMix_succ, ih]
    by_cases e : n ≤ J + 1
    · have e' : n ≤ J + 1 + 1 := by omega
      simp [min_eq_left e, min_eq_left e']
    · have e₁ : J + 1 ≤ n := by omega
      have e₂ : J + 1 + 1 ≤ n := by omega
      simp only [min_eq_right e₁, min_eq_right e₂, Nat.cast_add, Nat.cast_one]
      rw [Finset.sum_range_succ _ (J + 1)]
      ring

/-- At the site i+1, every mixture with J ≥ i dominates its terminal contribution at i. -/
theorem residue_head_lower (h : ℕ → ℝ) (p : ℕ → ℕ) (hh : Antitone h)
    (hp : ∀ j, j + 1 < p j) (i J : ℕ) (hJ : i ≤ J) :
    h i * ((i + 1 : ℕ) : ℝ) ≤
      cutMix h (fun j => (((i + 1) % p j : ℕ) : ℝ)) J := by
  induction J, hJ using Nat.le_induction with
  | base =>
    unfold cutMix
    dsimp only
    rw [Nat.mod_eq_of_lt (hp i)]
    apply le_add_of_nonneg_left
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hh (Nat.le_succ j))) (Nat.cast_nonneg _)
  | succ J hJ ih =>
    have ha : i + 1 < p J := by have := hp J; omega
    have hb : i + 1 < p (J + 1) := by have := hp (J + 1); omega
    rw [cutMix_succ]
    simpa only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, sub_self, mul_zero, add_zero] using ih

theorem residue_global_upper (h : ℕ → ℝ) (p : ℕ → ℕ) (hh : Antitone h)
    (h₀ : ∀ j, 0 ≤ h j) (hp : ∀ j, j + 1 < p j) (hq : ∀ j, p j ≤ 2 * (j + 1))
    (n J : ℕ) : cutMix h (fun j => ((n % p j : ℕ) : ℝ)) J ≤
      2 * ∑ k ∈ Finset.range n, h k := by
  have hmod (j : ℕ) : n % p j ≤ 2 * min n (j + 1) := by
    have h₁ := Nat.mod_le n (p j)
    have h₂ := Nat.mod_lt n (show 0 < p j by have := hp j; omega)
    have h₃ := hq j
    by_cases e : n ≤ j + 1
    · rw [min_eq_left e]; omega
    · rw [min_eq_right (by omega : j + 1 ≤ n)]; omega
  have hmod' (j : ℕ) : ((n % p j : ℕ) : ℝ) ≤ 2 * ((min n (j + 1) : ℕ) : ℝ) := by
    exact_mod_cast hmod j
  calc
    _ ≤ cutMix h (fun j => 2 * ((min n (j + 1) : ℕ) : ℝ)) J :=
      cutMix_mono h _ _ hh h₀ hmod' J
    _ = 2 * ∑ k ∈ Finset.range (min n (J + 1)), h k := by
      rw [cutMix_const_mul h (fun j => ((min n (j + 1) : ℕ) : ℝ)) 2 J, cutMix_min]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (min_le_left n (J + 1))) (fun j _ _ => h₀ j)

/-- Bertrand's postulate supplies all conductors of this nonnegative finite mixture. -/
theorem exists_prime_residue_mixtures (h : ℕ → ℝ) (hh : Antitone h) (h₀ : ∀ j, 0 ≤ h j) :
    ∃ p : ℕ → ℕ, (∀ j, (p j).Prime) ∧
      (∀ i J, i ≤ J → h i * ((i + 1 : ℕ) : ℝ) ≤
        cutMix h (fun j => (((i + 1) % p j : ℕ) : ℝ)) J) ∧
      (∀ n J, cutMix h (fun j => ((n % p j : ℕ) : ℝ)) J ≤
        2 * ∑ j ∈ Finset.range n, h j) := by
  choose p hprime hlo hhi using fun j : ℕ =>
    Nat.exists_prime_lt_and_le_two_mul (j + 1) (Nat.succ_ne_zero j)
  exact ⟨p, hprime, residue_head_lower h p hh hlo, residue_global_upper h p hh h₀ hlo hhi⟩

end RiemannResearch.Analysis.PrimeResidueMixture

open scoped BigOperators

namespace RiemannResearch.Analysis.PrimeResidueMixture

/-- Tangency of x^a yields a one-step integral comparison with no improper integrals. -/
theorem shiftPower_increment (a x : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hx : 1 ≤ x) :
    a * x ^ (a - 1) ≤ x ^ a - (x - 1) ^ a := by
  have hx₀ : 0 < x := by linarith
  have hs : -1 ≤ -(1 / x) := by
    have hdiv : 1 / x ≤ 1 := (div_le_iff₀ hx₀).mpr (by linarith)
    linarith
  have ht := rpow_one_add_le_one_add_mul_self hs ha₀ ha₁
  have heq : 1 + -(1 / x) = (x - 1) / x := by
    field_simp [hx₀.ne']
    ring
  rw [heq, Real.div_rpow (sub_nonneg.mpr hx) hx₀.le] at ht
  have hpow := (div_le_iff₀ (Real.rpow_pos_of_pos hx₀ a)).mp ht
  rw [Real.rpow_sub_one hx₀.ne' a]
  calc
    a * (x ^ a / x) = x ^ a - (1 + a * -(1 / x)) * x ^ a := by ring
    _ ≤ _ := sub_le_sub_left hpow _

theorem shiftPower_sum (a : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1) (n : ℕ) :
    a * (∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) ^ (a - 1)) ≤ (n : ℝ) ^ a := by
  induction n with
  | zero => simp [Real.zero_rpow ha.ne']
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add]
    have hs : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
    have hstep := shiftPower_increment a _ ha.le ha₁ hs
    have heq : ((n + 1 : ℕ) : ℝ) - 1 = n := by push_cast; ring
    rw [heq] at hstep
    linarith

/-- Nonnegative finite combinations of prime remainders dominate n^a on any chosen
head and have global majorant (2/a)n^a. The two sides use the same finite tests. -/
theorem exists_power_prime_residue_mixtures (a : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1) :
    ∃ p : ℕ → ℕ, (∀ j, (p j).Prime) ∧
      (∀ i J, i ≤ J → ((i + 1 : ℕ) : ℝ) ^ a ≤
        cutMix (fun j => ((j + 1 : ℕ) : ℝ) ^ (a - 1))
          (fun j => (((i + 1) % p j : ℕ) : ℝ)) J) ∧
      (∀ n J, a * cutMix (fun j => ((j + 1 : ℕ) : ℝ) ^ (a - 1))
        (fun j => ((n % p j : ℕ) : ℝ)) J ≤ 2 * (n : ℝ) ^ a) := by
  let h : ℕ → ℝ := fun j => ((j + 1 : ℕ) : ℝ) ^ (a - 1)
  have hh : Antitone h := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast (by omega : 0 < i + 1)
    · exact_mod_cast (by omega : i + 1 ≤ j + 1)
    · linarith
  have h₀ (j : ℕ) : 0 ≤ h j := Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨p, hp, hlow, hup⟩ := exists_prime_residue_mixtures h hh h₀
  refine ⟨p, hp, ?_, ?_⟩
  · intro i J hJ
    have hi : 0 < ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < i + 1)
    have H := hlow i J hJ
    change ((i + 1 : ℕ) : ℝ) ^ (a - 1) * ((i + 1 : ℕ) : ℝ) ≤ _ at H
    rw [Real.rpow_sub_one hi.ne', div_mul_cancel₀ _ hi.ne'] at H
    exact H
  · intro n J
    have hS : a * (∑ j ∈ Finset.range n, h j) ≤ (n : ℝ) ^ a := shiftPower_sum a ha ha₁ n
    calc
      _ ≤ a * (2 * ∑ j ∈ Finset.range n, h j) :=
        mul_le_mul_of_nonneg_left (hup n J) ha.le
      _ = 2 * (a * ∑ j ∈ Finset.range n, h j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hS (by norm_num)

end RiemannResearch.Analysis.PrimeResidueMixture

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis
open PrimeResidueMixture

/-- Vanishing signed balances against the individual primes already transfer
one-sided power moments to absolute ones, for every 0 < a ≤ 1. -/
theorem absolute_moment_of_one_sided_prime_orthogonality (b : ℕ → ℝ) (a : ℝ)
    (ha : 0 < a) (ha₁ : a ≤ 1)
    (hzero : ∀ p : ℕ, p.Prime → HasSum (fun n : ℕ => b n * ((n % p : ℕ) : ℝ)) 0)
    (hpos : Summable (fun n : ℕ => max (b n) 0 * (n : ℝ) ^ a)) :
    Summable (fun n : ℕ => |b n| * (n : ℝ) ^ a) ∧
      (∑' n : ℕ, |b n| * (n : ℝ) ^ a) ≤
        (4 / a) * ∑' n : ℕ, max (b n) 0 * (n : ℝ) ^ a := by
  obtain ⟨p, hp, hlow, hup⟩ := exists_power_prime_residue_mixtures a ha ha₁
  let h : ℕ → ℝ := fun j => ((j + 1 : ℕ) : ℝ) ^ (a - 1)
  let T : ℕ → ℕ → ℝ := fun J n => cutMix h (fun j => ((n % p j : ℕ) : ℝ)) J
  have hh : Antitone h := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast (by omega : 0 < i + 1)
    · exact_mod_cast (by omega : i + 1 ≤ j + 1)
    · linarith
  have hh₀ (j : ℕ) : 0 ≤ h j := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hT (J n : ℕ) : 0 ≤ T J n := by
    unfold T cutMix
    exact add_nonneg (Finset.sum_nonneg fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hh (Nat.le_succ j))) (Nat.cast_nonneg _))
      (mul_nonneg (hh₀ J) (Nat.cast_nonneg _))
  have head (N n : ℕ) (hn : n < N) : 1 * (n : ℝ) ^ a ≤ T N n := by
    cases n with
    | zero => simpa only [Nat.cast_zero, Real.zero_rpow ha.ne', mul_zero] using hT N 0
    | succ i => simpa only [one_mul] using hlow i N (by omega : i ≤ N)
  have major (J n : ℕ) : T J n ≤ (2 / a) * (n : ℝ) ^ a := by
    calc
      T J n ≤ (2 * (n : ℝ) ^ a) / a := by
        apply (le_div_iff₀ ha).2
        rw [mul_comm (T J n) a]
        exact hup n J
      _ = _ := by ring
  have sums (J : ℕ) : HasSum (fun n : ℕ => b n * T J n) 0 := by
    induction J with
    | zero =>
        have hs := (hzero (p 0) (hp 0)).mul_left (h 0)
        rw [mul_zero] at hs
        apply hs.congr_fun
        intro n
        simp only [T, cutMix, Finset.range_zero, Finset.sum_empty, zero_add]
        ring
    | succ J ih =>
        have hd := (hzero (p (J + 1)) (hp (J + 1))).sub (hzero (p J) (hp J))
        have hs := ih.add (hd.mul_left (h (J + 1)))
        simp only [sub_zero, mul_zero, add_zero] at hs
        apply hs.congr_fun
        intro n
        dsimp only [T]
        rw [cutMix_succ]
        ring
  obtain ⟨hs, hbound⟩ := absolute_moment_of_positive_tests b (fun n : ℕ => (n : ℝ) ^ a)
    T 1 (2 / a) zero_lt_one (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hT
    head major sums hpos
  refine ⟨hs, hbound.trans_eq ?_⟩
  ring

end RiemannResearch.Analysis
