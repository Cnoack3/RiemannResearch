/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RiemannResearch.Analysis.MultiplicativeBudget
import RiemannResearch.NumberTheory.PrimeReciprocalBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The summable higher prime-power budget

Source: CanonicalPrimePowerUpdatesResearch20261107.md, Section 7, and the
user's PAPER-005 verification request, 11 November 2026. This is an
unconditional arithmetic budget. It does not provide the actual canonical
one-step energy inequality.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.PrimePowerDepthBudget

def reciprocalBudget (n : ℕ) : ℝ := 1 / ((n : ℝ) * ((n : ℝ) - 1))

theorem reciprocalBudget_nonneg (n : ℕ) : 0 ≤ reciprocalBudget n := by
  rcases n with _ | n
  · norm_num [reciprocalBudget]
  · unfold reciprocalBudget
    have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_pos n
    positivity

/-- Exact finite telescoping identity, including the terms at zero and one. -/
theorem sum_reciprocalBudget (N : ℕ) :
    (∑ n ∈ Finset.range (N + 2), reciprocalBudget n) =
      1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => norm_num [reciprocalBudget, Finset.sum_range_succ]
  | succ N ih =>
      rw [show N + 1 + 2 = (N + 2) + 1 by omega, Finset.sum_range_succ, ih]
      simp only [reciprocalBudget, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      rw [show (N : ℝ) + 2 - 1 = (N : ℝ) + 1 by ring,
        show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]
      have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (N : ℝ) + 2 ≠ 0 := by positivity
      field_simp [h1, h2]
      ring

theorem sum_reciprocalBudget_le_one (N : ℕ) :
    (∑ n ∈ Finset.range N, reciprocalBudget n) ≤ 1 := by
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 2), reciprocalBudget n :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun n _ _ => reciprocalBudget_nonneg n)
    _ = 1 - 1 / ((N : ℝ) + 1) := sum_reciprocalBudget N
    _ ≤ 1 := sub_le_self _ (by positivity)

theorem summable_reciprocalBudget : Summable reciprocalBudget :=
  summable_of_sum_range_le reciprocalBudget_nonneg sum_reciprocalBudget_le_one

theorem tsum_reciprocalBudget_le_one : (∑' n, reciprocalBudget n) ≤ 1 :=
  Real.tsum_le_of_sum_range_le reciprocalBudget_nonneg sum_reciprocalBudget_le_one

/-- The complete geometric tail at a prime, with depth starting at two. -/
theorem hasSum_higher_prime_powers (p : Nat.Primes) :
    HasSum (fun k : ℕ => 1 / (p.val : ℝ) ^ (k + 2))
      (1 / ((p.val : ℝ) * ((p.val : ℝ) - 1))) := by
  have hp1 : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hp0 : (0 : ℝ) < p.val := by linarith
  have hr : (1 : ℝ) / p.val < 1 := (div_lt_one hp0).mpr hp1
  have h := (hasSum_geometric_of_lt_one
    (by positivity : 0 ≤ (1 : ℝ) / p.val) hr).mul_left (1 / (p.val : ℝ) ^ 2)
  have he : 1 / (p.val : ℝ) ^ 2 * (1 - 1 / (p.val : ℝ))⁻¹ =
      1 / ((p.val : ℝ) * ((p.val : ℝ) - 1)) := by
    have hm : (p.val : ℝ) - 1 ≠ 0 := by linarith
    field_simp [ne_of_gt hp0, hm]
  rw [he] at h
  exact h.congr (fun k => by simp [one_div, inv_pow, pow_add, mul_comm])

theorem summable_prime_reciprocalBudget :
    Summable (fun p : Nat.Primes => reciprocalBudget p.val) :=
  summable_reciprocalBudget.subtype Nat.Prime

theorem tsum_prime_reciprocalBudget_le_one :
    (∑' p : Nat.Primes, reciprocalBudget p.val) ≤ 1 := by
  exact (Summable.tsum_subtype_le reciprocalBudget {p : ℕ | p.Prime}
    reciprocalBudget_nonneg summable_reciprocalBudget).trans
      tsum_reciprocalBudget_le_one

theorem higher_prime_power_budget :
    (∑' p : Nat.Primes, ∑' k : ℕ, 1 / (p.val : ℝ) ^ (k + 2)) =
      ∑' p : Nat.Primes, 1 / ((p.val : ℝ) * ((p.val : ℝ) - 1)) := by
  congr 1
  funext p
  exact (hasSum_higher_prime_powers p).tsum_eq

theorem higher_prime_power_budget_le_one :
    (∑' p : Nat.Primes, ∑' k : ℕ, 1 / (p.val : ℝ) ^ (k + 2)) ≤ 1 := by
  rw [higher_prime_power_budget]
  exact tsum_prime_reciprocalBudget_le_one

theorem summable_higher_prime_powers :
    Summable (fun pk : Nat.Primes × ℕ => 1 / (pk.1.val : ℝ) ^ (pk.2 + 2)) := by
  apply (summable_prod_of_nonneg (fun _ => by positivity)).mpr
  refine ⟨fun p => (hasSum_higher_prime_powers p).summable, ?_⟩
  have he : (fun p : Nat.Primes => ∑' k : ℕ, 1 / (p.val : ℝ) ^ (k + 2)) =
      (fun p => reciprocalBudget p.val) := by
    funext p
    exact (hasSum_higher_prime_powers p).tsum_eq
  rw [he]
  exact summable_prime_reciprocalBudget

/-- Any finite selection of higher prime-power depths has total weight at most one. -/
theorem finite_higher_prime_power_budget_le_one (s : Finset (Nat.Primes × ℕ)) :
    (∑ q ∈ s, 1 / (q.1.val : ℝ) ^ (q.2 + 2)) ≤ 1 := by
  have h := Summable.sum_le_tsum s (fun q _ => by positivity)
    summable_higher_prime_powers
  rw [summable_higher_prime_powers.tsum_prod] at h
  exact h.trans higher_prime_power_budget_le_one

/-- Higher depths alone multiply an energy by at most exp C, uniformly
over the primes, maximum depth and chosen finite set. -/
theorem higher_depth_product_le_exp (s : Finset (Nat.Primes × ℕ))
    (C : ℝ) (hC : 0 ≤ C) :
    (∏ q ∈ s, (1 + C / (q.1.val : ℝ) ^ (q.2 + 2))) ≤ Real.exp C := by
  simpa only [mul_one, mul_one_div] using
    Analysis.MultiplicativeBudget.prod_one_add_mul_le_exp s
      (fun q => 1 / (q.1.val : ℝ) ^ (q.2 + 2)) C 1 hC
      (fun q _ => by positivity) (finite_higher_prime_power_budget_le_one s)

/-- The geometric sum including the first power, separated into its
depth-one and higher-depth contributions. -/
theorem hasSum_positive_prime_powers (p : Nat.Primes) :
    HasSum (fun k : ℕ => 1 / (p.val : ℝ) ^ (k + 1))
      (1 / (p.val : ℝ) + reciprocalBudget p.val) := by
  have hp1 : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hp0 : (0 : ℝ) < p.val := by linarith
  have hr : (1 : ℝ) / p.val < 1 := (div_lt_one hp0).mpr hp1
  have h := (hasSum_geometric_of_lt_one
    (by positivity : 0 ≤ (1 : ℝ) / p.val) hr).mul_left (1 / (p.val : ℝ))
  have he : 1 / (p.val : ℝ) * (1 - 1 / (p.val : ℝ))⁻¹ =
      1 / (p.val : ℝ) + reciprocalBudget p.val := by
    have hm : (p.val : ℝ) - 1 ≠ 0 := by linarith
    unfold reciprocalBudget
    field_simp [ne_of_gt hp0, hm]
    ring
  rw [he] at h
  exact h.congr (fun k => by simp [one_div, inv_pow, pow_succ, mul_comm])

/-- Every finite selection of distinct prime/depth pairs has an explicit
log-log budget. Here depth index zero means the first prime power. -/
theorem finite_prime_power_budget_le (s : Finset (Nat.Primes × ℕ)) (M : ℕ)
    (hs : ∀ q ∈ s, q.1.val ≤ M) :
    (∑ q ∈ s, 1 / (q.1.val : ℝ) ^ (q.2 + 1)) ≤
      5 + 4 * Real.log ((Nat.log 2 M : ℝ) + 1) := by
  classical
  let ps := s.image Prod.fst
  let ks := s.image Prod.snd
  have hsub : s ⊆ ps ×ˢ ks := by
    intro q hq
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hq, Finset.mem_image_of_mem _ hq⟩
  have hp : ∀ p ∈ ps, p.val ≤ M := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    exact hs q hq
  calc
    _ ≤ ∑ q ∈ ps ×ˢ ks, 1 / (q.1.val : ℝ) ^ (q.2 + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ = ∑ p ∈ ps, ∑ k ∈ ks, 1 / (p.val : ℝ) ^ (k + 1) := by
      rw [Finset.sum_product]
    _ ≤ ∑ p ∈ ps, (1 / (p.val : ℝ) + reciprocalBudget p.val) := by
      apply Finset.sum_le_sum
      intro p _
      exact (Summable.sum_le_tsum ks (fun k _ => by positivity)
        (hasSum_positive_prime_powers p).summable).trans_eq
          (hasSum_positive_prime_powers p).tsum_eq
    _ = (∑ p ∈ ps, 1 / (p.val : ℝ)) + ∑ p ∈ ps, reciprocalBudget p.val :=
      Finset.sum_add_distrib
    _ ≤ 4 * (1 + Real.log ((Nat.log 2 M : ℝ) + 1)) + 1 := by
      apply add_le_add (PrimeReciprocalBounds.prime_subtype_reciprocal_sum_le ps M hp)
      exact (Summable.sum_le_tsum ps (fun p _ => reciprocalBudget_nonneg p.val)
        summable_prime_reciprocalBudget).trans tsum_prime_reciprocalBudget_le_one
    _ = _ := by ring

theorem exp_prime_power_budget_eq (C : ℝ) (M : ℕ) :
    Real.exp (C * (5 + 4 * Real.log ((Nat.log 2 M : ℝ) + 1))) =
      Real.exp (5 * C) * ((Nat.log 2 M : ℝ) + 1) ^ (4 * C) := by
  rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
  congr 1
  ring

/-- The finite-product transfer is unconditional arithmetic. -/
theorem prime_power_product_le_polylog (s : Finset (Nat.Primes × ℕ)) (M : ℕ)
    (hs : ∀ q ∈ s, q.1.val ≤ M) (C : ℝ) (hC : 0 ≤ C) :
    (∏ q ∈ s, (1 + C / (q.1.val : ℝ) ^ (q.2 + 1))) ≤
      Real.exp (5 * C) * ((Nat.log 2 M : ℝ) + 1) ^ (4 * C) := by
  rw [← exp_prime_power_budget_eq]
  simpa only [mul_one_div] using
    Analysis.MultiplicativeBudget.prod_one_add_mul_le_exp s
      (fun q => 1 / (q.1.val : ℝ) ^ (q.2 + 1)) C _ hC
      (fun q _ => by positivity) (finite_prime_power_budget_le s M hs)

/-- Conditional energy transfer along any admission schedule without repeated
prime/depth pairs. This does not prove hstep for the canonical family. -/
theorem energy_le_polylog_of_prime_power_steps (E : ℕ → ℝ)
    (p : ℕ → Nat.Primes) (k : ℕ → ℕ) (C : ℝ)
    (hE : 0 ≤ E 0) (hC : 0 ≤ C)
    (hinj : Function.Injective (fun n => (p n, k n)))
    (hstep : ∀ n, E (n + 1) ≤ (1 + C / (p n).val ^ (k n + 1)) * E n)
    (N M : ℕ) (hM : ∀ n < N, (p n).val ≤ M) :
    E N ≤ E 0 * (Real.exp (5 * C) * ((Nat.log 2 M : ℝ) + 1) ^ (4 * C)) := by
  classical
  let w : ℕ → ℝ := fun n => 1 / ((p n).val : ℝ) ^ (k n + 1)
  have hbudget : (∑ n ∈ Finset.range N, w n) ≤
      5 + 4 * Real.log ((Nat.log 2 M : ℝ) + 1) := by
    have he := Finset.sum_image (s := Finset.range N)
      (g := fun n => (p n, k n))
      (f := fun q : Nat.Primes × ℕ => 1 / (q.1.val : ℝ) ^ (q.2 + 1))
      (fun a _ b _ hab => hinj hab)
    change (∑ n ∈ Finset.range N, 1 / ((p n).val : ℝ) ^ (k n + 1)) ≤ _
    rw [← he]
    apply finite_prime_power_budget_le
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
    exact hM n (Finset.mem_range.mp hn)
  rw [← exp_prime_power_budget_eq]
  apply Analysis.MultiplicativeBudget.energy_le_exp_of_sum_le E w C _ hE hC
    (fun n => by dsimp [w]; positivity) _ N hbudget
  intro n
  simpa only [w, mul_one_div] using hstep n

/-- Finitely many exceptional initial admissions are absorbed into E n₀.
Only the eventual one-step bound is required. -/
theorem energy_le_polylog_of_eventual_prime_power_steps (E : ℕ → ℝ)
    (p : ℕ → Nat.Primes) (k : ℕ → ℕ) (C : ℝ) (n₀ : ℕ)
    (hE : 0 ≤ E n₀) (hC : 0 ≤ C)
    (hinj : Function.Injective (fun n => (p n, k n)))
    (hstep : ∀ n, n₀ ≤ n →
      E (n + 1) ≤ (1 + C / (p n).val ^ (k n + 1)) * E n)
    (N M : ℕ) (hM : ∀ n < N, (p (n₀ + n)).val ≤ M) :
    E (n₀ + N) ≤ E n₀ *
      (Real.exp (5 * C) * ((Nat.log 2 M : ℝ) + 1) ^ (4 * C)) := by
  apply energy_le_polylog_of_prime_power_steps (fun n => E (n₀ + n))
    (fun n => p (n₀ + n)) (fun n => k (n₀ + n)) C
    (by simpa only [Nat.add_zero] using hE) hC
    (fun a b hab => Nat.add_left_cancel (hinj hab)) _ N M hM
  intro n
  simpa only [Nat.add_assoc] using hstep (n₀ + n) (Nat.le_add_right n₀ n)

end RiemannResearch.NumberTheory.PrimePowerDepthBudget
