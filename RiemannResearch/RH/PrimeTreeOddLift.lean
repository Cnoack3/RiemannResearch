/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.PrimeTreeCanonicalCarry
import RiemannResearch.RH.PrimeTreeUniformCarry
import Mathlib.Tactic

/-! # Every positive odd first lift and the uniform limit of its floor carries

Source: C. Noack, *Prime trees, fractional parts, and zeta zeros* (2026),
§3 and §5.1. The parameter j represents the odd lift U = 2j+1.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.CanonicalPrimeCarry
open CRTCarryArithmetic

def liftU (j : ℕ) : ℝ := 2 * (j : ℝ) + 1

private theorem liftU_pos (j : ℕ) : 0 < liftU j := by unfold liftU; positivity

def oddWeight (j : ℕ) : ℕ → ℝ
  | 0 => 1
  | k+1 => weight (k+1) / liftU j

theorem oddWeight_pos (j k : ℕ) : 0 < oddWeight j k := by
  cases k with
  | zero => exact zero_lt_one
  | succ k => exact div_pos (weight_pos _) (liftU_pos _)

theorem oddWeight_step (j k : ℕ) : oddWeight j (k+1) ≤ oddWeight j k := by
  cases k with
  | zero =>
    change weight 1 / liftU j ≤ 1
    have h1 : weight 1 = 1 := by norm_num [weight, inverse_zero]
    rw [h1, div_le_iff₀ (liftU_pos _)]
    unfold liftU
    norm_num
  | succ k => exact div_le_div_of_nonneg_right (weight_antitone_step _) (liftU_pos j).le

def oddChain (j : ℕ) : NormalizedCarryChain where
  D := firstChain.D
  p := firstChain.p
  a := fun k => if k = 0 then 2 * (j : ℤ) + 1 else firstChain.a k
  b := fun k => if k = 0 then -(3 * (j : ℤ) + 1) else firstChain.b k
  w := oddWeight j
  start_pos := firstChain.start_pos
  radix_ge := firstChain.radix_ge
  next := firstChain.next
  bezout := by
    intro k
    cases k with
    | zero => norm_num [firstChain, primorialAt, radix, primeAt]; ring
    | succ k => simpa using firstChain.bezout (k+1)
  normalize := by
    intro k
    cases k with
    | zero =>
      have h1 : weight 1 = 1 := by norm_num [weight, inverse_zero]
      simp [oddWeight, h1, liftU, show (2 * (j : ℝ) + 1) ≠ 0 by positivity]
    | succ k =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, oddWeight]
      have h := firstChain.normalize (k+1)
      change weight (k+1+1) * (firstChain.a (k+1) : ℝ) = weight (k+1) at h
      field_simp [ne_of_gt (liftU_pos j)]
      linarith
  weight_bound := by
    intro k
    rw [abs_of_pos (oddWeight_pos j k)]
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (oddWeight_step j k).trans ih

theorem oddChain_inverse (j k : ℕ) : (2 : ℤ) ≤ (oddChain j).a (k+1) := by
  change (2 : ℤ) ≤ (positiveInverse (k+1) : ℤ)
  exact_mod_cast inverse_after_first k

theorem oddChain_probability (j : ℕ) :
    HasSum (oddChain j).edgeMass 1 ∧ ∀ k, 0 < (oddChain j).edgeMass k :=
  ⟨(oddChain j).edgeMass_total (by norm_num [oddChain, firstChain, primorialAt, primeAt]) rfl,
    (oddChain j).edgeMass_pos (oddWeight_pos j) (oddWeight_step j)⟩

theorem oddChain_edgeMass_zero (j : ℕ) : (oddChain j).edgeMass 0 = 1 - 1/(3 * liftU j) := by
  have hj := (liftU_pos j).ne'
  norm_num [NormalizedCarryChain.edgeMass, oddChain, firstChain, oddWeight, weight, inverse_zero,
    primorialAt, Finset.prod_range_succ, primeAt]
  field_simp [hj]
  ring

theorem oddChain_edgeMass_succ (j k : ℕ) :
    (oddChain j).edgeMass (k+1) = firstChain.edgeMass (k+1) / liftU j := by
  simp [NormalizedCarryChain.edgeMass, oddChain, firstChain, oddWeight]
  ring

theorem oddChain_tendstoUniformly (j : ℕ) :
    TendstoUniformly (fun K n => ∑ k ∈ Finset.range K, (oddChain j).carryTerm n k)
      (fun n => ∑' k, (oddChain j).carryTerm n k) atTop := by
  let t := oddChain j
  have hw (k : ℕ) : 0 ≤ t.w k := (oddWeight_pos j k).le
  have hg : Summable (fun k : ℕ => (1/2 : ℝ)^k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hws : Summable t.w := by
    apply (summable_nat_add_iff 1).mp
    apply Summable.of_norm_bounded (hg.mul_left (t.w 1))
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (hw _)]
    exact t.futureWeight_bound hw (oddChain_inverse j) 1 (by decide) k
  have hz : Tendsto (fun k => 3 * t.w k) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (3 : ℝ))).mul hws.tendsto_atTop_zero
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hz.eventually_lt_const hε, eventually_ge_atTop 1] with K he hK n
  rw [Real.dist_eq]
  exact (t.carry_uniform_remainder hw (oddWeight_step j) (oddChain_inverse j)
    radix_le_prefix K hK n).trans_lt he

/-- All sufficiently late individual integer floors vanish at a fixed
physical site. The bound on k is independent of the first lift. -/
theorem oddChain_carry_eventually_zero (j n k : ℕ) (hk : n+1 ≤ k) :
    carry ((oddChain j).D k) ((oddChain j).p k) ((oddChain j).a k) ((oddChain j).b k) n = 0 := by
  let t := oddChain j
  have hmon : StrictMono primeAt := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hnrad : n < t.p k := lt_of_lt_of_le (by omega : n < k+1) (hmon.id_le (k+1))
  have hd : t.p k ≤ t.D k := by
    obtain ⟨l, rfl⟩ : ∃ l, k = l+1 := ⟨k-1, by omega⟩
    exact radix_le_prefix l
  have hx := carry_head (t.D k) (t.p k) (t.a k) (t.b k) 0 n
    ((Nat.zero_le n).trans_lt (hnrad.trans_le hd)) ((Nat.zero_le n).trans_lt hnrad)
    (by simpa using t.bezout k) (hnrad.trans_le hd) hnrad
  simpa using hx

end RiemannResearch.RH.CanonicalPrimeCarry
