/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import RiemannResearch.NumberTheory.DivisorEscapeTail
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact Euler representation of the finite divisor contribution

Source: the finite divisor/Euler identity in the user's CRT collocation
handoff, Section 8, specialized through Mathlib's absolutely convergent
Euler product for multiplicative arithmetic functions. No tail term is dropped.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.NumberTheory.DivisorEscapeTail

/-- The complete Dirichlet term retained by the divisor cutoff. -/
def keptAF (t : ℝ) (L : ℕ) (hL : 0 < L) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ∣ L then (n : ℝ)^(-t) else 0, by simp [ne_of_gt hL]⟩

theorem keptAF_multiplicative (t : ℝ) (L : ℕ) (hL : 0 < L) :
    (keptAF t L hL).IsMultiplicative := by
  constructor
  · simp [keptAF]
  · intro a b hab
    have hd : a * b ∣ L ↔ a ∣ L ∧ b ∣ L := by
      constructor
      · intro h
        exact ⟨(dvd_mul_right a b).trans h, (dvd_mul_left b a).trans h⟩
      · intro h
        exact hab.mul_dvd_of_dvd_of_dvd h.1 h.2
    by_cases ha : a ∣ L <;> by_cases hb : b ∣ L <;>
      simp [keptAF, hd, ha, hb, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

theorem keptAF_norm_summable (t : ℝ) (L : ℕ) (hL : 0 < L) :
    Summable (fun n : ℕ => ‖keptAF t L hL n‖) := by
  apply summable_of_ne_finset_zero (s := L.divisors)
  intro n hn
  have hnd : ¬ n ∣ L := fun hd => hn (Nat.mem_divisors.mpr ⟨hd, ne_of_gt hL⟩)
  simp only [keptAF, ArithmeticFunction.coe_mk, if_neg hnd, norm_zero]

theorem keptAF_tsum (t : ℝ) (L : ℕ) (hL : 0 < L) :
    (∑' n : ℕ, keptAF t L hL n) = ∑ d ∈ L.divisors, (d : ℝ)^(-t) := by
  rw [tsum_eq_sum (s := L.divisors) (by
    intro n hn
    have hnd : ¬ n ∣ L := fun hd => hn (Nat.mem_divisors.mpr ⟨hd, ne_of_gt hL⟩)
    simp only [keptAF, ArithmeticFunction.coe_mk, if_neg hnd])]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [keptAF, ArithmeticFunction.coe_mk,
    if_pos (Nat.dvd_of_mem_divisors hn)]

/-- The local Euler factor includes exactly the allowed valuation depths. -/
theorem keptAF_prime_local (t : ℝ) (L : ℕ) (hL : 0 < L)
    (p : ℕ) (hp : p.Prime) :
    (∑' e : ℕ, keptAF t L hL (p^e)) =
      ∑ e ∈ Finset.range (L.factorization p + 1), ((p^e : ℕ) : ℝ)^(-t) := by
  rw [tsum_eq_sum (s := Finset.range (L.factorization p + 1)) (by
    intro e he
    have hne : ¬ e ≤ L.factorization p := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using he
    have hnd : ¬ p^e ∣ L := fun h =>
      hne ((hp.pow_dvd_iff_le_factorization (ne_of_gt hL)).mp h)
    simp only [keptAF, ArithmeticFunction.coe_mk, if_neg hnd])]
  apply Finset.sum_congr rfl
  intro e he
  have hed : p^e ∣ L :=
    (hp.pow_dvd_iff_le_factorization (ne_of_gt hL)).mpr
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp he))
  simp only [keptAF, ArithmeticFunction.coe_mk, if_pos hed]

/-- The finite divisor contribution is an actual convergent Euler product. -/
theorem divisor_sum_euler_product (t : ℝ) (L : ℕ) (hL : 0 < L) :
    (∑ d ∈ L.divisors, (d : ℝ)^(-t)) =
      ∏' p : Nat.Primes,
        ∑ e ∈ Finset.range (L.factorization (p : ℕ) + 1),
          (((p : ℕ)^e : ℕ) : ℝ)^(-t) := by
  rw [← keptAF_tsum t L hL]
  have h := (keptAF_multiplicative t L hL).eulerProduct_tprod
    (keptAF_norm_summable t L hL)
  rw [← h]
  apply tprod_congr
  intro p
  exact keptAF_prime_local t L hL p p.property

/-- Complete escape equals the full Dirichlet series minus its exact Euler cutoff. -/
theorem tail_eq_series_sub_euler_product (t : ℝ) (ht : 1 < t)
    (L : ℕ) (hL : 0 < L) :
    tail t L = (∑' n : ℕ, (n : ℝ)^(-t)) -
      ∏' p : Nat.Primes,
        ∑ e ∈ Finset.range (L.factorization (p : ℕ) + 1),
          (((p : ℕ)^e : ℕ) : ℝ)^(-t) := by
  rw [tail_eq_tsum_sub_divisor_sum t ht L hL, divisor_sum_euler_product t L hL]



def powerAF (t : ℝ) (ht : 1 < t) : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ)^(-t), by simp [Real.zero_rpow (by linarith : -t ≠ 0)]⟩

theorem powerAF_multiplicative (t : ℝ) (ht : 1 < t) :
    (powerAF t ht).IsMultiplicative := by
  constructor
  · simp [powerAF]
  · intro a b hab
    simp only [powerAF, ArithmeticFunction.coe_mk, Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)

theorem powerAF_norm_summable (t : ℝ) (ht : 1 < t) :
    Summable (fun n : ℕ => ‖powerAF t ht n‖) := by
  apply (Real.summable_nat_rpow.mpr (by linarith : -t < -1)).congr
  intro n
  simp only [powerAF, ArithmeticFunction.coe_mk, Real.norm_eq_abs]
  exact (abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (-t))).symm

theorem power_series_pos (t : ℝ) (ht : 1 < t) :
    0 < ∑' n : ℕ, (n : ℝ)^(-t) :=
  (Real.summable_nat_rpow.mpr (by linarith : -t < -1)).tsum_pos
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) 1 (by simp)

theorem nat_pow_rpow (t : ℝ) (p e : ℕ) :
    ((p^e : ℕ) : ℝ)^(-t) = ((p : ℝ)^(-t))^e := by
  induction e with
  | zero => simp
  | succ e ih =>
    calc
      ((p^(e+1) : ℕ) : ℝ)^(-t) =
          ((p^e : ℕ) : ℝ)^(-t) * (p : ℝ)^(-t) := by
        rw [pow_succ, Nat.cast_mul,
          Real.mul_rpow (Nat.cast_nonneg (p^e)) (Nat.cast_nonneg p)]
      _ = ((p : ℝ)^(-t))^(e+1) := by rw [ih, pow_succ]

theorem powerAF_prime_local (t : ℝ) (ht : 1 < t) (p : Nat.Primes) :
    (∑' e : ℕ, powerAF t ht ((p : ℕ)^e)) =
      (1 - ((p : ℕ) : ℝ)^(-t))⁻¹ := by
  have hq0 : 0 ≤ ((p : ℕ) : ℝ)^(-t) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hq1 : ((p : ℕ) : ℝ)^(-t) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (by linarith)
  calc
    _ = ∑' e : ℕ, (((p : ℕ) : ℝ)^(-t))^e := by
      apply tsum_congr
      intro e
      exact nat_pow_rpow t p e
    _ = _ := tsum_geometric_of_lt_one hq0 hq1

theorem local_factor_ratio (t : ℝ) (ht : 1 < t) (L : ℕ) (hL : 0 < L)
    (p : Nat.Primes) :
    (∑' e : ℕ, keptAF t L hL ((p : ℕ)^e)) /
        (∑' e : ℕ, powerAF t ht ((p : ℕ)^e)) =
      1 - (((p : ℕ) : ℝ)^(-t))^(L.factorization p + 1) := by
  rw [keptAF_prime_local t L hL p p.property, powerAF_prime_local t ht p]
  simp_rw [nat_pow_rpow]
  rw [div_inv_eq_mul]
  exact geom_sum_mul_neg _ _

/-- The actual infinite product converges to the retained fraction of the
full Dirichlet mass. No zero or prime is deleted from its index set. -/
theorem euler_deficit_hasProd (t : ℝ) (ht : 1 < t) (L : ℕ) (hL : 0 < L) :
    HasProd (fun p : Nat.Primes =>
      1 - (((p : ℕ) : ℝ)^(-t))^(L.factorization p + 1))
      ((∑ d ∈ L.divisors, (d : ℝ)^(-t)) /
        (∑' n : ℕ, (n : ℝ)^(-t))) := by
  have hk := (keptAF_multiplicative t L hL).eulerProduct_hasProd
    (keptAF_norm_summable t L hL)
  have hp := (powerAF_multiplicative t ht).eulerProduct_hasProd
    (powerAF_norm_summable t ht)
  have hz : (∑' n : ℕ, powerAF t ht n) ≠ 0 := ne_of_gt (power_series_pos t ht)
  have h := hk.div₀ hp hz
  simp_rw [local_factor_ratio t ht L hL] at h
  rw [keptAF_tsum t L hL] at h
  exact h

/-- The complete escape tail is zeta(t) times the infinite Euler deficit.
The formal statement writes zeta(t) as its absolutely convergent real series. -/
theorem tail_eq_series_mul_euler_deficit
    (t : ℝ) (ht : 1 < t) (L : ℕ) (hL : 0 < L) :
    tail t L = (∑' n : ℕ, (n : ℝ)^(-t)) *
      (1 - ∏' p : Nat.Primes,
        (1 - (((p : ℕ) : ℝ)^(-t))^(L.factorization p + 1))) := by
  rw [tail_eq_tsum_sub_divisor_sum t ht L hL,
    (euler_deficit_hasProd t ht L hL).tprod_eq]
  field_simp [ne_of_gt (power_series_pos t ht)]



/-- The individual prime-power escape probabilities under the zeta(t) law. -/
def primeEscape (t : ℝ) (L : ℕ) (p : Nat.Primes) : ℝ :=
  (((p : ℕ) : ℝ)^(-t))^(L.factorization p + 1)

theorem primeEscape_nonneg (t : ℝ) (L : ℕ) (p : Nat.Primes) :
    0 ≤ primeEscape t L p :=
  pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _

theorem primeEscape_le_power (t : ℝ) (ht : 1 < t) (L : ℕ) (p : Nat.Primes) :
    primeEscape t L p ≤ ((p : ℕ) : ℝ)^(-t) := by
  have hq0 : 0 ≤ ((p : ℕ) : ℝ)^(-t) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hq1 : ((p : ℕ) : ℝ)^(-t) ≤ 1 :=
    (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (by linarith : -t < 0)).le
  have hp (k : ℕ) : ((((p : ℕ) : ℝ)^(-t))^(k+1)) ≤ ((p : ℕ) : ℝ)^(-t) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc
        ((((p : ℕ) : ℝ)^(-t))^(k+1)) * ((p : ℕ) : ℝ)^(-t) ≤
            ((p : ℕ) : ℝ)^(-t) * ((p : ℕ) : ℝ)^(-t) :=
          mul_le_mul_of_nonneg_right ih hq0
        _ ≤ ((p : ℕ) : ℝ)^(-t) * 1 := mul_le_mul_of_nonneg_left hq1 hq0
        _ = ((p : ℕ) : ℝ)^(-t) := mul_one _
  exact hp _

theorem primeEscape_le_one (t : ℝ) (ht : 1 < t) (L : ℕ) (p : Nat.Primes) :
    primeEscape t L p ≤ 1 :=
  (primeEscape_le_power t ht L p).trans
    (Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (by linarith : -t < 0)).le

theorem primeEscape_summable (t : ℝ) (ht : 1 < t) (L : ℕ) :
    Summable (primeEscape t L) := by
  have hp : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ)^(-t)) :=
    (Real.summable_nat_rpow.mpr (by linarith : -t < -1)).comp_injective
      Subtype.val_injective
  exact Summable.of_nonneg_of_le (primeEscape_nonneg t L)
    (primeEscape_le_power t ht L) hp

private theorem finite_union_bound {ι : Type*} (a : ι → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (s : Finset ι) :
    1 - (∏ i ∈ s, (1 - a i)) ≤ ∑ i ∈ s, a i := by
  classical
  have aux (s : Finset ι) :
      0 ≤ (∏ i ∈ s, (1 - a i)) ∧ (∏ i ∈ s, (1 - a i)) ≤ 1 ∧
        1 - (∏ i ∈ s, (1 - a i)) ≤ ∑ i ∈ s, a i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      have hi0 := ha0 i
      have hi1 := ha1 i
      refine ⟨mul_nonneg (sub_nonneg.mpr hi1) ih.1, ?_, ?_⟩
      · have hm := mul_le_mul_of_nonneg_right (sub_le_self (1 : ℝ) hi0) ih.1
        have hm' : (1 - a i) * (∏ j ∈ s, (1-a j)) ≤ ∏ j ∈ s, (1-a j) := by
          simpa only [one_mul] using hm
        exact hm'.trans ih.2.1
      · have hm := mul_le_mul_of_nonneg_left ih.2.1 hi0
        nlinarith [ih.2.2]
  exact (aux s).2.2

private theorem infinite_union_bound {ι : Type*} (a : ι → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hs : Summable a) (hp : Multipliable (fun i => 1 - a i)) :
    1 - (∏' i, (1 - a i)) ≤ ∑' i, a i := by
  have ht : Tendsto (fun s : Finset ι => ∏ i ∈ s, (1 - a i)) atTop
      (𝓝 (∏' i, (1 - a i))) := hp.hasProd
  apply le_of_tendsto ((tendsto_const_nhds (x := (1 : ℝ))).sub ht)
  apply Eventually.of_forall
  intro s
  exact (finite_union_bound a ha0 ha1 s).trans
    (sum_le_hasSum s (fun i _ => ha0 i) hs.hasSum)

/-- The elementary Euler union bound, with the complete prime-power escape sum. -/
theorem tail_le_series_mul_prime_escape (t : ℝ) (ht : 1 < t)
    (L : ℕ) (hL : 0 < L) :
    tail t L ≤ (∑' n : ℕ, (n : ℝ)^(-t)) * ∑' p : Nat.Primes, primeEscape t L p := by
  rw [tail_eq_series_mul_euler_deficit t ht L hL]
  apply mul_le_mul_of_nonneg_left _ (power_series_pos t ht).le
  exact infinite_union_bound (primeEscape t L) (primeEscape_nonneg t L)
    (primeEscape_le_one t ht L) (primeEscape_summable t ht L)
    (euler_deficit_hasProd t ht L hL).multipliable

end RiemannResearch.NumberTheory.DivisorEscapeTail
