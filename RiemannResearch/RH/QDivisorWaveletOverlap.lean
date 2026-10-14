/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimeWaveletOverlap
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
/-!
# Finite arithmetic Euler products for absolute divisor-wavelet overlap

Source: user-provided argument, Section 7 of
https://github.com/Cnoack3/RiemannResearch/blob/main/RiemannResearch/RH/QDPPMovingWindowsResearch20261014.md
supports the statements and local proof strategy. Existing local providers
are reused. Saturated divisor sums retain an exact ratio to the site-one
mass before any estimate. Completeness and limiting DPP applications belong
to the higher application module.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ZetaTwoHilbert
open ZetaTwoProbability
theorem qDivisorWavelet_eq_jordan_of_dvd (r : ℕ) (hr : r ≠ 0)
    (n : ℕ+) (hd : r ∣ (n : ℕ)) :
    qDivisorWavelet r (n : ℕ) = qJordanTwo r := by
  rw [qDivisorWavelet_eq_prime_product r hr n, qJordanTwo, if_neg hr]
  apply Finset.prod_congr rfl
  intro p hp
  apply geometricWavelet_eq_weight
  have hpP := Nat.prime_of_mem_primeFactors hp
  exact (hpP.pow_dvd_iff_le_factorization (ne_of_gt n.pos)).mp
    ((Nat.ordProj_dvd r p).trans hd)

theorem qJordanTwo_mul_coprime (a b : ℕ) (hab : a.Coprime b) :
    qJordanTwo (a * b) = qJordanTwo a * qJordanTwo b := by
  by_cases ha : a = 0
  · subst a; simp [qJordanTwo]
  by_cases hb : b = 0
  · subst b; simp [qJordanTwo]
  let n : ℕ+ := ⟨a * b, Nat.mul_pos (Nat.pos_of_ne_zero ha) (Nat.pos_of_ne_zero hb)⟩
  have h := (divisorWaveletAF_multiplicative (n : ℕ)).map_mul_of_coprime hab
  simp only [divisorWaveletAF_apply] at h
  rw [qDivisorWavelet_eq_jordan_of_dvd (a * b) (mul_ne_zero ha hb) n (dvd_refl _),
    qDivisorWavelet_eq_jordan_of_dvd a ha n (dvd_mul_right a b),
    qDivisorWavelet_eq_jordan_of_dvd b hb n (dvd_mul_left b a)] at h
  exact h

def absoluteOverlapAF (n m : ℕ+) : ArithmeticFunction ℝ :=
  ⟨fun r => |qDivisorWavelet r (n : ℕ) * qDivisorWavelet r (m : ℕ)| / qJordanTwo r,
    by simp [qJordanTwo]⟩

theorem absoluteOverlapAF_nonneg (n m : ℕ+) (r : ℕ) :
    0 ≤ absoluteOverlapAF n m r := by
  by_cases hr : r = 0
  · subst r; simp [absoluteOverlapAF, qJordanTwo]
  exact div_nonneg (abs_nonneg _)
    (qJordanTwo_pos r (Nat.pos_of_ne_zero hr)).le

theorem absoluteOverlapAF_multiplicative (n m : ℕ+) :
    (absoluteOverlapAF n m).IsMultiplicative := by
  constructor
  · simp [absoluteOverlapAF, qDivisorWavelet, qScaledDivisibilitySum, qJordanTwo]
  · intro a b hab
    have hn := (divisorWaveletAF_multiplicative (n : ℕ)).map_mul_of_coprime hab
    have hm := (divisorWaveletAF_multiplicative (m : ℕ)).map_mul_of_coprime hab
    simp only [divisorWaveletAF_apply] at hn hm
    change |qDivisorWavelet (a * b) (n : ℕ) * qDivisorWavelet (a * b) (m : ℕ)| /
      qJordanTwo (a * b) = _
    rw [hn, hm, qJordanTwo_mul_coprime a b hab]
    simp only [absoluteOverlapAF, ArithmeticFunction.coe_mk, abs_mul, div_eq_mul_inv, mul_inv]
    ring

theorem qJordanTwo_prime_pow (p a : ℕ) (hp : p.Prime) :
    qJordanTwo (p ^ a) = valuationWaveletWeight p a := by
  cases a with
  | zero => simp [qJordanTwo, valuationWaveletWeight]
  | succ a =>
    simp [qJordanTwo, hp.ne_zero, Nat.primeFactors_prime_pow, hp.factorization_pow, hp]

theorem absoluteOverlapAF_prime_pow (n m : ℕ+) (p a : ℕ) (hp : p.Prime) :
    absoluteOverlapAF n m (p ^ a) =
      |geometricWavelet p a (primeValuation p n) *
        geometricWavelet p a (primeValuation p m)| / valuationWaveletWeight p a := by
  change |qDivisorWavelet (p ^ a) (n : ℕ) * qDivisorWavelet (p ^ a) (m : ℕ)| /
    qJordanTwo (p ^ a) = _
  rw [← divisorWaveletAF_apply, ← divisorWaveletAF_apply,
    divisorWaveletAF_prime_pow p a hp n, divisorWaveletAF_prime_pow p a hp m,
    qJordanTwo_prime_pow p a hp]
  rfl

theorem absoluteOverlapAF_divisor_euler (n m : ℕ+) (L : ℕ) (hL : L ≠ 0) :
    (∑ r ∈ L.divisors, absoluteOverlapAF n m r) =
      ∏ p ∈ L.primeFactors,
        ∑ a ∈ Finset.range (L.factorization p + 1), absoluteOverlapAF n m (p ^ a) := by
  let f : ArithmeticFunction ℝ := (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
    absoluteOverlapAF n m
  have hf : f.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul
      (absoluteOverlapAF_multiplicative n m)
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  change f L = _
  calc
    _ = f (∏ p ∈ L.primeFactors, p ^ L.factorization p) := by
      rw [← Nat.prod_primeFactors_pow_factorization hL]
    _ = ∏ p ∈ L.primeFactors, f (p ^ L.factorization p) := by
      apply hf.map_prod
      intro p hp q hq hpq
      exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq) hpq
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      change ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * absoluteOverlapAF n m) _ = _
      rw [ArithmeticFunction.coe_zeta_mul_apply,
        Nat.sum_divisors_prime_pow (Nat.prime_of_mem_primeFactors hp)]

theorem local_overlap_sum_saturated (p v w k : ℕ)
    (hk : min v w + 1 ≤ k) :
    (∑ a ∈ Finset.range (k + 1), |geometricWavelet p a v * geometricWavelet p a w| /
      valuationWaveletWeight p a) = localAbsoluteOverlap p v w := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro a ha hnot
  rw [geometricWavelet_product_above p a v w
    (by simp only [Finset.mem_range] at hnot; omega), abs_zero, zero_div]

theorem absoluteOverlapAF_divisor_saturated (n m : ℕ+) (L : ℕ) (hL : L ≠ 0)
    (hcap : ∀ p ∈ L.primeFactors,
      min (primeValuation p n) (primeValuation p m) + 1 ≤ L.factorization p) :
    (∑ r ∈ L.divisors, absoluteOverlapAF n m r) =
      ∏ p ∈ L.primeFactors, localAbsoluteOverlap p (primeValuation p n) (primeValuation p m) := by
  rw [absoluteOverlapAF_divisor_euler n m L hL]
  apply Finset.prod_congr rfl
  intro p hp
  simp_rw [absoluteOverlapAF_prime_pow n m p _ (Nat.prime_of_mem_primeFactors hp)]
  exact local_overlap_sum_saturated _ _ _ _ (hcap p hp)

def localOverlapCorrection (p v w : ℕ) : ℝ :=
  if v = w then 1 else 2 * (1 - 1 / (p : ℝ) ^ 2)

theorem localAbsoluteOverlap_eq_correction (p v w : ℕ) (hp : p.Prime) :
    localAbsoluteOverlap p v w =
      ((p : ℝ) ^ (min v w)) ^ 2 * localOverlapCorrection p v w *
        localAbsoluteOverlap p 0 0 := by
  rw [localAbsoluteOverlap_self p 0 hp]
  simp only [pow_zero, one_pow, one_mul]
  rcases lt_trichotomy v w with h | h | h
  · rw [localAbsoluteOverlap_lt p v w hp h, min_eq_left h.le,
      localOverlapCorrection, if_neg (ne_of_lt h)]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hden : (p : ℝ) ^ 2 - 1 ≠ 0 := by
      have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      nlinarith
    field_simp [hp0, hden]
  · subst w
    rw [localAbsoluteOverlap_self p v hp]
    simp [localOverlapCorrection, mul_div_assoc]
  · rw [localAbsoluteOverlap_symm p v w, localAbsoluteOverlap_lt p w v hp h,
      min_eq_right h.le, localOverlapCorrection, if_neg (ne_of_gt h)]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hden : (p : ℝ) ^ 2 - 1 ≠ 0 := by
      have : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      nlinarith
    field_simp [hp0, hden]

def overlapCorrection (n m : ℕ+) : ℝ :=
  ∏ p ∈ (n : ℕ).primeFactors ∪ (m : ℕ).primeFactors,
    localOverlapCorrection p (primeValuation p n) (primeValuation p m)

theorem localOverlapCorrection_of_zero (p : ℕ) :
    localOverlapCorrection p 0 0 = 1 := by simp [localOverlapCorrection]

theorem prod_min_valuation (n m : ℕ+) (S : Finset ℕ)
    (hn : (n : ℕ).primeFactors ⊆ S) (_hm : (m : ℕ).primeFactors ⊆ S) :
    (∏ p ∈ S, (p : ℝ) ^ min (primeValuation p n) (primeValuation p m)) =
      (Nat.gcd (n : ℕ) (m : ℕ) : ℝ) := by
  have hg0 : Nat.gcd (n : ℕ) (m : ℕ) ≠ 0 :=
    ne_of_gt (Nat.gcd_pos_of_pos_left (m : ℕ) n.pos)
  have hgS : (Nat.gcd (n : ℕ) (m : ℕ)).primeFactors ⊆ S :=
    (Nat.primeFactors_mono (Nat.gcd_dvd_left _ _) (ne_of_gt n.pos)).trans hn
  have he (p : ℕ) :
      min (primeValuation p n) (primeValuation p m) =
        (Nat.gcd (n : ℕ) (m : ℕ)).factorization p := by
    simp [primeValuation, Nat.factorization_gcd (ne_of_gt n.pos) (ne_of_gt m.pos)]
  simp_rw [he]
  calc
    _ = ∏ p ∈ (Nat.gcd (n : ℕ) (m : ℕ)).primeFactors,
        (p : ℝ) ^ (Nat.gcd (n : ℕ) (m : ℕ)).factorization p := by
      symm
      apply Finset.prod_subset hgS
      intro p hp hpnot
      rw [qFactorization_zero_of_notmem _ _ hpnot, pow_zero]
    _ = _ := by exact_mod_cast (Nat.prod_primeFactors_pow_factorization hg0).symm

theorem prod_overlapCorrection (n m : ℕ+) (S : Finset ℕ)
    (hn : (n : ℕ).primeFactors ⊆ S) (hm : (m : ℕ).primeFactors ⊆ S) :
    (∏ p ∈ S, localOverlapCorrection p (primeValuation p n) (primeValuation p m)) =
      overlapCorrection n m := by
  symm
  apply Finset.prod_subset (Finset.union_subset hn hm)
  intro p hp hpnot
  have hn0 := qFactorization_zero_of_notmem (n : ℕ) p
    (fun h => hpnot (Finset.mem_union_left _ h))
  have hm0 := qFactorization_zero_of_notmem (m : ℕ) p
    (fun h => hpnot (Finset.mem_union_right _ h))
  simpa [primeValuation, hn0, hm0] using localOverlapCorrection_of_zero p

theorem absoluteOverlapAF_divisor_ratio (n m : ℕ+) (L : ℕ) (hL : L ≠ 0)
    (hn : (n : ℕ).primeFactors ⊆ L.primeFactors)
    (hm : (m : ℕ).primeFactors ⊆ L.primeFactors)
    (hcap : ∀ p ∈ L.primeFactors,
      min (primeValuation p n) (primeValuation p m) + 1 ≤ L.factorization p) :
    (∑ r ∈ L.divisors, absoluteOverlapAF n m r) =
      (Nat.gcd (n : ℕ) (m : ℕ) : ℝ) ^ 2 * overlapCorrection n m *
        ∑ r ∈ L.divisors, absoluteOverlapAF 1 1 r := by
  have hcap0 (p : ℕ) (hp : p ∈ L.primeFactors) :
      min (primeValuation p (1 : ℕ+)) (primeValuation p (1 : ℕ+)) + 1 ≤ L.factorization p := by
    have hne : L.factorization p ≠ 0 := by
      exact Finsupp.mem_support_iff.mp (by simpa [Nat.support_factorization] using hp)
    simp [primeValuation]
    omega
  rw [absoluteOverlapAF_divisor_saturated n m L hL hcap,
    absoluteOverlapAF_divisor_saturated 1 1 L hL hcap0]
  have he : (∏ p ∈ L.primeFactors,
      localAbsoluteOverlap p (primeValuation p n) (primeValuation p m)) =
      ∏ p ∈ L.primeFactors, ((p : ℝ) ^ min (primeValuation p n) (primeValuation p m)) ^ 2 *
        localOverlapCorrection p (primeValuation p n) (primeValuation p m) *
          localAbsoluteOverlap p 0 0 := by
    apply Finset.prod_congr rfl
    intro p hp
    exact localAbsoluteOverlap_eq_correction p _ _ (Nat.prime_of_mem_primeFactors hp)
  rw [he, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow,
    prod_min_valuation n m L.primeFactors hn hm, prod_overlapCorrection n m L.primeFactors hn hm]
  simp [primeValuation]


theorem absoluteOverlapAF_divisor_ratio_of_square_dvd (n m : ℕ+) (L : ℕ)
    (hL : L ≠ 0) (hd : ((n : ℕ) * (m : ℕ)) ^ 2 ∣ L) :
    (∑ r ∈ L.divisors, absoluteOverlapAF n m r) =
      (Nat.gcd (n : ℕ) (m : ℕ) : ℝ) ^ 2 * overlapCorrection n m *
        ∑ r ∈ L.divisors, absoluteOverlapAF 1 1 r := by
  have hn0 := ne_of_gt n.pos
  have hm0 := ne_of_gt m.pos
  have hnm0 := mul_ne_zero hn0 hm0
  have hnL : (n : ℕ) ∣ L :=
    ((dvd_mul_right (n : ℕ) (m : ℕ)).trans (dvd_pow_self _ (by omega : 2 ≠ 0))).trans hd
  have hmL : (m : ℕ) ∣ L :=
    ((dvd_mul_left (m : ℕ) (n : ℕ)).trans (dvd_pow_self _ (by omega : 2 ≠ 0))).trans hd
  apply absoluteOverlapAF_divisor_ratio n m L hL
    (Nat.primeFactors_mono hnL hL) (Nat.primeFactors_mono hmL hL)
  intro p hp
  have hpos : 0 < L.factorization p := Nat.pos_of_ne_zero
    (Finsupp.mem_support_iff.mp (by simpa [Nat.support_factorization] using hp))
  have hle := ((Nat.factorization_le_iff_dvd (pow_ne_zero 2 hnm0) hL).mpr hd) p
  simp only [Nat.factorization_pow, Nat.factorization_mul hn0 hm0,
    Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at hle
  simp only [primeValuation]
  omega


def smallPrimePenalty (p : ℕ) : ℝ := if p = 2 ∨ p = 3 then 2 else 1

theorem localOverlapCorrection_nonneg (p v w : ℕ) (hp : p.Prime) :
    0 ≤ localOverlapCorrection p v w := by
  unfold localOverlapCorrection
  split_ifs
  · norm_num
  · have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hden : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    have hrec : 1 / (p : ℝ) ^ 2 ≤ 1 :=
      (div_le_iff₀ hden).mpr (by nlinarith)
    exact mul_nonneg (by norm_num) (by linarith)

theorem localOverlapCorrection_le_two (p v w : ℕ) :
    localOverlapCorrection p v w ≤ 2 := by
  unfold localOverlapCorrection
  split_ifs
  · norm_num
  · have : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
    linarith

theorem localOverlapCorrection_sq_budget_lt (p v w : ℕ) (hp : p.Prime)
    (hvw : v < w) :
    localOverlapCorrection p v w ^ 2 * ((p : ℝ) ^ v) ^ 2 ≤
      smallPrimePenalty p * (p : ℝ) ^ v * (p : ℝ) ^ w := by
  have hc0 := localOverlapCorrection_nonneg p v w hp
  have hc2 := localOverlapCorrection_le_two p v w
  have hc : localOverlapCorrection p v w ^ 2 ≤ 4 := by nlinarith
  have hP : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hpow : (p : ℝ) ^ (v + 1) ≤ (p : ℝ) ^ w :=
    pow_le_pow_right₀ hP (Nat.succ_le_of_lt hvw)
  rw [pow_succ] at hpow
  have hC0 : 0 ≤ smallPrimePenalty p := by unfold smallPrimePenalty; split_ifs <;> norm_num
  have hCP : 4 ≤ smallPrimePenalty p * (p : ℝ) := by
    unfold smallPrimePenalty
    split_ifs with h
    · have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      linarith
    · have hpr : (4 : ℝ) ≤ p := by
        have : 4 ≤ p := by have := hp.two_le; omega
        exact_mod_cast this
      simpa using hpr
  calc
    _ ≤ 4 * ((p : ℝ) ^ v) ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ ≤ (smallPrimePenalty p * (p : ℝ)) * ((p : ℝ) ^ v) ^ 2 :=
      mul_le_mul_of_nonneg_right hCP (sq_nonneg _)
    _ ≤ smallPrimePenalty p * (p : ℝ) ^ v * (p : ℝ) ^ w := by
      have hh := mul_le_mul_of_nonneg_left hpow
        (mul_nonneg hC0 (pow_nonneg (Nat.cast_nonneg p) v))
      nlinarith

theorem localOverlapCorrection_sq_budget (p v w : ℕ) (hp : p.Prime) :
    localOverlapCorrection p v w ^ 2 * ((p : ℝ) ^ min v w) ^ 2 ≤
      smallPrimePenalty p * (p : ℝ) ^ v * (p : ℝ) ^ w := by
  rcases lt_trichotomy v w with h | h | h
  · simpa [min_eq_left h.le] using localOverlapCorrection_sq_budget_lt p v w hp h
  · subst w
    have hC : 1 ≤ smallPrimePenalty p := by unfold smallPrimePenalty; split_ifs <;> norm_num
    simpa [localOverlapCorrection, pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right hC (sq_nonneg ((p : ℝ) ^ v))
  · have he : localOverlapCorrection p v w = localOverlapCorrection p w v := by
      simp only [localOverlapCorrection, eq_comm]
    simpa [he, min_eq_right h.le, mul_comm, mul_left_comm, mul_assoc] using
      localOverlapCorrection_sq_budget_lt p w v hp h

theorem prod_smallPrimePenalty_le (S : Finset ℕ) :
    (∏ p ∈ S, smallPrimePenalty p) ≤ 4 := by
  have hc : (S.filter (fun p => p = 2 ∨ p = 3)).card ≤ 2 := by
    calc
      _ ≤ ({2, 3} : Finset ℕ).card := Finset.card_le_card (by
        intro p hp
        simpa using (Finset.mem_filter.mp hp).2)
      _ = 2 := by norm_num
  have he : (∏ p ∈ S, smallPrimePenalty p) =
      (2 : ℝ) ^ (S.filter (fun p => p = 2 ∨ p = 3)).card := by
    simp [smallPrimePenalty, Finset.prod_ite]
  rw [he]
  calc
    _ ≤ (2 : ℝ) ^ 2 := pow_le_pow_right₀ (by norm_num) hc
    _ = 4 := by norm_num

theorem prod_valuation (n : ℕ+) (S : Finset ℕ) (hn : (n : ℕ).primeFactors ⊆ S) :
    (∏ p ∈ S, (p : ℝ) ^ primeValuation p n) = (n : ℝ) := by
  calc
    _ = ∏ p ∈ (n : ℕ).primeFactors, (p : ℝ) ^ (n : ℕ).factorization p := by
      symm
      apply Finset.prod_subset hn
      intro p hp hpnot
      simp only [qFactorization_zero_of_notmem _ _ hpnot, pow_zero]
    _ = _ := by exact_mod_cast (Nat.prod_primeFactors_pow_factorization (ne_of_gt n.pos)).symm

theorem overlapCorrection_nonneg (n m : ℕ+) : 0 ≤ overlapCorrection n m := by
  apply Finset.prod_nonneg
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact localOverlapCorrection_nonneg p _ _ (Nat.prime_of_mem_primeFactors hp)
  · exact localOverlapCorrection_nonneg p _ _ (Nat.prime_of_mem_primeFactors hp)

theorem overlapCorrection_sq_mul_gcd_sq_le (n m : ℕ+) :
    overlapCorrection n m ^ 2 * (Nat.gcd (n : ℕ) (m : ℕ) : ℝ) ^ 2 ≤ 4 * (n : ℝ) * (m : ℝ) := by
  let S := (n : ℕ).primeFactors ∪ (m : ℕ).primeFactors
  have hloc : (∏ p ∈ S,
      localOverlapCorrection p (primeValuation p n) (primeValuation p m) ^ 2 *
        ((p : ℝ) ^ min (primeValuation p n) (primeValuation p m)) ^ 2) ≤
      ∏ p ∈ S, smallPrimePenalty p * (p : ℝ) ^ primeValuation p n *
        (p : ℝ) ^ primeValuation p m := by
    apply Finset.prod_le_prod
    · intro p hp; positivity
    · intro p hp
      have hpP : p.Prime := by
        rcases Finset.mem_union.mp hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
      exact localOverlapCorrection_sq_budget p _ _ hpP
  rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
    prod_min_valuation n m S Finset.subset_union_left Finset.subset_union_right,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_valuation n S Finset.subset_union_left,
    prod_valuation m S Finset.subset_union_right] at hloc
  change overlapCorrection n m ^ 2 * _ ≤ _ at hloc
  exact hloc.trans (by
    have := mul_le_mul_of_nonneg_right (prod_smallPrimePenalty_le S)
      (mul_nonneg (by exact_mod_cast n.pos.le : (0 : ℝ) ≤ n)
        (by exact_mod_cast m.pos.le : (0 : ℝ) ≤ m))
    simpa [mul_assoc] using this)

def valuationMismatchPrimes (n m : ℕ+) : Finset ℕ :=
  ((n : ℕ).primeFactors ∪ (m : ℕ).primeFactors).filter
    (fun p => primeValuation p n ≠ primeValuation p m)

theorem overlapCorrection_eq_prod_mismatch (n m : ℕ+) :
    overlapCorrection n m =
      ∏ p ∈ valuationMismatchPrimes n m, 2 * (1 - 1 / (p : ℝ) ^ 2) := by
  unfold overlapCorrection valuationMismatchPrimes
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases h : primeValuation p n = primeValuation p m <;>
    simp [localOverlapCorrection, h]

theorem overlapCorrection_le_two_pow (n m : ℕ+) :
    overlapCorrection n m ≤ (2 : ℝ) ^ (valuationMismatchPrimes n m).card := by
  rw [overlapCorrection_eq_prod_mismatch]
  calc
    _ ≤ ∏ p ∈ valuationMismatchPrimes n m, (2 : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hmem := Finset.mem_filter.mp hp
        have hpP : p.Prime := by
          rcases Finset.mem_union.mp hmem.1 with h | h <;>
            exact Nat.prime_of_mem_primeFactors h
        simpa [localOverlapCorrection, hmem.2] using
          localOverlapCorrection_nonneg p (primeValuation p n) (primeValuation p m) hpP
      · intro p hp
        have : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
        linarith
    _ = _ := by simp

end RiemannResearch.RH.ZetaTwoHilbert
