/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamMobiusCoefficients
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A change of measure for the finite signed Möbius lcm form

The prime divisibility indicators are independent on a finite squarefree
period. Their Bernoulli parameters change from `1/p` to `1/p^(1+ε)`.
Conditioning successively on the primes preserves arbitrary signed divisor
coefficients inside a square. Legendre's formula bounds the cost of changing
all the failure probabilities.
-/

noncomputable section
open Finset
namespace RiemannResearch.Analysis.InghamMollifier

private def primeForm (P D : Finset ℕ) (r c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D, c d * c e * ∏ p ∈ P, if p ∣ d ∨ p ∣ e then r p else 1

private theorem primeForm_insert (P D : Finset ℕ) (p : ℕ) (hp : p ∉ P) (r c : ℕ → ℝ) :
    primeForm (insert p P) D r c =
      r p * primeForm P D r c +
        (1 - r p) * primeForm P D r (fun d => if p ∣ d then 0 else c d) := by
  classical
  simp only [primeForm, prod_insert hp, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  by_cases h₁ : p ∣ d <;> by_cases h₂ : p ∣ e <;> simp [h₁, h₂] <;> ring

private theorem primeForm_nonneg (P D : Finset ℕ) (r c : ℕ → ℝ)
    (hr : ∀ p ∈ P, 0 ≤ r p ∧ r p ≤ 1) : 0 ≤ primeForm P D r c := by
  classical
  induction P using Finset.induction_on generalizing c with
  | empty =>
    simp only [primeForm, prod_empty, mul_one, ← mul_sum, ← sum_mul]
    exact mul_self_nonneg _
  | @insert p P hp ih =>
    obtain ⟨h₀, h₁⟩ := hr p (mem_insert_self ..)
    have hs : ∀ q ∈ P, 0 ≤ r q ∧ r q ≤ 1 := fun q hq => hr q (mem_insert_of_mem hq)
    rw [primeForm_insert P D p hp]
    exact add_nonneg (mul_nonneg h₀ (ih _ hs)) (mul_nonneg (sub_nonneg.mpr h₁) (ih _ hs))

private theorem primeForm_change (P D : Finset ℕ) (r s k c : ℕ → ℝ)
    (h : ∀ p ∈ P, (0 ≤ r p ∧ r p ≤ 1) ∧ (0 ≤ s p ∧ s p ≤ 1) ∧ 0 ≤ k p ∧
      r p ≤ k p * s p ∧ 1 - r p ≤ k p * (1 - s p)) :
    primeForm P D r c ≤ (∏ p ∈ P, k p) * primeForm P D s c := by
  classical
  induction P using Finset.induction_on generalizing c with
  | empty => simp [primeForm]
  | @insert p P hp ih =>
    obtain ⟨hr, hs, hk, h₁, h₂⟩ := h p (mem_insert_self ..)
    have ht := fun q (hq : q ∈ P) => h q (mem_insert_of_mem hq)
    let c₀ := fun d => if p ∣ d then 0 else c d
    have hK : 0 ≤ ∏ q ∈ P, k q := prod_nonneg (fun q hq => (ht q hq).2.2.1)
    have hnon (f : ℕ → ℝ) : 0 ≤ (∏ q ∈ P, k q) * primeForm P D s f :=
      mul_nonneg hK (primeForm_nonneg P D s f (fun q hq => (ht q hq).2.1))
    rw [primeForm_insert P D p hp r, primeForm_insert P D p hp s, prod_insert hp]
    change r p * primeForm P D r c + (1 - r p) * primeForm P D r c₀ ≤ _
    calc
      _ ≤ (k p * s p) * ((∏ q ∈ P, k q) * primeForm P D s c) +
          (k p * (1 - s p)) * ((∏ q ∈ P, k q) * primeForm P D s c₀) :=
        add_le_add ((mul_le_mul_of_nonneg_left (ih c ht) hr.1).trans
          (mul_le_mul_of_nonneg_right h₁ (hnon c)))
          ((mul_le_mul_of_nonneg_left (ih c₀ ht) (sub_nonneg.mpr hr.2)).trans
          (mul_le_mul_of_nonneg_right h₂ (hnon c₀)))
      _ = _ := by dsimp [c₀]; ring

/-- The finite sum controlling the change of the Bernoulli failure odds.
The bound holds at every positive integer cutoff. -/
theorem prime_log_over_pred_sum_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ p ∈ (Icc 1 X).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) ≤ 4 * Real.log X := by
  classical
  let P := (Icc 1 X).filter Nat.Prime
  have hx : (0 : ℝ) < X := by exact_mod_cast hX
  have hfac := Nat.factorial_ne_zero X
  have hsub : P ⊆ X.factorial.primeFactors := by
    intro p hp
    obtain ⟨hi, hpr⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hpr, Nat.dvd_factorial hpr.pos (mem_Icc.mp hi).2, hfac⟩
  have hw (p : ℕ) (hp : p ∈ P) :
      (X : ℝ) * (Real.log p / ((p : ℝ) - 1)) ≤
        4 * (((X / p : ℕ) : ℝ) * Real.log p) := by
    obtain ⟨hi, hpr⟩ := mem_filter.mp hp
    have hpos := Nat.div_pos (mem_Icc.mp hi).2 hpr.pos
    have hn : X ≤ 2 * (X / p) * p := by
      calc
        X = X % p + p * (X / p) := (Nat.mod_add_div _ _).symm
        _ ≤ p * (X / p) + p * (X / p) := Nat.add_le_add_right
          ((Nat.mod_lt _ hpr.pos).le.trans (Nat.le_mul_of_pos_right p hpos)) _
        _ = _ := by ring
    have hn' : (X : ℝ) ≤ 2 * ((X / p : ℕ) : ℝ) * p := by exact_mod_cast hn
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
    have hnum : (X : ℝ) ≤ 4 * ((X / p : ℕ) : ℝ) * (p - 1 : ℝ) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg (X / p) : (0 : ℝ) ≤ _) (sub_nonneg.mpr h2)]
    rw [mul_div_assoc', div_le_iff₀ (by linarith : 0 < (p : ℝ) - 1)]
    have hh := mul_le_mul_of_nonneg_right hnum
      (Real.log_nonneg (show 1 ≤ (p : ℝ) by linarith))
    linarith only [hh]
  have hv (p : ℕ) (hp : p ∈ P) : X / p ≤ X.factorial.factorization p := by
    obtain ⟨hi, hpr⟩ := mem_filter.mp hp
    apply (hpr.pow_dvd_iff_le_factorization hfac).mp
    apply (Nat.Prime.pow_dvd_factorial_iff (b := Nat.log p X + 2) hpr (by omega)).mpr
    have hsum := single_le_sum (f := fun i => X / p ^ i)
      (fun i _ => Nat.zero_le _) (show 1 ∈ Ico 1 (Nat.log p X + 2) by simp)
    simpa using hsum
  have hsum : ∑ p ∈ P, ((X / p : ℕ) : ℝ) * Real.log p ≤ Real.log X.factorial := by
    have hid : (X.factorial : ℝ) = ∏ p ∈ X.factorial.primeFactors,
        (p : ℝ) ^ X.factorial.factorization p := by
      exact_mod_cast Nat.prod_primeFactors_pow_factorization hfac
    calc
      _ ≤ ∑ p ∈ P, (X.factorial.factorization p : ℝ) * Real.log p := by
        apply sum_le_sum; intro p hp
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hv p hp)
        exact Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
      _ ≤ ∑ p ∈ X.factorial.primeFactors, (X.factorial.factorization p : ℝ) * Real.log p :=
        sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => mul_nonneg (Nat.cast_nonneg _)
          (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le)))
      _ = _ := by
        have hne (p : ℕ) (hp : p ∈ X.factorial.primeFactors) :
            (p : ℝ) ^ X.factorial.factorization p ≠ 0 :=
          pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)
        rw [hid, Real.log_prod hne]
        simp only [Real.log_pow]
  have hfact : Real.log X.factorial ≤ (X : ℝ) * Real.log X := by
    simpa [Real.log_pow] using Real.log_le_log
      (show (0 : ℝ) < X.factorial by exact_mod_cast X.factorial_pos)
      (show (X.factorial : ℝ) ≤ (X : ℝ)^X by exact_mod_cast X.factorial_le_pow)
  apply le_of_mul_le_mul_left (a := (X : ℝ)) _ hx
  calc
    (X : ℝ) * (∑ p ∈ P, Real.log p / ((p : ℝ) - 1)) ≤
        4 * ∑ p ∈ P, ((X / p : ℕ) : ℝ) * Real.log p := by
      simp only [mul_sum]
      exact sum_le_sum hw
    _ ≤ 4 * ((X : ℝ) * Real.log X) := mul_le_mul_of_nonneg_left (hsum.trans hfact) (by norm_num)
    _ = _ := by ring

private theorem primeForm_lcm_product {X d e : ℕ} (hd : d ∈ Icc 1 X)
    (he : e ∈ Icc 1 X) (hsd : Squarefree d) (hse : Squarefree e) (τ : ℝ) :
    (∏ p ∈ (Icc 1 X).filter Nat.Prime,
      if p ∣ d ∨ p ∣ e then (p : ℝ) ^ (-τ) else 1) = (Nat.lcm d e : ℝ) ^ (-τ) := by
  classical
  have hd₀ := hsd.ne_zero
  have he₀ := hse.ne_zero
  have hl₀ := Nat.lcm_ne_zero hd₀ he₀
  have hsf : Squarefree (Nat.lcm d e) := by
    apply Nat.squarefree_of_factorization_le_one hl₀
    intro p
    rw [Nat.factorization_lcm hd₀ he₀]
    exact max_le (hsd.natFactorization_le_one p) (hse.natFactorization_le_one p)
  have hset : ((Icc 1 X).filter Nat.Prime).filter (fun p => p ∣ d ∨ p ∣ e) =
      (Nat.lcm d e).primeFactors := by
    ext p
    simp only [mem_filter, mem_Icc, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_, hp⟩, h | h⟩
      · exact ⟨hp, h.trans (Nat.dvd_lcm_left d e), hl₀⟩
      · exact ⟨hp, h.trans (Nat.dvd_lcm_right d e), hl₀⟩
    · rintro ⟨hp, hpl, _⟩
      have hh : p ∣ d ∨ p ∣ e := hp.dvd_mul.mp (hpl.trans
        (Nat.lcm_dvd (dvd_mul_right d e) (dvd_mul_left e d)))
      have hpx : p ≤ X := hh.elim
        (fun h => (Nat.le_of_dvd (mem_Icc.mp hd).1 h).trans (mem_Icc.mp hd).2)
        (fun h => (Nat.le_of_dvd (mem_Icc.mp he).1 h).trans (mem_Icc.mp he).2)
      exact ⟨⟨⟨hp.one_le, hpx⟩, hp⟩, hh⟩
  have hprod (P : Finset ℕ) :
      (∏ p ∈ P, (p : ℝ) ^ (-τ)) = (∏ p ∈ P, (p : ℝ)) ^ (-τ) := by
    induction P using Finset.induction_on with
    | empty => simp
    | @insert p P hp ih =>
      simp only [prod_insert hp, ih, Real.mul_rpow (Nat.cast_nonneg p)
        (prod_nonneg (fun q _ => Nat.cast_nonneg q))]
  rw [← prod_filter, hset, hprod]
  congr 1
  simpa only [Nat.cast_prod] using congrArg (fun n : ℕ => (n : ℝ))
    (Nat.prod_primeFactors_of_squarefree hsf)

private theorem truncatedMobiusLCMForm_eq_primeForm (X : ℕ) (τ : ℝ) :
    truncatedMobiusLCMForm X τ =
      primeForm ((Icc 1 X).filter Nat.Prime) (Icc 1 X)
        (fun p => (p : ℝ) ^ (-τ)) (fun n => (ArithmeticFunction.moebius n : ℝ)) := by
  classical
  unfold truncatedMobiusLCMForm primeForm
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro e he
  by_cases hsd : Squarefree d
  · by_cases hse : Squarefree e
    · rw [primeForm_lcm_product hd he hsd hse]
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hse]
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsd]

private theorem prime_parameter_change {v ε : ℝ} (hv : 1 < v) (hε : 0 ≤ ε) :
    let r := v ^ (-(1 + ε))
    let s := v ^ (-(1 : ℝ))
    let k := Real.exp (ε * (Real.log v / (v - 1)))
    (0 ≤ r ∧ r ≤ 1) ∧ (0 ≤ s ∧ s ≤ 1) ∧ 0 ≤ k ∧
      r ≤ k * s ∧ 1 - r ≤ k * (1 - s) := by
  dsimp only
  rw [Real.rpow_neg_one]
  have hv₀ : 0 < v := by linarith
  have hv₁ : 0 < v - 1 := by linarith
  have hl := (Real.log_pos hv).le
  have hi : v⁻¹ ≤ 1 := by rw [← one_div, div_le_iff₀ hv₀]; simpa using hv.le
  have hsplit : v ^ (-(1 + ε)) = v⁻¹ * Real.exp (-(ε * Real.log v)) := by
    rw [show -(1 + ε) = -1 + -ε by ring, Real.rpow_add hv₀, Real.rpow_neg_one,
      Real.rpow_def_of_pos hv₀]
    congr 2
    ring
  have hs : v ^ (-(1 + ε)) ≤ v⁻¹ := by
    rw [hsplit]
    exact mul_le_of_le_one_right (inv_nonneg.mpr hv₀.le)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hε hl)))
  have hk : 1 ≤ Real.exp (ε * (Real.log v / (v - 1))) :=
    Real.one_le_exp (mul_nonneg hε (div_nonneg hl hv₁.le))
  refine ⟨⟨Real.rpow_nonneg hv₀.le _, hs.trans hi⟩, ⟨inv_nonneg.mpr hv₀.le, hi⟩,
    (Real.exp_pos _).le, hs.trans (le_mul_of_one_le_left (inv_nonneg.mpr hv₀.le) hk), ?_⟩
  calc
    1 - v ^ (-(1 + ε)) ≤ 1 - v⁻¹ * (-(ε * Real.log v) + 1) := by
      rw [hsplit]
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by positivity)) _
    _ = (ε * (Real.log v / (v - 1)) + 1) * (1 - v⁻¹) := by
      field_simp [hv₀.ne', hv₁.ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (sub_nonneg.mpr hi)

/-- The signed Möbius lcm form at a moving exponent is controlled by its
unshifted form. For `ε = c / log X` the loss is the constant `exp (4*c)`. -/
theorem truncatedMobiusLCMForm_shift_le {X : ℕ} (hX : 1 ≤ X) {ε : ℝ} (hε : 0 ≤ ε) :
    truncatedMobiusLCMForm X (1 + ε) ≤
      Real.exp (4 * ε * Real.log X) * truncatedMobiusLCMForm X 1 := by
  classical
  let P := (Icc 1 X).filter Nat.Prime
  let r := fun p : ℕ => (p : ℝ) ^ (-(1 + ε))
  let s := fun p : ℕ => (p : ℝ) ^ (-(1 : ℝ))
  let k := fun p : ℕ => Real.exp (ε * (Real.log p / ((p : ℝ) - 1)))
  let c := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ)
  have hp (p : ℕ) (h : p ∈ P) : (1 : ℝ) < p := by
    exact_mod_cast (mem_filter.mp h).2.one_lt
  have hform := primeForm_change P (Icc 1 X) r s k c
    (fun p h => prime_parameter_change (hp p h) hε)
  have hn := primeForm_nonneg P (Icc 1 X) s c
    (fun p h => (prime_parameter_change (hp p h) hε).2.1)
  have hcost : (∏ p ∈ P, k p) ≤ Real.exp (4 * ε * Real.log X) := by
    dsimp only [k]
    rw [← Real.exp_sum, ← mul_sum]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ε * (4 * Real.log X) := mul_le_mul_of_nonneg_left (prime_log_over_pred_sum_le X hX) hε
      _ = _ := by ring
  rw [truncatedMobiusLCMForm_eq_primeForm, truncatedMobiusLCMForm_eq_primeForm]
  exact hform.trans (mul_le_mul_of_nonneg_right hcost hn)

/-- At the logarithmically moving right edge the likelihood cost is uniform
in the cutoff. -/
theorem truncatedMobiusLCMForm_moving_le {X : ℕ} (hX : 2 ≤ X) {b : ℝ} (hb : 0 ≤ b) :
    truncatedMobiusLCMForm X (1 + b / Real.log X) ≤
      Real.exp (4 * b) * truncatedMobiusLCMForm X 1 := by
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have h := truncatedMobiusLCMForm_shift_le (show 1 ≤ X by omega) (div_nonneg hb hlog.le)
  rwa [show 4 * (b / Real.log X) * Real.log X = 4 * b by field_simp [hlog.ne']] at h

/--
info: 'RiemannResearch.Analysis.InghamMollifier.truncatedMobiusLCMForm_moving_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms truncatedMobiusLCMForm_moving_le

end RiemannResearch.Analysis.InghamMollifier
