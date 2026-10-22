/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteIncidenceTailCharge
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
# Divisor incidence inversion and positive gcd classes

Source: user-provided CRT carry memorandum, 19 October 2026. This is the
concrete divisor-Möbius specialization of the generic finite incidence inverse.
The cardinalities retain the positive representative L of residue zero.
These are finite identities for arbitrary positive periods, without
squarefreeness or analytic hypotheses.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.NumberTheory.DivisorIncidence

theorem sum_divisor_interval (L e c : ℕ) (hL : L ≠ 0)
    (hcL : c ∣ L) (hc : c ≠ 0) (hec : e ∣ c) (g : ℕ → ℝ) :
    (∑ j ∈ L.divisors.filter (fun j => e ∣ j ∧ j ∣ c), g (j / e)) =
      ∑ t ∈ (c / e).divisors, g t := by
  have he : 0 < e := Nat.pos_of_dvd_of_pos hec (Nat.pos_of_ne_zero hc)
  symm
  apply Finset.sum_bij (fun t _ => e * t)
  · intro t ht
    have htc : e * t ∣ c := by
      rw [← Nat.mul_div_cancel' hec]
      exact Nat.mul_dvd_mul_left e (Nat.dvd_of_mem_divisors ht)
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨htc.trans hcL, hL⟩, dvd_mul_right e t, htc⟩
  · intro t ht u hu htu
    exact Nat.eq_of_mul_eq_mul_left he htu
  · intro j hj
    obtain ⟨hjL, hej, hjc⟩ := Finset.mem_filter.mp hj
    refine ⟨j / e, Nat.mem_divisors.mpr ⟨Nat.div_dvd_div hej hjc, ?_⟩,
      Nat.mul_div_cancel' hej⟩
    exact Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hc) hec) he)
  · intro t ht
    rw [Nat.mul_div_cancel_left t he]

/-- The actual divisor incidence matrix has the usual Möbius left inverse. -/
theorem moebius_left_inverse (L e c : ℕ)
    (heL : e ∈ L.divisors) (hcL : c ∈ L.divisors) :
    (∑ j ∈ L.divisors,
      (if e ∣ j then (ArithmeticFunction.moebius (j/e) : ℝ) else 0) *
        (if j ∣ c then (1 : ℝ) else 0)) = if e = c then 1 else 0 := by
  classical
  have hc : c ≠ 0 := ne_of_gt (Nat.pos_of_mem_divisors hcL)
  have hs : (∑ j ∈ L.divisors,
      (if e ∣ j then (ArithmeticFunction.moebius (j/e) : ℝ) else 0) *
        (if j ∣ c then (1 : ℝ) else 0)) =
      ∑ j ∈ L.divisors.filter (fun j => e ∣ j ∧ j ∣ c),
        (ArithmeticFunction.moebius (j/e) : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> simp_all
  rw [hs]
  by_cases hec : e ∣ c
  · rw [sum_divisor_interval L e c (Nat.mem_divisors.mp hcL).2
      (Nat.dvd_of_mem_divisors hcL) hc hec (fun t => (ArithmeticFunction.moebius t : ℝ))]
    have hsum : (∑ t ∈ (c/e).divisors, (ArithmeticFunction.moebius t : ℝ)) =
        if c/e = 1 then 1 else 0 := by
      simpa only [ArithmeticFunction.coe_mul_zeta_apply,
        ArithmeticFunction.intCoe_apply, ArithmeticFunction.one_apply] using
        congrArg (fun f : ArithmeticFunction ℝ => f (c/e))
          (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
    rw [hsum]
    have hiff : c/e = 1 ↔ e = c := by
      constructor
      · intro h
        have := Nat.mul_div_cancel' hec
        simpa [h] using this
      · intro h
        subst c
        exact Nat.div_self (Nat.pos_of_mem_divisors heL)
    simp [hiff]
  · have hne : e ≠ c := by intro h; subst c; exact hec (dvd_refl e)
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    exact (hec (h.1.trans h.2)).elim

/-- The positive representatives in one gcd class. In particular e=L is
not discarded: it is the singleton containing L. -/
def gcdClass (L e : ℕ) : Finset ℕ :=
  (Finset.Icc 1 L).filter (fun k => Nat.gcd k L = e)

/-- Specialize the generic incidence extractor to every divisor gcd class. -/
theorem gcd_class_charge_moebius (L : ℕ) (hL : L ≠ 0)
    (s : Finset ℕ) (x rhs : ℕ → ℝ)
    (heq : ∀ d ∈ L.divisors,
      (∑ k ∈ s, if d ∣ k then x k else 0) = rhs d)
    (e : ℕ) (he : e ∈ L.divisors) :
    (∑ k ∈ s.filter (fun k => Nat.gcd k L = e), x k) =
      ∑ d ∈ L.divisors,
        if e ∣ d then (ArithmeticFunction.moebius (d/e) : ℝ) * rhs d else 0 := by
  classical
  let label : ℕ → L.divisors := fun k =>
    ⟨Nat.gcd k L, Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right k L, hL⟩⟩
  have hl (b c : L.divisors) :
      (∑ j : L.divisors,
        (if (b : ℕ) ∣ j then (ArithmeticFunction.moebius ((j : ℕ)/b) : ℝ) else 0) *
          (if (j : ℕ) ∣ c then (1 : ℝ) else 0)) =
        if b = c then 1 else 0 := by
    rw [Finset.sum_coe_sort L.divisors (fun j =>
      (if (b : ℕ) ∣ j then (ArithmeticFunction.moebius (j/(b : ℕ)) : ℝ) else 0) *
        (if j ∣ (c : ℕ) then (1 : ℝ) else 0))]
    simpa only [Subtype.ext_iff] using
      moebius_left_inverse L b c b.property c.property
  have hinc (d : L.divisors) :
      (∑ k ∈ s, (if (d : ℕ) ∣ (label k : ℕ) then (1 : ℝ) else 0) * x k) =
        rhs d := by
    convert heq d d.property using 1
    apply Finset.sum_congr rfl
    intro k hk
    simp [label, Nat.dvd_gcd_iff, Nat.dvd_of_mem_divisors d.property]
  have h := RiemannResearch.Analysis.FiniteIncidenceTailCharge.extract_class_charge
    s label x
    (fun d b : L.divisors => if (d : ℕ) ∣ b then 1 else 0)
    (fun b d : L.divisors =>
      if (b : ℕ) ∣ d then (ArithmeticFunction.moebius ((d : ℕ)/b) : ℝ) else 0)
    (fun d => rhs d) hl hinc ⟨e, he⟩
  rw [Finset.sum_coe_sort L.divisors (fun j =>
    (if e ∣ j then (ArithmeticFunction.moebius (j/e) : ℝ) else 0) * rhs j)] at h
  simpa only [Finset.sum_filter, label, Subtype.ext_iff,
    ite_mul, zero_mul] using h

theorem sum_Icc_one (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.Icc 1 n, f k) = ∑ k ∈ Finset.range n, f (k+1) := by
  symm
  refine Finset.sum_bij (fun k _ => k+1) ?_ ?_ ?_ ?_
  · intro k hk
    have := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k hk j hj he
    omega
  · intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    exact ⟨k-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk
    rfl

theorem coprime_Icc_card (n : ℕ) :
    ((Finset.Icc 1 n).filter (fun k => Nat.Coprime k n)).card = Nat.totient n := by
  let f : ℕ → ℝ := fun k => if Nat.Coprime k n then 1 else 0
  have he : f n = f 0 := by simp [f, Nat.coprime_iff_gcd_eq_one]
  have hshift : (∑ k ∈ Finset.range n, f (k+1)) =
      ∑ k ∈ Finset.range n, f k := by
    have h0 := Finset.sum_range_succ f n
    have h1 := Finset.sum_range_succ' f n
    linarith
  have hc : (((Finset.Icc 1 n).filter (fun k => Nat.Coprime k n)).card : ℝ) =
      (Nat.totient n : ℝ) := by
    rw [Finset.card_eq_sum_ones, Nat.totient, Finset.card_eq_sum_ones]
    push_cast
    rw [Finset.sum_filter, Finset.sum_filter, sum_Icc_one]
    change (∑ k ∈ Finset.range n, f (k+1)) = _
    rw [hshift]
    apply Finset.sum_congr rfl
    intro k hk
    simp [f, Nat.coprime_comm]
  exact_mod_cast hc

theorem gcd_class_card (L e : ℕ) (heL : e ∈ L.divisors) :
    (gcdClass L e).card = Nat.totient (L/e) := by
  classical
  have he : 0 < e := Nat.pos_of_mem_divisors heL
  have hdiv : e ∣ L := Nat.dvd_of_mem_divisors heL
  rw [← coprime_Icc_card (L/e)]
  symm
  apply Finset.card_bij (fun k _ => e*k)
  · intro k hk
    obtain ⟨hk, hcop⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, ?_⟩
    · calc
        e*k ≤ e*(L/e) := Nat.mul_le_mul_left e hkn
        _ = L := Nat.mul_div_cancel' hdiv
    · rw [← Nat.mul_div_cancel' hdiv, Nat.gcd_mul_left,
        Nat.coprime_iff_gcd_eq_one.mp hcop, mul_one]
  · intro k hk j hj heq
    exact Nat.eq_of_mul_eq_mul_left he heq
  · intro k hk
    obtain ⟨hks, hkg⟩ := Finset.mem_filter.mp hk
    obtain ⟨hk1, hkL⟩ := Finset.mem_Icc.mp hks
    have hek : e ∣ k := hkg ▸ Nat.gcd_dvd_left k L
    have hke : e ≤ k := Nat.le_of_dvd (by omega) hek
    refine ⟨k/e, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.div_pos hke he, Nat.div_le_div_right hkL⟩, ?_⟩,
      Nat.mul_div_cancel' hek⟩
    apply Nat.coprime_iff_gcd_eq_one.mpr
    rw [Nat.gcd_div hek hdiv, hkg, Nat.div_self he]

theorem gcd_class_endpoint (L : ℕ) (hL : 0 < L) :
    gcdClass L L = {L} := by
  ext k
  simp only [gcdClass, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hk1, hkL⟩, hg⟩
    have hLk : L ∣ k := hg ▸ Nat.gcd_dvd_left k L
    exact le_antisymm hkL (Nat.le_of_dvd (by omega) hLk)
  · rintro rfl
    exact ⟨⟨Nat.succ_le_iff.mpr hL, le_rfl⟩, Nat.gcd_self k⟩

end RiemannResearch.NumberTheory.DivisorIncidence
