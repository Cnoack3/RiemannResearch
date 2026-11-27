import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The Möbius transform of normalized conductor factors

This is the finite Euler-factor algebra in §2 of the CRT packet character
decomposition. Its input is a product over the distinct primes of the
normalized modulus. Repeated primes in the cofactor automatically vanish.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Inverting a product over the distinct prime factors detects squarefreeness. -/
theorem moebius_prime_support_product (w : ℕ → ℂ) (k : ℕ) (hk : 0 < k) :
    (∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k/d) : ℂ) *
      ∏ p ∈ d.primeFactors, w p) =
      if Squarefree k then ∏ p ∈ k.primeFactors, (w p - 1) else 0 := by
  classical
  let F := fun d : ℕ => if Squarefree d then ∏ p ∈ d.primeFactors, (w p - 1) else 0
  let G := fun d : ℕ => ∏ p ∈ d.primeFactors, w p
  have hs : ∀ n > 0, ∑ d ∈ n.divisors, F d = G n := by
    intro n hn
    unfold F G
    rw [← Finset.sum_filter, Nat.sum_divisors_filter_squarefree hn.ne', Nat.factors_eq]
    change (∑ t ∈ n.primeFactors.powerset, ∏ p ∈ t.val.prod.primeFactors, (w p - 1)) =
      ∏ p ∈ n.primeFactors, w p
    calc
      _ = ∑ t ∈ n.primeFactors.powerset, ∏ p ∈ t, (w p - 1) := by
        apply Finset.sum_congr rfl
        intro t ht
        have hp : ∀ p ∈ t, p.Prime := fun p hpt =>
          Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hpt)
        rw [Finset.prod_val, show t.prod id = ∏ p ∈ t, p from rfl, Nat.primeFactors_prod hp]
      _ = _ := by
        rw [← Finset.prod_one_add]
        apply Finset.prod_congr rfl
        intro p _
        ring
  have hi := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := F) (g := G)).mp hs k hk
  simpa only [Nat.sum_divisorsAntidiagonal'
    (fun a b => (ArithmeticFunction.moebius a : ℂ) * G b), F, G] using hi

/-- The normalized primitive-column product, including all cases where its
Möbius transform vanishes. Here z p is the conjugated primitive character value. -/
theorem primitive_conductor_moebius_product (f k : ℕ) (hk : 0 < k) (z : ℕ → ℂ) :
    (∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k/d) : ℂ) *
      ∏ p ∈ d.primeFactors, (if p ∣ f then 1 else (p : ℂ)*(1-z p)/(p-1))) =
      if Squarefree k ∧ k.Coprime f then
        ∏ p ∈ k.primeFactors, (1 - (p : ℂ)*z p)/(p-1) else 0 := by
  classical
  rw [moebius_prime_support_product _ _ hk]
  by_cases hsf : Squarefree k
  · rw [if_pos hsf]
    by_cases hcop : k.Coprime f
    · rw [if_pos ⟨hsf,hcop⟩]
      apply Finset.prod_congr rfl
      intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      have hpf := hp'.coprime_iff_not_dvd.mp
        (hcop.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp))
      have hp1 : (p : ℂ) ≠ 1 := by exact_mod_cast hp'.ne_one
      rw [if_neg hpf]
      field_simp [sub_ne_zero.mpr hp1]
      ring
    · rw [if_neg (fun h => hcop h.2)]
      obtain ⟨p,hp,hpk,hpf⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      apply Finset.prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp,hpk,hk.ne'⟩)
      rw [if_pos hpf, sub_self]
  · simp [hsf]

/-- Iterate the normalized residue-moment recursion from the primitive level.
The old value recurs at a repeated prime; a new prime contributes its Euler factor. -/
theorem normalized_prime_column_product (f : ℕ) (hf : 0 < f) (z C : ℕ → ℂ)
    (hstep : ∀ p m : ℕ, p.Prime → 0 < m → f ∣ m → C (p*m) =
      if p ∣ m then C m else (p : ℂ)*(1-z p)/(p-1) * C m)
    (k : ℕ) (hk : 0 < k) :
    C (f*k) = C f * ∏ p ∈ k.primeFactors,
      (if p ∣ f then 1 else (p : ℂ)*(1-z p)/(p-1)) := by
  classical
  induction k using induction_on_primes with
  | zero => omega
  | one => simp
  | prime_mul p a hp ih =>
    have ha : 0 < a := Nat.pos_of_mul_pos_left hk
    have he := hstep p (f*a) hp (Nat.mul_pos hf ha) (dvd_mul_right f a)
    rw [Nat.mul_left_comm, he, ih ha, Nat.primeFactors_mul hp.ne_zero ha.ne',
      hp.primeFactors, Finset.singleton_union]
    by_cases hpa : p ∣ a
    · rw [if_pos (dvd_mul_of_dvd_right hpa f),
        Finset.insert_eq_of_mem (Nat.mem_primeFactors.mpr ⟨hp,hpa,ha.ne'⟩)]
    · have hmem : p ∉ a.primeFactors := fun h => hpa (Nat.dvd_of_mem_primeFactors h)
      rw [Finset.prod_insert hmem]
      by_cases hpf : p ∣ f
      · rw [if_pos hpf, if_pos (dvd_mul_of_dvd_left hpf a), one_mul]
      · rw [if_neg hpf, if_neg (fun h => (hp.dvd_mul.mp h).elim hpf hpa)]
        ring

/-- Once the normalized lower-modulus columns are supplied, their entire
primitive Möbius transform is the squarefree coprime conductor product. -/
theorem primitive_column_moebius_sum (f k : ℕ) (hf : 0 < f) (hk : 0 < k)
    (z C : ℕ → ℂ) (A : ℂ)
    (hC : ∀ d ∈ k.divisors, C (f * d) =
      A * ∏ p ∈ d.primeFactors, (if p ∣ f then 1 else (p : ℂ) * (1 - z p) / (p - 1))) :
    (∑ d ∈ (f*k).divisors.filter (fun d => f ∣ d),
      (ArithmeticFunction.moebius (f*k/d) : ℂ) * C d) =
    if Squarefree k ∧ k.Coprime f then
      A * ∏ p ∈ k.primeFactors, (1 - (p : ℂ)*z p)/(p-1) else 0 := by
  classical
  have reindex : (∑ d ∈ (f*k).divisors.filter (fun d => f ∣ d),
      (ArithmeticFunction.moebius (f*k/d) : ℂ) * C d) =
      ∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k/d) : ℂ) * C (f*d) := by
    symm
    apply Finset.sum_bij (fun d _ => f*d)
    · intro d hd
      apply Finset.mem_filter.mpr
      exact ⟨Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left f (Nat.dvd_of_mem_divisors hd),
        (Nat.mul_pos hf hk).ne'⟩, dvd_mul_right f d⟩
    · intro d _ e _ he
      exact Nat.eq_of_mul_eq_mul_left hf he
    · intro d hd
      obtain ⟨hd, e, rfl⟩ := Finset.mem_filter.mp hd
      exact ⟨e, Nat.mem_divisors.mpr ⟨(Nat.mul_dvd_mul_iff_left hf).mp (Nat.dvd_of_mem_divisors hd),
        hk.ne'⟩, rfl⟩
    · intro d _
      rw [Nat.mul_div_mul_left _ _ hf]
  rw [reindex]
  have hsum := primitive_conductor_moebius_product f k hk z
  calc
    _ = A * (∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k/d) : ℂ) *
      ∏ p ∈ d.primeFactors, (if p ∣ f then 1 else (p : ℂ)*(1-z p)/(p-1))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        rw [hC d hd]
        ring
    _ = _ := by rw [hsum]; split_ifs <;> simp

end RiemannResearch.RH.Pareto
