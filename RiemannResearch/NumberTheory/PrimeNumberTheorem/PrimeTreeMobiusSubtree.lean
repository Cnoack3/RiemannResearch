/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusLogBootstrapFinite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Fixed prime cylinders of the ordinary Möbius sum

Source: Section 9 of *Prime trees, fractional parts, and zeta zeros* (2026).
The finite prime deletion and power-bound transfer below are arithmetic.
The global analytic equivalence used at the last step is Titchmarsh,
*The Theory of the Riemann Zeta-function*, Theorem 14.25(C).
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder

/-- Set the Möbius weight to zero on the multiples of the forbidden primes. -/
def coefficient (B : Finset ℕ) (n : ℕ) : ℝ := by
  classical
  exact if ∀ p ∈ B, ¬p ∣ n then (ArithmeticFunction.moebius n : ℝ) else 0

/-- Sum of the retained weights up to and including the natural cutoff. -/
def roughSum (B : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, coefficient B (j + 1)

private theorem roughSum_succ (B : Finset ℕ) (n : ℕ) :
    roughSum B (n + 1) = roughSum B n + coefficient B (n + 1) :=
  Finset.sum_range_succ _ _

theorem roughSum_empty (n : ℕ) : roughSum ∅ n = M (n : ℝ) := by
  rw [M_nat_eq_sum_range, Finset.sum_range_succ']
  simp [roughSum, coefficient]

/-- Multiplying by a fresh prime deletes that prime from the allowed
quotient and reverses the sign of its Möbius weight. -/
theorem coefficient_mul_prime {B : Finset ℕ} {p : ℕ}
    (hB : ∀ q ∈ B, q.Prime) (hp : p.Prime) (hfresh : p ∉ B) (k : ℕ) :
    coefficient B (p * k) = -coefficient (insert p B) k := by
  classical
  by_cases hd : p ∣ k
  · have hsq : ¬Squarefree (p * k) := fun hs =>
      (Nat.squarefree_iff_prime_squarefree.mp hs) p hp (Nat.mul_dvd_mul_left p hd)
    simp [coefficient, hd,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  · have hrel : (∀ q ∈ B, ¬q ∣ p * k) ↔ (∀ q ∈ B, ¬q ∣ k) := by
      constructor
      · intro h q hq hdiv
        exact h q hq ((hB q hq).dvd_mul.mpr (Or.inr hdiv))
      · intro h q hq hdiv
        rcases (hB q hq).dvd_mul.mp hdiv with hqp | hqk
        · have he := (Nat.prime_dvd_prime_iff_eq (hB q hq) hp).mp hqp
          exact hfresh (he ▸ hq)
        · exact h q hq hqk
    have hmu : ArithmeticFunction.moebius (p * k) = -ArithmeticFunction.moebius k := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
          (hp.coprime_iff_not_dvd.mpr hd), ArithmeticFunction.moebius_apply_prime hp,
        neg_one_mul]
    by_cases h : ∀ q ∈ B, ¬q ∣ k
    · have ha := hrel.mpr h
      have hb : ∀ q ∈ insert p B, ¬q ∣ k :=
        (Finset.forall_mem_insert _ _ _).mpr ⟨hd,h⟩
      simp only [coefficient, if_pos ha, if_pos hb, hmu, Int.cast_neg]
    · have ha := mt hrel.mp h
      have hb : ¬∀ q ∈ insert p B, ¬q ∣ k := fun hh =>
        h (fun q hq => hh q (Finset.mem_insert_of_mem hq))
      simp only [coefficient, if_neg ha, if_neg hb, neg_zero]

/-- Exact deletion of one fresh Euler factor, including its boundary cutoff. -/
theorem roughSum_delete_factor {B : Finset ℕ} {p : ℕ}
    (hB : ∀ q ∈ B, q.Prime) (hp : p.Prime) (hfresh : p ∉ B) (n : ℕ) :
    roughSum B n = roughSum (insert p B) n - roughSum (insert p B) (n / p) := by
  classical
  induction n with
  | zero => simp [roughSum]
  | succ n ih =>
    rw [roughSum_succ B, roughSum_succ (insert p B), ih]
    by_cases hd : p ∣ n + 1
    · have hdiv := Nat.succ_div_of_dvd hd
      have hx : n + 1 = p * (n / p + 1) := by
        rw [← hdiv, Nat.mul_div_cancel' hd]
      have hterm : coefficient B (n+1) = -coefficient (insert p B) (n/p+1) := by
        rw [hx, coefficient_mul_prime hB hp hfresh]
      have hz : coefficient (insert p B) (n + 1) = 0 := by
        simp [coefficient, hd]
      rw [hdiv, roughSum_succ, hterm, hz]
      ring
    · have hterm : coefficient (insert p B) (n+1) = coefficient B (n+1) := by
        simp [coefficient, hd]
      rw [Nat.succ_div_of_not_dvd hd, hterm]
      ring

/-- An all-cutoff power bound. At a positive exponent this includes the natural
zero boundary and agrees with the usual bound restricted to positive cutoffs. -/
def PowerBound (a : ℝ) (f : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |f n| ≤ C * (n : ℝ) ^ a

private theorem div_rpow_mul_le (n p : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    ((n / p : ℕ) : ℝ) ^ a * (p : ℝ) ^ a ≤ (n : ℝ) ^ a := by
  rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.div_mul_le_self n p) ha

/-- Removing one fixed prime preserves every positive power, with constants
allowed to depend on the prime. -/
theorem powerBound_insert {B : Finset ℕ} {p : ℕ} {a : ℝ}
    (hB : ∀ q ∈ B, q.Prime) (hp : p.Prime) (hfresh : p ∉ B) (ha : 0 < a) :
    PowerBound a (roughSum B) ↔ PowerBound a (roughSum (insert p B)) := by
  have he := roughSum_delete_factor hB hp hfresh
  constructor
  · rintro ⟨C, hC, hroot⟩
    let u : ℝ := (p : ℝ)^a
    have hu : 1 < u := Real.one_lt_rpow (by exact_mod_cast hp.one_lt) ha
    have hu0 : 0 < u := zero_lt_one.trans hu
    let K := C * u / (u - 1)
    have hK : 0 ≤ K := div_nonneg (mul_nonneg hC hu0.le) (sub_nonneg.mpr hu.le)
    have hbalance : C + K / u = K := by
      dsimp [K]
      field_simp [ne_of_gt hu0, ne_of_gt (sub_pos.mpr hu)]
      ring
    refine ⟨K, hK, ?_⟩
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [roughSum, Real.zero_rpow ha.ne']
      · have hrec : roughSum (insert p B) n =
            roughSum B n + roughSum (insert p B) (n / p) := by linarith [he n]
        have hscale := mul_le_mul_of_nonneg_left (div_rpow_mul_le n p ha.le)
          (div_nonneg hK hu0.le)
        have halg : K/u * (((n/p : ℕ) : ℝ)^a * u) = K * ((n/p : ℕ) : ℝ)^a := by
          field_simp [ne_of_gt hu0]
        change K/u * (((n/p : ℕ) : ℝ)^a * u) ≤ _ at hscale
        rw [halg] at hscale
        calc |roughSum (insert p B) n| ≤ |roughSum B n| +
            |roughSum (insert p B) (n/p)| := by rw [hrec]; exact abs_add_le _ _
             _ ≤ C * (n : ℝ)^a + K * ((n/p : ℕ) : ℝ)^a :=
               add_le_add (hroot n) (ih (n/p) (Nat.div_lt_self hn hp.one_lt))
             _ ≤ C * (n : ℝ)^a + (K/u) * (n : ℝ)^a := add_le_add le_rfl hscale
             _ = K * (n : ℝ)^a := by rw [← add_mul, hbalance]
  · rintro ⟨C, hC, hrough⟩
    refine ⟨C+C, add_nonneg hC hC, ?_⟩
    intro n
    have hdiv : ((n / p : ℕ) : ℝ)^a ≤ (n : ℝ)^a :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self n p) ha.le
    calc |roughSum B n| ≤ |roughSum (insert p B) n| + |roughSum (insert p B) (n/p)| := by
           rw [he n, sub_eq_add_neg]
           simpa only [abs_neg] using abs_add_le (roughSum (insert p B) n)
             (-roughSum (insert p B) (n/p))
         _ ≤ C*(n:ℝ)^a + C*((n/p : ℕ):ℝ)^a := add_le_add (hrough n) (hrough (n/p))
         _ ≤ C*(n:ℝ)^a + C*(n:ℝ)^a := add_le_add le_rfl (mul_le_mul_of_nonneg_left hdiv hC)
         _ = (C+C)*(n:ℝ)^a := by ring

/-- No analytic assumption enters the finite-prime transfer. -/
theorem mertens_iff_roughSum (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime)
    {a : ℝ} (ha : 0 < a) :
    PowerBound a (fun n => M (n : ℝ)) ↔ PowerBound a (roughSum B) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp only [funext roughSum_empty]
  | @insert p B hfresh ih =>
    have hsmall : ∀ q ∈ B, q.Prime := fun q hq => hB q (Finset.mem_insert_of_mem hq)
    exact (ih hsmall).trans (powerBound_insert hsmall (hB p (Finset.mem_insert_self ..)) hfresh ha)

/-- The literal signed sum over a fixed cylinder. The predicates say that the
node contains the root and that the remaining prime factors avoid `B`. -/
def cylinder (r : ℕ) (B : Finset ℕ) (n : ℕ) : ℝ := by
  classical
  exact ∑ j ∈ Finset.range n, if r ∣ j+1 ∧ ∀ q ∈ B, ¬q ∣ (j+1)/r
    then (ArithmeticFunction.moebius (j+1) : ℝ) else 0

theorem cylinder_eq_roughSum {r : ℕ} (B : Finset ℕ)
    (hcover : ∀ p, p.Prime → p ∣ r → p ∈ B) (n : ℕ) :
    cylinder r B n = (ArithmeticFunction.moebius r : ℝ) * roughSum B (n / r) := by
  classical
  induction n with
  | zero => simp [cylinder, roughSum]
  | succ n ih =>
    unfold cylinder at ih ⊢
    rw [Finset.sum_range_succ, ih]
    by_cases hd : r ∣ n+1
    · have hdiv := Nat.succ_div_of_dvd hd
      have hx : r * ((n + 1) / r) = n+1 := Nat.mul_div_cancel' hd
      have hquot : (n / r + 1) = (n+1)/r := hdiv.symm
      rw [hdiv, roughSum_succ B, hquot]
      by_cases hgood : ∀ q ∈ B, ¬q ∣ (n+1)/r
      · have hc := Nat.coprime_of_dvd (m := r) (n := (n+1)/r)
            (fun p hp hpr => hgood p (hcover p hp hpr))
        have hm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
        rw [hx] at hm
        simp only [coefficient, if_pos (And.intro hd hgood), if_pos hgood, hm, Int.cast_mul,
          mul_add]
      · have hbad : ¬(r ∣ n+1 ∧ ∀ q ∈ B, ¬q ∣ (n+1)/r) := fun h => hgood h.2
        simp only [coefficient, if_neg hbad, if_neg hgood, add_zero]
    · simp [hd, Nat.succ_div_of_not_dvd hd]

/-- Arbitrarily many fixed prime exclusions and the fixed scale `r` preserve
the power bound in both directions. For the tree at `r`, take `B` to be
all primes through the largest prime of `r` (and empty at the root). -/
theorem mertens_iff_cylinder {r : ℕ} (hr : Squarefree r) (hr0 : 0 < r)
    (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime) (hcover : ∀ p, p.Prime → p ∣ r → p ∈ B)
    {a : ℝ} (ha : 0 < a) :
    PowerBound a (fun n => M (n : ℝ)) ↔ PowerBound a (cylinder r B) := by
  rw [mertens_iff_roughSum B hB ha]
  have hmu : |(ArithmeticFunction.moebius r : ℝ)| = 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hr
  have he (n : ℕ) : |cylinder r B n| = |roughSum B (n/r)| := by
    rw [cylinder_eq_roughSum B hcover, abs_mul, hmu, one_mul]
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, fun n => ?_⟩
    rw [he]
    exact (h (n/r)).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
      (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self n r) ha.le) hC)
  · rintro ⟨C, hC, h⟩
    refine ⟨C * (r : ℝ)^a, mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _), fun n => ?_⟩
    have hb := h (r*n)
    rw [he, Nat.mul_div_cancel_left _ hr0, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), ← mul_assoc] at hb
    exact hb

/-- The only remaining analytic input for the arithmetic formulation is the
global Littlewood--Mertens criterion (Titchmarsh, Theorem 14.25(C)). -/
theorem riemannHypothesis_iff_cylinder_of_littlewood {r : ℕ} (hr : Squarefree r)
    (hr0 : 0 < r) (B : Finset ℕ) (hB : ∀ p ∈ B, p.Prime)
    (hcover : ∀ p, p.Prime → p ∣ r → p ∈ B)
    (hLittlewood : RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → PowerBound (1/2+ε) (fun n => M (n : ℝ))) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → PowerBound (1/2+ε) (cylinder r B) := by
  rw [hLittlewood]
  exact forall_congr' fun ε => forall_congr' fun hε =>
    mertens_iff_cylinder hr hr0 B hB hcover (show 0 < 1/2+ε by linarith)

end RiemannResearch.NumberTheory.PrimeNumberTheorem.FixedPrimeCylinder
