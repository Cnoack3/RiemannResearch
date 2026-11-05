/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ParetoPacketGreenGram
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Dist

/-! # Positive Ramanujan kernels on integer intervals

A prime congruence kernel is the Gram matrix of the centered indicators of
its residue classes. Inducting on the finite prime support proves the
positive quadratic form for the actual squarefree Ramanujan sum. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

private def divisorValue (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun m => if m ∣ k then (m : ℝ) else 0, by simp⟩

private theorem divisorValue_mult (k : ℕ) : (divisorValue k).IsMultiplicative := by
  refine ⟨by simp [divisorValue], ?_⟩
  intro x y hxy
  have iff' : x * y ∣ k ↔ x ∣ k ∧ y ∣ k :=
    ⟨fun h => ⟨dvd_trans (dvd_mul_right x y) h, dvd_trans (dvd_mul_left y x) h⟩,
      fun h => hxy.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
  change (if x * y ∣ k then ((x * y : ℕ) : ℝ) else 0) = _
  by_cases hx : x ∣ k <;> by_cases hy : y ∣ k <;> simp [iff', hx, hy, divisorValue]

/-- At squarefree conductors the actual Ramanujan row is the product of
its prime divisibility contrasts. -/
theorem ramanujanSum_prime_contrasts (D k : ℕ) (hs : Squarefree D) :
    ramanujanSum D k = ∏ p ∈ D.primeFactors, ((if p ∣ k then (p : ℝ) else 0) - 1) := by
  let u : ArithmeticFunction ℝ := ArithmeticFunction.moebius
  have hm : u.IsMultiplicative := ArithmeticFunction.isMultiplicative_moebius.intCast
  have he := (divisorValue_mult k).prodPrimeFactors_add_of_squarefree hm hs
  rw [ArithmeticFunction.prodPrimeFactors_apply hs.ne_zero, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d s => divisorValue k d * u s)] at he
  calc
    _ = ∑ d ∈ D.divisors, divisorValue k d * u (D / d) := by
      apply Finset.sum_congr rfl
      intro d _
      change _ = (if d ∣ k then (d : ℝ) else 0) * (ArithmeticFunction.moebius (D / d) : ℝ)
      ring
    _ = _ := by
      rw [← he]
      apply Finset.prod_congr rfl
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      change ((if p ∣ k then (p : ℝ) else 0) + ((ArithmeticFunction.moebius p : ℤ) : ℝ)) = _
      rw [ArithmeticFunction.moebius_apply_prime hpr]
      push_cast <;> ring

private def primeKernel (p i j : ℕ) : ℝ :=
  (if i % p = j % p then (p : ℝ) else 0) - 1

private def feature (p i z : ℕ) : ℝ := (if i % p = z then (p : ℝ) else 0) - 1

private theorem local_feature_gram (p i j : ℕ) (hp : 0 < p) :
    (∑ z ∈ Finset.range p, feature p i z * feature p j z) = (p : ℝ) * primeKernel p i j := by
  classical
  let f := fun i z : ℕ => if i % p = z then (p : ℝ) else 0
  have single (i : ℕ) : (∑ z ∈ Finset.range p, f i z) = p := by
    simp [f, Nat.mod_lt i hp]
  have pair : (∑ z ∈ Finset.range p, f i z * f j z) =
      (if i % p = j % p then (p : ℝ) ^ 2 else 0) := by
    simp only [f, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_range.mpr (Nat.mod_lt i hp))]
    by_cases h : i % p = j % p <;> simp [h, Ne.symm, pow_two, eq_comm]
  have aff (z : ℕ) : feature p i z * feature p j z =
      f i z * f j z - f i z - f j z + 1 := by dsimp [feature, f]; ring
  simp_rw [aff]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, pair, single, single]
  by_cases h : i % p = j % p <;> simp [primeKernel, h] <;> ring

private theorem contrast_quadratic_nonneg (P T : Finset ℕ) (hp : ∀ p ∈ P, 0 < p)
    (x : ℕ → ℝ) :
    0 ≤ ∑ i ∈ T, ∑ j ∈ T, x i * x j * ∏ p ∈ P, primeKernel p i j := by
  classical
  induction P using Finset.induction_on generalizing x with
  | empty =>
    simp only [Finset.prod_empty, mul_one]
    simpa only [← Finset.mul_sum, ← Finset.sum_mul, pow_two] using sq_nonneg (∑ i ∈ T, x i)
  | @insert p P hpn ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hP : ∀ q ∈ P, 0 < q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    let G := fun i j => ∏ q ∈ P, primeKernel q i j
    have hloc (i j : ℕ) :
        (x i * x j * (primeKernel p i j * G i j)) * p =
          ∑ z ∈ Finset.range p, (x i * feature p i z) * (x j * feature p j z) * G i j := by
      calc
        _ = (x i * x j * G i j) * ((p : ℝ) * primeKernel p i j) := by ring
        _ = _ := by
          rw [← local_feature_gram p i j hp', Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by ring
    simp only [Finset.prod_insert hpn]
    apply (nonneg_of_mul_nonneg_left _ (show (0 : ℝ) < p by exact_mod_cast hp'))
    calc
      0 ≤ ∑ z ∈ Finset.range p, ∑ i ∈ T, ∑ j ∈ T,
        (x i * feature p i z) * (x j * feature p j z) * G i j := by
          exact Finset.sum_nonneg fun z _ => ih hP (fun i => x i * feature p i z)
      _ = (∑ i ∈ T, ∑ j ∈ T, x i * x j * (primeKernel p i j * G i j)) * p := by
        simp_rw [Finset.sum_mul, hloc]
        rw [Finset.sum_comm (s := Finset.range p) (t := T)]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

private theorem dvd_dist_iff (p i j : ℕ) : p ∣ Nat.dist i j ↔ i % p = j % p := by
  rcases le_total i j with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    exact (Nat.modEq_iff_dvd' h).symm
  · rw [Nat.dist_eq_sub_of_le_right h, eq_comm]
    exact (Nat.modEq_iff_dvd' h).symm

/-- Positive quadratic form on any finite set of sites, with arbitrary real
coefficients and any squarefree conductor. -/
theorem ramanujan_congruence_quadratic_nonneg (D : ℕ) (T : Finset ℕ) (x : ℕ → ℝ)
    (hs : Squarefree D) :
    0 ≤ ∑ i ∈ T, ∑ j ∈ T, x i * x j * ramanujanSum D (Nat.dist i j) := by
  simp_rw [ramanujanSum_prime_contrasts D _ hs, dvd_dist_iff]
  exact contrast_quadratic_nonneg D.primeFactors T
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos) x

theorem ramanujan_double_gram_nonneg (D t : ℕ) (hs : Squarefree D) :
    0 ≤ ∑ i ∈ Finset.range t, ∑ j ∈ Finset.range t, ramanujanSum D (Nat.dist i j) := by
  simpa only [one_mul] using
    ramanujan_congruence_quadratic_nonneg D (Finset.range t) (fun _ => 1) hs

end RiemannResearch.RH.Pareto
