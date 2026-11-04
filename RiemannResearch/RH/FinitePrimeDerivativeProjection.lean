/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.FinitePrimeLikelihood
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact finite prime-product derivative projection

Source: elementary finite-product Hilbert projection specialization of the
prime-block agenda (4 November 2026), using the existing finite likelihood
and Boolean-lift modules. Euler-product background: NIST DLMF 25.2.11.
The target is derivative least squares; no bounded primitive energy or RH
provider is asserted. Exact norm-square remainders are retained.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.FinitePrimeDerivativeProjection
open FinitePrimeLikelihood

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def zeroConfiguration : ι → Bool := fun _ => false

def zeroIndicator (x : ι → Bool) : ℝ := if x = zeroConfiguration then 1 else 0

def zeroMass (p : ι → ℝ) : ℝ := ∏ i, (1 - primeParameter (p i))

def derivativeAtom (p : ι → ℝ) (A : Finset ι) (x : ι → Bool) : ℝ :=
  1/(∏ i ∈ A, p i) - finiteMonomial A x

def derivativeProjection (p : ι → ℝ) (q : ℝ) (x : ι → Bool) : ℝ :=
  q / zeroMass p * zeroIndicator x -
    q / (2:ℝ)^(Fintype.card ι) * finiteLikelihood p x

def targetError (p : ι → ℝ) (q : ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  q - 2*q*f zeroConfiguration +
    tensorExpectation (fun i => primeParameter (p i)) (fun x => f x ^ 2)

private theorem expectation_sub (r : ι → ℝ) (f g : (ι → Bool) → ℝ) :
    tensorExpectation r (fun x => f x - g x) =
      tensorExpectation r f - tensorExpectation r g := by
  simp [tensorExpectation, mul_sub, Finset.sum_sub_distrib]

private theorem expectation_const_mul (r : ι → ℝ) (c : ℝ)
    (f : (ι → Bool) → ℝ) :
    tensorExpectation r (fun x => c*f x) = c*tensorExpectation r f := by
  unfold tensorExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem expectation_square_sub (r : ι → ℝ) (f g : (ι → Bool) → ℝ) :
    tensorExpectation r (fun x => (f x - g x)^2) =
      tensorExpectation r (fun x => f x ^ 2) -
      2*tensorExpectation r (fun x => g x * f x) +
      tensorExpectation r (fun x => g x ^ 2) := by
  unfold tensorExpectation
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem expectation_zero_indicator (p : ι → ℝ) (f : (ι → Bool) → ℝ) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun x => zeroIndicator x * f x) = zeroMass p * f zeroConfiguration := by
  unfold tensorExpectation
  have hpoint (x : ι → Bool) :
      productMass (fun i => primeParameter (p i)) x * (zeroIndicator x * f x) =
      if x = zeroConfiguration then zeroMass p * f zeroConfiguration else 0 := by
    by_cases hx : x = zeroConfiguration
    · subst x
      simp [zeroIndicator, productMass, zeroMass, zeroConfiguration, bernoulliMass]
    · simp [zeroIndicator, hx]
  simp_rw [hpoint]
  simp

theorem finiteLikelihood_zero (p : ι → ℝ) :
    finiteLikelihood p zeroConfiguration = baseRatio p := by
  simp [finiteLikelihood, tensorFunction, zeroConfiguration, primeLikelihood, baseRatio]

theorem finiteMonomial_zero {A : Finset ι} (hA : A.Nonempty) :
    finiteMonomial A zeroConfiguration = 0 := by
  obtain ⟨i, hi⟩ := hA
  unfold finiteMonomial
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi, boolIndicator, zeroConfiguration]

theorem likelihood_orthogonal_derivative (p : ι → ℝ) (A : Finset ι)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i + 1 ≠ 0) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun x => finiteLikelihood p x * derivativeAtom p A x) = 0 := by
  have hsplit : tensorExpectation (fun i => primeParameter (p i))
      (fun x => finiteLikelihood p x * derivativeAtom p A x) =
      1/(∏ i ∈ A, p i) *
        tensorExpectation (fun i => primeParameter (p i)) (finiteLikelihood p) -
      tensorExpectation (fun i => primeParameter (p i))
        (fun x => finiteLikelihood p x * finiteMonomial A x) := by
    unfold tensorExpectation derivativeAtom
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsplit, expect_finiteLikelihood p hp0 hp1,
    expect_finiteLikelihood_monomial p hp0 hp1 A]
  ring

theorem projection_normal_equation (p : ι → ℝ) (q : ℝ) (A : Finset ι)
    (hA : A.Nonempty) (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i + 1 ≠ 0)
    (ha : zeroMass p ≠ 0) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun x => derivativeProjection p q x * derivativeAtom p A x) =
      q/(∏ i ∈ A, p i) := by
  have hsplit : tensorExpectation (fun i => primeParameter (p i))
      (fun x => derivativeProjection p q x * derivativeAtom p A x) =
      q/zeroMass p * tensorExpectation (fun i => primeParameter (p i))
        (fun x => zeroIndicator x * derivativeAtom p A x) -
      q/(2:ℝ)^(Fintype.card ι) *
        tensorExpectation (fun i => primeParameter (p i))
          (fun x => finiteLikelihood p x * derivativeAtom p A x) := by
    unfold tensorExpectation derivativeProjection
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsplit, expectation_zero_indicator,
    likelihood_orthogonal_derivative p A hp0 hp1]
  simp only [derivativeAtom, finiteMonomial_zero hA, sub_zero, mul_zero]
  rw [← mul_assoc, div_mul_cancel₀ q ha]
  ring

theorem projection_energy (p : ι → ℝ) (q : ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i + 1 ≠ 0)
    (ha : zeroMass p ≠ 0) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun x => derivativeProjection p q x ^ 2) =
      q^2/zeroMass p - q^2*baseRatio p/(2:ℝ)^(Fintype.card ι) := by
  have hzero : tensorExpectation (fun i => primeParameter (p i))
      (fun x => zeroIndicator x ^ 2) = zeroMass p := by
    have h := expectation_zero_indicator p (fun _ => (1:ℝ))
    have hpoint : (fun x : ι → Bool => zeroIndicator x ^ 2) =
        (fun x => zeroIndicator x * 1) := by
      funext x
      unfold zeroIndicator
      split_ifs <;> norm_num
    rw [hpoint]
    simpa using h
  have hmixed : tensorExpectation (fun i => primeParameter (p i))
      (fun x => zeroIndicator x * finiteLikelihood p x) =
      zeroMass p * baseRatio p := by
    rw [expectation_zero_indicator, finiteLikelihood_zero]
  have hsplit : tensorExpectation (fun i => primeParameter (p i))
      (fun x => derivativeProjection p q x ^ 2) =
      (q/zeroMass p)^2 * tensorExpectation (fun i => primeParameter (p i))
        (fun x => zeroIndicator x ^ 2) -
      2*(q/zeroMass p)*(q/(2:ℝ)^(Fintype.card ι)) *
        tensorExpectation (fun i => primeParameter (p i))
          (fun x => zeroIndicator x * finiteLikelihood p x) +
      (q/(2:ℝ)^(Fintype.card ι))^2 *
        tensorExpectation (fun i => primeParameter (p i))
          (fun x => finiteLikelihood p x ^ 2) := by
    unfold tensorExpectation derivativeProjection
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsplit, hzero, hmixed, expect_finiteLikelihood_sq p hp0 hp1]
  have hM : (2:ℝ)^(Fintype.card ι) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [ha, hM]
  ring

theorem expectation_projection_mul (p : ι → ℝ) (q : ℝ)
    (ha : zeroMass p ≠ 0) (f : (ι → Bool) → ℝ) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun x => derivativeProjection p q x * f x) =
      q*f zeroConfiguration - q/(2:ℝ)^(Fintype.card ι) *
        tensorExpectation (fun i => primeParameter (p i))
          (fun x => finiteLikelihood p x * f x) := by
  have hpoint : (fun x => derivativeProjection p q x * f x) =
      (fun x => (q/zeroMass p)*(zeroIndicator x * f x) -
        (q/(2:ℝ)^(Fintype.card ι))*(finiteLikelihood p x * f x)) := by
    funext x
    unfold derivativeProjection
    ring
  rw [hpoint, expectation_sub, expectation_const_mul, expectation_const_mul,
    expectation_zero_indicator]
  rw [← mul_assoc, div_mul_cancel₀ q ha]

theorem projection_admissible (p : ι → ℝ) (q : ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i + 1 ≠ 0)
    (ha : zeroMass p ≠ 0) :
    tensorExpectation (fun i => primeParameter (p i))
      (fun x => finiteLikelihood p x*derivativeProjection p q x) = 0 := by
  have h := expectation_projection_mul p q ha (finiteLikelihood p)
  have hpoint : (fun x => finiteLikelihood p x*finiteLikelihood p x) =
      (fun x => finiteLikelihood p x ^ 2) := by funext x; ring
  rw [hpoint, expect_finiteLikelihood_sq p hp0 hp1, finiteLikelihood_zero] at h
  have hM : (2:ℝ)^(Fintype.card ι) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcancel : q*baseRatio p - q/(2:ℝ)^(Fintype.card ι)*
      ((2:ℝ)^(Fintype.card ι)*baseRatio p) = 0 := by
    field_simp [hM]
    ring
  rw [hcancel] at h
  simpa [mul_comm] using h

theorem targetError_complete (p : ι → ℝ) (q : ℝ)
    (ha : zeroMass p ≠ 0) (f : (ι → Bool) → ℝ)
    (horth : tensorExpectation (fun i => primeParameter (p i))
      (fun x => finiteLikelihood p x * f x) = 0) :
    targetError p q f =
      q - tensorExpectation (fun i => primeParameter (p i))
        (fun x => derivativeProjection p q x ^ 2) +
      tensorExpectation (fun i => primeParameter (p i))
        (fun x => (f x-derivativeProjection p q x)^2) := by
  rw [expectation_square_sub, expectation_projection_mul p q ha f, horth]
  unfold targetError
  ring

theorem targetError_exact (p : ι → ℝ) (q : ℝ)
    (hp0 : ∀ i, p i ≠ 0) (hp1 : ∀ i, p i + 1 ≠ 0)
    (ha : zeroMass p ≠ 0) (f : (ι → Bool) → ℝ)
    (horth : tensorExpectation (fun i => primeParameter (p i))
      (fun x => finiteLikelihood p x * f x) = 0) :
    targetError p q f = q-q^2/zeroMass p +
      q^2*baseRatio p/(2:ℝ)^(Fintype.card ι) +
      tensorExpectation (fun i => primeParameter (p i))
        (fun x => (f x-derivativeProjection p q x)^2) := by
  rw [targetError_complete p q ha f horth, projection_energy p q hp0 hp1 ha]
  ring

theorem expectation_square_nonneg (p : ι → ℝ) (hp : ∀ i, 1 ≤ p i)
    (f : (ι → Bool) → ℝ) :
    0 ≤ tensorExpectation (fun i => primeParameter (p i)) (fun x => f x ^ 2) := by
  unfold tensorExpectation
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg _ (sq_nonneg _)
  apply productMass_nonneg
  · intro i
    exact (primeParameter_mem_unitInterval (hp i)).1
  · intro i
    exact (primeParameter_mem_unitInterval (hp i)).2

theorem derivativeProjection_minimizes (p : ι → ℝ) (q : ℝ)
    (hp : ∀ i, 1 ≤ p i) (ha : zeroMass p ≠ 0)
    (f : (ι → Bool) → ℝ)
    (horth : tensorExpectation (fun i => primeParameter (p i))
      (fun x => finiteLikelihood p x * f x) = 0) :
    targetError p q (derivativeProjection p q) ≤ targetError p q f := by
  have hp0 (i : ι) : p i ≠ 0 := by have := hp i; linarith
  have hp1 (i : ι) : p i+1 ≠ 0 := by have := hp i; linarith
  rw [targetError_exact p q hp0 hp1 ha f horth,
    targetError_exact p q hp0 hp1 ha (derivativeProjection p q)
      (projection_admissible p q hp0 hp1 ha)]
  have hnonneg := expectation_square_nonneg p hp
    (fun x => f x-derivativeProjection p q x)
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0)]
  simp only [tensorExpectation, mul_zero, Finset.sum_const_zero, add_zero]
  exact le_add_of_nonneg_right hnonneg

end RiemannResearch.RH.FinitePrimeDerivativeProjection
