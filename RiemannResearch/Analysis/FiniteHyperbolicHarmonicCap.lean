/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite exponential products and the harmonic hyperbolic cap

A complete finite exponential product is even and monotone in the absolute
row displacement. Translation of all frequencies cancels in the product.
For the integer logarithmic frequencies this gives the exact harmonic cap
and its elementary logarithmic upper bound.

Source: the finite balanced-row calculation in the user-requested Landau
and density provider analysis, RH/ActualHyperbolicLowerBounds20261005.md.
These are finite scalar identities and inequalities; no zeta distribution
estimate is assumed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHyperbolicHarmonicCap

def finiteExponentialSum {d : ℕ} (x : Fin d → ℝ) (t : ℝ) : ℝ :=
  ∑ n, Real.exp (t*x n)

theorem finiteExponentialProduct_eq_cosh {d : ℕ} (x : Fin d → ℝ) (t : ℝ) :
    finiteExponentialSum x t*finiteExponentialSum x (-t) =
      ∑ n, ∑ m, Real.cosh (t*(x n-x m)) := by
  have hforward (n m : Fin d) :
      Real.exp (t*(x n-x m)) = Real.exp (t*x n)*Real.exp (-t*x m) := by
    rw [show t*(x n-x m) = t*x n+(-t*x m) by ring, Real.exp_add]
  have hbackward (n m : Fin d) :
      Real.exp (-(t*(x n-x m))) = Real.exp (-t*x n)*Real.exp (t*x m) := by
    rw [show -(t*(x n-x m)) = -t*x n+t*x m by ring, Real.exp_add]
  have hsumForward :
      (∑ n : Fin d, ∑ m : Fin d, Real.exp (t*x n)*Real.exp (-t*x m)) =
      finiteExponentialSum x t*finiteExponentialSum x (-t) := by
    unfold finiteExponentialSum
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have hsumBackward :
      (∑ n : Fin d, ∑ m : Fin d, Real.exp (-t*x n)*Real.exp (t*x m)) =
      finiteExponentialSum x (-t)*finiteExponentialSum x t := by
    unfold finiteExponentialSum
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have hhalf (n m : Fin d) :
      Real.cosh (t*(x n-x m)) =
        (Real.exp (t*x n)*Real.exp (-t*x m)+
          Real.exp (-t*x n)*Real.exp (t*x m))/2 := by
    rw [Real.cosh_eq, hforward, hbackward]
  simp_rw [hhalf, add_div]
  simp only [Finset.sum_add_distrib]
  simp_rw [← Finset.sum_div]
  rw [hsumForward, hsumBackward]
  ring

theorem finiteExponentialProduct_le_endpoint {d : ℕ} (x : Fin d → ℝ)
    (t : ℝ) (ht : |t| ≤ 1) :
    finiteExponentialSum x t*finiteExponentialSum x (-t) ≤
      finiteExponentialSum x 1*finiteExponentialSum x (-1) := by
  rw [finiteExponentialProduct_eq_cosh, finiteExponentialProduct_eq_cosh]
  apply Finset.sum_le_sum
  intro n hn
  apply Finset.sum_le_sum
  intro m hm
  apply Real.cosh_le_cosh.mpr
  rw [abs_mul, one_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right ht (abs_nonneg (x n-x m))

theorem finiteExponentialProduct_translate {d : ℕ} (x : Fin d → ℝ)
    (b t : ℝ) :
    finiteExponentialSum (fun n => x n-b) t*
        finiteExponentialSum (fun n => x n-b) (-t) =
      finiteExponentialSum x t*finiteExponentialSum x (-t) := by
  rw [finiteExponentialProduct_eq_cosh, finiteExponentialProduct_eq_cosh]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  ring

def harmonicFrequencyMass (d : ℕ) : ℝ :=
  ∑ n : Fin d, (((n.val+1 : ℕ) : ℝ))⁻¹

def harmonicHyperbolicCap (d : ℕ) : ℝ :=
  ((d : ℝ)+Real.sqrt
    ((∑ n : Fin d, ((n.val+1 : ℕ) : ℝ))*harmonicFrequencyMass d))/2

theorem harmonicHyperbolicCap_nonneg (d : ℕ) : 0 ≤ harmonicHyperbolicCap d := by
  unfold harmonicHyperbolicCap
  positivity

theorem harmonicFrequencyMass_eq_harmonic (d : ℕ) :
    harmonicFrequencyMass d = (harmonic d : ℝ) := by
  have hrange : (harmonic d : ℝ) = ∑ j ∈ Finset.range d, 1/((j : ℝ)+1) := by
    simp [harmonic, one_div]
  rw [hrange, Finset.sum_range]
  unfold harmonicFrequencyMass
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Nat.cast_add, Nat.cast_one, one_div]

theorem sum_integerFrequency (d : ℕ) :
    (∑ n : Fin d, ((n.val+1 : ℕ) : ℝ)) = (d : ℝ)*((d : ℝ)+1)/2 := by
  have h (k : ℕ) :
      (∑ n ∈ Finset.range k, ((n : ℝ)+1)) = (k : ℝ)*((k : ℝ)+1)/2 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hd := h d
  rw [Finset.sum_range] at hd
  simpa only [Nat.cast_add, Nat.cast_one] using hd

theorem harmonicHyperbolicCap_eq (d : ℕ) :
    harmonicHyperbolicCap d =
      ((d : ℝ)+Real.sqrt ((d : ℝ)*((d : ℝ)+1)*(harmonic d : ℝ)/2))/2 := by
  unfold harmonicHyperbolicCap
  rw [sum_integerFrequency, harmonicFrequencyMass_eq_harmonic]
  rw [show (d : ℝ)*((d : ℝ)+1)/2*(harmonic d : ℝ) =
    (d : ℝ)*((d : ℝ)+1)*(harmonic d : ℝ)/2 by ring]

theorem harmonicHyperbolicCap_le_log (d : ℕ) (hd : 1 ≤ d) :
    harmonicHyperbolicCap d ≤
      (d : ℝ)/2*(1+Real.sqrt (1+Real.log (d : ℝ))) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hH0 : 0 ≤ (harmonic d : ℝ) := by
    rw [← harmonicFrequencyMass_eq_harmonic]
    unfold harmonicFrequencyMass
    positivity
  have hH := harmonic_le_one_add_log d
  have hL : 0 ≤ 1+Real.log (d : ℝ) := by
    have := Real.log_nonneg hdR
    linarith
  let P : ℝ := (d : ℝ)*((d : ℝ)+1)*(harmonic d : ℝ)/2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hPupper : P ≤ (d : ℝ)^2*(1+Real.log (d : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hH (sq_nonneg (d : ℝ))
    have hds : (d : ℝ)*((d : ℝ)+1)/2 ≤ (d : ℝ)^2 := by nlinarith
    have hfirst := mul_le_mul_of_nonneg_right hds hH0
    dsimp [P]
    nlinarith
  have hs : ((d : ℝ)*Real.sqrt (1+Real.log (d : ℝ)))^2 =
      (d : ℝ)^2*(1+Real.log (d : ℝ)) := by
    rw [mul_pow, Real.sq_sqrt hL]
  have hroot : Real.sqrt P ≤ (d : ℝ)*Real.sqrt (1+Real.log (d : ℝ)) := by
    have h0 : 0 ≤ (d : ℝ)*Real.sqrt (1+Real.log (d : ℝ)) := by positivity
    nlinarith [Real.sq_sqrt hP, Real.sqrt_nonneg P]
  rw [harmonicHyperbolicCap_eq]
  change ((d : ℝ)+Real.sqrt P)/2 ≤ _
  nlinarith

def integerLogFrequency (d : ℕ) (n : Fin d) : ℝ :=
  Real.log ((n.val+1 : ℕ) : ℝ)

theorem integerLogFrequency_endpoint_product (d : ℕ) :
    finiteExponentialSum (integerLogFrequency d) 1*
      finiteExponentialSum (integerLogFrequency d) (-1) =
      (∑ n : Fin d, ((n.val+1 : ℕ) : ℝ))*harmonicFrequencyMass d := by
  unfold finiteExponentialSum harmonicFrequencyMass integerLogFrequency
  have he (n : Fin d) :
      Real.exp (Real.log ((n.val+1 : ℕ) : ℝ)) = ((n.val+1 : ℕ) : ℝ) :=
    Real.exp_log (by positivity)
  simp only [one_mul, neg_one_mul, Real.exp_neg, he]

theorem harmonicHyperbolicCap_ge_card (d : ℕ) :
    (d : ℝ) ≤ harmonicHyperbolicCap d := by
  let P : ℝ := (∑ n : Fin d, ((n.val+1 : ℕ) : ℝ))*harmonicFrequencyMass d
  have hP : 0 ≤ P := by dsimp [P, harmonicFrequencyMass]; positivity
  have hzero : finiteExponentialSum (integerLogFrequency d) 0 = (d : ℝ) := by
    simp [finiteExponentialSum]
  have hprod : (d : ℝ)*(d : ℝ) ≤ P := by
    have h := finiteExponentialProduct_le_endpoint (integerLogFrequency d) 0
      (by norm_num)
    rw [neg_zero, hzero, integerLogFrequency_endpoint_product] at h
    exact h
  have hroot : (d : ℝ) ≤ Real.sqrt P := by
    nlinarith [Real.sq_sqrt hP, Real.sqrt_nonneg P, (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  unfold harmonicHyperbolicCap
  change (d : ℝ) ≤ ((d : ℝ)+Real.sqrt P)/2
  linarith

theorem harmonicHyperbolicCap_sub_card_nonneg (d : ℕ) :
    0 ≤ harmonicHyperbolicCap d-(d : ℝ) :=
  sub_nonneg.mpr (harmonicHyperbolicCap_ge_card d)

theorem harmonicHyperbolicCap_le_card_log (d : ℕ) (hd : 1 ≤ d) :
    harmonicHyperbolicCap d ≤ (d : ℝ)*(1+Real.log (d : ℝ)) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  have hs : Real.sqrt (1+Real.log (d : ℝ)) ≤ 1+Real.log (d : ℝ) := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ 1+Real.log (d : ℝ)),
      sq_nonneg (Real.sqrt (1+Real.log (d : ℝ))-1)]
  have h := harmonicHyperbolicCap_le_log d hd
  have hp := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (d : ℝ)/2)
  nlinarith [mul_nonneg (Nat.cast_nonneg d : (0:ℝ) ≤ d) hL]

end RiemannResearch.Analysis.FiniteHyperbolicHarmonicCap
