import RiemannResearch.Analysis.FiniteStrictTail
import RiemannResearch.Analysis.LogarithmicTailCounting
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Positivity

/-!
# Finite moments from exponential strict-tail bounds

The finite layer-cake identity and Euler's integral for `Real.Gamma` give
factorial moment bounds.  In particular, an exponential bound on the strict
tail contains all positive integral moment bounds, without a separate moment
assumption.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.Analysis.LogarithmicMatrixMoments

open FiniteStrictTail

/-- Euler's integral in the natural-power normalization needed for moments. -/
theorem integral_pow_mul_exp_neg (p : ℕ) :
    (∫ t : ℝ in Ioi 0, Real.exp (-t) * t ^ p) = (p.factorial : ℝ) := by
  calc
    _ = Real.Gamma ((p : ℝ) + 1) := by
      simpa only [add_sub_cancel_right, Real.rpow_natCast] using
        (Real.Gamma_eq_integral (by positivity : (0 : ℝ) < (p : ℝ) + 1)).symm
    _ = _ := Real.Gamma_nat_eq_factorial p

theorem integrableOn_pow_mul_exp_neg (p : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ p) (Ioi 0) := by
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using
    (Real.GammaIntegral_convergent (by positivity : (0 : ℝ) < (p : ℝ) + 1))

/-- A finite nonnegative family with strict tail bounded by `B * exp (-t)`
has each positive integral moment bounded by `B` times the factorial.
The finite height `M` only records a bound on the finite family. -/
theorem finite_moment_of_exponential_tail {ι : Type*}
    (s : Finset ι) (x : ι → ℝ) (B M : ℝ) (p : ℕ)
    (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hxM : ∀ i ∈ s, x i ≤ M)
    (htail : ∀ t : ℝ, 0 ≤ t → tail s x t ≤ B * Real.exp (-t)) :
    (∑ i ∈ s, x i ^ (p + 1)) ≤ B * ((p + 1).factorial : ℝ) := by
  classical
  let f : ℝ → ℝ := fun t => (p + 1 : ℝ) * t ^ p
  let g : ℝ → ℝ := fun t => (B * (p + 1 : ℝ)) * (Real.exp (-t) * t ^ p)
  have hf : Continuous f := continuous_const.mul (continuous_id.pow p)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ => u ^ (p + 1)) (f t) t := by
    intro t
    simpa only [f, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] using
      hasDerivAt_pow (p + 1) t
  have hbad : badSum s x (fun t : ℝ => t ^ (p + 1)) 0 =
      ∑ i ∈ s, x i ^ (p + 1) := by
    unfold badSum
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hxi : 0 < x i
    · simp only [if_pos hxi]
    · have hzero : x i = 0 := le_antisymm (le_of_not_gt hxi) (hx0 i hi)
      simp [hxi, hzero]
  have hlayer : (∑ i ∈ s, x i ^ (p + 1)) =
      ∫ t in 0..M, tail s x t * f t := by
    have h := layerCake s x (fun t : ℝ => t ^ (p + 1)) f hf hderiv 0 M hM hxM
    simpa only [hbad, zero_pow (Nat.succ_ne_zero p), zero_mul, zero_add] using h
  have hg : IntegrableOn g (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg p).const_mul (B * (p + 1 : ℝ))
  have hsub : Ioc (0 : ℝ) M ⊆ Ioi (0 : ℝ) := fun _ ht => ht.1
  have hleft : IntegrableOn (fun t => tail s x t * f t) (Ioc 0 M) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hM).mp
      (intervalIntegrable_tail_mul s x f hf 0 M)
  have hpoint : ∀ t ∈ Ioc (0 : ℝ) M, tail s x t * f t ≤ g t := by
    intro t ht
    calc
      tail s x t * f t ≤ (B * Real.exp (-t)) * f t :=
        mul_le_mul_of_nonneg_right (htail t ht.1.le)
          (mul_nonneg (by positivity) (pow_nonneg ht.1.le p))
      _ = g t := by dsimp [f, g]; ring
  have hgnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg hB (by positivity))
      (mul_nonneg (Real.exp_pos (-t)).le (pow_nonneg ht.le p))
  have hfull : (∫ t : ℝ in Ioi 0, g t) = B * ((p + 1).factorial : ℝ) := by
    rw [show g = fun t : ℝ => (B * (p + 1 : ℝ)) *
        (Real.exp (-t) * t ^ p) from rfl,
      integral_const_mul, integral_pow_mul_exp_neg,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring
  calc
    (∑ i ∈ s, x i ^ (p + 1)) = ∫ t in Ioc 0 M, tail s x t * f t := by
      rw [hlayer, intervalIntegral.integral_of_le hM]
    _ ≤ ∫ t in Ioc 0 M, g t :=
      setIntegral_mono_on hleft (hg.mono_set hsub) measurableSet_Ioc hpoint
    _ ≤ ∫ t in Ioi 0, g t :=
      setIntegral_mono_set hg hgnonneg hsub.eventuallyLE
    _ = B * ((p + 1).factorial : ℝ) := hfull

/-- The actual one-sided logarithmic moment budget.  The zero exponent is
included; positive exponents follow from the arithmetic exponential tail. -/
theorem finite_log_moment (p n : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.Icc 1 (n - 1), Real.log ((n : ℝ) / (m : ℝ)) ^ p) ≤
      (p.factorial : ℝ) * (n : ℝ) := by
  cases p with
  | zero =>
      simpa only [pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
        Nat.factorial_zero, Nat.cast_one, one_mul, Nat.card_Icc,
        Nat.add_sub_cancel_right] using
        (show ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) from by
          exact_mod_cast Nat.sub_le n 1)
  | succ p =>
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hx0 : ∀ m ∈ Finset.Icc 1 (n - 1),
          0 ≤ Real.log ((n : ℝ) / (m : ℝ)) := by
        intro m hm
        rcases Finset.mem_Icc.mp hm with ⟨hm1, hmn⟩
        have hmR : (0 : ℝ) < (m : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
        have hmnR : (m : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (hmn.trans (Nat.sub_le n 1))
        exact Real.log_nonneg ((one_le_div hmR).mpr hmnR)
      have hxM : ∀ m ∈ Finset.Icc 1 (n - 1),
          Real.log ((n : ℝ) / (m : ℝ)) ≤ (n : ℝ) := by
        intro m hm
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hm).1
        calc
          Real.log ((n : ℝ) / (m : ℝ)) ≤ (n : ℝ) / (m : ℝ) :=
            Real.log_le_self (div_nonneg hnR.le (by linarith))
          _ ≤ (n : ℝ) := div_le_self hnR.le hm1
      simpa only [mul_comm] using
        finite_moment_of_exponential_tail (Finset.Icc 1 (n - 1))
          (fun m : ℕ => Real.log ((n : ℝ) / (m : ℝ))) (n : ℝ) (n : ℝ) p
          hnR.le hnR.le hx0 hxM (fun t _ => tail_log_ratio_le_exp hn t)

/-- All absolute logarithmic moments of the square `1 ≤ m,n ≤ X` have the
factorial matrix budget. -/
theorem double_abs_log_moment (p X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
      |Real.log ((n : ℝ) / (m : ℝ))| ^ p) ≤
        (p.factorial : ℝ) * (X : ℝ) * ((X : ℝ) + 1) := by
  cases p with
  | zero =>
      have hX : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
      simpa using mul_le_mul_of_nonneg_left
        (show (X : ℝ) ≤ (X : ℝ) + 1 by linarith) hX
  | succ p =>
      exact double_abs_log_moment_le_of_one_sided (Nat.succ_pos p)
        (fun n hn => finite_log_moment (p + 1) n hn) X

/-- The even matrix moment budget used in high-order truncation estimates. -/
theorem double_even_log_moment (k X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 X,
      |Real.log ((n : ℝ) / (m : ℝ))| ^ (2 * k)) ≤
        ((2 * k).factorial : ℝ) * (X : ℝ) * ((X : ℝ) + 1) :=
  double_abs_log_moment (2 * k) X

/-- The corresponding one-sided even moment estimate. -/
theorem finite_even_log_moment (k n : ℕ) (hn : 0 < n) :
    (∑ m ∈ Finset.Icc 1 (n - 1), Real.log ((n : ℝ) / (m : ℝ)) ^ (2 * k)) ≤
      ((2 * k).factorial : ℝ) * (n : ℝ) :=
  finite_log_moment (2 * k) n hn

end RiemannResearch.Analysis.LogarithmicMatrixMoments
