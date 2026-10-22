import RiemannResearch.RH.AnnularArithmeticWeight
import RiemannResearch.RH.ChebyshevMellin
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The actual second Riesz sum as a finite Chebyshev convolution

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

All coefficients are the actual von Mangoldt coefficients, including prime
powers. The variable Chebyshev cutoff becomes an exact filtered finite
cutoff. No infinite sum, explicit formula, zero hypothesis, or RH is used.

The step indicator includes its lower endpoint. The passage from Icc to
Ioc in the integral uses the nonatomic Lebesgue measure explicitly. At
u=0 the Chebyshev function is zero; at n=x the resulting Riesz weight is
zero. The proof works for every x>0, including the empty cutoff x<1.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology

namespace RiemannResearch.RH.ActualRieszTwo
open RiemannResearch.RH
open RiemannResearch.RH.ChebyshevMellin

def uncenteredRieszTwo (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    ArithmeticFunction.vonMangoldt n * rieszTwoWeight ((n : ℝ) / x)

/-- The usual Chebyshev function already agrees with its zero extension
below 1. This makes the behavior near u=0 explicit. -/
def zeroExtendedPsi : ℝ → ℝ := (Ici (1 : ℝ)).indicator Chebyshev.psi

theorem zeroExtendedPsi_eq_psi : zeroExtendedPsi = Chebyshev.psi := by
  funext y
  by_cases hy : 1 ≤ y
  · have hmem : y ∈ Ici (1 : ℝ) := hy
    simp only [zeroExtendedPsi, indicator_of_mem hmem]
  · have hz : Chebyshev.psi y = 0 :=
      Chebyshev.psi_eq_zero_of_le_one (le_of_not_ge hy)
    have hmem : y ∉ Ici (1 : ℝ) := hy
    simp only [zeroExtendedPsi, indicator_of_notMem hmem, hz]

/-- Exact arithmetic cutoff identity on the whole convolution interval. -/
theorem cutoff_mul_eq_filter {x u : ℝ} (hx : 0 < x)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    Finset.Icc 1 ⌊x * u⌋₊ =
      (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) / x ≤ u) := by
  classical
  have hxu : 0 ≤ x * u := mul_nonneg hx.le hu.1
  have hxu_le : x * u ≤ x := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu.2 hx.le
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hn1, hn⟩
    have hnr : (n : ℝ) ≤ x * u := (Nat.le_floor_iff hxu).mp hn
    have hnx : n ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx.le).mpr (hnr.trans hxu_le)
    refine ⟨⟨hn1, hnx⟩, (div_le_iff₀ hx).mpr ?_⟩
    simpa only [mul_comm] using hnr
  · rintro ⟨⟨hn1, hnx⟩, hratio⟩
    refine ⟨hn1, (Nat.le_floor_iff hxu).mpr ?_⟩
    simpa only [mul_comm] using (div_le_iff₀ hx).mp hratio

def primeStep (x : ℝ) (n : ℕ) : ℝ → ℝ :=
  (Ici ((n : ℝ) / x)).indicator (fun _ : ℝ => ArithmeticFunction.vonMangoldt n)

def weightedPrimeStep (x : ℝ) (n : ℕ) : ℝ → ℝ :=
  (Ici ((n : ℝ) / x)).indicator
    (fun u : ℝ => ArithmeticFunction.vonMangoldt n * (1 - u))

theorem psi_mul_eq_finite_steps {x u : ℝ} (hx : 0 < x)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    Chebyshev.psi (x * u) = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, primeStep x n u := by
  classical
  rw [← sum_vonMangoldt_Icc (x * u), cutoff_mul_eq_filter hx hu, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnu : (n : ℝ) / x ≤ u
  · simp [primeStep, hnu]
  · simp [primeStep, hnu]

theorem weightedPsi_eq_finite_steps {x u : ℝ} (hx : 0 < x)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    (1 - u) * Chebyshev.psi (x * u) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, weightedPrimeStep x n u := by
  rw [psi_mul_eq_finite_steps hx hu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnu : (n : ℝ) / x ≤ u
  · simp [primeStep, weightedPrimeStep, hnu, mul_comm]
  · simp [primeStep, weightedPrimeStep, hnu]

theorem weightedPrimeStep_intervalIntegrable (x : ℝ) (n : ℕ) :
    IntervalIntegrable (weightedPrimeStep x n) volume 0 1 := by
  have hc : Continuous (fun u : ℝ => ArithmeticFunction.vonMangoldt n * (1 - u)) :=
    continuous_const.mul (continuous_const.sub continuous_id)
  have hi : IntervalIntegrable
      (fun u : ℝ => ArithmeticFunction.vonMangoldt n * (1 - u)) volume 0 1 :=
    hc.intervalIntegrable (0 : ℝ) 1
  exact ⟨hi.1.indicator measurableSet_Ici, hi.2.indicator measurableSet_Ici⟩

theorem weightedPsi_intervalIntegrable {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable (fun u : ℝ => (1 - u) * Chebyshev.psi (x * u)) volume 0 1 := by
  have hi : IntervalIntegrable
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, weightedPrimeStep x n) volume 0 1 :=
    IntervalIntegrable.sum (Finset.Icc 1 ⌊x⌋₊)
      (fun n _ => weightedPrimeStep_intervalIntegrable x n)
  apply hi.congr
  intro u hu
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
  have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2⟩
  simpa only [Finset.sum_apply] using (weightedPsi_eq_finite_steps hx hu').symm

/-- Exact step integral. The lower endpoint is included in the pointwise
step and removed from the integral only by Lebesgue nullity. -/
theorem integral_upper_step {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) (c : ℝ) :
    2 * (∫ u in (0 : ℝ)..1, (Ici q).indicator (fun u : ℝ => c * (1 - u)) u) =
      c * (1 - q) ^ 2 := by
  have he : Ioc (0 : ℝ) 1 ∩ Ici q = Icc q 1 := by
    ext u
    simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨⟨hu0, hu1⟩, hqu⟩
      exact ⟨hqu, hu1⟩
    · rintro ⟨hqu, hu1⟩
      exact ⟨⟨hq0.trans_le hqu, hu1⟩, hqu⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    setIntegral_indicator measurableSet_Ici, he, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hq1, intervalIntegral.integral_const_mul]
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume q 1 :=
    continuous_const.intervalIntegrable q 1
  have hid : IntervalIntegrable (fun u : ℝ => u) volume q 1 :=
    continuous_id.intervalIntegrable q 1
  have hsub := intervalIntegral.integral_sub hconst hid
  rw [hsub, intervalIntegral.integral_const, _root_.integral_id]
  simp only [smul_eq_mul]
  ring

theorem uncenteredRieszTwo_eq_convolution {x : ℝ} (hx : 0 < x) :
    uncenteredRieszTwo x =
      2 * ∫ u in (0 : ℝ)..1, (1 - u) * Chebyshev.psi (x * u) := by
  have hi :
      (∫ u in (0 : ℝ)..1, (1 - u) * Chebyshev.psi (x * u)) =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ∫ u in (0 : ℝ)..1, weightedPrimeStep x n u := by
    calc
      _ = ∫ u in (0 : ℝ)..1,
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, weightedPrimeStep x n u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
        exact weightedPsi_eq_finite_steps hx hu
      _ = _ := intervalIntegral.integral_finsetSum
        (fun n _ => weightedPrimeStep_intervalIntegrable x n)
  unfold uncenteredRieszTwo
  calc
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        2 * (∫ u in (0 : ℝ)..1, weightedPrimeStep x n u) := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hn1, hnf⟩ := Finset.mem_Icc.mp hn
      have hn0 : 0 < (n : ℝ) :=
        Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn1)
      have hnr : (n : ℝ) ≤ x := (Nat.le_floor_iff hx.le).mp hnf
      have hq0 : 0 < (n : ℝ) / x := div_pos hn0 hx
      have hq1 : (n : ℝ) / x ≤ 1 :=
        (div_le_iff₀ hx).mpr (by simpa only [one_mul] using hnr)
      rw [weightedPrimeStep, integral_upper_step hq0 hq1,
        rieszTwoWeight_of_le_one hq1]
    _ = 2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ∫ u in (0 : ℝ)..1, weightedPrimeStep x n u) := by rw [Finset.mul_sum]
    _ = _ := by rw [hi]

end RiemannResearch.RH.ActualRieszTwo
