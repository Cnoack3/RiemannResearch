/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ReciprocalChargeDilationArithmetic
import RiemannResearch.NumberTheory.QuotientKernelEnergyLimit
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusReciprocal

/-!
# Quotient energy for every finite signed integer-dilation kernel

Source: Section 5 of the user-provided lateral-screening continuation,
24 September 2026, and the previously verified pair-dilation construction.
All coefficient estimates and null-kernel hypotheses are supplied here.
This theorem is unconditional; it does not provide the RH source divergence.
The physical mixed-cutoff identification and its Euler-series evaluation
are separate obligations, not assumptions hidden in this module.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.NumberTheory
open RiemannResearch.NumberTheory.QuotientWindow

def shiftedMobiusCoefficient (h n : ℕ) : ℝ :=
  if h ∣ n then mobiusReciprocalCoefficient (n / h) else 0

def finiteDilationMobiusCoefficient (S : Finset ℕ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ h ∈ S, w h * shiftedMobiusCoefficient h n

def finiteDilationMobiusKernel (S : Finset ℕ) (w : ℕ → ℝ) (M : ℕ) : ℝ :=
  ∑ h ∈ S, w h * mobiusReciprocalSum (M / h)

def finiteDilationMobiusBound (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  1 + ∑ h ∈ S, |w h| * (h : ℝ)

@[simp] theorem shiftedMobiusCoefficient_zero (h : ℕ) :
    shiftedMobiusCoefficient h 0 = 0 := by
  simp [shiftedMobiusCoefficient]

@[simp] theorem finiteDilationMobiusCoefficient_zero (S : Finset ℕ) (w : ℕ → ℝ) :
    finiteDilationMobiusCoefficient S w 0 = 0 := by
  simp [finiteDilationMobiusCoefficient]

theorem shiftedMobiusCoefficient_abs_le (h n : ℕ) (hh : 0 < h) (hn : 0 < n) :
    |shiftedMobiusCoefficient h n| ≤ (h : ℝ) / (n : ℝ) := by
  unfold shiftedMobiusCoefficient
  by_cases hdvd : h ∣ n
  · rw [if_pos hdvd]
    have hq : 0 < n / h := by
      have hhn : h ≤ n := Nat.le_of_dvd hn hdvd
      have ht : 1 ≤ n / h := (Nat.le_div_iff_mul_le hh).mpr (by simpa using hhn)
      omega
    have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hh
    have hqR : ((n / h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hq
    have hnR : (n : ℝ) = ((n / h : ℕ) : ℝ) * (h : ℝ) := by
      exact_mod_cast (Nat.div_mul_cancel hdvd).symm
    calc
      _ ≤ 1 / ((n / h : ℕ) : ℝ) := mobiusReciprocalCoefficient_abs_le _
      _ = (h : ℝ) / (n : ℝ) := by rw [hnR]; field_simp [hhR, hqR]
  · rw [if_neg hdvd, abs_zero]
    positivity

theorem finiteDilationMobiusBound_pos (S : Finset ℕ) (w : ℕ → ℝ) :
    0 < finiteDilationMobiusBound S w := by
  unfold finiteDilationMobiusBound
  have hs : 0 ≤ ∑ h ∈ S, |w h| * (h : ℝ) :=
    Finset.sum_nonneg (fun h _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  linarith

theorem finiteDilationMobiusCoefficient_abs_le (S : Finset ℕ) (w : ℕ → ℝ)
    (hS : ∀ h ∈ S, 0 < h) (n : ℕ) (hn : 0 < n) :
    |finiteDilationMobiusCoefficient S w n| ≤ finiteDilationMobiusBound S w / (n : ℝ) := by
  calc
    _ ≤ ∑ h ∈ S, |w h * shiftedMobiusCoefficient h n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ S, |w h| * ((h : ℝ) / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (shiftedMobiusCoefficient_abs_le h n (hS h hh) hn) (abs_nonneg _)
    _ = (∑ h ∈ S, |w h| * (h : ℝ)) / (n : ℝ) := by
      simp only [mul_div_assoc, Finset.sum_div]
    _ ≤ finiteDilationMobiusBound S w / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      unfold finiteDilationMobiusBound
      linarith

theorem finiteDilationMobiusCoefficient_sum (S : Finset ℕ) (w : ℕ → ℝ)
    (hS : ∀ h ∈ S, 0 < h) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, finiteDilationMobiusCoefficient S w n) =
      finiteDilationMobiusKernel S w M := by
  unfold finiteDilationMobiusCoefficient finiteDilationMobiusKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.mul_sum]
  unfold shiftedMobiusCoefficient
  rw [positive_dilation_sum M h (hS h hh)]
  rfl

theorem finiteDilationMobiusKernel_abs_le (S : Finset ℕ) (w : ℕ → ℝ)
    (hS : ∀ h ∈ S, 0 < h) (M : ℕ) :
    |finiteDilationMobiusKernel S w M| ≤ finiteDilationMobiusBound S w := by
  have hm (K : ℕ) : |mobiusReciprocalSum K| ≤ 1 := by
    by_cases hK : K = 0
    · simp [hK, mobiusReciprocalSum]
    · exact mobiusReciprocalSum_abs_le_one K (Nat.pos_of_ne_zero hK)
  calc
    _ ≤ ∑ h ∈ S, |w h * mobiusReciprocalSum (M / h)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ h ∈ S, |w h| * (h : ℝ) := by
      apply Finset.sum_le_sum
      intro h hh
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hhR : (1 : ℝ) ≤ h := by exact_mod_cast (hS h hh)
      exact (hm _).trans hhR
    _ ≤ finiteDilationMobiusBound S w := by
      unfold finiteDilationMobiusBound
      linarith

theorem finiteDilationMobiusKernel_tendsto_zero (S : Finset ℕ) (w : ℕ → ℝ)
    (hS : ∀ h ∈ S, 0 < h) :
    Tendsto (finiteDilationMobiusKernel S w) atTop (𝓝 0) := by
  change Tendsto (fun M => ∑ h ∈ S, w h * mobiusReciprocalSum (M / h))
    atTop (𝓝 0)
  have ht := tendsto_finsetSum S
    (f := fun h M => w h * mobiusReciprocalSum (M / h))
    (a := fun _ => (0 : ℝ)) (by
      intro h hh
      have hdiv : Tendsto (fun M : ℕ => M / h) atTop atTop := by
        apply tendsto_atTop.2
        intro b
        filter_upwards [eventually_ge_atTop (b * h)] with M hM
        exact (Nat.le_div_iff_mul_le (hS h hh)).mpr hM
      simpa only [Function.comp_def, mul_zero] using
        (mobiusReciprocalSum_tendsto_zero.comp hdiv).const_mul (w h))
  simpa only [Finset.sum_const_zero] using ht

theorem finiteDilationMobiusKernel_window (S : Finset ℕ) (w : ℕ → ℝ)
    (hS : ∀ h ∈ S, 0 < h) (N d : ℕ) (hd : 0 < d) :
    finiteDilationMobiusKernel S w (N / d) -
        finiteDilationMobiusKernel S w (N / (d + 1)) =
      ∑ n ∈ window N d, finiteDilationMobiusCoefficient S w n := by
  have hab : N / (d + 1) ≤ N / d := by
    have haN := Nat.div_mul_le_self N (d + 1)
    apply (Nat.le_div_iff_mul_le hd).mpr
    nlinarith
  have hdis : Disjoint (Finset.Icc 1 (N / (d + 1))) (window N d) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    simp only [window, Finset.mem_Icc, Finset.mem_Ioc] at hn hn'
    omega
  have hu : Finset.Icc 1 (N / (d + 1)) ∪ window N d = Finset.Icc 1 (N / d) := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_union.mp hn with hn | hn
      · obtain ⟨hn0, hna⟩ := Finset.mem_Icc.mp hn
        exact Finset.mem_Icc.mpr ⟨hn0, hna.trans hab⟩
      · have hnw : N / (d + 1) < n ∧ n ≤ N / d := Finset.mem_Ioc.mp hn
        exact Finset.mem_Icc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) hnw.1, hnw.2⟩
    · intro hn
      obtain ⟨hn0, hnb⟩ := Finset.mem_Icc.mp hn
      by_cases hna : n ≤ N / (d + 1)
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Icc.mpr ⟨hn0, hna⟩))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hna, hnb⟩))
  rw [← finiteDilationMobiusCoefficient_sum S w hS (N / d),
    ← finiteDilationMobiusCoefficient_sum S w hS (N / (d + 1)),
    ← hu, Finset.sum_union hdis]
  ring

/-- Unconditional scalar energy limit for arbitrary finite signed dilations.
The dilation set and coefficients are fixed before the quotient cutoff grows. -/
theorem finiteDilationMobiusKernel_square_energy_tendsto
    (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ h ∈ S, 0 < h) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc 1 M,
      (k : ℝ) * ((k : ℝ) + 1) *
        (finiteDilationMobiusKernel S w (M / k) / (k : ℝ) -
          finiteDilationMobiusKernel S w (M / (k + 1)) / ((k : ℝ) + 1)) ^ 2)
      atTop (𝓝 (∑' n, finiteDilationMobiusCoefficient S w n ^ 2)) := by
  apply quotient_kernel_square_energy_tendsto_scaled
    (finiteDilationMobiusKernel S w) (finiteDilationMobiusCoefficient S w)
    (finiteDilationMobiusBound S w)
    (finiteDilationMobiusBound_pos S w) (finiteDilationMobiusCoefficient_zero S w)
  · exact finiteDilationMobiusCoefficient_abs_le S w hS
  · exact finiteDilationMobiusKernel_abs_le S w hS
  · exact finiteDilationMobiusKernel_tendsto_zero S w hS
  · exact finiteDilationMobiusKernel_window S w hS

end RiemannResearch.RH.Pareto
