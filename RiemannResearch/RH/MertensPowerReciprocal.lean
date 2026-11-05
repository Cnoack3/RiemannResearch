/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ScalarPrefixDensityTail
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MobiusReciprocal

/-!
# Abel summation for the reciprocal Möbius charge under a power bound

Source: the user-provided Mertens displacement archive.
-/
noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- One power estimate for the ordinary Mertens function gives the matching
reciprocal estimate, through signed Abel summation in natural order. -/
theorem mobiusReciprocalSum_le_of_M_nat_power
    (s C : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) (hC : 0 ≤ C)
    (hM : ∀ t : ℕ, 0 < t → |M (t : ℝ)| ≤ C * (t : ℝ)^s)
    (N : ℕ) (hN : 0 < N) :
    |mobiusReciprocalSum N| ≤ ((2 + 1/(1-s)) * C) * (N : ℝ)^(s-1) := by
  let w : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ)
  have hw0 : w 0 = 0 := by simp [w]
  have hrec (n : ℕ) : positiveArithmeticPrefix (fun i => w i / (i:ℝ)) n =
      mobiusReciprocalSum n := by
    induction n with
    | zero => simp [mobiusReciprocalSum]
    | succ n ih => rw [positiveArithmeticPrefix_succ, mobiusReciprocalSum_succ, ih]
  have hlim : Tendsto (fun n => positiveArithmeticPrefix (fun i => w i / (i:ℝ)) n)
      atTop (𝓝 0) := by
    simpa only [hrec] using mobiusReciprocalSum_tendsto_zero
  have hP (x : ℝ) (hx : 1 ≤ x) : |arithmeticSummatory w x| ≤ C * x^s * (1:ℝ) := by
    have hx0 : 0 ≤ x := by linarith
    have hfloor : 0 < ⌊x⌋₊ := by
      have h : (1 : ℕ) ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx)
      omega
    have hindices : Finset.Icc 0 ⌊x⌋₊ = Finset.Iic ⌊x⌋₊ := by
      ext i; simp
    have he : arithmeticSummatory w x = M (⌊x⌋₊ : ℝ) := by
      simp only [arithmeticSummatory, M, Nat.floor_natCast, hindices, w]
    rw [he, mul_one]
    exact (hM ⌊x⌋₊ hfloor).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0) hs) hC)
  have hab := reciprocal_density_tail_bound_of_real_profile w hw0 (fun _ => 1) 0
    hlim hC hs1 (fun _ _ => zero_le_one) (fun _ _ _ _ _ => le_rfl) hP hN
  simpa only [hrec, zero_sub, abs_neg, mul_one] using hab

end RiemannResearch.RH.Pareto
