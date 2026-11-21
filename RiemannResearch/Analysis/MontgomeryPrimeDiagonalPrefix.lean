/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalAbel
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.ClassicalStrongPNT
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeErrorStretched
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalScalar

/-! Squared von Mangoldt sums from the classical quantitative prime number theorem.
The arithmetic inputs are `ClassicalRegion.StrongPNT` and `mangoldtSquarePrefix_abel`.
The latter records the correction supported on higher prime powers. -/

open MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Real
open RiemannResearch.NumberTheory.PrimeNumberTheorem
noncomputable section
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel

private theorem exp_moment (c : ℝ) (hc : 0 < c) (j : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ u : ℝ, 0 ≤ u → u ^ j * Real.exp (-(c * u)) ≤ H := by
  refine ⟨(j.factorial : ℝ) / c ^ j, by positivity, ?_⟩
  intro u hu
  have h := Real.pow_div_factorial_le_exp (c * u) (mul_nonneg hc.le hu) j
  have h' := (div_le_iff₀ (by positivity : (0:ℝ) < j.factorial)).mp h
  rw [mul_pow] at h'
  rw [Real.exp_neg]
  apply (le_div_iff₀ (pow_pos hc j)).2
  have hm := mul_le_mul_of_nonneg_right h' (inv_nonneg.mpr (Real.exp_pos (c * u)).le)
  calc
    _ = (c ^ j * u ^ j) * (Real.exp (c * u))⁻¹ := by ring
    _ ≤ (Real.exp (c * u) * j.factorial) * (Real.exp (c * u))⁻¹ := hm
    _ = _ := by field_simp

private theorem psiRelative_int {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.psi t / t - 1) volume a b := by
  have hmono := Chebyshev.psi_mono.intervalIntegrable (μ := volume) (a := a) (b := b)
  have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc a b) := by
    exact continuousOn_id.inv₀ fun t ht => by
      rw [uIcc_of_le hab] at ht
      change t ≠ 0
      linarith [ht.1]
  simpa only [div_eq_mul_inv] using
    (hmono.mul_continuousOn hinv).sub (intervalIntegrable_const (a := a) (b := b))

private theorem psiRelative_strip {a b K : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Ioc a b, |Chebyshev.psi t / t - 1| ≤ K) :
    |∫ t in a..b, (Chebyshev.psi t / t - 1)| ≤ K * (b - a) := by
  simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using
    intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun t : ℝ => Chebyshev.psi t / t - 1) (C := K) (fun t ht => by
        rw [uIoc_of_le hab] at ht; simpa only [Real.norm_eq_abs] using h t ht)

private theorem psiRelative_eq (t : ℝ) (ht : 1 ≤ t) :
    |Chebyshev.psi t / t - 1| = |Chebyshev.psi t - t| / t := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  rw [show Chebyshev.psi t / t - 1 = (Chebyshev.psi t - t) / t by field_simp, abs_div, abs_of_pos ht0]

/-- The logarithmic endpoint factor is absorbed using the reserved square-log weight. -/
private theorem psiWeighted_exp :
    ∃ a > (0:ℝ), ∃ D > (0:ℝ), ∀ x : ℝ, 1 ≤ x →
      |Chebyshev.psi x - x| * (1 + Real.log x) ≤ D * x * Real.exp (-a * Real.sqrt (Real.log x)) := by
  obtain ⟨a,ha,D,hD,h⟩ := R_stretched_squareLog_bound_of_medium_rpow (1 / 2) (by norm_num)
    Quantitative.ClassicalRegion.StrongPNT
  refine ⟨a,ha,D,hD, ?_⟩
  intro x hx
  have hL := Real.log_nonneg hx
  have hd : 0 < 1 + Real.log x := by linarith
  have hm := (le_div_iff₀ (sq_pos_of_pos hd)).mp (h x hx)
  change |Chebyshev.psi x - x| * (1 + Real.log x) ^ 2 ≤ D * x * Real.exp (-a * (Real.log x) ^ (1 / 2:ℝ)) at hm
  rw [← Real.sqrt_eq_rpow] at hm
  refine (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)).trans hm
  nlinarith [sq_nonneg (Real.log x)]

private theorem prefix_error_identity {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n ^ 2) - (x * Real.log x - x + 1) =
      Real.log x * (Chebyshev.psi x - x) - (∫ t in (1:ℝ)..x, (Chebyshev.psi t / t - 1)) -
        mangoldtSquareCorrection x := by
  have hi := psiRelative_int (a := 1) (b := x) le_rfl hx
  have hic : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 1 x := intervalIntegrable_const
  have hadd := intervalIntegral.integral_add hi hic
  simp only [sub_add_cancel, intervalIntegral.integral_const, smul_eq_mul, mul_one] at hadd
  rw [mangoldtSquarePrefix_abel hx, ← intervalIntegral.integral_of_le hx, hadd]
  ring

/-- The classical quantitative PNT for the squared von Mangoldt prefix. -/
theorem mangoldtSquare_error_sqrtLog :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n ^ 2) - (x * Real.log x - x + 1)| ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨a,ha,D,hD,hPNT⟩ := psiWeighted_exp
  obtain ⟨K,hK,hKbound⟩ := mangoldtSquareCorrection_le_sqrt_log
  let c := a / 2
  have hc : 0 < c := half_pos ha
  let H := 5 * Real.exp (c ^ 2)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨c,hc,2 * D + (D + K) * H, by positivity, ?_⟩
  intro x hx
  let s := Real.sqrt x
  let w := Real.exp (-c * Real.sqrt (Real.log x))
  have hx1 : 1 ≤ x := by linarith
  have hp : 0 < x := by linarith
  have hL := Real.log_nonneg hx1
  have hs : 1 ≤ s := by dsimp [s]; simpa using Real.sqrt_le_sqrt hx1
  have hsp : 0 ≤ s := zero_le_one.trans hs
  have hsx : s ≤ x := by
    have hw := mul_nonneg hsp (sub_nonneg.mpr hs)
    dsimp [s] at hw ⊢
    nlinarith only [hw, Real.sq_sqrt hp.le]
  have hwp : 0 < w := Real.exp_pos _
  have he (t : ℝ) (ht : s ≤ t) : Real.exp (-a * Real.sqrt (Real.log t)) ≤ w := by
    exact diagonal_rootExp_mono_from_sqrt ha.le hx1 ht
  have hrelative (t : ℝ) (ht : 1 ≤ t) :
      |Chebyshev.psi t / t - 1| ≤ D * Real.exp (-a * Real.sqrt (Real.log t)) := by
    rw [psiRelative_eq t ht]
    apply (div_le_iff₀ (zero_lt_one.trans_le ht)).2
    have hE := hPNT t ht
    have hmono := le_mul_of_one_le_right (abs_nonneg (Chebyshev.psi t - t))
      (show 1 ≤ 1 + Real.log t by linarith [Real.log_nonneg ht])
    exact (hmono.trans hE).trans_eq (by ring)
  have h1 := psiRelative_strip hs (K := D) (fun t ht => by
    have he1 : Real.exp (-a * Real.sqrt (Real.log t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _))
    exact (hrelative t ht.1.le).trans (mul_le_of_le_one_right hD.le he1))
  have h2 := psiRelative_strip hsx (K := D * w) (fun t ht =>
    (hrelative t (hs.trans ht.1.le)).trans (mul_le_mul_of_nonneg_left (he t ht.1.le) hD.le))
  let J := ∫ t in (1:ℝ)..x, (Chebyshev.psi t / t - 1)
  have hI : |J| ≤ D * s + D * x * w := by
    dsimp only [J]
    rw [← intervalIntegral.integral_add_adjacent_intervals (psiRelative_int le_rfl hs)
      (psiRelative_int hs hsx)]
    refine (abs_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
    nlinarith only [hD.le, mul_nonneg (mul_nonneg hD.le hwp.le) hsp]
  have hendpoint : |Real.log x * (Chebyshev.psi x - x)| ≤ D * x * w := by
    rw [abs_mul, abs_of_nonneg hL, mul_comm (Real.log x)]
    have h1' := mul_le_mul_of_nonneg_left (show Real.log x ≤ 1 + Real.log x by linarith)
      (abs_nonneg (Chebyshev.psi x - x))
    exact (h1'.trans (hPNT x hx1)).trans (mul_le_mul_of_nonneg_left (he x hsx) (by positivity))
  have hcor := hKbound x hx1
  have hsmall : s * (1 + Real.log x) ≤ H * x * w := by
    exact diagonal_sqrt_mul_one_add_log_le_rootExp c hx1
  have hsplit : D * s + K * s * Real.log x ≤ (D + K) * (s * (1 + Real.log x)) := by
    nlinarith only [mul_nonneg (mul_nonneg hD.le hsp) hL, mul_nonneg hK hsp]
  have hrest := hsplit.trans (mul_le_mul_of_nonneg_left hsmall (add_nonneg hD.le hK))
  rw [prefix_error_identity hx1]
  change |Real.log x * (Chebyshev.psi x - x) - J - mangoldtSquareCorrection x| ≤
    (2 * D + (D + K) * H) * x * w
  calc
    _ ≤ |Real.log x * (Chebyshev.psi x - x)| + |J| + |mangoldtSquareCorrection x| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ D * x * w + (D * s + D * x * w) + K * s * Real.log x := by
      rw [abs_of_nonneg (mangoldtSquareCorrection_bound hx1).1]
      exact add_le_add (add_le_add hendpoint hI) hcor
    _ ≤ _ := by linarith only [hrest]

/-- Every fixed inverse-logarithmic error follows from the exponential estimate. -/
theorem mangoldtSquare_error_logPow (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ n ∈ Finset.Icc 0 ⌊x⌋₊, Λ n ^ 2) - (x * Real.log x - x + 1)| ≤ C * x / (Real.log x) ^ j := by
  obtain ⟨c,hc,B,hB,h⟩ := mangoldtSquare_error_sqrtLog
  obtain ⟨H,hH,hHbound⟩ := exp_moment c hc (2 * j)
  refine ⟨B * H, mul_nonneg hB hH, ?_⟩
  intro x hx
  have hp : 0 < x := by linarith
  have hL := Real.log_pos (by linarith : 1 < x)
  have hmoment := hHbound (Real.sqrt (Real.log x)) (Real.sqrt_nonneg _)
  rw [pow_mul, Real.sq_sqrt hL.le] at hmoment
  apply (le_div_iff₀ (pow_pos hL j)).2
  refine (mul_le_mul_of_nonneg_right (h x hx) (pow_nonneg hL.le j)).trans ?_
  calc
    _ = B * x * ((Real.log x) ^ j * Real.exp (-(c * Real.sqrt (Real.log x)))) := by rw [neg_mul]; ring
    _ ≤ B * x * H := mul_le_mul_of_nonneg_left hmoment (mul_nonneg hB hp.le)
    _ = _ := by ring

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
