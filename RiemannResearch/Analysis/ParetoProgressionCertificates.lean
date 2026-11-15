/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ArithmeticProgressionSquareSeries
import RiemannResearch.Analysis.InverseSquareTailCertificates
import RiemannResearch.RH.ParetoProgressionTails
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import RiemannResearch.Analysis.LogRationalCertificates
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Complete Pareto progression certificates

The Pareto kernel is the unit-interval integral of the inverse-square kernel.
Consequently the exact complete inverse-square tail enclosures integrate to
complete Pareto tail enclosures. This is an analytic bridge to the actual
infinite sums, with no numerical remainder assumption.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set intervalIntegral

namespace RiemannResearch.Analysis.ParetoProgressionCertificates
open InverseSquareTailCertificates

private theorem square_summable (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    Summable (fun n : ℕ => 1 / (a + L * (n : ℝ)) ^ 2) := by
  simpa only [mul_comm] using
    ArithmeticProgressionSquareTail.full_progression_summable a L ha hL

/-- The inverse-square progression, shifted continuously by `s`. -/
def squareProgression (a L s : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (a + L * (n : ℝ) + s) ^ 2

/-- The complete Pareto progression with real initial point and spacing. -/
def paretoProgression (a L : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / ((a + L * (n : ℝ)) * (a + L * (n : ℝ) + 1))

private theorem integral_unit_eq_Ioo (f : ℝ → ℝ) :
    (∫ s : ℝ in 0..1, f s) = ∫ s in Ioo (0 : ℝ) 1, f s := by
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- Every reciprocal power is integrable on the positive shifted unit interval. -/
theorem inversePower_intervalIntegrable (a : ℝ) (ha : 0 < a) (k : ℕ) :
    IntervalIntegrable (fun s : ℝ => (1 / (a + s)) ^ k) volume 0 1 := by
  have hc : ContinuousOn (fun s : ℝ => (1 / (a + s)) ^ k) (Icc 0 1) := by
    apply ContinuousOn.pow
    apply continuousOn_const.div (continuousOn_const.add continuousOn_id)
    intro s hs
    change a + s ≠ 0
    exact ne_of_gt (by linarith [hs.1])
  exact hc.intervalIntegrable_of_Icc zero_le_one

/-- Exact primitive evaluation for every positive reciprocal power above one. -/
theorem integral_inversePower_succ (a : ℝ) (ha : 0 < a) (k : ℕ) (hk : 0 < k) :
    (∫ s : ℝ in 0..1, (1 / (a + s)) ^ (k + 1)) =
      ((1 / a) ^ k - (1 / (a + 1)) ^ k) / (k : ℝ) := by
  rw [intervalIntegral.integral_comp_add_left (fun x : ℝ => (1/x)^(k+1)) a]
  simp only [add_zero]
  have hz : (0 : ℝ) ∉ uIcc a (a + 1) := by
    rw [uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have he : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by ring
  have h := integral_zpow (a := a) (b := a + 1) (n := -(k : ℤ) - 1)
    (Or.inr ⟨by omega, hz⟩)
  have hf : (fun x : ℝ => (1 / x) ^ (k + 1)) =
      (fun x : ℝ => x ^ (-(k : ℤ) - 1)) := by
    funext x
    have he' : -(k : ℤ)-1 = -((k+1 : ℕ) : ℤ) := by omega
    calc
      (1/x)^(k+1) = (x^((k+1 : ℕ) : ℤ))⁻¹ := by
        simp only [one_div, inv_pow, zpow_natCast]
      _ = x^(-((k+1 : ℕ) : ℤ)) := (zpow_neg x ((k+1 : ℕ) : ℤ)).symm
      _ = x^(-(k : ℤ)-1) := congrArg (fun e : ℤ => x^e) he'.symm

  rw [hf, h, he]
  push_cast
  simp only [zpow_neg, zpow_natCast, one_div, inv_pow, div_neg]
  <;> ring

/-- The first reciprocal power has the exact logarithmic primitive. -/
theorem integral_inversePower_one (a : ℝ) (ha : 0 < a) :
    (∫ s : ℝ in 0..1, 1 / (a + s)) = Real.log ((a + 1) / a) := by
  rw [intervalIntegral.integral_comp_add_left (fun x : ℝ => 1/x) a]
  simpa only [add_zero] using integral_one_div_of_pos ha (by linarith : 0 < a + 1)

private theorem integral_square_kernel (a : ℝ) (ha : 0 < a) :
    (∫ s : ℝ in 0..1, 1 / (a + s) ^ 2) = 1 / (a * (a + 1)) := by
  have h := integral_inversePower_succ a ha 1 (by decide)
  simp only [one_div_pow, pow_one, Nat.cast_one, div_one] at h
  rw [h]
  field_simp
  <;> ring

/-- The real Pareto progression converges by comparison with inverse squares. -/
theorem paretoProgression_summable (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    Summable (fun n : ℕ => 1 / ((a + L * (n : ℝ)) *
      (a + L * (n : ℝ) + 1))) := by
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _
    (square_summable a L ha hL)
  intro n
  apply one_div_le_one_div_of_le (sq_pos_of_pos (by positivity))
  nlinarith [show 0 < a + L * (n : ℝ) by positivity]

/-- The complete inverse-square progression is integrable in its unit shift. -/
theorem squareProgression_integrableOn (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    IntegrableOn (squareProgression a L) (Ioo (0 : ℝ) 1) := by
  have hm : Measurable (squareProgression a L) := by
    unfold squareProgression
    exact Measurable.tsum (fun n => by fun_prop)
  apply (integrable_const (squareProgression a L 0)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have hsum : Summable (fun n : ℕ => 1 / (a + L * (n : ℝ) + s) ^ 2) := by
    simpa only [add_right_comm] using
      square_summable (a + s) L (by linarith [hs.1]) hL
  have hsum0 : Summable (fun n : ℕ => 1 / (a + L * (n : ℝ) + 0) ^ 2) := by
    simpa only [add_zero] using square_summable a L ha hL
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => by positivity))]
  apply Summable.tsum_le_tsum _ hsum hsum0
  intro n
  simp only [add_zero]
  apply one_div_le_one_div_of_le (sq_pos_of_pos (by positivity))
  nlinarith [show 0 < a + L * (n : ℝ) by positivity, hs.1]

/-- Exact identity connecting the actual complete Pareto and inverse-square sums. -/
theorem paretoProgression_eq_integral_squareProgression (a L : ℝ)
    (ha : 0 < a) (hL : 0 < L) :
    paretoProgression a L = ∫ s : ℝ in 0..1, squareProgression a L s := by
  let F : ℕ → ℝ → ℝ := fun n s => 1 / (a + L * (n : ℝ) + s) ^ 2
  have hint (n : ℕ) : IntegrableOn (F n) (Ioo (0 : ℝ) 1) := by
    have h := inversePower_intervalIntegrable (a + L * (n : ℝ)) (by positivity) 2
    simp only [one_div_pow] at h
    exact h.1.mono_set Ioo_subset_Ioc_self
  have hmass (n : ℕ) : (∫ s in Ioo (0 : ℝ) 1, F n s) =
      1 / ((a + L * (n : ℝ)) * (a + L * (n : ℝ) + 1)) := by
    rw [← integral_unit_eq_Ioo]
    exact integral_square_kernel _ (by positivity)
  have hnorm (n : ℕ) : (∫ s in Ioo (0 : ℝ) 1, ‖F n s‖) =
      1 / ((a + L * (n : ℝ)) * (a + L * (n : ℝ) + 1)) := by
    rw [← hmass n]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro s hs
    change ‖F n s‖ = F n s
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (by dsimp [F]; positivity)
  have hsum : Summable (fun n : ℕ => ∫ s in Ioo (0 : ℝ) 1, ‖F n s‖) := by
    simp_rw [hnorm]
    exact paretoProgression_summable a L ha hL
  rw [integral_unit_eq_Ioo]
  calc
    paretoProgression a L = ∑' n : ℕ, ∫ s in Ioo (0 : ℝ) 1, F n s := by
      unfold paretoProgression
      simp_rw [hmass]
    _ = ∫ s in Ioo (0 : ℝ) 1, ∑' n : ℕ, F n s :=
      integral_tsum_of_summable_integral_norm hint hsum

/-- Generic enclosure transfer. Its hypotheses are ordinary integrability and
pointwise bounds; the middle term is the complete actual Pareto progression. -/
theorem integral_enclosure (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (lo hi : ℝ → ℝ) (hlo : IntegrableOn lo (Ioo (0 : ℝ) 1))
    (hhi : IntegrableOn hi (Ioo (0 : ℝ) 1))
    (hbound : ∀ s ∈ Ioo (0 : ℝ) 1,
      lo s ≤ squareProgression a L s ∧ squareProgression a L s ≤ hi s) :
    (∫ s : ℝ in 0..1, lo s) ≤ paretoProgression a L ∧
      paretoProgression a L ≤ ∫ s : ℝ in 0..1, hi s := by
  rw [paretoProgression_eq_integral_squareProgression a L ha hL]
  simp only [integral_unit_eq_Ioo]
  have hmid := squareProgression_integrableOn a L ha hL
  constructor
  · exact integral_mono_ae hlo hmid (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (hbound s hs).1)
  · exact integral_mono_ae hmid hhi (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact (hbound s hs).2)

/-- Identification with the repository's natural-number progression masses. -/
theorem paretoProgression_eq_progressionWeight (N r : ℕ) :
    paretoProgression (r : ℝ) (N : ℝ) =
      RiemannResearch.RH.Pareto.progressionWeight N r := by
  unfold paretoProgression RiemannResearch.RH.Pareto.progressionWeight
  apply tsum_congr
  intro n
  simp only [RiemannResearch.RH.Pareto.positiveWeight, Nat.cast_add, Nat.cast_mul]


/-- The exact Bernoulli coefficients used in the archived ten-correction table. -/
def correctionCoefficient {𝕜 : Type*} [Field 𝕜] : ℕ → 𝕜
  | 0 => 1/6
  | 1 => -1/30
  | 2 => 1/42
  | 3 => -1/30
  | 4 => 5/66
  | 5 => -691/2730
  | 6 => 7/6
  | 7 => -3617/510
  | 8 => 43867/798
  | 9 => -174611/330
  | _ => 0

/-- A finite rational inverse-square tail expression, with the initial integral
and endpoint terms and every indicated signed correction retained. -/
def squareApprox {𝕜 : Type*} [Field 𝕜] (N : ℕ) (a L : 𝕜) : 𝕜 :=
  (1/L) * (1/a) + (1/a)^2/2 +
    ∑ j ∈ Finset.range N,
      (correctionCoefficient j * L^(2*j+1)) * (1/a)^((2*j+2)+1)

/-- The exact unit integral of `squareApprox`, including its logarithm. -/
def paretoApprox (N : ℕ) (a L : ℝ) : ℝ :=
  (1/L) * Real.log ((a+1)/a) + (1/a - 1/(a+1))/2 +
    ∑ j ∈ Finset.range N,
      (correctionCoefficient j * L^(2*j+1)) *
        (((1/a)^(2*j+2) - (1/(a+1))^(2*j+2)) / (2*j+2 : ℕ))

theorem squareApprox_nine_eq_scaled (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    squareApprox 9 a L = upperNine (a/L) / L^2 := by
  norm_num [squareApprox, upperNine, Finset.sum_range_succ, correctionCoefficient]
  field_simp
  <;> ring

theorem squareApprox_ten_eq_scaled (a L : ℝ) (ha : 0 < a) (hL : 0 < L) :
    squareApprox 10 a L = lowerTen (a/L) / L^2 := by
  norm_num [squareApprox, lowerTen, upperNine, Finset.sum_range_succ,
    correctionCoefficient]
  field_simp
  <;> ring

theorem squareApprox_intervalIntegrable (N : ℕ) (a L : ℝ) (ha : 0 < a) :
    IntervalIntegrable (fun s : ℝ => squareApprox N (a+s) L) volume 0 1 := by
  have h (k : ℕ) := inversePower_intervalIntegrable a ha k
  have h1 : IntervalIntegrable (fun s : ℝ => 1/(a+s)) volume 0 1 := by
    simpa only [pow_one] using h 1
  simpa only [squareApprox, Finset.sum_apply] using
    ((h1.const_mul (1/L)).add ((h 2).div_const 2)).add
      (IntervalIntegrable.sum (Finset.range N) (fun j _ =>
        (h ((2*j+2)+1)).const_mul (correctionCoefficient j * L^(2*j+1))))

/-- Evaluating the analytic bridge gives exactly the logarithmic and rational
expression used for the complete Pareto tails in the archived computation. -/
theorem integral_squareApprox (N : ℕ) (a L : ℝ) (ha : 0 < a) :
    (∫ s : ℝ in 0..1, squareApprox N (a+s) L) = paretoApprox N a L := by
  have h (k : ℕ) := inversePower_intervalIntegrable a ha k
  have h1 : IntervalIntegrable (fun s : ℝ => 1/(a+s)) volume 0 1 := by
    simpa only [pow_one] using h 1
  have hi (j : ℕ) : IntervalIntegrable
      (fun s : ℝ => (correctionCoefficient j * L^(2*j+1)) *
        (1/(a+s))^((2*j+2)+1)) volume 0 1 :=
    (h _).const_mul _
  have hiSum : IntervalIntegrable (fun s : ℝ => ∑ j ∈ Finset.range N,
      (correctionCoefficient j * L^(2*j+1)) * (1/(a+s))^((2*j+2)+1)) volume 0 1 := by
    have he : (fun s : ℝ => ∑ j ∈ Finset.range N,
        (correctionCoefficient j * L^(2*j+1)) * (1/(a+s))^((2*j+2)+1)) =
        ∑ j ∈ Finset.range N, (fun s : ℝ =>
          (correctionCoefficient j * L^(2*j+1)) * (1/(a+s))^((2*j+2)+1)) := by
      funext s
      simp only [Finset.sum_apply]
    rw [he]
    exact IntervalIntegrable.sum (Finset.range N) (fun j _ => hi j)
  unfold squareApprox paretoApprox
  rw [intervalIntegral.integral_add
    ((h1.const_mul (1/L)).add ((h 2).div_const 2)) hiSum]
  rw [intervalIntegral.integral_add (h1.const_mul (1/L)) ((h 2).div_const 2)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    integral_inversePower_one a ha, integral_inversePower_succ a ha 1 (by decide)]
  simp only [pow_one, Nat.cast_one, div_one]
  congr 1
  have hsumint := intervalIntegral.integral_finsetSum (s := Finset.range N)
    (f := fun j s => (correctionCoefficient j * L^(2*j+1)) *
      (1/(a+s))^((2*j+2)+1)) (fun j _ => hi j)
  rw [hsumint]
  apply Finset.sum_congr rfl
  intro j hj
  rw [intervalIntegral.integral_const_mul,
    integral_inversePower_succ a ha (2*j+2) (by omega)]

/-- Sharp complete P bounds obtained by integrating the nine- and ten-correction
Q bounds. There is no Euler--Maclaurin oracle or unbounded omitted tail. -/
theorem complete_tail_ten_bounds (a L : ℝ) (hL : 0 < L) (ha : L ≤ a) :
    paretoApprox 10 a L ≤ paretoProgression a L ∧
      paretoProgression a L ≤ paretoApprox 9 a L := by
  have ha0 : 0 < a := lt_of_lt_of_le hL ha
  have hpoint : ∀ s ∈ Ioo (0 : ℝ) 1,
      squareApprox 10 (a+s) L ≤ squareProgression a L s ∧
        squareProgression a L s ≤ squareApprox 9 (a+s) L := by
    intro s hs
    have hx : 1 ≤ (a+s)/L := (le_div_iff₀ hL).2 (by linarith [hs.1])
    have h := scaled_complete_tail_ten_bounds ((a+s)/L) L hx hL
    have he : (∑' n : ℕ, 1/(L*((a+s)/L)+(n:ℝ)*L)^2) =
        squareProgression a L s := by
      apply tsum_congr
      intro n
      congr 2
      field_simp
      <;> ring
    rw [he] at h
    rw [squareApprox_ten_eq_scaled (a+s) L (by linarith [hs.1]) hL,
      squareApprox_nine_eq_scaled (a+s) L (by linarith [hs.1]) hL]
    exact h
  have hb := integral_enclosure a L ha0 hL
    (fun s => squareApprox 10 (a+s) L) (fun s => squareApprox 9 (a+s) L)
    ((squareApprox_intervalIntegrable 10 a L ha0).1.mono_set Ioo_subset_Ioc_self)
    ((squareApprox_intervalIntegrable 9 a L ha0).1.mono_set Ioo_subset_Ioc_self) hpoint
  rw [integral_squareApprox 10 a L ha0, integral_squareApprox 9 a L ha0] at hb
  exact hb

/-- Exact finite-prefix and complete-tail decomposition for P progressions. -/
theorem prefix_tail_identity (a L : ℝ) (ha : 0 < a) (hL : 0 < L) (K : ℕ) :
    paretoProgression a L =
      (∑ n ∈ Finset.range K, 1/((a+L*(n:ℝ))*(a+L*(n:ℝ)+1))) +
        paretoProgression (a+L*(K:ℝ)) L := by
  have h := (paretoProgression_summable a L ha hL).sum_add_tsum_nat_add K
  unfold paretoProgression
  rw [← h]
  congr 1
  apply tsum_congr
  intro n
  congr 2 <;> push_cast <;> ring

/-- Every finite-prefix certificate encloses the actual complete P progression. -/
theorem prefix_tail_ten_bounds (a L : ℝ) (ha : 0 < a) (hL : 0 < L)
    (K : ℕ) (hK : L ≤ a + L*(K:ℝ)) :
    (∑ n ∈ Finset.range K, 1/((a+L*(n:ℝ))*(a+L*(n:ℝ)+1))) +
        paretoApprox 10 (a+L*(K:ℝ)) L ≤ paretoProgression a L ∧
      paretoProgression a L ≤
        (∑ n ∈ Finset.range K, 1/((a+L*(n:ℝ))*(a+L*(n:ℝ)+1))) +
          paretoApprox 9 (a+L*(K:ℝ)) L := by
  have h := complete_tail_ten_bounds (a+L*(K:ℝ)) L hL hK
  rw [prefix_tail_identity a L ha hL K]
  constructor <;> linarith [h.1, h.2]

end RiemannResearch.Analysis.ParetoProgressionCertificates

/-! Computable rational intervals for the actual complete Pareto progressions. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.ParetoProgressionCertificates
open RiemannResearch RatInterval LogRationalCertificates

/-- The signed rational part of a Pareto tail, separated from its logarithm. -/
def paretoRationalPart {𝕜 : Type*} [Field 𝕜] (N : ℕ) (a L : 𝕜) : 𝕜 :=
  (1/a - 1/(a+1))/2 +
    ∑ j ∈ Finset.range N,
      (correctionCoefficient j * L^(2*j+1)) *
        (((1/a)^(2*j+2) - (1/(a+1))^(2*j+2)) / (2*j+2 : ℕ))

theorem paretoApprox_eq_log_add_rationalPart (N : ℕ) (a L : ℝ) :
    paretoApprox N a L =
      (1/L)*Real.log ((a+1)/a) + paretoRationalPart N a L := by
  unfold paretoApprox paretoRationalPart
  ring

private theorem paretoRationalPart_nine_cast (a L : ℚ) :
    ((paretoRationalPart 9 a L : ℚ) : ℝ) =
      paretoRationalPart 9 (a : ℝ) (L : ℝ) := by
  norm_num [paretoRationalPart, Finset.sum_range_succ, correctionCoefficient]

private theorem paretoRationalPart_ten_cast (a L : ℚ) :
    ((paretoRationalPart 10 a L : ℚ) : ℝ) =
      paretoRationalPart 10 (a : ℝ) (L : ℝ) := by
  norm_num [paretoRationalPart, Finset.sum_range_succ, correctionCoefficient]

/-- A finite rational expression enclosing every omitted physical P atom.
The twelve-term positive logarithm series and all ten signed rational
corrections are retained in the lower endpoint. -/
def paretoProgressionInterval (a L : ℚ) (K : ℕ) : RatInterval :=
  let x := a + L*(K : ℚ)
  let P : ℚ := ∑ n ∈ Finset.range K,
    1/((a+L*(n : ℚ))*(a+L*(n : ℚ)+1))
  let J := logOnePlusInvInterval x 12
  ⟨P+(1/L)*J.lo+paretoRationalPart 10 x L,
   P+(1/L)*J.hi+paretoRationalPart 9 x L⟩

theorem paretoProgressionInterval_contains (a L : ℚ) (K : ℕ)
    (ha : 0 < a) (hL : 0 < L) (hK : 1 ≤ K) :
    (paretoProgressionInterval a L K).Contains
      (paretoProgression (a : ℝ) (L : ℝ)) := by
  have har : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hLr : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hKr : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hx : (0 : ℚ) < a+L*(K : ℚ) := by positivity
  have hlog := logOnePlusInvInterval_contains (a+L*(K : ℚ)) hx 12
  have hl := mul_le_mul_of_nonneg_left hlog.1
    (show (0 : ℝ) ≤ 1/(L : ℝ) by positivity)
  have hu := mul_le_mul_of_nonneg_left hlog.2
    (show (0 : ℝ) ≤ 1/(L : ℝ) by positivity)
  have hb := prefix_tail_ten_bounds (a : ℝ) (L : ℝ) har hLr K (by
    nlinarith)
  change _ ≤ _ ∧ _ ≤ _
  dsimp only [paretoProgressionInterval]
  push_cast
  rw [paretoRationalPart_ten_cast, paretoRationalPart_nine_cast]
  push_cast at hl hu ⊢
  change _ ≤ _ ∧ _ ≤ _ at hb
  simp only [paretoApprox_eq_log_add_rationalPart] at hb
  constructor <;> linarith [hb.1, hb.2]

end RiemannResearch.Analysis.ParetoProgressionCertificates
