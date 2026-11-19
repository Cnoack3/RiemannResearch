/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MontgomeryLogPhaseIntegral
import RiemannResearch.Analysis.MontgomeryLogMeanSquare
import RiemannResearch.Analysis.ZeroOrdinateEquidistribution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The actual prime cross integral in the corrected Montgomery formula

In BGSTB, §3, between (3.4) and (3.5), the signed A₁ times conjugate A₂
integral is expanded into logarithmically weighted prime phases. We justify
that expansion for the infinite von Mangoldt series. After division by x
the coefficients are dominated, uniformly in x, by Λ(n)/n^(3/2).
Absolute convergence on Re(s)=3/2 and the individual oscillatory estimate
give the O(log(T+2)) bound required in (3.5).
https://arxiv.org/html/2501.14545v3#S3.E4
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ArithmeticFunction
namespace RiemannResearch.Analysis.MontgomeryPrimeCrossIntegral
open ZeroOrdinate MontgomeryLogPhaseIntegral

def mangoldtThreeHalves (n : ℕ) : ℝ := Λ n / (n : ℝ) ^ (3 / 2 : ℝ)

private theorem weight_nonneg (n : ℕ) : 0 ≤ mangoldtThreeHalves n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem summable_mangoldtThreeHalves : Summable mangoldtThreeHalves := by
  let s : ℂ := ((3 / 2 : ℝ) : ℂ)
  have hs : LSeriesSummable (fun n => (Λ n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by dsimp [s]; norm_num)
  refine (summable_norm_iff.mpr hs).congr fun n => ?_
  rw [LSeries.norm_term_eq]
  by_cases hz : n = 0
  · subst n
    simp [mangoldtThreeHalves]
  · simp [hz, s, mangoldtThreeHalves, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- Real von Mangoldt coefficient in the conjugated Dirichlet series A₂. -/
def primeWeight (x : ℝ) (n : ℕ) : ℝ :=
  Λ n / Real.sqrt n * min ((n : ℝ) / x) (x / (n : ℝ))

private def crossWeight (x : ℝ) (n : ℕ) : ℝ := primeWeight x n / x

private theorem crossWeight_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 ≤ crossWeight x n :=
  div_nonneg (mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (le_min (div_nonneg (Nat.cast_nonneg _) hx.le) (div_nonneg hx.le (Nat.cast_nonneg _)))) hx.le

private theorem crossWeight_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    crossWeight x n ≤ mangoldtThreeHalves n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [crossWeight, primeWeight, mangoldtThreeHalves]
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hp : (n : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt n * n := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add hn0,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  calc
    crossWeight x n ≤ (Λ n / Real.sqrt n * (x / (n : ℝ))) / x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_right _ _)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))) hx.le
    _ = mangoldtThreeHalves n := by
      rw [mangoldtThreeHalves, hp]
      field_simp [hx.ne', hn0.ne', (Real.sqrt_pos.2 hn0).ne']
      <;> ring

/-- A bound in the normalization used by the squared prime signal. -/
theorem primeWeight_le_mangoldtThreeHalves {x : ℝ} (hx : 0 < x) (n : ℕ) :
    primeWeight x n ≤ x*mangoldtThreeHalves n := by
  simpa only [mul_comm] using (div_le_iff₀ hx).mp (crossWeight_le hx n)

theorem primeWeight_nonneg {x : ℝ} (hx : 0 < x) (n : ℕ) : 0 ≤ primeWeight x n :=
  mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (le_min (div_nonneg (Nat.cast_nonneg _) hx.le) (div_nonneg hx.le (Nat.cast_nonneg _)))

/-- The cross integral written with the positive phases in conjugate A₂.
For T ≥ 0 the logarithmic factor is exactly A₁ on its interval of integration. -/
def crossIntegral (x T : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..T, ((Real.log (t + 2) / x : ℝ) : ℂ) *
    (-(∑' n : ℕ, (primeWeight x n : ℂ) * phase (Real.log n) t))

/-- Exact signed series for the actual cross integral, including every prime power. -/
theorem crossIntegral_eq_series {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    crossIntegral x T = -(∑' n : ℕ, ((primeWeight x n / x : ℝ) : ℂ) *
      ∫ t in (0 : ℝ)..T, (Real.log (t + 2) : ℂ) * phase (Real.log n) t) := by
  let b := fun t : ℝ => (Real.log (t + 2) : ℂ)
  let term := fun (n : ℕ) (t : ℝ) => (crossWeight x n : ℂ) * (b t * phase (Real.log n) t)
  have hb : ContinuousOn b (uIcc 0 T) :=
    Complex.continuous_ofReal.comp_continuousOn (MontgomeryLogMeanSquare.shifted_log_continuousOn hT)
  have hint (n : ℕ) : IntegrableOn (term n) (Ioc 0 T) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul (hb.mul (by unfold phase; fun_prop))
  have hc : Summable (crossWeight x) := Summable.of_nonneg_of_le
    (crossWeight_nonneg hx) (crossWeight_le hx) summable_mangoldtThreeHalves
  have hnrm (n : ℕ) :
      (∫ t in Ioc (0 : ℝ) T, ‖term n t‖) = crossWeight x n * ∫ t in Ioc (0 : ℝ) T, ‖b t‖ := by
    simp only [term, norm_mul, phase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (crossWeight_nonneg hx n), integral_const_mul]
  have hsum : Summable (fun n => ∫ t in Ioc (0 : ℝ) T, ‖term n t‖) := by
    simp only [hnrm]
    exact hc.mul_right _
  have hswap : (∫ t in Ioc (0 : ℝ) T, ∑' n, term n t) =
      ∑' n, ∫ t in Ioc (0 : ℝ) T, term n t := by
    exact (integral_tsum_of_summable_integral_norm hint hsum).symm
  have he (t : ℝ) : ((Real.log (t + 2) / x : ℝ) : ℂ) *
      (-(∑' n : ℕ, (primeWeight x n : ℂ) * phase (Real.log n) t)) = -(∑' n, term n t) := by
    rw [mul_neg, ← tsum_mul_left]
    congr 1
    apply tsum_congr
    intro n
    simp only [term, b, crossWeight, Complex.ofReal_div]
    ring
  unfold crossIntegral
  simp_rw [he, intervalIntegral.integral_of_le hT]
  rw [integral_neg, hswap]
  congr 1
  apply tsum_congr
  intro n
  exact integral_const_mul _ _

/-- Uniform O(log(T+2)) estimate for the infinite mixed prime term, with an
explicit constant given by an absolutely convergent von Mangoldt sum. -/
theorem norm_crossIntegral_le {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    ‖crossIntegral x T‖ ≤ (2 * Real.log (T + 2) / Real.log 2) *
      ∑' n : ℕ, mangoldtThreeHalves n := by
  let J := fun n : ℕ => ∫ t in (0 : ℝ)..T, (Real.log (t + 2) : ℂ) * phase (Real.log n) t
  let K := 2 * Real.log (T + 2) / Real.log 2
  let a := fun n : ℕ => (crossWeight x n : ℂ) * J n
  have hl : 0 ≤ 2 * Real.log (T + 2) := mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmajor (n : ℕ) : ‖a n‖ ≤ K * mangoldtThreeHalves n := by
    by_cases hn : 2 ≤ n
    · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hfreq : 1 < (n : ℝ) := by linarith
      have hJ : ‖J n‖ ≤ K := (norm_log_phase_integral_le hfreq hT).trans
        (div_le_div_of_nonneg_left hl h2 (Real.log_le_log (by norm_num) hn2))
      calc
        ‖a n‖ = crossWeight x n * ‖J n‖ := by
          simp [a, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (crossWeight_nonneg hx n)]
        _ ≤ mangoldtThreeHalves n * K :=
          mul_le_mul (crossWeight_le hx n) hJ (norm_nonneg _) (weight_nonneg n)
        _ = _ := mul_comm _ _
    · have hh : n = 0 ∨ n = 1 := by omega
      rcases hh with rfl | rfl <;> simp [a, crossWeight, primeWeight, mangoldtThreeHalves]
  have hws := summable_mangoldtThreeHalves.mul_left K
  have has := Summable.of_nonneg_of_le (fun n => norm_nonneg (a n)) hmajor hws
  rw [crossIntegral_eq_series hx hT, norm_neg]
  change ‖∑' n, a n‖ ≤ K * ∑' n, mangoldtThreeHalves n
  exact (norm_tsum_le_tsum_norm has).trans ((has.tsum_le_tsum hmajor hws).trans_eq tsum_mul_left)

end RiemannResearch.Analysis.MontgomeryPrimeCrossIntegral
