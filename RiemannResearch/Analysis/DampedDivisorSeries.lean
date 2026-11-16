/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.DivisorPolynomialMoment
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual damped divisor series and justified L2 limits

The coefficients are the actual divisor coefficients from
`DivisorPolynomialMoment`. For every positive damping scale, the finite
polynomials converge uniformly for all real heights. An exact signed tail
identity precedes the geometric majorant and its interval L2 consequence.
Second moments also converge after subtraction of any continuous function,
so a fixed finite head may be retained during passage to the infinite tail.

Source: elementary Weierstrass majorization and dominated convergence, as
formalized in Mathlib's FunctionSeries and DominatedConvergence modules.
The intended consumer is the damped-tail obligation in
THEOREM_CATALOG_INGHAM_DYADIC_L2_20261116.md. This module does not supply
Mellin inversion, contour shifts, or a scale-uniform actual-zeta residual bound.
-/

noncomputable section
open MeasureTheory Complex Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis

/-- The `(n+1)`st actual damped critical-line divisor term; the index avoids zero. -/
def dampedDivisorTerm (Y : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  ((Real.exp (-((n + 1 : ℕ) : ℝ) / Y) : ℂ) * criticalDivisorCoefficient (n + 1)) *
    Complex.exp (Complex.I * t * (-Real.log (n + 1 : ℕ)))

/-- A height-independent, summable geometric majorant when `Y > 0`. -/
def dampedDivisorMajorant (Y : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ) / Y)

/-- The actual infinite damped divisor series, using the same terms as the finite polynomial. -/
def dampedDivisorSeries (Y t : ℝ) : ℂ := ∑' n, dampedDivisorTerm Y n t

/-- The complete scalar majorant after cutoff `N`. Its closed form is proved below. -/
def dampedDivisorTailBudget (Y : ℝ) (N : ℕ) : ℝ :=
  ∑' n, dampedDivisorMajorant Y (n + N)

theorem continuous_dampedDivisorTerm (Y : ℝ) (n : ℕ) :
    Continuous (dampedDivisorTerm Y n) := by
  unfold dampedDivisorTerm
  fun_prop

theorem norm_dampedDivisorTerm_le (Y : ℝ) (n : ℕ) (t : ℝ) :
    ‖dampedDivisorTerm Y n t‖ ≤ dampedDivisorMajorant Y n := by
  have hp : ‖Complex.exp (Complex.I * t * (-Real.log (n + 1 : ℕ)))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  unfold dampedDivisorTerm dampedDivisorMajorant
  rw [norm_mul, norm_mul, hp, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (criticalDivisorCoefficient_norm_le (n + 1))
    (Real.exp_pos (-((n + 1 : ℕ) : ℝ) / Y)).le

theorem dampedDivisorMajorant_nonneg (Y : ℝ) (n : ℕ) :
    0 ≤ dampedDivisorMajorant Y n := by
  unfold dampedDivisorMajorant
  positivity

theorem summable_dampedDivisorMajorant {Y : ℝ} (hY : 0 < Y) :
    Summable (dampedDivisorMajorant Y) := by
  have hr : ‖Real.exp (-1 / Y)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hY)
  have hs : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-1 / Y) ^ n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have he (n : ℕ) : Real.exp (-((n + 1 : ℕ) : ℝ) / Y) =
      Real.exp (-1 / Y) ^ (n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  change Summable (fun n => ((n + 1 : ℕ) : ℝ) * Real.exp (-((n + 1 : ℕ) : ℝ) / Y))
  simp_rw [he]
  exact (summable_nat_add_iff 1).mpr hs

theorem summable_norm_dampedDivisorTerm {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    Summable (fun n => ‖dampedDivisorTerm Y n t‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_dampedDivisorTerm_le Y n t)
    (summable_dampedDivisorMajorant hY)

theorem divisorPolynomial_eq_sum_dampedDivisorTerm (N : ℕ) (Y t : ℝ) :
    divisorPolynomial N (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t =
      ∑ n ∈ Finset.range N, dampedDivisorTerm Y n t := by
  induction N with
  | zero => simp [divisorPolynomial]
  | succ N ih =>
    unfold divisorPolynomial at *
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
    rfl

/-- Convergence is uniform on the entire real height axis for fixed positive damping. -/
theorem tendstoUniformly_damped_divisorPolynomial {Y : ℝ} (hY : 0 < Y) :
    TendstoUniformly
      (fun N => divisorPolynomial N (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)))
      (dampedDivisorSeries Y) atTop := by
  change TendstoUniformly
    (fun N t => divisorPolynomial N (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t)
    (fun t => ∑' n, dampedDivisorTerm Y n t) atTop
  simp_rw [divisorPolynomial_eq_sum_dampedDivisorTerm]
  exact tendstoUniformly_tsum_nat (summable_dampedDivisorMajorant hY)
    (norm_dampedDivisorTerm_le Y)

theorem continuous_dampedDivisorSeries {Y : ℝ} (hY : 0 < Y) :
    Continuous (dampedDivisorSeries Y) :=
  continuous_tsum (continuous_dampedDivisorTerm Y) (summable_dampedDivisorMajorant hY)
    (norm_dampedDivisorTerm_le Y)

/-- Exact signed tail, before taking norms. -/
theorem dampedDivisorSeries_sub_polynomial_eq_tsum {Y : ℝ} (hY : 0 < Y)
    (N : ℕ) (t : ℝ) :
    dampedDivisorSeries Y t -
      divisorPolynomial N (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t =
      ∑' n, dampedDivisorTerm Y (n + N) t := by
  have hs := (summable_norm_dampedDivisorTerm hY t).of_norm
  have he := hs.sum_add_tsum_nat_add N
  rw [divisorPolynomial_eq_sum_dampedDivisorTerm]
  unfold dampedDivisorSeries
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he.symm)

theorem norm_dampedDivisorSeries_sub_polynomial_le {Y : ℝ} (hY : 0 < Y)
    (N : ℕ) (t : ℝ) :
    ‖dampedDivisorSeries Y t -
      divisorPolynomial N (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t‖ ≤
      dampedDivisorTailBudget Y N := by
  rw [dampedDivisorSeries_sub_polynomial_eq_tsum hY]
  have hn : Summable (fun n => ‖dampedDivisorTerm Y (n + N) t‖) :=
    (summable_nat_add_iff N).mpr (summable_norm_dampedDivisorTerm hY t)
  have hm : Summable (fun n => dampedDivisorMajorant Y (n + N)) :=
    (summable_nat_add_iff N).mpr (summable_dampedDivisorMajorant hY)
  calc
    _ ≤ ∑' n, ‖dampedDivisorTerm Y (n + N) t‖ := norm_tsum_le_tsum_norm hn
    _ ≤ _ := Summable.tsum_le_tsum (fun n => norm_dampedDivisorTerm_le Y (n + N) t) hn hm

theorem dampedDivisorTailBudget_nonneg (Y : ℝ) (N : ℕ) :
    0 ≤ dampedDivisorTailBudget Y N :=
  tsum_nonneg (fun n => dampedDivisorMajorant_nonneg Y (n + N))

theorem tendsto_dampedDivisorTailBudget (Y : ℝ) :
    Tendsto (dampedDivisorTailBudget Y) atTop (𝓝 0) :=
  tendsto_sum_nat_add (dampedDivisorMajorant Y)

/-- An explicit interval L2 error bound, valid for every cutoff including zero. -/
theorem integral_dampedDivisor_tail_sq_le {Y H T : ℝ} (hY : 0 < Y)
    (hHT : H ≤ T) (N : ℕ) :
    (∫ t in H..T, ‖dampedDivisorSeries Y t -
      divisorPolynomial N (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t‖ ^ 2) ≤
      (T - H) * dampedDivisorTailBudget Y N ^ 2 := by
  have hc := (continuous_dampedDivisorSeries hY).sub
    (continuous_divisorPolynomial N (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)))
  calc
    _ ≤ ∫ _t in H..T, dampedDivisorTailBudget Y N ^ 2 := by
      apply intervalIntegral.integral_mono_on hHT ((hc.norm.pow 2).intervalIntegrable H T)
        (continuous_const.intervalIntegrable H T)
      intro t _
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_dampedDivisorSeries_sub_polynomial_le hY N t) 2
    _ = _ := by simp [smul_eq_mul]

/-- The actual damped polynomials converge to the infinite series in interval L2. -/
theorem tendsto_integral_dampedDivisor_tail_sq {Y H T : ℝ} (hY : 0 < Y)
    (hHT : H ≤ T) :
    Tendsto (fun N => ∫ t in H..T, ‖dampedDivisorSeries Y t -
      divisorPolynomial N (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t‖ ^ 2)
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun N => intervalIntegral.integral_nonneg hHT (fun _ _ => sq_nonneg _))
    (integral_dampedDivisor_tail_sq_le hY hHT)
  simpa using (tendsto_const_nhds.mul ((tendsto_dampedDivisorTailBudget Y).pow 2))

/-- Closed form of the complete majorant tail, with its damping dependence explicit. -/
theorem dampedDivisorTailBudget_eq {Y : ℝ} (hY : 0 < Y) (N : ℕ) :
    dampedDivisorTailBudget Y N =
      Real.exp (-1 / Y) ^ (N + 1) *
        (((N + 1 : ℕ) : ℝ) / (1 - Real.exp (-1 / Y)) +
          Real.exp (-1 / Y) / (1 - Real.exp (-1 / Y)) ^ 2) := by
  let r := Real.exp (-1 / Y)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hY)
  have hr : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hs : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hg : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have he (n : ℕ) : dampedDivisorMajorant Y (n + N) =
      r ^ (N + 1) * ((n : ℝ) * r ^ n + ((N + 1 : ℕ) : ℝ) * r ^ n) := by
    unfold dampedDivisorMajorant
    have hexp : Real.exp (-((n + N + 1 : ℕ) : ℝ) / Y) = r ^ (n + (N + 1)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hexp, pow_add]
    push_cast
    ring
  unfold dampedDivisorTailBudget
  simp_rw [he]
  rw [tsum_mul_left, hs.tsum_add (hg.mul_left _), tsum_mul_left,
    tsum_coe_mul_geometric_of_norm_lt_one hr, tsum_geometric_of_lt_one hr0 hr1]
  dsimp [r]
  ring

theorem norm_damped_divisorPolynomial_le {Y : ℝ} (hY : 0 < Y) (N : ℕ) (t : ℝ) :
    ‖divisorPolynomial N (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t‖ ≤
      dampedDivisorTailBudget Y 0 := by
  rw [divisorPolynomial_eq_sum_dampedDivisorTerm]
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖dampedDivisorTerm Y n t‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, dampedDivisorMajorant Y n :=
      Finset.sum_le_sum (fun n _ => norm_dampedDivisorTerm_le Y n t)
    _ ≤ ∑' n, dampedDivisorMajorant Y n :=
      (summable_dampedDivisorMajorant hY).sum_le_tsum _
        (fun n _ => dampedDivisorMajorant_nonneg Y n)
    _ = _ := by simp [dampedDivisorTailBudget]

/-- Second moments converge even after subtraction of an arbitrary continuous function.
In particular, a fixed finite head can be retained throughout the limit passage. -/
theorem tendsto_integral_damped_divisorPolynomial_sub_sq {Y : ℝ} (hY : 0 < Y)
    {g : ℝ → ℂ} (hg : Continuous g) (H T : ℝ) :
    Tendsto
      (fun N => ∫ t in H..T,
        ‖divisorPolynomial N (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t - g t‖ ^ 2)
      atTop (𝓝 (∫ t in H..T, ‖dampedDivisorSeries Y t - g t‖ ^ 2)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => (dampedDivisorTailBudget Y 0 + ‖g t‖) ^ 2)
  · exact Filter.Eventually.of_forall (fun N =>
      (((continuous_divisorPolynomial N _).sub hg).norm.pow 2).aestronglyMeasurable)
  · apply Filter.Eventually.of_forall
    intro N
    apply Filter.Eventually.of_forall
    intro t _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    exact (norm_sub_le _ _).trans
      (add_le_add (norm_damped_divisorPolynomial_le hY N t) le_rfl)
  · exact ((continuous_const.add hg.norm).pow 2).intervalIntegrable H T
  · apply Filter.Eventually.of_forall
    intro t _
    exact (((tendstoUniformly_damped_divisorPolynomial hY).tendsto_at t).sub
      tendsto_const_nhds).norm.pow 2

/-- A genuinely uniform finite-tail bound passes to the actual infinite tail. -/
theorem integral_dampedDivisor_tail_sq_le_of_eventually {Y H T C : ℝ} (hY : 0 < Y)
    (L : ℕ)
    (hb : ∀ᶠ N in atTop,
      (∫ t in H..T, ‖divisorPolynomial N
        (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t -
        divisorPolynomial L (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t‖ ^ 2) ≤ C) :
    (∫ t in H..T, ‖dampedDivisorSeries Y t -
      divisorPolynomial L (fun n => (Real.exp (-(n : ℝ) / Y) : ℂ)) t‖ ^ 2) ≤ C :=
  le_of_tendsto (tendsto_integral_damped_divisorPolynomial_sub_sq hY
    (continuous_divisorPolynomial L _) H T) hb

end RiemannResearch.Analysis

/--
info: 'RiemannResearch.Analysis.tendsto_integral_dampedDivisor_tail_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.tendsto_integral_dampedDivisor_tail_sq

/--
info: 'RiemannResearch.Analysis.dampedDivisorTailBudget_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.dampedDivisorTailBudget_eq

/--
info: 'RiemannResearch.Analysis.tendsto_integral_damped_divisorPolynomial_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.tendsto_integral_damped_divisorPolynomial_sub_sq

/--
info: 'RiemannResearch.Analysis.integral_dampedDivisor_tail_sq_le_of_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.Analysis.integral_dampedDivisor_tail_sq_le_of_eventually
