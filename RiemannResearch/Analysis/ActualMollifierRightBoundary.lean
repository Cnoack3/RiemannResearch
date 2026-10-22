/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualMobiusZeroDetector
import RiemannResearch.Analysis.ZetaAbsoluteConvergenceBounds
import RiemannResearch.Analysis.ComplexQuadraticDetectorLogBounds
import RiemannResearch.Analysis.PSeriesTail
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# An unconditional signed right boundary bound for the actual mollifier

The exact Mobius Dirichlet tail proves ||zeta M_X - 1|| <= 6/sqrt X on
Re s = 3/2. For X >= 37 the detector is nonzero and its signed right integral
is bounded by -(T-H) log(1-36/X), then by 36(T-H)/(X-36).
Chourasiya--Simonic, arXiv:2507.15184v2, equations (29) and Lemma 7, supports
the detector and signed integral being estimated:
https://arxiv.org/html/2507.15184v2. The absolute-convergence estimate here is
independent of the paper's numerical mean-square constant. No moment estimate
near the critical line or finite-RH certificate is used.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.InghamMollifier

def mobiusTail (X : ℕ) (s : ℂ) : ℂ :=
  ∑' k : ℕ, LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s (k + X + 1)

theorem mollifier_eq_sum_range (X : ℕ) (s : ℂ) :
    mollifier X s = ∑ n ∈ Finset.range (X + 1),
      LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n := by
  have hi : ∀ n ∈ Finset.Icc 1 X,
      (ArithmeticFunction.moebius n : ℂ) * Complex.exp (-s * (Real.log (n : ℝ) : ℂ)) =
        LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n := by
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    rw [LSeries.term_of_ne_zero hn0, div_eq_mul_inv, ← Complex.cpow_neg,
      Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn0), ← Complex.natCast_log]
    congr 2
    ring
  unfold mollifier
  calc
    _ = ∑ n ∈ Finset.Icc 1 X,
        LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n :=
      Finset.sum_congr rfl hi
    _ = ∑ n ∈ Finset.range (X + 1),
        LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n := by
      apply Finset.sum_subset (fun n hn => Finset.mem_range.mpr (by
        have := Finset.mem_Icc.mp hn; omega))
      intro n hn hnot
      have hn0 : n = 0 := by
        have hh := Finset.mem_range.mp hn
        simp only [Finset.mem_Icc, not_and_or] at hnot
        omega
      simp [hn0]

theorem mollifier_error_exact {s : ℂ} (hs : 1 < s.re) (X : ℕ) :
    riemannZeta s * mollifier X s - 1 = -riemannZeta s * mobiusTail X s := by
  have hsum : Summable (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hsplit := hsum.sum_add_tsum_nat_add (X + 1)
  change (∑ n ∈ Finset.range (X + 1),
      LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n) +
    mobiusTail X s = LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s at hsplit
  rw [← mollifier_eq_sum_range] at hsplit
  have hprod := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hprod
  calc riemannZeta s * mollifier X s - 1 =
      riemannZeta s * mollifier X s - riemannZeta s * (mollifier X s + mobiusTail X s) := by
        rw [hsplit, hprod]
    _ = _ := by ring

theorem mobiusTail_norm_le {s : ℂ} (hs : 1 < s.re) {X : ℕ} (hX : 1 ≤ X) :
    ‖mobiusTail X s‖ ≤ (X : ℝ) ^ (1 - s.re) / (s.re - 1) := by
  have hsum : Summable (LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have htail : Summable (fun k : ℕ =>
      LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s (k + X + 1)) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (X + 1)).mpr hsum
  have hp0 : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hp : Summable (fun k : ℕ => ((k + X + 1 : ℕ) : ℝ) ^ (-s.re)) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (X + 1)).mpr hp0
  have hle (k : ℕ) :
      ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s (k + X + 1)‖ ≤
        ((k + X + 1 : ℕ) : ℝ) ^ (-s.re) := by
    have hn0 : k + X + 1 ≠ 0 := by omega
    have hmu : ‖(ArithmeticFunction.moebius (k + X + 1) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k + X + 1))
    rw [LSeries.norm_term_eq, if_neg hn0]
    calc ‖(ArithmeticFunction.moebius (k + X + 1) : ℂ)‖ / ((k + X + 1 : ℕ) : ℝ) ^ s.re ≤
        1 / ((k + X + 1 : ℕ) : ℝ) ^ s.re := by gcongr
      _ = _ := by rw [Real.rpow_neg (Nat.cast_nonneg _), one_div]
  calc ‖mobiusTail X s‖ ≤ ∑' k : ℕ,
      ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s (k + X + 1)‖ :=
      norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' k : ℕ, ((k + X + 1 : ℕ) : ℝ) ^ (-s.re) :=
      htail.norm.tsum_le_tsum hle hp
    _ ≤ _ := Real.tsum_nat_rpow_tail_le hs hX

theorem mollifier_error_norm_le {s : ℂ} (hs : 1 < s.re) {X : ℕ} (hX : 1 ≤ X) :
    ‖riemannZeta s * mollifier X s - 1‖ ≤
      ‖riemannZeta s‖ * ((X : ℝ) ^ (1 - s.re) / (s.re - 1)) := by
  rw [mollifier_error_exact hs X, norm_mul, norm_neg]
  exact mul_le_mul_of_nonneg_left (mobiusTail_norm_le hs hX) (norm_nonneg _)

theorem mollifier_error_norm_le_right {X : ℕ} (hX : 1 ≤ X)
    {s : ℂ} (hr : s.re = 3 / 2) :
    ‖riemannZeta s * mollifier X s - 1‖ ≤ 6 / Real.sqrt (X : ℝ) := by
  have hs : 1 < s.re := by rw [hr]; norm_num
  have hζ : ‖riemannZeta s‖ ≤ 3 := by
    have hh := norm_riemannZeta_le_integral_test hs
    norm_num [hr] at hh
    exact hh
  have hp : (X : ℝ) ^ (1 - s.re) / (s.re - 1) = 2 / Real.sqrt (X : ℝ) := by
    rw [hr, show 1 - (3 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      show (3 / 2 : ℝ) - 1 = 1 / 2 by ring,
      Real.rpow_neg (Nat.cast_nonneg X), ← Real.sqrt_eq_rpow]
    ring
  have he := mollifier_error_norm_le hs hX
  rw [hp] at he
  calc _ ≤ ‖riemannZeta s‖ * (2 / Real.sqrt (X : ℝ)) := he
    _ ≤ 3 * (2 / Real.sqrt (X : ℝ)) := by gcongr
    _ = _ := by ring

theorem zetaDetector_eq_one_sub_error_sq (X : ℕ) (s : ℂ) :
    zetaDetector X s = 1 - (riemannZeta s * mollifier X s - 1) ^ 2 := by
  unfold zetaDetector Complex.quadraticZeroDetector
  ring

end RiemannResearch.Analysis.InghamMollifier

namespace RiemannResearch.Analysis.InghamMollifier

theorem zetaDetector_right_ne_zero_and_neg_log_le_sharp {X : ℕ} (hX : 37 ≤ X)
    {s : ℂ} (hr : s.re = 3 / 2) :
    zetaDetector X s ≠ 0 ∧
      -Real.log ‖zetaDetector X s‖ ≤ -Real.log (1 - 36 / (X : ℝ)) := by
  have hX1 : 1 ≤ X := by omega
  have hXp : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hsqrtp : 0 < Real.sqrt (X : ℝ) := Real.sqrt_pos.mpr hXp
  let e : ℂ := riemannZeta s * mollifier X s - 1
  have he : ‖e‖ ≤ 6 / Real.sqrt (X : ℝ) := mollifier_error_norm_le_right hX1 hr
  have he2 : ‖e‖ ^ 2 ≤ 36 / (X : ℝ) := by
    calc
      ‖e‖ ^ 2 ≤ (6 / Real.sqrt (X : ℝ)) ^ 2 := by
        simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg e) he
      _ = 36 / (X : ℝ) := by rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg X)]; norm_num
  have hr36 : 36 / (X : ℝ) < 1 := (div_lt_one hXp).mpr (by
    exact_mod_cast (show 36 < X by omega))
  rw [zetaDetector_eq_one_sub_error_sq]
  exact Complex.one_sub_sq_ne_zero_and_neg_log_norm_le_of_sq_le hr36 he2

theorem zetaDetector_right_log_norm_continuous_sharp {X : ℕ} (hX : 37 ≤ X) :
    Continuous (fun t : ℝ =>
      Real.log ‖zetaDetector X ((3 / 2 : ℂ) + (t : ℂ) * Complex.I)‖) := by
  let v : ℝ → ℂ := fun t => (3 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hv : Continuous v := by fun_prop
  have ha (t : ℝ) : AnalyticAt ℂ (zetaDetector X) (v t) := by
    apply Complex.quadraticZeroDetector_analyticAt
    · apply analyticAt_riemannZeta
      intro heq
      have hh := congrArg Complex.re heq
      norm_num [v] at hh
    · exact mollifier_analyticAt X (v t)
  have hc : Continuous (fun t : ℝ => zetaDetector X (v t)) :=
    continuous_iff_continuousAt.mpr (fun t => (ha t).continuousAt.comp hv.continuousAt)
  exact hc.norm.log (fun t => norm_ne_zero_iff.mpr
    (zetaDetector_right_ne_zero_and_neg_log_le_sharp hX (by simp [v])).1)

/-- The exact logarithmic majorant retained before its rational relaxation. -/
theorem zetaDetector_right_signed_log_integral_le_sharp {X : ℕ} (hX : 37 ≤ X)
    {H T : ℝ} (hHT : H ≤ T) :
    -(∫ t in H..T, Real.log ‖zetaDetector X ((3 / 2 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      (T - H) * (-Real.log (1 - 36 / (X : ℝ))) := by
  have hlog := zetaDetector_right_log_norm_continuous_sharp hX
  rw [← intervalIntegral.integral_neg]
  calc (∫ t in H..T, -Real.log ‖zetaDetector X ((3 / 2 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      ∫ _t in H..T, -Real.log (1 - 36 / (X : ℝ)) :=
        intervalIntegral.integral_mono hHT (hlog.neg.intervalIntegrable H T)
          (continuous_const.intervalIntegrable H T)
          (fun t => (zetaDetector_right_ne_zero_and_neg_log_le_sharp hX (by simp)).2)
    _ = (T - H) * (-Real.log (1 - 36 / (X : ℝ))) := by
      rw [intervalIntegral.integral_const]; rfl

theorem rightLogBudget_le_rational {X : ℕ} (hX : 37 ≤ X) :
    -Real.log (1 - 36 / (X : ℝ)) ≤ 36 / ((X : ℝ) - 36) := by
  have hXp : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hsub : 0 < (X : ℝ) - 36 := by
    have hx36 : (36 : ℝ) < (X : ℝ) := by exact_mod_cast (show 36 < X by omega)
    linarith
  have hr36 : 36 / (X : ℝ) < 1 := (div_lt_one hXp).mpr (by linarith only [hsub])
  have hp : 0 < 1 - 36 / (X : ℝ) := by linarith
  calc -Real.log (1 - 36 / (X : ℝ)) ≤
      (36 / (X : ℝ)) / (1 - 36 / (X : ℝ)) := Real.neg_log_one_sub_le_div_of_lt_one hr36
    _ = 36 / ((X : ℝ) - 36) := by field_simp [hXp.ne', hsub.ne', hp.ne']

theorem zetaDetector_right_signed_log_integral_le_rational {X : ℕ} (hX : 37 ≤ X)
    {H T : ℝ} (hHT : H ≤ T) :
    -(∫ t in H..T, Real.log ‖zetaDetector X ((3 / 2 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      36 * (T - H) / ((X : ℝ) - 36) := by
  calc -(∫ t in H..T, Real.log ‖zetaDetector X ((3 / 2 : ℂ) + (t : ℂ) * Complex.I)‖) ≤
      (T - H) * (-Real.log (1 - 36 / (X : ℝ))) :=
        zetaDetector_right_signed_log_integral_le_sharp hX hHT
    _ ≤ (T - H) * (36 / ((X : ℝ) - 36)) :=
      mul_le_mul_of_nonneg_left (rightLogBudget_le_rational hX) (sub_nonneg.mpr hHT)
    _ = _ := by ring

end RiemannResearch.Analysis.InghamMollifier


namespace RiemannResearch.Analysis.InghamMollifier
theorem zetaDetector_right_signed_log_integral_le_constant
    {X : ℕ} (hX : 37 ≤ X) {H T : ℝ} (hHT : H ≤ T)
    (hheight : T - H ≤ (X : ℝ) - 36) :
    -(∫ t in H..T, Real.log ‖zetaDetector X ((3 / 2 : ℂ) + (t : ℂ) * Complex.I)‖) ≤ 36 := by
  have hden : 0 < (X : ℝ) - 36 := by
    have hx : (36 : ℝ) < (X : ℝ) := by exact_mod_cast (show 36 < X by omega)
    linarith
  exact (zetaDetector_right_signed_log_integral_le_rational hX hHT).trans
    ((div_le_iff₀ hden).mpr (by nlinarith [hheight]))
end RiemannResearch.Analysis.InghamMollifier


namespace RiemannResearch.Analysis.InghamMollifier

/-- A concrete integral cutoff automatically sufficient for the right budget. -/
def growingMollifierCutoff (T : ℝ) : ℕ := Nat.ceil T + 37

theorem growingMollifierCutoff_ge_37 (T : ℝ) : 37 ≤ growingMollifierCutoff T := by
  dsimp [growingMollifierCutoff]
  omega

theorem growingMollifierCutoff_height (T : ℝ) :
    T + 37 ≤ (growingMollifierCutoff T : ℝ) := by
  simp only [growingMollifierCutoff, Nat.cast_add, Nat.cast_ofNat]
  linarith [Nat.le_ceil T]

end RiemannResearch.Analysis.InghamMollifier
