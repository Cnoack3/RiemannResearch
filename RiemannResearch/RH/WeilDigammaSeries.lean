import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.Mu
import RiemannResearch.RH.WeilCorrelationAdmissibility

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Positive digamma increments and the actual spatial gamma kernel

This adapts the proved partial-fraction expansion of the actual complex
digamma function from the vendored `Zeta23.GammaFacts.Mu` development.
The nonnegative terms provide domination for the Fourier-to-spatial passage.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.SignedWeilCorrelation

noncomputable section

def digammaIncrementTerm (a t : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + a) - ((n : ℝ) + a) / (((n : ℝ) + a) ^ 2 + t ^ 2)

theorem digammaIncrementTerm_nonneg {a : ℝ} (ha : 0 < a) (t : ℝ) (n : ℕ) :
    0 ≤ digammaIncrementTerm a t n := by
  have hx : 0 < (n : ℝ) + a := by positivity
  have hd : ((n : ℝ) + a) / ((n : ℝ) + a) ^ 2 = 1 / ((n : ℝ) + a) := by
    field_simp [ne_of_gt hx]
  have h := div_le_div_of_nonneg_left hx.le (sq_pos_of_pos hx)
    (show ((n : ℝ) + a) ^ 2 ≤ ((n : ℝ) + a) ^ 2 + t ^ 2 from
      le_add_of_nonneg_right (sq_nonneg t))
  rw [hd] at h
  exact sub_nonneg.mpr h

theorem digammaIncrementTerm_succ_eq {a : ℝ} (ha : 0 < a) (t : ℝ) (n : ℕ) :
    digammaIncrementTerm a t (n + 1) =
      (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) /
        (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) -
      (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) /
        (((n : ℝ) + 1 + a) ^ 2 + (0 : ℝ) ^ 2)) := by
  have hx : 0 < (n : ℝ) + 1 + a := by positivity
  have hd : ((n : ℝ) + 1 + a) / ((n : ℝ) + 1 + a) ^ 2 =
      1 / ((n : ℝ) + 1 + a) := by field_simp [ne_of_gt hx]
  simp only [digammaIncrementTerm, Nat.cast_add, Nat.cast_one, zero_pow (by decide : 2 ≠ 0),
    add_zero, hd]
  ring

theorem summable_digammaIncrementTerm {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (t : ℝ) :
    Summable (digammaIncrementTerm a t) := by
  apply (summable_nat_add_iff 1).mp
  have hs := (Zeta23.MuFields.summable_re_terms ha ha1 t).sub
    (Zeta23.MuFields.summable_re_terms ha ha1 0)
  exact hs.congr (fun n => (digammaIncrementTerm_succ_eq ha t n).symm)

/-- The actual digamma increment is the sum of nonnegative rational terms. -/
theorem re_digamma_sub_eq_tsum {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (t : ℝ) :
    (Complex.digamma ((a : ℂ) + Complex.I * t)).re -
      (Complex.digamma (a : ℂ)).re = ∑' n : ℕ, digammaIncrementTerm a t n := by
  have hr := Zeta23.MuFields.re_digamma_vertical ha ha1 t
  have h0 := Zeta23.MuFields.re_digamma_vertical ha ha1 0
  simp only [Complex.ofReal_zero, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] at h0
  have hd : a / a ^ 2 = 1 / a := by field_simp [ne_of_gt ha]
  rw [hd] at h0
  rw [(summable_digammaIncrementTerm ha ha1 t).tsum_eq_zero_add]
  have he : (fun n => digammaIncrementTerm a t (n + 1)) =
      (fun n : ℕ =>
        (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) /
          (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) -
        (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) /
          (((n : ℝ) + 1 + a) ^ 2 + (0 : ℝ) ^ 2))) := by
    funext n
    exact digammaIncrementTerm_succ_eq ha t n
  rw [he, (Zeta23.MuFields.summable_re_terms ha ha1 t).tsum_sub
    (Zeta23.MuFields.summable_re_terms ha ha1 0)]
  simp only [digammaIncrementTerm, Nat.cast_zero, zero_add]
  simp only [zero_pow (by decide : 2 ≠ 0), add_zero] at hr h0 ⊢
  linarith

/-- The exact spatial Weil gamma kernel is the sum of its positive
exponential Laplace kernels on the positive half-line. -/
theorem hasSum_weilGammaKernel {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => Real.exp (-(2 * (n : ℝ) + 1 / 2) * t))
      (weilGammaKernel t) := by
  have hq : ‖Real.exp (-2 * t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hs := (hasSum_geometric_of_norm_lt_one hq).mul_left (Real.exp (-t / 2))
  have hp (n : ℕ) : Real.exp (-2 * t) ^ n = Real.exp ((-2 * t) * (n : ℝ)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, ← Real.exp_add]
      congr 1
      push_cast
      ring
  have he : (fun n : ℕ => Real.exp (-t / 2) * Real.exp (-2 * t) ^ n) =
      (fun n : ℕ => Real.exp (-(2 * (n : ℝ) + 1 / 2) * t)) := by
    funext n
    rw [hp, ← Real.exp_add]
    congr 1
    ring
  rw [he] at hs
  simpa only [weilGammaKernel_eq_decay_quotient, div_eq_mul_inv] using hs

end
end RiemannResearch.RH.SignedWeilCorrelation
