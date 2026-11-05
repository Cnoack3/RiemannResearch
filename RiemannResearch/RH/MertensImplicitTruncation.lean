/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensTruncationReserve

/-!
# The implicit Mertens truncation yields a square-root reserve

Source: E. S. Lee and N. Leong, arXiv:2208.06141v5, Section 5.4 and
Proposition 5.2, (60) and (62). For y = log T and U = log log x - log 53.99,
(60) reads 5 log y + log log y = 3 U. The expression for y in the hypothesis
below rewrites this equation relative to the printed exponent.
-/
noncomputable section
open Filter
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert QSquarefreeDisplacementRigidity

/-- The implicit exponent and size estimate of Lee–Leong, Proposition 5.2
at W = 53.99. All identities concern sufficiently large positive inputs. -/
def LeeLeongImplicitTruncation : Prop :=
  ∃ (y : ℝ → ℝ) (K : ℝ), 0 < K ∧ Tendsto y atTop atTop ∧
    (∀ᶠ x : ℝ in atTop, |M x| ≤ K * x * Real.log x * Real.exp (-y x)) ∧
    ∀ᶠ x : ℝ in atTop,
      let z := Real.log (Real.log (y x)) / (3 * (Real.log (Real.log x) - Real.log 53.99))
      z < 1 ∧ y x = leeLeongFullProfile x * (1 - z) ^ (-(1/5 : ℝ))

/-- The implicit exponent has sufficient surplus to absorb both the printed
logarithmic prefactor and any fixed multiple of the square-root scale. -/
theorem truncationReserve_of_implicitTruncation (h : LeeLeongImplicitTruncation) :
    LeeLeongTruncationReserve := by
  obtain ⟨y, K, hK, hy, hM, hyid⟩ := h
  intro k
  let c := leeLeongRate / (15 * (|k| + 2))
  have hA : 0 < leeLeongRate := by unfold leeLeongRate; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hK0 : 0 < 15 * (|k| + 2) := by positivity
  have hr : 0 < Real.log (53.99 : ℝ) := Real.log_pos (by norm_num)
  have hLtop := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [hM, hyid, (hLtop.comp hy).eventually (eventually_ge_atTop (1 : ℝ)),
    hLtop.eventually (eventually_gt_atTop (Real.log (53.99 : ℝ))),
    hLtop.eventually (eventually_ge_atTop (Real.log K)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop (0 : ℝ), leeLeongFullProfile_eventually_bounds,
    vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ)),
    vkProfile_dominates_logLog_sq (c^2) (sq_pos_of_pos hc),
    vkProfile_dominates_logLog_sq 1 zero_lt_one] with x hMx hid hyL hL hLK ht hx hF hV hd hdom
  let L := Real.log (Real.log x)
  let P := vkProfile x
  let s := Real.sqrt P
  let F := leeLeongFullProfile x
  let H := Real.log (Real.log (y x))
  let U := 3 * (L - Real.log 53.99)
  let z := H / U
  change z < 1 ∧ y x = F * (1 - z) ^ (-(1/5 : ℝ)) at hid
  change 1 ≤ H at hyL
  change Real.log (53.99 : ℝ) < L at hL
  change Real.log K ≤ L at hLK
  change 0 ≤ P at hV
  change L ^ 2 ≤ c ^ 2 * P at hd
  change L ^ 2 ≤ 1 * P at hdom
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = P := Real.sq_sqrt hV
  have hL0 : 0 < L := hr.trans hL
  have hU : 0 < U := by dsimp [U]; linarith only [hL]
  have hF0 : 0 ≤ F := (mul_nonneg hA.le hV).trans hF.1
  have htan : 1 + z / 5 ≤ (1-z)^(-(1/5 : ℝ)) := by
    have hlog := Real.log_le_sub_one_of_pos (sub_pos.mpr hid.1)
    rw [Real.rpow_def_of_pos (sub_pos.mpr hid.1)]
    linarith [Real.add_one_le_exp (Real.log (1-z) * (-(1/5 : ℝ)))]
  have hz : 1 / (3*L) ≤ z := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3*L) hU).mpr
    dsimp only [U]
    nlinarith only [mul_le_mul_of_nonneg_right hyL hL0.le, hr]
  have hgap : F + leeLeongRate * P / (15*L) ≤ y x := by
    calc
      F + leeLeongRate * P / (15*L) ≤ F + F / (15*L) := by
        have hf : leeLeongRate * P ≤ F := hF.1
        linarith only [div_le_div_of_nonneg_right hf (show 0 ≤ 15*L by positivity)]
      _ = F * (1 + (1/(3*L))/5) := by
        field_simp [hL0.ne']
        ring
      _ ≤ F * (1 + z/5) := by
        apply mul_le_mul_of_nonneg_left _ hF0
        linarith only [hz]
      _ ≤ y x := by rw [hid.2]; exact mul_le_mul_of_nonneg_left htan hF0
  have hLs : L ≤ s := le_of_sq_le_sq (by linarith only [hdom, hs2]) hs0
  have hLc : L ≤ c * s := le_of_sq_le_sq (by simpa only [mul_pow, hs2] using hd)
    (mul_nonneg hc.le hs0)
  have hLc' : L * (15*(|k|+2)) ≤ leeLeongRate * s := by
    have he : c * s = leeLeongRate * s / (15*(|k|+2)) := by dsimp [c]; ring
    rw [he] at hLc
    exact (le_div_iff₀ hK0).mp hLc
  have hbudget : (|k|+2)*s ≤ leeLeongRate * P / (15*L) := by
    apply (le_div_iff₀ (by positivity : 0 < 15*L)).mpr
    calc
      _ = (L * (15*(|k|+2)))*s := by ring
      _ ≤ (leeLeongRate*s)*s := mul_le_mul_of_nonneg_right hLc' hs0
      _ = _ := by rw [mul_assoc, ← pow_two, hs2]
  calc
    |M x| ≤ K * x * Real.log x * Real.exp (-y x) := hMx
    _ = x * Real.exp ((Real.log K + L) - y x) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hK,
        show Real.exp L = Real.log x by exact Real.exp_log ht]
      ring
    _ ≤ x * Real.exp (-F - k * s) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hx
      linarith only [hLK, hLs, hgap, hbudget, mul_le_mul_of_nonneg_right (le_abs_self k) hs0]
    _ = _ := mul_comm _ _

/-- The displacement moment with any nonnegative square-root addition to the
printed profile implies RH directly under the published implicit estimate. -/
theorem riemannHypothesis_of_implicitTruncation_moment (h : LeeLeongImplicitTruncation)
    (a : ℝ) (ha : 0 ≤ a)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-(leeLeongFullProfile n + a * Real.sqrt (vkProfile n)))) *
      |qSequence displacement n|)) : RiemannHypothesis :=
  riemannHypothesis_of_truncationReserve_moment (truncationReserve_of_implicitTruncation h) a ha hd

/-- The actual displacement may grow at the printed profile plus any fixed
signed square-root correction, assuming the published implicit estimate. -/
theorem riemannHypothesis_of_implicitTruncation_pointwise (h : LeeLeongImplicitTruncation)
    (a D : ℝ) (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤ D *
      Real.exp (leeLeongFullProfile n + a * Real.sqrt (vkProfile n))) : RiemannHypothesis :=
  riemannHypothesis_of_truncationReserve_pointwise (truncationReserve_of_implicitTruncation h)
    a D hd

end RiemannResearch.RH.QMertensFirstMoment
