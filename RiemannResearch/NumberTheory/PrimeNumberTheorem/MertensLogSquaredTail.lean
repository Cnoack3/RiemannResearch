/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.ZetaBounds

/-! # The logarithmic integral on the far sides of the Möbius contour -/

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.MobiusContour

/-- Exact far-tail integral; the primitive is the negative of the expression
on the right. -/
theorem mertens_log_sq_tail_eq {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Ici T, (Real.log t)^2 / t^2) =
      ((Real.log T)^2 + 2 * Real.log T + 2) / T := by
  let g : ℝ → ℝ := fun x => -((Real.log x)^2 + 2 * Real.log x + 2) / x
  have hd : ∀ x ∈ Set.Ici T,
      HasDerivAt g ((Real.log x)^2 / x^2) x := by
    intro x hx
    have hx0 : x ≠ 0 := (hT.trans_le hx).ne'
    have hl := Real.hasDerivAt_log hx0
    have hn := ((hl.pow 2).add (hl.const_mul 2)).add_const 2
    have hh := hn.neg.div (hasDerivAt_id x) hx0
    apply hh.congr_deriv
    simp only [id_eq, Pi.neg_apply, Pi.add_apply, Pi.pow_apply]
    field_simp [hx0] <;> ring
  have hsq : Tendsto (fun x : ℝ => (Real.log x)^2 / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_two, Real.rpow_one] using
      Real.tendsto_pow_log_div_pow_atTop 1 2 zero_lt_one
  have hlin : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using Real.tendsto_pow_log_div_pow_atTop 1 1 zero_lt_one
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlim : Tendsto g atTop (𝓝 0) := by
    have hh := ((hsq.add (hlin.const_mul 2)).add (hinv.const_mul 2)).neg
    convert hh using 1
    · funext x
      dsimp [g]
      ring
    · norm_num
  have hnon : ∀ x ∈ Set.Ioi T, 0 ≤ (Real.log x)^2 / x^2 :=
    fun x _ => div_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_nonneg' hd hnon hlim]
  dsimp [g]
  ring

/-- Uniform form for the far edges of a truncated contour. -/
theorem mertens_log_sq_tail_le {T : ℝ} (hT : 3 < T) :
    (∫ t in Set.Ici T, (Real.log t)^2 / t^2) ≤ 2 * (1 + Real.log T)^2 / T := by
  have hpos : (0:ℝ) < T := by linarith
  rw [mertens_log_sq_tail_eq hpos]
  apply (div_le_div_iff_of_pos_right hpos).2
  nlinarith [sq_nonneg (Real.log T), Real.log_nonneg (show 1 ≤ T by linarith)]

theorem mertens_log_sq_tail_integrable {T : ℝ} (hT : 3 < T) :
    IntegrableOn (fun t : ℝ => (Real.log t)^2 / t^2) (Set.Ici T) := by
  have hpos : (0:ℝ) < T := by linarith
  have hlog := Real.log_pos (show 1 < T by linarith)
  by_contra hn
  have h := mertens_log_sq_tail_eq hpos
  rw [integral_undef hn] at h
  have hp : 0 < ((Real.log T)^2 + 2 * Real.log T + 2) / T := by positivity
  linarith

end RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.MobiusContour
