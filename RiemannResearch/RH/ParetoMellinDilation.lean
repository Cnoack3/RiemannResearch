import RiemannResearch.RH.ParetoMellinFunctional
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dilation covariance of the actual Pareto Mellin integral

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 9.2. The proof uses the actual step embedding, natural-floor
division and the ordinary Lebesgue change of variables. No arithmetic
transform formula or zero-existence hypothesis occurs.
-/

namespace RiemannResearch.RH.Pareto
open MeasureTheory Set
noncomputable section

theorem paretoMellin_eq_full_integral (f : ThresholdHilbert) (s : ℂ) :
    paretoMellin f s = ∫ x, mellinWeightedStep f x * paretoMellinKernel s x := by
  unfold paretoMellin
  rw [← integral_Ici_eq_integral_Ioi]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hlt : x < 1 := lt_of_not_ge hx
  simp [mellinWeightedStep, Nat.floor_eq_zero.mpr hlt]

private theorem mellin_integrand_dilation (f : ThresholdHilbert)
    (m : ℕ) (hm : 0 < m) (s : ℂ) (x : ℝ) :
    mellinWeightedStep (hilbertDilation m hm f) ((m : ℝ) * x) *
        paretoMellinKernel s ((m : ℝ) * x) =
      (m : ℂ)^(-s) * (mellinWeightedStep f x * paretoMellinKernel s x) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  by_cases hx : 0 < x
  · have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hfloor : ⌊(m : ℝ) * x⌋₊ / m = ⌊x⌋₊ := by
      rw [← Nat.floor_div_natCast]
      congr 1
      field_simp
    unfold mellinWeightedStep paretoMellinKernel
    rw [hilbertDilation_sequence]
    simp only [dilation, hfloor, Complex.ofReal_mul, Complex.ofReal_natCast]
    have hpower : ((m : ℂ) * (x : ℂ)) ^ (-s) =
        (m : ℂ)^(-s) * (x : ℂ)^(-s) := by
      simpa only [Complex.ofReal_natCast] using
        Complex.mul_cpow_ofReal_nonneg hmR.le hx.le (-s)
    rw [hpower]
    field_simp
  · have hxle : x ≤ 0 := le_of_not_gt hx
    have hmx : (m : ℝ) * x < 1 := lt_of_le_of_lt
      (mul_nonpos_of_nonneg_of_nonpos hmR.le hxle) zero_lt_one
    have hx1 : x < 1 := lt_of_le_of_lt hxle zero_lt_one
    simp [mellinWeightedStep, Nat.floor_eq_zero.mpr hmx, Nat.floor_eq_zero.mpr hx1]

/-- Exact covariance for every positive integer dilation. The statement
also holds for the totalized integral outside its continuity half-plane. -/
theorem paretoMellin_dilation (f : ThresholdHilbert) (m : ℕ) (hm : 0 < m)
    (s : ℂ) :
    paretoMellin (hilbertDilation m hm f) s =
      (m : ℂ) ^ (1 - s) * paretoMellin f s := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have h := Measure.integral_comp_mul_left
    (fun x => mellinWeightedStep (hilbertDilation m hm f) x * paretoMellinKernel s x)
    (m : ℝ)
  simp_rw [mellin_integrand_dilation f m hm s] at h
  rw [integral_const_mul, abs_of_pos (inv_pos.mpr hmR)] at h
  rw [← paretoMellin_eq_full_integral f s,
    ← paretoMellin_eq_full_integral (hilbertDilation m hm f) s] at h
  change (m : ℂ)^(-s) * paretoMellin f s =
    (((m : ℝ)⁻¹ : ℝ) : ℂ) * paretoMellin (hilbertDilation m hm f) s at h
  rw [Complex.ofReal_inv, Complex.ofReal_natCast] at h
  have hmul := congrArg (fun z : ℂ => (m : ℂ) * z) h
  rw [← mul_assoc (m : ℂ) (m : ℂ)⁻¹, mul_inv_cancel₀ hmC, one_mul] at hmul
  rw [show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add 1 (-s) hmC,
    Complex.cpow_one, mul_assoc]
  exact hmul.symm

end
end RiemannResearch.RH.Pareto
