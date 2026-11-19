import RiemannResearch.Analysis.MontgomeryCenteredLogMeanSquare
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Endpoint error in the fourth retained complex transition term

The exact real primitive retains all three powers of log T. The cost of
moving its upper endpoint from T+2 to T is explicitly bounded. -/

noncomputable section
open Set MeasureTheory
namespace RiemannResearch.Analysis.MontgomeryLogMeanSquare

/-- Finite-height control of the complete centered logarithmic polynomial. -/
theorem centered_log_mean_square_remainder_le (k : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    |(∫ t in (0:ℝ)..T, (Real.log (t+2)-k)^2) -
      T*((Real.log T-(1+k))^2+1)| ≤
      2*(Real.log (T+2)+|k|)^2 + |centeredLogSquarePrimitive k 2| := by
  let P := centeredLogSquarePrimitive k
  let M := (Real.log (T+2)+|k|)^2
  have hTp : 0 < T := zero_lt_one.trans_le hT
  have hder (y : ℝ) (hy : y ∈ Icc T (T+2)) : HasDerivAt P ((Real.log y-k)^2) y := by
    have hp : 0 < y := hTp.trans_le hy.1
    have hd := (Real.hasDerivAt_log hp.ne').sub_const k
    have H := (hasDerivAt_id y).mul (((hd.pow 2).sub (hd.const_mul 2)).add_const 2)
    convert H using 1 <;> first | rfl |
      (simp only [Pi.sub_apply,Pi.pow_apply,id_eq]; field_simp [hp.ne'] <;> ring)
  have hnorm (y : ℝ) (hy : y ∈ Icc T (T+2)) : ‖(Real.log y-k)^2‖ ≤ M := by
    have hly := Real.log_nonneg (hT.trans hy.1)
    have hlarge := Real.log_le_log (hTp.trans_le hy.1) hy.2
    have hh : |Real.log y-k| ≤ Real.log (T+2)+|k| := by
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg hly]
      linarith
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hh 2
  have HE := (convex_Icc T (T+2)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hder y hy).hasDerivWithinAt) hnorm
    (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
  have HE' : |P (T+2)-P T| ≤ 2*M := by
    simpa only [Real.norm_eq_abs,add_sub_cancel_left,abs_of_nonneg (by norm_num : (0:ℝ)≤2),
      mul_comm M 2] using HE
  have hpoly : T*((Real.log T-(1+k))^2+1) = P T := by dsimp [P,centeredLogSquarePrimitive]; ring
  rw [hpoly,centered_log_mean_square_eq k hTp.le]
  change |P (T+2)-P 2-P T| ≤ 2*M+|P 2|
  rw [show P (T+2)-P 2-P T = (P (T+2)-P T)-P 2 by ring]
  apply (abs_sub _ _).trans
  linarith only [HE']

end RiemannResearch.Analysis.MontgomeryLogMeanSquare
