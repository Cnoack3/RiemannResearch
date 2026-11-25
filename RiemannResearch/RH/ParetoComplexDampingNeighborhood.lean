import RiemannResearch.Analysis.RHInteriorZetaVariation
import RiemannResearch.Analysis.AnalyticReciprocalZeta
import RiemannResearch.RH.ParetoShiftedZetaBudget

/-! # A local complex damping bound for the Nyman–Beurling quotient -/

noncomputable section
open Complex Set Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint criticalPoint_re)
open RiemannResearch.Analysis.RHInteriorLogDerivative

/-- Complex damping with the reciprocal continued through its zero at one. -/
def complexDampedZeta (z : ℂ) (t : ℝ) : ℂ :=
  riemannZeta (criticalPoint t) * analyticReciprocalZeta (criticalPoint t+z)

theorem analyticAt_complexDampedZeta (hRH : RiemannHypothesis) {z : ℂ}
    (hz : 0 < z.re) (t : ℝ) : AnalyticAt ℂ (fun w => complexDampedZeta w t) z := by
  have hr : 1/2 < (criticalPoint t+z).re := by rw [Complex.add_re,criticalPoint_re]; linarith
  exact analyticAt_const.mul ((analyticAt_reciprocalZeta_of_riemannHypothesis hRH hr).comp
    (analyticAt_const.add analyticAt_id))

/-- The same exponent works around every real damping center in (0,3/4).
It leaves room below one half for a logarithm in the derivative estimate. -/
theorem complexDampedZeta_neighborhood_high (hRH : RiemannHypothesis) {d : ℝ}
    (hd : 0 < d) (hd' : d ≤ 3/4) :
    ∃ r > 0, ∃ K > 0, ∀ z ∈ Metric.ball (d:ℂ) r, ∀ t : ℝ, 3 ≤ |t| →
      ‖complexDampedZeta z t‖ ≤ K*(2*|t|)^(13/32:ℝ) := by
  let η := min (d/3) (1/4)
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  have hη1 : η ≤ 1/4 := min_le_right _ _
  have hηd : η ≤ d/3 := min_le_left _ _
  obtain ⟨C,hC,hCbound⟩ := interior_zeta_norm_ratio_le hRH hη hη1
  let r := min η (1/(32*C))
  have hr : 0 < r := lt_min hη (by positivity)
  let K := 2*Real.exp 10
  refine ⟨r,hr,K,by positivity,?_⟩
  intro z hz t ht
  let v := z-(d:ℂ)
  have hv : ‖v‖ < r := by simpa [v,Metric.mem_ball,dist_eq_norm] using hz
  have hn : ‖v‖ ≤ η := hv.le.trans (min_le_left _ _)
  have hCr : C*‖v‖ ≤ 1/32 := by
    have h := (le_div_iff₀ (show 0 < 32*C by positivity)).mp (hv.le.trans (min_le_right _ _))
    linarith
  have he := hCbound (1/2+d) t v (by linarith) (by linarith) ht hn
  have hs : (((1/2+d:ℝ):ℂ)+(t:ℂ)*I) = criticalPoint t+(d:ℂ) := by
    unfold criticalPoint
    push_cast
    ring
  rw [hs,show criticalPoint t+(d:ℂ)+v = criticalPoint t+z by dsimp [v];ring] at he
  have hw : criticalPoint t+z ≠ 1 := fun h => by
    have hz' : |z.im| ≤ η := by
      have hvz := (Complex.abs_im_le_norm v).trans hn
      simpa [v] using hvz
    have hc := congrArg Complex.im h
    simp [criticalPoint] at hc
    have hab : |t| = |z.im| := by rw [show t = -z.im by linarith,abs_neg]
    linarith
  have hbase : riemannZeta (criticalPoint t+(d:ℂ)) ≠ 0 := by
    have hs' : 1/2 < (criticalPoint t+(d:ℂ)).re := by simp [criticalPoint_re,hd]
    rcases lt_or_ge (criticalPoint t+(d:ℂ)).re 1 with h | h
    · exact riemannHypothesis_iff_right_half_strip_zero_free.mp hRH _ hs' h
    · exact riemannZeta_ne_zero_of_one_le_re h
  have hf := shiftedZetaQuotient_high_le_up_to_one hRH hd (by linarith) (show 1 ≤ |t| by linarith)
  have hp : Real.pi ^ (-(d/2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have ht2 : 1 ≤ t^2 := by nlinarith [sq_abs t,sq_nonneg (|t|-1)]
  have hE : Real.exp (10*d/t^2) ≤ Real.exp 10 :=
    Real.exp_le_exp.mpr ((div_le_iff₀ (by linarith : 0 < t^2)).mpr (by linarith))
  have hQ : 1 ≤ 2*|t| := by linarith
  have hdpre : (1+d)*Real.pi^(-(d/2)) ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 1+d by linarith)
    linarith
  have hpow : (|t|/2)^(d/2) ≤ (2*|t|)^(3/8:ℝ) :=
    (Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ (by linarith))
  have hf' : ‖shiftedZetaQuotient d t‖ ≤ K*(2*|t|)^(3/8:ℝ) := by
    apply hf.trans
    rw [←mul_assoc]
    exact mul_le_mul (mul_le_mul hdpre hE (by positivity) (by norm_num)) hpow (by positivity) (by positivity)
  have he' := he.trans (Real.rpow_le_rpow_of_exponent_le hQ hCr)
  rw [complexDampedZeta,analyticReciprocalZeta_off_one hw,norm_mul,norm_inv,← div_eq_mul_inv]
  have hmul := mul_le_mul hf' he' (div_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
  change ‖riemannZeta (criticalPoint t)/riemannZeta (criticalPoint t+(d:ℂ))‖ *
    (‖riemannZeta (criticalPoint t+(d:ℂ))‖ / ‖riemannZeta (criticalPoint t+z)‖) ≤ _ at hmul
  rw [norm_div] at hmul
  have hcancel : ‖riemannZeta (criticalPoint t)‖ / ‖riemannZeta (criticalPoint t+(d:ℂ))‖ *
      (‖riemannZeta (criticalPoint t+(d:ℂ))‖ / ‖riemannZeta (criticalPoint t+z)‖) =
      ‖riemannZeta (criticalPoint t)‖ / ‖riemannZeta (criticalPoint t+z)‖ := by
    rw [div_eq_mul_inv,div_eq_mul_inv,div_eq_mul_inv]
    calc _ = ‖riemannZeta (criticalPoint t)‖ *
        ((‖riemannZeta (criticalPoint t+(d:ℂ))‖)⁻¹ * ‖riemannZeta (criticalPoint t+(d:ℂ))‖) *
        (‖riemannZeta (criticalPoint t+z)‖)⁻¹ := by ring
      _ = _ := by rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hbase),mul_one]
  rw [hcancel] at hmul
  simpa only [mul_assoc,←Real.rpow_add (by linarith : 0 < 2*|t|),
    show (3/8:ℝ)+1/32=13/32 by norm_num] using hmul

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.complexDampedZeta_neighborhood_high' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms complexDampedZeta_neighborhood_high

end RiemannResearch.RH.Pareto.ResidueMellin
