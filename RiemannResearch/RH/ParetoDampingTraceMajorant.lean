import RiemannResearch.RH.ParetoComplexDampingNeighborhood
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint criticalPoint_re criticalPoint_ne_zero criticalPoint_ne_one)
open RiemannResearch.Analysis.RHInteriorLogDerivative

def dampedTrace (z : ℂ) (t : ℝ) : ℂ := complexDampedZeta z t / criticalPoint t

set_option maxHeartbeats 700000 in
-- Composition on the complex and real product uses both scalar instances.
theorem continuousAt_dampedTrace (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    ContinuousAt (fun p : ℂ × ℝ => dampedTrace p.1 p.2) (z,t) := by
  have hs : Continuous (fun p : ℂ × ℝ => criticalPoint p.2) := by unfold criticalPoint; fun_prop
  have ha := analyticAt_reciprocalZeta_of_riemannHypothesis hRH
    (s := criticalPoint t+z) (by rw [Complex.add_re,criticalPoint_re];linarith)
  have hshift : Continuous (fun p : ℂ × ℝ => criticalPoint p.2+p.1) := hs.add continuous_fst
  have hn : ContinuousAt (fun p : ℂ × ℝ => riemannZeta (criticalPoint p.2)) (z,t) :=
    ContinuousAt.comp (g := riemannZeta) (f := fun p : ℂ × ℝ => criticalPoint p.2)
      (differentiableAt_riemannZeta (criticalPoint_ne_one t)).continuousAt hs.continuousAt
  have hr : ContinuousAt (fun p : ℂ × ℝ => analyticReciprocalZeta (criticalPoint p.2+p.1)) (z,t) :=
    ContinuousAt.comp (g := analyticReciprocalZeta) (f := fun p : ℂ × ℝ => criticalPoint p.2+p.1)
      ha.continuousAt hshift.continuousAt
  exact (hn.mul hr).div hs.continuousAt (criticalPoint_ne_zero t)

private theorem high_trace_bound {u v : ℝ} (hu : 3 ≤ u) (hv : u ≤ v) :
    (2*u)^(13/32:ℝ) / v ≤ 4*(1+u)^(-(19/32:ℝ)) := by
  have hu0 : 0 < u := by linarith
  have hp : (2*u)^(13/32:ℝ) ≤ 2*u^(13/32:ℝ) := by
    rw [Real.mul_rpow (by norm_num) hu0.le]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2:ℝ)) (show (13/32:ℝ) ≤ 1 by norm_num)
  have hcmp : u^(-(19/32:ℝ)) ≤ 2*(1+u)^(-(19/32:ℝ)) := by
    have ht : (1+u)^(19/32:ℝ) ≤ 2*u^(19/32:ℝ) := by
      apply (Real.rpow_le_rpow (by linarith) (show 1+u ≤ 2*u by linarith) (by norm_num)).trans
      rw [Real.mul_rpow (by norm_num) hu0.le]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : 1 ≤ (2:ℝ)) (show (19/32:ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_neg hu0.le, Real.rpow_neg (by linarith : 0 ≤ 1+u)]
    rwa [←one_div,←div_eq_mul_inv,div_le_div_iff₀ (Real.rpow_pos_of_pos hu0 _) (Real.rpow_pos_of_pos (by linarith) _),one_mul]
  calc
    _ ≤ (2*u^(13/32:ℝ))/u := div_le_div₀ (by positivity) hp hu0 hv
    _ = 2*u^(-(19/32:ℝ)) := by
      calc
        _ = 2 * (u^(13/32:ℝ)/u^(1:ℝ)) := by rw [Real.rpow_one,mul_div_assoc]
        _ = _ := by rw [←Real.rpow_sub hu0];norm_num
    _ ≤ _ := by linarith only [hcmp]

private theorem decay_memLp : MemLp (fun t : ℝ => (1+|t|)^(-(19/32:ℝ))) 2 := by
  have hf : Continuous (fun t : ℝ => (1+|t|)^(-(19/32:ℝ))) := by
    apply Continuous.rpow_const (by fun_prop)
    exact fun t => Or.inl (by positivity)
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  have hi := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 19/16)
    (by rw [Module.finrank_self]; norm_num)
  refine hi.mono' ((hf.norm.pow 2).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
  change ‖‖(1+|t|)^(-(19/32:ℝ))‖^2‖ ≤ (1+‖t‖^2)^(-(19/16:ℝ)/2)
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖(1+|t|)^(-(19/32:ℝ))‖),Real.norm_eq_abs,sq_abs]
  rw [←Real.rpow_mul_natCast (by positivity : 0 ≤ 1+|t|)]
  have hun : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [abs_nonneg t,sq_abs t]
  have hb := Real.rpow_le_rpow_of_nonpos (show 0 < 1+t^2 by positivity) hun (show (-(19/16:ℝ)/2) ≤ 0 by norm_num)
  rw [←Real.rpow_natCast (1+|t|) 2,←Real.rpow_mul (by positivity),Nat.cast_ofNat] at hb
  simpa only [Real.norm_eq_abs,sq_abs,
    show (-(19/32:ℝ))*(2:ℕ)=2*(-(19/16:ℝ)/2) by norm_num] using hb

/-- Uniform Hilbert-space majorant on a parameter disc about every real
damping center between zero and three quarters. -/
theorem dampedTrace_local_memLp_majorant (hRH : RiemannHypothesis) {d : ℝ} (hd : 0 < d)
    (hd' : d ≤ 3/4) : ∃ r > 0, ∃ H : ℝ → ℝ, MemLp H 2 ∧
      ∀ z ∈ Metric.ball (d:ℂ) r, 0 < z.re ∧ ∀ t : ℝ, ‖dampedTrace z t‖ ≤ H t := by
  obtain ⟨r,hr,K,hK,hb⟩ := complexDampedZeta_neighborhood_high hRH hd hd'
  let q := min (d/2) (r/2)
  have hq : 0 < q := lt_min (by linarith) (by linarith)
  let S := Metric.closedBall (d:ℂ) q ×ˢ Icc (-3:ℝ) 3
  have hz {z:ℂ} (hz : z ∈ Metric.closedBall (d:ℂ) q) : 0 < z.re := by
    have h := (Complex.abs_re_le_norm (z-(d:ℂ))).trans (by simpa [Metric.mem_closedBall,dist_eq_norm] using hz)
    rw [Complex.sub_re,Complex.ofReal_re] at h
    linarith [(abs_le.mp h).1,show q ≤ d/2 from min_le_left _ _]
  have hc : ContinuousOn (fun p : ℂ × ℝ => dampedTrace p.1 p.2) S :=
    fun p hp => (continuousAt_dampedTrace hRH (hz hp.1) p.2).continuousWithinAt
  obtain ⟨B,hB⟩ := ((isCompact_closedBall (d:ℂ) q).prod isCompact_Icc).exists_bound_of_continuousOn hc
  let H (t:ℝ) := (Icc (-3:ℝ) 3).indicator (fun _ => |B|) t + (4*K)*(1+|t|)^(-(19/32:ℝ))
  refine ⟨q,hq,H,?_,?_⟩
  · have hbox : MemLp ((Icc (-3:ℝ) 3).indicator (fun _ => |B|)) 2 := by
      apply memLp_indicator_const 2 measurableSet_Icc
      exact Or.inr (by simp)
    exact hbox.add (decay_memLp.const_mul (4*K))
  intro z hzb
  have hzc := Metric.ball_subset_closedBall hzb
  refine ⟨hz hzc,?_⟩
  intro t
  by_cases ht : t ∈ Icc (-3:ℝ) 3
  · simp only [H, Set.indicator_of_mem ht]
    have h1 := hB (z,t) ⟨hzc,ht⟩
    exact (h1.trans (le_abs_self _)).trans (le_add_of_nonneg_right (by positivity))
  · have ht' : 3 ≤ |t| := le_of_not_gt fun h => ht ⟨(abs_lt.mp h).1.le,(abs_lt.mp h).2.le⟩
    have hnr : |t| ≤ ‖criticalPoint t‖ := by simpa [criticalPoint] using Complex.abs_im_le_norm (criticalPoint t)
    have hzb' : z ∈ Metric.ball (d:ℂ) r := Metric.ball_subset_ball (by have := min_le_right (d/2) (r/2); dsimp [q]; linarith) hzb
    simp only [H,Set.indicator_of_notMem ht,zero_add,dampedTrace,norm_div]
    apply (div_le_div_of_nonneg_right (hb z hzb' t ht') (norm_nonneg _)).trans
    rw [mul_div_assoc, mul_comm 4 K, mul_assoc]
    exact mul_le_mul_of_nonneg_left (high_trace_bound ht' hnr) hK.le

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.dampedTrace_local_memLp_majorant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dampedTrace_local_memLp_majorant

end RiemannResearch.RH.Pareto.ResidueMellin
