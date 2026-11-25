import RiemannResearch.RH.ParetoShiftedZetaBudget
import RiemannResearch.RH.ParetoShiftedZetaZeroProfile
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint)

/-- Pointwise limit density at any ordinate, with the actual zero multiplicity. -/
def dampingProfile (a u : ℝ) : ℝ :=
  ‖1-(((u:ℂ)*Complex.I)/(1+(u:ℂ)*Complex.I)) ^ Zeta23.zeroMult (criticalPoint a)‖^2/(1/4+a^2)

/-- Every fixed bounded window on the damping scale has the integral
of the multiplicity profile as its leading coefficient. -/
theorem critical_scaled_window (a L : ℝ) (hL : 0 ≤ L) :
    Tendsto (fun ε : ℝ => (∫ t in a-ε*L..a+ε*L,
      boundarySquare (fun v => 1-shiftedZetaQuotient ε v) t)/ε)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ u in -L..L, dampingProfile a u)) := by
  classical
  let w (ε t : ℝ) := boundarySquare (fun v => 1-shiftedZetaQuotient ε v) t
  let μ : Measure ℝ := volume.restrict (Ioc (-L) L)
  have hab : -L ≤ L := by linarith
  obtain ⟨r,hr,A,hA,hb⟩ := shiftedZetaQuotient_local_bound a
  have he : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < min (1/4) (r/(1+L)) :=
    (gt_mem_nhds (lt_min (by norm_num) (div_pos hr (by linarith)))).filter_mono nhdsWithin_le_nhds
  have loc {ε u : ℝ} (hε : 0 < ε) (hsmall : ε < min (1/4) (r/(1+L))) (hu : u ∈ Icc (-L) L) :
      riemannZeta (criticalPoint (a+ε*u)+(ε:ℂ)) ≠ 0 ∧ w ε (a+ε*u) ≤ 2*A := by
    have hj := (lt_div_iff₀ (show 0 < 1+L by linarith)).mp (lt_of_lt_of_le hsmall (min_le_right _ _))
    have hεr : ε < r := by nlinarith [mul_nonneg hε.le hL]
    have hε1 := lt_of_lt_of_le hsmall (min_le_left _ _)
    have hdist : |a+ε*u-a| < r := by
      rw [add_sub_cancel_left,abs_mul,abs_of_pos hε]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr hu) hε.le).trans_lt (by linarith)
    have hh := hb (a+ε*u) ε hdist hε hεr
    refine ⟨hh.1, hh.2.trans ?_⟩
    have hd : 0 < ε^2+(a+ε*u-a)^2 := by positivity
    have hfrac : ε^2/(ε^2+(a+ε*u-a)^2) ≤ 1 :=
      (div_le_one hd).mpr (by nlinarith [sq_nonneg (a+ε*u-a)])
    have he2 : ε^2 ≤ 1 := by nlinarith [mul_nonneg hε.le (show 0 ≤ 1-ε by linarith)]
    have := mul_le_mul_of_nonneg_left (show ε^2+ε^2/(ε^2+(a+ε*u-a)^2) ≤ 2 by linarith) hA
    linarith only [this]
  have hmeas : ∀ᶠ ε in 𝓝[>] (0:ℝ), AEStronglyMeasurable (fun u => w ε (a+ε*u)) μ := by
    filter_upwards [he,hsmall] with ε hε hs
    have hcont : Continuous (fun u : ℝ => criticalPoint (a+ε*u)) := by unfold criticalPoint; fun_prop
    have hdcont := hcont.add (continuous_const (y := (ε:ℂ)))
    have hn : Continuous (fun u => riemannZeta (criticalPoint (a+ε*u))) :=
      continuous_iff_continuousAt.mpr fun u =>
        (differentiableAt_riemannZeta (MellinFrequency.criticalPoint_ne_one (a+ε*u))).continuousAt.comp (x := u) hcont.continuousAt
    have hd : Continuous (fun u => riemannZeta (criticalPoint (a+ε*u)+(ε:ℂ))) :=
      continuous_iff_continuousAt.mpr fun u =>
        (differentiableAt_riemannZeta (fun h => by
          have hj := congrArg Complex.re h
          simp [MellinFrequency.criticalPoint_re] at hj
          linarith [lt_of_lt_of_le hs (min_le_left _ _)])).continuousAt.comp (x := u) hdcont.continuousAt
    have hquot := hn.continuousOn.div hd.continuousOn
      (fun u hu => (loc hε hs (Ioc_subset_Icc_self hu)).1)
    have ha : ContinuousOn (fun u => w ε (a+ε*u)) (Ioc (-L) L) :=
      ((continuousOn_const.sub hquot).norm.pow 2).div (by fun_prop)
        (fun u _ => by positivity : ∀ u ∈ Ioc (-L) L, 1/4+(a+ε*u)^2 ≠ 0)
    exact ha.aestronglyMeasurable measurableSet_Ioc
  have hbound : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ᵐ u ∂μ, ‖w ε (a+ε*u)‖ ≤ 2*A := by
    filter_upwards [he,hsmall] with ε hε hs
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hw : 0 ≤ w ε (a+ε*u) := by dsimp [w,boundarySquare]; positivity
    rw [Real.norm_eq_abs,abs_of_nonneg hw]
    exact (loc hε hs (Ioc_subset_Icc_self hu)).2
  have hdom := tendsto_integral_filter_of_dominated_convergence
    (F := fun ε u => w ε (a+ε*u)) (f := dampingProfile a) (μ := μ)
    (fun _ => 2*A) hmeas hbound (integrableOn_const (by simp))
    (Eventually.of_forall fun u => shiftedZeta_boundarySquare_scaled_limit a u)
  rw [intervalIntegral.integral_of_le hab]
  apply hdom.congr'
  filter_upwards [he] with ε hε
  change (∫ u in Ioc (-L) L, w ε (a+ε*u)) = (∫ t in a-ε*L..a+ε*L, w ε t)/ε
  rw [←intervalIntegral.integral_of_le hab]
  have hs := intervalIntegral.integral_comp_mul_add (a := -L) (b := L) (w ε) hε.ne' a
  simpa only [add_comm a, mul_neg, neg_add_eq_sub, smul_eq_mul, div_eq_inv_mul] using hs

/-- At a simple critical zero the window integral is explicit. -/
theorem simple_zero_scaled_window (a L : ℝ) (hL : 0 ≤ L)
    (hm : Zeta23.zeroMult (criticalPoint a) = 1) :
    Tendsto (fun ε : ℝ => (∫ t in a-ε*L..a+ε*L,
      boundarySquare (fun v => 1-shiftedZetaQuotient ε v) t)/ε)
      (𝓝[>] (0:ℝ)) (𝓝 ((2*Real.arctan L)/(1/4+a^2))) := by
  have h := critical_scaled_window a L hL
  have hv (u:ℝ) : dampingProfile a u = (1+u^2)⁻¹/(1/4+a^2) :=
    tendsto_nhds_unique (shiftedZeta_boundarySquare_scaled_limit a u) (simple_zero_scaled_boundary a u hm)
  simp_rw [hv] at h
  rw [intervalIntegral.integral_div] at h
  simp_rw [←one_div] at h
  rw [integral_one_div_one_add_sq,Real.arctan_neg] at h
  convert h using 2 <;> ring

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.critical_scaled_window' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms critical_scaled_window

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.simple_zero_scaled_window' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simple_zero_scaled_window

end RiemannResearch.RH.Pareto.ResidueMellin
