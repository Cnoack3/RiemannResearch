import RiemannResearch.RH.ParetoDampingTraceMajorant
import RiemannResearch.Analysis.DominatedHolomorphicTest
import RiemannResearch.RH.BalazardDeRotonNaturalTail

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint criticalPoint_re criticalPoint_ne_zero criticalPoint_ne_one)
open RiemannResearch.Analysis.RHInteriorLogDerivative

def dampedTraceTest (Y : ℝ → ℂ) (z : ℂ) : ℂ := ∫ t, Y t * dampedTrace z t

def fractionalTraceTest (Y : ℝ → ℂ) : ℂ := ∫ t, Y t*(riemannZeta (criticalPoint t)/criticalPoint t)

def centeredTraceTest (Y : ℝ → ℂ) (z : ℂ) : ℂ :=
  dampedTraceTest Y z - analyticReciprocalZeta (1+z)*fractionalTraceTest Y

private theorem hasDerivAt_trace (hRH : RiemannHypothesis) {z : ℂ} (hz : 0 < z.re) (t : ℝ) :
    HasDerivAt (fun w => dampedTrace w t)
      (riemannZeta (criticalPoint t)/criticalPoint t *
        deriv analyticReciprocalZeta (criticalPoint t+z)) z := by
  have ha := analyticAt_reciprocalZeta_of_riemannHypothesis hRH (s := criticalPoint t+z)
    (by rw [Complex.add_re,criticalPoint_re];linarith)
  have h := (ha.differentiableAt.hasDerivAt.comp z ((hasDerivAt_id z).const_add (criticalPoint t))).const_mul
    (riemannZeta (criticalPoint t)/criticalPoint t)
  have hsame : (fun w => dampedTrace w t) = fun w =>
      riemannZeta (criticalPoint t)/criticalPoint t * analyticReciprocalZeta (criticalPoint t+w) := by
    funext w
    dsimp [dampedTrace,complexDampedZeta]
    ring
  rw [hsame]
  simpa only [Function.comp_def, mul_one] using h

theorem analyticAt_dampedTraceTest (hRH : RiemannHypothesis) {d : ℝ} (hd : 0 < d)
    (hd' : d ≤ 3/4) {Y : ℝ → ℂ} (hY : MemLp Y 2) :
    AnalyticAt ℂ (dampedTraceTest Y) (d:ℂ) := by
  obtain ⟨r,hr,H,hH,hb⟩ := dampedTrace_local_memLp_majorant hRH hd hd'
  have hs : Continuous criticalPoint := by unfold criticalPoint; fun_prop
  have hz : Continuous (fun t => riemannZeta (criticalPoint t)) := continuous_iff_continuousAt.mpr
    fun t => (differentiableAt_riemannZeta (criticalPoint_ne_one t)).continuousAt.comp (x := t) hs.continuousAt
  have hf := hz.div hs criticalPoint_ne_zero
  apply RiemannResearch.Analysis.DominatedHolomorphicTest.analyticAt_parameter_integral
    (r := r) (M := fun t => ‖Y t‖*H t) hr (hY.norm.integrable_mul hH)
  · intro w hw
    have hcont : Continuous (dampedTrace w) := continuous_iff_continuousAt.mpr fun t =>
      (continuousAt_dampedTrace hRH (hb w hw).1 t).comp (x := t) (continuous_const.prodMk continuous_id).continuousAt
    exact hY.1.mul hcont.aestronglyMeasurable
  · intro w hw
    have hp : Continuous (fun t => deriv analyticReciprocalZeta (criticalPoint t+w)) :=
      continuous_iff_continuousAt.mpr fun t => by
        have ha := analyticAt_reciprocalZeta_of_riemannHypothesis hRH
          (s := criticalPoint t+w) (by rw [Complex.add_re,criticalPoint_re]; linarith [(hb w hw).1])
        have hs' : Continuous (fun v : ℝ => criticalPoint v+w) := hs.add continuous_const
        exact ContinuousAt.comp (g := deriv analyticReciprocalZeta) (f := fun v : ℝ => criticalPoint v+w)
          ha.deriv.continuousAt hs'.continuousAt
    have he (t:ℝ) := ((hasDerivAt_trace hRH (hb w hw).1 t).const_mul (Y t)).deriv
    simp_rw [he]
    exact hY.1.mul (hf.mul hp).aestronglyMeasurable
  · exact fun t w hw => ((hasDerivAt_trace hRH (hb w hw).1 t).const_mul (Y t)).differentiableAt
  · exact Eventually.of_forall fun t w hw => (norm_mul _ _).le.trans
      (mul_le_mul_of_nonneg_left ((hb w hw).2 t) (norm_nonneg _))

/-- A physical squarefree test that vanishes on the interval of absolute
convergence continues through every positive damping below three quarters. -/
theorem centeredTraceTest_zero_by_continuation (hRH : RiemannHypothesis)
    {Y : ℝ → ℂ} (hY : MemLp Y 2)
    (hseed : ∀ d ∈ Ioo (1/2:ℝ) (3/4), centeredTraceTest Y (d:ℂ) = 0) :
    ∀ d ∈ Ioo (0:ℝ) (3/4), centeredTraceTest Y (d:ℂ) = 0 := by
  have hloc : AnalyticOnNhd ℝ (fun d : ℝ => centeredTraceTest Y (d:ℂ)) (Ioo 0 (3/4)) := by
    intro d hd
    have hT := analyticAt_dampedTraceTest hRH hd.1 hd.2.le hY
    have hA := (analyticAt_reciprocalZeta_of_riemannHypothesis hRH (s := 1+(d:ℂ))
      (by simpa using (show (1/2:ℝ) < 1+d by linarith [hd.1]))).comp (analyticAt_const.add analyticAt_id)
    have hcol : AnalyticAt ℂ (centeredTraceTest Y) (d:ℂ) := hT.sub (hA.mul analyticAt_const)
    exact (show AnalyticAt ℝ (centeredTraceTest Y) (d:ℂ) from hcol.restrictScalars).comp (Complex.ofRealCLM.analyticAt d)
  have h5 : (5/8:ℝ) ∈ Ioo 0 (3/4) := ⟨by norm_num,by norm_num⟩
  have hh : (fun d : ℝ => centeredTraceTest Y (d:ℂ)) =ᶠ[𝓝 (5/8:ℝ)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (5/8:ℝ) ∈ Ioo (1/2) (3/4) from ⟨by norm_num,by norm_num⟩)] with d hd
    exact hseed d hd
  exact fun d hd => hloc.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo h5 hh hd

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.centeredTraceTest_zero_by_continuation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms centeredTraceTest_zero_by_continuation

end RiemannResearch.RH.Pareto.ResidueMellin
