import RiemannResearch.RH.ParetoDampedTraceTest
import RiemannResearch.Analysis.RemoteLaplaceTail

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint criticalPoint_re criticalPoint_ne_zero criticalPoint_ne_one)
open RiemannResearch.Analysis.RHInteriorLogDerivative
open MeasureTheory.RemoteLaplaceTail (norm_integral_mul_sq_le)
open BalazardDeRoton (bias lineEnergy bias_lineEnergy_tendsto_of_riemannHypothesis
  bias_correctedTail_memLp_of_riemannHypothesis)

theorem test_tendsto_zero_of_lineEnergy {Y : ℝ → ℂ} (hY : MemLp Y 2)
    {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℂ} (hF : ∀ᶠ i in l, MemLp (F i) 2)
    (hE : Tendsto (fun i => lineEnergy (F i)) l (𝓝 0)) :
    Tendsto (fun i => ∫ t, Y t*F i t) l (𝓝 0) := by
  let K := (∫ t, ‖Y t‖^2)*(2*Real.pi)
  have hl := (hE.const_mul K).sqrt
  rw [mul_zero,Real.sqrt_zero] at hl
  apply squeeze_zero_norm' _ hl
  filter_upwards [hF] with i hi
  have h := norm_integral_mul_sq_le hY hi
  have h' : ‖∫ t, Y t*F i t‖^2 ≤ K*lineEnergy (F i) := by
    apply h.trans_eq
    dsimp [K,lineEnergy]
    field_simp [ne_of_gt Real.pi_pos] <;> ring
  change ‖∫ t, Y t * F i t‖ ≤ Real.sqrt (K * lineEnergy (F i))
  simpa only [Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt h'

/-- The continued, centered reciprocal-zeta pairing converges to the pairing
against the physical constant as the damping decreases to zero. -/
theorem centeredTraceTest_tendsto_constant (hRH : RiemannHypothesis)
    {Y : ℝ → ℂ} (hY : MemLp Y 2) :
    Tendsto (fun d : ℝ => centeredTraceTest Y (d:ℂ)) (𝓝[>] 0)
      (𝓝 (∫ t, Y t*(1/criticalPoint t))) := by
  have hunit : MemLp (fun t => 1/criticalPoint t) 2 := by
    have he (t:ℝ) := paretoMellin_one_of_pos (criticalPoint t) (by rw [criticalPoint_re];norm_num)
    have h := BalazardDeRoton.angularTrace_memLp hilbertOne 1
      RiemannResearch.RH.ParetoResidualBoundaryEnergy.hilbertOne_sequence_bound
    change MemLp (fun t => paretoMellin hilbertOne (criticalPoint t)) 2 at h
    simpa only [he] using h
  have hF := (bias_correctedTail_memLp_of_riemannHypothesis hRH).mono fun d hd => hd.1
  have h0 := test_tendsto_zero_of_lineEnergy hY hF (bias_lineEnergy_tendsto_of_riemannHypothesis hRH)
  have hq : Tendsto (fun d : ℝ => dampedTraceTest Y (d:ℂ)) (𝓝[>] 0)
      (𝓝 (∫ t, Y t*(1/criticalPoint t))) := by
    have h := (tendsto_const_nhds (x := ∫ t, Y t*(1/criticalPoint t))).sub h0
    rw [sub_zero] at h
    apply h.congr'
    have h1 : ∀ᶠ d in 𝓝[>] (0:ℝ), d < 1/4 := (gt_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds
    filter_upwards [h1,hF] with d hd hf
    have huI : Integrable (fun t => Y t*(1/criticalPoint t)) := hY.integrable_mul hunit
    have hfI : Integrable (fun t => Y t*bias d (criticalPoint t)) := hY.integrable_mul hf
    change (∫ t, Y t*(1/criticalPoint t)) - (∫ t, Y t*bias d (criticalPoint t)) = _
    rw [← integral_sub huI hfI]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    have hs : criticalPoint t+(d:ℂ) ≠ 1 := by
      intro he
      have hh := congrArg Complex.re he
      rw [Complex.add_re, criticalPoint_re,Complex.ofReal_re,Complex.one_re] at hh
      linarith
    change Y t*(1/criticalPoint t)-Y t*bias d (criticalPoint t) = Y t*dampedTrace (d:ℂ) t
    dsimp [dampedTrace,complexDampedZeta,bias]
    rw [analyticReciprocalZeta_off_one hs]
    ring
  have hc : Tendsto (fun d : ℝ => analyticReciprocalZeta (1+(d:ℂ))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc := hasDerivAt_analyticReciprocalZeta_one.continuousAt.tendsto
    have hs : Continuous (fun d : ℝ => 1+(d:ℂ)) := by fun_prop
    have h1 : Tendsto (fun d : ℝ => 1+(d:ℂ)) (𝓝[>] 0) (𝓝 1) := by
      simpa only [Complex.ofReal_zero,add_zero] using (hs.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    simpa only [Function.comp_def,analyticReciprocalZeta_one] using hc.comp h1
  simpa [centeredTraceTest] using hq.sub (hc.mul_const (fractionalTraceTest Y))

theorem target_pairing_zero_of_absolute_seed (hRH : RiemannHypothesis) {Y : ℝ → ℂ} (hY : MemLp Y 2)
    (hseed : ∀ d ∈ Ioo (1/2:ℝ) (3/4), centeredTraceTest Y (d:ℂ) = 0) :
    (∫ t, Y t*(1/criticalPoint t)) = 0 := by
  have hz : (fun d : ℝ => centeredTraceTest Y (d:ℂ)) =ᶠ[𝓝[>] 0] fun _ => 0 := by
    filter_upwards [(self_mem_nhdsWithin : ∀ᶠ d in 𝓝[>] (0:ℝ), 0 < d),
      (gt_mem_nhds (by norm_num : (0:ℝ) < 3/4)).filter_mono nhdsWithin_le_nhds] with d h0 h1
    exact centeredTraceTest_zero_by_continuation hRH hY hseed d ⟨h0,h1⟩
  exact tendsto_nhds_unique ((centeredTraceTest_tendsto_constant hRH hY).congr' hz) tendsto_const_nhds

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.target_pairing_zero_of_absolute_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms target_pairing_zero_of_absolute_seed

end RiemannResearch.RH.Pareto.ResidueMellin
