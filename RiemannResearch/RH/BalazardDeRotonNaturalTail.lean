import RiemannResearch.RH.BalazardDeRotonChargeLimit
import RiemannResearch.RH.BalazardDeRotonBiasUnderRH

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.RH.Pareto.BalazardDeRoton

/-- The angular critical line trace of the fractional part is genuinely in L². -/
theorem zeta_div_criticalPoint_memLp :
    MemLp (fun t => riemannZeta (criticalPoint t) / criticalPoint t) 2 := by
  have hc : Continuous criticalPoint := by unfold criticalPoint; fun_prop
  have h1 (t : ℝ) : criticalPoint t ≠ 1 := fun h => by
    have he := congrArg Complex.re h
    rw [criticalPoint_re, Complex.one_re] at he
    norm_num at he
  have h0 (t : ℝ) : criticalPoint t ≠ 0 := fun h => by
    have he := congrArg Complex.re h
    rw [criticalPoint_re, Complex.zero_re] at he
    norm_num at he
  have hz : Continuous (fun t => riemannZeta (criticalPoint t)) := continuous_iff_continuousAt.mpr
    fun t => (differentiableAt_riemannZeta (h1 t)).continuousAt.comp hc.continuousAt
  apply (memLp_two_iff_integrable_sq_norm (hz.div hc h0).aestronglyMeasurable).mpr
  have hid := RiemannResearch.RH.PrimeTreeScalingEnergy.critical_integral
  change (∫ t, ‖riemannZeta (criticalPoint t) / criticalPoint t‖ ^ 2) = _ at hid
  have hpos : 0 < Real.log (2 * Real.pi) - Real.eulerMascheroniConstant := by
    rw [← StepCorrectionNorm.residueEnergy_eq_log_two_pi_sub_gamma, StepCorrectionNorm.residueEnergy]
    have ht : 0 ≤ ∑' m, StepCorrectionNorm.rawResidueCellEnergy m :=
      tsum_nonneg StepCorrectionNorm.rawResidueCellEnergy_nonneg
    linarith
  by_contra hn
  change ¬ Integrable (fun t => ‖riemannZeta (criticalPoint t) / criticalPoint t‖ ^ 2) at hn
  rw [integral_undef hn] at hid
  exact (ne_of_gt (mul_pos (by positivity : 0 < 2*Real.pi) hpos)) hid.symm

/-- Under RH a divergent schedule need only control the paper's natural
reciprocal-zeta truncation, with its uncentered coefficients. -/
theorem damped_fits_tendsto_iff_naturalTail (hRH : RiemannHypothesis) (N : ℝ → ℕ)
    (hN : Tendsto N (𝓝[>] (0:ℝ)) atTop) :
    Tendsto (fun ε => arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (N ε))
      (𝓝[>] (0:ℝ)) (𝓝 hilbertOne) ↔
    Tendsto (fun ε => lineEnergy (fun t => naturalTruncationTail ε (N ε) (criticalPoint t)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  rw [damped_fits_tendsto_iff_correctedTail hRH N]
  let c (ε t : ℝ) := correctedTail ε (N ε) (criticalPoint t)
  let a (ε t : ℝ) := naturalTruncationTail ε (N ε) (criticalPoint t)
  let k := 1/(2*Real.pi)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hen (f : ℝ → ℂ) : 0 ≤ lineEnergy f :=
    mul_nonneg hk (integral_nonneg fun _ => sq_nonneg _)
  have lim := (corrected_natural_tail_distance_tendsto N hN).sqrt
  rw [Real.sqrt_zero] at lim
  have hdiff : Tendsto (fun ε => Real.sqrt (lineEnergy (c ε))-Real.sqrt (lineEnergy (a ε)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm' _ lim
    filter_upwards [bias_correctedTail_memLp_of_riemannHypothesis hRH] with ε hε
    have hc : MemLp (c ε) 2 := hε.2 (N ε)
    have hd := zeta_div_criticalPoint_memLp.const_mul (charge ε (N ε))
    have he (t : ℝ) : a ε t = c ε t -
        charge ε (N ε) * (riemannZeta (criticalPoint t) / criticalPoint t) := by
      unfold a c correctedTail naturalTruncationTail
      ring
    have ha : MemLp (a ε) 2 := by
      have id : a ε = c ε - (fun t => charge ε (N ε) * (riemannZeta (criticalPoint t) / criticalPoint t)) :=
        funext he
      rw [id]
      exact hc.sub hd
    have hj := RiemannResearch.Analysis.MontgomeryComplexGram.sqrt_energy_reverse_triangle hc ha
    change ‖Real.sqrt (k * ∫ t, ‖c ε t‖^2) - Real.sqrt (k * ∫ t, ‖a ε t‖^2)‖ ≤
      Real.sqrt (k * ∫ t, ‖c ε t - a ε t‖^2)
    simp only [Real.sqrt_mul hk, ← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left hj (Real.sqrt_nonneg _)
  constructor
  · intro h
    have hc : Tendsto (fun ε => Real.sqrt (lineEnergy (c ε))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [Real.sqrt_zero] using h.sqrt
    have ha : Tendsto (fun ε => Real.sqrt (lineEnergy (a ε))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [sub_sub_cancel, sub_zero] using hc.sub hdiff
    simpa only [Real.sq_sqrt (hen _), zero_pow (by norm_num : 2 ≠ 0)] using ha.pow 2
  · intro h
    have ha : Tendsto (fun ε => Real.sqrt (lineEnergy (a ε))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [Real.sqrt_zero] using h.sqrt
    have hc : Tendsto (fun ε => Real.sqrt (lineEnergy (c ε))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [sub_add_cancel, add_zero] using hdiff.add ha
    simpa only [Real.sq_sqrt (hen _), zero_pow (by norm_num : 2 ≠ 0)] using hc.pow 2

end RiemannResearch.RH.Pareto.BalazardDeRoton

namespace RiemannResearch.RH.Pareto.BalazardDeRoton

/--
info: 'RiemannResearch.RH.Pareto.BalazardDeRoton.damped_fits_tendsto_iff_naturalTail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms damped_fits_tendsto_iff_naturalTail

end RiemannResearch.RH.Pareto.BalazardDeRoton
