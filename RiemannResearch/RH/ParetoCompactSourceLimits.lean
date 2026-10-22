import RiemannResearch.RH.CompactCorrectedTrialWindow
import RiemannResearch.RH.ParetoActualHeadSpectrum
import RiemannResearch.RH.ParetoTrialTailConditions
import RiemannResearch.RH.MobiusReciprocalChargeBridge
import Mathlib.Topology.Algebra.Order.Field

/-!
# Unconditional compact source and physical head limits

Source: the user-provided Green--Pareto--Schur continuation, Sections 13 and
Appendix C, and the actual sequence assembly requested on 6 October 2026.
The PNT supplies only reciprocal charge decay, not complete-tail tightness.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem compactReciprocalSum_eq_dilations (N : ℕ) :
    compactReciprocalSum N = 14 * mobiusReciprocalSum N -
      13 * mobiusReciprocalSum (N / 2) + 3 * mobiusReciprocalSum (N / 4) := by
  unfold compactReciprocalSum
  simp_rw [compactShiftedMobius_formula, add_div, sub_div, mul_div_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    reciprocal_dilation_sum N 2 (by decide) (fun d => (ArithmeticFunction.moebius d : ℝ)),
    reciprocal_dilation_sum N 4 (by decide) (fun d => (ArithmeticFunction.moebius d : ℝ))]
  change 14 * mobiusReciprocalSum N -
      26 * ((1 / (2 : ℝ)) * mobiusReciprocalSum (N / 2)) +
      12 * ((1 / (4 : ℝ)) * mobiusReciprocalSum (N / 4)) = _
  ring

private theorem cutoff_div_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => N / d) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b * d)] with N hN
  exact (Nat.le_div_iff_mul_le hd).mpr hN

/-- The actual shifted compact source charge decays without an RH premise. -/
theorem compactReciprocalSum_tendsto_zero :
    Tendsto compactReciprocalSum atTop (𝓝 0) := by
  have h2 := mobiusReciprocalSum_tendsto_zero.comp (cutoff_div_tendsto 2 (by decide))
  have h4 := mobiusReciprocalSum_tendsto_zero.comp (cutoff_div_tendsto 4 (by decide))
  have h := ((mobiusReciprocalSum_tendsto_zero.const_mul 14).sub
    (h2.const_mul 13)).add (h4.const_mul 3)
  change Tendsto (fun N => compactReciprocalSum N) atTop (𝓝 0)
  simpa only [Function.comp_def, compactReciprocalSum_eq_dilations, mul_zero, sub_zero, add_zero] using h

/-- The exact corrected compact lift uses no conductor beyond N. -/
theorem compactCorrectedHilbert_mem_conductorStage
    (N : ℕ) (hN : 0 < N) : compactCorrectedHilbert N hN ∈ finiteSpace (N-1) := by
  unfold compactCorrectedHilbert
  apply (finiteSpace (N-1)).add_mem
  · apply (finiteSpace (N-1)).neg_mem
    apply (finiteSpace (N-1)).sum_mem
    intro d hd
    apply (finiteSpace (N-1)).smul_mem
    apply normalizedResidueHilbert_mem_finiteSpace
    have hh := (Finset.mem_Icc.mp d.property).2
    omega
  · apply (finiteSpace (N-1)).smul_mem
    exact normalizedResidueHilbert_mem_finiteSpace (N-1) N hN (by omega)

theorem compactCorrectedHilbert_head_energy_le_charge_sq
    (N : ℕ) (hN : 0 < N) :
    ‖compactHead N (twoThreeDual - compactCorrectedHilbert N hN)‖^2 ≤
      (compactReciprocalSum N)^2 := by
  rw [compactCorrectedHilbert_head_norm_sq_eq_boundary]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) * ((N : ℝ)+1) := by positivity
  unfold positiveWeight
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg (compactReciprocalSum N)]

/-- Best approximation in the actual head image, compared with a full-stage
legal trial. The trial's complete physical head is retained. -/
theorem stageHead_error_le_legal_trial (n N : ℕ) (v u : ThresholdHilbert)
    (hv : compactHead N v = v) (hu : u ∈ finiteSpace n) :
    ‖v - (stageHeadSpace n N).starProjection v‖^2 ≤
      ‖compactHead N (v-u)‖^2 := by
  let y := (stageHeadSpace n N).starProjection v
  have hQu : compactHead N u ∈ stageHeadSpace n N := ⟨⟨u,hu⟩,rfl⟩
  have hy : y ∈ stageHeadSpace n N := (stageHeadSpace n N).starProjection_apply_mem v
  have ho : inner ℝ (v-y) (y-compactHead N u) = 0 := by
    rw [real_inner_comm]
    exact ((stageHeadSpace n N).mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal v) _
      ((stageHeadSpace n N).sub_mem hy hQu)
  have he : v-compactHead N u = (v-y)+(y-compactHead N u) := by abel
  rw [compactHead_sub, hv, he, norm_add_sq_real, ho]
  change ‖v-y‖^2 ≤ ‖v-y‖^2 + 2*0 + ‖y-compactHead N u‖^2
  nlinarith [sq_nonneg ‖y-compactHead N u‖]

/-- All arithmetic needed for compact head-projection decay is supplied by
the already proved PNT reciprocal cancellation. -/
theorem twoThree_actualHeadError_tendsto_zero :
    Tendsto (fun n => ‖twoThreeDual -
      (stageHeadSpace (n+3) (n+4)).starProjection twoThreeDual‖^2)
      atTop (𝓝 0) := by
  have hcharge : Tendsto (fun n => (compactReciprocalSum (n+4))^2)
      atTop (𝓝 0) := by
    simpa using (compactReciprocalSum_tendsto_zero.comp
      (tendsto_add_atTop_nat 4)).pow 2
  apply squeeze_zero (fun n => sq_nonneg _) _ hcharge
  intro n
  have hmem := compactCorrectedHilbert_mem_conductorStage (n+4) (by omega)
  have hbest := stageHead_error_le_legal_trial (n+3) (n+4) twoThreeDual
    (compactCorrectedHilbert (n+4) (by omega))
    (compactHead_twoThreeDual (n+4) (by omega))
    (by simpa only [show n+4-1=n+3 by omega] using hmem)
  exact hbest.trans (compactCorrectedHilbert_head_energy_le_charge_sq (n+4) (by omega))

end RiemannResearch.RH.Pareto.CoefficientStabilization
