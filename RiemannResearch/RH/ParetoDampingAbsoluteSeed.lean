import RiemannResearch.RH.ParetoDampedTraceLimit
import RiemannResearch.RH.BalazardDeRotonAbsoluteTail

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint criticalPoint_re criticalPoint_ne_zero criticalPoint_ne_one)
open RiemannResearch.Analysis.RHInteriorLogDerivative
open BalazardDeRoton (naturalTruncationTail polynomial charge partial_mellin_of_pos
  zeta_div_criticalPoint_memLp natural_tail_energy_tendsto_of_half_lt
  naturalTruncationTail_memLp_of_half_lt polynomial_reciprocal_error_le)

private theorem charge_tendsto_seed {d : ℝ} (hd : 0 < d) :
    Tendsto (charge d) atTop (𝓝 (analyticReciprocalZeta (1+(d:ℂ)))) := by
  have hs : 1+(d:ℂ) ≠ 1 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  rw [analyticReciprocalZeta_off_one hs,Metric.tendsto_nhds]
  intro δ hδ
  have ht := ((tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop).div_const d
  have hlim : ∀ᶠ N : ℕ in atTop, (N:ℝ)^(-d)/d < δ := by
    have hval : Tendsto (fun N : ℕ => (N:ℝ)^(-d)/d) atTop (𝓝 0) := by simpa using ht
    exact hval.eventually (gt_mem_nhds hδ)
  filter_upwards [eventually_ge_atTop 1,hlim] with N hN hlim
  rw [dist_comm,dist_eq_norm, show charge d N = polynomial d N 1 by simp [charge,polynomial,Complex.cpow_neg,div_eq_mul_inv]]
  have h := polynomial_reciprocal_error_le d 1 (by simp;linarith) hN
  rw [Complex.one_re,show 1-(d+1) = -d by ring,add_sub_cancel_right] at h
  exact h.trans_lt hlim

/-- Orthogonality to the finite squarefree fits kills the centered trace
on the full interval of absolute convergence for the critical-line series. -/
theorem centeredTraceTest_seed_of_finite_annihilation {d : ℝ} (hd : 1/2 < d)
    {Y : ℝ → ℂ} (hY : MemLp Y 2)
    (hfinite : ∀ N, (∫ t, Y t*paretoMellin (arithmeticFloorHilbertPartial
      (dampedMobiusWeight d) N) (criticalPoint t)) = 0) :
    centeredTraceTest Y (d:ℂ) = 0 := by
  let F (N:ℕ) (t:ℝ) := naturalTruncationTail d N (criticalPoint t)
  let G (N:ℕ) (t:ℝ) := paretoMellin (arithmeticFloorHilbertPartial (dampedMobiusWeight d) N) (criticalPoint t)
  let Z (t:ℝ) := riemannZeta (criticalPoint t)/criticalPoint t
  have hZ : MemLp Z 2 := zeta_div_criticalPoint_memLp
  have hG N : MemLp (G N) 2 := BalazardDeRoton.angularTrace_memLp _ _ (dampedMobius_partial_abs_le d N)
  have hw1 t : criticalPoint t+(d:ℂ) ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    rw [Complex.add_re,criticalPoint_re,Complex.ofReal_re,Complex.one_re] at hh
    linarith
  have hf t N : dampedTrace (d:ℂ) t = F N t + G N t + charge d N * Z t := by
    rw [dampedTrace,complexDampedZeta,analyticReciprocalZeta_off_one (hw1 t)]
    dsimp [F,G,Z,naturalTruncationTail]
    rw [partial_mellin_of_pos _ _ _ (by rw [criticalPoint_re];norm_num),
      dampedHardyMobiusSum_eq_zeta _ _ _ (by rw [criticalPoint_re];norm_num) (criticalPoint_ne_one t)]
    dsimp [polynomial,charge]
    ring
  have hF : ∀ᶠ N in atTop, MemLp (F N) 2 :=
    (eventually_ge_atTop 1).mono fun N hN => naturalTruncationTail_memLp_of_half_lt hd hN
  have hlim := test_tendsto_zero_of_lineEnergy hY hF (natural_tail_energy_tendsto_of_half_lt hd)
  have hc := (charge_tendsto_seed (by linarith : 0 < d)).mul_const (fractionalTraceTest Y)
  have hx := hlim.add hc
  have hid : (fun N => (∫ t, Y t*F N t)+charge d N*fractionalTraceTest Y) =ᶠ[atTop]
      fun _ => dampedTraceTest Y (d:ℂ) := by
    filter_upwards [hF] with N hFN
    unfold fractionalTraceTest dampedTraceTest
    have he (t:ℝ) : Y t*dampedTrace (d:ℂ) t = (Y t*F N t+Y t*G N t)+charge d N*(Y t*Z t) := by rw [hf];ring
    simp_rw [he]
    have iF : Integrable (fun t => Y t*F N t) := hY.integrable_mul hFN
    have iG : Integrable (fun t => Y t*G N t) := hY.integrable_mul (hG N)
    have iZ : Integrable (fun t => Y t*Z t) := hY.integrable_mul hZ
    have iFG : Integrable (fun t => Y t*F N t + Y t*G N t) := iF.add iG
    have iCZ : Integrable (fun t => charge d N*(Y t*Z t)) := iZ.const_mul _
    rw [integral_add iFG iCZ, integral_add iF iG,integral_const_mul,
      show (∫ t, Y t*G N t) = 0 from hfinite N,add_zero]
  have hzero := tendsto_nhds_unique tendsto_const_nhds (hx.congr' hid)
  rw [centeredTraceTest,show dampedTraceTest Y (d:ℂ) = analyticReciprocalZeta (1+(d:ℂ))*fractionalTraceTest Y by simpa using hzero,sub_self]

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.centeredTraceTest_seed_of_finite_annihilation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms centeredTraceTest_seed_of_finite_annihilation

end RiemannResearch.RH.Pareto.ResidueMellin
