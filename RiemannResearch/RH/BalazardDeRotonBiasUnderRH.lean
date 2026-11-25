import RiemannResearch.RH.ParetoShiftedZetaBudget
import RiemannResearch.RH.BalazardDeRotonCriticalEnergy
import RiemannResearch.Analysis.MontgomeryComplexGram

/-! # The corrected Möbius tail and the complete Nyman–Beurling error

The critical-line residual of every finite damped Möbius fit lies in L².
Horizontal comparison under RH supplies the vanishing bias. Consequently the
corrected-tail norm tracks the physical error uniformly in the cutoff.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.BalazardDeRoton

/-- A bounded physical vector has an actual square-integrable Mellin trace
in the angular height convention. -/
theorem angularTrace_memLp (f : ThresholdHilbert) (C : ℝ)
    (hC : ∀ n : ℕ, |hilbertSequence f n| ≤ C) :
    MemLp (fun t => paretoMellin f (criticalPoint t)) 2 := by
  have hf := complexPhysicalStep_finiteEnergy_of_bounded f C hC (by norm_num : (0 : ℝ) < 1/2)
  have hv := WeightedMellin.vertical_memLp hf (σ := 1/2) (by norm_num)
  have hcp : Continuous criticalPoint := by unfold criticalPoint; fun_prop
  have hcont : Continuous (fun t => paretoMellin f (criticalPoint t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ha := WeightedMellin.transform_analyticAt hf (z := criticalPoint t)
      (by rw [criticalPoint_re]; norm_num)
    rw [complexPhysicalStep_transform] at ha
    exact ha.continuousAt.comp hcp.continuousAt
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
  apply (integrable_comp_mul_left_iff _ (by positivity : 2 * Real.pi ≠ 0)).mp
  have hi := (memLp_two_iff_integrable_sq_norm hv.1).mp hv
  simpa only [WeightedMellin.verticalPoint, complexPhysicalStep_transform, criticalPoint,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using hi

/-- The full finite residual has a square-integrable trace for every real
damping parameter and every cutoff, including zero. -/
theorem finite_residual_split_memLp (ε : ℝ) (N : ℕ) :
    MemLp (fun t => bias ε (criticalPoint t) + correctedTail ε N (criticalPoint t)) 2 := by
  simp_rw [← critical_residual_split]
  apply angularTrace_memLp _ (1 + ∑ m ∈ Finset.range N, |dampedMobiusWeight ε (m+1)|)
  intro n
  have he := congrFun (hilbertSequenceLinear.map_sub hilbertOne
    (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N)) n
  change hilbertSequence (_ - _) n = hilbertSequence hilbertOne n -
    hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N) n at he
  rw [he]
  apply (abs_sub _ _).trans
  apply add_le_add _ (dampedMobius_partial_abs_le ε N n)
  rw [hilbertOne_sequence]
  by_cases hn : n = 0 <;> simp [zeroAnchor, hn]

private theorem bias_sq_eq (ε t : ℝ) :
    ‖bias ε (criticalPoint t)‖^2 =
      ResidueMellin.boundarySquare (fun v => 1-ResidueMellin.shiftedZetaQuotient ε v) t := by
  have hs : ‖criticalPoint t‖^2 = 1/4+t^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, criticalPoint_re]
    simp [criticalPoint]
    ring
  change ‖(1-ResidueMellin.shiftedZetaQuotient ε t) / criticalPoint t‖^2 = _
  rw [norm_div, div_pow, hs]
  rfl

/-- Under RH, the bias is square-integrable for all sufficiently small positive
shifts, and so are the corrected tails at every finite cutoff. -/
theorem bias_correctedTail_memLp_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), MemLp (fun t => bias ε (criticalPoint t)) 2 ∧
      ∀ N, MemLp (fun t => correctedTail ε N (criticalPoint t)) 2 := by
  have hi := (ResidueMellin.shiftedZetaQuotient_budget_of_riemannHypothesis hRH).1
  have hpos : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
  have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1/4 := (gt_mem_nhds (by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hi, hpos, hsmall] with ε hi he he'
  have hcn := ResidueMellin.continuous_shiftedZetaQuotient_of_riemannHypothesis hRH he he'.le
  have hcp : Continuous criticalPoint := by unfold criticalPoint; fun_prop
  have hc : Continuous (fun t => bias ε (criticalPoint t)) :=
    (continuous_const.sub hcn).div hcp (fun t => MellinFrequency.criticalPoint_ne_zero t)
  have hb : MemLp (fun t => bias ε (criticalPoint t)) 2 := by
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    simpa only [bias_sq_eq] using hi
  refine ⟨hb, fun N => ?_⟩
  have hs := (finite_residual_split_memLp ε N).sub hb
  change MemLp (fun t => (bias ε (criticalPoint t) + correctedTail ε N (criticalPoint t)) -
    bias ε (criticalPoint t)) 2 at hs
  simpa only [add_sub_cancel_left] using hs

theorem bias_lineEnergy_tendsto_of_riemannHypothesis (hRH : RiemannHypothesis) :
    Tendsto (fun ε => lineEnergy (fun t => bias ε (criticalPoint t))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  simpa only [lineEnergy, bias_sq_eq, mul_zero] using
    (ResidueMellin.shiftedZetaQuotient_budget_of_riemannHypothesis hRH).2.const_mul (1/(2*Real.pi))

/-- At any moving cutoff, the physical residual norm and the corrected
critical-line tail norm differ by a quantity tending to zero under RH. -/
theorem finite_error_sub_correctedTail_tendsto (hRH : RiemannHypothesis) (N : ℝ → ℕ) :
    Tendsto (fun ε => ‖hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (N ε)‖ -
      Real.sqrt (lineEnergy (fun t => correctedTail ε (N ε) (criticalPoint t))))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let k : ℝ := 1/(2*Real.pi)
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hlim := (bias_lineEnergy_tendsto_of_riemannHypothesis hRH).sqrt
  rw [Real.sqrt_zero] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [bias_correctedTail_memLp_of_riemannHypothesis hRH] with ε h
  let b := fun t => bias ε (criticalPoint t)
  let v := fun t => correctedTail ε (N ε) (criticalPoint t)
  have hdiff := RiemannResearch.Analysis.MontgomeryComplexGram.sqrt_energy_reverse_triangle
    (finite_residual_split_memLp ε (N ε)) (h.2 (N ε))
  simp only [add_sub_cancel_right] at hdiff
  have hr := congrArg Real.sqrt (critical_energy ε (N ε))
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hk] at hr
  change ‖‖hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (N ε)‖ -
      Real.sqrt (k * ∫ t, ‖v t‖^2)‖ ≤ Real.sqrt (k * ∫ t, ‖b t‖^2)
  rw [Real.norm_eq_abs, hr, Real.sqrt_mul hk, Real.sqrt_mul hk, ← mul_sub, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left hdiff (Real.sqrt_nonneg _)

/-- Along a prescribed cutoff schedule, convergence of the finite physical
Möbius fits is equivalent under RH to decay of the single corrected tail. -/
theorem damped_fits_tendsto_iff_correctedTail (hRH : RiemannHypothesis) (N : ℝ → ℕ) :
    Tendsto (fun ε => arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (N ε))
      (𝓝[>] (0:ℝ)) (𝓝 hilbertOne) ↔
    Tendsto (fun ε => lineEnergy (fun t => correctedTail ε (N ε) (criticalPoint t)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  let e := fun ε => ‖hilbertOne - arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (N ε)‖
  let a := fun ε => lineEnergy (fun t => correctedTail ε (N ε) (criticalPoint t))
  have hdiff : Tendsto (fun ε => e ε - Real.sqrt (a ε)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    finite_error_sub_correctedTail_tendsto hRH N
  have ha (ε : ℝ) : 0 ≤ a ε := by
    change 0 ≤ (1/(2*Real.pi)) * ∫ t:ℝ, ‖correctedTail ε (N ε) (criticalPoint t)‖^2
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  constructor
  · intro h
    have he : Tendsto e (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [e, norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp h
    have hs : Tendsto (fun ε => Real.sqrt (a ε)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [sub_sub_cancel, sub_zero] using he.sub hdiff
    simpa only [Real.sq_sqrt (ha _), zero_pow (by norm_num : 2 ≠ 0)] using hs.pow 2
  · intro h
    have hs : Tendsto (fun ε => Real.sqrt (a ε)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [Real.sqrt_zero] using h.sqrt
    have he : Tendsto e (𝓝[>] (0:ℝ)) (𝓝 0) := by
      simpa only [sub_add_cancel, add_zero] using hdiff.add hs
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [e, norm_sub_rev] using he

/-- The remaining corrected-tail estimate would put the constant in the
actual squarefree Nyman–Beurling space under RH. -/
theorem squarefreeClosure_of_correctedTail_schedule (hRH : RiemannHypothesis) (N : ℝ → ℕ)
    (h : Tendsto (fun ε => lineEnergy (fun t => correctedTail ε (N ε) (criticalPoint t)))
      (𝓝[>] (0:ℝ)) (𝓝 0)) : hilbertOne ∈ squarefreeCRTSpan.topologicalClosure := by
  exact mem_closure_of_tendsto ((damped_fits_tendsto_iff_correctedTail hRH N).mpr h)
    (Eventually.of_forall fun ε => dampedMobius_partial_mem_squarefreeSpan ε (N ε))

end RiemannResearch.RH.Pareto.BalazardDeRoton


namespace RiemannResearch.RH.Pareto.BalazardDeRoton

/--
info: 'RiemannResearch.RH.Pareto.BalazardDeRoton.finite_error_sub_correctedTail_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finite_error_sub_correctedTail_tendsto


/--
info: 'RiemannResearch.RH.Pareto.BalazardDeRoton.squarefreeClosure_of_correctedTail_schedule' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms squarefreeClosure_of_correctedTail_schedule

end RiemannResearch.RH.Pareto.BalazardDeRoton
