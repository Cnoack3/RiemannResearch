import RiemannResearch.RH.ParetoCompactCutoffLimits
import RiemannResearch.RH.ParetoCompactSourceLimits
import RiemannResearch.Analysis.FiniteSpectralDependentEscape

/-!
# Actual complete-source spectral limits and RH tightness consumer

Source: the user-provided Green--Pareto--Schur continuation, Appendix C.
All finite source data are CONSTRUCTED from the entire actual legal stage.
Head error decay and optimizer-tail decay are unconditional. Complete-source
tightness remains the explicit arithmetic provider.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis
open FiniteSpectralBudget FiniteHeadTailSpectralRealization

/-- Every eigenvector in the full conductor stage is retained. -/
abbrev compactSpectrumIndex (n : ℕ) :=
  Fin (Module.finrank ℝ (stageHeadSpace (n+3) (n+4)))

def compactSpectrumWeight (n : ℕ) : compactSpectrumIndex n → ℝ :=
  sourceWeight (stageSpectralHead (n+3) (n+4) (by omega)) twoThreeDual

def compactSpectrumEigenvalue (n : ℕ) : compactSpectrumIndex n → ℝ :=
  stageEigenvalue (n+3) (n+4) (by omega)

def compactProjectionDefect : ℝ :=
  ‖twoThreeDual - closedSpace.starProjection twoThreeDual‖^2

theorem compactSpectrumWeight_nonneg (n : ℕ) (i : compactSpectrumIndex n) :
    0 ≤ compactSpectrumWeight n i := sq_nonneg _

theorem compactSpectrumEigenvalue_nonneg (n : ℕ) (i : compactSpectrumIndex n) :
    0 ≤ compactSpectrumEigenvalue n i :=
  eigenvalue_nonneg (stageTailLift (n+3) (n+4) (by omega)) i

/-- The whole physical tail of the complete optimizer vanishes, without RH. -/
theorem compactSpectrum_optimizerTail_tendsto_zero :
    Tendsto (fun n => optimizerTail Finset.univ
      (compactSpectrumWeight n) (compactSpectrumEigenvalue n)) atTop (𝓝 0) := by
  have h := actualOptimizer_physicalTail_energy_tendsto_zero twoThreeDual
    (fun n => n+3) (fun n => n+4)
    (tendsto_add_atTop_nat 3) (tendsto_add_atTop_nat 4)
  have he (n : ℕ) := actualOptimizerTail_eq_spectral (n+3) (n+4) (by omega)
    twoThreeDual (compactHead_twoThreeDual (n+4) (by omega))
  simpa only [he, compactSpectrumWeight, compactSpectrumEigenvalue] using h

/-- Exact complete correction limit, obtained by subtracting the vanishing
physical head error from the actual full projection residual energy. -/
theorem compactSpectrum_correction_tendsto_defect :
    Tendsto (fun n => correction Finset.univ
      (compactSpectrumWeight n) (compactSpectrumEigenvalue n))
      atTop (𝓝 compactProjectionDefect) := by
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖^2)
      atTop (𝓝 compactProjectionDefect) :=
    ExhaustiveWalk.walkError_tendsto residueAtom id Function.surjective_id twoThreeDual
  have hd := hd0.comp (tendsto_add_atTop_nat 3)
  have he (n : ℕ) : correction Finset.univ
      (compactSpectrumWeight n) (compactSpectrumEigenvalue n) =
        ‖twoThreeDualResidual (n+3)‖^2 -
          ‖twoThreeDual - (stageHeadSpace (n+3) (n+4)).starProjection twoThreeDual‖^2 := by
    have h := actualProjectionError_eq_headError_add_correction (n+3) (n+4) (by omega)
      twoThreeDual (compactHead_twoThreeDual (n+4) (by omega))
    change ‖twoThreeDualResidual (n+3)‖^2 = _ at h
    dsimp [compactSpectrumWeight, compactSpectrumEigenvalue]
    linarith only [h]
  have ht := hd.sub twoThree_actualHeadError_tendsto_zero
  simpa only [Function.comp_def, he, sub_zero] using ht

/-- Escaped mass at EVERY fixed positive threshold converges to the actual
closed-span defect; the literal source is never supplied as a hypothesis. -/
theorem compactSpectrum_highMass_tendsto_defect (R : ℝ) (hR : 0 < R) :
    Tendsto (fun n => highMass Finset.univ
      (compactSpectrumWeight n) (compactSpectrumEigenvalue n) R)
      atTop (𝓝 compactProjectionDefect) :=
  dependent_highMass_tendsto compactSpectrumIndex compactSpectrumWeight
    compactSpectrumEigenvalue compactProjectionDefect R compactSpectrumWeight_nonneg
    compactSpectrumEigenvalue_nonneg hR compactSpectrum_correction_tendsto_defect
    compactSpectrum_optimizerTail_tendsto_zero

/-- Exact identification with closure membership; this does not assert an
unformalized RH-to-density converse. -/
theorem compactSpectrum_tight_iff_one_mem_closedSpace :
    DependentSourceTightAtInfinity compactSpectrumIndex compactSpectrumWeight
      compactSpectrumEigenvalue ↔ hilbertOne ∈ closedSpace := by
  rw [dependent_sourceTightAtInfinity_iff_defect_zero compactSpectrumIndex
    compactSpectrumWeight compactSpectrumEigenvalue compactProjectionDefect
    compactSpectrumWeight_nonneg compactSpectrumEigenvalue_nonneg
    compactSpectrum_correction_tendsto_defect compactSpectrum_optimizerTail_tendsto_zero]
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖^2)
      atTop (𝓝 compactProjectionDefect) :=
    ExhaustiveWalk.walkError_tendsto residueAtom id Function.surjective_id twoThreeDual
  rw [← twoThreeDual_error_tendsto_zero_iff_one_mem]
  constructor
  · intro hz
    simpa only [hz] using hd0
  · intro hz
    exact tendsto_nhds_unique hd0 hz

/-- The only remaining input is actual complete-source tightness. -/
theorem riemannHypothesis_of_actual_compactSpectrum_tight
    (htight : DependentSourceTightAtInfinity compactSpectrumIndex
      compactSpectrumWeight compactSpectrumEigenvalue) : RiemannHypothesis := by
  have hm := compactSpectrum_tight_iff_one_mem_closedSpace.mp htight
  exact riemannHypothesis_of_twoThreeDual_error_tendsto_zero
    (twoThreeDual_error_tendsto_zero_iff_one_mem.mpr hm)

/-- Sharp coefficient-one double-log obstruction for the literal complete
Pareto source. It asserts an eventual lower floor without postulating a limit
of the normalized moment. -/
theorem compactSpectrum_doubleLog_lower_floor
    (sigma : ℕ → ℝ) (hsigma : Tendsto sigma atTop (𝓝 0))
    (hpos : ∀ n, 0 < sigma n) (hone : ∀ n, sigma n < 1)
    (htail : ∀ n, optimizerTail Finset.univ (compactSpectrumWeight n)
      (compactSpectrumEigenvalue n) ≤ sigma n) :
    ∀ c : ℝ, c < compactProjectionDefect → ∀ᶠ n in atTop,
      c < moment Finset.univ (compactSpectrumWeight n)
        (compactSpectrumEigenvalue n) doubleLog /
          Real.log (1 + Real.log (1 / sigma n)) :=
  dependent_eventually_lt_relative_doubleLog_moment_of_envelope
    compactSpectrumIndex compactSpectrumWeight compactSpectrumEigenvalue
    compactProjectionDefect sigma compactSpectrumWeight_nonneg
    compactSpectrumEigenvalue_nonneg compactSpectrum_correction_tendsto_defect
    hsigma hpos hone htail

/-- Any fixed strict fraction is enough on the sharp double-log scale.
The normalized moment need not tend to zero as an independent premise. -/
theorem riemannHypothesis_of_actual_compactSpectrum_doubleLog_feedback
    (sigma E : ℕ → ℝ) (theta : ℝ)
    (hsigma : Tendsto sigma atTop (𝓝 0))
    (hpos : ∀ n, 0 < sigma n) (hone : ∀ n, sigma n < 1)
    (htail : ∀ n, optimizerTail Finset.univ (compactSpectrumWeight n)
      (compactSpectrumEigenvalue n) ≤ sigma n)
    (htheta : theta < 1) (hE : Tendsto E atTop (𝓝 0))
    (hbudget : ∀ᶠ n in atTop,
      moment Finset.univ (compactSpectrumWeight n) (compactSpectrumEigenvalue n) doubleLog /
        Real.log (1 + Real.log (1 / sigma n)) ≤
          E n + theta * correction Finset.univ
            (compactSpectrumWeight n) (compactSpectrumEigenvalue n)) : RiemannHypothesis := by
  have hz := dependent_defect_eq_zero_of_relative_doubleLog_feedback
    compactSpectrumIndex compactSpectrumWeight compactSpectrumEigenvalue
    compactProjectionDefect theta sigma E compactSpectrumWeight_nonneg
    compactSpectrumEigenvalue_nonneg compactSpectrum_correction_tendsto_defect
    hsigma hpos hone htail htheta hE hbudget
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖^2)
      atTop (𝓝 compactProjectionDefect) :=
    ExhaustiveWalk.walkError_tendsto residueAtom id Function.surjective_id twoThreeDual
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  simpa only [hz] using hd0


/-- The head-displacement square has the full limiting defect. The vanishing
optimizer-tail square is retained in the exact identity before taking limits. -/
theorem compactSpectrum_headDisplacement_tendsto_defect :
    Tendsto (fun n => headDisplacement Finset.univ
      (compactSpectrumWeight n) (compactSpectrumEigenvalue n))
      atTop (𝓝 compactProjectionDefect) := by
  have he (n : ℕ) : headDisplacement Finset.univ
      (compactSpectrumWeight n) (compactSpectrumEigenvalue n) =
      correction Finset.univ (compactSpectrumWeight n) (compactSpectrumEigenvalue n) -
        optimizerTail Finset.univ (compactSpectrumWeight n) (compactSpectrumEigenvalue n) := by
    have h := correction_eq_headDisplacement_add_optimizerTail Finset.univ
      (compactSpectrumWeight n) (compactSpectrumEigenvalue n)
      (fun i _ => compactSpectrumEigenvalue_nonneg n i)
    linarith only [h]
  simpa only [he, sub_zero] using
    compactSpectrum_correction_tendsto_defect.sub compactSpectrum_optimizerTail_tendsto_zero

/-- A canonical positive envelope is built from the literal complete physical
optimizer-tail square. No convergence rate or arithmetic bound is presumed. -/
def compactSpectrumTailEnvelope (n : ℕ) : ℝ :=
  optimizerTail Finset.univ (compactSpectrumWeight n) (compactSpectrumEigenvalue n) +
    1 / ((n : ℝ) + 1)

theorem compactSpectrumTailEnvelope_pos (n : ℕ) :
    0 < compactSpectrumTailEnvelope n := by
  have hS := optimizerTail_nonneg Finset.univ
    (compactSpectrumWeight n) (compactSpectrumEigenvalue n)
    (fun i _ => compactSpectrumWeight_nonneg n i)
    (fun i _ => compactSpectrumEigenvalue_nonneg n i)
  have hinv : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  dsimp [compactSpectrumTailEnvelope]
  linarith

theorem compactSpectrum_optimizerTail_le_envelope (n : ℕ) :
    optimizerTail Finset.univ (compactSpectrumWeight n)
      (compactSpectrumEigenvalue n) ≤ compactSpectrumTailEnvelope n := by
  unfold compactSpectrumTailEnvelope
  have hinv : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem compactSpectrumTailEnvelope_tendsto_zero :
    Tendsto compactSpectrumTailEnvelope atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun n => optimizerTail Finset.univ
    (compactSpectrumWeight n) (compactSpectrumEigenvalue n) +
      1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  simpa only [add_zero] using compactSpectrum_optimizerTail_tendsto_zero.add hinv

/-- The sharp normalized moment obstruction now uses an internally
constructed envelope, with no additional geometric hypotheses. -/
theorem compactSpectrum_canonical_doubleLog_lower_floor :
    ∀ c : ℝ, c < compactProjectionDefect → ∀ᶠ n in atTop,
      c < moment Finset.univ (compactSpectrumWeight n)
        (compactSpectrumEigenvalue n) doubleLog /
          Real.log (1 + Real.log (1 / compactSpectrumTailEnvelope n)) :=
  dependent_eventually_lt_relative_doubleLog_moment_of_eventual_envelope
    compactSpectrumIndex compactSpectrumWeight compactSpectrumEigenvalue
    compactProjectionDefect compactSpectrumTailEnvelope
    compactSpectrumWeight_nonneg compactSpectrumEigenvalue_nonneg
    compactSpectrum_correction_tendsto_defect compactSpectrumTailEnvelope_tendsto_zero
    (Filter.Eventually.of_forall compactSpectrumTailEnvelope_pos)
    (compactSpectrumTailEnvelope_tendsto_zero.eventually_lt_const zero_lt_one)
    (Filter.Eventually.of_forall compactSpectrum_optimizerTail_le_envelope)

/-- Actual sequence-to-RH consumer with no tail-envelope provider.
Only the strict normalized arithmetic moment budget remains. It need hold
on just a cofinal sequence and retains every source weight and correction. -/
theorem riemannHypothesis_of_actual_compactSpectrum_cofinal_canonical_feedback
    (k : ℕ → ℕ) (E : ℕ → ℝ) (theta : ℝ)
    (hk : Tendsto k atTop atTop) (htheta : theta < 1)
    (hE : Tendsto E atTop (𝓝 0))
    (hbudget : ∀ᶠ n in atTop,
      moment Finset.univ (compactSpectrumWeight (k n))
        (compactSpectrumEigenvalue (k n)) doubleLog /
          Real.log (1 + Real.log (1 / compactSpectrumTailEnvelope (k n))) ≤
        E n + theta * correction Finset.univ
          (compactSpectrumWeight (k n)) (compactSpectrumEigenvalue (k n))) :
    RiemannHypothesis := by
  have hz := dependent_defect_eq_zero_of_cofinal_relative_doubleLog_feedback
    compactSpectrumIndex compactSpectrumWeight compactSpectrumEigenvalue
    compactProjectionDefect theta compactSpectrumTailEnvelope E k
    compactSpectrumWeight_nonneg compactSpectrumEigenvalue_nonneg
    compactSpectrum_correction_tendsto_defect compactSpectrumTailEnvelope_tendsto_zero
    (Filter.Eventually.of_forall compactSpectrumTailEnvelope_pos)
    (compactSpectrumTailEnvelope_tendsto_zero.eventually_lt_const zero_lt_one)
    (Filter.Eventually.of_forall compactSpectrum_optimizerTail_le_envelope)
    hk htheta hE hbudget
  have hd0 : Tendsto (fun n => ‖twoThreeDualResidual n‖^2)
      atTop (𝓝 compactProjectionDefect) :=
    ExhaustiveWalk.walkError_tendsto residueAtom id Function.surjective_id twoThreeDual
  apply riemannHypothesis_of_twoThreeDual_error_tendsto_zero
  simpa only [hz] using hd0

end RiemannResearch.RH.Pareto.CoefficientStabilization
