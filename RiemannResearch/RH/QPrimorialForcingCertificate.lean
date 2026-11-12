import RiemannResearch.RH.QPrimorialMatchedGram
import RiemannResearch.RH.QParetoForcingCertificates
import RiemannResearch.Analysis.FiniteHilbertGramEnergyCertificate
import RiemannResearch.Analysis.ExhaustiveProjectionWalk

/-!
# Actual primorial forcing energies and the cofinal certificate obligation

The row is formed from the actual canonical Pareto residual, and the Gram
matrix uses complete Hilbert inner products. The cofinal smallness premise
is explicitly OPEN. This file proves the reduction, not that premise.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QPrimorialForcingCertificate
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer
open QSquarefreePrimorialCofinality QPrimorialMatchedDisplacement QPrimorialMatchedGram
open QParetoEquivalence QParetoClosedProjectionComparison QParetoForcingCertificates
open QSquarefreeDisplacementRigidity
open RiemannResearch.Analysis.FiniteHilbertGram

def stageForcing (n : ℕ) : ThresholdHilbert := forcing (paretoStage n) qOne

def forcingRow (n : ℕ) : DivisorIndex n → ℝ :=
  cross (paretoDivisorAtom n) (reciprocalD (toPareto (qOne-pOptimizer n)))

theorem paretoDivisor_span (n : ℕ) :
    synthesisSpan (paretoDivisorAtom n) = paretoStage n := by
  unfold synthesisSpan paretoStage paretoDivisorAtom
  rw [← divisor_span_eq_primorialStage]
  exact (map_span_range _).symm

/-- Exactly zᵀG⁻¹z for the full canonical primorial dictionary. -/
theorem stageForcing_energy (n : ℕ) :
    ‖stageForcing n‖ ^ 2 = dualEnergy (paretoDivisorAtom_independent n) (forcingRow n) := by
  have h := projection_norm_sq_dual (paretoDivisorAtom_independent n)
    (reciprocalD (toPareto (qOne-pOptimizer n)))
  simpa only [paretoDivisor_span, stageForcing, forcing, forcingRow, pOptimizer] using h


/-- An unconditional baseline endpoint for every complete primorial stage. -/
theorem stageForcing_energy_le (n : ℕ) :
    dualEnergy (paretoDivisorAtom_independent n) (forcingRow n) ≤ pError n / 4 := by
  have h := forcing_energy_le_quarter (paretoStage n) qOne
  change 4 * ‖stageForcing n‖ ^ 2 ≤ pError n at h
  rw [stageForcing_energy] at h
  linarith

theorem stageForcing_energy_le_one_quarter (n : ℕ) :
    dualEnergy (paretoDivisorAtom_independent n) (forcingRow n) ≤ (1/4:ℝ) :=
  (stageForcing_energy_le n).trans (by linarith [pError_le_one n])

/-- The full signed row e-Jc_P; the coefficient solve is the actual Pareto solve. -/
theorem forcingRow_signed (n : ℕ) (i : DivisorIndex n) :
    forcingRow n i =
      inner ℝ (paretoDivisorAtom n i) (reciprocalD (toPareto qOne)) -
        ∑ j, paretoCoefficients n j *
          inner ℝ (paretoDivisorAtom n i) (reciprocalD (paretoDivisorAtom n j)) := by
  have hs : Fintype.linearCombination ℝ (paretoDivisorAtom n) (paretoCoefficients n) =
      (paretoStage n).starProjection (toPareto qOne) := by
    simpa only [paretoDivisor_span, paretoCoefficients] using
      synthesis_inverseCoeff_eq_projection (paretoDivisorAtom_independent n) (toPareto qOne)
  unfold forcingRow cross pOptimizer
  rw [toPareto_sub, toPareto_pFit, ← hs]
  simp only [map_sub, inner_sub_right, Fintype.linearCombination_apply,
    map_sum, map_smul, inner_sum, real_inner_smul_right]

theorem stageForcing_inexact_energy (n : ℕ) (c : DivisorIndex n → ℝ) :
    ‖stageForcing n‖ ^ 2 =
      2 * (∑ i, c i * forcingRow n i) -
        (∑ i, c i * gram (paretoDivisorAtom n) c i) +
        dualEnergy (paretoDivisorAtom_independent n)
          (forcingRow n-gram (paretoDivisorAtom n) c) := by
  rw [stageForcing_energy]
  exact inexact_dualEnergy (paretoDivisorAtom_independent n) _ c

/-- Finite forcing controls the actual finite displacement in the same metric. -/
theorem stageDisplacement_norm_le (n : ℕ) :
    ‖toPareto (stageDisplacement n)‖ ≤ ‖stageForcing n‖ :=
  (correction_norm_bounds (primorialStage n) (paretoStage n)
    (toPareto_mem_stage_iff n) qOne).2


/-- The Pareto gain of the actual nested primorial spaces. -/
def paretoGain (n : ℕ) : ℝ :=
  ‖toPareto (pOptimizer (n+1)-pOptimizer n)‖ ^ 2

theorem pareto_error_step (n : ℕ) :
    pError n = pError (n+1) + paretoGain n := by
  have h := RiemannResearch.Analysis.ExhaustiveWalk.nested_projection_energy
    (paretoStage n) (paretoStage (n+1))
    (Submodule.map_mono (primorialStage_mono (Nat.le_succ n))) (toPareto qOne)
  simpa only [pError, paretoGain, pOptimizer, toPareto_sub, toPareto_pFit] using h

/-- Changes of prime projection are already included in these complete gains. -/
theorem pareto_accumulated_gain (N : ℕ) :
    (∑ n ∈ Finset.range N, paretoGain n) = pError 0-pError N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    linarith [pareto_error_step N]

theorem pareto_accumulated_gain_tendsto :
    Tendsto (fun N => ∑ n ∈ Finset.range N, paretoGain n) atTop
      (𝓝 (pError 0-‖toPareto pResidual‖ ^ 2)) := by
  simp only [pareto_accumulated_gain]
  exact tendsto_const_nhds.sub pError_tendsto

/-- Arbitrarily small certified energies at arbitrarily late stages suffice.
This arithmetic premise is not a consequence of CRT or compactness. -/
theorem displacement_zero_of_cofinal_energy
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, ‖stageForcing n‖ ^ 2 < ε) :
    displacement = 0 := by
  have ht : Tendsto (fun n => ‖toPareto (stageDisplacement n)‖) atTop
      (𝓝 ‖toPareto displacement‖) :=
    ((toParetoCLM.continuous.tendsto _).comp stageDisplacement_tendsto).norm
  have hn : ‖toPareto displacement‖ = 0 := by
    by_contra hzero
    have hp : 0 < ‖toPareto displacement‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have he := ht.eventually (lt_mem_nhds (half_lt_self hp))
    have hf := hsmall ((‖toPareto displacement‖/2)^2) (sq_pos_of_pos (half_pos hp))
    obtain ⟨n, hn, hgt⟩ := (hf.and_eventually he).exists
    have hb := stageDisplacement_norm_le n
    nlinarith [norm_nonneg (toPareto (stageDisplacement n)),
      norm_nonneg (stageForcing n)]
  apply paretoEquiv.injective
  simpa only [paretoEquiv_apply, map_zero] using norm_eq_zero.mp hn

/-- An explicit endpoint interface for the still-open arithmetic provider. -/
theorem riemannHypothesis_of_cofinal_upper_endpoints (A : ℕ → ℝ)
    (hcert : ∀ n, dualEnergy (paretoDivisorAtom_independent n) (forcingRow n) ≤ A n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop, A n < ε) :
    RiemannHypothesis := by
  have hd := displacement_zero_of_cofinal_energy (fun ε hε =>
    (hsmall ε hε).mono fun n hn => (by
      rw [stageForcing_energy]
      exact (hcert n).trans_lt hn))
  apply riemannHypothesis_of_displacement_bounded 0
  intro k
  rw [hd]
  cases k <;> simp [qSequence]

end RiemannResearch.RH.QPrimorialForcingCertificate
