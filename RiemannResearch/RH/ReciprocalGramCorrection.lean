import RiemannResearch.RH.ResidueGramModeIdentities
import RiemannResearch.RH.ResidueGramMobiusCorrection
import RiemannResearch.RH.CanonicalMobiusPNT

/-!
# A scalar limit of the growing inverse-Gram correction

Source: independent assembly of the project's exact finite Gram identities,
continuous first-coordinate evaluation, and classical PNT provider,
24 September 2026. No mathematical novelty is claimed.

The reciprocal-weighted correction converges unconditionally to minus the
first physical coordinate of the actual residual. This computes one growing
weighted sum without interchanging a limit with the inverse matrices.
Its zero-limit condition is equivalent to residual vanishing; a nonnegative
limit is an explicit conditional research reduction to RH. No provider of
that sign condition is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
open TailCapacity

def reciprocalCorrection (n : ℕ) : ℝ :=
  dotProduct (reciprocalSource n) (correctionVector n)

theorem reciprocalMobius_dot (n : ℕ) :
    1 + dotProduct (reciprocalSource n) (mobiusVector n) =
      mobiusReciprocalSum (n + 1) := by
  induction n with
  | zero => norm_num [dotProduct, mobiusReciprocalSum]
  | succ n ih =>
    simp only [dotProduct, reciprocalSource, mobiusVector] at ih ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [mobiusReciprocalSum_succ]
    rw [← ih]
    simp only [Nat.add_assoc]
    ring

theorem reciprocalCorrection_eq_firstCoordinate (n : ℕ) :
    reciprocalCorrection n =
      anchoredEvaluationCLM 1 (projection n) + mobiusReciprocalSum (n + 1) - 1 := by
  have hp : dotProduct (reciprocalSource n) (canonicalVector n) =
      anchoredEvaluationCLM 1 (projection n) := by
    rw [projection_firstCoordinate_eq_inverseGram]
    rw [canonicalVector, source, constant_cross_eq_logarithmicSource]
  rw [reciprocalCorrection, correctionVector_eq, dotProduct_add, hp]
  have hm := reciprocalMobius_dot n
  linarith

theorem reciprocalCorrection_tendsto :
    Tendsto reciprocalCorrection atTop (𝓝 (-hilbertSequence limitResidual 1)) := by
  have hp := (anchoredEvaluationCLM 1).continuous.tendsto limitProjection |>.comp projection_tendsto
  have hm := mobiusReciprocalSum_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  have hlim := (hp.add hm).sub_const 1
  have he : anchoredEvaluationCLM 1 limitProjection + 0 - 1 =
      -hilbertSequence limitResidual 1 := by
    have hone : anchoredEvaluationCLM 1 hilbertOne = 1 := by
      rw [anchoredEvaluationCLM_apply, hilbertOne_sequence]
      norm_num [zeroAnchor]
    rw [← anchoredEvaluationCLM_apply 1 limitResidual]
    change anchoredEvaluationCLM 1 limitProjection + 0 - 1 =
      -anchoredEvaluationCLM 1 (hilbertOne - limitProjection)
    rw [map_sub, hone]
    ring
  simpa only [Function.comp_def, ← reciprocalCorrection_eq_firstCoordinate, he] using hlim

theorem reciprocalCorrection_zero_iff_residual_zero :
    Tendsto reciprocalCorrection atTop (𝓝 0) ↔ limitResidual = 0 := by
  constructor
  · intro h
    have he := tendsto_nhds_unique reciprocalCorrection_tendsto h
    apply firstCoordinate_zero_iff_residual_zero.mp
    linarith
  · intro h
    simpa [h, hilbertSequence] using reciprocalCorrection_tendsto

theorem reciprocalCorrection_limit_bounds :
    -(2 + Real.sqrt 2) * limitEnergy ≤ -hilbertSequence limitResidual 1 ∧
      -hilbertSequence limitResidual 1 ≤ -(2 - Real.sqrt 2) * limitEnergy := by
  have h := firstCoordinate_energy_bounds
  constructor <;> nlinarith [h.1, h.2]

theorem riemannHypothesis_of_reciprocalCorrection_tendsto_nonneg
    {L : ℝ} (hL : 0 ≤ L)
    (hlim : Tendsto reciprocalCorrection atTop (𝓝 L)) : RiemannHypothesis := by
  have he := tendsto_nhds_unique reciprocalCorrection_tendsto hlim
  apply riemannHypothesis_of_firstCoordinate_zero
  have hn := firstCoordinate_nonneg
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
