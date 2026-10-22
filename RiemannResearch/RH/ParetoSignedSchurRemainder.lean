import RiemannResearch.RH.ParetoPointClosure
import RiemannResearch.RH.ParetoCoordinateEvaluation
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import RiemannResearch.Analysis.ResidualHarmonicGain
import RiemannResearch.RH.ParetoResidueMoments

/-!
# The exact signed fixed-head remainder and its RH consumer

Source: `RH_Exact_Signed_Schur_Remainder_2026-09-16.tex`.
All energies below are norms in the actual complete Pareto space. For a packet
whose physical first coordinate is one, the remainder is total energy minus
one half. Normal equations give the signed Schur subtraction exactly.

For any positive decreasing sequence of these actual remainders, relative
gains are defined from the remainders, not supplied as an independent model.
Their nonsummability implies Mathlib's RH when the packets are legal. No
arithmetic lower bound on those gains or RH-to-density converse is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra
open RiemannResearch.Analysis.ResidualGain

def fixedHeadRemainder (F : ThresholdHilbert) : ℝ := ‖F - paretoPointHilbert 0‖ ^ 2

theorem fixedHeadRemainder_pos_of_legal (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (F : ThresholdHilbert) (hF : F ∈ hilbertLegalSubspace A) :
    0 < fixedHeadRemainder F := by
  apply pow_pos
  apply norm_pos_iff.mpr
  intro he
  have heq := sub_eq_zero.mp he
  exact paretoPoint_zero_not_mem_legalSubspace A hA (heq ▸ hF)

theorem paretoPoint_zero_inner (F : ThresholdHilbert) :
    inner ℝ F (paretoPointHilbert 0) = (1 / 2 : ℝ) * hilbertSequence F 1 := by
  rw [inner_paretoPoint]
  simp [paretoWeight, hilbertGibbsPhysical, hilbertSequence]

theorem paretoPoint_zero_norm_sq : ‖paretoPointHilbert 0‖ ^ 2 = (1 / 2 : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, paretoPoint_zero_inner, hilbertSequence_paretoPoint]
  norm_num [paretoPointSequence]

theorem fixedHeadRemainder_eq_energy_sub_half (F : ThresholdHilbert)
    (hhead : hilbertSequence F 1 = 1) :
    fixedHeadRemainder F = ‖F‖ ^ 2 - 1 / 2 := by
  unfold fixedHeadRemainder
  rw [norm_sub_sq_real, paretoPoint_zero_norm_sq, paretoPoint_zero_inner, hhead]
  ring

/-- Exact one-dimensional projection distance for a unit-head packet. In a
Schur application the old zero-head controls are orthogonal to both targets. -/
theorem fixedHead_projection_distance_sq (F : ThresholdHilbert)
    (hhead : hilbertSequence F 1 = 1) :
    ‖schurRemove F (paretoPointHilbert 0)‖ ^ 2 =
      fixedHeadRemainder F / (1 + 2 * fixedHeadRemainder F) := by
  have hr : 0 ≤ fixedHeadRemainder F := sq_nonneg _
  have he := fixedHeadRemainder_eq_energy_sub_half F hhead
  have hF : F ≠ 0 := by
    intro hz
    subst F
    norm_num [hilbertSequence] at hhead
  rw [schurRemove_norm_sq _ F hF, paretoPoint_zero_norm_sq,
    real_inner_comm F (paretoPointHilbert 0), paretoPoint_zero_inner, hhead]
  have hn : ‖F‖ ^ 2 = fixedHeadRemainder F + 1 / 2 := by linarith
  rw [hn]
  field_simp
  ring

/-- The manuscript's initial packet is the actual binary remainder. -/
def fixedHeadSeed : ThresholdHilbert := digitHilbert 2 1 (by norm_num) (by norm_num)

theorem fixedHeadSeed_sequence : hilbertSequence fixedHeadSeed = residue 2 := by
  simpa only [fixedHeadSeed, hilbertDilation_one, dilation_one] using
    hilbertDilation_digit_one_sequence 2 1 (by norm_num) (by norm_num)

theorem fixedHeadSeed_first : hilbertSequence fixedHeadSeed 1 = 1 := by
  rw [fixedHeadSeed_sequence]
  norm_num [residue]

theorem fixedHeadSeed_norm_sq : ‖fixedHeadSeed‖ ^ 2 = Real.log 2 := by
  rw [← real_inner_self_eq_norm_sq, hilbert_inner_weighted,
    fixedHeadSeed_sequence, paretoInner_residue_two]

theorem fixedHeadSeed_legal : fixedHeadSeed ∈ hilbertLegalSubspace {2, 3} := by
  change hilbertSequence fixedHeadSeed ∈ legalSeedSpan {2, 3}
  rw [fixedHeadSeed_sequence]
  apply Submodule.subset_span
  exact ⟨2, by simp, 1, by norm_num, (dilation_one (residue 2)).symm⟩

variable {ι : Type*} [Fintype ι]

theorem finiteSchurResidual_first_coordinate (h : ThresholdHilbert)
    (z : ι → ThresholdHilbert) (c : ι → ℝ)
    (hh : hilbertSequence h 1 = 1) (hz : ∀ i, hilbertSequence (z i) 1 = 0) :
    hilbertSequence (finiteSchurResidual h z c) 1 = 1 := by
  rw [← physicalEvaluationCLM_apply 0]
  simp only [finiteSchurResidual, finiteSchurCombination, map_sub, map_sum, map_smul,
    physicalEvaluationCLM_apply, hh, hz, smul_eq_mul, mul_zero, Finset.sum_const_zero, sub_zero]

theorem finiteSchurResidual_mem_legal (A : Set ℕ) (h : ThresholdHilbert)
    (z : ι → ThresholdHilbert) (c : ι → ℝ)
    (hh : h ∈ hilbertLegalSubspace A) (hz : ∀ i, z i ∈ hilbertLegalSubspace A) :
    finiteSchurResidual h z c ∈ hilbertLegalSubspace A := by
  exact (hilbertLegalSubspace A).sub_mem hh
    ((hilbertLegalSubspace A).sum_mem (fun i _ => (hilbertLegalSubspace A).smul_mem _ (hz i)))

/-- Signed Schur subtraction for the actual fixed-head remainder. -/
theorem fixedHeadRemainder_schur_value (h : ThresholdHilbert)
    (z : ι → ThresholdHilbert) (c : ι → ℝ)
    (hh : hilbertSequence h 1 = 1) (hz : ∀ i, hilbertSequence (z i) 1 = 0)
    (hc : ∀ i, inner ℝ (z i) (finiteSchurCombination z c) = inner ℝ (z i) h) :
    fixedHeadRemainder (finiteSchurResidual h z c) =
      ‖h‖ ^ 2 - 1 / 2 - ∑ i, c i * inner ℝ (z i) h := by
  rw [fixedHeadRemainder_eq_energy_sub_half _
    (finiteSchurResidual_first_coordinate h z c hh hz), finiteSchurResidual_norm_sq h z c hc]
  ring

theorem fixedHeadRemainder_completion (h : ThresholdHilbert)
    (z : ι → ThresholdHilbert) (c d : ι → ℝ)
    (hh : hilbertSequence h 1 = 1) (hz : ∀ i, hilbertSequence (z i) 1 = 0)
    (hd : ∀ i, inner ℝ (z i) (finiteSchurCombination z d) = inner ℝ (z i) h) :
    fixedHeadRemainder (finiteSchurResidual h z c) =
      fixedHeadRemainder (finiteSchurResidual h z d) +
      ‖finiteSchurCombination z c - finiteSchurCombination z d‖ ^ 2 := by
  rw [fixedHeadRemainder_eq_energy_sub_half _ (finiteSchurResidual_first_coordinate h z c hh hz),
    fixedHeadRemainder_eq_energy_sub_half _ (finiteSchurResidual_first_coordinate h z d hh hz),
    finiteSchurResidual_completion h z c d hd]
  ring

theorem fixedHeadSeed_schur_remainder (z : ι → ThresholdHilbert) (c : ι → ℝ)
    (hz : ∀ i, hilbertSequence (z i) 1 = 0)
    (hc : ∀ i, inner ℝ (z i) (finiteSchurCombination z c) = inner ℝ (z i) fixedHeadSeed) :
    fixedHeadRemainder (finiteSchurResidual fixedHeadSeed z c) =
      Real.log 2 - 1 / 2 - ∑ i, c i * inner ℝ (z i) fixedHeadSeed := by
  rw [fixedHeadRemainder_schur_value _ z c fixedHeadSeed_first hz hc, fixedHeadSeed_norm_sq]

/-- Vanishing *actual* fixed-head energy gives RH through the proved Mellin
bridge. There is no assumed RH implication in this statement. -/
theorem riemannHypothesis_of_fixedHeadRemainder_tendsto
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (F : ℕ → ThresholdHilbert)
    (hF : ∀ n, F n ∈ hilbertLegalSubspace A)
    (hlim : Tendsto (fun n => fixedHeadRemainder (F n)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hn := hlim.sqrt
  have hn' : Tendsto (fun n => ‖F n - paretoPointHilbert 0‖) atTop (𝓝 0) := by
    simpa [fixedHeadRemainder, Real.sqrt_sq_eq_abs] using hn
  have ht : Tendsto F atTop (𝓝 (paretoPointHilbert 0)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hn'
  apply riemannHypothesis_of_paretoPoint_zero_mem_legalClosure A hA
  exact (hilbertLegalSubspace A).isClosed_topologicalClosure.mem_of_tendsto ht
    (Eventually.of_forall (fun n => (hilbertLegalSubspace A).le_topologicalClosure (hF n)))

def relativeFixedHeadGain (F : ℕ → ThresholdHilbert) (n : ℕ) : ℝ :=
  (fixedHeadRemainder (F n) - fixedHeadRemainder (F (n + 1))) / fixedHeadRemainder (F n)

/-- The gain sequence here is computed from the actual Pareto remainders. -/
theorem fixedHeadRemainder_tendsto_iff_not_summable_gain
    (F : ℕ → ThresholdHilbert) (hpos : ∀ n, 0 < fixedHeadRemainder (F n))
    (hdec : ∀ n, fixedHeadRemainder (F (n + 1)) ≤ fixedHeadRemainder (F n)) :
    Tendsto (fun n => fixedHeadRemainder (F n)) atTop (𝓝 0) ↔
      ¬Summable (relativeFixedHeadGain F) := by
  apply residual_tendsto_zero_iff_not_summable (hpos 0)
  · intro n
    exact div_nonneg (sub_nonneg.mpr (hdec n)) (hpos n).le
  · intro n
    unfold relativeFixedHeadGain
    apply (div_lt_iff₀ (hpos n)).mpr
    linarith [hpos (n + 1)]
  · intro n
    unfold relativeFixedHeadGain
    field_simp [ne_of_gt (hpos n)]
    ring

theorem riemannHypothesis_of_nonsummable_fixedHead_gains
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (F : ℕ → ThresholdHilbert)
    (hF : ∀ n, F n ∈ hilbertLegalSubspace A)
    (hdec : ∀ n, fixedHeadRemainder (F (n + 1)) ≤ fixedHeadRemainder (F n))
    (hgain : ¬Summable (relativeFixedHeadGain F)) : RiemannHypothesis :=
  riemannHypothesis_of_fixedHeadRemainder_tendsto A hA F hF
    ((fixedHeadRemainder_tendsto_iff_not_summable_gain F
      (fun n => fixedHeadRemainder_pos_of_legal A hA (F n) (hF n)) hdec).mpr hgain)

/-- A sufficient lower bound for the *actual* gains. The lower bound itself
is the open arithmetic obligation; it is not an axiom of this development. -/
theorem riemannHypothesis_of_harmonic_fixedHead_gains
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (F : ℕ → ThresholdHilbert)
    (hF : ∀ n, F n ∈ hilbertLegalSubspace A)
    (hdec : ∀ n, fixedHeadRemainder (F (n + 1)) ≤ fixedHeadRemainder (F n))
    (c : ℝ) (hc : 0 < c)
    (hlower : ∀ n : ℕ, c / ((n : ℝ) + 1) ≤ relativeFixedHeadGain F n) : RiemannHypothesis :=
  riemannHypothesis_of_nonsummable_fixedHead_gains A hA F hF hdec
    (not_summable_of_harmonic_lower hc hlower)

end RiemannResearch.RH.Pareto
