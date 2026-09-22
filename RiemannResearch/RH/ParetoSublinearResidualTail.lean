import RiemannResearch.Analysis.SublinearEnergyLimits
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.CanonicalMobiusSublinearEnergy
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sublinear exact-head energy and normalized residual tails

Source: user-provided `Pareto_Direct_Attempt_Sublinear_Energy_2026-09-22.md`,
Sections 3-4 and 7, for the statements and product-inequality proof strategy.
All tails below refer to the actual canonical residual and its complete
infinite weighted energy. The finite product lower bound is imported from
`ExactHeadResidualTail`; this module supplies the new limit implications.

The general reductions retain sublinear energy explicitly. The concrete
Möbius specialization now derives it from the two explicit PNT cancellation
inputs in `CanonicalMobiusSublinearEnergy`. Checked providers for those two
classical asymptotics are not supplied here.
A bounded cofinal subsequence of exact-head full energies also implies RH,
without any sublinear hypothesis; the boundedness provider remains open.
No vanishing actual residual is proved here.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

theorem one_sub_energy_le (f : ThresholdHilbert) :
    ‖hilbertOne - f‖^2 ≤ 2 + 2 * ‖f‖^2 := by
  have hn := norm_sub_le hilbertOne f
  have hs := sq_le_sq₀ (norm_nonneg (hilbertOne - f))
    (add_nonneg (norm_nonneg hilbertOne) (norm_nonneg f)) |>.mpr hn
  nlinarith [hilbertOne_norm_sq, sq_nonneg (‖hilbertOne‖ - ‖f‖)]

theorem error_energy_div_tendsto_zero_of_energy
    (F : ℕ → ThresholdHilbert)
    (hsub : Tendsto (fun N => ‖F N‖^2 / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N => ‖hilbertOne - F N‖^2 / (N : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => 2 * (1 / (N : ℝ)) +
      2 * (‖F N‖^2 / (N : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2 |>.add
      (hsub.const_mul 2)
  apply squeeze_zero (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) _ ht
  intro N
  have h := div_le_div_of_nonneg_right (one_sub_energy_le (F N))
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  calc
    _ ≤ (2 + 2 * ‖F N‖^2) / (N : ℝ) := h
    _ = _ := by ring

namespace CoefficientStabilization

/-- The complete tail energy, multiplied by N, diverges under sublinear errors. -/
theorem normalized_residual_tail_tendsto_atTop_of_sublinear_error
    (hpos : 0 < limitEnergy) (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (hsub : Tendsto (fun N => ‖hilbertOne - F N‖^2 / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℝ) * residualTailEnergy N) atTop atTop := by
  refine RiemannResearch.Analysis.tendsto_atTop_of_pos_le_mul_tendsto_zero
    (sq_pos_of_pos hpos) ?_ hsub ?_
  · exact Eventually.of_forall (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have heq : ((N : ℝ) * residualTailEnergy N) *
        (‖hilbertOne - F N‖^2 / (N : ℝ)) =
        residualTailEnergy N * ‖hilbertOne - F N‖^2 := by
      field_simp [hne]
    rw [heq]
    exact residual_tail_product_lower N (hlegal N) (hhead N)

theorem normalized_residual_tail_tendsto_atTop_of_sublinear_energy
    (hpos : 0 < limitEnergy) (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (hsub : Tendsto (fun N => ‖F N‖^2 / (N : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℝ) * residualTailEnergy N) atTop atTop :=
  normalized_residual_tail_tendsto_atTop_of_sublinear_error hpos F hlegal hhead
    (error_energy_div_tendsto_zero_of_energy F hsub)

theorem limitEnergy_zero_of_frequently_bounded_normalized_tail
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (hsub : Tendsto (fun N => ‖F N‖^2 / (N : ℝ)) atTop (𝓝 0))
    (C : ℝ) (hbounded : ∃ᶠ N : ℕ in atTop, (N : ℝ) * residualTailEnergy N ≤ C) :
    limitEnergy = 0 := by
  by_contra hn
  have hp : 0 < limitEnergy := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hn)
  have ht := normalized_residual_tail_tendsto_atTop_of_sublinear_energy hp F hlegal hhead hsub
  obtain ⟨N, hN, hN'⟩ :=
    (hbounded.and_eventually (ht.eventually_gt_atTop C)).exists
  linarith

theorem riemannHypothesis_of_frequently_bounded_normalized_tail
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (hsub : Tendsto (fun N => ‖F N‖^2 / (N : ℝ)) atTop (𝓝 0))
    (C : ℝ) (hbounded : ∃ᶠ N : ℕ in atTop, (N : ℝ) * residualTailEnergy N ≤ C) :
    RiemannHypothesis := by
  have hz := limitEnergy_zero_of_frequently_bounded_normalized_tail F hlegal hhead hsub C hbounded
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (limitEnergy_zero_iff_mem.mp hz))

theorem riemannHypothesis_of_frequently_bounded_exact_head_errors
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (C : ℝ) (hbounded : ∃ᶠ N in atTop, ‖hilbertOne - F N‖^2 ≤ C) :
    RiemannHypothesis := by
  by_contra hRH
  have ht := not_RH_exact_head_errors_tendsto_atTop hRH F hlegal hhead
  obtain ⟨N, hN, hN'⟩ :=
    (hbounded.and_eventually (ht.eventually_gt_atTop C)).exists
  linarith

theorem riemannHypothesis_of_frequently_bounded_exact_head_energy
    (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1)
    (C : ℝ) (hbounded : ∃ᶠ N in atTop, ‖F N‖^2 ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_frequently_bounded_exact_head_errors F hlegal hhead (2 + 2*C)
  apply hbounded.mono
  intro N hN
  exact (one_sub_energy_le (F N)).trans (by linarith)

/-- Failure of RH forces divergence of the full candidate energies. -/
theorem not_RH_exact_head_energy_tendsto_atTop
    (hRH : ¬ RiemannHypothesis) (F : ℕ → ThresholdHilbert)
    (hlegal : ∀ N, F N ∈ closedSpace)
    (hhead : ∀ N k, 0 < k → k ≤ N → hilbertSequence (F N) k = 1) :
    Tendsto (fun N => ‖F N‖^2) atTop atTop := by
  have ht := not_RH_exact_head_errors_tendsto_atTop hRH F hlegal hhead
  apply tendsto_atTop.mpr
  intro B
  filter_upwards [ht.eventually_ge_atTop (2 + 2*B)] with N hN
  have he := one_sub_energy_le (F N)
  linarith

/-- The verified head and legality providers discharge the representation
hypotheses for the manuscript's explicit family. The energy limit stays explicit. -/
theorem canonical_normalized_tail_tendsto_atTop
    (hpos : 0 < limitEnergy)
    (hsub : Tendsto (fun N => ‖canonicalMobiusHilbert N‖^2 / (N : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℝ) * residualTailEnergy N) atTop atTop :=
  normalized_residual_tail_tendsto_atTop_of_sublinear_energy hpos canonicalMobiusHilbert
    canonicalMobiusHilbert_mem_closedSpace canonicalMobiusHilbert_exact hsub

/-- Only a cofinal bounded subsequence of this explicit family's full energies
is needed. No such subsequence is constructed in this module. -/
theorem riemannHypothesis_of_canonical_frequently_bounded_energy
    (C : ℝ) (hbounded : ∃ᶠ N in atTop, ‖canonicalMobiusHilbert N‖^2 ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_frequently_bounded_exact_head_energy canonicalMobiusHilbert
    canonicalMobiusHilbert_mem_closedSpace canonicalMobiusHilbert_exact C hbounded


/-- Ordinary and reciprocal Möbius cancellation supply the sublinear-energy
provider for the actual residual-tail divergence theorem. -/
theorem canonical_normalized_tail_tendsto_atTop_of_mobius_cancellation
    (hpos : 0 < limitEnergy)
    (hM : Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)) / (N : ℝ))
      atTop (𝓝 0))
    (hm : Tendsto mobiusReciprocalSum atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℝ) * residualTailEnergy N) atTop atTop :=
  canonical_normalized_tail_tendsto_atTop hpos
    (canonicalMobiusHilbert_sublinear_of_mobius_cancellation hM hm)

/-- With the two explicit PNT inputs, a bounded cofinal normalized residual
tail suffices. The bounded-tail estimate is still an open research input. -/
theorem canonical_limitEnergy_zero_of_frequently_bounded_tail
    (hM : Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)) / (N : ℝ))
      atTop (𝓝 0))
    (hm : Tendsto mobiusReciprocalSum atTop (𝓝 0))
    (C : ℝ) (hbounded : ∃ᶠ N : ℕ in atTop, (N : ℝ) * residualTailEnergy N ≤ C) :
    limitEnergy = 0 :=
  limitEnergy_zero_of_frequently_bounded_normalized_tail canonicalMobiusHilbert
    canonicalMobiusHilbert_mem_closedSpace canonicalMobiusHilbert_exact
    (canonicalMobiusHilbert_sublinear_of_mobius_cancellation hM hm) C hbounded

end CoefficientStabilization
end RiemannResearch.RH.Pareto
