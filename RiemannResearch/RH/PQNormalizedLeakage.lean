import RiemannResearch.RH.QuantitativeSieve
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.QDensityLeakage
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.QFullResidueProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Module

/-!
# Two-measure normalized leakage and an explicit arithmetic provider

Source: user-provided `PQ_Augmented_Density_and_RH_Agenda.pdf`,
14 November 2026, equation (30), Priority 1, and Section 7.6 items 3--4.
All norms below are Hilbert norms in the indicated measure. In particular,
no estimate uniform in the physical site is inferred from a Hilbert estimate.
The final RH provider retains legal membership, cofinal conductors, and the
actual small-o approximation premise in its type.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.PQNormalizedLeakage
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open QDensityMetric QuantitativeSieve QFullResidueProjection

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def measuredLeakage (A : WeightedModel H) (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] (k : ℕ) : H :=
  Vᗮ.starProjection (A.encode (B (qResidue k)))

def measuredResidual (A : WeightedModel H) (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] : H := Vᗮ.starProjection (A.encode qOne)

/-- Exact signed projection identity, with the constant residual retained. -/
theorem normalized_error_eq (A : WeightedModel H) (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] (k : ℕ) (hg : A.encode (qResidue k) ∈ V) :
    (zetaTwo * (k : ℝ)) • measuredLeakage A V k - measuredResidual A V =
      Vᗮ.starProjection (A.encode (approximation k - qOne)) := by
  have hz : Vᗮ.starProjection (A.encode (qResidue k)) = 0 := by
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_eq_self_iff.mpr hg, sub_self]
  simp only [measuredLeakage, measuredResidual, map_sub,
    approximation_eq_density_combination, map_smul, hz, smul_zero, sub_zero]

theorem normalized_error_le (A : WeightedModel H) (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] (k : ℕ) (hk : 0 < k)
    (hg : A.encode (qResidue k) ∈ V) :
    ‖(zetaTwo * (k : ℝ)) • measuredLeakage A V k - measuredResidual A V‖ ≤
      Real.sqrt (tailMass A (k-1)) := by
  rw [normalized_error_eq A V k hg]
  exact (Vᗮ.norm_starProjection_apply_le _).trans (approximation_error A k hk)

def pClosure : Submodule ℝ Pareto.ThresholdHilbert :=
  (legalSpan.map paretoEquiv.toLinearMap).topologicalClosure

instance : pClosure.HasOrthogonalProjection := by
  unfold pClosure
  infer_instance

theorem residue_mem_qClosure (k : ℕ) (hk : 2 ≤ k) : qResidue k ∈ closure :=
  legalSpan.le_topologicalClosure (Submodule.subset_span
    ⟨k-2, congrArg qResidue (Nat.sub_add_cancel hk)⟩)

theorem residue_mem_pClosure (k : ℕ) (hk : 2 ≤ k) : toPareto (qResidue k) ∈ pClosure := by
  exact (mem_closure_map_iff legalSpan (qResidue k)).mpr (residue_mem_qClosure k hk)

/-- Equation (30) under Q, in the repository's original leakage notation. -/
theorem q_normalized_error_le (k : ℕ) (hk : 2 ≤ k) :
    ‖(zetaTwo * (k : ℝ)) • QDensityLeakage.leakage (qResidue k) -
      (qOne - closure.starProjection qOne)‖ ≤ Real.sqrt (tailMass qModel (k-1)) := by
  exact (QDensityLeakage.scaled_residue_leakage_error_norm_le k hk).trans
    (approximation_error qModel k (by omega))

/-- Equation (30) under P: the projection is taken in P, not transported from Q. -/
theorem p_normalized_error_le (k : ℕ) (hk : 2 ≤ k) :
    ‖(zetaTwo * (k : ℝ)) • measuredLeakage pModel pClosure k -
      measuredResidual pModel pClosure‖ ≤ Real.sqrt (tailMass pModel (k-1)) :=
  normalized_error_le pModel pClosure k (by omega) (residue_mem_pClosure k hk)

/-- The P normalization has precisely the P-orthogonal residual as its limit. -/
theorem p_normalized_tendsto :
    Tendsto (fun k : ℕ => (zetaTwo * (k : ℝ)) • measuredLeakage pModel pClosure k)
      atTop (𝓝 (measuredResidual pModel pClosure)) := by
  have ht := (pClosureᗮ.starProjection.continuous.tendsto (toPareto qOne)).comp
    (toParetoCLM.continuous.continuousAt.tendsto.comp approximation_tendsto)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with k hk
  have he := normalized_error_eq pModel pClosure k (residue_mem_pClosure k hk)
  simp only [map_sub] at he
  exact (sub_left_inj.mp he).symm

/-- A cofinal subsequence of actual normalized leakage suffices; its decay is Open. -/
theorem riemannHypothesis_of_cofinal_normalized_leakage
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (hsmall : Tendsto (fun j => (k j : ℝ) * ‖QDensityLeakage.leakage (qResidue (k j))‖)
      atTop (𝓝 0)) : RiemannHypothesis := by
  have hzero : Tendsto (fun j => (zetaTwo * (k j : ℝ)) *
      ‖QDensityLeakage.leakage (qResidue (k j))‖) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_assoc] using hsmall.const_mul zetaTwo
  have he := tendsto_nhds_unique (QDensityLeakage.scaled_residue_leakage_norm_tendsto.comp hk) hzero
  apply riemannHypothesis_of_qOne_mem_full_closure
  exact Submodule.starProjection_eq_self_iff.mp
    (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

/-- Priority 1 provider: every arithmetic premise concerns actual finite legal trials.
The small-o estimate remains an explicit hypothesis, not an asserted conclusion. -/
theorem riemannHypothesis_of_finite_approximation_provider
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop) (a : ℕ → QHilbert)
    (ha : ∀ j, a j ∈ legalSpan)
    (hsmall : Tendsto (fun j => (k j : ℝ) * ‖B (qResidue (k j)) - a j‖)
      atTop (𝓝 0)) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_normalized_leakage k hk
  apply squeeze_zero (fun j => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) _ hsmall
  intro j
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hz : closureᗮ.starProjection (a j) = 0 := by
    have hamem : a j ∈ closure := legalSpan.le_topologicalClosure (ha j)
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_eq_self_iff.mpr hamem, sub_self]
  have hp := closureᗮ.norm_starProjection_apply_le (B (qResidue (k j)) - a j)
  simpa only [map_sub, hz, sub_zero, Submodule.starProjection_orthogonal_val,
    QDensityLeakage.leakage] using hp

#print axioms p_normalized_error_le
#print axioms q_normalized_error_le
#print axioms riemannHypothesis_of_finite_approximation_provider
end RiemannResearch.RH.PQNormalizedLeakage
