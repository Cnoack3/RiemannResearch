import RiemannResearch.RH.ParetoTailAverages
import RiemannResearch.Analysis.CoefficientShift
import RiemannResearch.RH.MobiusCoefficientStabilization

/-!
# The residual tail-average criterion, with its analytic density obligation
Source: user-provided Pareto_Lean_Research_Connections_2026-09-23(1).md,
equations (14)--(17). The density hypothesis is the real coefficient-space
transport of S. Waleed Noor, "A Hardy space analysis of the Baez-Duarte
criterion for the RH", Theorems 9 and 12, https://arxiv.org/abs/1809.09577.
This citation supports the analytic statement and proof strategy.
No provider of that density theorem is asserted or axiomatized here.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.CoefficientShift

theorem localDirichlet_iff_backwardRange (a : ThresholdHilbert) :
    LocalDirichlet a ↔ ∃ b : ThresholdHilbert, backwardDifference b = a := by
  constructor
  · rintro ⟨A, b, h0, hs⟩
    refine ⟨cons A b, ?_⟩
    apply Subtype.ext
    funext n
    cases n with
    | zero => simpa using h0.symm
    | succ n => simpa using (hs n).symm
  · rintro ⟨b, rfl⟩
    refine ⟨b 0, leftShift b, ?_, ?_⟩
    · rfl
    · intro n
      rfl

namespace CoefficientStabilization

/-- Open formalization obligation: the differenced actual residue coordinates
have dense span. This is not the assertion that the undifferenced span is dense. -/
def ShiftedResidueDensity : Prop :=
  (Submodule.span ℝ (Set.range (fun i =>
    forwardDifference (hardyCoordinates (residueAtom i))))).topologicalClosure = ⊤

/-- Conditional on the named analytic density provider, tail regularity kills
every vector orthogonal to the full residue span. -/
theorem eq_zero_of_orthogonal_tailRegular (hdense : ShiftedResidueDensity)
    (f : ThresholdHilbert) (hf : f ∈ closedSpaceᗮ) (hreg : TailRegular f) : f = 0 := by
  obtain ⟨b, hb⟩ := (localDirichlet_iff_backwardRange (hardyCoordinates f)).mp
    ((localDirichlet_iff_tailRegular f).mpr hreg)
  have hzero : b = 0 := backwardDifference_orthogonal_dense
    (fun i => hardyCoordinates (residueAtom i)) hdense b (by
      intro i
      rw [hb, hardyCoordinates.inner_map_map, real_inner_comm]
      apply hf
      exact (Submodule.span ℝ (Set.range residueAtom)).le_topologicalClosure
        (Submodule.subset_span ⟨i, rfl⟩))
  apply hardyCoordinates.injective
  rw [map_zero, ← hb, hzero]
  apply Subtype.ext
  funext n
  simp [backwardDifference_apply]

theorem limitResidual_zero_iff_tailRegular (hdense : ShiftedResidueDensity) :
    limitResidual = 0 ↔ TailRegular limitResidual := by
  constructor
  · intro h
    refine ⟨0, ?_⟩
    simp [h, tailAverage, hilbertGibbsPhysical]
  · exact eq_zero_of_orthogonal_tailRegular hdense limitResidual limitResidual_mem_orthogonal

/-- Explicit complete infinite Pareto-tail version, indexed from m=n+1. -/
theorem limitResidual_zero_iff_tail_average_summable (hdense : ShiftedResidueDensity) :
    limitResidual = 0 ↔ ∃ L : ℝ,
      Summable (fun n : ℕ =>
        |((n : ℝ) + 1) *
          (∑' k, paretoWeight (k + n) * hilbertSequence limitResidual (k + n + 1))
          - L| ^ 2) := by
  simpa only [TailRegular, tailAverage_eq_tsum, hilbertGibbsPhysical_eq] using
    limitResidual_zero_iff_tailRegular hdense

theorem limitResidual_tailAverage_zero :
    tailAverage limitResidual 0 = limitEnergy := by
  rw [tailAverage_zero]
  have ho : inner ℝ limitResidual limitProjection = 0 := by
    rw [real_inner_comm]
    exact limitResidual_mem_orthogonal _ (closedSpace.starProjection_apply_mem hilbertOne)
  have he : hilbertOne = limitResidual + limitProjection := by
    simp [limitResidual]
  calc
    inner ℝ limitResidual hilbertOne =
        inner ℝ limitResidual (limitResidual + limitProjection) := congrArg _ he
    _ = ‖limitResidual‖ ^ 2 := by rw [inner_add_right, ho, add_zero, real_inner_self_eq_norm_sq]
    _ = limitEnergy := rfl

/-- Unconditional Parseval identity: it controls differences, not centered values. -/
theorem limitResidual_tail_difference_energy :
    (∑' n, |tailAverage limitResidual n - tailAverage limitResidual (n + 1)| ^ 2) =
      limitEnergy - limitEnergy ^ 2 := by
  have hp := tailAverage_parseval limitResidual
  rw [limitResidual_tailAverage_zero, sq_abs] at hp
  change limitEnergy = limitEnergy ^ 2 + _ at hp
  linarith

/-- Both the analytic density provider and residual regularity are explicit. -/
theorem riemannHypothesis_of_tailRegular (hdense : ShiftedResidueDensity)
    (hreg : TailRegular limitResidual) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      ((limitResidual_zero_iff_tailRegular hdense).mpr hreg))

end CoefficientStabilization
end RiemannResearch.RH.Pareto
