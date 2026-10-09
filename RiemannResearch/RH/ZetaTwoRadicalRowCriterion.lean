import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.SquarefreeRadicalDifference

/-!
# Target-specific reciprocal differences at squarefree bases

Source: independently developed continuation of the user-directed exact
optimizer program, 9 October 2026. The linear rigidity argument in
RadicalDifferenceTotality needs reciprocal differences only at squarefree
base sites. Strong convergence of the actual projection residual supplies
the limiting argument. Every displayed row is signed and uses the complete
physical coordinates. Decay remains an explicit arithmetic provider.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.ZetaTwoRadicalRowCriterion
open ZetaTwoHilbert ZetaTwoOptimizerStage SquarefreeRadicalDifference
open RiemannResearch.Analysis.ExhaustiveWalk
open UniqueFactorizationMonoid

theorem stage_le_squarefree_residue_span (n : ℕ) :
    stage n ≤ Submodule.span ℝ (qResidue '' {d : ℕ | Squarefree d ∧ 2 ≤ d}) := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  change squarefreeAtom i ∈ _
  unfold squarefreeAtom
  split_ifs with hs
  · exact Submodule.subset_span ⟨i + 2, ⟨hs, by omega⟩, rfl⟩
  · exact Submodule.zero_mem _

theorem residual_difference_radical (n m : ℕ) (hm : 2 ≤ m) :
    qDifference (residual n) m = qDifference (residual n) (radical m) := by
  apply trialResidual_difference_radical {d : ℕ | Squarefree d ∧ 2 ≤ d}
    (fun _ hd => hd) m hm (optimizer n)
  exact stage_le_squarefree_residue_span n
    ((stage n).starProjection_apply_mem qOne)

theorem limitingResidual_difference_radical (m : ℕ) (hm : 2 ≤ m) :
    qDifference limitingResidual m = qDifference limitingResidual (radical m) :=
  limit_difference_radical residual limitingResidual residual_tendsto
    residual_difference_radical m hm

/-- Only the signed reciprocal differences at squarefree bases are needed.
Inverse-square summability removes the sole possible linear sequence. -/
theorem eq_zero_of_squarefree_reciprocal_differences (x : QHilbert)
    (hrad : ∀ m : ℕ, 2 ≤ m → qDifference x m = qDifference x (radical m))
    (hbase : ∀ a : ℕ, 2 ≤ a → Squarefree a →
      qDifference (reciprocalD x) a = 0) : x = 0 := by
  have hphysical :=
    RiemannResearch.Analysis.RadicalDifferenceTotality.zero_of_summable_radical_differences_and_squarefree_quotient_bases
      (qSequence_zero x) (qNormalized_square_summable x)
      (by simpa [qDifference,
        RiemannResearch.Analysis.RadicalDifferenceTotality.backwardDifference] using hrad)
      (by
        intro a ha hs
        have h := hbase a ha hs
        simpa [qDifference, qSequence_reciprocalD,
          RiemannResearch.Analysis.RadicalDifferenceTotality.quotientDifference] using h)
  apply qSequence_injective
  funext k
  change qSequence x k = qSequenceLinear 0 k
  rw [map_zero]
  exact hphysical k

/-- A target-specific cofinal consumer with no division by the moving error. -/
theorem mem_closure_of_cofinal_squarefree_reciprocal_differences
    (κ : ℕ → ℕ) (hκ : Tendsto κ atTop atTop)
    (hbase : ∀ a : ℕ, 2 ≤ a → Squarefree a →
      Tendsto (fun j => qDifference (reciprocalD (residual (κ j))) a)
        atTop (𝓝 0)) : qOne ∈ closure := by
  have hD := (reciprocalD.continuous.tendsto limitingResidual).comp
    (residual_tendsto.comp hκ)
  have hz : limitingResidual = 0 :=
    eq_zero_of_squarefree_reciprocal_differences limitingResidual
      limitingResidual_difference_radical (by
        intro a ha hs
        have h := ((continuous_qDifference a).tendsto
          (reciprocalD limitingResidual)).comp hD
        exact tendsto_nhds_unique h (hbase a ha hs))
  have hp : closure.starProjection qOne = qOne := by
    exact (sub_eq_zero.mp hz).symm
  exact Submodule.starProjection_eq_self_iff.mp hp

/-- Exact actual squarefree closure criterion. The infinitely many fixed-base
limits are required; any finite collection of numerical checks is insufficient. -/
theorem mem_closure_iff_squarefree_reciprocal_differences :
    qOne ∈ closure ↔ ∀ a : ℕ, 2 ≤ a → Squarefree a →
      Tendsto (fun n => qDifference (reciprocalD (residual n)) a) atTop (𝓝 0) := by
  constructor
  · intro hclosure a ha hs
    have hz : limitingResidual = 0 := by
      unfold limitingResidual
      rw [Submodule.starProjection_eq_self_iff.mpr hclosure, sub_self]
    have hD := (reciprocalD.continuous.tendsto limitingResidual).comp residual_tendsto
    have h := ((continuous_qDifference a).tendsto
      (reciprocalD limitingResidual)).comp hD
    simpa only [hz, map_zero, qDifference_zero, Function.comp_def] using h
  · intro hbase
    exact mem_closure_of_cofinal_squarefree_reciprocal_differences id tendsto_id hbase
end RiemannResearch.RH.ZetaTwoRadicalRowCriterion
