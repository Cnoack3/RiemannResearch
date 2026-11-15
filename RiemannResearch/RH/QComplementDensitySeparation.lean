import RiemannResearch.RH.QDensityCouplingSurjectivity
import RiemannResearch.RH.QDensityClosureTransfer
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QDensityMetricInverse
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.InnerProductSpace.l2Space
import RiemannResearch.RH.QAnnihilatorDilationEscape
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.QFullTargetTotality
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Density separation of the full Q complement

Source: Christian Noack's P/Q-complement question, 15 November 2026, and
deductions from the repository's full reciprocal density and arithmetic
annihilator tail-escape theorems. B always denotes dQ/dP, and U is the
Q-orthogonal complement of the full-conductor residue closure.

Invertibility identifies the P complement with B(U). Trivial intersection
makes the restricted difference I-B injective and excludes every nonzero
B-eigenvector from U. It does not prove U=0: the actual operator B admits
other nonzero subspaces S with S intersect B(S)=0.

A precise arithmetic continuation is established: U=0 if and only if the
physical constant residual Pi_U(1) is bounded. The existence of that bound
is Open. The conditional RH consequence does not assume RH.

The arithmetic target-to-totality step is supplied by QFullTargetTotality.
Its cited source, Bagchi, arXiv:math/0607733, Theorem 1, supports that
statement and the integer-dilation proof strategy.
-/

noncomputable section
namespace RiemannResearch.RH.QComplementDensitySeparation
open ZetaTwoHilbert ZetaTwoProbability QDensityMetric QDensityMetricInverse
open QReciprocalMetric QFullResidueProjection QDensityCouplingSurjectivity
abbrev U := QFullResidueProjection.closureᗮ


/-- Both complements are realized as physical sequences in the Q carrier. -/
theorem pareto_orthogonal_eq_density_image :
    Submodule.comap ZetaTwoParetoTransfer.toParetoLinear
      (QFullResidueProjection.closure.map ZetaTwoParetoTransfer.toParetoLinear)ᗮ =
        U.map B.toLinearMap := by
  ext f
  constructor
  · intro hf
    refine ⟨inverse f, ?_, B_inverse f⟩
    change inverse f ∈ QFullResidueProjection.closureᗮ
    rw [Submodule.mem_orthogonal]
    intro g hg
    have hp : ZetaTwoParetoTransfer.toPareto f ∈
        (QFullResidueProjection.closure.map ZetaTwoParetoTransfer.toParetoLinear)ᗮ := hf
    have hpg : ZetaTwoParetoTransfer.toPareto g ∈
        QFullResidueProjection.closure.map ZetaTwoParetoTransfer.toParetoLinear :=
      ⟨g, hg, rfl⟩
    have he := Submodule.inner_right_of_mem_orthogonal hpg hp
    rw [pareto_inner_inverse] at he
    exact he
  · rintro ⟨u, hu, rfl⟩
    change ZetaTwoParetoTransfer.toPareto (B u) ∈
      (QFullResidueProjection.closure.map ZetaTwoParetoTransfer.toParetoLinear)ᗮ
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨g, hg, rfl⟩
    change inner ℝ (ZetaTwoParetoTransfer.toPareto g)
      (ZetaTwoParetoTransfer.toPareto (B u)) = 0
    rw [← q_inner_density]
    exact Submodule.inner_right_of_mem_orthogonal hg hu

/-- A vector of U can have its density image in U only when it is zero. -/
theorem density_mem_orthogonal_iff (u : QHilbert) (hu : u ∈ U) :
    B u ∈ U ↔ u = 0 := by
  constructor
  · intro hb
    have hz : reverseCoupling ⟨u, hu⟩ = 0 := by
      change QFullResidueProjection.closure.orthogonalProjectionOnto (B u) = 0
      exact Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hb
    exact congrArg Subtype.val (reverseCoupling_zero ⟨u, hu⟩ hz)
  · rintro rfl
    simp

/-- The joint-complement theorem in one Q Hilbert carrier. -/
theorem orthogonal_inf_density_image_eq_bot :
    U ⊓ U.map B.toLinearMap = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro f ⟨hf, u, hu, rfl⟩
  rw [Submodule.mem_bot]
  have hz := (density_mem_orthogonal_iff u hu).mp hf
  simp [hz]

/-- Applying the inverse density preserves the trivial-intersection conclusion. -/
theorem orthogonal_inf_inverse_image_eq_bot :
    U ⊓ U.map inverse.toLinearMap = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro f ⟨hf, u, hu, rfl⟩
  rw [Submodule.mem_bot]
  apply (density_mem_orthogonal_iff (inverse u) hf).mp
  simpa using hu

/-- The restricted difference has zero kernel; it is not asserted to be the zero map. -/
theorem eq_zero_of_id_sub_density_zero (u : QHilbert) (hu : u ∈ U)
    (h : u - B u = 0) : u = 0 := by
  apply (density_mem_orthogonal_iff u hu).mp
  rw [← sub_eq_zero.mp h]
  exact hu

/-- The codomain is the ambient Hilbert space, since U is not known to be invariant. -/
theorem id_sub_density_injective :
    Function.Injective (fun u : U => (u : QHilbert) - B u) := by
  intro u v h
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_id_sub_density_zero _ (U.sub_mem u.property v.property)
  rw [map_sub]
  have hh : (u : QHilbert) - B u - ((v : QHilbert) - B v) = 0 := sub_eq_zero.mpr h
  calc
    (u : QHilbert) - v - (B u - B v) =
        (u : QHilbert) - B u - ((v : QHilbert) - B v) := by abel
    _ = 0 := hh

/-- Density invariance of the actual complement is equivalent to its vanishing. -/
theorem orthogonal_eq_bot_iff_density_invariant :
    U = ⊥ ↔ ∀ u ∈ U, B u ∈ U := by
  constructor
  · intro h u hu
    rw [h] at hu ⊢
    change u = 0 at hu
    simp [hu]
  · intro h
    apply le_antisymm ?_ bot_le
    intro u hu
    change u = 0
    exact (density_mem_orthogonal_iff u hu).mp (h u hu)

/-- No nonzero annihilator admits a complete-Q reciprocal preimage. -/
theorem orthogonal_inf_reciprocal_range_eq_bot :
    U ⊓ D.range = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro u ⟨hu, f, rfl⟩
  rw [Submodule.mem_bot]
  simp [eq_zero_of_reciprocal_mem_orthogonal f hu]

/-- Exact conditional criterion. Existence of the uniform physical bound remains Open. -/
theorem orthogonal_eq_bot_iff_bounded_constant_residual :
    U = ⊥ ↔ ∃ A : ℝ, 0 ≤ A ∧ ∀ k : ℕ, 0 < k →
      |qSequence (U.starProjection qOne) k| ≤ A := by
  constructor
  · intro h
    have hz : U.starProjection qOne = 0 := by
      have hall : ∀ u : QHilbert, u ∈ U → u = 0 := by
        intro u hu
        rw [h] at hu
        exact hu
      exact hall _ (U.starProjection_apply_mem qOne)
    refine ⟨0, le_rfl, ?_⟩
    intro k hk
    rw [hz]
    change |qSequenceLinear 0 k| ≤ 0
    rw [map_zero]
    simp
  · rintro ⟨A, hA, hb⟩
    have hz : U.starProjection qOne = 0 :=
      QAnnihilatorDilationEscape.annihilator_eq_zero_of_bounded_physical
        _ (U.starProjection_apply_mem _) A hA hb
    have hr : qOne - QFullResidueProjection.closure.starProjection qOne = 0 := by
      simpa only [U, Submodule.starProjection_orthogonal_val] using hz
    have hm : qOne ∈ QFullResidueProjection.closure :=
      Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
    exact Submodule.orthogonal_eq_bot_iff.mpr
      (QFullTargetTotality.closure_eq_top_iff_one_mem.mpr hm)

/-- Conditional RH consequence; vanishing of U is the substantive open premise. -/
theorem riemannHypothesis_of_orthogonal_eq_bot (h : U = ⊥) : RiemannHypothesis := by
  apply riemannHypothesis_of_qOne_mem_full_closure
  have hv : QFullResidueProjection.closure = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp h
  rw [hv]
  trivial

/-- A vector on the first two normalized coordinates, used only for the structural counterexample. -/
def counterexampleVector : QHilbert := lp.single 2 0 1 + lp.single 2 1 1

theorem counterexampleVector_ne_zero : counterexampleVector ≠ 0 := by
  intro h
  have he := congrArg (fun f : QHilbert => f 0) h
  norm_num [counterexampleVector, lp.single_apply] at he

theorem counterexampleVector_density_independent (a b : ℝ)
    (h : a • counterexampleVector = b • B counterexampleVector) : a = 0 ∧ b = 0 := by
  have h0 := congrArg (fun f : QHilbert => f 0) h
  have h1 := congrArg (fun f : QHilbert => f 1) h
  have ht0 : counterexampleVector 0 = 1 := by
    change (lp.single 2 0 1 : QHilbert) 0 + (lp.single 2 1 1 : QHilbert) 0 = 1
    norm_num [lp.single_apply]
  have ht1 : counterexampleVector 1 = 1 := by
    change (lp.single 2 0 1 : QHilbert) 1 + (lp.single 2 1 1 : QHilbert) 1 = 1
    norm_num [lp.single_apply]
  change a * counterexampleVector 0 = b * B counterexampleVector 0 at h0
  change a * counterexampleVector 1 = b * B counterexampleVector 1 at h1
  rw [B_apply, ht0] at h0
  rw [B_apply, ht1] at h1
  norm_num at h0 h1
  have hz := ne_of_gt zetaTwo_pos
  field_simp [hz] at h0 h1
  have ha : a = 0 := by nlinarith [zetaTwo_pos]
  exact ⟨ha, by simpa [ha] using h0.symm⟩


/-- Counterexample to a purely operator-theoretic inference from invertibility
and trivial intersection. S is not asserted to be the arithmetic complement U. -/
theorem exists_nonzero_submodule_inf_density_image_eq_bot :
    ∃ S : Submodule ℝ QHilbert, S ≠ ⊥ ∧ S ⊓ S.map B.toLinearMap = ⊥ := by
  let S : Submodule ℝ QHilbert := Submodule.span ℝ {counterexampleVector}
  have hmem : counterexampleVector ∈ S := Submodule.subset_span (by simp)
  refine ⟨S, ?_, ?_⟩
  · intro hs
    have hz : counterexampleVector = 0 := by simpa [hs] using hmem
    exact counterexampleVector_ne_zero hz
  · apply le_antisymm ?_ bot_le
    rintro f ⟨hf, u, hu, rfl⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hf
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hab := counterexampleVector_density_independent a b (by simpa using ha)
    change B (b • counterexampleVector) = 0
    simp [hab.2]

/-- The actual complement contains no nonzero eigenvector of B at any real eigenvalue. -/
theorem density_eigenvector_eq_zero (u : QHilbert) (hu : u ∈ U)
    (a : ℝ) (h : B u = a • u) : u = 0 :=
  (density_mem_orthogonal_iff u hu).mp (h ▸ U.smul_mem a hu)

#print axioms exists_nonzero_submodule_inf_density_image_eq_bot

#print axioms pareto_orthogonal_eq_density_image
#print axioms orthogonal_inf_density_image_eq_bot
#print axioms orthogonal_eq_bot_iff_bounded_constant_residual
#print axioms counterexampleVector_density_independent
end RiemannResearch.RH.QComplementDensitySeparation
