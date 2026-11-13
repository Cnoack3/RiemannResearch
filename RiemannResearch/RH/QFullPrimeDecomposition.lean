/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullPrimeProjectionControl
import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import RiemannResearch.RH.QPrimeCarryProjection
import RiemannResearch.RH.QSimultaneousCRT
import RiemannResearch.RH.QSquarefreeMultiplierRigidity
import RiemannResearch.RH.QShiftedReciprocalBounds
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.QFullDensityConditionalConverse
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Full-conductor prime decomposition and complementary forcing

Source: Full_Conductor_RH_Projection_Machinery.pdf, Section 10.3, and the
user-directed decomposition argument of 13 November 2026. The cubic control
is supplied by QFullPrimeProjectionControl. The complementary forcing equation
is obtained by applying the full normal equation to the nested complement.

W is the existing closed prime span; V is the full residue closure, not the
squarefree optimizer closure. C = V ⊓ Wᗮ contains the projected higher prime
powers as well as the projected mixed conductors.

The operator called R in the discussion is QShiftedReciprocal.B in the legacy
API. References are qualified; QDensityMetric.B remains the density dQ/dP.
The exact complement equation retains its forcing and contraction term.
It proves neither prime-component vanishing nor complementary forcing zero.

The RH implication has no analytic-provider premise. The reverse RH implication
explicitly retains BaezDuarteMobiusApproximation, as in the existing full-density
module. Source for that classical converse: Bagchi, Proc. Indian Acad. Sci.
(Math. Sci.) 116 (2006), Theorem 1, https://arxiv.org/abs/math/0607733.
-/

noncomputable section
open scoped Topology
namespace RiemannResearch.RH.QFullPrimeDecomposition
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QFullResidueProjection QFullDisplacement
open QPrimeCarryProjection (primeClosure qResidue_mem_primeClosure)
open RiemannResearch.Analysis.NestedOrthogonalDecomposition

/-- The prime dictionary embeds in the full dictionary without identifying their projections. -/
theorem primeClosure_le_full : primeClosure ≤ closure := by
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro x ⟨p, rfl⟩
  exact QFloorDilation.qResidue_mem_legalSpan p.val p.property.pos

/-- The full conductor complement, including higher prime-power depth. -/
abbrev conductorComplement : Submodule ℝ QHilbert := closure ⊓ primeClosureᗮ

instance conductorComplement_hasOrthogonalProjection :
    conductorComplement.HasOrthogonalProjection :=
  carry_hasOrthogonalProjection primeClosure_le_full

/-- The Q-orthogonal part of an atom after removing its closed-prime projection. -/
def nonprimeAtom (m : ℕ) : QHilbert := primeClosureᗮ.starProjection (qResidue m)

/-- Algebraic span of all projected nonprime conductors. -/
def nonprimeSpan : Submodule ℝ QHilbert :=
  Submodule.span ℝ (Set.range (fun m : {m : ℕ // 2 ≤ m ∧ ¬m.Prime} =>
    nonprimeAtom m.val))

/-- Projecting a prime generator gives zero, so only composite conductors remain. -/
theorem projected_full_span_eq :
    Submodule.span ℝ (primeClosureᗮ.starProjection ''
      Set.range (fun i : ℕ => qResidue (i + 2))) = nonprimeSpan := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
    by_cases hp : (i + 2).Prime
    · rw [Submodule.starProjection_orthogonal_apply_eq_zero
        (qResidue_mem_primeClosure (i + 2) hp)]
      exact nonprimeSpan.zero_mem
    · exact Submodule.subset_span ⟨⟨i + 2, by omega, hp⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro x ⟨m, rfl⟩
    refine Submodule.subset_span ⟨qResidue m.val, ?_, rfl⟩
    refine ⟨m.val - 2, ?_⟩
    change qResidue (m.val - 2 + 2) = qResidue m.val
    rw [Nat.sub_add_cancel m.property.1]

/-- Exact closed-span identification of the full conductor complement. -/
theorem conductorComplement_eq_closed_nonprimeSpan :
    conductorComplement = nonprimeSpan.topologicalClosure := by
  have h := carry_eq_closure_projected_generators primeClosure_le_full
    (Set.range (fun i : ℕ => qResidue (i + 2))) (by rfl)
  rw [projected_full_span_eq] at h
  exact h

/-- The full legal space is the orthogonal sum of W and C. -/
theorem fullClosure_eq_prime_sup_complement :
    closure = primeClosure ⊔ conductorComplement :=
  (prime_sup_carry primeClosure_le_full).symm

/-- The selected all-conductor decomposition, with its necessary closure. -/
theorem fullClosure_eq_prime_sup_closed_nonprimeSpan :
    closure = primeClosure ⊔ nonprimeSpan.topologicalClosure := by
  rw [← conductorComplement_eq_closed_nonprimeSpan]
  exact fullClosure_eq_prime_sup_complement

/-- Every projected legal atom belongs to the canonical complement. -/
theorem nonprimeAtom_mem_complement (m : ℕ) (hm : 2 ≤ m) :
    nonprimeAtom m ∈ conductorComplement := by
  have hmem : qResidue m ∈ closure :=
    legalSpan.le_topologicalClosure
      (QFloorDilation.qResidue_mem_legalSpan m (by omega))
  constructor
  · unfold nonprimeAtom
    rw [Submodule.starProjection_orthogonal_val]
    exact closure.sub_mem hmem
      (primeClosure_le_full (primeClosure.starProjection_apply_mem _))
  · exact primeClosureᗮ.starProjection_apply_mem _

/-- Prime component of the actual full-conductor matched displacement. -/
def primeComponent : QHilbert := primeClosure.starProjection displacement
/-- Complementary component of the actual full-conductor matched displacement. -/
def complementaryComponent : QHilbert := conductorComplement.starProjection displacement

/-- Exact displacement decomposition. -/
theorem displacement_eq_prime_add_complement :
    displacement = primeComponent + complementaryComponent :=
  (projection_split_of_mem primeClosure_le_full displacement_mem).symm

/-- The complementary component is the remainder after prime projection. -/
theorem complementaryComponent_eq_sub :
    complementaryComponent = displacement - primeComponent := by
  change conductorComplement.starProjection displacement =
    displacement - primeClosure.starProjection displacement
  rw [carry_projection_apply primeClosure_le_full,
    closure.starProjection_eq_self_iff.mpr displacement_mem]

/-- Since d is legal, projection onto C agrees with projection onto the ambient W orthogonal. -/
theorem complementaryComponent_eq_orthogonal_projection :
    complementaryComponent = primeClosureᗮ.starProjection displacement := by
  rw [complementaryComponent_eq_sub, Submodule.starProjection_orthogonal_val]
  rfl

/-- The two displacement components are Q-orthogonal. -/
theorem components_orthogonal : inner ℝ primeComponent complementaryComponent = 0 :=
  prime_carry_inner_eq_zero (primeClosure.starProjection_apply_mem _)
    (conductorComplement.starProjection_apply_mem _)

/-- Pythagoras retains both nonnegative component energies. -/
theorem displacement_norm_sq_split :
    ‖displacement‖ ^ 2 = ‖primeComponent‖ ^ 2 + ‖complementaryComponent‖ ^ 2 :=
  norm_sq_split_of_mem primeClosure_le_full displacement_mem

/-- Prime normal equation for the actual matched residual. -/
theorem primeComponent_eq_projected_source :
    primeComponent = primeClosure.starProjection (QShiftedReciprocal.B pResidual) := by
  unfold primeComponent
  rw [displacement_eq_projected_pResidual, nested_projection_apply primeClosure_le_full]

/-- Complementary normal equation for the actual matched residual. -/
theorem complementaryComponent_eq_projected_source :
    complementaryComponent =
      conductorComplement.starProjection (QShiftedReciprocal.B pResidual) := by
  unfold complementaryComponent
  rw [displacement_eq_projected_pResidual, nested_projection_apply
    (show conductorComplement ≤ closure from inf_le_left)]

/-- Complementary vanishing is precisely membership of d in W; it is not assumed. -/
theorem complementaryComponent_eq_zero_iff_mem_primeClosure :
    complementaryComponent = 0 ↔ displacement ∈ primeClosure := by
  rw [complementaryComponent_eq_sub, sub_eq_zero, eq_comm]
  exact primeClosure.starProjection_eq_self_iff

/-- A complementary projection vanishes exactly when every projected composite test vanishes. -/
theorem complement_projection_eq_zero_iff (t : QHilbert) :
    conductorComplement.starProjection t = 0 ↔
      ∀ m : ℕ, 2 ≤ m → ¬m.Prime → inner ℝ (nonprimeAtom m) t = 0 := by
  constructor
  · intro hz m hm _
    have h := Submodule.inner_right_of_mem_orthogonal (nonprimeAtom_mem_complement m hm)
      (Submodule.sub_starProjection_mem_orthogonal (K := conductorComplement) t)
    simpa only [hz, sub_zero] using h
  · intro h
    let L : QHilbert →L[ℝ] ℝ := innerSL ℝ t
    have hspan : nonprimeSpan ≤ LinearMap.ker L.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro x ⟨m, rfl⟩
      change inner ℝ t (nonprimeAtom m.val) = 0
      rw [real_inner_comm]
      exact h m.val m.property.1 m.property.2
    have hclosed : nonprimeSpan.topologicalClosure ≤ LinearMap.ker L.toLinearMap :=
      nonprimeSpan.topologicalClosure_minimal hspan L.isClosed_ker
    have hp : conductorComplement.starProjection t ∈ nonprimeSpan.topologicalClosure := by
      rw [← conductorComplement_eq_closed_nonprimeSpan]
      exact conductorComplement.starProjection_apply_mem _
    have hz : inner ℝ t (conductorComplement.starProjection t) = 0 := hclosed hp
    have he := Submodule.inner_right_of_mem_orthogonal
      (conductorComplement.starProjection_apply_mem t)
      (Submodule.sub_starProjection_mem_orthogonal (K := conductorComplement) t)
    have hz' : inner ℝ (conductorComplement.starProjection t) t = 0 :=
      (real_inner_comm _ _).trans hz
    rw [inner_sub_right, hz', real_inner_self_eq_norm_sq] at he
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (conductorComplement.starProjection t)]

/-- Exact cancellation obligation expressed using the actual Pareto residual. -/
theorem complementaryComponent_eq_zero_iff_pairings :
    complementaryComponent = 0 ↔
      ∀ m : ℕ, 2 ≤ m → ¬m.Prime →
        inner ℝ pResidual (QShiftedReciprocal.B (nonprimeAtom m)) = 0 := by
  rw [complementaryComponent_eq_projected_source, complement_projection_eq_zero_iff]
  constructor <;> intro h m hm hnp
  · rw [real_inner_comm, QShiftedReciprocal.B_symmetric]
    exact h m hm hnp
  · rw [← QShiftedReciprocal.B_symmetric, real_inner_comm]
    exact h m hm hnp

/-- Complementary forcing from the Q residual and prime component, excluding the unknown complement. -/
def complementForcing : QHilbert :=
  conductorComplement.starProjection
    (QShiftedReciprocal.B (qResidual + primeComponent))

/-- Exact signed equation: complementary component equals forcing plus its compressed reciprocal image. -/
theorem complementaryComponent_fixed_point :
    complementaryComponent = complementForcing +
      conductorComplement.starProjection (QShiftedReciprocal.B complementaryComponent) := by
  calc
    complementaryComponent =
        conductorComplement.starProjection (QShiftedReciprocal.B pResidual) :=
      complementaryComponent_eq_projected_source
    _ = conductorComplement.starProjection
        (QShiftedReciprocal.B ((qResidual + primeComponent) + complementaryComponent)) := by
      rw [pResidual_eq_residual_add_displacement, displacement_eq_prime_add_complement,
        add_assoc]
    _ = _ := by rw [map_add, map_add]; rfl

/-- The half-contraction bounds the complementary component by twice its forcing. -/
theorem complementaryComponent_norm_le :
    ‖complementaryComponent‖ ≤ 2 * ‖complementForcing‖ := by
  have h := norm_add_le complementForcing
    (conductorComplement.starProjection (QShiftedReciprocal.B complementaryComponent))
  rw [← complementaryComponent_fixed_point] at h
  have hp := conductorComplement.norm_starProjection_apply_le
    (QShiftedReciprocal.B complementaryComponent)
  have hb := QShiftedReciprocal.B_norm_le_half complementaryComponent
  nlinarith

/-- Complementary-component vanishing is equivalent to zero reduced forcing. -/
theorem complementaryComponent_eq_zero_iff_forcing :
    complementaryComponent = 0 ↔ complementForcing = 0 := by
  constructor
  · intro hz
    have h := complementaryComponent_fixed_point
    simpa only [hz, map_zero, add_zero] using h.symm
  · intro hz
    have h := complementaryComponent_norm_le
    rw [hz, norm_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

/-- Composite test criterion with the complementary component removed from the source. -/
theorem complementaryComponent_eq_zero_iff_reduced_pairings :
    complementaryComponent = 0 ↔
      ∀ m : ℕ, 2 ≤ m → ¬m.Prime →
        inner ℝ (qResidual + primeComponent)
          (QShiftedReciprocal.B (nonprimeAtom m)) = 0 := by
  rw [complementaryComponent_eq_zero_iff_forcing]
  unfold complementForcing
  rw [complement_projection_eq_zero_iff]
  constructor <;> intro h m hm hnp
  · rw [real_inner_comm, QShiftedReciprocal.B_symmetric]
    exact h m hm hnp
  · rw [← QShiftedReciprocal.B_symmetric, real_inner_comm]
    exact h m hm hnp

/-- The full displacement cannot be nonzero with a zero prime component. -/
theorem primeComponent_eq_zero_iff_displacement :
    primeComponent = 0 ↔ displacement = 0 :=
  prime_projection_eq_zero_iff_displacement_eq_zero
    primeClosure qResidue_mem_primeClosure

/-- Prime-component vanishing is equivalent to target membership, without an RH converse provider. -/
theorem primeComponent_eq_zero_iff_one_mem :
    primeComponent = 0 ↔ qOne ∈ closure :=
  prime_projection_eq_zero_iff_one_mem primeClosure qResidue_mem_primeClosure

/-- Quantitative prime control of the actual full Pareto residual. -/
theorem pResidual_norm_cube_le_primeComponent :
    ‖toPareto pResidual‖ ^ 3 ≤ 8 * Real.sqrt zetaTwo * ‖primeComponent‖ :=
  pResidual_norm_cube_le_prime_projection primeClosure qResidue_mem_primeClosure

/-- Zero prime component forces the complementary component to vanish as well. -/
theorem complementaryComponent_eq_zero_of_primeComponent_eq_zero
    (h : primeComponent = 0) : complementaryComponent = 0 := by
  unfold complementaryComponent
  rw [primeComponent_eq_zero_iff_displacement.mp h, map_zero]

/-- Conditional research reduction: prime-component vanishing is the open premise. -/
theorem riemannHypothesis_of_primeComponent_eq_zero
    (h : primeComponent = 0) : RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure (primeComponent_eq_zero_iff_one_mem.mp h)

/-- The RH converse retains the unresolved analytic approximation provider explicitly. -/
theorem riemannHypothesis_iff_primeComponent_eq_zero
    (hBD : Pareto.BaezDuarte.BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔ primeComponent = 0 :=
  (QFullDensityConditionalConverse.riemannHypothesis_iff_one_mem hBD).trans
    primeComponent_eq_zero_iff_one_mem.symm

/-- The reciprocal parity atom violates the continuous four-site identity of W. -/
theorem reciprocal_parity_not_mem_primeClosure :
    QShiftedReciprocal.B (qResidue 2) ∉ primeClosure := by
  intro h
  have hh := QSquarefreeMultiplierRigidity.closure_difference_square
    (QPrimeCarryProjection.primeClosure_le_optimizerClosure h) 2 (by decide)
  simp only [SquarefreeRadicalDifference.qDifference,
    QShiftedReciprocal.qSequence_B, qSequence_qResidue] at hh
  norm_num [ArithmeticCumulative.residueFraction] at hh

/-- Reciprocal multiplication does not commute with the closed-prime projection. -/
theorem reciprocal_not_commute_prime_projection :
    ¬ (∀ f : QHilbert,
      primeClosure.starProjection (QShiftedReciprocal.B f) =
        QShiftedReciprocal.B (primeClosure.starProjection f)) := by
  intro h
  have he := h (qResidue 2)
  rw [primeClosure.starProjection_eq_self_iff.mpr
    (qResidue_mem_primeClosure 2 (by decide))] at he
  apply reciprocal_parity_not_mem_primeClosure
  rw [← he]
  exact primeClosure.starProjection_apply_mem _

#print axioms pResidual_norm_cube_le_primeComponent
#print axioms complementaryComponent_eq_zero_iff_reduced_pairings
#print axioms riemannHypothesis_of_primeComponent_eq_zero
#print axioms reciprocal_not_commute_prime_projection
end RiemannResearch.RH.QFullPrimeDecomposition
