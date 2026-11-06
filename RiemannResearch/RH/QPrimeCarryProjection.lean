/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import RiemannResearch.RH.QSimultaneousCRT
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QPrimeProjectionLimit

/-!
# Canonical prime and carry projections in the physical Q Hilbert space

Source: *Projection Displacement, Prime Atoms, and Carries*, 5 November 2026,
page 3. This applies the nested Hilbert-space decomposition to the actual
prime residue span and the actual squarefree optimizer closure. The CRT
identity identifies the canonical carry space with the closed span of
the orthogonally projected canonical carries.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QPrimeCarryProjection

open ZetaTwoHilbert ZetaTwoProbability QSimultaneousCRT
open ZetaTwoParetoTransfer
open QSquarefreeDisplacementRigidity QSquarefreeFiniteDisplacement
open RiemannResearch.Analysis.NestedOrthogonalDecomposition

/-- The closed span of all prime residue atoms. -/
abbrev primeClosure : Submodule ℝ QHilbert := primeSpan.topologicalClosure

/-- The canonical carry complement inside the actual legal space. -/
abbrev carryClosure : Submodule ℝ QHilbert :=
  ZetaTwoOptimizerStage.closure ⊓ primeClosureᗮ

theorem primeClosure_le_optimizerClosure :
    primeClosure ≤ ZetaTwoOptimizerStage.closure := by
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact Submodule.topologicalClosure_mono primeSpan_le_squarefreeSpan

instance carryClosure_hasOrthogonalProjection : carryClosure.HasOrthogonalProjection :=
  carry_hasOrthogonalProjection primeClosure_le_optimizerClosure

theorem qResidue_mem_primeClosure (p : ℕ) (hp : p.Prime) :
    qResidue p ∈ primeClosure :=
  primeSpan.le_topologicalClosure
    (Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩)

theorem primeSynthesis_mem_primeClosure (d : ℕ) :
    primeSynthesis d ∈ primeClosure :=
  primeSpan.le_topologicalClosure (primeSynthesis_mem_primeSpan d)

/-- Projecting away from all prime atoms removes the entire CRT prime synthesis. -/
theorem orthogonal_primeSynthesis (d : ℕ) :
    primeClosureᗮ.starProjection (primeSynthesis d) = 0 :=
  Submodule.starProjection_orthogonal_apply_eq_zero
    (primeSynthesis_mem_primeClosure d)

/-- The projected carry is exactly the negative of the projected residue atom. -/
theorem projected_canonicalCarry (d : ℕ) :
    primeClosureᗮ.starProjection (canonicalCarry d) =
      -(primeClosureᗮ.starProjection (qResidue d)) := by
  rw [canonicalCarry_eq, map_sub, orthogonal_primeSynthesis, zero_sub]

/-- Projection onto the actual carry space is the difference of nested projections. -/
theorem carry_projection_eq :
    carryClosure.starProjection =
      ZetaTwoOptimizerStage.closure.starProjection - primeClosure.starProjection :=
  carry_projection primeClosure_le_optimizerClosure

/-- The actual legal space is the orthogonal sum of prime and carry spaces. -/
theorem optimizerClosure_eq_prime_sup_carry :
    ZetaTwoOptimizerStage.closure = primeClosure ⊔ carryClosure :=
  (prime_sup_carry primeClosure_le_optimizerClosure).symm

theorem prime_carry_orthogonal {w c : QHilbert}
    (hw : w ∈ primeClosure) (hc : c ∈ carryClosure) :
    inner ℝ w c = 0 :=
  prime_carry_inner_eq_zero hw hc

/-- The canonical prime component of the actual matched displacement. -/
def primeDisplacement : QHilbert := primeClosure.starProjection displacement

/-- The canonical carry component of the actual matched displacement. -/
def carryDisplacement : QHilbert := carryClosure.starProjection displacement

theorem displacement_eq_prime_add_carry :
    displacement = primeDisplacement + carryDisplacement :=
  (projection_split_of_mem primeClosure_le_optimizerClosure displacement_mem).symm

theorem carryDisplacement_eq_sub :
    carryDisplacement = displacement - primeDisplacement := by
  change carryClosure.starProjection displacement =
    displacement - primeClosure.starProjection displacement
  rw [carry_projection_apply primeClosure_le_optimizerClosure,
    ZetaTwoOptimizerStage.closure.starProjection_eq_self_iff.mpr displacement_mem]

theorem displacement_norm_sq_split :
    ‖displacement‖ ^ 2 = ‖primeDisplacement‖ ^ 2 + ‖carryDisplacement‖ ^ 2 :=
  norm_sq_split_of_mem primeClosure_le_optimizerClosure displacement_mem

/-- Quantitative control by the actual canonical prime component. -/
theorem pResidual_cube_le_primeDisplacement :
    (‖toPareto pResidual‖ ^ 2) ^ 3 ≤
      64 * zetaTwo * ‖primeDisplacement‖ ^ 2 :=
  pResidual_cube_le_prime_projection primeClosure qResidue_mem_primeClosure

/-- Vanishing of the canonical prime component is equivalent to full displacement vanishing. -/
theorem primeDisplacement_eq_zero_iff :
    primeDisplacement = 0 ↔ displacement = 0 :=
  prime_projection_eq_zero_iff_displacement_eq_zero
    primeClosure qResidue_mem_primeClosure

/-- Finite matched residuals are controlled by their actual closed-prime projection. -/
theorem finitePResidual_cube_le_closedPrimeProjection (N : ℕ) :
    (‖toPareto (qOne - finitePFit N)‖ ^ 2) ^ 3 ≤
      max ((8 / ((N : ℝ) + 1)) ^ 3)
        (64 * zetaTwo * ‖primeClosure.starProjection (finiteDisplacement N)‖ ^ 2) :=
  finitePResidual_cube_le_prime_projection N primeClosure
    (fun p hp _ => qResidue_mem_primeClosure p hp)

/-- The prime components of the actual matched finite projections converge in norm. -/
theorem finite_prime_components_tendsto :
    Tendsto (fun N => primeClosure.starProjection (finiteDisplacement N)) atTop
      (𝓝 primeDisplacement) :=
  prime_component_tendsto finiteDisplacement_tendsto

/-- The carry components of the actual matched finite projections converge in norm. -/
theorem finite_carry_components_tendsto :
    Tendsto (fun N => carryClosure.starProjection (finiteDisplacement N)) atTop
      (𝓝 carryDisplacement) :=
  (carryClosure.starProjection.continuous.tendsto displacement).comp
    finiteDisplacement_tendsto

/-- The actual canonical CRT carries after removing their prime components. -/
def projectedCarrySpan : Submodule ℝ QHilbert :=
  Submodule.span ℝ (Set.range (fun d : SquarefreeConductor =>
    primeClosureᗮ.starProjection (canonicalCarry d.val)))

theorem projected_residue_span_eq_projectedCarrySpan :
    Submodule.span ℝ
      (primeClosureᗮ.starProjection ''
        Set.range (fun d : SquarefreeConductor => qResidue d.val)) =
      projectedCarrySpan := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨y, ⟨d, rfl⟩, rfl⟩
    change primeClosureᗮ.starProjection (qResidue d.val) ∈ projectedCarrySpan
    have hc : primeClosureᗮ.starProjection (canonicalCarry d.val) ∈
        projectedCarrySpan := Submodule.subset_span ⟨d, rfl⟩
    have hn := projectedCarrySpan.neg_mem hc
    simpa only [projected_canonicalCarry, neg_neg] using hn
  · change Submodule.span ℝ _ ≤ _
    apply Submodule.span_le.mpr
    rintro x ⟨d, rfl⟩
    change primeClosureᗮ.starProjection (canonicalCarry d.val) ∈
      Submodule.span ℝ (primeClosureᗮ.starProjection ''
        Set.range (fun d : SquarefreeConductor => qResidue d.val))
    rw [projected_canonicalCarry]
    apply (Submodule.span ℝ _).neg_mem
    exact Submodule.subset_span ⟨qResidue d.val, ⟨d, rfl⟩, rfl⟩

/-- The actual carry complement is precisely the closed span of projected CRT carries. -/
theorem carryClosure_eq_projectedCarrySpan_closure :
    carryClosure = projectedCarrySpan.topologicalClosure := by
  have hV :
      (Submodule.span ℝ
        (Set.range (fun d : SquarefreeConductor => qResidue d.val))).topologicalClosure =
      ZetaTwoOptimizerStage.closure := by
    change qSquarefreeCRTSpan.topologicalClosure = ZetaTwoOptimizerStage.closure
    exact QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure.symm
  have h := carry_eq_closure_projected_generators
    primeClosure_le_optimizerClosure
    (Set.range (fun d : SquarefreeConductor => qResidue d.val)) hV
  rw [projected_residue_span_eq_projectedCarrySpan] at h
  exact h

/-- The paper's prime and projected-carry closed-span decomposition. -/
theorem optimizerClosure_eq_prime_sup_projected_carries :
    ZetaTwoOptimizerStage.closure =
      primeClosure ⊔ projectedCarrySpan.topologicalClosure := by
  rw [← carryClosure_eq_projectedCarrySpan_closure]
  exact optimizerClosure_eq_prime_sup_carry

end RiemannResearch.RH.QPrimeCarryProjection
