/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueNormalizationBounds
import RiemannResearch.Analysis.GramSchmidtTriangular
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.Filter.Cofinite
import Lean.Elab.Tactic.Omega

/-!
# Residue triangular specialization for distinct conductors

The arbitrary-index independence theorem removes the finite-index limitation
of QCovarianceInvertibility.qResidue_linearIndependent, using the same checked
Pareto residue family and its linear pullback. No squarefree assumption is
needed: all pairwise distinct conductors greater than one are independent.
-/

noncomputable section
open Filter InnerProductSpace
open scoped Topology

namespace RiemannResearch.RH.QResidueTriangular

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.TriangularCoefficientBounds
open RiemannResearch.Analysis.GramSchmidtTriangular
open QResidueNormalizationBounds

/-- All distinct Q residue atoms of conductor greater than one are independent,
with no finiteness restriction on the index type. -/
theorem qResidue_linearIndependent_injective {ι : Type*} (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    LinearIndependent ℝ (fun i => qResidue (d i)) := by
  have hinj' : Function.Injective (fun i => d i - 2) := by
    intro i j hij
    change d i - 2 = d j - 2 at hij
    apply hinj
    have hi := hd i
    have hj := hd j
    omega
  have hp := residueAtom_linearIndependent.comp (fun i => d i - 2) hinj'
  have hmap (i : ι) : toParetoLinear (qResidue (d i)) = residueAtom (d i - 2) := by
    change toPareto (qResidue (d i)) = _
    have hi : d i = (d i - 2) + 2 := by have h := hd i; omega
    nth_rw 1 [hi]
    exact toPareto_residueAtom _
  apply LinearIndependent.of_comp toParetoLinear
  simpa only [Function.comp_def, hmap] using hp

/-- Direct conductor formulation of the diagonal lower bound. -/
theorem inverse_scale_lower_of_injective {ι : Type*} [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [WellFoundedLT ι] (d : ι → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) (j : ι) :
    Real.sqrt (zetaTwo * (d j : ℝ) / 2) ≤
      (‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖)⁻¹ :=
  inverse_scale_lower d j (by have h := hd j; omega)
    (qResidue_linearIndependent_injective d hd hinj)

/-- Direct conductor formulation of divergence of the normalization diagonal. -/
theorem inverse_scale_tendsto_atTop_of_injective (d : ℕ → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    Tendsto (fun j => (‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖)⁻¹)
      atTop atTop :=
  inverse_scale_tendsto_atTop d hinj.nat_tendsto_atTop
    (qResidue_linearIndependent_injective d hd hinj)

/-- Injective conductor formulation for the standard l2 coefficient matrix. -/
theorem no_bounded_normalization_matrix_of_injective (d : ℕ → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d)
    (A : ℕ → ℕ → ℝ)
    (hdiag : ∀ j, A j j = (‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖)⁻¹) :
    ¬ ∃ T : Coefficients →L[ℝ] Coefficients,
      ∀ i j, (T (coordinateUnit j)) i = A i j :=
  no_bounded_normalization_matrix d hinj.nat_tendsto_atTop
    (qResidue_linearIndependent_injective d hd hinj) A hdiag

/-- Injective conductor formulation for the distinct physical Q-space question. -/
theorem no_continuous_atom_normalizer_of_injective (d : ℕ → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    ¬ ∃ T : QHilbert →L[ℝ] QHilbert,
      ∀ j, T (qResidue (d j)) = gramSchmidtNormed ℝ (fun i => qResidue (d i)) j :=
  no_continuous_atom_normalizer d hinj.nat_tendsto_atTop
    (qResidue_linearIndependent_injective d hd hinj)

/-- The actual triangular coefficient matrix has the reciprocal innovation scale
on its diagonal. -/
theorem entry_diagonal_reciprocal (d : ℕ → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) (j : ℕ) :
    entry (fun i => qResidue (d i)) j j =
      (‖gramSchmidt ℝ (fun i => qResidue (d i)) j‖)⁻¹ :=
  diagonal_reciprocal (qResidue_linearIndependent_injective d hd hinj) j

/-- Explicit conductor lower bound for each actual diagonal matrix entry. -/
theorem entry_diagonal_lower (d : ℕ → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) (j : ℕ) :
    Real.sqrt (zetaTwo * (d j : ℝ) / 2) ≤
      entry (fun i => qResidue (d i)) j j := by
  rw [entry_diagonal_reciprocal d hd hinj j]
  exact inverse_scale_lower_of_injective d hd hinj j

/-- Distinct residue conductors force the actual triangular diagonal to diverge. -/
theorem entry_diagonal_tendsto_atTop (d : ℕ → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    Tendsto (fun j => entry (fun i => qResidue (d i)) j j) atTop atTop := by
  simpa only [entry_diagonal_reciprocal d hd hinj] using
    inverse_scale_tendsto_atTop_of_injective d hd hinj

/-- The actual infinite triangular coefficient matrix has no bounded realization
on standard l2. This is an unconditional coefficient-space obstruction. -/
theorem no_bounded_entry_columns (d : ℕ → ℕ)
    (hd : ∀ i, 1 < d i) (hinj : Function.Injective d) :
    ¬ ∃ T : Coefficients →L[ℝ] Coefficients,
      ∀ i j, (T (coordinateUnit j)) i = entry (fun k => qResidue (d k)) i j :=
  no_bounded_normalization_matrix_of_injective d hd hinj
    (entry (fun i => qResidue (d i))) (entry_diagonal_reciprocal d hd hinj)

end RiemannResearch.RH.QResidueTriangular
