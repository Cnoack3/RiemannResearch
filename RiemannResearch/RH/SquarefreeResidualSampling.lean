/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Part of the RiemannResearch project.
Authors: Christian Noack
-/

import RiemannResearch.Analysis.ProjectionResidualSampling
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ParetoGibbsTailBasis
import Mathlib.Data.Nat.Factorial.Basic
import RiemannResearch.RH.ParetoCoordinateEvaluation
import Mathlib.Tactic.FieldSimp
import RiemannResearch.Analysis.FiniteHilbertGramMatrix

-- The Apache-specific header convention does not determine project licensing.
set_option linter.style.header false

/-!
# Actual squarefree residual sampling

Source: the user's October 4 squarefree DPP manuscript, Sections 7 and 9,
for the physical sampling law and target; Bagchi, arXiv:math/0607733,
Remarks 4 and 8, for the squarefree closure criterion used in the paper.
The formal statements below are deterministic projection theorems.

The cutoff contains every squarefree conductor from 2 through n+1. It is
cofinal with the primorial cutoff, but no formal comparison of those
cofinal spans or formal RH equivalence is claimed here. The exact closure
identification with all original squarefree conductors is proved below.
Constant-target membership remains explicit.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.SquarefreeSampling
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionResidualSampling
open RiemannResearch.RH.ArithmeticCumulative

/-- All original squarefree legal atoms; other indices contribute zero. -/
def atom (i : ℕ) : ThresholdHilbert :=
  if Squarefree (i + 2) then CoefficientStabilization.residueAtom i else 0

abbrev finiteSpace (n : ℕ) : Submodule ℝ ThresholdHilbert :=
  walkSpan atom id n

abbrev closedSpace : Submodule ℝ ThresholdHilbert := dictionaryClosure atom

def residual (n : ℕ) : ThresholdHilbert :=
  hilbertOne - (finiteSpace n).starProjection hilbertOne

def energy (n : ℕ) : ℝ := ‖residual n‖ ^ 2

/-- Physical site i means integer i+1, with its actual Pareto weight. -/
def siteMass (n i : ℕ) : ℝ :=
  paretoWeight i * (hilbertGibbsPhysical (residual n) i) ^ 2 / energy n

def headMass (n : ℕ) (A : Finset ℕ) : ℝ := ∑ i ∈ A, siteMass n i

def headTrace (n : ℕ) (A : Finset ℕ) : ℝ :=
  ∑ i ∈ A,
    ‖closedSpace.starProjection (paretoPointHilbert i) -
      (finiteSpace n).starProjection (paretoPointHilbert i)‖ ^ 2 / paretoWeight i

theorem finiteSpace_le_closedSpace (n : ℕ) : finiteSpace n ≤ closedSpace :=
  le_trans (walkSpan_le atom id n) (Submodule.le_topologicalClosure _)

/-- Remove the zero columns without changing the actual physical finite
subspace. A Gram matrix should be indexed by this filtered subtype. -/
theorem finiteSpace_eq_filteredResidueSpan (n : ℕ) :
    finiteSpace n = Submodule.span ℝ
      (Set.range (fun i : {j : Fin n // Squarefree (j.val + 2)} =>
        CoefficientStabilization.residueAtom i.val.val)) := by
  classical
  change Submodule.span ℝ (Set.range (fun i : Fin n => atom i.val)) =
    Submodule.span ℝ
      (Set.range (fun i : {j : Fin n // Squarefree (j.val + 2)} =>
        CoefficientStabilization.residueAtom i.val.val))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨i, rfl⟩
    change atom i.val ∈ _
    by_cases hs : Squarefree (i.val + 2)
    · rw [atom, if_pos hs]
      exact Submodule.subset_span ⟨⟨i, hs⟩, rfl⟩
    · rw [atom, if_neg hs]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro f ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨i.val, ?_⟩
    simp only [atom, if_pos i.property]

/-- The filtered family consists of distinct original residue atoms, so its
complete Pareto Gram matrix has no zero-padding singularity. -/
theorem filteredResidueAtoms_linearIndependent (n : ℕ) :
    LinearIndependent ℝ
      (fun i : {j : Fin n // Squarefree (j.val + 2)} =>
        CoefficientStabilization.residueAtom i.val.val) := by
  have hinj : Function.Injective
      (fun i : {j : Fin n // Squarefree (j.val + 2)} => i.val.val) := by
    intro i j hij
    exact Subtype.ext (Fin.ext hij)
  exact CoefficientStabilization.residueAtom_linearIndependent.comp _ hinj

theorem finiteSpace_coordinate_zero_factorial {n : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ finiteSpace n) : hilbertSequence f ((n+1).factorial) = 0 := by
  classical
  change f ∈ Submodule.span ℝ (Set.range (fun i : Fin n => atom i.val)) at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨i, rfl⟩ := hf
    change hilbertSequence (atom i.val) ((n+1).factorial) = 0
    by_cases hs : Squarefree (i.val + 2)
    · rw [atom, if_pos hs, CoefficientStabilization.residueAtom,
        normalizedResidueHilbert_sequence]
      have hd : i.val + 2 ∣ (n+1).factorial :=
        Nat.dvd_factorial (by omega) (by omega)
      simp [residueFraction, Nat.mod_eq_zero_of_dvd hd]
    · rw [atom, if_neg hs]
      exact congrFun (hilbertSequenceLinear.map_zero) ((n+1).factorial)
  | zero =>
    exact congrFun (hilbertSequenceLinear.map_zero) ((n+1).factorial)
  | add f g hf hg ihf ihg =>
    have he := congrFun (hilbertSequenceLinear.map_add f g) ((n+1).factorial)
    change hilbertSequence (f+g) ((n+1).factorial) =
      hilbertSequence f ((n+1).factorial) + hilbertSequence g ((n+1).factorial) at he
    rw [he, ihf, ihg, add_zero]
  | smul a f hf ih =>
    have he := congrFun (hilbertSequenceLinear.map_smul a f) ((n+1).factorial)
    change hilbertSequence (a • f) ((n+1).factorial) =
      a * hilbertSequence f ((n+1).factorial) at he
    rw [he, ih, mul_zero]

theorem residual_ne_zero (n : ℕ) : residual n ≠ 0 := by
  intro hz
  have hp : (finiteSpace n).starProjection hilbertOne = hilbertOne :=
    (sub_eq_zero.mp (show hilbertOne - (finiteSpace n).starProjection hilbertOne = 0 from hz)).symm
  have hc := finiteSpace_coordinate_zero_factorial
    ((finiteSpace n).starProjection_apply_mem hilbertOne)
  rw [hp, hilbertOne_sequence] at hc
  have hQ : (n+1).factorial ≠ 0 := Nat.ne_of_gt (Nat.factorial_pos _)
  simp [zeroAnchor, hQ] at hc

theorem energy_pos (n : ℕ) : 0 < energy n := by
  change 0 < ‖residual n‖ ^ 2
  exact sq_pos_of_pos (norm_pos_iff.mpr (residual_ne_zero n))

/-- The actual site weights form a probability distribution at every stage. -/
theorem siteMass_tsum (n : ℕ) : (∑' i, siteMass n i) = 1 := by
  simp only [siteMass, tsum_div_const, hilbertGibbsPhysical_square]
  rw [← hilbert_norm_sq]
  exact div_self (ne_of_gt (energy_pos n))

theorem siteMass_summable (n : ℕ) : Summable (siteMass n) :=
  (hilbertGibbsPhysical_square_summable (residual n)).div_const (energy n)

theorem energy_eq_limit_add (n : ℕ) :
    energy n = limitingError atom hilbertOne +
      ‖closedSpace.starProjection hilbertOne -
        (finiteSpace n).starProjection hilbertOne‖ ^ 2 := by
  exact walkError_eq_limitingError_add atom id hilbertOne n

theorem energy_tendsto : Tendsto energy atTop (𝓝 (limitingError atom hilbertOne)) :=
  walkError_tendsto atom id Function.surjective_id hilbertOne

theorem energy_zero_iff_target_mem :
    limitingError atom hilbertOne = 0 ↔ hilbertOne ∈ closedSpace :=
  limitingError_eq_zero_iff atom hilbertOne

theorem siteMass_nonneg (n i : ℕ) : 0 ≤ siteMass n i := by
  unfold siteMass energy
  exact div_nonneg (mul_nonneg (paretoWeight_pos i).le (sq_nonneg _)) (sq_nonneg _)

/-- A bound on the actual physical coordinate, without replacing the atoms. -/
theorem siteMass_le_projection_trace (n i : ℕ)
    (hTarget : hilbertOne ∈ closedSpace) :
    siteMass n i ≤
      ‖closedSpace.starProjection (paretoPointHilbert i) -
        (finiteSpace n).starProjection (paretoPointHilbert i)‖ ^ 2 / paretoWeight i := by
  have hs := residual_pairing_sq_le_projection_difference
    (finiteSpace n) closedSpace (finiteSpace_le_closedSpace n)
    hilbertOne (paretoPointHilbert i) hTarget
  change (inner ℝ (residual n) (paretoPointHilbert i)) ^ 2 ≤
    energy n * ‖closedSpace.starProjection (paretoPointHilbert i) -
      (finiteSpace n).starProjection (paretoPointHilbert i)‖ ^ 2 at hs
  rw [inner_paretoPoint] at hs
  have hE : 0 < energy n := energy_pos n
  have hw : 0 < paretoWeight i := by unfold paretoWeight; positivity
  unfold siteMass
  apply (div_le_div_iff₀ hE hw).mpr
  nlinarith [hs]

theorem headMass_le_headTrace (n : ℕ) (A : Finset ℕ)
    (hTarget : hilbertOne ∈ closedSpace) :
    headMass n A ≤ headTrace n A := by
  apply Finset.sum_le_sum
  intro i hi
  exact siteMass_le_projection_trace n i hTarget

theorem headTrace_tendsto_zero (A : Finset ℕ) :
    Tendsto (fun n => headTrace n A) atTop (𝓝 0) := by
  have ht (i : ℕ) : Tendsto
      (fun n => ‖closedSpace.starProjection (paretoPointHilbert i) -
        (finiteSpace n).starProjection (paretoPointHilbert i)‖ ^ 2 / paretoWeight i)
      atTop (𝓝 0) := by
    have hp := walkProjection_tendsto atom id Function.surjective_id (paretoPointHilbert i)
    have hc : Tendsto
        (fun _ : ℕ => closedSpace.starProjection (paretoPointHilbert i)) atTop
        (𝓝 (closedSpace.starProjection (paretoPointHilbert i))) := tendsto_const_nhds
    simpa using ((hc.sub hp).norm.pow 2).div_const (paretoWeight i)
  simpa [headTrace] using tendsto_finsetSum A (fun i _ => ht i)

/-- Target membership gives escape from each fixed finite set. It is an
explicit hypothesis, not an arithmetic provider proved by this theorem. -/
theorem headMass_tendsto_zero (A : Finset ℕ)
    (hTarget : hilbertOne ∈ closedSpace) :
    Tendsto (fun n => headMass n A) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => Finset.sum_nonneg (fun i _ => siteMass_nonneg n i))
    (fun n => headMass_le_headTrace n A hTarget)
    (headTrace_tendsto_zero A)

def limitResidual : ThresholdHilbert :=
  hilbertOne - closedSpace.starProjection hilbertOne

def limitingSiteMass (i : ℕ) : ℝ :=
  paretoWeight i * (hilbertGibbsPhysical limitResidual i) ^ 2 /
    limitingError atom hilbertOne

theorem residual_tendsto : Tendsto residual atTop (𝓝 limitResidual) := by
  change Tendsto
    (fun n => hilbertOne - (finiteSpace n).starProjection hilbertOne) atTop
    (𝓝 (hilbertOne - closedSpace.starProjection hilbertOne))
  exact tendsto_const_nhds.sub
    (walkProjection_tendsto atom id Function.surjective_id hilbertOne)

/-- Every actual physical coordinate converges by its already constructed
continuous evaluation map. -/
theorem residual_physical_tendsto (i : ℕ) :
    Tendsto (fun n => hilbertGibbsPhysical (residual n) i) atTop
      (𝓝 (hilbertGibbsPhysical limitResidual i)) := by
  simpa only [Function.comp_def, physicalEvaluationCLM_apply, hilbertGibbsPhysical_eq] using
    ((physicalEvaluationCLM i).continuous.tendsto limitResidual).comp residual_tendsto

/-- A nonzero limiting residual gives pointwise convergence to its genuine
normalized coordinate-square law. -/
theorem siteMass_tendsto_of_limitEnergy_ne_zero (i : ℕ)
    (hE : limitingError atom hilbertOne ≠ 0) :
    Tendsto (fun n => siteMass n i) atTop (𝓝 (limitingSiteMass i)) := by
  have ht :=
    (((residual_physical_tendsto i).pow 2).const_mul (paretoWeight i)).div
      energy_tendsto hE
  convert ht using 1
  · ext n
    simp [siteMass]
  · rfl

/-- Escape of every singleton forces the actual canonical limiting residual
to vanish. The proof does not invoke an RH hypothesis. -/
theorem target_mem_of_siteMass_tendsto_zero
    (h : ∀ i : ℕ, Tendsto (fun n => siteMass n i) atTop (𝓝 0)) :
    hilbertOne ∈ closedSpace := by
  apply energy_zero_iff_target_mem.mp
  by_contra hE
  have hphysical : ∀ i : ℕ, hilbertGibbsPhysical limitResidual i = 0 := by
    intro i
    have hm : limitingSiteMass i = 0 :=
      tendsto_nhds_unique (siteMass_tendsto_of_limitEnergy_ne_zero i hE) (h i)
    have hnum : paretoWeight i * (hilbertGibbsPhysical limitResidual i) ^ 2 = 0 := by
      have hn := congrArg (fun z : ℝ => z * limitingError atom hilbertOne) hm
      unfold limitingSiteMass at hn
      field_simp [hE] at hn
      simpa using hn
    have hs : (hilbertGibbsPhysical limitResidual i) ^ 2 = 0 :=
      (mul_eq_zero.mp hnum).resolve_left (ne_of_gt (paretoWeight_pos i))
    exact sq_eq_zero_iff.mp hs
  have hsequence : hilbertSequence limitResidual = 0 := by
    funext k
    cases k with
    | zero => exact hilbertSequence_zero limitResidual
    | succ i =>
      change hilbertGibbsPhysical limitResidual i = 0
      exact hphysical i
  have hR : limitResidual = 0 := by
    apply hilbertSequence_injective
    rw [hsequence]
    exact (hilbertSequenceLinear.map_zero).symm
  have hz : limitingError atom hilbertOne = 0 := by
    change ‖limitResidual‖ ^ 2 = 0
    rw [hR]
    simp
  exact hE hz

theorem siteMass_tendsto_zero_iff_target_mem :
    (∀ i : ℕ, Tendsto (fun n => siteMass n i) atTop (𝓝 0)) ↔
      hilbertOne ∈ closedSpace := by
  constructor
  · exact target_mem_of_siteMass_tendsto_zero
  · intro h i
    simpa [headMass] using headMass_tendsto_zero {i} h

/-- The complete finite-head escape criterion. This is an exact geometric
equivalence; it does not establish that either side holds. -/
theorem headMass_tendsto_zero_iff_target_mem :
    (∀ A : Finset ℕ, Tendsto (fun n => headMass n A) atTop (𝓝 0)) ↔
      hilbertOne ∈ closedSpace := by
  constructor
  · intro h
    apply target_mem_of_siteMass_tendsto_zero
    intro i
    simpa [headMass] using h {i}
  · intro h A
    exact headMass_tendsto_zero A h

theorem headMass_tendsto_zero_iff_limitEnergy_zero :
    (∀ A : Finset ℕ, Tendsto (fun n => headMass n A) atTop (𝓝 0)) ↔
      limitingError atom hilbertOne = 0 :=
  headMass_tendsto_zero_iff_target_mem.trans energy_zero_iff_target_mem.symm

/-- The squarefree family remains a genuine subfamily of all original legal
residue atoms. No closure equality or RH converse is used. -/
theorem closedSpace_le_fullResidueClosedSpace :
    closedSpace ≤ CoefficientStabilization.closedSpace := by
  change (Submodule.span ℝ (Set.range atom)).topologicalClosure ≤
    (Submodule.span ℝ (Set.range CoefficientStabilization.residueAtom)).topologicalClosure
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro f ⟨i, rfl⟩
  unfold atom
  split_ifs
  · exact Submodule.subset_span ⟨i, rfl⟩
  · exact Submodule.zero_mem _

/-- Conditional research reduction. Open: prove actual finite-head escape
for this squarefree residual sampling law. -/
theorem riemannHypothesis_of_headMass_tendsto_zero
    (h : ∀ A : Finset ℕ, Tendsto (fun n => headMass n A) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply CoefficientStabilization.riemannHypothesis_of_limitCoefficients
  apply CoefficientStabilization.limitCoefficients_eq_mobius_iff_mem.mpr
  exact closedSpace_le_fullResidueClosedSpace
    (headMass_tendsto_zero_iff_target_mem.mp h)

open RiemannResearch.Analysis.FiniteHilbertGram

/-- Complete inverse-Gram coefficients for the actual finite physical
projection. Every squarefree conductor in `2, ..., n+1` occurs. -/
theorem projection_eq_filteredInverseGram (n : ℕ) :
    (finiteSpace n).starProjection hilbertOne =
      ∑ i : {j : Fin n // Squarefree (j.val + 2)},
        (((gramMatrix (fun j : {k : Fin n // Squarefree (k.val + 2)} =>
            CoefficientStabilization.residueAtom j.val.val))⁻¹).mulVec
          (fun j => inner ℝ (CoefficientStabilization.residueAtom j.val.val)
            hilbertOne)) i • CoefficientStabilization.residueAtom i.val.val := by
  classical
  let v : {j : Fin n // Squarefree (j.val + 2)} → ThresholdHilbert :=
    fun i => CoefficientStabilization.residueAtom i.val.val
  have hv : LinearIndependent ℝ v := filteredResidueAtoms_linearIndependent n
  have hspan : finiteSpace n = synthesisSpan v := by
    simpa only [synthesisSpan, v] using finiteSpace_eq_filteredResidueSpan n
  have hinverse : (gramMatrix v)⁻¹.mulVec (cross v hilbertOne) =
      inverseCoeff hv hilbertOne :=
    gramMatrix_inverseSource hv (cross v hilbertOne)
  have hp : (finiteSpace n).starProjection hilbertOne =
      (synthesisSpan v).starProjection hilbertOne := by
    simp only [hspan]
  rw [hp, ← synthesis_inverseCoeff_eq_projection hv hilbertOne,
    Fintype.linearCombination_apply, ← hinverse]
  rfl


open RiemannResearch.Analysis.ExhaustiveWalk

/-- The infinite original atom family with the zero columns removed. -/
def filteredAtom (i : {i : ℕ // Squarefree (i + 2)}) : ThresholdHilbert :=
  CoefficientStabilization.residueAtom i.val

/-- Zero padding changes neither the infinite algebraic span nor its closure. -/
theorem span_atom_eq_filteredAtom_span :
    Submodule.span ℝ (Set.range atom) =
      Submodule.span ℝ (Set.range filteredAtom) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨i, rfl⟩
    by_cases hs : Squarefree (i + 2)
    · rw [atom, if_pos hs]
      exact Submodule.subset_span ⟨⟨i, hs⟩, rfl⟩
    · rw [atom, if_neg hs]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro f ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨i.val, ?_⟩
    simp only [atom, if_pos i.property, filteredAtom]

theorem closedSpace_eq_filteredAtom_closure :
    closedSpace = (Submodule.span ℝ (Set.range filteredAtom)).topologicalClosure := by
  change (Submodule.span ℝ (Set.range atom)).topologicalClosure = _
  rw [span_atom_eq_filteredAtom_span]

/-- Every filtered atom occurs at an explicit original numeric cutoff. -/
theorem filteredAtom_mem_finiteSpace
    (i : {i : ℕ // Squarefree (i + 2)}) :
    filteredAtom i ∈ finiteSpace (i.val + 1) := by
  change filteredAtom i ∈ Submodule.span ℝ
    (Set.range (fun j : Fin (i.val + 1) => atom j.val))
  apply Submodule.subset_span
  refine ⟨⟨i.val, Nat.lt_succ_self i.val⟩, ?_⟩
  simp only [atom, if_pos i.property, filteredAtom]

/-- The numeric cutoff exhausts precisely the actual filtered algebraic span. -/
theorem iSup_finiteSpace_eq_filteredAtom_span :
    (⨆ n : ℕ, finiteSpace n) = Submodule.span ℝ (Set.range filteredAtom) := by
  change (⨆ n : ℕ, walkSpan atom id n) = _
  rw [iSup_walkSpan atom id Function.surjective_id, span_atom_eq_filteredAtom_span]

/-- Independence concerns the true family, not the singular zero-padded walk. -/
theorem filteredAtom_linearIndependent : LinearIndependent ℝ filteredAtom := by
  have hinj : Function.Injective
      (fun i : {i : ℕ // Squarefree (i + 2)} => i.val) := by
    intro i j hij
    exact Subtype.ext hij
  exact CoefficientStabilization.residueAtom_linearIndependent.comp _ hinj

/-- The original Bagchi squarefree dictionary, indexed directly by conductor. -/
def squarefreeConductorAtom
    (d : {d : ℕ // 1 < d ∧ Squarefree d}) : ThresholdHilbert :=
  normalizedResidueHilbert d.val (by have hd := d.property.1; omega)

/-- The shift from index i to conductor i+2 affects no actual atom. -/
theorem filteredAtom_range_eq_squarefreeConductorAtom_range :
    Set.range filteredAtom = Set.range squarefreeConductorAtom := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨⟨i.val + 2, ⟨by omega, i.property⟩⟩, ?_⟩
    rfl
  · rintro ⟨d, rfl⟩
    have hd : d.val - 2 + 2 = d.val := by
      have hd1 := d.property.1
      omega
    refine ⟨⟨d.val - 2, ?_⟩, ?_⟩
    · simpa only [hd] using d.property.2
    · simp only [filteredAtom, squarefreeConductorAtom,
        CoefficientStabilization.residueAtom, hd]

/-- Exact closure equality with all original squarefree conductors. No RH-to-
membership provider is introduced by this purely structural identification. -/
theorem closedSpace_eq_squarefreeConductorAtom_closure :
    closedSpace =
      (Submodule.span ℝ (Set.range squarefreeConductorAtom)).topologicalClosure := by
  rw [closedSpace_eq_filteredAtom_closure,
    filteredAtom_range_eq_squarefreeConductorAtom_range]

theorem target_mem_iff_mem_squarefreeConductorAtom_closure :
    hilbertOne ∈ closedSpace ↔
      hilbertOne ∈
        (Submodule.span ℝ (Set.range squarefreeConductorAtom)).topologicalClosure := by
  rw [closedSpace_eq_squarefreeConductorAtom_closure]

end RiemannResearch.RH.Pareto.SquarefreeSampling
