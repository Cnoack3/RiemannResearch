/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorHeadCoercivity
import RiemannResearch.RH.QHeadGramCoercivity
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Algebra.BigOperators.Option
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# An unconditional inverse bound for the actual squarefree head Schur family

The low family includes every squarefree conductor between 2 and H, including
composite conductors. The screening space is the full actual legal head-null
space at stage N, and its Gram matrix uses the entire Q inner product.

The arithmetic estimate is proved in QDivisorHeadCoercivity. No coercivity
hypothesis appears in the concrete results here. These inverse bounds do not
bound the signed short-head source; that remains a separate arithmetic task.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeSchurCoercivity
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeTailResponse
open QFiniteSupportDualCriterion QDivisorHeadCoercivity QHeadGramCoercivity
open RiemannResearch.Analysis.FiniteGramCoercivity
open RiemannResearch.Analysis.FiniteHilbertGram

/-- The slope coordinate and all the low conductor coordinates. -/
def anchoredFamily (s : Finset ℕ) (d0 : ℕ) : Option s → QHilbert
  | none => (d0 : ℝ) • qResidue d0
  | some d => (d.val : ℝ) • qResidue d.val - (d0 : ℝ) • qResidue d0

def lowCoeff (s : Finset ℕ) (c : Option s → ℝ) (d : ℕ) : ℝ :=
  if hd : d ∈ s then c (some ⟨d, hd⟩) else 0

theorem anchored_coefficient_sq_sum (s : Finset ℕ) (c : Option s → ℝ) :
    (∑ i, (c i) ^ 2) = (c none) ^ 2 + ∑ d ∈ s, (lowCoeff s c d) ^ 2 := by
  classical
  rw [Fintype.sum_option]
  congr 1
  have h := Finset.sum_attach s (fun d => (lowCoeff s c d) ^ 2)
  simpa [lowCoeff] using h

theorem synthesis_anchoredFamily (s : Finset ℕ) (d0 : ℕ)
    (c : Option s → ℝ) :
    Fintype.linearCombination ℝ (anchoredFamily s d0) c =
      anchoredSynthesis s d0 (c none) (lowCoeff s c) := by
  classical
  rw [Fintype.linearCombination_apply, Fintype.sum_option]
  unfold anchoredSynthesis
  simp only [anchoredFamily]
  congr 1
  have h := Finset.sum_attach s (fun d =>
    lowCoeff s c d • ((d : ℝ) • qResidue d - (d0 : ℝ) • qResidue d0))
  simpa [lowCoeff] using h

theorem anchoredFamily_head_coercivity (H : ℕ) (hH : 1 ≤ H)
    (s : Finset ℕ) (d0 : ℕ) (hs : ∀ d ∈ s, 2 ≤ d ∧ d ≤ H)
    (hanchor : H < d0) (c : Option s → ℝ) :
    (∑ i, (c i) ^ 2) ≤ coercivityConstant H *
      ‖finiteHead H (Fintype.linearCombination ℝ (anchoredFamily s d0) c)‖ ^ 2 := by
  rw [anchored_coefficient_sq_sum, synthesis_anchoredFamily]
  exact anchored_head_coercivity H hH s d0 hs hanchor (c none) (lowCoeff s c)

/-- The complete squarefree low dictionary, without prime-only pruning. -/
def lowConductors (H : ℕ) : Finset ℕ :=
  (Finset.Icc 2 H).filter Squarefree

theorem mem_lowConductors (H d : ℕ) :
    d ∈ lowConductors H ↔ (2 ≤ d ∧ d ≤ H) ∧ Squarefree d := by
  simp only [lowConductors, Finset.mem_filter, Finset.mem_Icc]

def squarefreeHeadFamily (H d0 : ℕ) : Option (lowConductors H) → QHilbert :=
  anchoredFamily (lowConductors H) d0

def squarefreeSchurFamily (N H d0 : ℕ) : Option (lowConductors H) → QHilbert :=
  screened (tailStage N H) (squarefreeHeadFamily H d0)

theorem qResidue_mem_stage (N d : ℕ) (hd2 : 2 ≤ d)
    (hdN : d ≤ N + 1) (hsf : Squarefree d) : qResidue d ∈ stage N := by
  unfold stage RiemannResearch.Analysis.ExhaustiveWalk.walkSpan
  apply Submodule.subset_span
  refine ⟨⟨d - 2, by omega⟩, ?_⟩
  change squarefreeAtom (d - 2) = qResidue d
  have he : d - 2 + 2 = d := by omega
  simp only [squarefreeAtom, he, if_pos hsf]

theorem squarefreeHeadFamily_mem_stage (N H d0 : ℕ) (hH : 1 ≤ H)
    (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0)
    (i : Option (lowConductors H)) : squarefreeHeadFamily H d0 i ∈ stage N := by
  have ha := qResidue_mem_stage N d0 (by omega) hd0N hsf
  cases i with
  | none => exact (stage N).smul_mem _ ha
  | some d =>
      have hd := (mem_lowConductors H d.val).mp d.property
      exact (stage N).sub_mem
        ((stage N).smul_mem _ (qResidue_mem_stage N d.val hd.1.1 (by omega) hd.2))
        ((stage N).smul_mem _ ha)

theorem squarefreeSchurFamily_legal (N H d0 : ℕ) (hH : 1 ≤ H)
    (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0)
    (i : Option (lowConductors H)) :
    squarefreeSchurFamily N H d0 i ∈ stage N ∧
      squarefreeSchurFamily N H d0 i ∈ (tailStage N H)ᗮ := by
  constructor
  · exact (stage N).sub_mem (squarefreeHeadFamily_mem_stage N H d0 hH hanchor hd0N hsf i)
      ((tailStage N H).starProjection_apply_mem _).1
  · exact Submodule.sub_starProjection_mem_orthogonal _

/-- Unconditional head coefficient estimate for the complete low family. -/
theorem squarefreeHeadFamily_coercivity (H d0 : ℕ) (hH : 1 ≤ H)
    (hanchor : H < d0) (c : Option (lowConductors H) → ℝ) :
    (∑ i, (c i) ^ 2) ≤ coercivityConstant H *
      ‖finiteHead H (Fintype.linearCombination ℝ (squarefreeHeadFamily H d0) c)‖ ^ 2 := by
  exact anchoredFamily_head_coercivity H hH (lowConductors H) d0
    (fun d hd => ((mem_lowConductors H d).mp hd).1) hanchor c

theorem squarefreeSchurFamily_linearIndependent (N H d0 : ℕ)
    (hH : 1 ≤ H) (hanchor : H < d0) :
    LinearIndependent ℝ (squarefreeSchurFamily N H d0) := by
  exact screened_head_linearIndependent N H (squarefreeHeadFamily H d0)
    (coercivityConstant H) (coercivityConstant_pos H hH).le
    (squarefreeHeadFamily_coercivity H d0 hH hanchor)

/-- Literal inverse of the full Q Schur Gram. No arithmetic provider is assumed. -/
theorem squarefreeSchur_inverseGram_le (N H d0 : ℕ) (hH : 1 ≤ H)
    (hanchor : H < d0) (b : Option (lowConductors H) → ℝ) :
    dotProduct b ((gramMatrix (squarefreeSchurFamily N H d0))⁻¹.mulVec b) ≤
      coercivityConstant H * ∑ i, (b i) ^ 2 := by
  exact screened_head_inverseGram_le N H (squarefreeHeadFamily H d0)
    (coercivityConstant H) (coercivityConstant_pos H hH)
    (squarefreeHeadFamily_coercivity H d0 hH hanchor) b

/-- Actual-stage theorem: every vector is legal, head-null-orthogonal, and its
complete inverse Gram satisfies the N-uniform bound. -/
theorem squarefreeSchur_legal_and_inverse_bound (N H d0 : ℕ) (hH : 1 ≤ H)
    (hanchor : H < d0) (hd0N : d0 ≤ N + 1) (hsf : Squarefree d0) :
    (∀ i, squarefreeSchurFamily N H d0 i ∈ stage N ∧
      squarefreeSchurFamily N H d0 i ∈ (tailStage N H)ᗮ) ∧
    (∀ b : Option (lowConductors H) → ℝ,
      dotProduct b ((gramMatrix (squarefreeSchurFamily N H d0))⁻¹.mulVec b) ≤
        coercivityConstant H * ∑ i, (b i) ^ 2) := by
  exact ⟨squarefreeSchurFamily_legal N H d0 hH hanchor hd0N hsf,
    squarefreeSchur_inverseGram_le N H d0 hH hanchor⟩

/-- Bertrand supplies an actual legal anchor whenever the head is at most
half the dictionary cutoff. Composite low conductors are still all present. -/
theorem exists_squarefreeSchur_legal_and_inverse_bound (N H : ℕ)
    (hH : 1 ≤ H) (hsize : 2 * H ≤ N + 1) :
    ∃ d0 : ℕ, H < d0 ∧ d0 ≤ N + 1 ∧ Squarefree d0 ∧
      (∀ i, squarefreeSchurFamily N H d0 i ∈ stage N ∧
        squarefreeSchurFamily N H d0 i ∈ (tailStage N H)ᗮ) ∧
      (∀ b : Option (lowConductors H) → ℝ,
        dotProduct b ((gramMatrix (squarefreeSchurFamily N H d0))⁻¹.mulVec b) ≤
          coercivityConstant H * ∑ i, (b i) ^ 2) := by
  obtain ⟨d0, hp, hgt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul H (by omega)
  have hN : d0 ≤ N + 1 := hle.trans hsize
  refine ⟨d0, hgt, hN, hp.squarefree, ?_⟩
  exact squarefreeSchur_legal_and_inverse_bound N H d0 hH hgt hN hp.squarefree

end RiemannResearch.RH.QSquarefreeSchurCoercivity
