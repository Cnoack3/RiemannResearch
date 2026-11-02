/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.CRTSquarefreeBoundedTail
import RiemannResearch.RH.CoupledCorrectionRHBridge
import RiemannResearch.RH.QWeightedResidues
import RiemannResearch.RH.QCesaroEnergy
import RiemannResearch.RH.QCesaroLowerGrowth
import RiemannResearch.RH.SquarefreeWeightedPrimitives
import RiemannResearch.Analysis.FiniteWeightedRefinement
import RiemannResearch.Analysis.LowerLogGrowth
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Complete weighted residue energy criterion for RH

Source: user-provided Cesàro weighted-CRT manuscript, 1 November 2026,
sections "The criterion to be supplied with an arithmetic family" and
"The exact arithmetic measure on a periodic primitive". These sections
supply the statement and intended assembly.

The input consists of actual legal zero-mean divisor-residue primitives.
The exact energy identity discharges summability and converts the finite
residue energy to the existing complete latent-Q criterion. The statement
holds for arbitrary positive periods, hence in particular for squarefree
periods. Heads use only positive indices. Amplitudes need only be nonzero.

Conditional research reduction: constructing a cofinal legal exact-head
family with zero normalized lower logarithmic energy growth remains Open.
No such growth provider, and no unconditional RH theorem, is proved here.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

theorem divisorResidueSpan_mem_legal {L : ℕ} {g : ℕ → ℝ}
    (hg : g ∈ divisorResidueSpan L) : g ∈ legalSeedSpan allPositiveSeeds := by
  have hs : divisorResidueSpan L ≤ legalSeedSpan allPositiveSeeds := by
    apply Submodule.span_le.mpr
    rintro f ⟨d, hd, _, rfl⟩
    exact residueFraction_mem_legal d (by omega)
  exact hs hg


end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.WeightedResidueRHCriterion
open ArithmeticCumulative Pareto QWeightedResidues
open SquarefreeWeightedPrimitives QCesaroEnergy QCesaroLowerGrowth
open RiemannResearch.Analysis.FiniteWeightedRefinement
open RiemannResearch.Analysis.SubpolynomialWindow

/-- Conditional research reduction: the cofinal lower-growth provider remains open. -/
theorem riemannHypothesis_of_legal_residue_lower_growth
    (L H : ℕ → ℕ) (hL : ∀ j, 0 < L j)
    (R : (j : ℕ) → Fin (L j) → ℝ) (c : ℕ → ℝ)
    (hlegal : ∀ j, IsLegalPrimitive (L j) (R j))
    (hc : ∀ j, c j ≠ 0)
    (hhead : ∀ j n, 0 < n → n ≤ H j →
      R j ⟨n % L j, Nat.mod_lt n (hL j)⟩ = c j * (n : ℝ))
    (hH : Tendsto H atTop atTop)
    (hsmall : lowerLogGrowth
      (fun j => energy (residueWeight (L j)) (R j) / |c j| ^ 2)
      (fun j => (H j : ℝ)) = 0) : RiemannHypothesis := by
  classical
  choose g hg hz hR using hlegal
  have hp (j : ℕ) := legal_cumulative_periodic (g j) (L j) (hg j) (hz j)
  have hcum (j n : ℕ) (hn : n ≤ H j) :
      cumulative (g j) n = c j * (n : ℝ) := by
    by_cases hn0 : n = 0
    · subst n
      simp
    calc
      _ = cumulative (g j) (n % L j) := ((hp j).map_mod_nat n).symm
      _ = R j ⟨n % L j, Nat.mod_lt n (hL j)⟩ := (hR j ⟨n % L j, Nat.mod_lt n (hL j)⟩).symm
      _ = _ := hhead j n (Nat.pos_of_ne_zero hn0) hn
  have hheadg : ∀ j n, 0 < n → n ≤ H j → g j n = c j := by
    intro j n hn hnH
    cases n with
    | zero => omega
    | succ m =>
      have h1 := hcum j (m + 1) hnH
      have h0 := hcum j m (by omega)
      have hs := cumulative_succ (g j) m
      rw [Nat.cast_add, Nat.cast_one] at h1
      nlinarith
  have he (j : ℕ) :
      qConditionalMeanSquare (g j) = energy (residueWeight (L j)) (R j) :=
    (legalPrimitive_energy (L j) (hL j) (R j) (g j) (hg j) (hz j) (hR j)).symm
  apply riemannHypothesis_of_q_lower_growth_normalized
    allPositiveSeeds (by intro a ha; exact ha) g H c
    (fun j => divisorResidueSpan_mem_legal (hg j)) hc hheadg hH
  simpa only [he] using hsmall

end RiemannResearch.RH.WeightedResidueRHCriterion
