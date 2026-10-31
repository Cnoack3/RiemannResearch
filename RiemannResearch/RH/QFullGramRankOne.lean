/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.RankOneCoefficientCoercivity
import RiemannResearch.RH.QDivisorHeadCoercivity
import RiemannResearch.RH.QAnnihilatorTailEscape
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Full-Q inverse Gram bound retaining the leading slope square

Source: the exact coefficient energy in SquarefreeShortHeadSchurResearch20261030.md,
with the user-requested improvement formalized on 31 October 2026.
The dictionary may be any finite set of conductors in [2,H]. In particular
the final theorem uses every squarefree conductor through N+1, including
composites. The Gram uses the entire Q inner product. Its inverse bound
subtracts the explicit rank-one term; no signed response estimate is assumed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFullGramRankOne
open ZetaTwoHilbert ZetaTwoProbability QFiniteSupportDualCriterion
open QDivisorHeadCoercivity QHeadGramCoercivity QAnnihilatorTailEscape
open RiemannResearch.Analysis.FiniteDivisorCoercivity
open RiemannResearch.Analysis.RankOneCoefficientCoercivity
open RiemannResearch.Analysis.FiniteGramCoercivity
open RiemannResearch.Analysis.FiniteHilbertGram

def normalizedFamily (s : Finset ℕ) (d : s) : QHilbert :=
  (d.val : ℝ) • qResidue d.val

def normalizedCoefficients (s : Finset ℕ) (a : s → ℝ) (d : ℕ) : ℝ :=
  if hd : d ∈ s then (d : ℝ) * a ⟨d, hd⟩ else 0

theorem normalizedFamily_synthesis (s : Finset ℕ) (a : s → ℝ) :
    Fintype.linearCombination ℝ (normalizedFamily s) a =
      qSynthesis s (normalizedCoefficients s a) := by
  classical
  have h := Finset.sum_attach s
    (fun d => normalizedCoefficients s a d • qResidue d)
  simpa [Fintype.linearCombination_apply, normalizedFamily, qSynthesis,
    normalizedCoefficients, smul_smul, mul_comm] using h

theorem normalizedCoefficients_div (s : Finset ℕ) (a : s → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) (d : s) :
    normalizedCoefficients s a d.val / (d.val : ℝ) = a d := by
  have hdR : (d.val : ℝ) ≠ 0 := by
    exact_mod_cast (show d.val ≠ 0 by have := hs d.val d.property; omega)
  simp only [normalizedCoefficients, dif_pos d.property]
  field_simp [hdR]

theorem normalizedCoefficients_energy (s : Finset ℕ) (a : s → ℝ)
    (hs : ∀ d ∈ s, 2 ≤ d) :
    (∑ d ∈ s, normalizedCoefficients s a d / (d : ℝ)) ^ 2 +
      (∑ d ∈ s, (normalizedCoefficients s a d / (d : ℝ)) ^ 2) =
      coefficientEnergy a := by
  have hsum :
      (∑ d ∈ s, normalizedCoefficients s a d / (d : ℝ)) = ∑ d : s, a d := by
    calc
      _ = ∑ d : s, normalizedCoefficients s a d.val / (d.val : ℝ) :=
        (Finset.sum_attach s _).symm
      _ = _ := Finset.sum_congr rfl (fun d _ => normalizedCoefficients_div s a hs d)
  have hsquare :
      (∑ d ∈ s, (normalizedCoefficients s a d / (d : ℝ)) ^ 2) =
        ∑ d : s, (a d) ^ 2 := by
    calc
      _ = ∑ d : s, (normalizedCoefficients s a d.val / (d.val : ℝ)) ^ 2 :=
        (Finset.sum_attach s _).symm
      _ = _ := Finset.sum_congr rfl (fun d _ =>
        congrArg (fun x : ℝ => x ^ 2) (normalizedCoefficients_div s a hs d))
  rw [hsum, hsquare]
  unfold coefficientEnergy
  ring

/-- The slope square and every coefficient square control the complete norm. -/
theorem normalizedFamily_rankOne_coercivity (H : ℕ) (hH : 1 ≤ H)
    (s : Finset ℕ) (hs : ∀ d ∈ s, 2 ≤ d ∧ d ≤ H) (a : s → ℝ) :
    coefficientEnergy a ≤
      coercivityConstant H * ‖Fintype.linearCombination ℝ (normalizedFamily s) a‖ ^ 2 := by
  have h := qSynthesis_head_coercivity H hH s (normalizedCoefficients s a)
    (fun d hd => (hs d hd).1)
  have hfilter : s.filter (fun d => d ≤ H) = s :=
    Finset.filter_true_of_mem (fun d hd => (hs d hd).2)
  rw [hfilter, normalizedCoefficients_energy s a (fun d hd => (hs d hd).1),
    ← normalizedFamily_synthesis] at h
  have hn : ‖finiteHead H (Fintype.linearCombination ℝ (normalizedFamily s) a)‖ ^ 2 ≤
      ‖Fintype.linearCombination ℝ (normalizedFamily s) a‖ ^ 2 := by
    have hb := finiteHead_norm_le H
      (Fintype.linearCombination ℝ (normalizedFamily s) a)
    nlinarith [norm_nonneg (finiteHead H
      (Fintype.linearCombination ℝ (normalizedFamily s) a)),
      norm_nonneg (Fintype.linearCombination ℝ (normalizedFamily s) a)]
  exact h.trans (mul_le_mul_of_nonneg_left hn (coercivityConstant_pos H hH).le)

theorem normalizedFamily_linearIndependent (H : ℕ) (hH : 1 ≤ H)
    (s : Finset ℕ) (hs : ∀ d ∈ s, 2 ≤ d ∧ d ≤ H) :
    LinearIndependent ℝ (normalizedFamily s) :=
  linearIndependent_of_rankOne_coercive _ (coercivityConstant H)
    (normalizedFamily_rankOne_coercivity H hH s hs)

/-- Actual complete-Q inverse, with its negative rank-one correction retained. -/
theorem normalizedFamily_inverseGram_rankOne (H : ℕ) (hH : 1 ≤ H)
    (s : Finset ℕ) (hs : ∀ d ∈ s, 2 ≤ d ∧ d ≤ H) (b : s → ℝ) :
    dotProduct b ((gramMatrix (normalizedFamily s))⁻¹.mulVec b) ≤
      coercivityConstant H *
        ((∑ d : s, b d ^ 2) - (∑ d : s, b d) ^ 2 / ((s.card : ℝ) + 1)) := by
  classical
  simpa only [Fintype.card_coe] using inverseGram_rankOne_quadratic_le
    (normalizedFamily_linearIndependent H hH s hs)
    (coercivityConstant H) (coercivityConstant_pos H hH)
    (normalizedFamily_rankOne_coercivity H hH s hs) b

/-- Every squarefree conductor, not just primes, occurs in the concrete family. -/
def completeSquarefreeFamily (N : ℕ) :
    ((Finset.Icc 2 (N + 1)).filter Squarefree) → QHilbert :=
  normalizedFamily ((Finset.Icc 2 (N + 1)).filter Squarefree)

/-- Unconditional full-squarefree inverse-Gram estimate with improved constant
and leading-slope subtraction. -/
theorem completeSquarefree_inverseGram_rankOne (N : ℕ)
    (b : ((Finset.Icc 2 (N + 1)).filter Squarefree) → ℝ) :
    dotProduct b ((gramMatrix (completeSquarefreeFamily N))⁻¹.mulVec b) ≤
      coercivityConstant (N + 1) *
        ((∑ d, b d ^ 2) - (∑ d, b d) ^ 2 /
          ((((Finset.Icc 2 (N + 1)).filter Squarefree).card : ℝ) + 1)) := by
  apply normalizedFamily_inverseGram_rankOne (N + 1) (by omega)
  intro d hd
  exact Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1

end RiemannResearch.RH.QFullGramRankOne
