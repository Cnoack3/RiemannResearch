/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.MobiusHeadCoercivity
import RiemannResearch.RH.QHeadGramCoercivity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Divisor coercivity in the actual Q Hilbert space

Source: SquarefreeShortHeadSchurResearch20261030.md, with the improved
finite-head factor (2-1/H) ^ 2. All conductors of the chosen finite synthesis
are retained, including composite squarefree and high anchor conductors.

The reciprocal physical coordinate energy is converted exactly to the Q
head norm. The anchored coefficient estimate is unconditional and supplies
the arithmetic input for the complete head-null Schur Gram inequality.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QDivisorHeadCoercivity
open ZetaTwoHilbert ZetaTwoProbability QFiniteSupportDualCriterion QHeadGramCoercivity
open RiemannResearch.Analysis.FiniteDivisorCoercivity

def qSynthesis (s : Finset ℕ) (c : ℕ → ℝ) : QHilbert :=
  ∑ d ∈ s, c d • qResidue d

theorem qSequence_qSynthesis (s : Finset ℕ) (c : ℕ → ℝ) :
    qSequence (qSynthesis s c) = CRTBlock.normalizedResidueSynthesis s c := by
  funext n
  unfold qSynthesis CRTBlock.normalizedResidueSynthesis
  change qSequenceLinear (∑ d ∈ s, c d • qResidue d) n = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_smul]
  change c d * qSequence (qResidue d) n = _
  rw [qSequence_qResidue]

def coercivityConstant (H : ℕ) : ℝ :=
  zetaTwo * (headDifferenceFactor H * mobiusMass H) ^ 2

/-- Actual Q coefficient/slope estimate, retaining the complete finite
conductor synthesis and measuring its genuine physical head. -/
theorem qSynthesis_head_coercivity (H : ℕ) (hH : 1 ≤ H)
    (s : Finset ℕ) (c : ℕ → ℝ) (hs : ∀ d ∈ s, 2 ≤ d) :
    (∑ d ∈ s, c d / (d : ℝ)) ^ 2 +
      (∑ d ∈ s.filter (fun d => d ≤ H), (c d / (d : ℝ)) ^ 2) ≤
        coercivityConstant H * ‖finiteHead H (qSynthesis s c)‖ ^ 2 := by
  have h := CRTBlock.normalizedResidueSynthesis_head_coercivity H hH s c hs
  rw [← qSequence_qSynthesis s c] at h
  change _ ≤ (headDifferenceFactor H * mobiusMass H) ^ 2 *
    (∑ n ∈ Finset.range (H + 1), (qSequence (qSynthesis s c) n / (n : ℝ)) ^ 2) at h
  rw [physical_head_energy] at h
  simpa only [coercivityConstant, mul_assoc, mul_left_comm, mul_comm] using h

def anchoredCoefficients (s : Finset ℕ) (d0 : ℕ) (a0 : ℝ) (a : ℕ → ℝ)
    (d : ℕ) : ℝ :=
  if d = d0 then (d0 : ℝ) * (a0 - ∑ e ∈ s, a e) else (d : ℝ) * a d

def anchoredSynthesis (s : Finset ℕ) (d0 : ℕ) (a0 : ℝ) (a : ℕ → ℝ) : QHilbert :=
  a0 • ((d0 : ℝ) • qResidue d0) +
    ∑ d ∈ s, a d • ((d : ℝ) • qResidue d - (d0 : ℝ) • qResidue d0)

theorem anchored_synthesis_eq (s : Finset ℕ) (d0 : ℕ) (hd0 : d0 ∉ s)
    (a0 : ℝ) (a : ℕ → ℝ) :
    qSynthesis (insert d0 s) (anchoredCoefficients s d0 a0 a) =
      anchoredSynthesis s d0 a0 a := by
  classical
  unfold qSynthesis
  rw [Finset.sum_insert hd0]
  have hsum : (∑ d ∈ s, anchoredCoefficients s d0 a0 a d • qResidue d) =
      ∑ d ∈ s, a d • ((d : ℝ) • qResidue d) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hne : d ≠ d0 := by intro h; subst d; exact hd0 hd
    rw [anchoredCoefficients, if_neg hne, smul_smul]
    congr 1
    ring
  rw [hsum]
  simp only [anchoredCoefficients, anchoredSynthesis,
    smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  simp only [ite_true]
  module

theorem anchored_slope_exact (H : ℕ) (s : Finset ℕ) (d0 : ℕ)
    (hs : ∀ d ∈ s, 2 ≤ d ∧ d ≤ H) (hanchor : H < d0)
    (a0 : ℝ) (a : ℕ → ℝ) :
    (∑ d ∈ insert d0 s, anchoredCoefficients s d0 a0 a d / (d : ℝ)) = a0 := by
  classical
  have hd0 : d0 ∉ s := by intro hd; have := (hs d0 hd).2; omega
  have hd0R : (d0 : ℝ) ≠ 0 := by exact_mod_cast (show d0 ≠ 0 by omega)
  rw [Finset.sum_insert hd0]
  have hsum : (∑ d ∈ s, anchoredCoefficients s d0 a0 a d / (d : ℝ)) =
      ∑ d ∈ s, a d := by
    apply Finset.sum_congr rfl
    intro d hd
    have hne : d ≠ d0 := by intro h; subst d; exact hd0 hd
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by have := (hs d hd).1; omega)
    rw [anchoredCoefficients, if_neg hne]
    field_simp [hdR]
  rw [hsum, anchoredCoefficients, if_pos rfl]
  field_simp [hd0R]
  ring

/-- Unconditional coercivity of the explicit anchored head coordinates.
This is the arithmetic provider for the head-null Schur transfer. -/
theorem anchored_head_coercivity (H : ℕ) (hH : 1 ≤ H) (s : Finset ℕ)
    (d0 : ℕ) (hs : ∀ d ∈ s, 2 ≤ d ∧ d ≤ H) (hanchor : H < d0)
    (a0 : ℝ) (a : ℕ → ℝ) :
    a0 ^ 2 + (∑ d ∈ s, (a d) ^ 2) ≤
      coercivityConstant H * ‖finiteHead H (anchoredSynthesis s d0 a0 a)‖ ^ 2 := by
  classical
  have hd0 : d0 ∉ s := by intro hd; have := (hs d0 hd).2; omega
  have hsall : ∀ d ∈ insert d0 s, 2 ≤ d := by
    intro d hd
    rcases Finset.mem_insert.mp hd with he | hd
    · subst d; omega
    · exact (hs d hd).1
  have hf : (insert d0 s).filter (fun d => d ≤ H) = s := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨he | hd, hle⟩
      · subst d; omega
      · exact hd
    · intro hd
      exact ⟨Or.inr hd, (hs d hd).2⟩
  have hsum : (∑ d ∈ s, (anchoredCoefficients s d0 a0 a d / (d : ℝ)) ^ 2) =
      ∑ d ∈ s, (a d) ^ 2 := by
    apply Finset.sum_congr rfl
    intro d hd
    have hne : d ≠ d0 := by intro h; subst d; exact hd0 hd
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by have := (hs d hd).1; omega)
    rw [anchoredCoefficients, if_neg hne]
    field_simp [hdR]
  have h := qSynthesis_head_coercivity H hH (insert d0 s)
    (anchoredCoefficients s d0 a0 a) hsall
  rw [anchored_slope_exact H s d0 hs hanchor a0 a, hf, hsum,
    anchored_synthesis_eq s d0 hd0 a0 a] at h
  exact h

/-- The proved head estimate forces a strictly positive coercivity constant. -/
theorem coercivityConstant_pos (H : ℕ) (hH : 1 ≤ H) :
    0 < coercivityConstant H := by
  have h := anchored_head_coercivity H hH ∅ (H + 1)
    (by simp) (by omega) 1 (fun _ => 0)
  have hle : (1 : ℝ) ≤ coercivityConstant H *
      ‖finiteHead H (anchoredSynthesis ∅ (H + 1) 1 (fun _ => 0))‖ ^ 2 := by
    simpa using h
  by_contra hn
  have hc : coercivityConstant H ≤ 0 := le_of_not_gt hn
  have hm := mul_nonpos_of_nonpos_of_nonneg hc
    (sq_nonneg ‖finiteHead H (anchoredSynthesis ∅ (H + 1) 1 (fun _ => 0))‖)
  linarith

end RiemannResearch.RH.QDivisorHeadCoercivity
