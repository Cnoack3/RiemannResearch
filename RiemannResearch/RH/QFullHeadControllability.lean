/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.Analysis.DenseProjectionTesting
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QSquarefreeHeadCompression
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! Full legal head interpolation and finite-test injectivity.
Source: continuation of the user-provided uniform dual bound agenda, 22 October 2026.
The proof reuses the repository compensated residue directions.
No uniform energy bound is assumed or proved. -/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QFullHeadControllability
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QSquarefreeLatticePackets QFiniteSupportDualCriterion
open RiemannResearch.Analysis.DenseProjectionTesting

theorem qResidue_mem_legalSpan (d : ℕ) (hd : 2 ≤ d) :
    qResidue d ∈ QFullResidueProjection.legalSpan := by
  apply Submodule.subset_span
  refine ⟨d - 2, ?_⟩
  change qResidue (d - 2 + 2) = qResidue d
  congr 1
  omega

/-- Every finite physical head is attained in the actual full legal span. -/
theorem interpolate_head (M : ℕ) (u : ℕ → ℝ) :
    ∃ F ∈ QFullResidueProjection.legalSpan,
      ∀ n, 0 < n → n ≤ M → qSequence F n = u n := by
  by_cases hM : M = 0
  · subst M
    exact ⟨0, Submodule.zero_mem _, by intro n hn hnM; omega⟩
  let r := M + 1
  have hr : qResidue r ∈ QFullResidueProjection.legalSpan :=
    qResidue_mem_legalSpan r (by dsimp [r]; omega)
  have hstep : ∀ N, N ≤ M → ∃ F ∈ QFullResidueProjection.legalSpan,
      ∀ n, 0 < n → n ≤ N → qSequence F n = u n := by
    intro N
    induction N with
    | zero =>
        intro hN
        exact ⟨0, Submodule.zero_mem _, by intro n hn hnN; omega⟩
    | succ N ih =>
        intro hN
        obtain ⟨F, hF, hh⟩ := ih (by omega)
        have hq : qResidue (N + 1) ∈ QFullResidueProjection.legalSpan := by
          by_cases he : N + 1 = 1
          · rw [he, qResidue_one]
            exact Submodule.zero_mem _
          · exact qResidue_mem_legalSpan (N + 1) (by omega)
        have hv : compensatedResidue (N + 1) r ∈
            QFullResidueProjection.legalSpan :=
          QFullResidueProjection.legalSpan.sub_mem hq
            (QFullResidueProjection.legalSpan.smul_mem _ hr)
        refine ⟨F + (qSequence F (N + 1) - u (N + 1)) •
            compensatedResidue (N + 1) r,
          QFullResidueProjection.legalSpan.add_mem hF
            (QFullResidueProjection.legalSpan.smul_mem _ hv), ?_⟩
        intro n hn hnN
        change qSequenceLinear (_ + _ • _) n = _
        simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        change qSequence F n + (qSequence F (N + 1) - u (N + 1)) *
          qSequence (compensatedResidue (N + 1) r) n = u n
        by_cases he : n = N + 1
        · subst n
          rw [QSquarefreeHeadCompression.compensated_diagonal
            (N + 1) r (by omega) (by dsimp [r]; omega)]
          ring
        · rw [compensatedResidue_head (N + 1) r n (by omega)
            (by dsimp [r]; omega) (by omega) (by dsimp [r]; omega),
            mul_zero, add_zero]
          exact hh n hn (by omega)
  exact hstep M le_rfl

/-- The full projection has trivial kernel on every finite coordinate head. -/
theorem finiteHead_projection_eq_zero_iff (M : ℕ) (a : QHilbert) :
    QFullResidueProjection.closure.starProjection (finiteHead M a) = 0 ↔
      finiteHead M a = 0 := by
  constructor
  · intro hp
    obtain ⟨F, hF, hh⟩ := interpolate_head M (qSequence (finiteHead M a))
    have hFc : F ∈ QFullResidueProjection.closure :=
      QFullResidueProjection.legalSpan.le_topologicalClosure hF
    have hpair := inner_finiteHead_eq_of_matching_head
      M F (finiteHead M a) a hh
    rw [inner_eq_projected_test QFullResidueProjection.closure hFc _, hp,
      inner_zero_right, real_inner_self_eq_norm_sq] at hpair
    have hz : ‖finiteHead M a‖ = 0 := by
      nlinarith [norm_nonneg (finiteHead M a)]
    exact norm_eq_zero.mp hz
  · intro h
    simp only [h, map_zero]

theorem finiteHead_projection_norm_pos (M : ℕ) (a : QHilbert)
    (ha : finiteHead M a ≠ 0) :
    0 < ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖ := by
  apply norm_pos_iff.mpr
  intro hp
  exact ha ((finiteHead_projection_eq_zero_iff M a).mp hp)

/-- The compensated direction is exactly the negative floor on the anchored head. -/
theorem compensatedResidue_floor (d r n : ℕ) (hd : 0 < d) (hnr : n < r) :
    qSequence (compensatedResidue d r) n = -((n / d : ℕ) : ℝ) := by
  rw [compensatedResidue_sequence]
  simp only [residueFraction, Nat.mod_eq_of_lt hnr]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have he : ((n % d : ℕ) : ℝ) + (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast (Nat.mod_add_div n d)
  have hfrac : (r : ℝ) / (d : ℝ) * ((n : ℝ) / (r : ℝ)) =
      (n : ℝ) / (d : ℝ) := by
    field_simp [hdR, hrR]
  rw [hfrac, ← sub_div]
  apply (div_eq_iff hdR).mpr
  nlinarith [he]

end RiemannResearch.RH.QFullHeadControllability
