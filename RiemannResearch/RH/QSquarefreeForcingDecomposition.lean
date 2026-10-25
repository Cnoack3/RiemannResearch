/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeCorrectionKernel
import RiemannResearch.RH.QSmoothedResidueAsymptotic
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QShiftedReciprocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QSquarefreeSignedNormal
import RiemannResearch.RH.QUniformTail
import Mathlib.Tactic.FieldSimp

/-!
# Masked first-site forcing and uniform conductor remainder

Source: user-provided signed regularity handoff R1; direct tail localization.
Both singular systems have ambient-vector providers. Coefficient independence
is proved through canonical synthesized responses. No uniform inverse-Gram
physical bound is assumed or concluded.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeForcingDecomposition
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeSmoothedProjection QSquarefreeCorrectionKernel QSquarefreeSignedNormal
open QSmoothedResidueAsymptotic

def leadingAmplitude (N : ℕ) : ℝ := inner ℝ (residual N) leading
def leadingCoordinate (N : ℕ) (i : Fin N) : ℝ :=
  if Squarefree (i.val + 2) then 1 / ((i.val + 2 : ℕ) : ℝ) else 0
def remainder (N : ℕ) (c : Fin N → ℝ) (i : Fin N) : ℝ :=
  forcing N c i - leadingAmplitude N * leadingCoordinate N i

theorem leadingCoordinate_eq_evaluation (N : ℕ) (i : Fin N) :
    leadingCoordinate N i = qSequence (squarefreeAtom i) 1 := by
  by_cases hi : Squarefree (i.val + 2)
  · simp only [leadingCoordinate, squarefreeAtom, if_pos hi]
    rw [qSequence_qResidue]
    simp [ArithmeticCumulative.residueFraction,
      Nat.mod_eq_of_lt (show 1 < i.val + 2 by omega)]
  · simp [leadingCoordinate, squarefreeAtom, hi]

theorem leading_response {N n : ℕ} {x : Fin N → ℝ}
    (hx : ∀ i, ∑ j, gram N i j * x j = qSequence (squarefreeAtom i) n) :
    ∑ i, x i * leadingCoordinate N i = qSequence (kernel N n) 1 := by
  simp_rw [leadingCoordinate_eq_evaluation]
  rw [← synthesis_physical, kernel_synthesis hx]

theorem signed_decomposition {N n : ℕ} {c x : Fin N → ℝ}
    (hc : Normal N qOne c)
    (hx : ∀ i, ∑ j, gram N i j * x j = qSequence (squarefreeAtom i) n) :
    qSequence (movingCorrection N) n =
      leadingAmplitude N * qSequence (kernel N n) 1 +
        ∑ i, x i * remainder N c i := by
  rw [correction_signed_scalar hc hx, ← leading_response hx]
  simp only [remainder, mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  have he : (∑ i, x i * (leadingAmplitude N * leadingCoordinate N i)) =
      ∑ i, leadingAmplitude N * (x i * leadingCoordinate N i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  ring

theorem remainder_eq_inner {N : ℕ} {c : Fin N → ℝ}
    (hc : Normal N qOne c) (i : Fin N) :
    remainder N c i = inner ℝ (squarefreeAtom i)
      (B (residual N) - leadingAmplitude N • evaluation 1) := by
  rw [remainder, forcing_eq hc, inner_sub_right, real_inner_smul_right,
    inner_evaluation, leadingCoordinate_eq_evaluation]

theorem inactive_remainder {N : ℕ} {c : Fin N → ℝ}
    (hc : Normal N qOne c) (i : Fin N) (hi : ¬ Squarefree (i.val + 2)) :
    remainder N c i = 0 := by
  rw [remainder_eq_inner hc]
  simp [squarefreeAtom, hi]

theorem exists_separated_systems {N : ℕ} {c : Fin N → ℝ}
    (hc : Normal N qOne c) :
    ∃ u v : Fin N → ℝ,
      (∀ i, ∑ j, gram N i j * u j = leadingCoordinate N i) ∧
      (∀ i, ∑ j, gram N i j * v j = remainder N c i) := by
  obtain ⟨u, hu, hun⟩ := exists_projection_coefficients N (evaluation 1)
  obtain ⟨v, hv, hvn⟩ := exists_projection_coefficients N
    (B (residual N) - leadingAmplitude N • evaluation 1)
  refine ⟨u, v, ?_, ?_⟩
  · intro i
    rw [leadingCoordinate_eq_evaluation, ← inner_evaluation]
    exact hun i
  · intro i
    rw [remainder_eq_inner hc]
    exact hvn i

theorem remainder_choice_independent {N : ℕ} {c d : Fin N → ℝ}
    (hc : Normal N qOne c) (hd : Normal N qOne d) :
    remainder N c = remainder N d := by
  funext i
  rw [remainder_eq_inner hc, remainder_eq_inner hd]

theorem remainder_response {N n : ℕ} {c x : Fin N → ℝ}
    (hc : Normal N qOne c)
    (hx : ∀ i, ∑ j, gram N i j * x j = qSequence (squarefreeAtom i) n) :
    ∑ i, x i * remainder N c i = qSequence (movingCorrection N) n -
      leadingAmplitude N * qSequence (kernel N n) 1 := by
  linarith [signed_decomposition hc hx]

theorem remainder_response_choice_independent {N n : ℕ} {c d x y : Fin N → ℝ}
    (hc : Normal N qOne c) (hd : Normal N qOne d)
    (hx : ∀ i, ∑ j, gram N i j * x j = qSequence (squarefreeAtom i) n)
    (hy : ∀ i, ∑ j, gram N i j * y j = qSequence (squarefreeAtom i) n) :
    ∑ i, x i * remainder N c i = ∑ i, y i * remainder N d i := by
  rw [remainder_response hc hx, remainder_response hd hy]

theorem active_remainder_sq_bound {N : ℕ} {c : Fin N → ℝ}
    (hc : Normal N qOne c) (i : Fin N) (hi : Squarefree (i.val + 2)) :
    ZetaTwoProbability.zetaTwo * ((i.val + 2 : ℕ) : ℝ) *
      (((i.val + 2 : ℕ) : ℝ) * remainder N c i) ^ 2 ≤ error N := by
  have hd : (((i.val + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have he : ((i.val + 2 : ℕ) : ℝ) * remainder N c i =
      ((i.val + 2 : ℕ) : ℝ) * forcing N c i - leadingAmplitude N := by
    simp only [remainder, leadingCoordinate, if_pos hi]
    field_simp
  rw [he]
  exact forcing_rank_one_bound hc i hi

open Filter QAnnihilatorTailEscape ZetaTwoProbability
open scoped Topology

/-- Uniform conductor little-o for the actual moving residuals, expressed
without supremum or square roots. No quantitative convergence rate or
inverse-Gram bound is asserted. -/
theorem residual_forcing_uniform_little_o (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℕ, ∀ d ≥ D, ∀ N : ℕ,
      zetaTwo * (d : ℝ) *
        ((d : ℝ) * inner ℝ (ZetaTwoOptimizerStage.residual N) (B (qResidue d)) -
          inner ℝ (ZetaTwoOptimizerStage.residual N) leading) ^ 2 ≤ ε := by
  obtain ⟨H, hH⟩ := uniform_tail_tightness_of_tendsto
    ZetaTwoOptimizerStage.residual ZetaTwoOptimizerStage.limitingResidual
    ZetaTwoOptimizerStage.residual_tendsto (Real.sqrt (ε))
    (Real.sqrt_pos.2 (by linarith))
  refine ⟨H + 1, ?_⟩
  intro d hd N
  have hdpos : 0 < d := by omega
  have hsmall := hH (d - 1) (by omega) N
  have hsq : ‖tail (d - 1) (ZetaTwoOptimizerStage.residual N)‖ ^ 2 ≤ ε := by
    have hsqrt := Real.sq_sqrt (show 0 ≤ ε by linarith)
    nlinarith [norm_nonneg (tail (d - 1) (ZetaTwoOptimizerStage.residual N)),
      Real.sqrt_nonneg (ε)]
  exact (signed_forcing_tail_sq_bound (ZetaTwoOptimizerStage.residual N) d hdpos).trans hsq


end RiemannResearch.RH.QSquarefreeForcingDecomposition
