/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeDimension
import RiemannResearch.RH.QSquarefreeBoundary
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The squarefree projection is not order-positive

The explicit legal vector g_2-g_3 has an absolute value violating the closed
span's four-site relation. A physically positive orthogonal projection would
make its range closed under absolute values, by norm monotonicity and the exact
Pythagorean remainder. Hence the actual squarefree projection is not positive
in the pointwise order. This is distinct from Hilbert operator positivity.

Source: standard Hilbert projection identities (Mathlib's Projection.Submodule);
the explicit arithmetic counterexample was developed in the user's CRT
regularity investigation, 4 November 2026. Wolfram checked the four rational
values diagnostically; the proof below uses exact Lean arithmetic.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeProjectionOrder
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeBoundary

def signChangingLegal : QHilbert := qResidue 2 - qResidue 3

theorem signChangingLegal_mem : signChangingLegal ∈ closure := by
  exact closure.sub_mem
    (QSquarefreeDimension.qResidue_mem_of_squarefree (by norm_num)
      Nat.prime_two.squarefree)
    (QSquarefreeDimension.qResidue_mem_of_squarefree (by norm_num)
      Nat.prime_three.squarefree)

theorem abs_signChangingLegal_fourSite :
    fourSiteFunctional (qAbs signChangingLegal) = -(2 / 3 : ℝ) := by
  rw [fourSiteFunctional_apply]
  simp only [qAbs_sequence, signChangingLegal]
  simp only [← qEvalCLM_apply, map_sub]
  simp only [qEvalCLM_apply, qSequence_qResidue]
  norm_num [ArithmeticCumulative.residueFraction]

theorem abs_signChangingLegal_not_mem : qAbs signChangingLegal ∉ closure := by
  intro h
  have hz := fourSiteFunctional_zero_on_closure h
  rw [abs_signChangingLegal_fourSite] at hz
  norm_num at hz

/-- Positivity is physical order preservation at zero. -/
def PhysicallyPositiveProjection : Prop :=
  ∀ f : QHilbert, (∀ n, 0 ≤ qSequence f n) →
    ∀ n, 0 ≤ qSequence (closure.starProjection f) n

theorem qAbs_mem_of_positive_projection
    (hpos : PhysicallyPositiveProjection) {v : QHilbert} (hv : v ∈ closure) :
    qAbs v ∈ closure := by
  have hpv := Submodule.starProjection_eq_self_iff.mpr hv
  have hplus : ∀ n, 0 ≤ qSequence (qAbs v + v) n := by
    intro n
    simp only [← qEvalCLM_apply, map_add]
    simp only [qEvalCLM_apply, qAbs_sequence]
    linarith [neg_abs_le (qSequence v n)]
  have hminus : ∀ n, 0 ≤ qSequence (qAbs v - v) n := by
    intro n
    simp only [← qEvalCLM_apply, map_sub]
    simp only [qEvalCLM_apply, qAbs_sequence]
    exact sub_nonneg.mpr (le_abs_self _)
  have hdom (n : ℕ) :
      qSequence (qAbs v) n ≤ qSequence (closure.starProjection (qAbs v)) n := by
    have h1 := hpos (qAbs v + v) hplus n
    have h2 := hpos (qAbs v - v) hminus n
    rw [map_add, hpv] at h1
    rw [map_sub, hpv] at h2
    simp only [← qEvalCLM_apply, map_add, map_sub] at h1 h2
    simp only [qEvalCLM_apply] at h1 h2
    rw [qAbs_sequence]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hnorm : ‖qAbs v‖ ^ 2 ≤ ‖closure.starProjection (qAbs v)‖ ^ 2 := by
    rw [qNorm_weighted_sq, qNorm_weighted_sq]
    apply Summable.tsum_le_tsum _ (qSequence_square_summable _)
      (qSequence_square_summable _)
    intro n
    apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg n)
    have ha : 0 ≤ qSequence (qAbs v) n := by
      rw [qAbs_sequence]
      exact abs_nonneg _
    nlinarith [hdom n]
  have hgap := RiemannResearch.Analysis.ResidualizedProjectionKernel.residual_norm_sq
    closure (qAbs v)
  have hz : ‖qAbs v - closure.starProjection (qAbs v)‖ = 0 := by
    nlinarith [norm_nonneg (qAbs v - closure.starProjection (qAbs v))]
  have he := sub_eq_zero.mp (norm_eq_zero.mp hz)
  rw [he]
  exact closure.starProjection_apply_mem _

theorem projection_not_physically_positive : ¬ PhysicallyPositiveProjection := by
  intro h
  exact abs_signChangingLegal_not_mem
    (qAbs_mem_of_positive_projection h signChangingLegal_mem)


end RiemannResearch.RH.QSquarefreeProjectionOrder
