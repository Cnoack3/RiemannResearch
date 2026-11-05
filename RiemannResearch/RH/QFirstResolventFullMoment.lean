/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeFiniteMoment
import RiemannResearch.RH.MertensFullDisplacement
import RiemannResearch.RH.QSquarefreeDisplacementResolvent
import RiemannResearch.RH.QSquarefreeSmoothedProjection

/-!
# A fixed first-step test at the full Lee–Leong weight

The same arithmetic majorant applies to the screened orthogonal vector
formed from the Q residual. Its mean is a faithful positive quadratic form.
The full infinite iteration can therefore be replaced by its first source.
-/
noncomputable section
open Filter
namespace RiemannResearch.RH.QMertensFirstMoment
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeSmoothedProjection QSquarefreeDisplacementResolvent RiemannResearch.Analysis

/-- The full-profile moment in the physical Q normalization. -/
def fullCorrectionMoment (δ : ℝ) (v : QHilbert) : Prop :=
  Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
    Real.exp (-(leeLeongFullDisplacementExponent δ n))) * |qSequence v n|)

/-- A single positive-margin weighted moment on the fixed first source suffices. -/
theorem residual_zero_iff_full_correction_moment (hLL : LeeLeongMertensEstimate)
    (δ : ℝ) (hδ : 0 < δ) : limitingResidual = 0 ↔ fullCorrectionMoment δ correction := by
  constructor
  · intro hr
    have hz (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by cases n <;> simp [qSequence]
    simp [fullCorrectionMoment, correction, hr, hz]
  · intro hb
    have hm := annihilator_mean_zero_of_leeLeong_full_moment limitingResidual correction
      screened_mem_orthogonal hLL δ hδ hb
    exact B_faithful _ (screened_mean_eq_energy.symm.trans hm)

/-- The first iterate and its source have identical moment summability. -/
theorem first_resolvent_full_moment_iff (δ : ℝ) :
    fullCorrectionMoment δ (resolventApprox 1) ↔ fullCorrectionMoment δ correction := by
  have he (n : ℕ) : qSequence (resolventApprox 1) n = (4/3 : ℝ) * qSequence correction n := by
    rw [show resolventApprox 1 = (4/3 : ℝ) • correction by simp [resolventApprox, centeredFeedback]]
    change qSequenceLinear ((4/3 : ℝ) • correction) n = _
    rw [map_smul]
    rfl
  let a (n : ℕ) := positiveQWeight n * ((n : ℝ) *
    Real.exp (-(leeLeongFullDisplacementExponent δ n))) * |qSequence correction n|
  change Summable _ ↔ Summable a
  constructor
  · intro hs
    refine (hs.mul_left (3/4 : ℝ)).congr ?_
    intro n
    dsimp [a]
    rw [he, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4/3)]
    ring
  · intro hs
    refine (hs.mul_left (4/3 : ℝ)).congr ?_
    intro n
    dsimp [a]
    rw [he, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4/3)]
    ring

/-- The forward RH test at one resolvent step uses the Lee–Leong estimate. -/
theorem riemannHypothesis_of_first_resolvent_full_moment (hLL : LeeLeongMertensEstimate)
    (δ : ℝ) (hδ : 0 < δ) (h : fullCorrectionMoment δ (resolventApprox 1)) :
    RiemannHypothesis :=
  rh_of_zero_projection_residual ((residual_zero_iff_full_correction_moment hLL δ hδ).mpr
    ((first_resolvent_full_moment_iff δ).mp h))

/-- Báez-Duarte's RH-conditional approximation gives the converse. -/
theorem riemannHypothesis_iff_first_resolvent_full_moment (hLL : LeeLeongMertensEstimate)
    (hBD : Pareto.BaezDuarte.BaezDuarteMobiusApproximation) (δ : ℝ) (hδ : 0 < δ) :
    RiemannHypothesis ↔ fullCorrectionMoment δ (resolventApprox 1) :=
  ⟨fun h => (first_resolvent_full_moment_iff δ).mpr
    ((residual_zero_iff_full_correction_moment hLL δ hδ).mp
      (residual_zero_of_baezDuarte_and_riemannHypothesis hBD h)),
    riemannHypothesis_of_first_resolvent_full_moment hLL δ hδ⟩

/-- Finite moving projection stages and finite physical heads characterize the full moment.
For each head the good conductor stages may be chosen independently. -/
theorem residual_zero_iff_cofinal_full_moving_moment (hLL : LeeLeongMertensEstimate)
    (δ : ℝ) (hδ : 0 < δ) :
    limitingResidual = 0 ↔ ∃ C : ℝ, ∀ K : ℕ, ∃ᶠ N : ℕ in Filter.atTop,
      QSquarefreeFiniteMoment.momentHead (fun n => positiveQWeight n * ((n : ℝ) *
        Real.exp (-(leeLeongFullDisplacementExponent δ n)))) (movingCorrection N) K ≤ C :=
  (residual_zero_iff_full_correction_moment hLL δ hδ).trans
    (QSquarefreeFiniteMoment.correction_moment_iff_cofinal_moving_heads _
      (fun n => mul_nonneg (positiveQWeight_nonneg n)
        (mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le)))

end RiemannResearch.RH.QMertensFirstMoment
