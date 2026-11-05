/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensImplicitTruncation
import RiemannResearch.RH.QFirstResolventFullMoment

/-!
# The implicit Lee–Leong moment of the first projected correction

At `s = 0` the physical weight is the printed full exponent. Positive `s`
permits the additional damping `exp (-s * sqrt Φ)`. The arithmetic input is
Lee and Leong, Proposition 5.2, equations (60) and (62), specialized in §5.4.
-/
noncomputable section
open Filter
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QSquarefreeSmoothedProjection QShiftedReciprocal

/-- The first-moment coefficient at signed reserve `s`, including the Q weight. -/
def implicitMomentWeight (s : ℝ) (n : ℕ) : ℝ :=
  positiveQWeight n * ((n : ℝ) * Real.exp (-(leeLeongFullProfile n + s * Real.sqrt (vkProfile n))))

private theorem implicitMomentWeight_nonneg (s : ℝ) (n : ℕ) : 0 ≤ implicitMomentWeight s n :=
  mul_nonneg (positiveQWeight_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)

private theorem implicitMomentWeight_antitone (n : ℕ) : Antitone (fun s => implicitMomentWeight s n) := by
  intro s a hsa
  unfold implicitMomentWeight
  apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg n)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  apply Real.exp_le_exp.mpr
  linarith only [mul_le_mul_of_nonneg_right hsa (Real.sqrt_nonneg (vkProfile n))]

/-- Vanishing of the actual Q residual is equivalent to a single absolute
moment of the first correction at any fixed additional reserve `s`. -/
theorem residual_zero_iff_implicit_correction_moment (h : LeeLeongImplicitTruncation) (s : ℝ) :
    limitingResidual = 0 ↔ Summable (fun n => implicitMomentWeight s n * |qSequence correction n|) := by
  constructor
  · intro hr
    have hz (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by cases n <;> simp [qSequence]
    simp [correction, hr, hz]
  · intro hs
    have hm : inner ℝ qOne screened = 0 := by
      apply annihilator_mean_zero_of_truncationReserve_moment limitingResidual correction
        screened_mem_orthogonal (truncationReserve_of_implicitTruncation h) (max s 0) (le_max_right _ _)
      change Summable (fun n => implicitMomentWeight (max s 0) n * |qSequence correction n|)
      exact Summable.of_nonneg_of_le
        (fun n => mul_nonneg (implicitMomentWeight_nonneg _ _) (abs_nonneg _))
        (fun n => mul_le_mul_of_nonneg_right (implicitMomentWeight_antitone n (le_max_left s 0))
          (abs_nonneg _)) hs
    exact B_faithful _ (screened_mean_eq_energy.symm.trans hm)

/-- At the exact printed exponent the square-root margin vanishes. -/
theorem residual_zero_iff_printed_correction_moment (h : LeeLeongImplicitTruncation) :
    limitingResidual = 0 ↔ Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-(leeLeongFullProfile n))) * |qSequence correction n|) := by
  simpa only [implicitMomentWeight, zero_mul, add_zero] using
    residual_zero_iff_implicit_correction_moment h 0

/-- Finite physical heads at cofinal conductor stages characterize the same moment. -/
theorem residual_zero_iff_cofinal_implicit_correction_heads (h : LeeLeongImplicitTruncation) (s : ℝ) :
    limitingResidual = 0 ↔ ∃ C : ℝ, ∀ K, ∃ᶠ N in atTop,
      QSquarefreeFiniteMoment.momentHead (implicitMomentWeight s) (movingCorrection N) K ≤ C :=
  (residual_zero_iff_implicit_correction_moment h s).trans
    (QSquarefreeFiniteMoment.correction_moment_iff_cofinal_moving_heads _ (implicitMomentWeight_nonneg s))

/-- One finite moment suffices for RH at each fixed signed reserve. -/
theorem riemannHypothesis_of_implicit_correction_moment (h : LeeLeongImplicitTruncation) (s : ℝ)
    (hm : Summable (fun n => implicitMomentWeight s n * |qSequence correction n|)) : RiemannHypothesis :=
  rh_of_zero_projection_residual ((residual_zero_iff_implicit_correction_moment h s).mpr hm)

/-- The implicit Lee–Leong input gives the moment-to-RH direction. The reverse
direction uses the separate RH-conditional Báez-Duarte approximation input. -/
theorem riemannHypothesis_iff_implicit_correction_moment (h : LeeLeongImplicitTruncation)
    (hBD : Pareto.BaezDuarte.BaezDuarteMobiusApproximation) (s : ℝ) :
    RiemannHypothesis ↔ Summable (fun n => implicitMomentWeight s n * |qSequence correction n|) :=
  ⟨fun hr => (residual_zero_iff_implicit_correction_moment h s).mp
      (residual_zero_of_baezDuarte_and_riemannHypothesis hBD hr),
   riemannHypothesis_of_implicit_correction_moment h s⟩

/-- A pointwise estimate on the first correction at any fixed signed reserve
implies RH using the implicit truncation alone. -/
theorem riemannHypothesis_of_implicit_correction_pointwise (h : LeeLeongImplicitTruncation)
    (s D : ℝ) (hb : ∀ᶠ n : ℕ in atTop, |qSequence correction n| ≤ D *
      Real.exp (leeLeongFullProfile n + s * Real.sqrt (vkProfile n))) : RiemannHypothesis := by
  apply rh_of_zero_projection_residual
  apply (residual_zero_iff_implicit_correction_moment h (s+1)).mpr
  unfold implicitMomentWeight
  refine summable_harmonic_moment_of_exponent_gap _ _ _ D hb ?_
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually (vkProfile_dominates_logLog_sq ((1/2 : ℝ)^2) (by norm_num)),
    hn.eventually (vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ)))] with n hx hv
  have hl : Real.log (Real.log (n : ℝ)) ≤ (1/2 : ℝ) * Real.sqrt (vkProfile n) := by
    apply le_of_sq_le_sq _ (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hv] using hx
  linarith only [hl]

end RiemannResearch.RH.QMertensFirstMoment
