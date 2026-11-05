/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensDelayedSharpEndpoint
import RiemannResearch.RH.MertensDelayedComparison
import RiemannResearch.RH.MertensRawFullArithmetic
import RiemannResearch.RH.MertensDelayedEnvelope
import RiemannResearch.RH.QFirstResolventFullMoment

/-!
# The full Lee–Leong moment with a translated argument

Theorem 1.1(12) in the HTML edition of Lee and Leong
(https://arxiv.org/html/2208.06141v5) bounds the ordinary Mertens function.
This module transfers its complete logarithmic prefactor to the physical envelope.
-/
noncomputable section
open Filter
namespace RiemannResearch.RH.QMertensFirstMoment
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage QSquarefreeSmoothedProjection
open QSquarefreeDisplacementRigidity QSquarefreeDisplacementResolvent QShiftedReciprocal

/-- Absolute physical moment at the translated full exponent. -/
def delayedMoment (z : QHilbert) : Prop :=
  Summable (fun n : ℕ => positiveQWeight n * ((n:ℝ) * leeLeongDelayedDamping n) *
    |qSequence z n|)

/-- The same cutoff pairing applies to both projection witnesses. -/
theorem annihilator_mean_zero_of_delayed_moment (v z : QHilbert)
    (ho : B v - z ∈ closureᗮ) (hLL : LeeLeongMertensEstimate) (hz : delayedMoment z) :
    inner ℝ qOne (B v - z) = 0 := by
  apply annihilator_mean_zero_of_exponential_cutoff_moment v z ho leeLeongRawLogError
    (fun n => (n:ℝ) * leeLeongDelayedDamping n)
    leeLeongRawLogError_tendsto_atBot leeLeongRawLogError_eventually_antitone
    (mertens_rawLogError_of_leeLeong hLL) _ summable_leeLeongDelayedDamping_Q hz
  refine ⟨400, by norm_num, ?_⟩
  filter_upwards [exp_leeLeongRawLogError_eventually_nat,
    errorEnvelope_eventually_le_leeLeongDelayed] with N hE hN n
  rw [hE]
  exact hN n

/-- The translated moment of the first correction forces the Hilbert residual to vanish. -/
theorem residual_zero_iff_delayed_correction_moment (hLL : LeeLeongMertensEstimate) :
    limitingResidual = 0 ↔ delayedMoment correction := by
  constructor
  · intro hr
    have hz (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by cases n <;> simp [qSequence]
    simp [delayedMoment, correction, hr, hz]
  · intro h
    have hm := annihilator_mean_zero_of_delayed_moment limitingResidual correction
      screened_mem_orthogonal hLL h
    exact B_faithful _ (screened_mean_eq_energy.symm.trans hm)

/-- One explicit first-correction moment with a loss on the scale Φ²/log x
and the two printed logarithms suffices for the forward implication. -/
theorem riemannHypothesis_of_explicit_delayed_correction (hLL : LeeLeongMertensEstimate)
    (hs : Summable (fun n : ℕ => positiveQWeight n * ((n:ℝ) *
      Real.exp (-leeLeongFullProfile n + (2 * leeLeongRate)^2 *
        (RiemannResearch.Analysis.vkProfile n ^ 2 / Real.log n) +
        2 * Real.log (Real.log n))) * |qSequence correction n|)) : RiemannHypothesis := by
  apply rh_of_zero_projection_residual
  apply (residual_zero_iff_delayed_correction_moment hLL).mpr
  apply hs.of_norm_bounded_eventually_nat
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually leeLeongDelayedDamping_eventually_le_explicit] with n h
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (positiveQWeight_nonneg n)
    (mul_nonneg (Nat.cast_nonneg n) (leeLeongDelayedDamping_nonneg n))) (abs_nonneg _))]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)) (positiveQWeight_nonneg n)) (abs_nonneg _)

/-- The analogous translated moment on the displacement is also sufficient. -/
theorem riemannHypothesis_of_delayed_displacement_moment (hLL : LeeLeongMertensEstimate)
    (hd : delayedMoment displacement) : RiemannHypothesis :=
  rh_of_zero_projection_residual (residual_eq_zero_of_witness_mean_zero
    (annihilator_mean_zero_of_delayed_moment pResidual displacement witness_mem_orthogonal hLL hd))

/-- A finite-stage test for the translated absolute moment of the first correction. -/
theorem residual_zero_iff_cofinal_delayed_heads (hLL : LeeLeongMertensEstimate) :
    limitingResidual = 0 ↔ ∃ C : ℝ, ∀ K : ℕ, ∃ᶠ N : ℕ in atTop,
      QSquarefreeFiniteMoment.momentHead (fun n => positiveQWeight n *
        ((n:ℝ) * leeLeongDelayedDamping n)) (movingCorrection N) K ≤ C :=
  (residual_zero_iff_delayed_correction_moment hLL).trans
    (QSquarefreeFiniteMoment.correction_moment_iff_cofinal_moving_heads _
      (fun n => mul_nonneg (positiveQWeight_nonneg n) (mul_nonneg (Nat.cast_nonneg n)
        (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))))

/-- The forward direction takes Lee–Leong; the converse takes Báez-Duarte. -/
theorem riemannHypothesis_iff_delayed_correction_moment (hLL : LeeLeongMertensEstimate)
    (hBD : Pareto.BaezDuarte.BaezDuarteMobiusApproximation) :
    RiemannHypothesis ↔ delayedMoment correction :=
  ⟨fun h => (residual_zero_iff_delayed_correction_moment hLL).mp
      (residual_zero_of_baezDuarte_and_riemannHypothesis hBD h),
   fun h => rh_of_zero_projection_residual ((residual_zero_iff_delayed_correction_moment hLL).mpr h)⟩

/-- The explicit unshifted moment with the leading window cost 3F²/(5 log n)
dominates the delayed moment, for every physical vector. -/
theorem delayedMoment_of_sharp_endpoint (z : QHilbert)
    (hs : Summable (fun n : ℕ => positiveQWeight n * ((n:ℝ) *
      Real.exp (-leeLeongFullProfile n + (3/5:ℝ)*leeLeongFullProfile n^2/Real.log n)) *
        |qSequence z n|)) : delayedMoment z := by
  apply hs.of_norm_bounded_eventually_nat
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually leeLeongDelayedDamping_eventually_sharp_endpoint] with n h
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (positiveQWeight_nonneg n)
    (mul_nonneg (Nat.cast_nonneg n) (leeLeongDelayedDamping_nonneg n))) (abs_nonneg _))]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n)) (positiveQWeight_nonneg n)) (abs_nonneg _)

/-- The physically weighted full Lee–Leong endpoint suffices for RH on the first correction. -/
theorem riemannHypothesis_of_sharp_endpoint_correction (hLL : LeeLeongMertensEstimate)
    (hs : Summable (fun n : ℕ => positiveQWeight n * ((n:ℝ) *
      Real.exp (-leeLeongFullProfile n + (3/5:ℝ)*leeLeongFullProfile n^2/Real.log n)) *
        |qSequence correction n|)) : RiemannHypothesis :=
  rh_of_zero_projection_residual ((residual_zero_iff_delayed_correction_moment hLL).mpr
    (delayedMoment_of_sharp_endpoint correction hs))

/-- At the precise coefficient 3/5 no extra logarithmic saving in |z(n)| is
needed: the iterated logarithm in the printed profile pays the summability cost. -/
theorem delayedMoment_of_sharp_endpoint_growth (z : QHilbert) (D : ℝ)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence z n| ≤ D *
      Real.exp (leeLeongFullProfile n - (3/5:ℝ)*leeLeongFullProfile n^2/Real.log n)) :
    delayedMoment z := by
  let V (n : ℕ) := leeLeongFullProfile n - (3/5:ℝ)*leeLeongFullProfile n^2/Real.log n
  let U (n : ℕ) := V n + 2*Real.log (Real.log (n:ℝ))
  have hgap : ∀ᶠ n : ℕ in atTop, 2*Real.log (Real.log (n:ℝ)) ≤ U n - V n :=
    Eventually.of_forall (fun n => by dsimp only [U]; linarith)
  have hs := summable_harmonic_moment_of_exponent_gap (qSequence z) U V D hd hgap
  apply hs.of_norm_bounded_eventually_nat
  have hn : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually leeLeongDelayedDamping_eventually_sharp_log_reserve] with n hn'
  have hm : leeLeongDelayedDamping n ≤ Real.exp (-(U n)) := by
    apply hn'.trans_eq
    congr 1
    dsimp only [U, V]
    ring
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (positiveQWeight_nonneg n)
    (mul_nonneg (Nat.cast_nonneg n) (leeLeongDelayedDamping_nonneg n))) (abs_nonneg _))]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg n)) (positiveQWeight_nonneg n)) (abs_nonneg _)

theorem riemannHypothesis_of_sharp_endpoint_correction_growth (hLL : LeeLeongMertensEstimate)
    (D : ℝ) (hd : ∀ᶠ n : ℕ in atTop, |qSequence correction n| ≤ D *
      Real.exp (leeLeongFullProfile n - (3/5:ℝ)*leeLeongFullProfile n^2/Real.log n)) :
    RiemannHypothesis :=
  rh_of_zero_projection_residual ((residual_zero_iff_delayed_correction_moment hLL).mpr
    (delayedMoment_of_sharp_endpoint_growth correction D hd))

end RiemannResearch.RH.QMertensFirstMoment
