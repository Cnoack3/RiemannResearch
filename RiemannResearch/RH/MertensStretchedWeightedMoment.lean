/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.StretchedLogProductIncrement
import RiemannResearch.RH.QSquarefreeStretchedDisplacement
import RiemannResearch.RH.QPhysicalTailEnergy

/-!
# A weighted second moment at the unconditional Mertens scale

The weighted-tail comparison follows the proof of
`QPolylogTailEnergy.profile_mul_tail_energy_le` for an arbitrary nonnegative
weight that is eventually increasing. The analytic exponent in the application
comes from the existing Mertens displacement-tail theorem.
-/
noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QAnnihilatorTailEscape
open QFiniteSupportDualCriterion ZetaTwoProbability ZetaTwoHilbert

/-- Bound the complete weighted tail by the full weighted second moment. -/
theorem tail_energy_le_weighted_second_moment (u : QHilbert) (w : ℕ → ℝ)
    (hw : ∀ n, 0 ≤ w n) (N : ℕ) (hm : ∀ n, N < n → w N ≤ w n)
    (hs : Summable fun n => w n * (positiveQWeight n * qSequence u n ^ 2)) :
    w N * ‖tail N u‖ ^ 2 ≤ ∑' n, w n * (positiveQWeight n * qSequence u n ^ 2) := by
  let e (n : ℕ) := positiveQWeight n * qSequence u n ^ 2
  have he (n : ℕ) : 0 ≤ e n := mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)
  have hq : Summable (fun j : ℕ => e (j + (N+1))) :=
    (summable_nat_add_iff (f := e) (N+1)).mpr (qSequence_square_summable u)
  have ht : Summable (fun j : ℕ => w (j+(N+1)) * e (j+(N+1))) :=
    (summable_nat_add_iff (f := fun n => w n * e n) (N+1)).mpr hs
  have hb (j : ℕ) : w N * e (j+(N+1)) ≤ w (j+(N+1)) * e (j+(N+1)) :=
    mul_le_mul_of_nonneg_right (hm _ (by omega)) (he _)
  have hsum := (hq.mul_left (w N)).tsum_le_tsum hb ht
  rw [tsum_mul_left] at hsum
  have hfull := hs.sum_add_tsum_nat_add (N+1)
  have hhead : 0 ≤ ∑ n ∈ Finset.range (N+1), w n * e n :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (hw n) (he n))
  rw [tail_energy_physical]
  dsimp only [e] at hsum hhead
  simp only [Nat.add_assoc] at hsum hfull ⊢
  linarith

end RiemannResearch.RH.QAnnihilatorTailEscape

namespace RiemannResearch.RH.QSquarefreeStretchedDisplacement
open RiemannResearch.Analysis RiemannResearch.Analysis.StretchedTailWeights
open QAnnihilatorTailEscape QSquarefreeDisplacementRigidity QFiniteSupportDualCriterion
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage

/-- At a positive absolute rate given by the formal Mertens theorem, a finite
weighted second moment of the actual displacement suffices for RH. -/
theorem exists_riemannHypothesis_of_stretched_weighted_second_moment :
    ∃ a : ℝ, 0 < a ∧
      ((Summable fun n : ℕ => arithmeticWeight a n *
        (positiveQWeight n * qSequence displacement n ^ 2)) → RiemannHypothesis) := by
  obtain ⟨a, ha, hc⟩ := exists_residual_zero_iff_frequently_bounded_stretched_displacement_tail
  refine ⟨a, ha, fun hs => ?_⟩
  have hinc := (tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
      (shifted_logProductPower_eventual_log_increment (1 / 11) a
        (by norm_num) (by norm_num) ha.le)
  have hm : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, N < n →
      arithmeticWeight a N ≤ arithmeticWeight a n := by
    filter_upwards [hinc, eventually_ge_atTop (1 : ℕ)] with N hi hN n hn
    have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hnr : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    have h := hi (n:ℝ) (by exact_mod_cast hn.le)
    unfold arithmeticWeight arithmeticDecay
    apply (Real.log_le_log_iff (mul_pos hNr (Real.exp_pos _)) (mul_pos hnr (Real.exp_pos _))).mp
    rw [Real.log_mul hNr.ne' (Real.exp_pos _).ne',
      Real.log_mul hnr.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
    linarith only [h]
  have hr := hc.mpr ⟨_, (hm.mono fun N hN =>
    tail_energy_le_weighted_second_moment displacement (arithmeticWeight a)
      (arithmeticWeight_nonneg a) N hN hs).frequently⟩
  have hmem : qOne ∈ closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hmem)

end RiemannResearch.RH.QSquarefreeStretchedDisplacement
