/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QDisplacementTailTests
import RiemannResearch.RH.QUniformTail
import RiemannResearch.RH.QSievePrimeJump

/-! # Localizing the finite change-of-measure forcing for eighth moments

Source: the user's finite-head displacement question. Truncation takes place
before applying the full stage projection. The retained input is the actual
finite Pareto residual. -/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QShiftedReciprocal QAnnihilatorTailEscape QFiniteSupportDualCriterion
open QSquarefreeDisplacementRegularity ArithmeticCumulative

/-- The finite-stage projection of the truncated Pareto forcing. -/
def projectedFiniteForcing (N T : ℕ) : QHilbert :=
  (stage N).starProjection (B (finiteHead T (qOne - finitePFit N)))

/-- The omitted forcing stays signed and is projected by the full Gram system. -/
theorem projectedFiniteForcing_remainder (N T : ℕ) :
    finiteDisplacement N - projectedFiniteForcing N T =
      (stage N).starProjection (B (tail T (qOne - finitePFit N))) := by
  have he : (stage N).starProjection (B (qOne - finitePFit N)) = finiteDisplacement N := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (finiteDisplacement_mem N)
    intro v hv
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hv (finite_witness_mem_orthogonal N)
  rw [projectedFiniteForcing, tail, map_sub, map_sub, he]

theorem projectedFiniteForcing_scaled_error (N T : ℕ) :
    ((T : ℝ) + 2) * ‖finiteDisplacement N - projectedFiniteForcing N T‖ ≤
      ‖tail T (qOne - finitePFit N)‖ := by
  have hz (n : ℕ) (hn : n ≤ T) : qSequence (tail T (qOne - finitePFit N)) n = 0 := by
    cases n with
    | zero => exact qSequence_zero _
    | succ k =>
      change ((qOne - finitePFit N) k - finiteHead T (qOne - finitePFit N) k) /
        Real.sqrt (qWeight k) = 0
      rw [finiteHead_apply_of_lt _ _ _ (by omega), sub_self, zero_div]
  rw [projectedFiniteForcing_remainder]
  have hp (f : QHilbert) : ‖(stage N).starProjection f‖ ≤ ‖f‖ :=
    ((stage N).starProjection.le_opNorm f).trans (by
      simpa using mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le (stage N))
        (norm_nonneg f))
  exact (mul_le_mul_of_nonneg_left (hp _) (by positivity)).trans
    (scaled_B_norm_le_of_head _ _ hz)

/-- A finite physical eighth moment controlled by the Hilbert norm and the output cutoff. -/
theorem weighted_eighth_head_le_norm (v : QHilbert) (H : ℕ) :
    (∑ n ∈ Finset.Icc 1 H, positiveQWeight n * (qSequence v n) ^ 8) ≤
      (Real.sqrt zetaTwo * (H : ℝ) * ‖v‖) ^ 6 * ‖v‖ ^ 2 := by
  let A := Real.sqrt zetaTwo * (H : ℝ) * ‖v‖
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 H, A ^ 6 * (positiveQWeight n * (qSequence v n) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      have hmax : |qSequence v n| ≤ A := by
        apply (QPrimePowerSieve.qSequence_abs_le v n).trans
        dsimp [A]
        gcongr
        exact_mod_cast (Finset.mem_Icc.mp hn).2
      have h6 : (qSequence v n) ^ 6 ≤ A ^ 6 := by
        calc
          _ = |qSequence v n|^6 := by rw [Even.pow_abs (by decide : Even 6)]
          _ ≤ _ := by gcongr
      calc
        _ = (qSequence v n) ^ 6 * (positiveQWeight n * (qSequence v n) ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h6
          (mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (QPrimePowerSieve.finite_head_le_norm_sq v H) (by positivity)

/-- Any input cutoff satisfying H ^ 6 ≤ (T+2) ^ 8 controls the output head H. -/
theorem projectedFiniteForcing_eighth_error (N T H : ℕ)
    (hHT : (H : ℝ) ^ 6 ≤ ((T : ℝ) + 2) ^ 8) :
    (∑ n ∈ Finset.Icc 1 H, positiveQWeight n *
      (qSequence (finiteDisplacement N - projectedFiniteForcing N T) n) ^ 8) ≤
      (Real.sqrt zetaTwo) ^ 6 * ‖tail T (qOne - finitePFit N)‖ ^ 8 := by
  let v := finiteDisplacement N - projectedFiniteForcing N T
  have hscaled : ((T : ℝ) + 2) * ‖v‖ ≤ ‖tail T (qOne - finitePFit N)‖ :=
    projectedFiniteForcing_scaled_error N T
  calc
    _ ≤ (Real.sqrt zetaTwo * (H : ℝ) * ‖v‖) ^ 6 * ‖v‖ ^ 2 := weighted_eighth_head_le_norm v H
    _ = (Real.sqrt zetaTwo) ^ 6 * ((H : ℝ) ^ 6 * ‖v‖ ^ 8) := by ring
    _ ≤ (Real.sqrt zetaTwo) ^ 6 * ((((T : ℝ) + 2) * ‖v‖) ^ 8) := by
      rw [mul_pow]
      gcongr
    _ ≤ _ := by gcongr

/-- The moving Pareto residuals are uniformly tight along every cofinal input cutoff. -/
theorem finiteParetoResidual_tail_tendsto (T : ℕ → ℕ) (hT : Tendsto T atTop atTop) :
    Tendsto (fun N => ‖tail (T N) (qOne - finitePFit N)‖) atTop (𝓝 0) := by
  have hc : Tendsto (fun N => qOne - finitePFit N) atTop
      (𝓝 (qOne - QParetoClosedProjectionComparison.pFit
        QSquarefreeMeasureRigidity.paretoSquarefreeClosure qOne)) :=
    tendsto_const_nhds.sub finitePFit_tendsto
  have ht : Tendsto (fun N => ‖tail (T N) (qOne - finitePFit N)‖) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun _ => ha.trans_le (norm_nonneg _))
    · intro a ha
      obtain ⟨K, hK⟩ := uniform_tail_tightness_of_tendsto _ _ hc a ha
      filter_upwards [hT.eventually (eventually_ge_atTop K)] with N hN
      exact hK (T N) hN N
  exact ht

/-- Arbitrarily slowly growing input cutoffs recover the actual limiting displacement
in the Hilbert norm. No relation between the stage and the input cutoff is needed. -/
theorem projectedFiniteForcing_tendsto (T : ℕ → ℕ) (hT : Tendsto T atTop atTop) :
    Tendsto (fun N => projectedFiniteForcing N (T N)) atTop
      (𝓝 QSquarefreeDisplacementRigidity.displacement) := by
  have hd : Tendsto (fun N => finiteDisplacement N - projectedFiniteForcing N (T N))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun N => norm_nonneg _)
      (fun N => ?_) (finiteParetoResidual_tail_tendsto T hT)
    have hscale : (1 : ℝ) ≤ (T N : ℝ) + 2 := by linarith [Nat.cast_nonneg (T N) (α := ℝ)]
    exact (le_mul_of_one_le_left (norm_nonneg _) hscale).trans
      (projectedFiniteForcing_scaled_error N (T N))
  simpa only [sub_sub_cancel, sub_zero] using finiteDisplacement_tendsto.sub hd

/-- Along any cofinal input cutoff satisfying the displayed power comparison,
the aligned head eighth moment of the truncation error tends to zero. -/
theorem projectedFiniteForcing_eighth_error_tendsto (T : ℕ → ℕ)
    (hT : Tendsto T atTop atTop) (hHT : ∀ N : ℕ, (N : ℝ) ^ 6 ≤ ((T N : ℝ) + 2) ^ 8) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, positiveQWeight n *
      (qSequence (finiteDisplacement N - projectedFiniteForcing N (T N)) n) ^ 8)
      atTop (𝓝 0) := by
  have ht := finiteParetoResidual_tail_tendsto T hT
  apply squeeze_zero (fun N => Finset.sum_nonneg
    (fun i _ => mul_nonneg (positiveQWeight_nonneg i) (by positivity)))
    (fun N => projectedFiniteForcing_eighth_error N (T N) N (hHT N))
  simpa only [zero_pow (by decide : 8 ≠ 0), mul_zero] using
    (ht.pow 8).const_mul ((Real.sqrt zetaTwo) ^ 6)

/-- Every retained high-conductor Gram right-hand side is one scalar divided by m. -/
theorem high_conductor_truncated_forcing (T m : ℕ) (hm : T < m) (f : QHilbert) :
    (∑ k ∈ Finset.Icc 1 T, positiveQWeight k * qSequence (qResidue m) k * qSequence (B f) k) =
      (∑ k ∈ Finset.Icc 1 T, ArithmeticCumulative.weight k * qSequence f k) /
        (zetaTwo * (m : ℝ)) := by
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hkpos, hkT⟩ := Finset.mem_Icc.mp hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  rw [qSequence_qResidue, qSequence_B]
  simp only [residueFraction, Nat.mod_eq_of_lt (lt_of_le_of_lt hkT hm), positiveQWeight,
    ArithmeticCumulative.weight]
  field_simp [hk0.ne', hm0.ne', hkp.ne', zetaTwo_pos.ne']

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
