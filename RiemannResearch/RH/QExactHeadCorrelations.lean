/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeSublinearHeads
import RiemannResearch.RH.QTailGram
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.CanonicalMobiusFullEnergy
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Complete Q correlations of exact-head residuals

Source: the user's sparse power-cost continuation, 17 October 2026.
The tail bound uses the actual Q/P weight comparison and the complete
telescoping Pareto tail mass. Canonical Mobius sublinear energy supplies
fixed-row decay. The signed-mixture identity keeps every full-Q cross term.

These unconditional entrywise limits do not provide a uniform estimate
for growing Gram matrices or a sparse cost exponent below one.
The missing estimate is recorded in QSparsePowerCostResearch20261017.md.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QExactHeadCorrelations
open ZetaTwoHilbert ZetaTwoProbability QTailGram Pareto

theorem tail_norm_sq_bounded (f : QHilbert) (H : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, 0 < k → |qSequence f k| ≤ C) :
    zetaTwo * ‖tailMap H f‖ ^ 2 ≤ 2 * C ^ 2 / ((H : ℝ) + 1) := by
  have hs : Summable (fun n : ℕ =>
      positiveQWeight (n + H + 1) * qSequence f (n + H + 1) ^ 2) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (H + 1)).mpr (qSequence_square_summable f)
  have hw : Summable (fun n : ℕ => positiveWeight (n + H + 1)) := by
    simpa only [Nat.add_assoc] using
      (summable_nat_add_iff (H + 1)).mpr positiveWeight_summable
  calc
    _ = ∑' n : ℕ, zetaTwo *
        (positiveQWeight (n + H + 1) * qSequence f (n + H + 1) ^ 2) := by
      rw [qNorm_sq, ← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [show n + H + 1 = (n + H) + 1 by omega, qSequence_weighted_square]
      rfl
    _ ≤ ∑' n : ℕ, positiveWeight (n + H + 1) * (2 * C ^ 2) := by
      apply Summable.tsum_le_tsum _ (hs.mul_left zetaTwo) (hw.mul_right _)
      intro n
      have hsq : qSequence f (n + H + 1) ^ 2 ≤ C ^ 2 := by
        simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hC).mpr (hf (n + H + 1) (by omega))
      calc
        _ = (zetaTwo * positiveQWeight (n + H + 1)) *
            qSequence f (n + H + 1) ^ 2 := by ring
        _ ≤ (2 * positiveWeight (n + H + 1)) * C ^ 2 :=
          mul_le_mul (ZetaTwoParetoTransfer.zetaTwo_mul_QWeight_le_two_mul_paretoWeight _)
            hsq (sq_nonneg _) (mul_nonneg (by norm_num) (positiveWeight_nonneg _))
        _ = _ := by ring
    _ = _ := by
      rw [tsum_mul_right]
      have ht : (∑' n : ℕ, positiveWeight (n + H + 1)) =
          1 / ((H + 1 : ℕ) : ℝ) := by
        simpa only [Nat.add_assoc] using positiveWeight_tail_tsum (H + 1) (by omega)
      rw [ht]
      push_cast
      ring

theorem inner_sq_le_sublinear_energy (f u : QHilbert) (N : ℕ) (hN : 1 ≤ N)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, 0 < k → |qSequence f k| ≤ C)
    (hu : ∀ k, 0 < k → k ≤ N → qSequence u k = 0) :
    (inner ℝ f u) ^ 2 ≤
      (2 * C ^ 2 / zetaTwo) * (‖u‖ ^ 2 / (N : ℝ)) := by
  have hraw : ∀ k < N, u k = 0 := by
    intro k hk
    have he := hu (k + 1) (by omega) (by omega)
    change u k / Real.sqrt (qWeight k) = 0 at he
    exact (div_eq_zero_iff.mp he).resolve_right
      (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos k)))
  have hc := hilbertTailShift_inner_sq_le f u N hraw
  change (inner ℝ f u) ^ 2 ≤ ‖tailMap N f‖ ^ 2 * ‖u‖ ^ 2 at hc
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have ht : ‖tailMap N f‖ ^ 2 ≤ (2 * C ^ 2 / zetaTwo) / (N : ℝ) := by
    calc
      _ ≤ (2 * C ^ 2 / ((N : ℝ) + 1)) / zetaTwo :=
        (le_div_iff₀ zetaTwo_pos).mpr (by
          simpa only [mul_comm] using tail_norm_sq_bounded f N C hC hf)
      _ ≤ (2 * C ^ 2 / (N : ℝ)) / zetaTwo :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity) hNp (by linarith)) zetaTwo_pos.le
      _ = _ := by ring
  calc
    _ ≤ ‖tailMap N f‖ ^ 2 * ‖u‖ ^ 2 := hc
    _ ≤ ((2 * C ^ 2 / zetaTwo) / (N : ℝ)) * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right ht (sq_nonneg _)
    _ = _ := by ring

theorem inner_tendsto_zero_of_sublinear_head_zero
    (u : ℕ → QHilbert)
    (hu : ∀ N k, 0 < k → k ≤ N → qSequence (u N) k = 0)
    (hsub : Tendsto (fun N => ‖u N‖ ^ 2 / (N : ℝ)) atTop (𝓝 0))
    (f : QHilbert) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, 0 < k → |qSequence f k| ≤ C) :
    Tendsto (fun N => inner ℝ f (u N)) atTop (𝓝 0) := by
  have hs : Tendsto (fun N => (inner ℝ f (u N)) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun N => sq_nonneg _)) ?_
      (by simpa only [mul_zero] using hsub.const_mul (2 * C ^ 2 / zetaTwo))
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact inner_sq_le_sublinear_energy f (u N) N hN C hC hf (hu N)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, sub_zero, Real.norm_eq_abs,
    Real.sqrt_sq_eq_abs, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hs

def residual (N : ℕ) : QHilbert := qOne - QMobiusExactHead.exactHead N

theorem residual_sequence (N k : ℕ) :
    qSequence (residual N) k = qOneSequence k - canonicalMobiusHead N k := by
  change qSequenceLinear (qOne - QMobiusExactHead.exactHead N) k = _
  rw [map_sub]
  change qSequence qOne k - qSequence (QMobiusExactHead.exactHead N) k = _
  rw [qSequence_qOne, QMobiusExactHead.exactHead_sequence]

theorem residual_head_zero (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    qSequence (residual N) k = 0 := by
  rw [residual_sequence, canonicalMobiusHead_exact N k hk hkN]
  simp [qOneSequence, Nat.ne_of_gt hk]

theorem residual_bounded (M : ℕ) (hM : 0 < M) (k : ℕ) (hk : 0 < k) :
    |qSequence (residual M) k| ≤ 1 + 2 * (M : ℝ) := by
  rw [residual_sequence]
  have hone : qOneSequence k = 1 := by simp [qOneSequence, Nat.ne_of_gt hk]
  rw [hone]
  calc
    _ ≤ |(1 : ℝ)| + |-(canonicalMobiusHead M k)| := by
      simpa only [Real.norm_eq_abs, abs_neg] using norm_sub_le (1 : ℝ) (canonicalMobiusHead M k)
    _ ≤ _ := by
      simp only [abs_one, abs_neg]
      linarith [canonicalMobiusHead_abs_le_two_mul M hM k]

theorem residual_fixed_row_tendsto_zero (M : ℕ) (hM : 0 < M) :
    Tendsto (fun N => inner ℝ (residual M) (residual N)) atTop (𝓝 0) := by
  apply inner_tendsto_zero_of_sublinear_head_zero residual residual_head_zero
    QSquarefreeSublinearHeads.exactHead_error_sublinear (residual M)
      (1 + 2 * (M : ℝ)) (by positivity)
  exact residual_bounded M hM




/-- Complete arithmetic Gram entry before applying a tail estimate. -/
theorem residual_pairing_weighted (M N : ℕ) :
    inner ℝ (residual M) (residual N) =
      ∑' k, positiveQWeight k *
        (qOneSequence k - canonicalMobiusHead M k) *
        (qOneSequence k - canonicalMobiusHead N k) := by
  rw [qInner_weighted]
  simp only [residual_sequence]

theorem residual_mixed_sq_le (M N : ℕ) (hM : 0 < M) (hN : 1 ≤ N) :
    (inner ℝ (residual M) (residual N)) ^ 2 ≤
      (2 * (1 + 2 * (M : ℝ)) ^ 2 / zetaTwo) *
        (‖residual N‖ ^ 2 / (N : ℝ)) :=
  inner_sq_le_sublinear_energy (residual M) (residual N) N hN
    (1 + 2 * (M : ℝ)) (by positivity) (residual_bounded M hM)
      (residual_head_zero N)

def signedHeadAverage (s : Finset ℕ) (b : ℕ → ℝ) : QHilbert :=
  ∑ i ∈ s, b i • QMobiusExactHead.exactHead i

theorem signedHeadAverage_mem (s : Finset ℕ) (b : ℕ → ℝ)
    (hsf : ∀ i ∈ s, Squarefree (i + 1)) :
    signedHeadAverage s b ∈ qSquarefreeCRTSpan := by
  unfold signedHeadAverage
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _
    (QSquarefreeSublinearHeads.exactHead_mem_squarefreeSpan i (hsf i hi))

theorem signedHeadAverage_head (s : Finset ℕ) (b : ℕ → ℝ) (H : ℕ)
    (hb : ∑ i ∈ s, b i = 1) (hH : ∀ i ∈ s, H ≤ i)
    (k : ℕ) (hk : 0 < k) (hkH : k ≤ H) :
    qSequence (signedHeadAverage s b) k = 1 := by
  change qSequenceLinear (∑ i ∈ s, b i • QMobiusExactHead.exactHead i) k = 1
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i ∈ s, b i * qSequence (QMobiusExactHead.exactHead i) k) = 1
  calc
    _ = ∑ i ∈ s, b i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [QMobiusExactHead.exactHead_exact i k hk (hkH.trans (hH i hi)), mul_one]
    _ = 1 := hb

theorem signedHeadAverage_error_exact (s : Finset ℕ) (b : ℕ → ℝ)
    (hb : ∑ i ∈ s, b i = 1) :
    ‖qOne - signedHeadAverage s b‖ ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, b i * b j * inner ℝ (residual i) (residual j) := by
  have he : qOne - signedHeadAverage s b = ∑ i ∈ s, b i • residual i := by
    symm
    simp only [residual, smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hb, one_smul]
    rfl
  rw [he, ← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp only [mul_assoc]

end RiemannResearch.RH.QExactHeadCorrelations
