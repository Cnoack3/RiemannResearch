import RiemannResearch.RH.QMatchedResidualTails
import RiemannResearch.RH.QMatchedOscillationKernel
import RiemannResearch.Analysis.SublinearTailCutoff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Short physical localization of matched oscillation pairings

Source: the user-provided argument of 10 November 2026.
All tail norms use the full infinite sums. The exact signed head/tail
identity precedes its estimate. No short-head Schur bound is assumed here.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QMatchedShortHead
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoMetric QMatchedOscillationKernel QSquarefreeCorrectionKernel
open QFiniteSupportDualCriterion QAnnihilatorTailEscape QMatchedResidualTails
open RiemannResearch.Analysis.ResidualizedProjectionKernel
open RiemannResearch.Analysis.SublinearTailCutoff

theorem reciprocal_coordinate_sq (f : QHilbert) (i : ℕ) :
    (reciprocalD (toPareto f) i) ^ 2 =
      zetaTwo * (f i) ^ 2 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) := by
  rw [reciprocalD_apply, div_pow, ← hilbertSequence_weighted_square,
    toPareto_sequence, ← qSequence_weighted_square,
    positiveWeight_succ, paretoWeight, positiveQWeight]
  push_cast
  field_simp [ne_of_gt zetaTwo_pos]
  <;> ring

theorem reciprocal_tail_norm_sq_le (f : QHilbert) (A : ℕ) :
    ‖tail A (reciprocalD (toPareto f))‖ ^ 2 ≤
      zetaTwo / (((A : ℝ) + 1) * ((A : ℝ) + 2)) * ‖f‖ ^ 2 := by
  have hZ := zetaTwo_pos
  have hnn : 0 ≤ zetaTwo / (((A : ℝ) + 1) * ((A : ℝ) + 2)) := by positivity
  have hnorm : ‖hilbertTailShift f A‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [← pareto_tail_norm_eq_shift]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (tail_norm_le A f)
  calc
    ‖tail A (reciprocalD (toPareto f))‖ ^ 2 =
        ∑' i, (reciprocalD (toPareto f) (i + A)) ^ 2 := by
      rw [pareto_tail_norm_eq_shift, hilbert_norm_sq]
      rfl
    _ ≤ ∑' i, (zetaTwo / (((A : ℝ) + 1) * ((A : ℝ) + 2))) *
        (f (i + A)) ^ 2 := by
      change (∑' i, (hilbertTailShift (reciprocalD (toPareto f)) A i) ^ 2) ≤
        ∑' i, (zetaTwo / (((A : ℝ) + 1) * ((A : ℝ) + 2))) *
          (hilbertTailShift f A i) ^ 2
      apply Summable.tsum_le_tsum _
        (hilbert_coordinate_square_summable (hilbertTailShift (reciprocalD (toPareto f)) A))
        ((hilbert_coordinate_square_summable (hilbertTailShift f A)).mul_left _)
      intro i
      change (reciprocalD (toPareto f) (i + A)) ^ 2 ≤
        (zetaTwo / (((A : ℝ) + 1) * ((A : ℝ) + 2))) * (f (i + A)) ^ 2
      rw [reciprocal_coordinate_sq]
      have hden : ((A : ℝ) + 1) * ((A : ℝ) + 2) ≤
          (((i + A : ℕ) : ℝ) + 1) * (((i + A : ℕ) : ℝ) + 2) := by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) i, Nat.cast_nonneg (α := ℝ) A]
      have h := div_le_div_of_nonneg_left
        (mul_nonneg hZ.le (sq_nonneg (f (i + A)))) (by positivity) hden
      simpa only [div_mul_eq_mul_div] using h
    _ = (zetaTwo / (((A : ℝ) + 1) * ((A : ℝ) + 2))) *
        ‖hilbertTailShift f A‖ ^ 2 := by
      rw [tsum_mul_left, hilbert_norm_sq]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hnn

theorem evaluation_norm_sq (n : ℕ) :
    ‖evaluation n‖ ^ 2 = zetaTwo * (n : ℝ) ^ 2 := by
  cases n with
  | zero => simp [evaluation]
  | succ i =>
      rw [evaluation, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
      rw [Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt (qWeight_pos i).le]
      simp only [qWeight, positiveQWeight]
      field_simp

theorem evaluation_inner_nonneg (n m : ℕ) :
    0 ≤ inner ℝ (evaluation n) (evaluation m) := by
  cases n with
  | zero => simp [evaluation]
  | succ i =>
    cases m with
    | zero => simp [evaluation]
    | succ j =>
      simp only [evaluation, lp.inner_single_right, RCLike.inner_apply, conj_trivial,
        lp.single_apply]
      by_cases h : j = i
      · subst j
        simp only [Pi.single_eq_same]
        positivity
      · simp [Pi.single_eq_of_ne h]

theorem pairKernel_norm_sq_le (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (H n m : ℕ) (hn : n ≤ H) (hm : m ≤ H) :
    ‖pairKernel S n m‖ ^ 2 ≤ 2 * zetaTwo * (H : ℝ) ^ 2 := by
  have hp : ‖pairKernel S n m‖ ≤ ‖evaluation n - evaluation m‖ := by
    exact (S.starProjection.le_opNorm _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le S) (norm_nonneg (evaluation n - evaluation m)))
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hp
  rw [norm_sub_sq_real, evaluation_norm_sq, evaluation_norm_sq] at hs
  have hnR : (n : ℝ) ≤ H := by exact_mod_cast hn
  have hmR : (m : ℝ) ≤ H := by exact_mod_cast hm
  have hn2 := mul_self_le_mul_self (Nat.cast_nonneg n) hnR
  have hm2 := mul_self_le_mul_self (Nat.cast_nonneg m) hmR
  have hZ := zetaTwo_pos
  nlinarith [evaluation_inner_nonneg n m]

theorem pairKernel_tail_norm_le (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (H A n m : ℕ) (hn : n ≤ H) (hm : m ≤ H) :
    ‖tail A (reciprocalD (toPareto (pairKernel S n m)))‖ ≤
      zetaTwo * Real.sqrt 2 * H /
        Real.sqrt (((A : ℝ) + 1) * ((A : ℝ) + 2)) := by
  have hZ := zetaTwo_pos
  have h := (reciprocal_tail_norm_sq_le (pairKernel S n m) A).trans
    (mul_le_mul_of_nonneg_left (pairKernel_norm_sq_le S H n m hn hm) (by positivity))
  have he : zetaTwo / (((A : ℝ) + 1) * ((A : ℝ) + 2)) *
        (2 * zetaTwo * (H : ℝ) ^ 2) =
      (zetaTwo * Real.sqrt 2 * H /
        Real.sqrt (((A : ℝ) + 1) * ((A : ℝ) + 2))) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt (by positivity)]
    ring
  rw [he] at h
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h

def signedTail (A : ℕ) (r : ThresholdHilbert) (f : QHilbert) : ℝ :=
  inner ℝ (tail A r) (tail A (reciprocalD (toPareto f)))

def signedHead (A : ℕ) (r : ThresholdHilbert) (f : QHilbert) : ℝ :=
  inner ℝ r (finiteHead A (reciprocalD (toPareto f)))

theorem signed_head_tail (A : ℕ) (r : ThresholdHilbert) (f : QHilbert) :
    inner ℝ r (reciprocalD (toPareto f)) = signedHead A r f + signedTail A r f := by
  have ho := inner_finiteHead_tail A r (reciprocalD (toPareto f))
  change inner ℝ (finiteHead A r) (tail A (reciprocalD (toPareto f))) = 0 at ho
  unfold signedHead signedTail
  change inner ℝ r _ = _ +
    inner ℝ (r - finiteHead A r) (tail A (reciprocalD (toPareto f)))
  rw [inner_sub_left, ho, sub_zero, tail, inner_sub_right]
  ring

theorem screened_signed_head_tail (T : Submodule ℝ ThresholdHilbert)
    [T.HasOrthogonalProjection] (A : ℕ) (r : ThresholdHilbert) (hr : r ∈ Tᗮ)
    (f : QHilbert) :
    inner ℝ r (screenReciprocal T f) = signedHead A r f + signedTail A r f := by
  rw [screenReciprocal, inner_sub_right, orthogonal_inner_projection T hr, sub_zero]
  exact signed_head_tail A r f

theorem signedTail_bound (r : ℕ → ThresholdHilbert) {B : ℝ}
    (hr : ∀ j, ‖r j‖ ≤ B)
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (H A n m j : ℕ) (hn : n ≤ H) (hm : m ≤ H) :
    |signedTail A (r j) (pairKernel S n m)| ≤
      zetaTwo * Real.sqrt 2 *
        ((H : ℝ) * tailEnvelope r A /
          Real.sqrt (((A : ℝ) + 1) * ((A : ℝ) + 2))) := by
  have hZ := zetaTwo_pos
  calc
    _ ≤ ‖tail A (r j)‖ * ‖tail A (reciprocalD (toPareto (pairKernel S n m)))‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ tailEnvelope r A *
        (zetaTwo * Real.sqrt 2 * H /
          Real.sqrt (((A : ℝ) + 1) * ((A : ℝ) + 2))) :=
      mul_le_mul (tail_le_envelope r hr A j) (pairKernel_tail_norm_le S H A n m hn hm)
        (norm_nonneg _) (envelope_nonneg r hr A)
    _ = _ := by ring

/-- The bound is uniform in the stage j, subspace, and every pair in the head. -/
theorem uniform_signedTail_tendsto_bound (r : ℕ → ThresholdHilbert)
    (rLimit : ThresholdHilbert) (hconv : Tendsto r atTop (𝓝 rLimit))
    {B : ℝ} (hr : ∀ j, ‖r j‖ ≤ B) :
    Tendsto (fun H : ℕ => zetaTwo * Real.sqrt 2 *
      ((H : ℝ) * tailEnvelope r (cutoff (tailEnvelope r) H) /
        Real.sqrt (((cutoff (tailEnvelope r) H : ℝ) + 1) *
          ((cutoff (tailEnvelope r) H : ℝ) + 2))))
      atTop (𝓝 0) := by
  simpa only [mul_zero] using
    (normalized_tail_tendsto_zero (tailEnvelope r) (envelope_nonneg r hr)
      (envelope_antitone r hr) (envelope_tendsto_zero r rLimit hconv hr)).const_mul
        (zetaTwo * Real.sqrt 2)

end RiemannResearch.RH.QMatchedShortHead
