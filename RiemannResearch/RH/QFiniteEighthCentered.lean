/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteEighthMoment
import RiemannResearch.RH.QFiniteEighthForcing
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QUniformTail
import Mathlib.Tactic.Module

/-! # Minimax centering for the matched finite displacement

Source: the finite eighth-moment handoff, using the two matched normal equations.
Every affine shift projects to the same actual displacement. Centering the omitted
reciprocal spectrum yields the denominator 2T+3 and preserves the boundedness
test on the aligned output. The retained shift acts by a taper on the original input.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QShiftedReciprocal QAnnihilatorTailEscape QFiniteSupportDualCriterion

/-- Subtracting a multiple of the Pareto normal vector preserves the full fit. -/
def affineForcing (a : ℝ) : QHilbert →L[ℝ] QHilbert :=
  (1 + a) • B - a • ContinuousLinearMap.id ℝ QHilbert

theorem stage_affineForcing_residual (N : ℕ) (a : ℝ) :
    (stage N).starProjection (affineForcing a (qOne - finitePFit N)) =
      finiteDisplacement N := by
  have hb := (stage N).starProjection_apply_eq_zero_iff.mpr (finite_witness_mem_orthogonal N)
  rw [map_sub, Submodule.starProjection_eq_self_iff.mpr (finiteDisplacement_mem N)] at hb
  have hr : (stage N).starProjection (qOne - finitePFit N) = finiteDisplacement N := by
    rw [finitePResidual_eq, map_add,
      (stage N).starProjection_apply_eq_zero_iff.mpr (residual_mem_orthogonal N),
      Submodule.starProjection_eq_self_iff.mpr (finiteDisplacement_mem N), zero_add]
  change (stage N).starProjection ((1 + a) • B (qOne - finitePFit N) -
    a • (qOne - finitePFit N)) = _
  rw [map_sub, map_smul, map_smul, sub_eq_zero.mp hb, hr, add_smul, one_smul]
  abel

/-- Truncate the actual Pareto residual after choosing a scalar shift.
The complete squarefree projection is retained. -/
def shiftedHeadForcing (N T : ℕ) (a : ℝ) : QHilbert :=
  (stage N).starProjection (affineForcing a (finiteHead T (qOne - finitePFit N)))

/-- Exact signed remainder, valid for every real shift. -/
theorem shiftedHeadForcing_remainder (N T : ℕ) (a : ℝ) :
    finiteDisplacement N - shiftedHeadForcing N T a =
      (stage N).starProjection (affineForcing a (tail T (qOne - finitePFit N))) := by
  rw [tail, map_sub, map_sub, stage_affineForcing_residual]
  rfl

/-- The smallest uniform tail multiplier in the affine family. Its two
extreme values occur at the first omitted site and in the limit at infinity. -/
def tailCenter (T : ℕ) : ℝ := 1 / (2 * (T : ℝ) + 3)

theorem tailCenter_minimax (T : ℕ) (a : ℝ) :
    tailCenter T ≤ max |a| |(1 + a) / ((T : ℝ) + 2) - a| := by
  let m := max |a| |(1 + a) / ((T : ℝ) + 2) - a|
  have hleft : a ≤ m := (le_abs_self a).trans (le_max_left _ _)
  have hright : (1 + a) / ((T : ℝ) + 2) - a ≤ m :=
    (le_abs_self _).trans (le_max_right _ _)
  have ht : 0 < (T : ℝ) + 2 := by positivity
  have h := (div_le_iff₀ ht).mp (show (1 + a) / ((T : ℝ) + 2) ≤ m + a by linarith)
  apply (div_le_iff₀ (by positivity : 0 < 2 * (T : ℝ) + 3)).mpr
  nlinarith [mul_nonneg (show 0 ≤ m - a by linarith) (show 0 ≤ (T : ℝ) + 1 by positivity)]

/-- On the omitted physical sites the scaled centered multiplier lies in [-1,1]. -/
theorem tailCenter_scaled_norm_le (T : ℕ) (f : QHilbert) (hf : ∀ i < T, f i = 0) :
    (2 * (T : ℝ) + 3) * ‖affineForcing (tailCenter T) f‖ ≤ ‖f‖ := by
  let D : ℝ := 2 * (T : ℝ) + 3
  have hD : 0 < D := by dsimp [D]; positivity
  have he : ‖D • affineForcing (tailCenter T) f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [qNorm_sq, qNorm_sq]
    apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _) (qCoordinate_square_summable _)
    intro i
    change (D * ((1 + 1 / D) * (f i / ((i : ℝ) + 2)) - (1 / D) * f i)) ^ 2 ≤ (f i) ^ 2
    by_cases hi : i < T
    · simp [hf i hi]
    · have hiT : (T : ℝ) ≤ i := by exact_mod_cast le_of_not_gt hi
      have hd : 0 < (i : ℝ) + 2 := by positivity
      let c := (D + 1) / ((i : ℝ) + 2) - 1
      have hlo : -1 ≤ c := by
        dsimp only [c]
        linarith [div_nonneg (show 0 ≤ D + 1 by linarith) hd.le]
      have hhi : c ≤ 1 := by
        have hratio : (D + 1) / ((i : ℝ) + 2) ≤ 2 := (div_le_iff₀ hd).mpr (by
          dsimp only [D]
          linarith)
        dsimp only [c]
        linarith
      have hsq : c ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - c) (by linarith : 0 ≤ 1 + c)]
      have hid : D * ((1 + 1 / D) * (f i / ((i : ℝ) + 2)) - (1 / D) * f i) =
          c * f i := by
        dsimp only [c]
        field_simp [hD.ne', hd.ne']
      rw [hid, mul_pow]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (f i))
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hD] using le_of_sq_le_sq he (norm_nonneg f)

/-- Exact constants for the shifted truncation of the matched projections. -/
theorem shiftedHeadForcing_scaled_error (N T : ℕ) :
    (2 * (T : ℝ) + 3) * ‖finiteDisplacement N - shiftedHeadForcing N T (tailCenter T)‖ ≤
      ‖tail T (qOne - finitePFit N)‖ := by
  rw [shiftedHeadForcing_remainder]
  have hp (v : QHilbert) : ‖(stage N).starProjection v‖ ≤ ‖v‖ :=
    ((stage N).starProjection.le_opNorm v).trans (by
      simpa using mul_le_mul_of_nonneg_right (Submodule.starProjection_norm_le (stage N))
        (norm_nonneg v))
  apply (mul_le_mul_of_nonneg_left (hp _) (by positivity)).trans
  apply tailCenter_scaled_norm_le
  intro i hi
  change (qOne - finitePFit N) i - finiteHead T (qOne - finitePFit N) i = 0
  rw [finiteHead_apply_of_lt _ _ _ hi, sub_self]

/-- At the improved comparison scale the centered error has vanishing
unnormalized aligned eighth moment. -/
theorem shiftedHeadForcing_eighth_error_tendsto (T : ℕ → ℕ)
    (hT : Tendsto T atTop atTop)
    (hscale : ∀ N : ℕ, (N : ℝ) ^ 6 ≤ (2 * (T N : ℝ) + 3) ^ 8) :
    Tendsto (fun N => eighthHead
      (finiteDisplacement N - shiftedHeadForcing N (T N) (tailCenter (T N))) N) atTop (𝓝 0) := by
  let v (N : ℕ) := finiteDisplacement N - shiftedHeadForcing N (T N) (tailCenter (T N))
  let R (N : ℕ) := ‖tail (T N) (qOne - finitePFit N)‖
  have hbound (N : ℕ) : eighthHead (v N) N ≤
      (zetaTwo * (Real.sqrt zetaTwo) ^ 6) * R N ^ 8 := by
    have hs := shiftedHeadForcing_scaled_error N (T N)
    have hu := weighted_eighth_head_le_norm (v N) N
    rw [eighthHead_eq_weighted]
    calc
      _ ≤ zetaTwo * ((Real.sqrt zetaTwo * (N : ℝ) * ‖v N‖) ^ 6 * ‖v N‖^2) :=
        mul_le_mul_of_nonneg_left hu zetaTwo_pos.le
      _ = (zetaTwo * (Real.sqrt zetaTwo) ^ 6) * ((N : ℝ) ^ 6 * ‖v N‖^8) := by ring
      _ ≤ (zetaTwo * (Real.sqrt zetaTwo) ^ 6) * (((2 * (T N : ℝ) + 3) * ‖v N‖) ^ 8) := by
        rw [mul_pow (2 * (T N : ℝ) + 3) _ 8]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hscale N) (by positivity))
          (mul_nonneg zetaTwo_pos.le (by positivity))
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg zetaTwo_pos.le (by positivity))
        exact pow_le_pow_left₀ (by positivity) hs 8
  have ht : Tendsto R atTop (𝓝 0) := finiteParetoResidual_tail_tendsto T hT
  apply squeeze_zero (fun N => Finset.sum_nonneg (fun i _ => by positivity)) hbound
  simpa only [zero_pow (by decide : 8 ≠ 0), mul_zero] using
    (ht.pow 8).const_mul (zetaTwo * (Real.sqrt zetaTwo) ^ 6)

/-- At the first omitted site the centered multiplier attains its uniform bound. -/
theorem tailCenter_first_omitted (T : ℕ) :
    (1 + tailCenter T) / ((T : ℝ) + 2) - tailCenter T = tailCenter T := by
  unfold tailCenter
  field_simp
  ring

/-- At this comparison scale the centered statistic tests precisely the
cofinal boundedness asked for in the original finite-eighth-moment problem. -/
theorem shiftedHeadForcing_eighth_bounded_iff (T : ℕ → ℕ)
    (hT : Tendsto T atTop atTop)
    (hscale : ∀ N : ℕ, (N : ℝ) ^ 6 ≤ (2 * (T N : ℝ) + 3) ^ 8) :
    (∃ C : ℝ, ∃ᶠ N : ℕ in atTop, eighthHead (finiteDisplacement N) N ≤ C) ↔
      ∃ C : ℝ, ∃ᶠ N : ℕ in atTop,
        eighthHead (shiftedHeadForcing N (T N) (tailCenter (T N))) N ≤ C :=
  frequently_eighthHead_bounded_iff_of_error (shiftedHeadForcing_eighth_error_tendsto T hT hscale)

open ZetaTwoHilbert ZetaTwoProbability
open QFiniteSupportDualCriterion QShiftedReciprocal ArithmeticCumulative

/-- The centered multiplier written as ordinary reciprocal forcing of tapered
    physical data, with the full vector zero above the input cutoff. -/
def taperedHead (T : ℕ) (f : QHilbert) : QHilbert :=
  ∑ j ∈ Finset.range T, lp.single 2 j ((1 - tailCenter T * ((j : ℝ) + 1)) * f j)

theorem taperedHead_apply (T : ℕ) (f : QHilbert) (j : ℕ) :
    taperedHead T f j = if j < T then (1 - tailCenter T * ((j : ℝ) + 1)) * f j else 0 := by
  classical
  simp only [taperedHead, lp.coeFn_sum, Finset.sum_apply]
  by_cases hj : j < T <;> simp [lp.single_apply, hj]

theorem qSequence_taperedHead (T : ℕ) (f : QHilbert) (k : ℕ) :
    qSequence (taperedHead T f) k =
      if k ≤ T then (1 - tailCenter T * (k : ℝ)) * qSequence f k else 0 := by
  cases k with
  | zero => simp
  | succ j =>
    by_cases hj : j < T
    · rw [if_pos (show j + 1 ≤ T by omega), qSequence_succ, qSequence_succ,
        taperedHead_apply, if_pos hj, Nat.cast_succ]
      ring
    · rw [if_neg (show ¬j + 1 ≤ T by omega), qSequence_succ, taperedHead_apply,
        if_neg hj, zero_div]

/-- The centered retained source enters exactly the same Schur matrix as the
    original source; only its physical data acquire the stated taper. -/
theorem affineForcing_finiteHead_eq_taper (T : ℕ) (f : QHilbert) :
    affineForcing (tailCenter T) (finiteHead T f) = finiteHead T (B (taperedHead T f)) := by
  apply lp.ext
  funext j
  change (1 + tailCenter T) * (finiteHead T f j / ((j : ℝ) + 2)) -
    tailCenter T * finiteHead T f j = finiteHead T (B (taperedHead T f)) j
  by_cases hj : j < T
  · rw [finiteHead_apply_of_lt T f j hj, finiteHead_apply_of_lt T _ j hj,
      B_apply, taperedHead_apply, if_pos hj]
    field_simp [ne_of_gt (by positivity : 0 < (j : ℝ) + 2)]
    ring
  · have hT : T ≤ j := by omega
    rw [finiteHead_apply_eq_zero T f j hT, finiteHead_apply_eq_zero T _ j hT]
    simp

/-- At every site in the head, the taper lies between zero and one. -/
theorem tailCenter_taper_bounds (T k : ℕ) (hk : k ≤ T) :
    0 ≤ 1 - tailCenter T * (k : ℝ) ∧ 1 - tailCenter T * (k : ℝ) ≤ 1 := by
  have hden : 0 < 2 * (T : ℝ) + 3 := by positivity
  have hkT : (k : ℝ) ≤ T := by exact_mod_cast hk
  have hkn : tailCenter T * (k : ℝ) = (k : ℝ) / (2 * (T : ℝ) + 3) := by
    simp [tailCenter, div_eq_mul_inv, mul_comm]
  rw [hkn]
  exact ⟨sub_nonneg.mpr ((div_le_iff₀ hden).mpr (by linarith [Nat.cast_nonneg T (α := ℝ)])),
    sub_le_self _ (div_nonneg (Nat.cast_nonneg k) hden.le)⟩

/-- Centering does not increase the physical Pareto input energy on any
    finite set. In particular, the bound holds on the entire retained head. -/
theorem taperedHead_pareto_energy_le (T : ℕ) (f : QHilbert) (s : Finset ℕ) :
    (∑ k ∈ s, weight k * (qSequence (taperedHead T f) k) ^ 2) ≤
      ∑ k ∈ s, weight k * (qSequence f k) ^ 2 := by
  apply Finset.sum_le_sum
  intro k _
  rw [qSequence_taperedHead]
  by_cases hk : k ≤ T
  · rw [if_pos hk, mul_pow]
    obtain ⟨hlo, hhi⟩ := tailCenter_taper_bounds T k hk
    have hs : (1 - tailCenter T * (k : ℝ)) ^ 2 ≤ (1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hlo hhi _
    have hu : (1 - tailCenter T * (k : ℝ)) ^ 2 * (qSequence f k) ^ 2 ≤ (qSequence f k) ^ 2 := by
      simpa only [one_pow, one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg (qSequence f k))
    exact mul_le_mul_of_nonneg_left hu (Pareto.positiveWeight_nonneg k)
  · rw [if_neg hk, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact mul_nonneg (Pareto.positiveWeight_nonneg k) (sq_nonneg _)

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
