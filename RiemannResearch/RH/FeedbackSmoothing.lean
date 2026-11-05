/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeDisplacementResolvent
import Mathlib.Tactic.Positivity

/-!
# Dissipation in the centered resolvent with orthogonal forcing

The source is the component coming from the orthogonal complement. The
lost norm of each step of a self-adjoint compression controls this source,
giving a square-root gain over the geometric remainder.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeDisplacementResolvent
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeResidualTail
open QShiftedReciprocal QSquarefreeDisplacementRigidity QSquarefreeSmoothedProjection

private def reflection : QHilbert →ₗ[ℝ] QHilbert :=
  (4 : ℝ) • (B.toLinearMap - (1 / 4 : ℝ) • LinearMap.id)

private def compressedReflection : QHilbert →ₗ[ℝ] QHilbert :=
  closure.starProjection.toLinearMap.comp reflection

private def sweep : ℕ → QHilbert →ₗ[ℝ] QHilbert
  | 0 => LinearMap.id
  | j + 1 => compressedReflection.comp (sweep j)

private theorem refl_symm (x y : QHilbert) :
    inner ℝ (reflection x) y = inner ℝ x (reflection y) := by
  change inner ℝ ((4 : ℝ) • (B x - (1 / 4 : ℝ) • x)) y =
    inner ℝ x ((4 : ℝ) • (B y - (1 / 4 : ℝ) • y))
  simp only [real_inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, B_symmetric]

private theorem refl_norm (x : QHilbert) : ‖reflection x‖ ≤ ‖x‖ := by
  change ‖(4 : ℝ) • (B x - (1 / 4 : ℝ) • x)‖ ≤ ‖x‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith only [B_centered_norm_le x]

private theorem projection_inner {y : QHilbert} (hy : y ∈ closure) (x : QHilbert) :
    inner ℝ (closure.starProjection x) y = inner ℝ x y := by
  have h := Submodule.inner_right_of_mem_orthogonal hy
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) x)
  rw [inner_sub_right] at h
  calc
    inner ℝ (closure.starProjection x) y = inner ℝ y (closure.starProjection x) := real_inner_comm _ _
    _ = inner ℝ y x := by linarith only [h]
    _ = inner ℝ x y := real_inner_comm _ _

private theorem comp_mem (x : QHilbert) : compressedReflection x ∈ closure :=
  closure.starProjection_apply_mem _

private theorem comp_symm {x y : QHilbert} (hx : x ∈ closure) (hy : y ∈ closure) :
    inner ℝ (compressedReflection x) y = inner ℝ x (compressedReflection y) := by
  change inner ℝ (closure.starProjection (reflection x)) y =
    inner ℝ x (closure.starProjection (reflection y))
  calc
    _ = inner ℝ (reflection x) y := projection_inner hy _
    _ = inner ℝ x (reflection y) := refl_symm _ _
    _ = inner ℝ (reflection y) x := real_inner_comm _ _
    _ = inner ℝ (closure.starProjection (reflection y)) x := (projection_inner hx _).symm
    _ = _ := real_inner_comm _ _

private theorem sweep_mem {x : QHilbert} (hx : x ∈ closure) (j : ℕ) : sweep j x ∈ closure := by
  cases j with
  | zero => exact hx
  | succ j => exact comp_mem _

private theorem sweep_comm (x : QHilbert) (j : ℕ) :
    sweep j (compressedReflection x) = compressedReflection (sweep j x) := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg compressedReflection ih

private theorem sweep_symm {x y : QHilbert} (hx : x ∈ closure) (hy : y ∈ closure) (j : ℕ) :
    inner ℝ (sweep j x) y = inner ℝ x (sweep j y) := by
  induction j generalizing y with
  | zero => rfl
  | succ j ih =>
    change inner ℝ (compressedReflection (sweep j x)) y =
      inner ℝ x (compressedReflection (sweep j y))
    rw [comp_symm (sweep_mem hx j) hy, ih (comp_mem y), sweep_comm]

private theorem dissipated_norm (y : QHilbert) (hy : y ∈ closure) (j : ℕ) :
    Real.sqrt ((j : ℝ) + 1) *
      ‖reflection (sweep j y) - compressedReflection (sweep j y)‖ ≤ ‖y‖ := by
  let a (k : ℕ) := ‖sweep k y‖ ^ 2
  let D (k : ℕ) := a k - a (k+1)
  have hdec (k : ℕ) : D (k+1) ≤ D k := by
    let v := sweep k y
    have hinner : inner ℝ v (compressedReflection (compressedReflection v)) =
        ‖compressedReflection v‖ ^ 2 := by
      rw [← comp_symm (sweep_mem hy k) (comp_mem v), real_inner_self_eq_norm_sq]
    have h := sq_nonneg ‖v - compressedReflection (compressedReflection v)‖
    rw [norm_sub_sq_real, hinner] at h
    change ‖compressedReflection v‖ ^ 2 - ‖compressedReflection (compressedReflection v)‖ ^ 2 ≤
      ‖v‖ ^ 2 - ‖compressedReflection v‖ ^ 2
    linarith only [h]
  have htel (k : ℕ) : ((k : ℝ) + 1) * D k ≤ a 0 - a (k+1) := by
    induction k with
    | zero => simp [D]
    | succ k ih =>
      have hh := mul_le_mul_of_nonneg_left (hdec k) (show 0 ≤ (k : ℝ) + 1 by positivity)
      have he : D (k+1) = a (k+1) - a (k+2) := rfl
      rw [Nat.cast_succ]
      linarith only [ih, hh, he]
  let v := sweep j y
  let z := reflection v
  let p := compressedReflection v
  have hip : inner ℝ z p = ‖p‖ ^ 2 := by
    have h := projection_inner (comp_mem v) z
    change inner ℝ p p = inner ℝ z p at h
    rw [real_inner_self_eq_norm_sq] at h
    exact h.symm
  have hstep : ‖z - p‖ ^ 2 ≤ D j := by
    rw [norm_sub_sq_real, hip]
    change _ ≤ ‖v‖ ^ 2 - ‖p‖ ^ 2
    have hh := pow_le_pow_left₀ (norm_nonneg z) (refl_norm v) 2
    linarith only [hh]
  apply le_of_sq_le_sq _ (norm_nonneg y)
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hh := mul_le_mul_of_nonneg_left hstep (show 0 ≤ (j : ℝ) + 1 by positivity)
  have hh' := htel j
  change ((j : ℝ) + 1) * D j ≤ ‖y‖ ^ 2 - ‖sweep (j+1) y‖ ^ 2 at hh'
  linarith only [hh, hh', sq_nonneg ‖sweep (j+1) y‖]

private theorem sweep_orthogonal_source (r : QHilbert) (hr : r ∈ closureᗮ) (j : ℕ) :
    Real.sqrt ((j : ℝ) + 1) * ‖sweep j (compressedReflection r)‖ ≤ ‖r‖ := by
  let y := sweep j (compressedReflection r)
  let v := sweep j y
  have hy := sweep_mem (comp_mem r) j
  have hv := sweep_mem hy j
  have horth : inner ℝ r (compressedReflection v) = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal (comp_mem v) hr
  have hp : ‖y‖ ^ 2 = inner ℝ r (reflection v - compressedReflection v) := by
    calc
      _ = inner ℝ y y := (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ (compressedReflection r) v := sweep_symm (comp_mem r) hy j
      _ = inner ℝ (reflection r) v := projection_inner hv _
      _ = _ := by rw [refl_symm, inner_sub_right, horth, sub_zero]
  have hinner : ‖y‖ ^ 2 ≤ ‖r‖ * ‖reflection v - compressedReflection v‖ :=
    hp.le.trans (real_inner_le_norm _ _)
  have hsl := dissipated_norm y hy j
  change Real.sqrt ((j : ℝ) + 1) * ‖reflection v - compressedReflection v‖ ≤ ‖y‖ at hsl
  by_cases hz : y = 0
  · change _ * ‖y‖ ≤ _
    simpa only [hz, norm_zero, mul_zero] using norm_nonneg r
  have hpos := norm_pos_iff.mpr hz
  apply (le_of_mul_le_mul_right _ hpos)
  have h1 := mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg ((j : ℝ) + 1))
  have h2 := mul_le_mul_of_nonneg_left hsl (norm_nonneg r)
  change Real.sqrt ((j : ℝ) + 1) * ‖y‖ * ‖y‖ ≤ ‖r‖ * ‖y‖
  linarith only [h1, h2]

private theorem feedback_eq (x : QHilbert) :
    centeredFeedback x = (1 / 3 : ℝ) • compressedReflection x := by
  change (4 / 3 : ℝ) • closure.starProjection (B x - (1 / 4 : ℝ) • x) =
    (1 / 3 : ℝ) • closure.starProjection ((4 : ℝ) • (B x - (1 / 4 : ℝ) • x))
  rw [map_smul, smul_smul]
  norm_num

private theorem comp_residual : compressedReflection limitingResidual = (4 : ℝ) • correction := by
  have hr := limitingResidual_mem_squarefree_orthogonal
  have h1 := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem limitingResidual) hr
  have h2 := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem limitingResidual)
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) limitingResidual)
  rw [inner_sub_right, h1, real_inner_self_eq_norm_sq] at h2
  have hz : closure.starProjection limitingResidual = 0 := by
    apply norm_eq_zero.mp
    nlinarith only [h2, norm_nonneg (closure.starProjection limitingResidual)]
  change closure.starProjection ((4 : ℝ) • (B limitingResidual - (1 / 4 : ℝ) • limitingResidual)) = _
  rw [map_smul, map_sub, map_smul, hz, smul_zero, sub_zero] <;> rfl

private theorem centered_sweep_norm (j : ℕ) :
    2 * (Real.sqrt ((j : ℝ) + 1) * ‖sweep j displacement‖) ≤ ‖limitingResidual‖ := by
  have hid : displacement = (1 / 3 : ℝ) • compressedReflection limitingResidual +
      (1 / 3 : ℝ) • compressedReflection displacement := by
    rw [comp_residual, smul_smul, ← feedback_eq]
    convert displacement_centered_fixed_point using 2 <;> norm_num
  have hj := congrArg (sweep j) hid
  rw [map_add, map_smul, map_smul, sweep_comm displacement] at hj
  have htri := norm_add_le ((1 / 3 : ℝ) • sweep j (compressedReflection limitingResidual))
    ((1 / 3 : ℝ) • compressedReflection (sweep j displacement))
  rw [← hj, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)] at htri
  have hcn : ‖compressedReflection (sweep j displacement)‖ ≤ ‖sweep j displacement‖ :=
    (Submodule.norm_starProjection_apply_le closure _).trans (refl_norm _)
  have hco : 2 * ‖sweep j displacement‖ ≤ ‖sweep j (compressedReflection limitingResidual)‖ := by
    linarith only [htri, hcn]
  have h := sweep_orthogonal_source limitingResidual limitingResidual_mem_squarefree_orthogonal j
  have hh := mul_le_mul_of_nonneg_left hco (Real.sqrt_nonneg ((j : ℝ) + 1))
  linarith only [h, hh]

/-- Orthogonality of the actual residual source saves a factor √(j+1) beyond
geometric contraction of the centered transfer operator. -/
theorem resolvent_error_sqrt_depth (j : ℕ) :
    2 * Real.sqrt ((j : ℝ) + 1) * ‖displacement - resolventApprox j‖ ≤
      (1 / 3 : ℝ) ^ j * ‖limitingResidual‖ := by
  have hrep (k : ℕ) : displacement - resolventApprox k =
      ((1 / 3 : ℝ) ^ k) • sweep k displacement := by
    induction k with
    | zero => simp [resolventApprox, sweep]
    | succ k ih =>
      rw [resolvent_error_succ, feedback_eq, ih, map_smul, smul_smul, pow_succ]
      change ((1 / 3 : ℝ) * (1 / 3 : ℝ) ^ k) • _ = ((1 / 3 : ℝ) ^ k * (1 / 3 : ℝ)) • _
      rw [mul_comm (1 / 3 : ℝ)] <;> rfl
  rw [hrep, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_left (centered_sweep_norm j)
    (show 0 ≤ (1 / 3 : ℝ) ^ j by positivity)
  linarith only [h]

/- This fragment belongs directly before the closing namespace in FeedbackSmoothing. -/

open scoped BigOperators

private theorem sweep_add_apply (x : QHilbert) (k n : ℕ) :
    sweep (k + n) x = sweep n (sweep k x) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg compressedReflection ih

private theorem sweep_even_inner (x : QHilbert) (hx : x ∈ closure) (k n : ℕ) :
    inner ℝ (sweep (2*k) x) (sweep (2*n) x) = ‖sweep (k+n) x‖^2 := by
  calc
    _ = inner ℝ x (sweep (2*k) (sweep (2*n) x)) := sweep_symm hx (sweep_mem hx _) _
    _ = inner ℝ x (sweep ((k+n)+(k+n)) x) := by
      rw [← sweep_add_apply, show 2*n+2*k=(k+n)+(k+n) by omega]
    _ = inner ℝ (sweep (k+n) x) (sweep (k+n) x) := by
      rw [sweep_add_apply, ← sweep_symm hx (sweep_mem hx (k+n))]
    _ = _ := real_inner_self_eq_norm_sq _

private theorem sweep_energy_orthogonal_source (r : QHilbert) (hr : r ∈ closureᗮ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ‖sweep k (compressedReflection r)‖^2) ≤ ‖r‖^2 := by
  let w := compressedReflection r
  have hw : w ∈ closure := comp_mem r
  let Y (m : ℕ) := ∑ k ∈ Finset.range m, sweep (2*k) w
  have hY : Y N ∈ closure := Submodule.sum_mem _ (fun k _ => sweep_mem hw _)
  let s := ∑ k ∈ Finset.range N, ‖sweep k w‖^2
  have hs0 : 0 ≤ s := Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hsum : s = inner ℝ w (Y N) := by
    unfold Y s
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro k _
    have he := (sweep_even_inner w hw 0 k).symm
    simp only [Nat.mul_zero, Nat.zero_add] at he
    exact he
  have htail : 0 ≤ inner ℝ (Y N) (sweep (2*N) w) := by
    unfold Y
    rw [sum_inner]
    apply Finset.sum_nonneg
    intro k _
    rw [sweep_even_inner w hw k N]
    exact sq_nonneg _
  have htel (m : ℕ) : Y m - compressedReflection (compressedReflection (Y m)) =
      w - sweep (2*m) w := by
    induction m with
    | zero => simp [Y, sweep]
    | succ m ih =>
      have hpow : sweep (2*(m+1)) w = compressedReflection (compressedReflection (sweep (2*m) w)) := by
        rw [show 2*(m+1) = (2*m+1)+1 by omega]
        rfl
      have hs : Y (m+1) = Y m + sweep (2*m) w := Finset.sum_range_succ _ _
      rw [hs, map_add, map_add, hpow]
      calc
        _ = (Y m - compressedReflection (compressedReflection (Y m))) +
          sweep (2*m) w - compressedReflection (compressedReflection (sweep (2*m) w)) := by abel
        _ = _ := by rw [ih] <;> abel
  let z := reflection (Y N)
  let p := compressedReflection (Y N)
  have hp : inner ℝ z p = ‖p‖^2 := by
    have h := projection_inner (comp_mem (Y N)) z
    change inner ℝ p p = inner ℝ z p at h
    rw [real_inner_self_eq_norm_sq] at h
    exact h.symm
  have hpy : inner ℝ (Y N) (compressedReflection p) = ‖p‖^2 := by
    rw [← comp_symm hY (comp_mem (Y N)), real_inner_self_eq_norm_sq]
  have he : inner ℝ (Y N) (Y N - compressedReflection p) =
      inner ℝ (Y N) (w - sweep (2*N) w) := congrArg (inner ℝ (Y N)) (htel N)
  rw [inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq, hpy,
    show inner ℝ (Y N) w = s from (real_inner_comm _ _).trans hsum.symm] at he
  have hz : ‖z-p‖^2 ≤ s := by
    rw [norm_sub_sq_real, hp]
    have hh := pow_le_pow_left₀ (norm_nonneg z) (refl_norm (Y N)) 2
    linarith only [hh, he, htail]
  have ho : inner ℝ r p = 0 := by
    calc
      _ = inner ℝ p r := real_inner_comm _ _
      _ = 0 := Submodule.inner_right_of_mem_orthogonal (comp_mem _) hr
  have hcs : s ≤ ‖r‖ * ‖z-p‖ := by
    calc
      s = inner ℝ w (Y N) := hsum
      _ = inner ℝ (reflection r) (Y N) := projection_inner hY _
      _ = inner ℝ r z := refl_symm _ _
      _ = inner ℝ r (z-p) := by rw [inner_sub_right, ho, sub_zero]
      _ ≤ _ := real_inner_le_norm _ _
  change s ≤ ‖r‖^2
  rcases eq_or_lt_of_le hs0 with h0 | h0
  · rw [← h0]
    exact sq_nonneg _
  apply le_of_mul_le_mul_right _ h0
  have h1 := pow_le_pow_left₀ hs0 hcs 2
  rw [mul_pow] at h1
  have h2 := mul_le_mul_of_nonneg_left hz (sq_nonneg ‖r‖)
  linarith only [h1, h2]

/-- The errors left after removing geometric decay have finite square energy.
This is a simultaneous bound at every finite collection of initial depths. -/
theorem resolvent_error_weighted_energy (N : ℕ) :
    4 * (∑ k ∈ Finset.range N, (9 : ℝ)^k * ‖displacement - resolventApprox k‖^2)
      ≤ ‖limitingResidual‖^2 := by
  have hrep (k : ℕ) : displacement - resolventApprox k =
      ((1 / 3 : ℝ) ^ k) • sweep k displacement := by
    induction k with
    | zero => simp [resolventApprox, sweep]
    | succ k ih =>
      rw [resolvent_error_succ, feedback_eq, ih, map_smul, smul_smul, pow_succ]
      change ((1 / 3 : ℝ) * (1 / 3 : ℝ) ^ k) • _ = ((1 / 3 : ℝ) ^ k * (1 / 3 : ℝ)) • _
      rw [mul_comm (1 / 3 : ℝ)] <;> rfl
  have hc (j : ℕ) : 2 * ‖sweep j displacement‖ ≤ ‖sweep j (compressedReflection limitingResidual)‖ := by
    have hid : displacement = (1 / 3 : ℝ) • compressedReflection limitingResidual +
        (1 / 3 : ℝ) • compressedReflection displacement := by
      rw [comp_residual, smul_smul, ← feedback_eq]
      convert displacement_centered_fixed_point using 2 <;> norm_num
    have hj := congrArg (sweep j) hid
    rw [map_add, map_smul, map_smul, sweep_comm displacement] at hj
    have htri := norm_add_le ((1 / 3 : ℝ) • sweep j (compressedReflection limitingResidual))
      ((1 / 3 : ℝ) • compressedReflection (sweep j displacement))
    rw [← hj, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)] at htri
    have hcn : ‖compressedReflection (sweep j displacement)‖ ≤ ‖sweep j displacement‖ :=
      (Submodule.norm_starProjection_apply_le closure _).trans (refl_norm _)
    have hco : 2 * ‖sweep j displacement‖ ≤ ‖sweep j (compressedReflection limitingResidual)‖ := by
      linarith only [htri, hcn]
    exact hco
  apply le_trans _ (sweep_energy_orthogonal_source limitingResidual limitingResidual_mem_squarefree_orthogonal N)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [hrep, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
  have hh := pow_le_pow_left₀ (show 0 ≤ 2 * ‖sweep k displacement‖ by positivity) (hc k) 2
  have he : (9:ℝ)^k * ((1/3:ℝ)^k)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ← mul_pow]
    norm_num
  calc
    _ = 4 * ((9:ℝ)^k * ((1/3:ℝ)^k)^2) * ‖sweep k displacement‖^2 := by ring
    _ = (2 * ‖sweep k displacement‖)^2 := by rw [he]; ring
    _ ≤ _ := hh

end RiemannResearch.RH.QSquarefreeDisplacementResolvent
