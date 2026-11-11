/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimorialSchurCertificate
import RiemannResearch.RH.QSquarefreeDisplacementEnergy
import Mathlib.Tactic.Module

/-!
# Certified finite primorial resolvents

Source: the squarefree CRT displacement research agenda, 9 November 2026,
and the request of 10 November to produce cofinally small Schur upper
endpoints. The centered iteration and restarted degree-two Chebyshev
polynomial are the finite-stage versions of QDisplacementChebyshevResolvent
(Golub--Varga, Chebyshev semi-iterative methods, I, 1961, section 2).

The recursion uses the Q projection and reciprocal multiplier, without
using the unknown Pareto optimizer. Its complete Hilbert error contracts
by 1/17 per two-step cycle. The arithmetic initial-error certificate uses
the existing exact four-site constant 983/2000. These error estimates do
not assert that the actual displacement vanishes.
-/

noncomputable section
namespace RiemannResearch.RH.QPrimorialResolvent
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoClosedProjectionComparison QSquarefreePrimorialCofinality
open QPrimorialMatchedDisplacement QShiftedReciprocal
open QSquarefreeBoundary QSquarefreeDisplacementEnergy

theorem projection_norm_le (S : Submodule ℝ QHilbert)
    [S.HasOrthogonalProjection] (f : QHilbert) :
    ‖S.starProjection f‖ ≤ ‖f‖ :=
  (S.starProjection.le_opNorm f).trans (by
    simpa using mul_le_mul_of_nonneg_right
      (Submodule.starProjection_norm_le S) (norm_nonneg f))

theorem stage_pairing (n : ℕ) {v : QHilbert} (hv : v ∈ primorialStage n) :
    inner ℝ v (stageDisplacement n) =
      inner ℝ v (B (qOne - pOptimizer n)) := by
  have hp : inner ℝ (toPareto v) (toPareto (qOne - pOptimizer n)) = 0 := by
    change inner ℝ (toPareto v) (toPareto (qOne - pFit (paretoStage n) qOne)) = 0
    rw [toPareto_sub, toPareto_pFit]
    exact Submodule.inner_right_of_mem_orthogonal
      ((toPareto_mem_stage_iff n v).mpr hv)
      (Submodule.sub_starProjection_mem_orthogonal (K := paretoStage n) (toPareto qOne))
  rw [pareto_inner_identity] at hp
  have hp' := (mul_eq_zero.mp hp).resolve_left zetaTwo_pos.ne'
  have hq := Submodule.inner_right_of_mem_orthogonal hv
    (Submodule.sub_starProjection_mem_orthogonal (K := primorialStage n) qOne)
  change inner ℝ v (qOne - primorialOptimizer n) = 0 at hq
  rw [inner_sub_right] at hq hp'
  rw [stageDisplacement, inner_sub_right]
  linarith

/-- The canonical finite displacement is a fixed point of Q-only feedback. -/
theorem displacement_projected (n : ℕ) :
    (primorialStage n).starProjection (B (qOne - pOptimizer n)) =
      stageDisplacement n := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (stageDisplacement_mem n)
  intro v hv
  rw [real_inner_comm, inner_sub_right, ← stage_pairing n hv, sub_self]

def correction (n : ℕ) : QHilbert :=
  (primorialStage n).starProjection (B (qOne - primorialOptimizer n))

theorem displacement_fixed_point (n : ℕ) :
    stageDisplacement n = correction n +
      (primorialStage n).starProjection (B (stageDisplacement n)) := by
  have he : qOne - pOptimizer n =
      (qOne - primorialOptimizer n) + stageDisplacement n := by
    unfold stageDisplacement
    abel
  calc
    _ = (primorialStage n).starProjection (B (qOne - pOptimizer n)) :=
      (displacement_projected n).symm
    _ = _ := by rw [he, map_add, map_add]; rfl

private theorem stage_fourSite (n : ℕ) {f : QHilbert} (hf : f ∈ primorialStage n) :
    fourSiteFunctional f = 0 := by
  apply fourSiteFunctional_zero_on_closure
  rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact qSquarefreeCRTSpan.le_topologicalClosure (primorialStage_le_squarefreeSpan n hf)

/-- Exact finite-stage arithmetic identity, with both full energy remainders. -/
theorem displacement_energy_exact (n : ℕ) :
    ‖qOne - primorialOptimizer n‖ ^ 2 =
      (8136000 / 966289 : ℝ) * ‖stageDisplacement n‖ ^ 2 +
      (2000 / 983 : ℝ) * inner ℝ
        ((qOne - primorialOptimizer n) - (2034 / 983 : ℝ) • stageDisplacement n)
        (B ((qOne - primorialOptimizer n) - (2034 / 983 : ℝ) • stageDisplacement n)) +
      (‖(qOne - primorialOptimizer n) + (4000 / 983 : ℝ) • stageDisplacement n‖ ^ 2 -
        (2000 / 983 : ℝ) * inner ℝ
          ((qOne - primorialOptimizer n) + (4000 / 983 : ℝ) • stageDisplacement n)
          (B ((qOne - primorialOptimizer n) + (4000 / 983 : ℝ) • stageDisplacement n))) := by
  have ho : inner ℝ (stageDisplacement n) (qOne - primorialOptimizer n) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (stageDisplacement_mem n)
      (Submodule.sub_starProjection_mem_orthogonal (K := primorialStage n) qOne)
  have hn : inner ℝ (stageDisplacement n)
      (B ((qOne - primorialOptimizer n) + stageDisplacement n)) =
        ‖stageDisplacement n‖ ^ 2 := by
    have he : (qOne - primorialOptimizer n) + stageDisplacement n =
        qOne - pOptimizer n := by unfold stageDisplacement; abel
    rw [he, ← stage_pairing n (stageDisplacement_mem n), real_inner_self_eq_norm_sq]
  have h := displacement_energy_remainder_param (qOne - primorialOptimizer n)
    (stageDisplacement n) (4000 / 983 : ℝ) ho hn
  norm_num at h
  simpa only [neg_smul, ← sub_eq_add_neg, map_add, map_sub, map_smul] using h

theorem displacement_energy_bound (n : ℕ) :
    ‖stageDisplacement n‖ ^ 2 ≤ (966289 / 8136000 : ℝ) * primorialError n := by
  have hopt : fourSiteFunctional (primorialOptimizer n) = 0 :=
    stage_fourSite n ((primorialStage n).starProjection_apply_mem qOne)
  have hr : fourSiteFunctional (qOne - primorialOptimizer n) = 0 := by
    rw [map_sub, fourSiteFunctional_qOne, hopt, sub_self]
  have hd := stage_fourSite n (stageDisplacement_mem n)
  have hf : fourSiteFunctional
      ((qOne - primorialOptimizer n) + (4000 / 983 : ℝ) • stageDisplacement n) = 0 := by
    simp only [map_add, map_smul, hr, hd, smul_zero, add_zero]
  have hb := B_inner_le_four_site_983_2000 hf
  have hp := B_positive
    ((qOne - primorialOptimizer n) - (2034 / 983 : ℝ) • stageDisplacement n)
  have he := displacement_energy_exact n
  change ‖stageDisplacement n‖ ^ 2 ≤
    (966289 / 8136000 : ℝ) * ‖qOne - primorialOptimizer n‖ ^ 2
  linarith

theorem primorialError_le_one (n : ℕ) : primorialError n ≤ 1 := by
  have he : qOne - primorialOptimizer n = (primorialStage n)ᗮ.starProjection qOne := by
    rw [Submodule.starProjection_orthogonal]
    rfl
  have hn := projection_norm_le (primorialStage n)ᗮ qOne
  rw [← he, qOne_norm] at hn
  change ‖qOne - primorialOptimizer n‖ ^ 2 ≤ 1
  nlinarith [norm_nonneg (qOne - primorialOptimizer n)]

def feedback (n : ℕ) (f : QHilbert) : QHilbert :=
  (4 / 3 : ℝ) • (primorialStage n).starProjection (B f - (1 / 4 : ℝ) • f)

theorem feedback_sub (n : ℕ) (f g : QHilbert) :
    feedback n (f - g) = feedback n f - feedback n g := by
  unfold feedback
  have he : B (f - g) - (1 / 4 : ℝ) • (f - g) =
      (B f - (1 / 4 : ℝ) • f) - (B g - (1 / 4 : ℝ) • g) := by
    rw [map_sub, smul_sub]
    abel
  rw [he, map_sub, smul_sub]

theorem feedback_norm_le (n : ℕ) (f : QHilbert) :
    ‖feedback n f‖ ≤ (1 / 3 : ℝ) * ‖f‖ := by
  unfold feedback
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  have h := (projection_norm_le (primorialStage n) _).trans (B_centered_norm_le f)
  nlinarith

private theorem feedback_mem (n : ℕ) (f : QHilbert) :
    feedback n f ∈ primorialStage n :=
  (primorialStage n).smul_mem _ ((primorialStage n).starProjection_apply_mem _)

theorem displacement_centered_fixed_point (n : ℕ) :
    stageDisplacement n = (4 / 3 : ℝ) • correction n + feedback n (stageDisplacement n) := by
  have hf := displacement_fixed_point n
  unfold feedback
  rw [map_sub, map_smul, Submodule.starProjection_eq_self_iff.mpr (stageDisplacement_mem n)]
  have he : (primorialStage n).starProjection (B (stageDisplacement n)) =
      stageDisplacement n - correction n := by
    apply eq_sub_iff_add_eq.mpr
    calc
      _ = correction n + (primorialStage n).starProjection (B (stageDisplacement n)) :=
        add_comm _ _
      _ = stageDisplacement n := hf.symm
  rw [he]
  module

private theorem inner_projected_right (n : ℕ) (x y : QHilbert) (hx : x ∈ primorialStage n) :
    inner ℝ x ((primorialStage n).starProjection y) = inner ℝ x y := by
  have h := Submodule.inner_right_of_mem_orthogonal hx
    (Submodule.sub_starProjection_mem_orthogonal (K := primorialStage n) y)
  rw [inner_sub_right] at h
  linarith

theorem feedback_symmetric (n : ℕ) (x y : QHilbert)
    (hx : x ∈ primorialStage n) (hy : y ∈ primorialStage n) :
    inner ℝ (feedback n x) y = inner ℝ x (feedback n y) := by
  unfold feedback
  rw [real_inner_smul_left, real_inner_smul_right]
  congr 1
  calc
    _ = inner ℝ y ((primorialStage n).starProjection (B x - (1 / 4 : ℝ) • x)) :=
      real_inner_comm _ _
    _ = inner ℝ y (B x - (1 / 4 : ℝ) • x) := inner_projected_right n _ _ hy
    _ = inner ℝ (B x - (1 / 4 : ℝ) • x) y := real_inner_comm _ _
    _ = inner ℝ x (B y - (1 / 4 : ℝ) • y) := by
      rw [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, B_symmetric]
    _ = _ := (inner_projected_right n _ _ hx).symm

def step (n : ℕ) (x : QHilbert) : QHilbert :=
  (4 / 3 : ℝ) • correction n + feedback n x

theorem step_error (n : ℕ) (x : QHilbert) :
    stageDisplacement n - step n x = feedback n (stageDisplacement n - x) := by
  unfold step
  rw [feedback_sub]
  have h := displacement_centered_fixed_point n
  conv_lhs => rw [h]
  abel

/-- Two Q-only affine steps, followed by the restarted Chebyshev combination. -/
def cycle (n : ℕ) (x : QHilbert) : QHilbert :=
  (18 / 17 : ℝ) • step n (step n x) - (1 / 17 : ℝ) • x

theorem cycle_error (n : ℕ) (x : QHilbert) :
    stageDisplacement n - cycle n x =
      (1 / 17 : ℝ) • ((18 : ℝ) • feedback n (feedback n (stageDisplacement n - x)) -
        (stageDisplacement n - x)) := by
  rw [← step_error n x, ← step_error n (step n x)]
  unfold cycle
  module

theorem chebyshev_numerator_sq (n : ℕ) (e : QHilbert) (he : e ∈ primorialStage n) :
    ‖(18 : ℝ) • feedback n (feedback n e) - e‖ ^ 2 =
      ‖e‖ ^ 2 - 36 * (‖feedback n e‖ ^ 2 - 9 * ‖feedback n (feedback n e)‖ ^ 2) := by
  have h := feedback_symmetric n (feedback n e) e (feedback_mem n e) he
  rw [real_inner_self_eq_norm_sq] at h
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, real_inner_smul_left, h]
  norm_num
  ring

theorem cycle_error_norm (n : ℕ) (x : QHilbert) (hx : x ∈ primorialStage n) :
    ‖stageDisplacement n - cycle n x‖ ≤ (1 / 17 : ℝ) * ‖stageDisplacement n - x‖ := by
  let e := stageDisplacement n - x
  have he : e ∈ primorialStage n := (primorialStage n).sub_mem (stageDisplacement_mem n) hx
  have hb := feedback_norm_le n (feedback n e)
  have hs := mul_self_le_mul_self (norm_nonneg _) hb
  have hsq := chebyshev_numerator_sq n e he
  have hle : ‖(18 : ℝ) • feedback n (feedback n e) - e‖ ≤ ‖e‖ := by
    nlinarith [norm_nonneg e]
  rw [cycle_error, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  exact mul_le_mul_of_nonneg_left hle (by norm_num)

def approx (n : ℕ) : ℕ → QHilbert
  | 0 => 0
  | k + 1 => cycle n (approx n k)

private theorem step_mem (n : ℕ) (x : QHilbert) : step n x ∈ primorialStage n :=
  (primorialStage n).add_mem
    ((primorialStage n).smul_mem _ ((primorialStage n).starProjection_apply_mem _))
    (feedback_mem n x)

theorem approx_mem (n k : ℕ) : approx n k ∈ primorialStage n := by
  induction k with
  | zero => exact (primorialStage n).zero_mem
  | succ k ih =>
    exact (primorialStage n).sub_mem
      ((primorialStage n).smul_mem _ (step_mem n _)) ((primorialStage n).smul_mem _ ih)

theorem approx_error_norm (n k : ℕ) :
    ‖stageDisplacement n - approx n k‖ ≤ (1 / 17 : ℝ)^k * ‖stageDisplacement n‖ := by
  induction k with
  | zero => simp [approx]
  | succ k ih =>
    calc
      _ ≤ (1 / 17 : ℝ) * ‖stageDisplacement n - approx n k‖ :=
        cycle_error_norm n _ (approx_mem n k)
      _ ≤ _ :=
        (mul_le_mul_of_nonneg_left ih (by norm_num : 0 ≤ (1/17:ℝ))).trans_eq (by ring)

/-- Complete arithmetic error certificate, uniform in the primorial stage. -/
theorem approx_error_sq (n k : ℕ) :
    ‖stageDisplacement n - approx n k‖ ^ 2 ≤
      (966289 / 8136000 : ℝ) * primorialError n * (1 / 289 : ℝ)^k := by
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (approx_error_norm n k)
  have hp : ((1 / 17 : ℝ)^k)^2 = (1 / 289 : ℝ)^k := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  rw [mul_pow, hp] at hs
  calc
    _ ≤ (1 / 289 : ℝ)^k * ‖stageDisplacement n‖ ^ 2 := hs
    _ ≤ (1 / 289 : ℝ)^k * ((966289 / 8136000 : ℝ) * primorialError n) :=
      mul_le_mul_of_nonneg_left (displacement_energy_bound n) (by positivity)
    _ = _ := by ring

/-- A posteriori error from one observed Chebyshev increment. -/
theorem approx_successor_error_norm (n k : ℕ) :
    ‖stageDisplacement n - approx n (k + 1)‖ ≤
      (1 / 16 : ℝ) * ‖approx n (k + 1) - approx n k‖ := by
  have hc := cycle_error_norm n (approx n k) (approx_mem n k)
  change ‖stageDisplacement n - approx n (k + 1)‖ ≤
    (1 / 17 : ℝ) * ‖stageDisplacement n - approx n k‖ at hc
  have ht : ‖stageDisplacement n - approx n k‖ ≤
      ‖stageDisplacement n - approx n (k + 1)‖ +
        ‖approx n (k + 1) - approx n k‖ := by
    calc
      _ = ‖(stageDisplacement n - approx n (k + 1)) +
          (approx n (k + 1) - approx n k)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  linarith

theorem approx_successor_error_sq (n k : ℕ) :
    ‖stageDisplacement n - approx n (k + 1)‖ ^ 2 ≤
      (1 / 256 : ℝ) * ‖approx n (k + 1) - approx n k‖ ^ 2 := by
  have h := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    (approx_successor_error_norm n k)
  nlinarith only [h]

end RiemannResearch.RH.QPrimorialResolvent
