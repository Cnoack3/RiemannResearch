/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QParetoDisplacementResolvent
import RiemannResearch.RH.QParetoPrimorialForcing
import RiemannResearch.RH.QParetoSquareRootCompactness
import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import RiemannResearch.RH.QPrimorialResidualCertificate

/-!
# Finite-rank certificates for the complete Pareto forcing and its inverse

Source: Pareto-first research agenda, Priority 6, 11 November 2026.
The physical cutoff retains sites 1 through H. The full reciprocal tail
has exact operator norm 1/(H+1). Tail, approximate forcing, and inverse
iteration errors remain separate in the final complete-norm certificate.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QParetoFiniteRankForcing
open Pareto ZetaTwoHilbert QFiniteSupportDualCriterion
open QParetoDisplacementBounds QParetoDisplacementResolvent

def reciprocalHead (H : ℕ) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  reciprocalD.comp (finiteHeadCLM H)

theorem reciprocal_single (n : ℕ) (a : ℝ) :
    reciprocalD (lp.single 2 n a) = lp.single 2 n (a / ((n : ℝ) + 1)) := by
  apply lp.ext
  funext k
  by_cases hk : k = n
  · subst k
    simp [reciprocalD_apply, lp.single_apply]
  · simp [reciprocalD_apply, lp.single_apply, hk]

/-- Explicit finite-rank synthesis, in the encoded Pareto coordinates. -/
theorem reciprocalHead_expansion (H : ℕ) (f : ThresholdHilbert) :
    reciprocalHead H f =
      ∑ n ∈ Finset.range H, lp.single 2 n (f n / ((n : ℝ) + 1)) := by
  simp only [reciprocalHead, ContinuousLinearMap.comp_apply, finiteHeadCLM_apply,
    finiteHead, map_sum, reciprocal_single]

theorem reciprocalHead_compact (H : ℕ) : IsCompactOperator (reciprocalHead H) :=
  (finiteHeadCLM_compact H).clm_comp reciprocalD

theorem reciprocalHead_error (H : ℕ) (f : ThresholdHilbert) :
    ‖reciprocalD f - reciprocalHead H f‖ ≤ ‖f‖ / ((H : ℝ) + 1) := by
  let u := f - finiteHead H f
  have hz (n : ℕ) (hn : n < H) : u n = 0 := by
    change f n - finiteHead H f n = 0
    rw [finiteHead_apply_of_lt H f n hn, sub_self]
  have h := reciprocalD_head_tail_bound u H
  have hh : (∑ n ∈ Finset.range H, (reciprocalD u n)^2) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [reciprocalD_apply, hz n (Finset.mem_range.mp hn), zero_div, zero_pow (by decide)]
  rw [hh, zero_add] at h
  have hu := finiteHead_remainder_norm_le H f
  have hu2 : ‖u‖ ^ 2 ≤ ‖f‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hu
  have hratio : ‖reciprocalD u‖ ^ 2 ≤ (‖f‖ / ((H : ℝ) + 1)) ^ 2 := by
    rw [div_pow]
    exact h.trans (div_le_div_of_nonneg_right hu2 (by positivity))
  have hn := (sq_le_sq₀ (norm_nonneg (reciprocalD u)) (by positivity)).mp hratio
  simpa only [reciprocalHead, ContinuousLinearMap.comp_apply, finiteHeadCLM_apply,
    u, map_sub] using hn

theorem reciprocalHead_opNorm_le (H : ℕ) :
    ‖reciprocalD - reciprocalHead H‖ ≤ 1 / ((H : ℝ) + 1) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  simpa only [sub_apply, one_div_mul_eq_div] using reciprocalHead_error H f

/-- The first omitted coordinate attains the complete operator error. -/
theorem reciprocalHead_opNorm_eq (H : ℕ) :
    ‖reciprocalD - reciprocalHead H‖ = 1 / ((H : ℝ) + 1) := by
  apply le_antisymm (reciprocalHead_opNorm_le H)
  let e : ThresholdHilbert := lp.single 2 H 1
  have hh : finiteHead H e = 0 := by
    unfold finiteHead
    apply Finset.sum_eq_zero
    intro n hn
    have hnH : n ≠ H := Nat.ne_of_lt (Finset.mem_range.mp hn)
    simp [e, lp.single_apply, hnH]
  have he : ‖(reciprocalD - reciprocalHead H) e‖ = 1 / ((H : ℝ) + 1) := by
    simp only [sub_apply, reciprocalHead, ContinuousLinearMap.comp_apply,
      finiteHeadCLM_apply, hh, map_zero, sub_zero, e, reciprocal_single]
    rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2), Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h := (reciprocalD - reciprocalHead H).le_opNorm e
  rw [he] at h
  simpa only [e, lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one, mul_one] using h

theorem reciprocalHead_tendsto : Tendsto reciprocalHead atTop (𝓝 reciprocalD) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop N] with H hH
  rw [dist_eq_norm, norm_sub_rev, reciprocalHead_opNorm_eq]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (H : ℝ) + 1)).mpr
  have hn : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
  have hNH : (N : ℝ) ≤ H := by exact_mod_cast hH
  nlinarith

theorem reciprocalD_compact : IsCompactOperator reciprocalD :=
  isCompactOperator_of_tendsto reciprocalHead_tendsto
    (Eventually.of_forall reciprocalHead_compact)

variable (T : Submodule ℝ ThresholdHilbert) [T.HasOrthogonalProjection]

theorem forcing_head_error (r : ThresholdHilbert) (H : ℕ) :
    ‖T.starProjection (reciprocalD r) - T.starProjection (reciprocalHead H r)‖ ≤
      ‖r‖ / ((H : ℝ) + 1) := by
  rw [← map_sub]
  exact (T.norm_starProjection_apply_le _).trans (reciprocalHead_error H r)


/-- The normal equation controls the full P-plus-reciprocal energy without a factor two. -/
theorem normal_solution_weighted_energy_le (d a : ThresholdHilbert) (hd : d ∈ T)
    (he : d + T.starProjection (reciprocalD d) = a) :
    ‖d‖ ^ 2 + inner ℝ d (reciprocalD d) ≤ ‖a‖ ^ 2 := by
  have ho := Submodule.inner_right_of_mem_orthogonal hd
    (Submodule.sub_starProjection_mem_orthogonal (K := T) (reciprocalD d))
  rw [inner_sub_right] at ho
  have hn := congrArg (fun x => inner ℝ d x) he
  rw [inner_add_right, real_inner_self_eq_norm_sq] at hn
  have hcs := real_inner_le_norm d a
  have hp := mul_le_mul_of_nonneg_right (displacement_le_forcing T d a hd he) (norm_nonneg a)
  nlinarith only [ho, hn, hcs, hp]

theorem inverse_lipschitz (a b : ThresholdHilbert) (ha : a ∈ T) (hb : b ∈ T) :
    ‖inverseSum T a - inverseSum T b‖ ≤ ‖a - b‖ := by
  apply displacement_le_forcing T _ _ (T.sub_mem (inverseSum_mem T a ha) (inverseSum_mem T b hb))
  have h₁ := inverseSum_normal_equation T a ha
  have h₂ := inverseSum_normal_equation T b hb
  rw [map_sub, map_sub]
  calc
    _ = (inverseSum T a + T.starProjection (reciprocalD (inverseSum T a))) -
      (inverseSum T b + T.starProjection (reciprocalD (inverseSum T b))) := by abel
    _ = _ := by rw [h₁, h₂]

/-- The inverse has Lipschitz constant one, so the finite-rank error is not amplified. -/
theorem inverse_head_error (r : ThresholdHilbert) (H : ℕ) :
    ‖inverseSum T (T.starProjection (reciprocalD r)) -
      inverseSum T (T.starProjection (reciprocalHead H r))‖ ≤ ‖r‖ / ((H : ℝ) + 1) :=
  (inverse_lipschitz T _ _ (T.starProjection_apply_mem _) (T.starProjection_apply_mem _)).trans
    (forcing_head_error T r H)

/-- Complete error: full infinite tail + supplied finite solve error + geometric inverse error. -/
theorem complete_inverse_budget (r b : ThresholdHilbert) (hb : b ∈ T)
    (H N : ℕ) (δ : ℝ)
    (hδ : ‖T.starProjection (reciprocalHead H r) - b‖ ≤ δ) :
    ‖inverseSum T (T.starProjection (reciprocalD r)) - inverseApprox T b N‖ ≤
      ‖r‖ / ((H : ℝ) + 1) + δ + (1 / 3 : ℝ)^N * ‖b‖ := by
  have hab : ‖T.starProjection (reciprocalD r) - b‖ ≤ ‖r‖ / ((H : ℝ) + 1) + δ := by
    calc
      _ = ‖(T.starProjection (reciprocalD r) - T.starProjection (reciprocalHead H r)) +
        (T.starProjection (reciprocalHead H r) - b)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (forcing_head_error T r H) hδ)
  have hI := (inverse_lipschitz T _ b (T.starProjection_apply_mem _) hb).trans hab
  have hN := inverseApprox_error_norm T (inverseSum T b) b (inverseSum_mem T b hb)
    (inverseSum_normal_equation T b hb) N
  calc
    _ = ‖(inverseSum T (T.starProjection (reciprocalD r)) - inverseSum T b) +
      (inverseSum T b - inverseApprox T b N)‖ := by congr 1; abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add hI hN)

open ZetaTwoParetoTransfer QParetoClosedProjectionComparison


/-- The complete Q energy has constant one after normalization by zeta(2). -/
theorem matched_q_energy_le_forcing
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ T ↔ f ∈ S) (x : QHilbert) :
    ZetaTwoProbability.zetaTwo * ‖qFit S x - pFit T x‖ ^ 2 ≤
      ‖T.starProjection (reciprocalD (toPareto (x - pFit T x)))‖ ^ 2 := by
  have hd : toPareto (qFit S x - pFit T x) ∈ T := by
    rw [toPareto_sub, toPareto_pFit]
    exact T.sub_mem (toPareto_qFit_mem S T hsame x) (T.starProjection_apply_mem _)
  have h := normal_solution_weighted_energy_le T _ _ hd
    (normal_equation_strong S T hsame x)
  rw [QParetoMetric.norm_identity]
  exact h

/-- The budget applies directly to the physical displacement of matched P and Q fits. -/
theorem matched_complete_inverse_budget
    (S : Submodule ℝ QHilbert) [S.HasOrthogonalProjection]
    (hsame : ∀ f : QHilbert, toPareto f ∈ T ↔ f ∈ S)
    (x : QHilbert) (b : ThresholdHilbert) (hb : b ∈ T) (H N : ℕ) (δ : ℝ)
    (hδ : ‖T.starProjection (reciprocalHead H (toPareto (x - pFit T x))) - b‖ ≤ δ) :
    ‖toPareto (qFit S x - pFit T x) - inverseApprox T b N‖ ≤
      ‖toPareto (x - pFit T x)‖ / ((H : ℝ) + 1) + δ +
        (1 / 3 : ℝ)^N * ‖b‖ := by
  rw [matched_displacement_eq_inverseSum T S hsame x]
  exact complete_inverse_budget T _ b hb H N δ hδ

open QParetoPrimorialForcing QPrimorialMatchedDisplacement QSquarefreePrimorialCofinality

theorem primorial_forcing_head_error (n H : ℕ) :
    ‖forcing n - (paretoStage n).starProjection (reciprocalHead H (residual n))‖ ≤
      1 / ((H : ℝ) + 1) := by
  have hr : ‖residual n‖ ≤ 1 := by
    have h := pError_le_one n
    change ‖toPareto (qOne - pOptimizer n)‖ ^ 2 ≤ 1 at h
    rw [← residual_eq_physical] at h
    nlinarith [norm_nonneg (residual n)]
  exact (forcing_head_error (paretoStage n) (residual n) H).trans
    (div_le_div_of_nonneg_right hr (by positivity))

/-- Uniform canonical certificate; the physical tail costs at most 1/(H+1) at every stage. -/
theorem primorial_complete_inverse_budget (n H N : ℕ) (b : ThresholdHilbert)
    (hb : b ∈ paretoStage n) (δ : ℝ)
    (hδ : ‖(paretoStage n).starProjection (reciprocalHead H (residual n)) - b‖ ≤ δ) :
    ‖toPareto (stageDisplacement n) - inverseApprox (paretoStage n) b N‖ ≤
      1 / ((H : ℝ) + 1) + δ + (1 / 3 : ℝ)^N * ‖b‖ := by
  have hr : ‖residual n‖ ≤ 1 := by
    have h := pError_le_one n
    change ‖toPareto (qOne - pOptimizer n)‖ ^ 2 ≤ 1 at h
    rw [← residual_eq_physical] at h
    nlinarith [norm_nonneg (residual n)]
  have hδ' : ‖(paretoStage n).starProjection
      (reciprocalHead H (toPareto (qOne - pFit (paretoStage n) qOne))) - b‖ ≤ δ := by
    simpa only [residual_eq_physical, pOptimizer] using hδ
  have h := matched_complete_inverse_budget (paretoStage n) (primorialStage n)
    (toPareto_mem_stage_iff n) qOne b hb H N δ hδ'
  change ‖toPareto (stageDisplacement n) - inverseApprox (paretoStage n) b N‖ ≤
    ‖toPareto (qOne - pOptimizer n)‖ / ((H : ℝ) + 1) + δ +
      (1 / 3 : ℝ)^N * ‖b‖ at h
  rw [← residual_eq_physical] at h
  have hbnd := div_le_div_of_nonneg_right hr (show 0 ≤ (H : ℝ) + 1 by positivity)
  linarith



/-- Using the full metric normal equation improves the earlier detector factor 128 to 64. -/
theorem primorial_pError_cube_le_forcing (n : ℕ) :
    (pError n)^3 ≤ max ((8 / ((n : ℝ) + 3))^3) (64 * ‖forcing n‖ ^ 2) := by
  have hm := matched_q_energy_le_forcing (paretoStage n) (primorialStage n)
    (toPareto_mem_stage_iff n) qOne
  change ZetaTwoProbability.zetaTwo * ‖stageDisplacement n‖ ^ 2 ≤
    ‖(paretoStage n).starProjection
      (reciprocalD (toPareto (qOne - pOptimizer n)))‖ ^ 2 at hm
  rw [← residual_eq_physical] at hm
  change ZetaTwoProbability.zetaTwo * ‖stageDisplacement n‖ ^ 2 ≤ ‖forcing n‖ ^ 2 at hm
  have hp := (QPrimorialPrimeCarry.primeStage n).norm_starProjection_apply_le (stageDisplacement n)
  have hp2 : ‖QPrimorialPrimeCarry.primeComponent n‖ ^ 2 ≤ ‖stageDisplacement n‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hp
  have hz := mul_le_mul_of_nonneg_left hp2 ZetaTwoProbability.zetaTwo_pos.le
  have he : 64 * ZetaTwoProbability.zetaTwo * ‖QPrimorialPrimeCarry.primeComponent n‖ ^ 2 ≤
      64 * ‖forcing n‖ ^ 2 := by nlinarith only [hz, hm]
  exact (QPrimorialResidualCertificate.pError_cube_le_primeComponent n).trans
    (max_le_max_left _ he)

/-- A complete finite-head bound plus its rigorous tail controls the limiting residual. -/
theorem limiting_pError_cube_le_head_forcing (n H : ℕ) (B : ℝ)
    (hB : ‖(paretoStage n).starProjection (reciprocalHead H (residual n))‖ ≤ B) :
    (‖toPareto QSquarefreeDisplacementRigidity.pResidual‖ ^ 2)^3 ≤
      max ((8 / ((n : ℝ) + 3))^3) (64 * (B + 1 / ((H : ℝ) + 1))^2) := by
  have hb0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hf : ‖forcing n‖ ≤ B + 1 / ((H : ℝ) + 1) := by
    have ht := primorial_forcing_head_error n H
    have hn := norm_le_norm_add_norm_sub
      ((paretoStage n).starProjection (reciprocalHead H (residual n))) (forcing n)
    rw [norm_sub_rev ((paretoStage n).starProjection (reciprocalHead H (residual n))) (forcing n)] at hn
    linarith
  have hf2 := (sq_le_sq₀ (norm_nonneg (forcing n)) (by positivity)).mpr hf
  have hlim : (‖toPareto QSquarefreeDisplacementRigidity.pResidual‖ ^ 2)^3 ≤
      (pError n)^3 := by
    gcongr
    exact QPrimorialResidualCertificate.limiting_pError_le n
  exact hlim.trans ((primorial_pError_cube_le_forcing n).trans
    (max_le_max_left _ (mul_le_mul_of_nonneg_left hf2 (by norm_num))))

end RiemannResearch.RH.QParetoFiniteRankForcing
