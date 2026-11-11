/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimorialSchurEndpoints
import RiemannResearch.RH.QPrimorialPairingRefinement

/-!
# Quantitative residual bounds from finite Schur certificates

Source: the squarefree CRT priorities and the 10 November 2026 request
for small canonical upper endpoints. We specialize the already formalized
Bertrand prime-scale argument to the complete primorial stages, improve
the Schur coercivity using the exact 983/2000 four-site certificate, and
transfer each finite bound to the limiting Pareto residual. No assumption
of cofinal endpoint smallness is used in these finite inequalities.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimorialPrimeCarry
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoClosedProjectionComparison QSquarefreePrimorialCofinality

/-- The strongest existing rational four-site certificate improves the Schur gap. -/
theorem schurForm_coercive_983_2000 (n : ℕ) {x : QHilbert} (hx : x ∈ primeStage n) :
    (1017 / 2000 : ℝ) * zetaTwo * ‖x‖ ^ 2 ≤ schurForm n x x := by
  have hfit : pFit (paretoCarryStage n) x ∈ carryStage n :=
    pFit_mem _ _ (toPareto_mem_paretoCarryStage_iff n) x
  have ho := Submodule.inner_right_of_mem_orthogonal hx hfit.2
  have ho' : inner ℝ (pFit (paretoCarryStage n) x) x = 0 := by
    rw [real_inner_comm]
    exact ho
  have hnorm : ‖schurLift n x‖ ^ 2 = ‖x‖ ^ 2 + ‖pFit (paretoCarryStage n) x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, schurLift, inner_sub_left,
      inner_sub_right, inner_sub_right, ho, ho',
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hlegal : schurLift n x ∈ ZetaTwoOptimizerStage.closure := by
    rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
    exact qSquarefreeCRTSpan.le_topologicalClosure
      (primorialStage_le_squarefreeSpan n (schurLift_mem n hx))
  have hb := QSquarefreeDisplacementEnergy.B_inner_le_four_site_983_2000
    (QSquarefreeBoundary.fourSiteFunctional_zero_on_closure hlegal)
  have hm := QShiftedReciprocal.pareto_inner_identity (schurLift n x) (schurLift n x)
  simp only [real_inner_self_eq_norm_sq] at hm
  have hbZ := mul_le_mul_of_nonneg_left hb zetaTwo_pos.le
  rw [schurForm, real_inner_self_eq_norm_sq]
  have hp := mul_nonneg zetaTwo_pos.le (sq_nonneg ‖pFit (paretoCarryStage n) x‖)
  have hnZ := congrArg (fun t : ℝ => zetaTwo * t) hnorm
  nlinarith only [hm, hbZ, hp, hnZ]

theorem selfForcing_coercive_983_2000 (n : ℕ) :
    (1017 / 2000 : ℝ) * zetaTwo * ‖primeComponent n‖ ^ 2 ≤ selfForcing n := by
  have hm : primeComponent n ∈ primeStage n := (primeStage n).starProjection_apply_mem _
  rw [selfForcing, ← schur_equation n hm]
  exact schurForm_coercive_983_2000 n hm

end RiemannResearch.RH.QPrimorialPrimeCarry

namespace RiemannResearch.RH.QPrimorialResidualCertificate
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoClosedProjectionComparison QSquarefreePrimorialCofinality
open QPrimorialMatchedDisplacement QPrimorialPrimeCarry QPrimorialSchurEndpoints
open QSquarefreeDisplacementRigidity
open RiemannResearch.NumberTheory.PrimeScaleBounds

theorem prime_residual_control (n p : ℕ) (hp : p.Prime) (hle : p ≤ n + 3) :
    pError n ≤ Real.sqrt (2 * zetaTwo * (p : ℝ)) * ‖primeComponent n‖ +
      Real.sqrt (pError n / (p : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hmem : qResidue p ∈ primeStage n :=
    Submodule.subset_span ⟨p, Nat.mem_primesLE.mpr ⟨hle, hp⟩, rfl⟩
  have hr := Submodule.inner_right_of_mem_orthogonal hmem
    (Submodule.sub_starProjection_mem_orthogonal (K := primeStage n) (stageDisplacement n))
  rw [inner_sub_right] at hr
  have heq : inner ℝ (qResidue p) (stageDisplacement n) =
      inner ℝ (qResidue p) (primeComponent n) := sub_eq_zero.mp hr
  have hinner : normalizedPairing n p ≤
      Real.sqrt (2 * zetaTwo * (p : ℝ)) * ‖primeComponent n‖ := by
    rw [normalizedPairing, heq]
    calc
      _ ≤ (zetaTwo * (p : ℝ)) * (‖qResidue p‖ * ‖primeComponent n‖) :=
        mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (abs_real_inner_le_norm _ _))
          (mul_nonneg zetaTwo_pos.le hpR.le)
      _ = ((zetaTwo * (p : ℝ)) * ‖qResidue p‖) * ‖primeComponent n‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (QSquarefreeFiniteDisplacement.scaled_qResidue_norm_le p hp.two_le) (norm_nonneg _)
  have herr := normalizedPairing_energy_bound n p hp.pos (prime_mem n p hp hle)
  have hsqrt : Real.sqrt (1 / (p : ℝ)) * ‖toPareto (qOne - pOptimizer n)‖ =
      Real.sqrt (pError n / (p : ℝ)) := by
    calc
      _ = Real.sqrt (1 / (p : ℝ)) *
          Real.sqrt (‖toPareto (qOne - pOptimizer n)‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      _ = Real.sqrt ((1 / (p : ℝ)) * ‖toPareto (qOne - pOptimizer n)‖ ^ 2) :=
        (Real.sqrt_mul (by positivity) _).symm
      _ = _ := by unfold pError; congr 1; ring
  rw [hsqrt] at herr
  have hh := (le_abs_self _).trans herr
  linarith

theorem pError_cube_le_primeComponent (n : ℕ) :
    (pError n)^3 ≤ max ((8 / ((n : ℝ) + 3))^3)
      (64 * zetaTwo * ‖primeComponent n‖ ^ 2) := by
  have he : 0 ≤ pError n := sq_nonneg _
  have hH : (0 : ℝ) < (n : ℝ) + 3 := by positivity
  by_cases hscale : 8 ≤ pError n * ((n : ℝ) + 3)
  · have hepos : 0 < pError n := by
      by_contra hn
      have hz : pError n = 0 := le_antisymm (le_of_not_gt hn) he
      norm_num [hz] at hscale
    obtain ⟨p, hp, hpN, hlo, hhi⟩ := exists_prime_at_residual_scale (pError n) (n + 3)
      hepos (pError_le_one n) (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hscale)
    have hc := cube_le_of_prime_scale (pError n) ‖primeComponent n‖ zetaTwo (p : ℝ)
      hepos (norm_nonneg _) zetaTwo_pos (by exact_mod_cast hp.pos)
      hlo hhi (prime_residual_control n p hp hpN)
    exact hc.trans (le_max_right _ _)
  · have hel : pError n ≤ 8 / ((n : ℝ) + 3) :=
      (le_div_iff₀ hH).mpr (lt_of_not_ge hscale).le
    have hc : (pError n)^3 ≤ (8 / ((n : ℝ) + 3))^3 := by gcongr
    exact hc.trans (le_max_left _ _)

/-- A single certified Schur bound controls the complete finite Pareto error. -/
theorem pError_cube_le_upper (n : ℕ) (U : ℝ) (hU : selfForcing n ≤ U) :
    (pError n)^3 ≤ max ((8 / ((n : ℝ) + 3))^3) ((128000 / 1017 : ℝ) * U) := by
  have hb : 64 * zetaTwo * ‖primeComponent n‖ ^ 2 ≤ (128000 / 1017 : ℝ) * U := by
    have hc := selfForcing_coercive_983_2000 n
    linarith
  exact (pError_cube_le_primeComponent n).trans (max_le_max_left _ hb)

theorem pError_antitone : Antitone pError := by
  intro n m hnm
  have hle : paretoStage n ≤ paretoStage m := Submodule.map_mono (primorialStage_mono hnm)
  have hz : (paretoStage m)ᗮ.starProjection
      ((paretoStage n).starProjection (toPareto qOne)) = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero
      (hle ((paretoStage n).starProjection_apply_mem _))
  have he : (paretoStage m)ᗮ.starProjection (toPareto (qOne - pOptimizer n)) =
      toPareto (qOne - pOptimizer m) := by
    simp only [pOptimizer, toPareto_sub, toPareto_pFit, map_sub, hz, sub_zero]
    rw [Submodule.starProjection_orthogonal]
    rfl
  have hn : ‖(paretoStage m)ᗮ.starProjection (toPareto (qOne - pOptimizer n))‖ ≤
      ‖toPareto (qOne - pOptimizer n)‖ :=
    ((paretoStage m)ᗮ.starProjection.le_opNorm _).trans (by
      simpa using mul_le_mul_of_nonneg_right
        (Submodule.starProjection_norm_le _) (norm_nonneg _))
  rw [he] at hn
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn

theorem limiting_pError_le (n : ℕ) : ‖toPareto pResidual‖ ^ 2 ≤ pError n := by
  apply le_of_tendsto pError_tendsto
  filter_upwards [eventually_ge_atTop n] with m hm
  exact pError_antitone hm

/-- A finite complete certificate bounds the limiting residual, unconditionally. -/
theorem limiting_pError_cube_le_upper (n : ℕ) (U : ℝ) (hU : selfForcing n ≤ U) :
    (‖toPareto pResidual‖ ^ 2)^3 ≤
      max ((8 / ((n : ℝ) + 3))^3) ((128000 / 1017 : ℝ) * U) := by
  have hc : (‖toPareto pResidual‖ ^ 2)^3 ≤ (pError n)^3 := by
    gcongr
    exact limiting_pError_le n
  exact hc.trans (pError_cube_le_upper n U hU)

theorem limiting_pError_cube_le_certified (n k : ℕ) :
    (‖toPareto pResidual‖ ^ 2)^3 ≤
      max ((8 / ((n : ℝ) + 3))^3)
        ((128000 / 1017 : ℝ) * min (upper n (k + 1)) (posteriorUpper n k)) :=
  limiting_pError_cube_le_upper n _ (min_upper_certified n k)

/-- Explicit finite stopping rule for any positive tolerance on residual energy. -/
theorem limiting_pError_le_tolerance (n : ℕ) (U ε : ℝ)
    (hU : selfForcing n ≤ U) (hε : 0 ≤ ε)
    (hstage : 8 / ((n : ℝ) + 3) ≤ ε)
    (hcert : (128000 / 1017 : ℝ) * U ≤ ε^3) :
    ‖toPareto pResidual‖ ^ 2 ≤ ε := by
  have hs : (8 / ((n : ℝ) + 3))^3 ≤ ε^3 := by gcongr
  have hc := (limiting_pError_cube_le_upper n U hU).trans (max_le hs hcert)
  exact (pow_le_pow_iff_left₀ (sq_nonneg _) hε (by decide : 3 ≠ 0)).mp hc

end RiemannResearch.RH.QPrimorialResidualCertificate
