/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ThreeStageSieveAlgebra
import RiemannResearch.Analysis.VanishingProbeCost
import RiemannResearch.RH.QSievePrimeJump
import RiemannResearch.RH.QPrimePowerSievePrimeStep
import RiemannResearch.RH.QPrimePowerSieveUniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Choose
import Mathlib.NumberTheory.Bertrand
import Lean.Elab.Tactic.Omega

/-!
# Actual three-stage prime-jump energy inequality

Source: user-requested signed-sieve investigation, 21 October 2026.
No bound on variation and no sign condition is assumed. All vectors are
the actual complete-Q sieve vectors; the two prime witnesses are explicit.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimePowerSieve
open ZetaTwoHilbert ZetaTwoProbability SquarefreeRadicalDifference
open RiemannResearch.Analysis.ThreeStageSieve

def threeStageVector (p K1 K2 K3 : ℕ) (u v w : ℝ) : QHilbert :=
  u • sieveVector (primorial K1) p + v • sieveVector (primorial K2) p +
    w • sieveVector (primorial K3) p

/-- Bertrand supplies a short prime witness inside any interval ending at a prime. -/
theorem exists_short_prime_before_prime (H K : ℕ) (hH : H ≠ 0)
    (hK : K.Prime) (hHK : H < K) :
    ∃ q, q.Prime ∧ H < q ∧ q ≤ K ∧ q ≤ 2 * H := by
  by_cases hshort : K ≤ 2 * H
  · exact ⟨K, hK, hHK, le_rfl, hshort⟩
  · obtain ⟨q, hq, hHq, hqH⟩ := Nat.exists_prime_lt_and_le_two_mul H hH
    exact ⟨q, hq, hHq, by omega, hqH⟩

theorem threeStage_probe_energy_bound (p K1 K2 K3 q1 q2 : ℕ)
    (hp : p.Prime) (hq1 : q1.Prime) (hq2 : q2.Prime)
    (hpK1 : p ≤ K1) (h1 : K1 < q1) (h12 : q1 ≤ K2)
    (h2 : K2 < q2) (h23 : q2 ≤ K3)
    (u v w x y z : ℝ) (hm : u + v + w = 1)
    (hd : u * sieveSlope (primorial K1) p + v * sieveSlope (primorial K2) p +
      w * sieveSlope (primorial K3) p = 0)
    (hyx : y ≤ x) (hzy : z ≤ y) :
    |u * x + v * y + w * z - z| ≤
      2 * Real.sqrt zetaTwo * (p : ℝ) *
      ‖u • sieveVector (primorial K1) p + v • sieveVector (primorial K2) p +
        w • sieveVector (primorial K3) p‖ *
      ((q1 : ℝ) * (x - y) + (q2 : ℝ) * (y - z)) := by
  let B := u • sieveVector (primorial K1) p + v • sieveVector (primorial K2) p +
    w • sieveVector (primorial K3) p
  have hpK2 : p ≤ K2 := by omega
  have hpK3 : p ≤ K3 := by omega
  have hpq1 : p < q1 := by omega
  have hpq2 : p < q2 := by omega
  have hj1 : qDifference B (p * q1) = u := by
    dsimp only [B]
    simp only [qDifference_add, qDifference_smul,
      qDifference_sieveVector_semiprime p q1 K1 hp hq1 hpK1 hpq1,
      qDifference_sieveVector_semiprime p q1 K2 hp hq1 hpK2 hpq1,
      qDifference_sieveVector_semiprime p q1 K3 hp hq1 hpK3 hpq1,
      if_pos h1, if_neg (show ¬K2 < q1 by omega), if_neg (show ¬K3 < q1 by omega)]
    nlinarith [hd]
  have hj2 : qDifference B (p * q2) = u + v := by
    dsimp only [B]
    simp only [qDifference_add, qDifference_smul,
      qDifference_sieveVector_semiprime p q2 K1 hp hq2 hpK1 hpq2,
      qDifference_sieveVector_semiprime p q2 K2 hp hq2 hpK2 hpq2,
      qDifference_sieveVector_semiprime p q2 K3 hp hq2 hpK3 hpq2,
      if_pos (show K1 < q2 by omega), if_pos h2, if_neg (show ¬K3 < q2 by omega)]
    nlinarith [hd]
  have hu := qDifference_abs_le B (p * q1)
  have hv := qDifference_abs_le B (p * q2)
  rw [hj1, Nat.cast_mul] at hu
  rw [hj2, Nat.cast_mul] at hv
  have hb := prefix_probe_bound u v w x y z _ _ hm hyx hzy hu hv
  convert hb using 1; ring

/-- Specialization to the decreasing positive actual Euler probes. -/
theorem threeStage_euler_energy_bound (p K1 K2 K3 q1 q2 : ℕ)
    (hp : p.Prime) (hq1 : q1.Prime) (hq2 : q2.Prime)
    (hpK1 : p ≤ K1) (h1 : K1 < q1) (h12 : q1 ≤ K2)
    (h2 : K2 < q2) (h23 : q2 ≤ K3)
    (hq1short : q1 ≤ 2 * K1) (hq2short : q2 ≤ 2 * K2)
    (u v w σ : ℝ) (hσ : 0 < σ) (hm : u + v + w = 1)
    (hd : u * sieveSlope (primorial K1) p + v * sieveSlope (primorial K2) p +
      w * sieveSlope (primorial K3) p = 0) :
    |u * primePowerEulerFactor p K1 σ + v * primePowerEulerFactor p K2 σ +
        w * primePowerEulerFactor p K3 σ - primePowerEulerFactor p K3 σ| ≤
      4 * Real.sqrt zetaTwo * (p : ℝ) *
      ‖u • sieveVector (primorial K1) p + v • sieveVector (primorial K2) p +
        w • sieveVector (primorial K3) p‖ *
      ((K1 : ℝ) * primePowerEulerFactor p K1 σ +
        (K2 : ℝ) * primePowerEulerFactor p K2 σ) := by
  have he1 := (primePowerEulerFactor_pos p K1 hp.pos σ hσ).le
  have he2 := (primePowerEulerFactor_pos p K2 hp.pos σ hσ).le
  have he3 := (primePowerEulerFactor_pos p K3 hp.pos σ hσ).le
  have hmono1 := primePowerEulerFactor_le_of_le p K1 K2 hp hpK1 (by omega) σ hσ
  have hmono2 := primePowerEulerFactor_le_of_le p K2 K3 hp (by omega) (by omega) σ hσ
  have hb := threeStage_probe_energy_bound p K1 K2 K3 q1 q2 hp hq1 hq2
    hpK1 h1 h12 h2 h23 u v w _ _ _ hm hd hmono1 hmono2
  have hq1R : (q1 : ℝ) ≤ 2 * (K1 : ℝ) := by exact_mod_cast hq1short
  have hq2R : (q2 : ℝ) ≤ 2 * (K2 : ℝ) := by exact_mod_cast hq2short
  have hb1 : (q1 : ℝ) * (primePowerEulerFactor p K1 σ - primePowerEulerFactor p K2 σ) ≤
      2 * (K1 : ℝ) * primePowerEulerFactor p K1 σ := by
    have hmul := mul_le_mul_of_nonneg_right hq1R he1
    have hsub := mul_nonneg (Nat.cast_nonneg q1 : (0 : ℝ) ≤ q1) he2
    nlinarith
  have hb2 : (q2 : ℝ) * (primePowerEulerFactor p K2 σ - primePowerEulerFactor p K3 σ) ≤
      2 * (K2 : ℝ) * primePowerEulerFactor p K2 σ := by
    have hmul := mul_le_mul_of_nonneg_right hq2R he2
    have hsub := mul_nonneg (Nat.cast_nonneg q2 : (0 : ℝ) ≤ q2) he3
    nlinarith
  have hsum := add_le_add hb1 hb2
  have hc : 0 ≤ 2 * Real.sqrt zetaTwo * (p : ℝ) *
      ‖u • sieveVector (primorial K1) p + v • sieveVector (primorial K2) p +
        w • sieveVector (primorial K3) p‖ := by positivity
  have hmultiply := mul_le_mul_of_nonneg_left hsum hc
  nlinarith [hb, hmultiply]

/-- A nonzero fixed Euler signature forces complete norm divergence. The prime
witnesses lie between successive cutoffs and within twice the earlier cutoff.
There is no sign, variation, determinant-gap, or energy assumption. -/
theorem threeStage_signature_norm_tendsto_atTop
    (p : ℕ) (hp : p.Prime) (σ T : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) (hT : T ≠ 0)
    (K1 K2 K3 q1 q2 : ℕ → ℕ) (u v w : ℕ → ℝ)
    (hK1 : Tendsto K1 atTop atTop)
    (hcut : ∀ j, p ≤ K1 j)
    (hq1 : ∀ j, (q1 j).Prime) (hq2 : ∀ j, (q2 j).Prime)
    (h1 : ∀ j, K1 j < q1 j) (h12 : ∀ j, q1 j ≤ K2 j)
    (h2 : ∀ j, K2 j < q2 j) (h23 : ∀ j, q2 j ≤ K3 j)
    (hshort1 : ∀ j, q1 j ≤ 2 * K1 j) (hshort2 : ∀ j, q2 j ≤ 2 * K2 j)
    (hm : ∀ j, u j + v j + w j = 1)
    (hd : ∀ j, u j * sieveSlope (primorial (K1 j)) p +
      v j * sieveSlope (primorial (K2 j)) p + w j * sieveSlope (primorial (K3 j)) p = 0)
    (he : ∀ j, u j * primePowerEulerFactor p (K1 j) σ +
      v j * primePowerEulerFactor p (K2 j) σ + w j * primePowerEulerFactor p (K3 j) σ = T) :
    Tendsto (fun j => ‖threeStageVector p (K1 j) (K2 j) (K3 j) (u j) (v j) (w j)‖)
      atTop atTop := by
  have hK2 : Tendsto K2 atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hK1.eventually (eventually_ge_atTop b)] with j hj
    exact hj.trans ((h1 j).le.trans (h12 j))
  have hK3 : Tendsto K3 atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [hK2.eventually (eventually_ge_atTop b)] with j hj
    exact hj.trans ((h2 j).le.trans (h23 j))
  have hz : Tendsto (fun j => primePowerEulerFactor p (K3 j) σ) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul, Function.comp_def] using
      (primePowerEulerFactor_any_power_tendsto_zero p hp σ 0 hσ hσ1).comp hK3
  have hE1 : Tendsto (fun j => (K1 j : ℝ) * primePowerEulerFactor p (K1 j) σ)
      atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (primePowerEulerFactor_any_power_tendsto_zero p hp σ 1 hσ hσ1).comp hK1
  have hE2 : Tendsto (fun j => (K2 j : ℝ) * primePowerEulerFactor p (K2 j) σ)
      atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (primePowerEulerFactor_any_power_tendsto_zero p hp σ 1 hσ hσ1).comp hK2
  let d := fun j => 4 * Real.sqrt zetaTwo * (p : ℝ) *
    ((K1 j : ℝ) * primePowerEulerFactor p (K1 j) σ +
      (K2 j : ℝ) * primePowerEulerFactor p (K2 j) σ)
  have hd0 : Tendsto d atTop (𝓝 0) := by
    simpa only [zero_add, mul_zero] using
      (hE1.add hE2).const_mul (4 * Real.sqrt zetaTwo * (p : ℝ))
  apply RiemannResearch.Analysis.tendsto_atTop_of_vanishing_probe_cost
    _ _ d T hT hz hd0
  · exact Filter.Eventually.of_forall (fun j => norm_nonneg _)
  · apply Filter.Eventually.of_forall
    intro j
    have hpos1 := (primePowerEulerFactor_pos p (K1 j) hp.pos σ hσ).le
    have hpos2 := (primePowerEulerFactor_pos p (K2 j) hp.pos σ hσ).le
    dsimp only [d]
    positivity
  · apply Filter.Eventually.of_forall
    intro j
    have hb := threeStage_euler_energy_bound p (K1 j) (K2 j) (K3 j) (q1 j) (q2 j)
      hp (hq1 j) (hq2 j) (hcut j) (h1 j) (h12 j) (h2 j) (h23 j)
      (hshort1 j) (hshort2 j) (u j) (v j) (w j) σ hσ (hm j) (hd j)
    rw [he j] at hb
    dsimp only [d, threeStageVector]
    convert hb using 1; ring

/-- For strictly increasing effective prime cutoffs, all short-prime providers
are discharged by Bertrand. This rules out both alternating sign patterns. -/
theorem threeStage_prime_cutoffs_norm_tendsto_atTop
    (p : ℕ) (hp : p.Prime) (σ T : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) (hT : T ≠ 0)
    (K1 K2 K3 : ℕ → ℕ) (u v w : ℕ → ℝ)
    (hK1 : Tendsto K1 atTop atTop) (hcut : ∀ j, p ≤ K1 j)
    (hprime2 : ∀ j, (K2 j).Prime) (hprime3 : ∀ j, (K3 j).Prime)
    (h12 : ∀ j, K1 j < K2 j) (h23 : ∀ j, K2 j < K3 j)
    (hm : ∀ j, u j + v j + w j = 1)
    (hd : ∀ j, u j * sieveSlope (primorial (K1 j)) p +
      v j * sieveSlope (primorial (K2 j)) p + w j * sieveSlope (primorial (K3 j)) p = 0)
    (he : ∀ j, u j * primePowerEulerFactor p (K1 j) σ +
      v j * primePowerEulerFactor p (K2 j) σ + w j * primePowerEulerFactor p (K3 j) σ = T) :
    Tendsto (fun j => ‖threeStageVector p (K1 j) (K2 j) (K3 j) (u j) (v j) (w j)‖)
      atTop atTop := by
  have hex1 (j : ℕ) := exists_short_prime_before_prime (K1 j) (K2 j)
    (ne_of_gt (hp.pos.trans_le (hcut j))) (hprime2 j) (h12 j)
  have hex2 (j : ℕ) := exists_short_prime_before_prime (K2 j) (K3 j)
    (hprime2 j).ne_zero (hprime3 j) (h23 j)
  choose q1 hq1 h1 hq12 hshort1 using hex1
  choose q2 hq2 h2 hq23 hshort2 using hex2
  exact threeStage_signature_norm_tendsto_atTop p hp σ T hσ hσ1 hT
    K1 K2 K3 q1 q2 u v w hK1 hcut hq1 hq2 h1 hq12 h2 hq23 hshort1 hshort2 hm hd he

end RiemannResearch.RH.QPrimePowerSieve
