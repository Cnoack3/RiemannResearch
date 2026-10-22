/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensShiftedGlobal
import RiemannResearch.Analysis.WeightedMertensTail
import RiemannResearch.RH.HyperbolaLogCutoff
import RiemannResearch.RH.ParetoLogEnergyCriterion
import RiemannResearch.RH.DampedMobiusFiniteEnergy

/-!
# The unconditional half-damping endpoint

Statement source: J.-F. Burnol, "On an analytic estimate in the theory of
the Riemann zeta function and a theorem of Báez-Duarte", Acta Cientifica
Venezolana 54 (2003), 210–215, Lemma 4.1;
author manuscript https://arxiv.org/abs/math/0202166.

This proof uses the repository's quantitative PNT, a logarithmic Mertens
bootstrap, exact Abel identities, and the signed Dirichlet hyperbola
decomposition. It supplies the actual arithmetic endpoint and an eventual
square-root discrepancy bound with logarithmic saving 3/4. No RH hypothesis
or unproved estimate occurs. Finiteness for damping tending to zero remains
a separate obligation.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators


namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
open RiemannResearch.NumberTheory.PrimeNumberTheorem

private theorem arithmeticSummatory_moebius (x : ℝ) :
    arithmeticSummatory (fun n => (ArithmeticFunction.moebius n : ℝ)) x = M x := by
  unfold arithmeticSummatory M
  apply Finset.sum_congr
  · ext n
    simp
  · intro n hn
    rfl

private theorem icc_zero_eq_range_succ (N : ℕ) :
    Finset.Icc 0 N = Finset.range (N + 1) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_range, Nat.zero_le, true_and]
  omega

private theorem halfWeightedPrefix_moebius (N : ℕ) :
    halfWeightedPrefix (fun n => (ArithmeticFunction.moebius n : ℝ)) (N : ℝ) =
      positiveArithmeticPrefix (dampedMobiusWeight (1 / 2)) N := by
  unfold halfWeightedPrefix
  rw [Nat.floor_natCast, icc_zero_eq_range_succ, Finset.sum_range_succ']
  norm_num [positiveArithmeticPrefix, dampedMobiusWeight]

private theorem half_density_term (n : ℕ) :
    dampedMobiusWeight (1 / 2) n / (n : ℝ) =
      (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ) := by
  rw [dampedMobiusWeight_div]
  norm_num only [show (1 + (1 / 2 : ℝ)) = 3 / 2 by norm_num]
  rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

private theorem threeHalfWeightedPrefix_moebius (N : ℕ) :
    threeHalfWeightedPrefix (fun n => (ArithmeticFunction.moebius n : ℝ)) (N : ℝ) =
      ∑ n ∈ Finset.range (N + 1), dampedMobiusWeight (1 / 2) n / (n : ℝ) := by
  unfold threeHalfWeightedPrefix
  rw [Nat.floor_natCast, icc_zero_eq_range_succ]
  simp_rw [half_density_term]

private theorem moebius_threeHalf_summable :
    Summable (fun n : ℕ =>
      (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply hs.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  apply mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- The elementary coefficient bound at half damping. -/
theorem dampedMobius_half_weight_bound (d : ℕ) (hd : 0 < d) :
    |dampedMobiusWeight (1 / 2) d| ≤ 1 / Real.sqrt (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
  rw [dampedMobiusWeight, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hd0.le _)]
  calc
    _ ≤ 1 * (d : ℝ) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hmu (Real.rpow_nonneg hd0.le _)
    _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_neg hd0.le]; simp

/-- Unconditional signed summatory cancellation for the half-damped
coefficients, with the logarithmic saving needed uniformly in truncations. -/
theorem dampedMobius_half_prefix_log_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℕ, 0 < t →
      |positiveArithmeticPrefix (dampedMobiusWeight (1 / 2)) t| ≤
        B * Real.sqrt (t : ℝ) / (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ) := by
  obtain ⟨B, hB, hM⟩ := M_shiftedLog_threeHalves_bound
  have hMu : ∀ x : ℝ, 1 ≤ x →
      |arithmeticSummatory (fun n => (ArithmeticFunction.moebius n : ℝ)) x| ≤
        B * x * shiftedLogProfile x := by
    simpa only [arithmeticSummatory_moebius, shiftedLogProfile] using hM
  refine ⟨3 * B, by positivity, ?_⟩
  intro t ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have h := halfWeightedPrefix_bound
    (fun n => (ArithmeticFunction.moebius n : ℝ)) (by simp) hB ht1 hMu
  rw [halfWeightedPrefix_moebius, halfLogPrimitive_eq_sqrt_div ht1] at h
  simpa only [mul_div_assoc] using h

/-- Quantitative endpoint cancellation with the absolutely convergent density
series as center. All prime-error and Mertens premises are discharged. -/
private theorem dampedMobius_half_density_log_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 0 < N → 200 ≤ Real.log (N : ℝ) →
      |dampedMobiusPrefix (1 / 2) N - (N : ℝ) *
        (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) *
          (n : ℝ) ^ (-3 / 2 : ℝ))| ≤
        K * Real.sqrt (N : ℝ) / (6 + Real.log (N : ℝ)) ^ (3 / 4 : ℝ) := by
  obtain ⟨B, hB, hM⟩ := M_shiftedLog_threeHalves_bound
  have hMu : ∀ x : ℝ, 1 ≤ x →
      |arithmeticSummatory (fun n => (ArithmeticFunction.moebius n : ℝ)) x| ≤
        B * x * shiftedLogProfile x := by
    simpa only [arithmeticSummatory_moebius, shiftedLogProfile] using hM
  have hc : (ArithmeticFunction.moebius 0 : ℝ) = 0 := by simp
  have hP (t : ℕ) (ht : 0 < t) :
      |positiveArithmeticPrefix (dampedMobiusWeight (1 / 2)) t| ≤
        (3 * B) * Real.sqrt (t : ℝ) /
          (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ) := by
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hL := shiftedLog_pos ht1
    have h := halfWeightedPrefix_bound
      (fun n => (ArithmeticFunction.moebius n : ℝ)) hc hB ht1 hMu
    rw [halfWeightedPrefix_moebius, halfLogPrimitive, shiftedLogProfile,
      ← Real.sqrt_eq_rpow,
      show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring,
      Real.rpow_neg hL.le] at h
    simpa only [div_eq_mul_inv, mul_assoc] using h
  have hT (t : ℕ) (ht : 0 < t) :
      |(∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) *
          (n : ℝ) ^ (-3 / 2 : ℝ)) -
        ∑ d ∈ Finset.range (t + 1), dampedMobiusWeight (1 / 2) d / (d : ℝ)| ≤
        (5 * B) / (Real.sqrt (t : ℝ) *
          (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ)) := by
    have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
    have hL := shiftedLog_pos ht1
    have h := threeHalfWeightedPrefix_tail_bound
      (fun n => (ArithmeticFunction.moebius n : ℝ)) hc hB hMu
      moebius_threeHalf_summable (y := t) ht
    rw [threeHalfWeightedPrefix_moebius] at h
    have he : (t : ℝ) ^ (-1 / 2 : ℝ) * shiftedLogProfile (t : ℝ) =
        1 / (Real.sqrt (t : ℝ) * (6 + Real.log (t : ℝ)) ^ (3 / 2 : ℝ)) := by
      unfold shiftedLogProfile
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
        show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring,
        Real.rpow_neg ht0.le, Real.rpow_neg hL.le, ← Real.sqrt_eq_rpow]
      simp only [one_div, mul_inv_rev, mul_comm]
    calc
      _ ≤ 5 * B * (t : ℝ) ^ (-1 / 2 : ℝ) * shiftedLogProfile (t : ℝ) := h
      _ = _ := by rw [mul_assoc, he]; ring
  refine ⟨2 + 112 * B, by positivity, ?_⟩
  intro N hN hlarge
  have h := arithmeticFloorPrefix_endpoint_log_bound
    (dampedMobiusWeight (1 / 2)) (dampedMobiusWeight_zero _) _
    (W := 1) (B := 3 * B) (D := 5 * B)
    (by norm_num) (by positivity) (by positivity)
    dampedMobius_half_weight_bound hP hT hN hlarge
  change |dampedMobiusPrefix (1 / 2) N - (N : ℝ) * _| ≤ _ at h
  convert h using 1 <;> ring

/-- Burnol's unconditional half-damping endpoint, together with an explicit
eventual discrepancy shape and the uniquely forced reciprocal-zeta center. -/
theorem dampedMobius_half_endpoint :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ N : ℕ, 0 < N → 200 ≤ Real.log (N : ℝ) →
        |dampedMobiusPrefix (1 / 2) N - (N : ℝ) *
          (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re| ≤
          K * Real.sqrt (N : ℝ) / (6 + Real.log (N : ℝ)) ^ (3 / 4 : ℝ)) ∧
      Summable (fun n => positiveWeight n *
        (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
          (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ^ 2) := by
  let C : ℝ := ∑' n : ℕ,
    (ArithmeticFunction.moebius n : ℝ) * (n : ℝ) ^ (-3 / 2 : ℝ)
  obtain ⟨K, hK, hbound⟩ := dampedMobius_half_density_log_bound
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ n : ℕ in atTop,
      |dampedMobiusPrefix (1 / 2) n - (n : ℝ) * C| ≤
        K * Real.sqrt (n : ℝ) * (6 + Real.log (n : ℝ)) ^ (-(3 / 4 : ℝ)) := by
    filter_upwards [hloglim.eventually (eventually_ge_atTop (200 : ℝ)),
      eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hL : 0 < 6 + Real.log (n : ℝ) := by linarith
    rw [Real.rpow_neg hL.le, ← div_eq_mul_inv]
    exact hbound n (by omega) hn
  have henergy := centered_dampedMobius_half_energy_of_shifted_log_bound C hK
    (by norm_num : (1 / 2 : ℝ) < 3 / 4) hevent
  have hnormal := centered_dampedMobius_normalization
    (by norm_num : (0 : ℝ) < 1 / 2) C henergy
  have hz : riemannZeta (1 + ((1 / 2 : ℝ) : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by norm_num)
  have hcenter : C = (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re := by
    exact congrArg Complex.re ((eq_div_iff hz).mpr hnormal)
  refine ⟨K, hK, ?_, ?_⟩
  · simpa only [← hcenter, C] using hbound
  · simpa only [hcenter] using henergy

/-- The full unconditional range epsilon >= 1/2, now including its endpoint. -/
theorem centered_dampedMobius_square_summable_of_half_le
    {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) := by
  rcases eq_or_lt_of_le hε with heq | hlt
  · subst ε
    obtain ⟨K, hK, hb, hs⟩ := dampedMobius_half_endpoint
    exact hs
  · exact (centered_dampedMobius_square_summable_iff hlt _).mpr rfl

/-- The reciprocal-zeta center is the unique finite-energy center throughout
the full unconditional range, including epsilon = 1/2. -/
theorem centered_dampedMobius_square_summable_iff_of_half_le
    {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) (C : ℝ) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) * C) ^ 2) ↔
      C = (1 / riemannZeta (1 + (ε : ℂ))).re := by
  have hcanonical := centered_dampedMobius_square_summable_of_half_le hε
  constructor
  · intro henergy
    exact square_summable_centering_unique (dampedMobiusPrefix ε) henergy hcanonical
  · intro hC
    simpa only [hC] using hcanonical

end RiemannResearch.RH.Pareto
