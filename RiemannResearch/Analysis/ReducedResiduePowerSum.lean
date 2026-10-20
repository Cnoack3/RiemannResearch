/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.NumberTheory.DivisorIncidence
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Fixed-modulus reduced-residue power-sum asymptotics

Source: user-provided TwoStageSieveObstructionResearch20261020.md, Section 4,
for the target limit. The proof uses a power-sum integral squeeze and exact
finite Mobius inversion. The modulus is fixed; no uniformity in a moving
modulus or prime asymptotic input is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ReducedResiduePowerSum

def powerSum (σ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ (-σ)

theorem powerSum_succ_bounds (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) (n : ℕ) :
    (((n + 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) ≤ powerSum σ (n + 1) ∧
    powerSum σ (n + 1) ≤ 1 + (((n + 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Set.Icc 1 (1 + (n : ℝ))) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hlo := hanti.integral_le_sum
  have hhi := hanti.sum_le_integral
  have hint : (∫ x : ℝ in (1 : ℝ)..1 + n, x ^ (-σ)) =
      (((n + 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
    rw [integral_rpow (Or.inl (by linarith : -1 < -σ))]
    rw [show -σ + 1 = 1 - σ by ring]
    simp only [Real.one_rpow, Nat.cast_add, Nat.cast_one, add_comm]
  rw [hint] at hlo hhi
  have hlo' : (((n + 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) ≤ powerSum σ n := by
    simpa [powerSum, Nat.cast_add, Nat.cast_one, add_comm] using hlo
  have hhi' : powerSum σ (n + 1) ≤
      1 + (((n + 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ) := by
    unfold powerSum
    rw [Finset.sum_range_succ']
    convert add_le_add_left hhi 1 using 1 <;>
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
  refine ⟨hlo'.trans ?_, hhi'⟩
  simp only [powerSum]
  rw [Finset.sum_range_succ]
  exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)

theorem powerSum_normalized_tendsto (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (σ - 1) * powerSum σ N)
      atTop (𝓝 (1 / (1 - σ))) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  have hw : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (σ - 1)) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop (show 0 < 1 - σ by linarith)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    simpa only [neg_sub, Function.comp_def] using ht
  have hlo : Tendsto (fun n : ℕ =>
      (1 - ((n + 1 : ℕ) : ℝ) ^ (σ - 1)) / (1 - σ))
      atTop (𝓝 (1 / (1 - σ))) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hw).div_const (1 - σ)
  have hhi : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (σ - 1) +
      (1 - ((n + 1 : ℕ) : ℝ) ^ (σ - 1)) / (1 - σ))
      atTop (𝓝 (1 / (1 - σ))) := by
    simpa using hw.add hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro n
    have hb := mul_le_mul_of_nonneg_left (powerSum_succ_bounds σ hσ hσ1 n).1
      (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) (σ - 1))
    have hp : ((n + 1 : ℕ) : ℝ) ^ (σ - 1) * ((n + 1 : ℕ) : ℝ) ^ (1 - σ) = 1 := by
      rw [← Real.rpow_add (by positivity), show σ - 1 + (1 - σ) = 0 by ring,
        Real.rpow_zero]
    calc
      _ = ((n + 1 : ℕ) : ℝ) ^ (σ - 1) *
          ((((n + 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ)) := by
        rw [← mul_div_assoc, mul_sub, hp, mul_one]
      _ ≤ _ := hb
  · intro n
    have hb := mul_le_mul_of_nonneg_left (powerSum_succ_bounds σ hσ hσ1 n).2
      (Real.rpow_nonneg (Nat.cast_nonneg (n + 1)) (σ - 1))
    have hp : ((n + 1 : ℕ) : ℝ) ^ (σ - 1) * ((n + 1 : ℕ) : ℝ) ^ (1 - σ) = 1 := by
      rw [← Real.rpow_add (by positivity), show σ - 1 + (1 - σ) = 0 by ring,
        Real.rpow_zero]
    calc
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ (σ - 1) *
          (1 + ((((n + 1 : ℕ) : ℝ) ^ (1 - σ) - 1) / (1 - σ))) := hb
      _ = _ := by rw [mul_add, mul_one, ← mul_div_assoc, mul_sub, hp, mul_one]

theorem nat_div_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N / d : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 (1 / (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlo : Tendsto (fun N : ℕ => 1 / (d : ℝ) - 1 / (N : ℝ))
      atTop (𝓝 (1 / (d : ℝ))) := by
    simpa using (tendsto_const_nhds (x := 1 / (d : ℝ))).sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have he : (d : ℝ) * (N / d : ℕ) + (N % d : ℕ) = (N : ℝ) := by
      exact_mod_cast Nat.div_add_mod N d
    have hr : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt N hd
    have hb : (N : ℝ) - d ≤ (d : ℝ) * (N / d : ℕ) := by linarith
    calc
      _ = ((N : ℝ) - d) / ((N : ℝ) * d) := by
        field_simp [ne_of_gt hdR, ne_of_gt hNR]
      _ ≤ ((d : ℝ) * (N / d : ℕ)) / ((N : ℝ) * d) :=
        div_le_div_of_nonneg_right hb (by positivity)
      _ = _ := by field_simp [ne_of_gt hdR, ne_of_gt hNR]
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    apply (div_le_div_iff₀ hNR hdR).2
    norm_cast
    simpa [mul_comm] using Nat.div_mul_le_self N d

theorem multiples_power_sum (σ : ℝ) (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Finset.Icc 1 N, if d ∣ n then (n : ℝ) ^ (-σ) else 0) =
      (d : ℝ) ^ (-σ) * powerSum σ (N / d) := by
  classical
  rw [← Finset.sum_filter, powerSum]
  rw [← RiemannResearch.NumberTheory.DivisorIncidence.sum_Icc_one (N / d)
    (fun k => (k : ℝ) ^ (-σ)), Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun k _ => d * k)
  · intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
    exact (Nat.mul_le_mul_left d hkN).trans (by simpa [mul_comm] using Nat.div_mul_le_self N d)
  · intro k hk j hj heq
    exact Nat.eq_of_mul_eq_mul_left hd heq
  · intro n hn
    obtain ⟨hn, hdn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    refine ⟨n / d, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hnN⟩,
      Nat.mul_div_cancel' hdn⟩
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hd
  · intro k hk
    simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg k)]

theorem coprime_power_sum_moebius (σ : ℝ) (N L : ℕ) (hL : 0 < L) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n L), (n : ℝ) ^ (-σ)) =
      ∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ((d : ℝ) ^ (-σ) * powerSum σ (N / d)) := by
  have h := RiemannResearch.NumberTheory.DivisorIncidence.gcd_class_charge_moebius
    L (ne_of_gt hL) (Finset.Icc 1 N) (fun n => (n : ℝ) ^ (-σ))
    (fun d => (d : ℝ) ^ (-σ) * powerSum σ (N / d))
    (fun d hd => multiples_power_sum σ N d (Nat.pos_of_mem_divisors hd))
    1 (Nat.mem_divisors.mpr ⟨one_dvd _, ne_of_gt hL⟩)
  simpa only [Nat.coprime_iff_gcd_eq_one, one_dvd, if_true, Nat.div_one] using h

theorem powerSum_div_normalized_tendsto (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (σ - 1) * powerSum σ (N / d))
      atTop (𝓝 ((1 / (d : ℝ)) ^ (1 - σ) / (1 - σ))) := by
  have hratio := (nat_div_ratio_tendsto d hd).rpow_const
    (Or.inr (show 0 ≤ 1 - σ by linarith))
  have hps := (powerSum_normalized_tendsto σ hσ hσ1).comp
    (Nat.tendsto_div_const_atTop (ne_of_gt hd))
  have ht := hratio.mul hps
  simp only [mul_one_div, Function.comp_def] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop d] with N hN
  have hq : (0 : ℝ) < (N / d : ℕ) := by exact_mod_cast Nat.div_pos hN hd
  have hNR : (0 : ℝ) < N := by exact_mod_cast hd.trans_le hN
  have hp : ((N / d : ℕ) : ℝ) ^ (1 - σ) * ((N / d : ℕ) : ℝ) ^ (σ - 1) = 1 := by
    rw [← Real.rpow_add hq, show 1 - σ + (σ - 1) = 0 by ring, Real.rpow_zero]
  rw [Real.div_rpow (le_of_lt hq) (le_of_lt hNR)]
  calc
    _ = (((N / d : ℕ) : ℝ) ^ (1 - σ) * ((N / d : ℕ) : ℝ) ^ (σ - 1)) /
        (N : ℝ) ^ (1 - σ) * powerSum σ (N / d) := by ring
    _ = (N : ℝ) ^ (σ - 1) * powerSum σ (N / d) := by
      rw [hp, one_div, ← Real.rpow_neg (le_of_lt hNR), neg_sub]

theorem multiples_normalized_tendsto (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (σ - 1) *
      ((d : ℝ) ^ (-σ) * powerSum σ (N / d)))
      atTop (𝓝 (1 / ((d : ℝ) * (1 - σ)))) := by
  have ht := (powerSum_div_normalized_tendsto σ hσ hσ1 d hd).const_mul ((d : ℝ) ^ (-σ))
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have he : (d : ℝ) ^ (-σ) * ((1 / (d : ℝ)) ^ (1 - σ) / (1 - σ)) =
      1 / ((d : ℝ) * (1 - σ)) := by
    rw [one_div, Real.inv_rpow hdR.le, ← Real.rpow_neg hdR.le,
      ← mul_div_assoc, ← Real.rpow_add hdR]
    rw [show -σ + -(1 - σ) = -1 by ring, Real.rpow_neg_one]
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [he] at ht
  convert ht using 1
  funext N
  ring

theorem moebius_divisor_reciprocal_sum (L : ℕ) (hL : 0 < L) :
    (∑ d ∈ L.divisors, (ArithmeticFunction.moebius d : ℝ) / d) =
      (Nat.totient L : ℝ) / L := by
  have h := coprime_power_sum_moebius 0 L L hL
  have hps (N : ℕ) : powerSum 0 N = N := by simp [powerSum]
  simp only [neg_zero, Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    hps, one_mul] at h
  rw [RiemannResearch.NumberTheory.DivisorIncidence.coprime_Icc_card] at h
  apply (eq_div_iff (show (L : ℝ) ≠ 0 by exact_mod_cast ne_of_gt hL)).2
  rw [Finset.sum_mul, h]
  apply Finset.sum_congr rfl
  intro d hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (Nat.pos_of_mem_divisors hd)
  have hmul : (d : ℝ) * (L / d : ℕ) = L := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  rw [← hmul]
  field_simp [hdR]

/-- A fixed-modulus reduced-residue power-sum limit.
The modulus is fixed before N tends to infinity. -/
theorem reduced_residue_power_sum_tendsto (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ < 1)
    (L : ℕ) (hL : 0 < L) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (σ - 1) *
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n L), (n : ℝ) ^ (-σ)))
      atTop (𝓝 (((Nat.totient L : ℝ) / L) / (1 - σ))) := by
  have ht := tendsto_finsetSum L.divisors (fun d hd =>
    (multiples_normalized_tendsto σ hσ hσ1 d (Nat.pos_of_mem_divisors hd)).const_mul
      (ArithmeticFunction.moebius d : ℝ))
  have he : (∑ d ∈ L.divisors,
      (ArithmeticFunction.moebius d : ℝ) * (1 / ((d : ℝ) * (1 - σ)))) =
      ((Nat.totient L : ℝ) / L) / (1 - σ) := by
    rw [← moebius_divisor_reciprocal_sum L hL, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    ring
  rw [he] at ht
  convert ht using 1
  funext N
  rw [coprime_power_sum_moebius σ N L hL, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end RiemannResearch.Analysis.ReducedResiduePowerSum
