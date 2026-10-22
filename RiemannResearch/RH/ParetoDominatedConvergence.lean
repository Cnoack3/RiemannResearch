/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ThresholdHilbertAdjoint
import RiemannResearch.RH.ParetoLogEnergyCriterion
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith

/-!
# Dominated convergence in the full Pareto Hilbert space

Coordinate convergence becomes norm convergence under a common summable
weighted square envelope. The envelope is only needed outside a finite
set of coordinates; convergence bounds the exceptional coordinates.
The proof uses Mathlib's Tannery theorem for the complete square error.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Coordinate convergence plus one summable envelope, uniform in the
approximant and needed only at sufficiently large coordinates, gives norm
convergence in the full Pareto Hilbert space. -/
theorem pareto_tendsto_of_eventual_dominated_coordinates
    (F : ℕ → ThresholdHilbert) (f : ThresholdHilbert) (A : ℕ → ℝ)
    (hs : Summable (fun n => positiveWeight n * (A n) ^ 2))
    (hlim : ∀ n, Tendsto (fun j => hilbertSequence (F j) n) atTop
      (𝓝 (hilbertSequence f n)))
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ j, |hilbertSequence (F j) n| ≤ A n) :
    Tendsto F atTop (𝓝 f) := by
  have hfinite : ∀ n : ℕ, ∃ B : ℝ, ∀ j, |hilbertSequence (F j) n| ≤ B := by
    intro n
    have h := (hlim n).abs
    rw [← Nat.cofinite_eq_atTop] at h
    obtain ⟨B, hB⟩ := h.bddAbove_range_of_cofinite
    exact ⟨B, fun j => hB (Set.mem_range_self j)⟩
  choose C hC using hfinite
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  let b := fun n => if n < N then C n else A n
  have hb (j n) : |hilbertSequence (F j) n| ≤ b n := by
    dsimp [b]
    split_ifs with hn
    · exact hC n j
    · exact hN n (by omega) j
  have hbs : Summable (fun n => positiveWeight n * (b n) ^ 2) := by
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))]
    simp [b, not_lt_of_ge hn]
  have hsum := (hbs.add (hilbertSequence_square_summable f)).mul_left 2
  have ht : Tendsto (fun j => ∑' n, positiveWeight n *
      (hilbertSequence (F j) n - hilbertSequence f n) ^ 2) atTop (𝓝 0) := by
    have hd := tendsto_tsum_of_dominated_convergence hsum
      (g := fun _ : ℕ => (0 : ℝ))
      (fun n => by
        simpa only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
          (((hlim n).sub_const (hilbertSequence f n)).pow 2).const_mul (positiveWeight n))
      (Eventually.of_forall (fun j n => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))]
        have hbn : 0 ≤ b n := (abs_nonneg _).trans (hb j n)
        have hsq := (sq_le_sq₀ (abs_nonneg _) hbn).mpr (hb j n)
        rw [sq_abs] at hsq
        have he : (hilbertSequence (F j) n - hilbertSequence f n) ^ 2 ≤
            2 * ((b n) ^ 2 + (hilbertSequence f n) ^ 2) := by
          nlinarith [sq_nonneg (hilbertSequence (F j) n + hilbertSequence f n)]
        simpa only [mul_add, mul_assoc, mul_left_comm] using
          mul_le_mul_of_nonneg_left he (positiveWeight_nonneg n)))
    simpa only [tsum_zero] using hd
  have ht' : Tendsto (fun j => ‖F j - f‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hilbert_norm_weighted_sq, hilbertSequence_sub, Pi.sub_apply] using ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp ht'
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end RiemannResearch.RH.Pareto

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Domination constructs the limit as well as proving norm convergence.
Finite energy of the proposed limit is a conclusion, not a premise. -/
theorem pareto_exists_tendsto_of_eventual_dominated_coordinates
    (F : ℕ → ThresholdHilbert) (g A : ℕ → ℝ) (hg0 : g 0 = 0)
    (hs : Summable (fun n => positiveWeight n * (A n) ^ 2))
    (hlim : ∀ n, Tendsto (fun j => hilbertSequence (F j) n) atTop (𝓝 (g n)))
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ j, |hilbertSequence (F j) n| ≤ A n) :
    ∃ f : ThresholdHilbert, hilbertSequence f = g ∧ Tendsto F atTop (𝓝 f) := by
  have hg : Summable (fun n => positiveWeight n * (g n) ^ 2) := by
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [hbound] with n hn
    have h : |g n| ≤ A n := le_of_tendsto (hlim n).abs (Eventually.of_forall (hn ·))
    have hA : 0 ≤ A n := (abs_nonneg _).trans h
    have hsq := (sq_le_sq₀ (abs_nonneg _) hA).mpr h
    rw [sq_abs] at hsq
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg n)
  let f := sequenceHilbert g hg
  have he : hilbertSequence f = g := hilbertSequence_sequenceHilbert g hg hg0
  refine ⟨f, he, ?_⟩
  apply pareto_tendsto_of_eventual_dominated_coordinates F f A hs
  · simpa only [he] using hlim
  · exact hbound

/-- Strict sub-square-root growth gives finite Pareto energy. -/
theorem square_summable_of_eventual_rpow_bound
    {g : ℕ → ℝ} {C b : ℝ} (hb : b < 1 / 2)
    (hg : ∀ᶠ n : ℕ in atTop, |g n| ≤ C * (n : ℝ) ^ b) :
    Summable (fun n => positiveWeight n * (g n) ^ 2) := by
  have hs := (Real.summable_nat_rpow.mpr (by linarith : 2 * b - 2 < -1)).mul_left (C ^ 2)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [hg, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsquare := mul_self_le_mul_self (abs_nonneg (g n)) hn
  have hpow : ((n : ℝ) ^ b) ^ 2 = (n : ℝ) ^ (2 * b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    ring
  have hsq : (g n) ^ 2 ≤ C ^ 2 * (n : ℝ) ^ (2 * b) := by
    simpa only [← pow_two, sq_abs, mul_pow, hpow] using hsquare
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))]
  calc
    _ ≤ positiveWeight n * (C ^ 2 * (n : ℝ) ^ (2 * b)) :=
      mul_le_mul_of_nonneg_left hsq (positiveWeight_nonneg n)
    _ ≤ (1 / ((n : ℝ) ^ 2)) * (C ^ 2 * (n : ℝ) ^ (2 * b)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      unfold positiveWeight
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    _ = C ^ 2 * (n : ℝ) ^ (2 * b - 2) := by
      rw [Real.rpow_sub hn0, Real.rpow_two]
      ring

/-- Strict power envelope criterion; there is no assumed limiting energy. -/
theorem pareto_exists_tendsto_of_uniform_rpow_bound
    (F : ℕ → ThresholdHilbert) (g : ℕ → ℝ) (hg0 : g 0 = 0)
    {C b : ℝ} (hC : 0 ≤ C) (hb : b < 1 / 2)
    (hlim : ∀ n, Tendsto (fun j => hilbertSequence (F j) n) atTop (𝓝 (g n)))
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ j, |hilbertSequence (F j) n| ≤ C * (n : ℝ) ^ b) :
    ∃ f : ThresholdHilbert, hilbertSequence f = g ∧ Tendsto F atTop (𝓝 f) := by
  apply pareto_exists_tendsto_of_eventual_dominated_coordinates F g
    (fun n => C * (n : ℝ) ^ b) hg0
  · apply square_summable_of_eventual_rpow_bound hb
    exact Eventually.of_forall (fun n => by rw [abs_of_nonneg (by positivity)])
  · exact hlim
  · exact hbound

/-- The sharp logarithmic endpoint for a common physical-coordinate envelope. -/
theorem pareto_exists_tendsto_of_uniform_sqrt_log_bound
    (F : ℕ → ThresholdHilbert) (g : ℕ → ℝ) (hg0 : g 0 = 0)
    {C q : ℝ} (hC : 0 ≤ C) (hq : 1 / 2 < q)
    (hlim : ∀ n, Tendsto (fun j => hilbertSequence (F j) n) atTop (𝓝 (g n)))
    (hbound : ∀ᶠ n : ℕ in atTop, ∀ j, |hilbertSequence (F j) n| ≤
      C * Real.sqrt (n : ℝ) * (6 + Real.log (n : ℝ)) ^ (-q)) :
    ∃ f : ThresholdHilbert, hilbertSequence f = g ∧ Tendsto F atTop (𝓝 f) := by
  apply pareto_exists_tendsto_of_eventual_dominated_coordinates F g
    (fun n => C * Real.sqrt (n : ℝ) * (6 + Real.log (n : ℝ)) ^ (-q)) hg0
  · apply square_summable_of_eventual_sqrt_shifted_log_bound hC hq
    exact Eventually.of_forall (fun n => by rw [abs_of_nonneg (by positivity)])
  · exact hlim
  · exact hbound

end RiemannResearch.RH.Pareto
