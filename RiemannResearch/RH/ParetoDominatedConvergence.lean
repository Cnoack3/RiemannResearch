/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ThresholdHilbertAdjoint
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
