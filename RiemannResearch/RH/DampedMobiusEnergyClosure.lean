/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.DampedMobiusSeed
import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Closure of finite-energy damped Möbius prefixes

This is the discrete Fatou step in the endpoint argument of J.-F. Burnol,
"On an analytic estimate in the theory of the Riemann zeta function and a
theorem of Báez-Duarte", Acta Cientifica Venezolana 54 (2003), 210–215,
Lemma 4.1 (author manuscript https://arxiv.org/abs/math/0202166).
The quantitative bound remains an explicit premise: finite energy for each
strictly larger damping parameter does not by itself supply this bound.
The transfer needs only eventual bounds for each fixed finite head.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

theorem continuous_dampedMobiusWeight (n : ℕ) :
    Continuous (fun ε : ℝ => dampedMobiusWeight ε n) := by
  by_cases hn : n = 0
  · simpa only [hn, dampedMobiusWeight_zero] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  · exact continuous_const.mul
      ((Real.continuous_const_rpow (Nat.cast_ne_zero.mpr hn)).comp continuous_neg)

theorem continuous_dampedMobiusPrefix (n : ℕ) :
    Continuous (fun ε : ℝ => dampedMobiusPrefix ε n) := by
  unfold dampedMobiusPrefix arithmeticFloorPrefix
  exact continuous_finsetSum _ (fun d _ => (continuous_dampedMobiusWeight d).mul_const _)

/-- A finite-head Fatou argument; no majorant or norm-convergent subsequence is needed. -/
theorem pareto_square_summable_of_coordinate_limit
    (F : ℕ → ℕ → ℝ) (g : ℕ → ℝ) (B : ℝ)
    (hlim : ∀ n, Tendsto (fun j => F j n) atTop (𝓝 (g n)))
    (hhead : ∀ N, ∀ᶠ j : ℕ in atTop,
      (∑ n ∈ Finset.range N, positiveWeight n * F j n ^ 2) ≤ B) :
    Summable (fun n => positiveWeight n * g n ^ 2) ∧
      (∑' n, positiveWeight n * g n ^ 2) ≤ B := by
  have hb (N : ℕ) : (∑ n ∈ Finset.range N, positiveWeight n * g n ^ 2) ≤ B := by
    apply le_of_tendsto
      (tendsto_finsetSum (Finset.range N) (fun n _ =>
        ((hlim n).pow 2).const_mul (positiveWeight n)))
    exact hhead N
  have hn (n : ℕ) : 0 ≤ positiveWeight n * g n ^ 2 :=
    mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩

/-- The canonical reciprocal-zeta center is continuous at every positive damping. -/
theorem dampedMobius_center_tendsto
    (ε : ℕ → ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hε : Tendsto ε atTop (𝓝 ε₀)) :
    Tendsto (fun j => (1 / riemannZeta (1 + (ε j : ℂ))).re)
      atTop (𝓝 ((1 / riemannZeta (1 + (ε₀ : ℂ))).re)) := by
  have hs : 1 + (ε₀ : ℂ) ≠ 1 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at h'
    linarith
  have hz : riemannZeta (1 + (ε₀ : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by
      simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      linarith)
  have harg : Tendsto (fun j => (1 : ℂ) + (ε j : ℂ))
      atTop (𝓝 (1 + (ε₀ : ℂ))) :=
    tendsto_const_nhds.add (Complex.continuous_ofReal.continuousAt.tendsto.comp hε)
  have hζ := (differentiableAt_riemannZeta hs).continuousAt.tendsto.comp harg
  exact Complex.continuous_re.continuousAt.tendsto.comp (tendsto_const_nhds.div hζ hz)

/-- Actual arithmetic endpoint energy from a single uniform bound on each finite head.
The bound may start at a different damping index for each head length. -/
theorem centered_dampedMobius_energy_of_finite_head_bound
    (ε : ℕ → ℝ) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hε : Tendsto ε atTop (𝓝 ε₀)) (B : ℝ)
    (hhead : ∀ N, ∀ᶠ j : ℕ in atTop,
      (∑ n ∈ Finset.range N, positiveWeight n *
        (dampedMobiusPrefix (ε j) n -
          (n : ℝ) * (1 / riemannZeta (1 + (ε j : ℂ))).re) ^ 2) ≤ B) :
    Summable (fun n => positiveWeight n *
      (dampedMobiusPrefix ε₀ n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε₀ : ℂ))).re) ^ 2) ∧
      (∑' n, positiveWeight n *
        (dampedMobiusPrefix ε₀ n -
          (n : ℝ) * (1 / riemannZeta (1 + (ε₀ : ℂ))).re) ^ 2) ≤ B := by
  apply pareto_square_summable_of_coordinate_limit _ _ B _ hhead
  intro n
  exact ((continuous_dampedMobiusPrefix n).continuousAt.tendsto.comp hε).sub
    ((dampedMobius_center_tendsto ε hε₀ hε).const_mul (n : ℝ))

/-- Uniform Hilbert energy along any damping sequence approaching one half supplies
the actual Burnol endpoint. The arithmetic bound is the sole extra premise. -/
theorem centered_dampedMobius_half_of_bounded_energy
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 (1 / 2 : ℝ)))
    (f : ℕ → ThresholdHilbert)
    (hcoord : ∀ j n, hilbertSequence (f j) n = dampedMobiusPrefix (ε j) n -
      (n : ℝ) * (1 / riemannZeta (1 + (ε j : ℂ))).re)
    (B : ℝ) (hB : ∀ᶠ j : ℕ in atTop, ‖f j‖ ^ 2 ≤ B) :
    Summable (fun n => positiveWeight n *
      (dampedMobiusPrefix (1 / 2) n -
        (n : ℝ) * (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ^ 2) ∧
      (∑' n, positiveWeight n *
        (dampedMobiusPrefix (1 / 2) n -
          (n : ℝ) * (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ^ 2) ≤ B := by
  apply centered_dampedMobius_energy_of_finite_head_bound ε (by norm_num) hε B
  intro N
  filter_upwards [hB] with j hj
  simp_rw [← hcoord j]
  apply le_trans (Summable.sum_le_tsum (Finset.range N)
    (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _))
    (hilbertSequence_square_summable (f j)))
  simpa only [← hilbert_norm_weighted_sq] using hj

end RiemannResearch.RH.Pareto
