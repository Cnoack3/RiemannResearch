/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ArithmeticFloorHilbertSeries
import RiemannResearch.RH.BurnolFiniteEnergyReduction
import Mathlib.Analysis.PSeries
import RiemannResearch.Analysis.PSeriesTail

/-!
# Unconditional finite energy for damped Mobius floor prefixes

Source: J.-F. Burnol, "On an analytic estimate in the theory of the Riemann
zeta function and a theorem of Baez-Duarte", Acta Cientifica Venezolana
54 (2003), 210-215; author manuscript https://arxiv.org/abs/math/0202166,
Section 4, the absolute-convergence part of Lemma 4.1.
The published lemma includes epsilon = 1/2. This file proves only the
strict range epsilon > 1/2, specializes the general real-weight Hilbert
series construction, and identifies the unique admissible centering.
The endpoint and finite energy for positive damping tending to zero are
not consequences of the absolute-convergence argument.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- The elementary signed-coefficient majorant; cancellation is not used. -/
theorem dampedMobius_half_weight_le (ε : ℝ) (m : ℕ) :
    |dampedMobiusWeight ε (m + 1)| / ((m + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) ^ (-ε - 1 / 2) := by
  have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hmu : |(ArithmeticFunction.moebius (m + 1) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m + 1))
  rw [dampedMobiusWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg hm.le _)]
  calc
    _ ≤ (1 * ((m + 1 : ℕ) : ℝ) ^ (-ε)) / ((m + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmu
        (Real.rpow_nonneg hm.le _)) (Real.rpow_nonneg hm.le _)
    _ = _ := by rw [one_mul, ← Real.rpow_sub hm]

theorem dampedMobius_half_weight_summable {ε : ℝ} (hε : (1 / 2 : ℝ) < ε) :
    Summable (fun m : ℕ =>
      |dampedMobiusWeight ε (m + 1)| / ((m + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) := by
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-ε - 1 / 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  exact Summable.of_nonneg_of_le (fun m => by positivity)
    (dampedMobius_half_weight_le ε) ((summable_nat_add_iff 1).mpr hp)

/-- The centering of an actual finite-energy vector is forced by the pole at one. -/
theorem centered_dampedMobius_normalization
    {ε : ℝ} (hε : 0 < ε) (C : ℝ)
    (henergy : Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) * C) ^ 2)) :
    (C : ℂ) * riemannZeta (1 + (ε : ℂ)) = 1 := by
  let g : ℕ → ℝ := fun n => dampedMobiusPrefix ε n - (n : ℝ) * C
  let f : ThresholdHilbert := sequenceHilbert g henergy
  have hcoord : ∀ n, hilbertSequence f n = g n := by
    intro n
    apply congrFun (hilbertSequence_sequenceHilbert g henergy ?_) n
    simp [g, dampedMobiusPrefix, arithmeticFloorPrefix]
  apply Burnol.normalization_of_mellin_identity ε hε (C : ℂ)
    (paretoMellin f) (paretoMellin_analyticOnNhd f)
  have he : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [he] with s hs
  exact centered_dampedMobius_mellin_cross_identity f hε.le C hcoord s hs


/-- The actual centered prefix has finite energy unconditionally in the
strict absolute-convergence range. -/
theorem centered_dampedMobius_square_summable_of_half_lt
    {ε : ℝ} (hε : (1 / 2 : ℝ) < ε) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * arithmeticFloorDensity (dampedMobiusWeight ε)) ^ 2) := by
  have h := hilbertSequence_square_summable
    (arithmeticFloorHilbert (dampedMobiusWeight ε))
  simpa only [arithmeticFloorHilbert_sequence _
    (dampedMobius_half_weight_summable hε), dampedMobiusPrefix] using h

/-- Exact characterization of every finite-energy centering. In particular
the right-hand side supplies an unconditional canonical provider. -/
theorem centered_dampedMobius_square_summable_iff
    {ε : ℝ} (hε : (1 / 2 : ℝ) < ε) (C : ℝ) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) * C) ^ 2) ↔
    C = (1 / riemannZeta (1 + (ε : ℂ))).re := by
  have hpos : 0 < ε := by linarith
  have hz : riemannZeta (1 + (ε : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by
      simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      linarith)
  have hcanonical :
      arithmeticFloorDensity (dampedMobiusWeight ε) =
        (1 / riemannZeta (1 + (ε : ℂ))).re := by
    have h := centered_dampedMobius_normalization hpos _
      (centered_dampedMobius_square_summable_of_half_lt hε)
    have hc := (eq_div_iff hz).mpr h
    exact congrArg Complex.re hc
  constructor
  · intro henergy
    exact (square_summable_centering_unique (dampedMobiusPrefix ε) henergy
      (centered_dampedMobius_square_summable_of_half_lt hε)).trans hcanonical
  · intro hC
    have heq : C = arithmeticFloorDensity (dampedMobiusWeight ε) :=
      hC.trans hcanonical.symm
    simpa only [heq] using centered_dampedMobius_square_summable_of_half_lt hε

/-- Concrete Hilbert realization and a complete infinite norm bound, using
the canonical reciprocal-zeta center. No RH or PNT assumption occurs. -/
theorem dampedMobius_finiteEnergy_with_bound
    {ε : ℝ} (hε : (1 / 2 : ℝ) < ε) :
    ∃ f : ThresholdHilbert,
      (∀ n : ℕ, hilbertSequence f n = dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ∧
      ‖f‖ ≤ Real.sqrt 2 *
        ∑' m : ℕ, |dampedMobiusWeight ε (m + 1)| /
          ((m + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
  have hw := dampedMobius_half_weight_summable hε
  have hcenter := (centered_dampedMobius_square_summable_iff hε
    (arithmeticFloorDensity (dampedMobiusWeight ε))).mp
    (centered_dampedMobius_square_summable_of_half_lt hε)
  refine ⟨arithmeticFloorHilbert (dampedMobiusWeight ε), ?_,
    arithmeticFloorHilbert_norm_le _ hw⟩
  intro n
  simpa only [dampedMobiusPrefix, hcenter] using
    arithmeticFloorHilbert_sequence (dampedMobiusWeight ε) hw n


/-- Explicit truncation rate for the complete signed Hilbert series.
This is the integral-test quantitative refinement of the strict-range
absolute-convergence proof in Burnol's Lemma 4.1. -/
theorem dampedMobius_finiteEnergy_tail_bound {ε : ℝ}
    (hε : (1 / 2 : ℝ) < ε) {N : ℕ} (hN : 1 ≤ N) :
    ‖arithmeticFloorHilbert (dampedMobiusWeight ε) -
        arithmeticFloorHilbertPartial (dampedMobiusWeight ε) N‖ ≤
      Real.sqrt 2 * (N : ℝ) ^ (1 / 2 - ε) / (ε - 1 / 2) := by
  have hw := dampedMobius_half_weight_summable hε
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ (-ε - 1 / 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hp' := (summable_nat_add_iff 1).mpr hp
  have hs : (∑' j : ℕ, |dampedMobiusWeight ε (j + N + 1)| /
      ((j + N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) ≤
      ∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) ^ (-ε - 1 / 2) :=
    ((summable_nat_add_iff N).mpr hw).tsum_le_tsum
      (fun j => dampedMobius_half_weight_le ε (j + N))
      ((summable_nat_add_iff N).mpr hp')
  have ht : (∑' j : ℕ, ((j + N + 1 : ℕ) : ℝ) ^ (-ε - 1 / 2)) ≤
      (N : ℝ) ^ (1 / 2 - ε) / (ε - 1 / 2) := by
    have h := Real.tsum_nat_rpow_tail_le (p := ε + 1 / 2) (by linarith) hN
    simpa only [show -(ε + 1 / 2) = -ε - 1 / 2 by ring,
      show 1 - (ε + 1 / 2) = 1 / 2 - ε by ring,
      show ε + 1 / 2 - 1 = ε - 1 / 2 by ring] using h
  calc
    _ ≤ Real.sqrt 2 * ∑' j : ℕ,
        |dampedMobiusWeight ε (j + N + 1)| /
          ((j + N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
      arithmeticFloorHilbert_partial_error_le _ hw N
    _ ≤ Real.sqrt 2 * ((N : ℝ) ^ (1 / 2 - ε) / (ε - 1 / 2)) :=
      mul_le_mul_of_nonneg_left (hs.trans ht) (Real.sqrt_nonneg _)
    _ = _ := by ring

end RiemannResearch.RH.Pareto
