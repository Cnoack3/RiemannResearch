/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MonotoneAbelConvergence
import RiemannResearch.RH.DampedMobiusSignedAbelGrowth
import RiemannResearch.RH.BurnolFixedDampingObstruction

/-!
# Zero-free strips from full signed Hilbert cutoff growth

This module isolates a stronger consequence of a bound on all finite Hilbert
cutoffs than the consequence of finite energy for just one limiting arithmetic
sequence. A full-cutoff bound persists under every additional positive power
damping. The resulting continuum of actual finite-energy vectors eliminates
the common shifted-zero loophole by discreteness of the zeros of zeta.

The exact growth hypothesis remains explicit. None of these theorems supplies
an unconditional subhalf bound. The zero-shift strategy is due to J.-F. Burnol,
arXiv:math/0202166, Section 4; the proof here assembles the repository's signed
Abel transformation, scalar coordinate limits, and isolated-zero theorem.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Exact factorization relative to any real base damping. -/
theorem dampedMobiusResidue_from_base (α ε : ℝ) (m : ℕ) :
    arithmeticResidueTerm (dampedMobiusWeight ε) m =
      ((m + 1 : ℕ) : ℝ) ^ (-(ε - α)) •
        arithmeticResidueTerm (dampedMobiusWeight α) m := by
  unfold arithmeticResidueTerm dampedMobiusWeight
  rw [smul_smul]
  congr 1
  have hp : ((m + 1 : ℕ) : ℝ) ^ (-ε) =
      ((m + 1 : ℕ) : ℝ) ^ (-α) *
        ((m + 1 : ℕ) : ℝ) ^ (-(ε - α)) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  rw [hp]
  ring

theorem dampedMobiusPartial_from_base (α ε : ℝ) (M : ℕ) :
    arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M =
      ∑ m ∈ Finset.range M, ((m + 1 : ℕ) : ℝ) ^ (-(ε - α)) •
        (-arithmeticResidueTerm (dampedMobiusWeight α) m) := by
  simp only [arithmeticFloorHilbertPartial, dampedMobiusResidue_from_base α ε,
    smul_neg, Finset.sum_neg_distrib]

/-- Signed growth at any base damping gives full natural-order convergence
after additional damping larger than the growth exponent. -/
theorem dampedMobius_cutoffs_converge_of_base_signed_growth
    {α C θ ε : ℝ} (hC : 0 ≤ C) (hαε : α < ε) (hθε : θ < ε - α)
    (hgrowth : ∀ n : ℕ,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight α) (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ) ^ θ) :
    ∃ f : ThresholdHilbert,
      Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight ε)) atTop (𝓝 f) := by
  have hg : ∀ n : ℕ, ‖signedVectorPrefix
      (fun m => -arithmeticResidueTerm (dampedMobiusWeight α) m) (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ) ^ θ := by
    intro n
    simpa only [signedVectorPrefix, Finset.sum_neg_distrib,
      arithmeticFloorHilbertPartial] using hgrowth n
  have ht := signedVector_power_damped_tendsto_of_prefix_growth
    (fun m => -arithmeticResidueTerm (dampedMobiusWeight α) m)
    hC (sub_pos.mpr hαε) hθε hg
  refine ⟨∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (-(ε - α)) -
    ((n + 2 : ℕ) : ℝ) ^ (-(ε - α))) •
      signedVectorPrefix
        (fun m => -arithmeticResidueTerm (dampedMobiusWeight α) m) (n + 1), ?_⟩
  change Tendsto (fun M => arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)
    atTop _
  simpa only [dampedMobiusPartial_from_base α ε] using ht

/-- The Hilbert limit from signed cutoff growth has the actual arithmetic
coordinates; its finite energy is a conclusion. -/
theorem dampedMobius_energy_of_base_signed_growth
    {α C θ ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε)
    (hαε : α < ε) (hθε : θ < ε - α)
    (hgrowth : ∀ n : ℕ,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight α) (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ) ^ θ) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) := by
  obtain ⟨f, hf⟩ := dampedMobius_cutoffs_converge_of_base_signed_growth hC hαε hθε hgrowth
  have hcoord : ∀ n : ℕ, hilbertSequence f n = dampedMobiusPrefix ε n -
      (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re := by
    intro n
    cases n with
    | zero => simp [dampedMobiusPrefix, arithmeticFloorPrefix]
    | succ n =>
      have hleft := ((physicalEvaluationCLM n).continuous.tendsto f).comp hf
      simp only [Function.comp_def, physicalEvaluationCLM_apply] at hleft
      exact tendsto_nhds_unique hleft (dampedMobius_partial_coordinate_tendsto hε (n + 1))
  simpa only [hcoord] using hilbertSequence_square_summable f

/-- A full signed cutoff growth exponent forces a zero-free right strip.
The conclusion is stronger than single-damping zero propagation: varying the
extra damping excludes every possible common numerator/denominator zero. -/
theorem zeta_ne_zero_of_dampedMobius_signed_growth
    {α C θ : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (hθ : 0 ≤ θ)
    (hgrowth : ∀ n : ℕ,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight α) (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ) ^ θ)
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) + α + θ < ρ.re) (hone : ρ.re < 1) :
    riemannZeta ρ ≠ 0 := by
  intro hz
  let z : ℂ := ρ - ((α + θ : ℝ) : ℂ)
  have hz1 : z ≠ 1 := by
    intro heq
    have hr := congrArg Complex.re heq
    simp only [z, Complex.sub_re, Complex.ofReal_re, Complex.one_re] at hr
    linarith
  obtain ⟨δ, hδ, hshift⟩ := Burnol.zeta_small_left_shift_ne_zero z hz1
  let t : ℝ := min δ (ρ.re - (1 / 2 + α + θ)) / 2
  have hgap : 0 < ρ.re - (1 / 2 + α + θ) := by linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by
    dsimp [t]
    have := min_le_left δ (ρ.re - (1 / 2 + α + θ))
    linarith
  have htr : t < ρ.re - (1 / 2 + α + θ) := by
    dsimp [t]
    have := min_le_right δ (ρ.re - (1 / 2 + α + θ))
    linarith
  have he : 0 < α + θ + t := by linarith
  have henergy := dampedMobius_energy_of_base_signed_growth
    (α := α) (θ := θ) (ε := α + θ + t) hC he (by linarith) (by linarith) hgrowth
  have hp := centered_damped_square_summable_zero_propagation he.le
    (1 / riemannZeta (1 + ((α + θ + t : ℝ) : ℂ))).re henergy
    ρ (by linarith) hone hz
  apply hshift t ht htδ
  have heq : z - (t : ℂ) = ρ - ((α + θ + t : ℝ) : ℂ) := by
    simp only [z, Complex.ofReal_add]
    ring
  rw [heq]
  exact hp

/-- Uniformly bounded full cutoffs at damping α exclude zeros to the right
of 1/2+α. This does not follow merely from finite limiting energy at α. -/
theorem zeta_ne_zero_of_dampedMobius_cutoffs_bounded
    {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hbound : ∀ M : ℕ, ‖arithmeticFloorHilbertPartial (dampedMobiusWeight α) M‖ ≤ C)
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) + α < ρ.re) (hone : ρ.re < 1) :
    riemannZeta ρ ≠ 0 := by
  apply zeta_ne_zero_of_dampedMobius_signed_growth hα hC (θ := 0) le_rfl
    (fun n => by simpa only [Real.rpow_zero, mul_one] using hbound (n + 1))
    ρ (by simpa only [add_zero] using hhalf) hone

/-- Natural-order convergence implies bounded cutoffs, so it too forces
the zero-free strip. The limit need not be supplied with coordinates. -/
theorem zeta_ne_zero_of_dampedMobius_cutoffs_tendsto
    {α : ℝ} (hα : 0 ≤ α) {f : ThresholdHilbert}
    (hf : Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight α)) atTop (𝓝 f))
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) + α < ρ.re) (hone : ρ.re < 1) :
    riemannZeta ρ ≠ 0 := by
  have h := hf.norm
  rw [← Nat.cofinite_eq_atTop] at h
  obtain ⟨C, hC⟩ := h.bddAbove_range_of_cofinite
  have hb (M : ℕ) : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight α) M‖ ≤ C :=
    hC (Set.mem_range_self M)
  exact zeta_ne_zero_of_dampedMobius_cutoffs_bounded hα
    ((norm_nonneg _).trans (hb 0)) hb ρ hhalf hone

/-- Every zero to the right of the shifted critical line forces failure of
every smaller power bound on the complete signed cutoff norm. -/
theorem right_half_zero_forces_dampedMobius_cutoff_growth
    {α θ : ℝ} (hα : 0 ≤ α) (hθ : 0 ≤ θ)
    (ρ : ℂ) (hhalf : (1 / 2 : ℝ) + α + θ < ρ.re) (hone : ρ.re < 1)
    (hz : riemannZeta ρ = 0) :
    ∀ C : ℝ, 0 ≤ C → ∃ n : ℕ,
      C * ((n + 1 : ℕ) : ℝ) ^ θ <
        ‖arithmeticFloorHilbertPartial (dampedMobiusWeight α) (n + 1)‖ := by
  classical
  intro C hC
  by_contra h
  push Not at h
  exact zeta_ne_zero_of_dampedMobius_signed_growth hα hC hθ h ρ hhalf hone hz

/-- At zero damping, bounded full signed cutoffs already imply RH. -/
theorem riemannHypothesis_of_raw_dampedMobius_cutoffs_bounded
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ M : ℕ, ‖arithmeticFloorHilbertPartial (dampedMobiusWeight 0) M‖ ≤ C) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro ρ hhalf hone
  exact zeta_ne_zero_of_dampedMobius_cutoffs_bounded (by norm_num) hC hbound
    ρ (by simpa only [add_zero] using hhalf) hone

end RiemannResearch.RH.Pareto
