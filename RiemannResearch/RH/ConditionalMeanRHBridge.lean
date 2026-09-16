/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.MellinCesaroSummability
import RiemannResearch.Probability.ConditionalIIDReplica
import RiemannResearch.RH.ParetoLegalApproximationClosure

/-!
# Conditional-mean legal approximation implies the actual Riemann hypothesis

The proof uses the actual Mellin integral, explicit second differences,
proved dual summability, and the full signed pairing. No inverse Cesaro
bound, Nyman criterion axiom, or arithmetic approximation family is assumed.
The approximation hypothesis is not proved here; only its implication is.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID ArithmeticCumulative

/-- Error in the weaker, exact conditional-mean Hilbert norm. -/
def conditionalMeanError (g : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, mixtureWeight (k + 1) * (1 - cesaro g (k + 1)) ^ 2

/-- This constant is finite by the proved weighted dual summability theorem. -/
def conditionalMellinDualSquare (s : ℂ) : ℝ :=
  ∑' k : ℕ, ‖mellinSecond s (k + 1)‖ ^ 2 / conditionalWeight k

theorem conditionalMeanError_nonneg (g : ℕ → ℝ) : 0 ≤ conditionalMeanError g :=
  tsum_nonneg (fun k => mul_nonneg (mixtureWeight_nonneg _) (sq_nonneg _))

theorem conditionalMellinDualSquare_nonneg (s : ℂ) : 0 ≤ conditionalMellinDualSquare s :=
  tsum_nonneg (fun k => div_nonneg (sq_nonneg _) (conditionalWeight_pos k).le)

/-- At a right-half-plane zero, even the weaker conditional-mean error has a positive obstruction. -/
theorem conditionalMeanError_obstruction_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    {g : ℕ → ℝ} (hg : g ∈ legalSeedSpan A) :
    1 ≤ conditionalMellinDualSquare s * conditionalMeanError g := by
  obtain ⟨f, hf, hfg⟩ := legalSeedSpan_exists_hilbert A hA hg
  obtain ⟨B, hB⟩ := legalSeedSpan_bounded A hA hg
  have herr (n : ℕ) (hn : 0 < n) :
      hilbertSequence (hilbertOne - f) n = 1 - g n := by
    change hilbertSequenceLinear (hilbertOne - f) n = _
    rw [map_sub]
    change hilbertSequence hilbertOne n - hilbertSequence f n = _
    rw [hilbertOne_sequence, hfg]
    simp [zeroAnchor, ne_of_gt hn]
  have hb (n : ℕ) (hn : 0 < n) :
      ‖(hilbertSequence (hilbertOne - f) n : ℂ)‖ ≤ 1 + B := by
    rw [herr n hn, Complex.ofReal_sub, Complex.ofReal_one]
    apply (norm_sub_le (1 : ℂ) (g n : ℂ)).trans
    simpa only [norm_one, Complex.norm_real, Real.norm_eq_abs, add_comm] using
      add_le_add_left (hB n) 1
  have hmean (k : ℕ) :
      mean (fun n => (hilbertSequence (hilbertOne - f) n : ℂ)) (k + 1) =
        ((1 - cesaro g (k + 1) : ℝ) : ℂ) := by
    rw [mean_ofReal]
    apply congrArg (fun x : ℝ => (x : ℂ))
    calc
      cesaro (hilbertSequence (hilbertOne - f)) (k + 1) =
          cesaro (fun n => 1 - g n) (k + 1) := by
        unfold cesaro
        congr 1
        apply Finset.sum_congr rfl
        intro n hn
        exact herr n (Finset.mem_Icc.mp hn).1
      _ = _ := cesaro_const_sub g 1 (k + 1) (Nat.succ_pos k)
  have hfzero := paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz
    ((hilbertLegalSubspace A).le_topologicalClosure hf)
  have heval : paretoMellin (hilbertOne - f) s = 1 / s := by
    change paretoMellinContinuous s hs (hilbertOne - f) = _
    rw [map_sub]
    change paretoMellin hilbertOne s - paretoMellin f s = _
    rw [paretoMellin_one s hs, hfzero, sub_zero]
  have hp := cesaro_mellin_pairing (hilbertOne - f) s hs (1 + B) hb
  rw [heval] at hp
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have hp1 : (∑' k : ℕ, mellinSecond s (k + 1) *
      mean (fun n => (hilbertSequence (hilbertOne - f) n : ℂ)) (k + 1)) = 1 := by
    rw [hp]
    field_simp
  have hbound := Analysis.WeightedPairing.pairing_norm_sq_le conditionalWeight conditionalWeight_pos
    (fun k => mellinSecond s (k + 1))
    (fun k => mean (fun n => (hilbertSequence (hilbertOne - f) n : ℂ)) (k + 1))
    (mellinSecond_dual_summable s hs)
    (bounded_mean_energy_summable _ (1 + B) hb)
  rw [hp1, norm_one, one_pow] at hbound
  simp_rw [hmean, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hbound
  exact hbound

/-- Conditional-mean legal approximation excludes every zero in Re(s)>1/2 other than the pole. -/
theorem zeta_ne_zero_of_conditionalMeanApproximation
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g ∈ legalSeedSpan A, conditionalMeanError g < ε)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hD := conditionalMellinDualSquare_nonneg s
  have hd : 0 < conditionalMellinDualSquare s + 1 := by linarith
  obtain ⟨g, hg, he⟩ := happrox (1 / (conditionalMellinDualSquare s + 1)) (by positivity)
  have hob := conditionalMeanError_obstruction_of_zeta A hA s hs hs1 hz hg
  have he0 := conditionalMeanError_nonneg g
  have ht := (lt_div_iff₀ hd).mp he
  nlinarith

/-- Actual mathlib RH, using zeta reflection rather than an assumed Nyman--Beurling criterion. -/
theorem riemannHypothesis_of_conditionalMeanApproximation
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g ∈ legalSeedSpan A, conditionalMeanError g < ε) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hright (s : ℂ) (hsz : riemannZeta s = 0)
      (hs0 : 0 < s.re) (hs1 : s.re < 1) : s.re ≤ 1 / 2 := by
    by_contra h
    have hs : 1 / 2 < s.re := lt_of_not_ge h
    have hsne : s ≠ 1 := by intro he; simp [he] at hs1
    exact zeta_ne_zero_of_conditionalMeanApproximation A hA happrox s hs hsne hsz
  have hr := Zeta23.zeta_reflect_zero ρ ⟨hz, h0, h1⟩
  have hrbound := hright (Zeta23.reflect ρ) hr.1 hr.2.1 hr.2.2
  have hbnd := hright ρ hz h0 h1
  simp [Zeta23.reflect] at hrbound
  linarith

/-- Sequence form of the weaker-norm implication; no bounded inverse of Cesaro averaging is used. -/
theorem riemannHypothesis_of_conditionalMeanError_tendsto
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (g : ℕ → ℕ → ℝ)
    (hg : ∀ j, g j ∈ legalSeedSpan A)
    (hlim : Tendsto (fun j => conditionalMeanError (g j)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_conditionalMeanApproximation A hA
  intro ε hε
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨g j, hg j, hj⟩

end RiemannResearch.RH.Pareto
