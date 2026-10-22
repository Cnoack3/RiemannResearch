/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SignedCriticalDamping
import RiemannResearch.RH.DampedMobiusSignedAbelGrowth

/-!
# Critical logarithmic cancellation in the complete raw Hilbert prefix

The premise here concerns the complete signed raw residue vector, including
its infinite physical tail. It is an explicit arithmetic obligation. No bound
on separate physical coordinates, coefficient magnitudes, or scalar Mertens
prefixes is substituted for it.

The critical logarithmic criterion is an application of standard Banach-valued
Abel summation. It extends the existing strict-exponent signed growth transfer.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- Critical logarithmic control of the complete signed raw Hilbert prefix
gives full natural-order convergence at the same damping exponent. -/
theorem arithmeticFloorHilbertPartial_power_damping_converges_of_critical_log
    (w : ℕ → ℝ) {C ε q : ℝ} (hε : 0 ≤ ε) (hq : 1 < q)
    (hgrowth : ∀ᶠ n : ℕ in atTop,
      ‖arithmeticFloorHilbertPartial w (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ)^ε /
          Real.log (2 * ((n + 1 : ℕ) : ℝ))^q) :
    ∃ f : ThresholdHilbert,
      Tendsto (arithmeticFloorHilbertPartial (fun d => w d * (d : ℝ)^(-ε)))
        atTop (𝓝 f) := by
  have hg : ∀ᶠ n : ℕ in atTop,
      ‖RiemannResearch.Analysis.signedVectorPrefix (arithmeticResidueTerm w) (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ)^ε /
          Real.log (2 * ((n + 1 : ℕ) : ℝ))^q := by
    simpa only [arithmeticFloorHilbertPartial, norm_neg,
      RiemannResearch.Analysis.signedVectorPrefix] using hgrowth
  have ht := RiemannResearch.Analysis.signedVector_power_damped_tendsto_of_critical_log
    (arithmeticResidueTerm w) hε hq hg
  refine ⟨-(∑' n, ((((n + 1 : ℕ) : ℝ)^(-ε)) -
    (((n + 2 : ℕ) : ℝ)^(-ε))) •
      RiemannResearch.Analysis.signedVectorPrefix (arithmeticResidueTerm w) (n + 1)), ?_⟩
  change Tendsto (fun N => -(∑ n ∈ Finset.range N,
    arithmeticResidueTerm (fun d => w d * (d : ℝ)^(-ε)) n)) atTop _
  simp_rw [arithmeticResidueTerm_power_damping]
  exact ht.neg

/-- Möbius specialization, with an eventual critical signed norm bound.
This is a conditional research reduction; the raw signed bound is open. -/
theorem dampedMobius_cutoffs_converge_of_raw_critical_log
    {C ε q : ℝ} (hε : 0 < ε) (hq : 1 < q)
    (hgrowth : ∀ᶠ n : ℕ in atTop,
      ‖arithmeticFloorHilbertPartial (fun d => (ArithmeticFunction.moebius d : ℝ)) (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ)^ε /
          Real.log (2 * ((n + 1 : ℕ) : ℝ))^q) :
    ∃ f : ThresholdHilbert,
      Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight ε)) atTop (𝓝 f) := by
  change ∃ f : ThresholdHilbert,
    Tendsto (arithmeticFloorHilbertPartial
      (fun d => (ArithmeticFunction.moebius d : ℝ) * (d : ℝ)^(-ε))) atTop (𝓝 f)
  exact arithmeticFloorHilbertPartial_power_damping_converges_of_critical_log
    (fun d => (ArithmeticFunction.moebius d : ℝ)) hε.le hq hgrowth

/-- The critical signed bound supplies finite energy of the canonical
centered discrepancy, by identifying all coordinates of the norm limit. -/
theorem dampedMobius_energy_of_raw_critical_log
    {C ε q : ℝ} (hε : 0 < ε) (hq : 1 < q)
    (hgrowth : ∀ᶠ n : ℕ in atTop,
      ‖arithmeticFloorHilbertPartial (fun d => (ArithmeticFunction.moebius d : ℝ)) (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ)^ε /
          Real.log (2 * ((n + 1 : ℕ) : ℝ))^q) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re)^2) := by
  obtain ⟨f, hf⟩ := dampedMobius_cutoffs_converge_of_raw_critical_log hε hq hgrowth
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

end RiemannResearch.RH.Pareto
