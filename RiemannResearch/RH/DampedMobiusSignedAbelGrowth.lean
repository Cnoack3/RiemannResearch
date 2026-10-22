/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.SignedPowerDampingAbel
import RiemannResearch.RH.DampedMobiusSignedHeadClosure

/-!
# Arithmetic power damping from complete signed residue growth

This is an analytic transfer with an explicit arithmetic premise. It gives
ordered convergence of the actual damped residue cutoffs and then identifies
their Hilbert limit with the canonical centered discrepancy. No pointwise
bound on individual physical discrepancy coordinates is used.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

theorem arithmeticResidueTerm_power_damping (w : ℕ → ℝ) (ε : ℝ) (m : ℕ) :
    arithmeticResidueTerm (fun d => w d * (d : ℝ) ^ (-ε)) m =
      ((m + 1 : ℕ) : ℝ) ^ (-ε) • arithmeticResidueTerm w m := by
  unfold arithmeticResidueTerm
  rw [smul_smul]
  congr 1
  ring

/-- Transfer a signed raw-prefix norm bound into genuine ordered Hilbert
convergence at any larger positive damping exponent. -/
theorem arithmeticFloorHilbertPartial_power_damping_converges
    (w : ℕ → ℝ) {C θ ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hθε : θ < ε)
    (hgrowth : ∀ n : ℕ,
      ‖arithmeticFloorHilbertPartial w (n + 1)‖ ≤ C * ((n + 1 : ℕ) : ℝ) ^ θ) :
    ∃ f : ThresholdHilbert,
      Tendsto (arithmeticFloorHilbertPartial (fun d => w d * (d : ℝ) ^ (-ε)))
        atTop (𝓝 f) := by
  have hg : ∀ n : ℕ,
      ‖RiemannResearch.Analysis.signedVectorPrefix (arithmeticResidueTerm w) (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ) ^ θ := by
    intro n
    simpa only [arithmeticFloorHilbertPartial, norm_neg,
      RiemannResearch.Analysis.signedVectorPrefix] using hgrowth n
  have ht := RiemannResearch.Analysis.signedVector_power_damped_tendsto_of_prefix_growth
    (arithmeticResidueTerm w) hC hε hθε hg
  refine ⟨-(∑' n, ((((n + 1 : ℕ) : ℝ) ^ (-ε)) -
    (((n + 2 : ℕ) : ℝ) ^ (-ε))) •
      RiemannResearch.Analysis.signedVectorPrefix (arithmeticResidueTerm w) (n + 1)), ?_⟩
  change Tendsto (fun N => -(∑ n ∈ Finset.range N,
    arithmeticResidueTerm (fun d => w d * (d : ℝ) ^ (-ε)) n)) atTop _
  simp_rw [arithmeticResidueTerm_power_damping]
  exact ht.neg

/-- Actual Möbius specialization. The bound concerns the full signed raw
residue cutoff, including its infinite Pareto physical tail. -/
theorem dampedMobius_cutoffs_converge_of_raw_signed_growth
    {C θ ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hθε : θ < ε)
    (hgrowth : ∀ n : ℕ,
      ‖arithmeticFloorHilbertPartial (fun d => (ArithmeticFunction.moebius d : ℝ)) (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ) ^ θ) :
    ∃ f : ThresholdHilbert,
      Tendsto (arithmeticFloorHilbertPartial (dampedMobiusWeight ε)) atTop (𝓝 f) := by
  change ∃ f : ThresholdHilbert,
    Tendsto (arithmeticFloorHilbertPartial
      (fun d => (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ε))) atTop (𝓝 f)
  exact arithmeticFloorHilbertPartial_power_damping_converges
    (fun d => (ArithmeticFunction.moebius d : ℝ)) hC hε hθε hgrowth

/-- Signed raw-prefix growth supplies finite energy at every larger
positive damping. Identifying the limit uses the already proved scalar
coordinate limit, independently of any absolute vector-series convergence. -/
theorem dampedMobius_energy_of_raw_signed_growth
    {C θ ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (hθε : θ < ε)
    (hgrowth : ∀ n : ℕ,
      ‖arithmeticFloorHilbertPartial (fun d => (ArithmeticFunction.moebius d : ℝ)) (n + 1)‖ ≤
        C * ((n + 1 : ℕ) : ℝ) ^ θ) :
    Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n -
        (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) := by
  obtain ⟨f, hf⟩ := dampedMobius_cutoffs_converge_of_raw_signed_growth hC hε hθε hgrowth
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
