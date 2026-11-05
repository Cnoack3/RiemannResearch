/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.BalazardReciprocalCharge
import RiemannResearch.RH.QDisplacementTranslationCarry

/-! # The limiting centered carry expansion

The reciprocal Möbius charge rule proved in the Pareto realization
(Balazard, arXiv:1812.04309, Propositions 6–7) also supplies the scalar
boundary limit in Q. Passing to the limit at each fixed translated site
retains the centered carry series in its natural conductor order.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QDisplacementTranslationCarry
open Pareto ZetaTwoHilbert ZetaTwoParetoTransfer QSquarefreeHeadBoundary

theorem qSequence_reciprocal_charge_tendsto (f : QHilbert) :
    Tendsto (fun H => ∑ m ∈ Finset.Icc 1 H, mobiusDifference m (qSequence f) / (m : ℝ))
      atTop (𝓝 0) := by
  simpa only [mobiusDifferenceCLM_apply, toPareto_sequence] using
    mobiusDifference_reciprocal_tendsto_zero (toPareto f)

theorem headCharge_tendsto_zero (f : QHilbert) :
    Tendsto (fun N => headCharge N f) atTop (𝓝 0) := by
  have h := (qSequence_reciprocal_charge_tendsto f).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, slope_eq_headCharge] using h

/-- Pointwise recovery of the canonical residue synthesis at every fixed site. -/
theorem headSynthesis_tendsto_at_site (f : QHilbert) (k : ℕ) :
    Tendsto (fun H => qSequence (headSynthesis H f) k) atTop (𝓝 (qSequence f k)) := by
  have h := (headCharge_tendsto_zero f).const_mul (k : ℝ)
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => qSequence f k)
    atTop (𝓝 (qSequence f k))).sub h
  rw [mul_zero, sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop k] with H hH
  exact (headSynthesis_prefix H f k (by omega)).symm

/-- The finite horizon can go to infinity before the physical block changes.
No absolute summability of the centered carry series is required. -/
theorem centered_translation_tendsto (f : QHilbert) (L t : ℕ) :
    Tendsto (fun H => ∑ m ∈ Finset.Icc 1 H, mobiusDifference m (qSequence f) *
      ((if m ≤ L % m + t % m then (1 : ℝ) else 0) - (L % m : ℕ) / (m : ℝ)))
      atTop (𝓝 (qSequence f (L + t) - qSequence f t)) := by
  let y := qSequence f (L + t) - qSequence f t
  have hs := (qSequence_reciprocal_charge_tendsto f).const_mul (L : ℝ)
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y)).sub hs
  rw [mul_zero, sub_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (L + t)] with H hH
  dsimp only [y]
  linarith only [centered_translation (qSequence f) (qSequence_zero f) H L t hH]

end RiemannResearch.RH.QDisplacementTranslationCarry
