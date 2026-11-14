/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.RationalIntervalLimits
import RiemannResearch.Analysis.MontgomeryGaussianSmoothing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # A countable interval criterion for Montgomery's actual form factor

Source for the arithmetic target: Carneiro--Milinovich--Ramos,
https://arxiv.org/abs/2310.01913, equation (1.4), citing Goldston (1988).
That paper's equivalence with PCC assumes RH and uses N(T) normalization.
Here we prove only the countable-testing equivalence for the repository's
actual multiplicity-aware T log(T)/(2*pi) normalized form factor.
The rational anchored limit is an open arithmetic obligation, not a theorem.
No PCC equivalence from the paper is inserted as an axiom or hypothesis.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryFormFactor

/-- The countable arithmetic target. Its truth remains open. -/
def RationalAnchoredLimit : Prop :=
  ∀ q : ℚ, 1 < q → Tendsto
    (fun T : ℝ => ∫ α in (1 : ℝ)..(q : ℝ), formFactor T α)
    atTop (𝓝 ((q : ℝ) - 1))

/-- All fixed intervals above Fourier support one. -/
def IntervalMassLimit : Prop :=
  ∀ a b : ℝ, 1 ≤ a → a < b → Tendsto
    (fun T : ℝ => ∫ α in a..b, formFactor T α) atTop (𝓝 (b - a))

/-- The interval-average target, with fixed base and positive length. -/
def IntervalAverageLimit : Prop :=
  ∀ b ℓ : ℝ, 1 ≤ b → 0 < ℓ → Tendsto
    (fun T : ℝ => (∫ α in b..(b + ℓ), formFactor T α) / ℓ)
    atTop (𝓝 1)

theorem intervalMassLimit_of_rationalAnchoredLimit
    (h : RationalAnchoredLimit) : IntervalMassLimit := by
  intro a b ha hab
  apply tendsto_intervalIntegral_of_rat_Ici ?_ ?_ ?_ ha (le_trans ha hab.le)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    intro x hx
    exact formFactor_nonneg hT x
  · intro T x y
    exact (MontgomeryGaussianSmoothing.continuous_formFactor T).intervalIntegrable x y
  · intro q hq
    rcases eq_or_lt_of_le hq with hq | hq
    · simp only [← hq, intervalIntegral.integral_same, sub_self]
      exact tendsto_const_nhds
    · exact h q (by exact_mod_cast hq)

theorem rationalAnchoredLimit_iff_intervalMassLimit :
    RationalAnchoredLimit ↔ IntervalMassLimit := by
  constructor
  · exact intervalMassLimit_of_rationalAnchoredLimit
  · intro h q hq
    exact h 1 q le_rfl (by exact_mod_cast hq)

theorem intervalMassLimit_iff_intervalAverageLimit :
    IntervalMassLimit ↔ IntervalAverageLimit := by
  constructor
  · intro h b ℓ hb hℓ
    have hh := (h b (b + ℓ) hb (by linarith)).div_const ℓ
    simpa only [add_sub_cancel_left, div_self (ne_of_gt hℓ)] using hh
  · intro h a b ha hab
    have hh := (h a (b - a) ha (sub_pos.mpr hab)).mul_const (b - a)
    simpa only [add_sub_cancel, div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hab)),
      one_mul] using hh

/-- Checked reduction, not a proof of either open arithmetic property. -/
theorem rationalAnchoredLimit_iff_intervalAverageLimit :
    RationalAnchoredLimit ↔ IntervalAverageLimit :=
  rationalAnchoredLimit_iff_intervalMassLimit.trans
    intervalMassLimit_iff_intervalAverageLimit

/-- The same countable input also handles convergent moving endpoints,
including endpoints tending to the Fourier-support boundary one. -/
theorem moving_interval_limit_of_rationalAnchoredLimit
    (h : RationalAnchoredLimit) {a b : ℝ} {a' b' : ℝ → ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha' : Tendsto a' atTop (𝓝 a)) (hb' : Tendsto b' atTop (𝓝 b))
    (ha1 : ∀ᶠ T in atTop, 1 ≤ a' T) (hb1 : ∀ᶠ T in atTop, 1 ≤ b' T) :
    Tendsto (fun T : ℝ => ∫ α in a' T..b' T, formFactor T α)
      atTop (𝓝 (b - a)) := by
  apply tendsto_intervalIntegral_of_rat_Ici_moving ?_ ?_ ?_ ha hb ha' hb' ha1 hb1
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    intro x hx
    exact formFactor_nonneg hT x
  · intro T x y
    exact (MontgomeryGaussianSmoothing.continuous_formFactor T).intervalIntegrable x y
  · intro q hq
    rcases eq_or_lt_of_le hq with hq | hq
    · simp only [← hq, intervalIntegral.integral_same, sub_self]
      exact tendsto_const_nhds
    · exact h q (by exact_mod_cast hq)

end RiemannResearch.Analysis.MontgomeryFormFactor
