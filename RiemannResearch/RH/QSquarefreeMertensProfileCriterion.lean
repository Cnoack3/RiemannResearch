/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QProfileTailEnergy
import RiemannResearch.RH.QMobiusStretchedEnergy
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.QSquarefreeCapacity
import Mathlib.Tactic.FieldSimp

/-!
# The actual squarefree displacement under a uniform Mertens profile
The complete error of a legal Möbius head is paired with an annihilator tail.
The arithmetic estimate and the physical displacement condition are explicit.
-/
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeMertensProfileCriterion
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QAnnihilatorTailEscape QFiniteSupportDualCriterion QSquarefreeResidualTail
open QSquarefreeDisplacementRigidity QShiftedReciprocal QMobiusStretchedEnergy

/-- The existing complete-energy estimate, transferred to its exact-head error.
The uniform Mertens bound is an explicit analytic premise. -/
theorem defect_energy_of_uniform_mertens_log
    (N : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hsmall : ε * (1 + Real.log (1 / ε)) ≤ 1 / 2)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y →
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M y| ≤ ε * y) :
    ‖defect N‖ ^ 2 ≤ 2 * ‖qOne‖ ^ 2 + 12 / zetaTwo +
      (1040 / zetaTwo) * (N : ℝ) * (ε * (1 + Real.log (1 / ε))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh := (div_le_iff₀ hNR).mp
    (exactHead_energy_of_uniform_mertens_log N hN ε hε hεone hsmall hM)
  have heq :
      (2 / zetaTwo) * (3 / (N : ℝ) + 260 * (ε * (1 + Real.log (1 / ε)))) *
          (N : ℝ) =
        6 / zetaTwo + (520 / zetaTwo) * (N : ℝ) *
          (ε * (1 + Real.log (1 / ε))) := by
    field_simp [ne_of_gt zetaTwo_pos, ne_of_gt hNR]
    <;> ring
  rw [heq] at hh
  have hn := norm_sub_le qOne (QMobiusExactHead.exactHead N)
  have hs : ‖defect N‖ ^ 2 ≤
      2 * ‖qOne‖ ^ 2 + 2 * ‖QMobiusExactHead.exactHead N‖ ^ 2 := by
    change ‖qOne - QMobiusExactHead.exactHead N‖ ^ 2 ≤ _
    nlinarith [norm_nonneg qOne, norm_nonneg (QMobiusExactHead.exactHead N),
      norm_nonneg (qOne - QMobiusExactHead.exactHead N),
      sq_nonneg (‖qOne‖ - ‖QMobiusExactHead.exactHead N‖)]
  calc
    _ ≤ 2 * ‖qOne‖ ^ 2 + 2 * ‖QMobiusExactHead.exactHead N‖ ^ 2 := hs
    _ ≤ 2 * ‖qOne‖ ^ 2 + 2 * (6 / zetaTwo +
        (520 / zetaTwo) * (N : ℝ) * (ε * (1 + Real.log (1 / ε)))) := by
      linarith
    _ = _ := by ring

/-- A critical complete-tail consumer retaining the precise entropy loss in
the Mertens-to-energy estimate. Only cofinally many legal exact heads are used. -/
theorem annihilator_mean_zero_of_mertens_profile
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (ε : ℕ → ℝ)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hε : ∀ᶠ j : ℕ in atTop,
      0 < ε j ∧ ε j ≤ 1 ∧ ε j * (1 + Real.log (1 / ε j)) ≤ 1 / 2)
    (hM : ∀ᶠ j : ℕ in atTop, ∀ y : ℝ, (q j : ℝ) ≤ y →
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M y| ≤ ε j * y)
    (u : QHilbert) (hu : u ∈ closureᗮ)
    (hsmall : Tendsto (fun j => (q j : ℝ) *
        (ε j * (1 + Real.log (1 / ε j))) * ‖tail (q j) u‖ ^ 2)
      atTop (𝓝 0)) : inner ℝ qOne u = 0 := by
  have ht : Tendsto (fun j => ‖tail (q j) u‖ ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((tail_tendsto_zero u).comp hq).norm.pow 2
  have hlim :=
    (ht.const_mul (2 * ‖qOne‖ ^ 2 + 12 / zetaTwo)).add
      (hsmall.const_mul (1040 / zetaTwo))
  simp only [Function.comp_def, mul_zero, zero_add] at hlim
  have hle : ∀ᶠ j : ℕ in atTop, (inner ℝ qOne u) ^ 2 ≤
      (2 * ‖qOne‖ ^ 2 + 12 / zetaTwo) * ‖tail (q j) u‖ ^ 2 +
        (1040 / zetaTwo) * ((q j : ℝ) *
          (ε j * (1 + Real.log (1 / ε j))) * ‖tail (q j) u‖ ^ 2) := by
    filter_upwards [hlegal, hε, hM,
      hq.eventually (eventually_ge_atTop (1 : ℕ))] with j hj hεj hMj hqj
    have he := defect_energy_of_uniform_mertens_log (q j) (by omega)
      (ε j) hεj.1 hεj.2.1 hεj.2.2 hMj
    have hp := squarefree_defect_tail_sq_bound (q j) (q j) le_rfl hj u hu
    have hm := mul_le_mul_of_nonneg_right he (sq_nonneg ‖tail (q j) u‖)
    nlinarith
  have hz : (inner ℝ qOne u) ^ 2 ≤ 0 := ge_of_tendsto hlim hle
  nlinarith [sq_nonneg (inner ℝ qOne u)]

/-- Any vanishing nonnegative relative profile makes the reciprocal-smoothed
source negligible at the corresponding scaled complete-tail weight. -/
theorem profile_B_tail_tendsto_zero
    (q : ℕ → ℕ) (η : ℕ → ℝ)
    (hηnonneg : ∀ᶠ j : ℕ in atTop, 0 ≤ η j)
    (hη : Tendsto η atTop (𝓝 0)) (u : QHilbert) :
    Tendsto (fun j => (q j : ℝ) * η j * ‖tail (q j) (B u)‖ ^ 2)
      atTop (𝓝 0) := by
  let C : ℝ := 2 * (Real.sqrt zetaTwo * ‖u‖) ^ 2 / zetaTwo
  have hlim : Tendsto (fun j => η j * C) atTop (𝓝 0) := by
    simpa only [zero_mul] using hη.mul_const C
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hηnonneg] with j hj
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hj) (sq_nonneg _)
  · filter_upwards [hηnonneg] with j hj
    have h := scaled_tail_energy_le_of_bounded (B u) (q j)
      (Real.sqrt zetaTwo * ‖u‖) (by positivity) (B_physical_bound u)
    have hm := mul_le_mul_of_nonneg_left h hj
    simpa only [C, mul_assoc, mul_left_comm, mul_comm] using hm

/-- Exact equivalence for the actual displacement at an arbitrary certified
Mertens profile. The profile provider is a hypothesis, not an axiom or a newly
proved unconditional Mertens estimate. -/
theorem residual_zero_iff_mertens_profile_tail
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (ε : ℕ → ℝ)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hε : ∀ᶠ j : ℕ in atTop,
      0 < ε j ∧ ε j ≤ 1 ∧ ε j * (1 + Real.log (1 / ε j)) ≤ 1 / 2)
    (hM : ∀ᶠ j : ℕ in atTop, ∀ y : ℝ, (q j : ℝ) ≤ y →
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M y| ≤ ε j * y)
    (hη : Tendsto (fun j => ε j * (1 + Real.log (1 / ε j))) atTop (𝓝 0)) :
    limitingResidual = 0 ↔
      Tendsto (fun j => (q j : ℝ) *
        (ε j * (1 + Real.log (1 / ε j))) * ‖tail (q j) displacement‖ ^ 2)
        atTop (𝓝 0) := by
  constructor
  · intro hr
    simpa [displacement_eq_zero_of_residual_eq_zero hr, tail, finiteHead] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · intro hsmall
    have hηnonneg : ∀ᶠ j : ℕ in atTop,
        0 ≤ ε j * (1 + Real.log (1 / ε j)) := by
      filter_upwards [hε] with j hj
      have hinv : (1 : ℝ) ≤ 1 / ε j :=
        (le_div_iff₀ hj.1).mpr (by simpa using hj.2.1)
      exact mul_nonneg hj.1.le (by linarith [Real.log_nonneg hinv])
    have hw : ∀ᶠ j : ℕ in atTop,
        0 ≤ (q j : ℝ) * (ε j * (1 + Real.log (1 / ε j))) := by
      filter_upwards [hηnonneg] with j hj
      exact mul_nonneg (Nat.cast_nonneg _) hj
    have hBr := profile_B_tail_tendsto_zero q
      (fun j => ε j * (1 + Real.log (1 / ε j))) hηnonneg hη pResidual
    have hwitness : Tendsto (fun j => (q j : ℝ) *
        (ε j * (1 + Real.log (1 / ε j))) * ‖tail (q j) witness‖ ^ 2)
        atTop (𝓝 0) := by
      have hlim := (hBr.const_mul 2).add (hsmall.const_mul 2)
      simp only [Function.comp_def, mul_zero, zero_add] at hlim
      apply squeeze_zero' _ _ hlim
      · filter_upwards [hw] with j hj
        exact mul_nonneg hj (sq_nonneg _)
      · filter_upwards [hw] with j hj
        have hn : ‖tail (q j) witness‖ ≤
            ‖tail (q j) (B pResidual)‖ + ‖tail (q j) displacement‖ := by
          rw [witness, tail_sub]
          exact norm_sub_le _ _
        have hs : ‖tail (q j) witness‖ ^ 2 ≤
            2 * ‖tail (q j) (B pResidual)‖ ^ 2 +
              2 * ‖tail (q j) displacement‖ ^ 2 := by
          nlinarith [norm_nonneg (tail (q j) witness),
            norm_nonneg (tail (q j) (B pResidual)),
            norm_nonneg (tail (q j) displacement),
            sq_nonneg (‖tail (q j) (B pResidual)‖ -
              ‖tail (q j) displacement‖)]
        have hm := mul_le_mul_of_nonneg_left hs hj
        nlinarith
    exact residual_eq_zero_of_witness_mean_zero
      (annihilator_mean_zero_of_mertens_profile q hq ε hlegal hε hM
        witness witness_mem_orthogonal hwitness)

/-- Mathlib RH follows from the explicit Mertens provider and its critical
complete displacement-tail condition. No reverse implication from RH is used. -/
theorem riemannHypothesis_of_mertens_profile_tail
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (ε : ℕ → ℝ)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hε : ∀ᶠ j : ℕ in atTop,
      0 < ε j ∧ ε j ≤ 1 ∧ ε j * (1 + Real.log (1 / ε j)) ≤ 1 / 2)
    (hM : ∀ᶠ j : ℕ in atTop, ∀ y : ℝ, (q j : ℝ) ≤ y →
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M y| ≤ ε j * y)
    (hη : Tendsto (fun j => ε j * (1 + Real.log (1 / ε j))) atTop (𝓝 0))
    (hsmall : Tendsto (fun j => (q j : ℝ) *
        (ε j * (1 + Real.log (1 / ε j))) * ‖tail (q j) displacement‖ ^ 2)
      atTop (𝓝 0)) : RiemannHypothesis := by
  have hr := (residual_zero_iff_mertens_profile_tail q hq ε hlegal hε hM hη).mpr hsmall
  have hm : qOne ∈ closure :=
    Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  exact QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
    (QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr hm)

/-- An arbitrary physical envelope gives RH when its squared size is
negligible against the supplied Mertens profile. The complete physical tail
is retained, and the arithmetic and displacement bounds remain explicit
hypotheses. -/
theorem riemannHypothesis_of_mertens_profile_physical_bound
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (ε : ℕ → ℝ)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hε : ∀ᶠ j : ℕ in atTop,
      0 < ε j ∧ ε j ≤ 1 ∧ ε j * (1 + Real.log (1 / ε j)) ≤ 1 / 2)
    (hM : ∀ᶠ j : ℕ in atTop, ∀ y : ℝ, (q j : ℝ) ≤ y →
      |RiemannResearch.NumberTheory.PrimeNumberTheorem.M y| ≤ ε j * y)
    (hη : Tendsto (fun j => ε j * (1 + Real.log (1 / ε j))) atTop (𝓝 0))
    (H : ℕ → ℝ) (C : ℝ)
    (hprofile : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, N < n →
      H n ^ 2 / Real.sqrt (n : ℝ) ≤ H N ^ 2 / Real.sqrt (N : ℝ))
    (hb : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤ C * H n)
    (hsmall : Tendsto (fun j =>
        (ε j * (1 + Real.log (1 / ε j))) * H (q j) ^ 2)
      atTop (𝓝 0)) : RiemannHypothesis := by
  have hηnonneg : ∀ᶠ j : ℕ in atTop,
      0 ≤ ε j * (1 + Real.log (1 / ε j)) := by
    filter_upwards [hε] with j hj
    have hinv : (1 : ℝ) ≤ 1 / ε j :=
      (le_div_iff₀ hj.1).mpr (by simpa using hj.2.1)
    exact mul_nonneg hj.1.le (by linarith [Real.log_nonneg hinv])
  apply riemannHypothesis_of_mertens_profile_tail q hq ε hlegal hε hM hη
  exact QAnnihilatorTailEscape.profile_weighted_tail_tendsto_zero
    displacement H C hprofile hb q hq
    (fun j => ε j * (1 + Real.log (1 / ε j))) hηnonneg hsmall

end RiemannResearch.RH.QSquarefreeMertensProfileCriterion
