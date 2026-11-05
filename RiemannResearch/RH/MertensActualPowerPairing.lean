/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MertensPowerPairing
import RiemannResearch.RH.MertensFirstMomentEnvelope
import RiemannResearch.RH.QSquarefreeResidualTail
import RiemannResearch.RH.QMobiusExactHead

/-!
# Signed first moments of the actual squarefree displacement

The arithmetic two-part estimate for the canonical exact heads is an explicit
hypothesis. A power Mertens estimate supplies it by the finite Möbius floor
identity and Abel summation.
-/
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open RiemannResearch.Analysis ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QAnnihilatorTailEscape QSquarefreeResidualTail ZetaTwoOptimizerStage

private theorem defect_physical_succ (N n : ℕ) :
    qSequence (defect N) (n+1) = 1 - Pareto.canonicalMobiusHead N (n+1) := by
  change qSequenceLinear (qOne - QMobiusExactHead.exactHead N) (n+1) = _
  rw [map_sub]
  change qSequence qOne (n+1) - qSequence (QMobiusExactHead.exactHead N) (n+1) = _
  rw [qSequence_qOne, QMobiusExactHead.exactHead_sequence]
  simp [qOneSequence]

/-- Weighted absolute summability of any squarefree annihilator forces its mean
to vanish under the two-part canonical head bound. The arithmetic saving is a. -/
theorem annihilator_mean_zero_of_power_defect
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hdef : ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      |1 - Pareto.canonicalMobiusHead (q j) (n+1)| ≤
        C * min (q j : ℝ) (((n : ℝ) + 1) * (q j : ℝ) ^ (-a)))
    (u : QHilbert) (hu : u ∈ ZetaTwoOptimizerStage.closureᗮ)
    (hsum : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (1 / (1+a)) *
      |qSequence u (n+1) / ((n : ℝ) + 1) ^ 2|)) :
    inner ℝ qOne u = 0 := by
  let D : ℕ → ℕ → ℝ := fun j n => qSequence (defect (q j)) (n+1)
  let v : ℕ → ℝ := fun n => qSequence u (n+1) / ((n : ℝ) + 1)^2
  have hh (n : ℕ) : ∀ᶠ j in atTop, D j n = 0 := by
    filter_upwards [hq.eventually (eventually_ge_atTop (n+1))] with j hj
    change qSequence (defect (q j)) (n+1) = 0
    rw [defect_physical_succ, Pareto.canonicalMobiusHead_exact (q j) (n+1) (by omega) hj, sub_self]
  have hb : ∀ᶠ j : ℕ in atTop, (0 : ℝ) < q j ∧ ∀ n : ℕ,
      |D j n| ≤ C * min (q j : ℝ) (((n : ℝ) + 1) * (q j : ℝ) ^ (-a)) := by
    filter_upwards [hq.eventually (eventually_ge_atTop 1), hdef] with j hp hd
    refine ⟨by exact_mod_cast (show 0 < q j by omega), ?_⟩
    simpa only [D, defect_physical_succ] using hd
  have hlim := (power_defect_pairing_tendsto_zero D v (fun j => (q j : ℝ)) a C
    ha hC hh hb hsum).const_mul (1 / zetaTwo)
  simp only [mul_zero] at hlim
  have heq (j : ℕ) : (1 / zetaTwo) * (∑' n, D j n * v n) =
      inner ℝ (defect (q j)) u := by
    rw [qInner_weighted, (qSequence_product_summable (defect (q j)) u).tsum_eq_zero_add]
    simp only [qSequence_zero, mul_zero, zero_add, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [D, v, positiveQWeight, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
    ring
  have hevent : (fun j => (1 / zetaTwo) * (∑' n, D j n * v n)) =ᶠ[atTop]
      (fun _ : ℕ => inner ℝ qOne u) := by
    filter_upwards [hlegal] with j hj
    rw [heq, defect, inner_sub_left, Submodule.inner_right_of_mem_orthogonal
      (squarefree_exactHead_mem_closure (q j) hj) hu, sub_zero]
  exact tendsto_nhds_unique tendsto_const_nhds (hlim.congr' hevent)

/-- Absolute convergence of the displacement's weighted first moment suffices, even
when the displacement exceeds every admissible pointwise power on a sparse set. -/
theorem riemannHypothesis_of_power_defect_and_displacement_moment
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hdef : ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      |1 - Pareto.canonicalMobiusHead (q j) (n+1)| ≤
        C * min (q j : ℝ) (((n : ℝ) + 1) * (q j : ℝ) ^ (-a)))
    (hd : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (1 / (1+a)) *
      |qSequence displacement (n+1) / ((n : ℝ) + 1) ^ 2|)) :
    RiemannHypothesis := by
  obtain ⟨A, hA⟩ := B_physical_bounded pResidual
  have hA0 := (abs_nonneg _).trans (hA 0)
  have hB := summable_power_pairing_of_growth (fun n => qSequence (B pResidual) (n+1))
    a 0 A ha (div_pos ha (by linarith)) hA0 (fun n => by simpa using hA (n+1))
  apply QMertensFirstMoment.rh_of_zero_projection_residual
  apply residual_eq_zero_of_witness_mean_zero
  apply annihilator_mean_zero_of_power_defect q hq a C ha hC hlegal hdef witness witness_mem_orthogonal
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) (abs_nonneg _)) _ (hB.add hd)
  intro n
  have he : qSequence witness (n+1) =
      qSequence (B pResidual) (n+1) - qSequence displacement (n+1) := by
    change qSequenceLinear (B pResidual - displacement) (n+1) = _
    rw [map_sub]
    rfl
  let x : ℝ := (n : ℝ) + 1
  change x ^ (1 / (1 + a)) * |qSequence witness (n+1) / x^2| ≤
    x ^ (1 / (1 + a)) * |qSequence (B pResidual) (n+1) / x^2| +
    x ^ (1 / (1 + a)) * |qSequence displacement (n+1) / x^2|
  rw [he, sub_div, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by dsimp [x]; positivity) _)
  simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
    (qSequence (B pResidual) (n+1) / x^2) (-(qSequence displacement (n+1) / x^2))

/-- Polynomial displacement growth strictly below the threshold supplies the moment. -/
theorem riemannHypothesis_of_power_defect_and_displacement
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (a β C K : ℝ)
    (ha : 0 < a) (hβ : β < a / (1+a)) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1))
    (hdef : ∀ᶠ j : ℕ in atTop, ∀ n : ℕ,
      |1 - Pareto.canonicalMobiusHead (q j) (n+1)| ≤
        C * min (q j : ℝ) (((n : ℝ) + 1) * (q j : ℝ) ^ (-a)))
    (hd : ∀ n : ℕ, |qSequence displacement (n+1)| ≤ K * ((n : ℝ)+1)^β) :
    RiemannHypothesis :=
  riemannHypothesis_of_power_defect_and_displacement_moment q hq a C ha hC hlegal hdef
    (summable_power_pairing_of_growth _ a β K ha hβ hK hd)

end RiemannResearch.RH.QSquarefreeDisplacementRigidity
