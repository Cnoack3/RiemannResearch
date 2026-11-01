/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteWeightedPushforward
import RiemannResearch.RH.QCesaroDyadic
import RiemannResearch.RH.QUniformMixture
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
/-!
# Arithmetic primitive measure and weighted residue classes

Source: user-provided manuscript, "Cesàro Energy, Squarefree CRT, and
Quantitative Lifting Toward the Riemann Hypothesis", 1 November 2026,
sections "The exact arithmetic measure on a periodic primitive" and
"Weighted Hilbert maps". This module formalizes the positive primitive
kernel and its exact pushforward, without replacing it by Haar measure.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QWeightedResidues
open QCesaroDyadic QUniformMixture ZetaTwoProbability
theorem qCumulativeWeight_pos (n : ℕ) (hn : 0 < n) :
    0 < qCumulativeWeight n := by
  have hz := zetaTwo_pos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  unfold qCumulativeWeight
  positivity
theorem qCumulativeWeight_summable : Summable qCumulativeWeight := by
  have hm : Summable qMixtureWeight :=
    (summable_nat_add_iff 1).mp hasSum_qMixtureWeight.summable
  refine Summable.of_nonneg_of_le qCumulativeWeight_nonneg ?_ hm
  intro n
  rcases n with _ | n
  · simp [qCumulativeWeight, qMixtureWeight]
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have he : qCumulativeWeight (n + 1) =
      qMixtureWeight (n + 1) / (((n + 1 : ℕ) : ℝ)^2) := by
    unfold qCumulativeWeight qMixtureWeight
    push_cast
    field_simp
  rw [he]
  exact div_le_self (qMixtureWeight_nonneg _) (by nlinarith)
def residueWeight (L : ℕ) (a : Fin L) : ℝ :=
  ∑' n : ℕ, if n % L = a.val then qCumulativeWeight n else 0
open QCesaroDyadic QUniformMixture QCesaroEnergy ArithmeticCumulative
open RiemannResearch.Probability.ConditionalIID
open RiemannResearch.Analysis.FiniteWeightedPushforward
theorem residue_integral (L : ℕ) (hL : 0 < L) (F : Fin L → ℝ) :
    (∑ a, residueWeight L a * F a) =
      ∑' n : ℕ, qCumulativeWeight n * F ⟨n % L, Nat.mod_lt n hL⟩ := by
  classical
  let π : ℕ → Fin L := fun n => ⟨n % L, Nat.mod_lt n hL⟩
  have he (a : Fin L) : residueWeight L a = pushWeight qCumulativeWeight π a := by
    apply tsum_congr
    intro n
    have h : n % L = a.val ↔ π n = a := by
      constructor
      · intro h
        exact Fin.ext h
      · intro h
        exact congrArg Fin.val h
    simp only [h]
  simpa only [he] using integral_pushWeight qCumulativeWeight π qCumulativeWeight_summable F

theorem periodic_cumulative_energy (g : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (hp : Function.Periodic (cumulative g) L) :
    qConditionalMeanSquare g =
      ∑ a : Fin L, residueWeight L a * cumulative g a.val ^ 2 := by
  classical
  let π : ℕ → Fin L := fun n => ⟨n % L, Nat.mod_lt n hL⟩
  have hs : Summable (fun n => qCumulativeWeight n * cumulative g n ^ 2) := by
    simpa only [π, hp.map_mod_nat] using
      summable_weighted_comp qCumulativeWeight π qCumulativeWeight_summable
        (fun a : Fin L => cumulative g a.val ^ 2)
  have hc : Summable (fun k => qMixtureWeight (k + 1) * cesaro g (k + 1) ^ 2) := by
    have ht := (summable_nat_add_iff 1).mpr hs
    exact ht.congr (fun k => (q_weight_cumulative g (k + 1)).symm)
  rw [qConditionalMeanSquare_eq_cumulative g hc, residue_integral L hL]
  exact tsum_congr (fun n => by rw [hp.map_mod_nat])
end RiemannResearch.RH.QWeightedResidues
