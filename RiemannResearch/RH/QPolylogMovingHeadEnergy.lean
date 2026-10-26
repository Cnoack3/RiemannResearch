/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PointwiseEnergyDivergence
import RiemannResearch.Analysis.WeightedHeadEnergy
import RiemannResearch.Analysis.LogTailWeights
import RiemannResearch.Analysis.LogSquareTail
import RiemannResearch.RH.QPolylogTailEnergy
import RiemannResearch.RH.QHilbertConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Cofinal finite-head budgets for convergent Q vectors

Source: the user-provided squarefree moving-head continuation. These statements are independent of squarefree legality
and RH. A polylogarithmic pointwise head envelope supplies a common head budget;
a cofinally bounded head budget supplies finite weighted energy of the limit.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QPolylogTailEnergy
open ZetaTwoHilbert ZetaTwoProbability
open RiemannResearch.Analysis RiemannResearch.Analysis.LogTailWeights

def weightedHeadEnergy (k H : ℕ) (u : QHilbert) : ℝ :=
  ∑ n ∈ Finset.range (H + 1), polylogWeightedEnergyTerm k u n

/-- The earlier all-stage pointwise condition implies the new energy budget
with one common finite constant, before any limiting argument. -/
theorem polylog_head_envelope_implies_uniform_head_budget
    (u : ℕ → QHilbert) (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ N n : ℕ, 0 < n → n ≤ N →
      |qSequence (u N) n| ≤ C*(6+Real.log (n : ℝ))^m) :
    ∃ D : ℝ, ∀ N : ℕ, weightedHeadEnergy (2*m+2) N (u N) ≤ D := by
  let a : ℕ → ℝ := fun n =>
    (C^2/zetaTwo) * (1 / ((n : ℝ)*(6+Real.log (n : ℝ))^2))
  have hs0 : Summable (fun n : ℕ =>
      1 / ((n : ℝ)*(6+Real.log (n : ℝ))^2)) := by
    simpa only [Real.rpow_two] using summable_shifted_log_square
  have hs : Summable a := hs0.mul_left (C^2/zetaTwo)
  refine ⟨∑' n : ℕ, a n, ?_⟩
  intro N
  have hp : weightedHeadEnergy (2*m+2) N (u N) ≤
      ∑ n ∈ Finset.range (N+1), a n := by
    apply Finset.sum_le_sum
    intro n hn
    apply polylogWeightedEnergyTerm_le_log_square
    by_cases hn0 : n = 0
    · subst n
      simp only [qSequence_zero, abs_zero, Nat.cast_zero, Real.log_zero, add_zero]
      positivity
    · exact hu N n (Nat.pos_of_ne_zero hn0) (by
        have hh := Finset.mem_range.mp hn
        omega)
  exact hp.trans (hs.sum_le_tsum (Finset.range (N+1)) (fun n _ => by
    dsimp [a]
    have hz := zetaTwo_pos
    positivity))

theorem weightedEnergy_summable_of_frequently_moving_head_bound
    (k : ℕ) (u : ℕ → QHilbert) (v : QHilbert)
    (hu : Tendsto u atTop (𝓝 v))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (C : ℝ) (hbound : ∃ᶠ N : ℕ in atTop,
      weightedHeadEnergy k (H N) (u N) ≤ C) :
    Summable (polylogWeightedEnergyTerm k v) ∧
      (∑' n : ℕ, polylogWeightedEnergyTerm k v n) ≤ C := by
  have hlim (n : ℕ) : Tendsto
      (fun N => polylogWeightedEnergyTerm k (u N) n)
      atTop (𝓝 (polylogWeightedEnergyTerm k v n)) := by
    have h := (qSequence_tendsto_of_tendsto hu n).pow 2
    simpa only [polylogWeightedEnergyTerm] using
      h.const_mul (polylogTailProfile k n * positiveQWeight n)
  have hhead : Tendsto (fun N => H N + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [hH.eventually (eventually_ge_atTop M)] with N hN
    omega
  exact summable_of_frequently_head_bound
    (fun N n => polylogWeightedEnergyTerm k (u N) n)
    (polylogWeightedEnergyTerm k v)
    (fun N n => polylogWeightedEnergyTerm_nonneg k (u N) n)
    hlim (fun N => H N + 1) hhead C hbound

/-- Hilbert convergence suffices for a normalized moving-head energy limit.
This does not assert a bounded unnormalized weighted energy. -/
theorem weightedHeadEnergy_div_profile_tendsto_zero
    (k : ℕ) (u : ℕ → QHilbert) (v : QHilbert)
    (hu : Tendsto u atTop (𝓝 v))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop) :
    Tendsto (fun N => weightedHeadEnergy k (H N) (u N) /
      polylogTailProfile k (H N)) atTop (𝓝 0) := by
  let E : ℕ → ℕ → ℝ := fun j n =>
    positiveQWeight n * qSequence (u j) n ^ 2
  let e : ℕ → ℝ := fun n => positiveQWeight n * qSequence v n ^ 2
  have hE (j n : ℕ) : 0 ≤ E j n :=
    mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)
  have he (n : ℕ) : 0 ≤ e n :=
    mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)
  have habs (j n : ℕ) : |E j n - e n| =
      positiveQWeight n * |qSequence (u j) n ^ 2 - qSequence v n ^ 2| := by
    dsimp [E, e]
    rw [← mul_sub, abs_mul, abs_of_nonneg (positiveQWeight_nonneg n)]
  have hd (j : ℕ) : Summable (fun n => |E j n - e n|) := by
    simpa only [habs] using qSquareL1Dist_summable (u j) v
  have hlim : Tendsto (fun j => ∑' n, |E j n - e n|) atTop (𝓝 0) := by
    simpa only [qSquareL1Dist, habs] using qSquareL1Dist_tendsto_zero hu
  have ht := normalized_weighted_head_tendsto_zero_of_l1
    (polylogTailProfile k) (polylogTailProfile_nonneg k)
    (polylogTailProfile_monotone k) (polylogTailProfile_tendsto_atTop k)
    E e hE he (qSequence_square_summable v) hd hlim H hH
  convert ht using 1
  funext j
  congr 1
  unfold weightedHeadEnergy
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [polylogWeightedEnergyTerm, E]
  ring

end RiemannResearch.RH.QPolylogTailEnergy
