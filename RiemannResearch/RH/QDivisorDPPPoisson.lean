/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QDivisorDPPGrowingWindows
import RiemannResearch.RH.QDivisorDPPArithmeticBounds
import RiemannResearch.Analysis.ProjectionDPPKernel
import RiemannResearch.Probability.DeterminantalCountPoissonLimit
import RiemannResearch.Probability.DeterminantalPoissonLimit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Conditional Poisson laws for the actual Q divisor projection DPP

Source: the user-provided growing-window argument, with the newly proved
arithmetic and generic probability consumers. All mean and scale budgets
remain explicit in theorem types. This does not identify a zeta spectrum.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Topology
namespace RiemannResearch.RH.QDivisorDPP
open ZetaTwoProbability ZetaTwoHilbert
open RiemannResearch.Probability.DPP

def consecutiveEmbedding (x h : ℕ) : Fin h ↪ ℕ :=
  ⟨fun i => x + i, fun _ _ he => Fin.ext (Nat.add_left_cancel he)⟩

theorem basisKernel_growing_full_sq_tendsto
    (ε : ℝ) (hε : 0 < ε) (hεthree : ε < 3 / 4)
    (rank x h : ℕ → ℕ) (hh : ∀ n, 0 < h n) (rate : ℝ)
    (hmean : Tendsto (fun n => ∑ i : Fin (h n),
      basisKernel (rank n) (x n + i) (x n + i)) atTop (𝓝 rate))
    (hcube : Tendsto (fun n => (rank n : ℝ) ^ 3 /
      ((x n + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0))
    (hbudget : Tendsto (fun n => (h n : ℝ) ^ (5 - 4 * ε) /
      ((x n + 1 : ℕ) : ℝ) ^ (4 - 4 * ε)) atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i : Fin (h n), ∑ j : Fin (h n),
      basisKernel (rank n) (x n + i) (x n + j) ^ 2) atTop (𝓝 0) := by
  let b : ℕ → ℝ := fun n => (rank n : ℝ) ^ 3 /
    (zetaTwo * ((x n + 1 : ℕ) : ℝ) ^ 2)
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa [b, div_div, mul_comm] using hcube.div_const zetaTwo
  have hoff := basisKernel_growing_window_energy_tendsto ε hε hεthree rank x h hh hbudget
  simp_rw [basisKernel_distinct_window_eq_fin] at hoff
  apply moving_full_sq_tendsto_zero_of_offdiag h
    (fun n => Matrix.of (fun i j => basisKernel (rank n) (x n + i) (x n + j)))
    b rate _ hmean hb hoff
  intro n i
  refine ⟨((basisLaw_isDPP (rank n)).diagonal_bounds (x n + i)).1, ?_⟩
  have hw := qWeight_le_of_location (x n + i) ((x n + 1 : ℕ) : ℝ)
    (by positivity) (by exact_mod_cast (by omega : x n + 1 ≤ x n + (i : ℕ) + 1))
  calc
    _ ≤ qWeight (x n + i) *
        ((rank n : ℝ) * (rank n + 1) * (2 * rank n + 1) / 6) :=
      basisKernel_diagonal_le (rank n) (x n + i)
    _ ≤ qWeight (x n + i) * (rank n : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left (conductor_square_budget_le_cube (rank n)) (qWeight_pos _).le
    _ ≤ (1 / (zetaTwo * ((x n + 1 : ℕ) : ℝ) ^ 2)) * (rank n : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ = b n := by dsimp [b]; ring

theorem basisLaw_moving_window_count_poisson
    (rank h : ℕ → ℕ) (e : (n : ℕ) → Fin (h n) ↪ ℕ) (rate : ℝ)
    (hmean : Tendsto (fun n => ∑ i, basisKernel (rank n) (e n i) (e n i))
      atTop (𝓝 rate))
    (hsq : Tendsto (fun n => ∑ i, ∑ j, basisKernel (rank n) (e n i) (e n j) ^ 2)
      atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n => (basisLaw (rank n)).real
      {ω | (Finset.univ.filter (fun i => ω (e n i) = true)).card = k}) atTop
      (𝓝 (Real.exp (-rate) * rate ^ k / k.factorial)) := by
  classical
  have hQ (n : ℕ) : (Matrix.of (fun i j => basisKernel (rank n) (e n i) (e n j))).PosSemidef :=
    RiemannResearch.Analysis.ProjectionDPP.principal_posSemidef
      (basisSpace (rank n)) countingBasis (e n)
  have hI (n : ℕ) : (1 - Matrix.of (fun i j => basisKernel (rank n) (e n i) (e n j))).PosSemidef := by
    apply RiemannResearch.Analysis.ProjectionDPP.identity_sub_principal_posSemidef
      (basisSpace (rank n)) countingBasis (e n)
    intro i j
    simp only [countingBasis_inner, (e n).injective.eq_iff]
  simpa only [Set.mem_ofPred_eq] using moving_window_count_mass_tendsto_poisson
    (fun n => basisLaw (rank n)) (fun _ ω => {i | ω i = true})
    (fun n => basisKernel (rank n)) (fun n => basisLaw_isDPP (rank n)) h e hQ hI
    rate hmean hsq k

theorem basisLaw_moving_window_vacancy_poisson
    (rank h : ℕ → ℕ) (e : (n : ℕ) → Fin (h n) ↪ ℕ) (rate : ℝ)
    (hmean : Tendsto (fun n => ∑ i, basisKernel (rank n) (e n i) (e n i))
      atTop (𝓝 rate))
    (hsq : Tendsto (fun n => ∑ i, ∑ j, basisKernel (rank n) (e n i) (e n j) ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun n => (basisLaw (rank n)).real {ω | ∀ i, ω (e n i) = false})
      atTop (𝓝 (Real.exp (-rate))) := by
  classical
  have ht := basisLaw_moving_window_count_poisson rank h e rate hmean hsq 0
  simpa using ht

theorem basisLaw_growing_window_count_poisson_of_budgets
    (ε : ℝ) (hε : 0 < ε) (hεthree : ε < 3 / 4)
    (rank x h : ℕ → ℕ) (hh : ∀ n, 0 < h n) (rate : ℝ)
    (hmean : Tendsto (fun n => ∑ i : Fin (h n),
      basisKernel (rank n) (x n + i) (x n + i)) atTop (𝓝 rate))
    (hcube : Tendsto (fun n => (rank n : ℝ) ^ 3 /
      ((x n + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0))
    (hbudget : Tendsto (fun n => (h n : ℝ) ^ (5 - 4 * ε) /
      ((x n + 1 : ℕ) : ℝ) ^ (4 - 4 * ε)) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n => (basisLaw (rank n)).real
      {ω | (Finset.univ.filter (fun i : Fin (h n) => ω (x n + i) = true)).card = k}) atTop
      (𝓝 (Real.exp (-rate) * rate ^ k / k.factorial)) := by
  exact basisLaw_moving_window_count_poisson rank h (fun n => consecutiveEmbedding (x n) (h n))
    rate hmean (basisKernel_growing_full_sq_tendsto ε hε hεthree rank x h hh rate hmean hcube hbudget) k

end RiemannResearch.RH.QDivisorDPP
