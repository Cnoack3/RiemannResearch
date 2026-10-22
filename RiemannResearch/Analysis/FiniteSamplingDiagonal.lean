/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field

/-!
# Diagonal selection for fixed-stage sampling limits

Source: elementary diagonal selection for the user-directed zero-ordinate
research program, 21 October 2026.

These are general filter and finite-cell lemmas. The convergence hypotheses
remain explicit: no statement about zeta-zero equidistribution is asserted.
The strictly increasing diagonal is nonquantitative. In particular, it supplies
no effective bound on the sample size as the stage or cell count grows.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.FiniteSamplingDiagonal

/-- Every stagewise eventual condition admits a strictly increasing diagonal.
The chosen sample size is at least the stage index. -/
theorem exists_strictMono_diagonal_of_eventually
    (P : ℕ → ℕ → Prop)
    (hP : ∀ j, ∀ᶠ n in atTop, P j n) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ (∀ j, j ≤ τ j) ∧ ∀ j, P j (τ j) := by
  classical
  have hex : ∀ j, ∃ N : ℕ, ∀ n ≥ N, P j n :=
    fun j => Filter.eventually_atTop.1 (hP j)
  let N : ℕ → ℕ := fun j => Classical.choose (hex j)
  have hN : ∀ j, ∀ n ≥ N j, P j n :=
    fun j => Classical.choose_spec (hex j)
  let τ : ℕ → ℕ :=
    Nat.rec (N 0) (fun j previous => max (N (j + 1)) (previous + 1))
  have hthreshold : ∀ j, N j ≤ τ j := by
    intro j
    cases j with
    | zero => exact le_rfl
    | succ j =>
        change N (j + 1) ≤ max (N (j + 1)) (τ j + 1)
        exact le_max_left _ _
  have hstep : ∀ j, τ j < τ (j + 1) := by
    intro j
    change τ j < max (N (j + 1)) (τ j + 1)
    exact lt_of_lt_of_le (Nat.lt_succ_self (τ j)) (le_max_right _ _)
  have hmono : StrictMono τ := strictMono_nat_of_lt_succ hstep
  have hindex : ∀ j, j ≤ τ j := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
        exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hstep j))
  exact ⟨τ, hmono, hindex, fun j => hN j (τ j) (hthreshold j)⟩

/-- Arbitrarily prescribed positive stagewise tolerances can be met along a
strictly increasing diagonal of fixed-stage limits. -/
theorem exists_strictMono_diagonal_abs_le
    (δ : ℕ → ℕ → ℝ) (ε : ℕ → ℝ)
    (hδ : ∀ j, Tendsto (δ j) atTop (𝓝 0))
    (hε : ∀ j, 0 < ε j) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ (∀ j, j ≤ τ j) ∧
      ∀ j, |δ j (τ j)| ≤ ε j := by
  have hsmall : ∀ j, ∀ᶠ n in atTop, |δ j n| ≤ ε j := by
    intro j
    have ht : Tendsto (fun n => |δ j n|) atTop (𝓝 (0 : ℝ)) := by
      simpa using (hδ j).abs
    have hlt : ∀ᶠ n in atTop, |δ j n| < ε j :=
      (tendsto_order.1 ht).2 (ε j) (hε j)
    exact hlt.mono fun _ hn => le_of_lt hn
  exact exists_strictMono_diagonal_of_eventually
    (fun j n => |δ j n| ≤ ε j) hsmall

/-- A finite collection of eventual statements holds simultaneously. This
elementary induction avoids any choice of a uniform-in-stage convergence rate. -/
theorem eventually_forall_finite_cells
    {ι : Type*} [Finite ι]
    (P : ι → ℕ → Prop)
    (hP : ∀ a, ∀ᶠ n in atTop, P a n) :
    ∀ᶠ n in atTop, ∀ a, P a n := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hfinite : ∀ s : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ s, P a n := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact Filter.Eventually.of_forall (by simp)
    | @insert a s ha ih =>
        refine ((hP a).and ih).mono ?_
        intro n hn b hb
        rcases Finset.mem_insert.1 hb with hba | hbs
        · subst b
          exact hn.1
        · exact hn.2 b hbs
  exact (hfinite Finset.univ).mono fun n hn a => hn a (Finset.mem_univ a)

/-- Pointwise convergence to zero over a finite cell set is eventually
uniform to every prescribed positive absolute tolerance. -/
theorem eventually_forall_abs_le_of_finite_tendsto
    {ι : Type*} [Finite ι]
    (δ : ι → ℕ → ℝ)
    (hδ : ∀ a, Tendsto (δ a) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ a, |δ a n| ≤ ε := by
  apply eventually_forall_finite_cells
  intro a
  have ht : Tendsto (fun n => |δ a n|) atTop (𝓝 (0 : ℝ)) := by
    simpa using (hδ a).abs
  exact ((tendsto_order.1 ht).2 ε hε).mono fun _ hn => le_of_lt hn

/-- Frequencies tending to the uniform value `1 / c` have uniformly small
relative cell errors, for the fixed finite cell set under consideration.
The constant `c` is normally the number of cells. -/
theorem eventually_forall_relative_frequency_error_le
    {ι : Type*} [Finite ι]
    (frequency : ℕ → ι → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hfrequency : ∀ a,
      Tendsto (fun n => frequency n a) atTop (𝓝 (1 / c)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ a, |c * frequency n a - 1| ≤ ε := by
  have hlimit : c * (1 / c) - 1 = (0 : ℝ) := by
    simp [div_eq_mul_inv, hc]
  apply eventually_forall_abs_le_of_finite_tendsto
    (fun a n => c * frequency n a - 1) _ hε
  intro a
  have ht : Tendsto (fun n => c * frequency n a - 1) atTop
      (𝓝 (c * (1 / c) - 1)) :=
    ((hfrequency a).const_mul c).sub tendsto_const_nhds
  simpa only [hlimit] using ht

/-- A diagonal may be chosen even when the finite cell set grows with the
stage. Only convergence at each fixed stage is assumed. -/
theorem exists_strictMono_diagonal_relative_frequency_error
    {ι : ℕ → Type*} [∀ j, Finite (ι j)]
    (frequency : (j : ℕ) → ℕ → ι j → ℝ)
    (c ε : ℕ → ℝ)
    (hc : ∀ j, c j ≠ 0) (hε : ∀ j, 0 < ε j)
    (hfrequency : ∀ j a,
      Tendsto (fun n => frequency j n a) atTop (𝓝 (1 / c j))) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ (∀ j, j ≤ τ j) ∧
      ∀ j a, |c j * frequency j (τ j) a - 1| ≤ ε j := by
  apply exists_strictMono_diagonal_of_eventually
    (fun j n => ∀ a, |c j * frequency j n a - 1| ≤ ε j)
  intro j
  exact eventually_forall_relative_frequency_error_le
    (frequency j) (c j) (hc j) (hfrequency j) (hε j)

end RiemannResearch.Analysis.FiniteSamplingDiagonal
