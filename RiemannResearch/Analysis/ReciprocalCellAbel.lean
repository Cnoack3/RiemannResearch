/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Exact reciprocal-cell Abel identities

The coefficients are those arising from compression of a Mellin kernel onto
the reciprocal cells `(1/(n+1), 1/n]`, with zero-based index `k = n - 1`.
All finite boundary terms are retained. The infinite theorems explicitly
require ordinary summability and the vanishing of the displayed boundary.

Mathematical source: the independent Q-witness refinement accompanying
J.-F. Burnol, arXiv:math/0103058 (2001). No historical novelty is claimed.
-/

open scoped BigOperators Topology
open Filter

noncomputable section
namespace RiemannResearch.Analysis.ReciprocalCellAbel

/-- The boundary factor at the cut immediately before cell `N`. -/
def boundaryFactor (N : ℕ) : ℝ := (N : ℝ) / ((N : ℝ) + 1)

/-- The coefficient created by Abel summation. -/
def cellWeight (k : ℕ) : ℝ :=
  1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))

/-- A reciprocal-cell energy envelope before Abel summation. -/
def cellDifference (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  boundaryFactor (k + 1) * (b k - b (k + 1))

theorem boundaryFactor_nonneg (N : ℕ) : 0 ≤ boundaryFactor N := by
  unfold boundaryFactor
  positivity

theorem boundaryFactor_le_one (N : ℕ) : boundaryFactor N ≤ 1 := by
  unfold boundaryFactor
  apply (div_le_one (by positivity : 0 < (N : ℝ) + 1)).2
  linarith

theorem cellWeight_nonneg (k : ℕ) : 0 ≤ cellWeight k := by
  unfold cellWeight
  positivity

theorem boundaryFactor_succ_sub (k : ℕ) :
    boundaryFactor (k + 1) - boundaryFactor k = cellWeight k := by
  simp only [boundaryFactor, cellWeight, Nat.cast_add, Nat.cast_one]
  field_simp [show (k : ℝ) + 1 ≠ 0 by positivity,
    show (k : ℝ) + 2 ≠ 0 by positivity,
    show (k : ℝ) + 1 + 1 ≠ 0 by positivity]
  <;> ring

/-- Summation by parts on an arbitrary consecutive block, with both
boundary terms. No monotonicity or decay assumption is used. -/
theorem sum_range_shifted_cellDifference (b : ℕ → ℝ) (M N : ℕ) :
    (∑ k ∈ Finset.range N, cellDifference b (M + k)) =
      (∑ k ∈ Finset.range N, cellWeight (M + k) * b (M + k)) +
        boundaryFactor M * b M -
        boundaryFactor (M + N) * b (M + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      simp only [cellDifference, Nat.add_succ]
      rw [← boundaryFactor_succ_sub (M + N)]
      ring

/-- The initial boundary is zero; the final boundary must be kept. -/
theorem sum_range_cellDifference (b : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, cellDifference b k) =
      (∑ k ∈ Finset.range N, cellWeight k * b k) -
        boundaryFactor N * b N := by
  simpa [boundaryFactor] using sum_range_shifted_cellDifference b 0 N

/-- The exact infinite Abel identity on an arbitrary tail. -/
theorem tsum_shifted_cellDifference (b : ℕ → ℝ) (M : ℕ)
    (he : Summable (fun k => cellDifference b (M + k)))
    (hw : Summable (fun k => cellWeight (M + k) * b (M + k)))
    (hboundary : Tendsto
      (fun N => boundaryFactor (M + N) * b (M + N)) atTop (𝓝 0)) :
    (∑' k, cellDifference b (M + k)) =
      (∑' k, cellWeight (M + k) * b (M + k)) + boundaryFactor M * b M := by
  apply tendsto_nhds_unique he.hasSum.tendsto_sum_nat
  have hlim := (hw.hasSum.tendsto_sum_nat.add_const
    (boundaryFactor M * b M)).sub hboundary
  simpa only [← sum_range_shifted_cellDifference, sub_zero] using hlim

/-- The exact infinite Abel identity from the first reciprocal cell. -/
theorem tsum_cellDifference (b : ℕ → ℝ)
    (he : Summable (cellDifference b))
    (hw : Summable (fun k => cellWeight k * b k))
    (hboundary : Tendsto (fun N => boundaryFactor N * b N) atTop (𝓝 0)) :
    (∑' k, cellDifference b k) = ∑' k, cellWeight k * b k := by
  have h := tsum_shifted_cellDifference b 0
    (by simpa using he) (by simpa using hw) (by simpa using hboundary)
  simpa [boundaryFactor] using h

/-- An antitone cell profile makes each envelope contribution nonnegative. -/
theorem cellDifference_nonneg {b : ℕ → ℝ} (hb : Antitone b) (k : ℕ) :
    0 ≤ cellDifference b k := by
  exact mul_nonneg (boundaryFactor_nonneg _) (sub_nonneg.mpr (hb (Nat.le_succ k)))

/-- A cell's envelope is at most its unweighted telescoping drop. -/
theorem cellDifference_le_drop {b : ℕ → ℝ} (hb : Antitone b) (k : ℕ) :
    cellDifference b k ≤ b k - b (k + 1) := by
  have hd : 0 ≤ b k - b (k + 1) := sub_nonneg.mpr (hb (Nat.le_succ k))
  have hh := mul_nonneg
    (sub_nonneg.mpr (boundaryFactor_le_one (k + 1))) hd
  unfold cellDifference
  nlinarith

/-- A finite tail certificate still retains the endpoint `b (M + N)`. -/
theorem sum_range_tail_le_drop {b : ℕ → ℝ} (hb : Antitone b) (M N : ℕ) :
    (∑ k ∈ Finset.range N, cellDifference b (M + k)) ≤ b M - b (M + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hd := cellDifference_le_drop hb (M + N)
      calc
        (∑ k ∈ Finset.range N, cellDifference b (M + k)) +
            cellDifference b (M + N) ≤
            (b M - b (M + N)) + (b (M + N) - b (M + N + 1)) :=
          add_le_add ih hd
        _ = b M - b (M + (N + 1)) := by
          simp only [Nat.add_assoc]
          ring

/-- The tail bound includes a nonzero limiting profile when one is present. -/
theorem tsum_tail_le_limit_drop {b : ℕ → ℝ} (hb : Antitone b) (M : ℕ) (ℓ : ℝ)
    (he : Summable (fun k => cellDifference b (M + k)))
    (hlimit : Tendsto (fun N => b (M + N)) atTop (𝓝 ℓ)) :
    (∑' k, cellDifference b (M + k)) ≤ b M - ℓ := by
  exact le_of_tendsto_of_tendsto he.hasSum.tendsto_sum_nat
    (tendsto_const_nhds.sub hlimit)
    (Filter.Eventually.of_forall (sum_range_tail_le_drop hb M))

/-- Exact preservation of any cellwise nonnegative Cauchy--Schwarz remainder.
No sign assumption is needed for the equality itself. -/
theorem finite_slack_identity (b energy slack : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (hcell : ∀ k, energy k + slack k = c * cellDifference b k) :
    (∑ k ∈ Finset.range N, energy k) +
      (∑ k ∈ Finset.range N, slack k) + c * boundaryFactor N * b N =
        c * (∑ k ∈ Finset.range N, cellWeight k * b k) := by
  have hs : (∑ k ∈ Finset.range N, (energy k + slack k)) =
      ∑ k ∈ Finset.range N, c * cellDifference b k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hcell k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_range_cellDifference] at hs
  nlinarith

/-- The full energy is the Abel envelope minus the complete slack. -/
theorem tsum_slack_identity (b energy slack : ℕ → ℝ) (c : ℝ)
    (henergy : Summable energy) (hslack : Summable slack)
    (he : Summable (cellDifference b))
    (hw : Summable (fun k => cellWeight k * b k))
    (hboundary : Tendsto (fun N => boundaryFactor N * b N) atTop (𝓝 0))
    (hcell : ∀ k, energy k + slack k = c * cellDifference b k) :
    (∑' k, energy k) = c * (∑' k, cellWeight k * b k) - ∑' k, slack k := by
  have hs : (∑' k, energy k) + (∑' k, slack k) =
      c * (∑' k, cellDifference b k) := by
    calc
      (∑' k, energy k) + (∑' k, slack k) = ∑' k, (energy k + slack k) :=
        (henergy.tsum_add hslack).symm
      _ = ∑' k, c * cellDifference b k := tsum_congr hcell
      _ = c * (∑' k, cellDifference b k) := by rw [tsum_mul_left]
  rw [tsum_cellDifference b he hw hboundary] at hs
  linarith

/-- The lower envelope can retain any certified prefix of the CS slack. -/
theorem tsum_energy_le_sub_finite_slack (b energy slack : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (henergy : Summable energy) (hslack : Summable slack)
    (he : Summable (cellDifference b))
    (hw : Summable (fun k => cellWeight k * b k))
    (hboundary : Tendsto (fun N => boundaryFactor N * b N) atTop (𝓝 0))
    (hcell : ∀ k, energy k + slack k = c * cellDifference b k)
    (hslack_nonneg : ∀ k, 0 ≤ slack k) :
    (∑' k, energy k) ≤ c * (∑' k, cellWeight k * b k) -
      ∑ k ∈ Finset.range N, slack k := by
  rw [tsum_slack_identity b energy slack c henergy hslack he hw hboundary hcell]
  exact sub_le_sub_left (Summable.sum_le_tsum (Finset.range N)
    (fun k hk => hslack_nonneg k) hslack) _

end RiemannResearch.Analysis.ReciprocalCellAbel
