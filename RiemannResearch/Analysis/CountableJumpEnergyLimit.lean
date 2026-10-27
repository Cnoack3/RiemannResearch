/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CountableJumpEnergy
import Mathlib.Topology.Order.OrderClosed

/-!
# Cofinal finite-grid bounds control a countable jump energy

For a fixed flow with finite individual coefficients, every finite-grid
energy is continuous under pointwise convergence. A common bound recurring
arbitrarily late on each grid therefore controls the complete limiting form.
The recurring indices may depend on the grid; no control of the complete
energies of the approximants is assumed. The intended consumer is the
actual moving squarefree correction from the user's resampling agenda.
-/

noncomputable section
open Filter
open scoped Topology BigOperators ENNReal
namespace RiemannResearch.Analysis.CountableJumpEnergyLimit
open CountableJumpEnergy

variable {α ι : Type*}

theorem finiteSetEnergy_tendsto
    (W : α → α → ℝ≥0∞) (hW : ∀ x y, W x y ≠ ⊤)
    (g : ι → α → ℝ) (f : α → ℝ) (l : Filter ι)
    (hg : ∀ x, Tendsto (fun i => g i x) l (𝓝 (f x))) (S : Finset α) :
    Tendsto (fun i => finiteSetEnergy W (g i) S) l
      (𝓝 (finiteSetEnergy W f S)) := by
  unfold finiteSetEnergy
  apply tendsto_finsetSum
  intro x hx
  apply tendsto_finsetSum
  intro y hy
  apply (ENNReal.continuous_const_mul (hW x y)).continuousAt.tendsto.comp
  apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
  exact (((hg x).sub (hg y)).pow 2).div_const 2

/-- It suffices that each fixed grid obey the same bound frequently; a single
subsequence controlling all grids is not a premise. -/
theorem countableJumpEnergy_le_of_frequently_finiteSetEnergy_le
    (W : α → α → ℝ≥0∞) (hW : ∀ x y, W x y ≠ ⊤)
    (g : ι → α → ℝ) (f : α → ℝ) (l : Filter ι)
    (hg : ∀ x, Tendsto (fun i => g i x) l (𝓝 (f x))) (C : ℝ≥0∞)
    (hC : ∀ S : Finset α, ∃ᶠ i in l, finiteSetEnergy W (g i) S ≤ C) :
    countableJumpEnergy W f ≤ C := by
  apply (countableJumpEnergy_le_iff W f C).mpr
  intro S
  exact le_of_tendsto_of_frequently (finiteSetEnergy_tendsto W hW g f l hg S) (hC S)

/-- Infinite limiting energy is already witnessed by eventual escape above
any finite threshold on one fixed finite grid. -/
theorem exists_finiteSetEnergy_eventually_gt_of_energy_eq_top
    (W : α → α → ℝ≥0∞) (hW : ∀ x y, W x y ≠ ⊤)
    (g : ι → α → ℝ) (f : α → ℝ) (l : Filter ι)
    (hg : ∀ x, Tendsto (fun i => g i x) l (𝓝 (f x)))
    (hE : countableJumpEnergy W f = ⊤) (M : ℝ≥0∞) (hM : M ≠ ⊤) :
    ∃ S : Finset α, ∀ᶠ i in l, M < finiteSetEnergy W (g i) S := by
  have hex : ∃ S : Finset α, M < finiteSetEnergy W f S := by
    by_contra h
    have hle : countableJumpEnergy W f ≤ M :=
      (countableJumpEnergy_le_iff W f M).mpr
        (fun S => le_of_not_gt (fun hS => h ⟨S, hS⟩))
    rw [hE] at hle
    exact hM (top_unique hle)
  obtain ⟨S, hS⟩ := hex
  exact ⟨S, (finiteSetEnergy_tendsto W hW g f l hg S).eventually (Ioi_mem_nhds hS)⟩

/-- Any physical head tending to infinity captures the divergence. No rate
comparison between approximation accuracy and head growth is needed. -/
theorem finiteSetEnergy_range_tendsto_top
    (W : ℕ → ℕ → ℝ≥0∞) (hW : ∀ x y, W x y ≠ ⊤)
    (g : ι → ℕ → ℝ) (f : ℕ → ℝ) (l : Filter ι)
    (hg : ∀ x, Tendsto (fun i => g i x) l (𝓝 (f x)))
    (hE : countableJumpEnergy W f = ⊤)
    (H : ι → ℕ) (hH : Tendsto H l atTop) :
    Tendsto (fun i => finiteSetEnergy W (g i) (Finset.range (H i))) l (𝓝 ⊤) := by
  classical
  apply ENNReal.tendsto_nhds_top
  intro M
  obtain ⟨S, hS⟩ := exists_finiteSetEnergy_eventually_gt_of_energy_eq_top
    W hW g f l hg hE (M : ℝ≥0∞) (by simp)
  have hhead : ∀ᶠ i in l, S.sup id + 1 ≤ H i :=
    hH.eventually (eventually_ge_atTop _)
  filter_upwards [hS, hhead] with i hi hHi
  apply hi.trans_le (finiteSetEnergy_mono W (g i) ?_)
  intro n hn
  apply Finset.mem_range.mpr
  exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)) hHi

end RiemannResearch.Analysis.CountableJumpEnergyLimit
