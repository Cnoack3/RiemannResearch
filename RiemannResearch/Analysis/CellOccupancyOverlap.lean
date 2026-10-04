import RiemannResearch.Analysis.GaussianCellGeometry

/-!
# Exact same-cell copy count and the sliding-window overlap budget

Source: user manuscript Prime_Phases_Agenda_Proof_Attempts.tex, the step
from microscopic count-square averages to squared cell occupancies.
These are deterministic finite identities. The integral identification and
actual Tsang second moment are separate providers.
-/
noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.GaussianCellGeometry

/-- Cell occupancy squares count exactly all ordered same-cell occurrence pairs. -/
theorem square_occupancy_eq_same_cell_pairs {ι : Type*} (s : Finset ι) (cell : ι → ℤ) :
    (∑ a ∈ s.image cell, occupancy s cell a ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, if cell i = cell j then (1 : ℝ) else 0 := by
  classical
  change (∑ a ∈ s.image cell, occupancy s cell a ^ 2) =
    ∑ i ∈ s, ∑ j ∈ s, (fun a b : ℤ => if a = b then (1 : ℝ) else 0)
      (cell i) (cell j)
  rw [pair_sum_by_cells s cell (fun a b : ℤ => if a = b then (1 : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro a ha
  simp [ha, pow_two]

/-- Points in the same half-open unit cell have separation less than one. -/
theorem abs_sub_lt_one_of_floor_eq {x y : ℝ} (h : Int.floor x = Int.floor y) :
    |x - y| < 1 := by
  have hfx := Int.floor_le x
  have hfy := Int.floor_le y
  have htx := Int.lt_floor_add_one x
  have hty := Int.lt_floor_add_one y
  rw [h] at hfx htx
  apply abs_lt.mpr
  constructor <;> linarith

/-- Every same-cell pair has overlap at least one in a window of length two.
The full occurrence-pair sum on the right contains all diagonals and coincidences. -/
theorem square_occupancy_le_overlap_pairs {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∑ a ∈ s.image (fun i => Int.floor (x i)),
      occupancy s (fun i => Int.floor (x i)) a ^ 2) ≤
        ∑ i ∈ s, ∑ j ∈ s, max (2 - |x i - x j|) 0 := by
  classical
  rw [square_occupancy_eq_same_cell_pairs]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases h : Int.floor (x i) = Int.floor (x j)
  · rw [if_pos h]
    have hd := abs_sub_lt_one_of_floor_eq h
    exact (by linarith : (1 : ℝ) ≤ 2 - |x i - x j|).trans (le_max_left _ _)
  · rw [if_neg h]
    exact le_max_right _ _

end RiemannResearch.Analysis.GaussianCellGeometry
