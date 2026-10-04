import RiemannResearch.Analysis.MarkedFourierTail
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Deterministic Gaussian cell geometry, with all occurrences retained

Source: user manuscript Prime_Phases_Agenda_Proof_Attempts.tex, Gaussian
spectral-window argument. This module formalizes only deterministic geometry.
The zero-copy index set may have repeated positions; neither diagonal copies
nor different zeros at the same height are removed. No Tsang estimate is assumed.
-/
noncomputable section
open scoped BigOperators ComplexConjugate
open Complex

namespace RiemannResearch.Analysis.GaussianCellGeometry

/-- A summable integer envelope whose total mass is exactly three. -/
def geometric (z : ℤ) : ℝ := (1 / 2 : ℝ) ^ z.natAbs

/-- A deliberately generous universal envelope for points in unit cells. -/
def cellKernel (a b : ℤ) : ℝ := 2 * geometric (a - b)

theorem geometric_nonneg (z : ℤ) : 0 ≤ geometric z := by unfold geometric; positivity

theorem summable_geometric : Summable geometric := by
  have hn : Summable (fun n : ℕ => geometric (n : ℤ)) := by
    simpa only [geometric, Int.natAbs_natCast] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have hm : Summable (fun n : ℕ => geometric (-(n : ℤ))) := by
    simpa only [geometric, Int.natAbs_neg, Int.natAbs_natCast] using hn
  exact Summable.of_nat_of_neg hn hm

theorem tsum_geometric : (∑' z : ℤ, geometric z) = 3 := by
  have hn : Summable (fun n : ℕ => geometric (n : ℤ)) := by
    simpa only [geometric, Int.natAbs_natCast] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  have hm : Summable (fun n : ℕ => geometric (-(n : ℤ))) := by
    simpa only [geometric, Int.natAbs_neg, Int.natAbs_natCast] using hn
  rw [Summable.tsum_of_nat_of_neg hn hm]
  simp only [geometric, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_zero, pow_zero]
  rw [tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)]
  norm_num

theorem cellKernel_nonneg (a b : ℤ) : 0 ≤ cellKernel a b := by
  exact mul_nonneg (by norm_num) (geometric_nonneg _)

theorem cellKernel_symmetric (a b : ℤ) : cellKernel a b = cellKernel b a := by
  have h : a - b = -(b - a) := by ring
  simp only [cellKernel, geometric, h, Int.natAbs_neg]

/-- Every finite integer row has an absolute bound independent of its location. -/
theorem cellKernel_row_le (s : Finset ℤ) (a : ℤ) :
    (∑ b ∈ s, cellKernel a b) ≤ 6 := by
  classical
  have hi : Function.Injective (fun b : ℤ => a - b) := by
    intro b c h
    change a - b = a - c at h
    omega
  calc
    _ = 2 * ∑ b ∈ s, geometric (a - b) := by simp only [cellKernel, Finset.mul_sum]
    _ = 2 * ∑ z ∈ s.image (fun b => a - b), geometric z := by
      rw [Finset.sum_image hi.injOn]
    _ ≤ 2 * ∑' z : ℤ, geometric z := mul_le_mul_of_nonneg_left
      (summable_geometric.sum_le_tsum _ (fun z _ => geometric_nonneg z)) (by norm_num)
    _ = 6 := by rw [tsum_geometric]; norm_num

/-- Occupancy counts occurrences, including repeated positions. -/
def occupancy {ι : Type*} (s : Finset ι) (cell : ι → ℤ) (a : ℤ) : ℝ :=
  ((s.filter (fun i => cell i = a)).card : ℝ)

/-- Exact finite fiber grouping; the complete index set is retained. -/
theorem sum_by_cells {ι : Type*} (s : Finset ι) (cell : ι → ℤ) (F : ℤ → ℝ) :
    (∑ i ∈ s, F (cell i)) =
      ∑ a ∈ s.image cell, occupancy s cell a * F a := by
  classical
  have hmap : ∀ i ∈ s, cell i ∈ s.image cell := fun i hi => Finset.mem_image_of_mem cell hi
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ i ∈ s with cell i = a, F (cell i)) = ∑ i ∈ s with cell i = a, F a := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := by simp only [occupancy, Finset.sum_const, nsmul_eq_mul]

/-- The exact pair matrix after grouping every copy into its microscopic cell. -/
theorem pair_sum_by_cells {ι : Type*} (s : Finset ι) (cell : ι → ℤ)
    (K : ℤ → ℤ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, K (cell i) (cell j)) =
      ∑ a ∈ s.image cell, ∑ b ∈ s.image cell,
        K a b * occupancy s cell a * occupancy s cell b := by
  classical
  calc
    _ = ∑ i ∈ s, ∑ b ∈ s.image cell, occupancy s cell b * K (cell i) b := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_by_cells s cell (K (cell i))
    _ = ∑ a ∈ s.image cell, occupancy s cell a *
        (∑ b ∈ s.image cell, occupancy s cell b * K a b) :=
      sum_by_cells s cell (fun a => ∑ b ∈ s.image cell, occupancy s cell b * K a b)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- The complete copy pair mass is controlled by the square occupancies. -/
theorem cell_pair_mass_le {ι : Type*} (s : Finset ι) (cell : ι → ℤ) :
    (∑ i ∈ s, ∑ j ∈ s, cellKernel (cell i) (cell j)) ≤
      6 * ∑ a ∈ s.image cell, occupancy s cell a ^ 2 := by
  classical
  rw [pair_sum_by_cells]
  exact MarkedFourierTail.symmetric_kernel_quadratic_le_row_bound
    (s.image cell) (occupancy s cell) cellKernel 6
    (fun a _ b _ => cellKernel_nonneg a b)
    (fun a _ b _ => cellKernel_symmetric a b)
    (fun a _ => cellKernel_row_le (s.image cell) a)

private theorem exp_neg_nat_le (n : ℕ) :
    Real.exp (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ n := by
  have hhalf : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp 1
      norm_num at h
      exact h
    have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg (-1))
    rw [← Real.exp_add] at hm
    norm_num at hm
    linarith
  calc
    _ = Real.exp (-1) ^ n := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) hhalf n

/-- Integer cell separation differs from point separation by at most one. -/
theorem floor_separation_le (x y : ℝ) :
    (((Int.floor x - Int.floor y).natAbs : ℕ) : ℝ) ≤ |x - y| + 1 := by
  rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
  apply abs_le.mpr
  have hfx := Int.floor_le x
  have hfy := Int.floor_le y
  have htx := Int.lt_floor_add_one x
  have hty := Int.lt_floor_add_one y
  constructor
  · linarith [neg_le_abs (x - y)]
  · linarith [le_abs_self (x - y)]

/-- The Gaussian is bounded by the universally summable cell envelope. -/
theorem gaussian_le_cellKernel (x y : ℝ) :
    Real.exp (-(x - y) ^ 2) ≤ cellKernel (Int.floor x) (Int.floor y) := by
  let d : ℕ := (Int.floor x - Int.floor y).natAbs
  have hdist : (d : ℝ) ≤ |x - y| + 1 := floor_separation_le x y
  by_cases hd0 : d = 0
  · have hg : Real.exp (-(x - y) ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x - y)])
    have hd0' : (Int.floor x - Int.floor y).natAbs = 0 := hd0
    simp only [cellKernel, geometric, hd0', pow_zero, mul_one]
    linarith
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hd0
    have hnabs : (n : ℝ) ≤ |x - y| := by
      rw [hn] at hdist
      push_cast at hdist
      linarith
    have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases n with _ | n
      · simp
      · have hge : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        nlinarith
    have hsq := mul_le_mul hnabs hnabs (Nat.cast_nonneg n) (abs_nonneg (x - y))
    rw [← pow_two, ← pow_two, sq_abs] at hsq
    calc
      Real.exp (-(x - y) ^ 2) ≤ Real.exp (-(n : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ ≤ (1 / 2 : ℝ) ^ n := exp_neg_nat_le n
      _ = 2 * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
      _ = _ := by
        change 2 * (1 / 2 : ℝ) ^ (n + 1) = 2 * (1 / 2 : ℝ) ^ d
        rw [hn, Nat.succ_eq_add_one]

/-- A complete Gaussian copy matrix is controlled by squared unit-cell occupancies. -/
theorem gaussian_pair_mass_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, Real.exp (-(x i - x j) ^ 2)) ≤
      6 * ∑ a ∈ s.image (fun i => Int.floor (x i)),
        occupancy s (fun i => Int.floor (x i)) a ^ 2 := by
  classical
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, cellKernel (Int.floor (x i)) (Int.floor (x j)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact gaussian_le_cellKernel (x i) (x j)
    _ ≤ _ := cell_pair_mass_le s (fun i => Int.floor (x i))


/-- Increasing the positive Gaussian coefficient preserves the same row budget. -/
theorem gaussian_coefficient_pair_mass_le {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) {c : ℝ} (hc : 1 ≤ c) :
    (∑ i ∈ s, ∑ j ∈ s, Real.exp (-c * (x i - x j) ^ 2)) ≤
      6 * ∑ a ∈ s.image (fun i => Int.floor (x i)),
        occupancy s (fun i => Int.floor (x i)) a ^ 2 := by
  classical
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, Real.exp (-(x i - x j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg (x i - x j))]
    _ ≤ _ := gaussian_pair_mass_le s x

/-- Bounded marks can be inserted without deleting any copy pair. This is a
norm estimate, not a signed-frequency cancellation theorem. -/
theorem marked_gaussian_pair_norm_le {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (left right : ι → ℂ) {c : ℝ} (hc : 1 ≤ c)
    (hleft : ∀ i ∈ s, ‖left i‖ ≤ 1) (hright : ∀ i ∈ s, ‖right i‖ ≤ 1) :
    ‖∑ i ∈ s, ∑ j ∈ s,
      (Real.exp (-c * (x i - x j) ^ 2) : ℂ) * left i * conj (right j)‖ ≤
      6 * ∑ a ∈ s.image (fun i => Int.floor (x i)),
        occupancy s (fun i => Int.floor (x i)) a ^ 2 := by
  classical
  have hterm (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      ‖(Real.exp (-c * (x i - x j) ^ 2) : ℂ) * left i * conj (right j)‖ ≤
        Real.exp (-c * (x i - x j) ^ 2) := by
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (Real.exp (-c * (x i - x j) ^ 2) * 1) * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hleft i hi) (Real.exp_nonneg _))
          (hright j hj) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ i ∈ s, ‖∑ j ∈ s,
        (Real.exp (-c * (x i - x j) ^ 2) : ℂ) * left i * conj (right j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        Real.exp (-c * (x i - x j) ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj => hterm i hi j hj))
    _ ≤ _ := gaussian_coefficient_pair_mass_le s x hc

end RiemannResearch.Analysis.GaussianCellGeometry
