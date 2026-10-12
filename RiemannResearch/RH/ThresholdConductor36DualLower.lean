import Mathlib.Algebra.BigOperators.Field
import RiemannResearch.Analysis.PeriodicSquareBound
import RiemannResearch.LinearAlgebra.WeightedDualCertificate
import RiemannResearch.RH.ThresholdInfiniteCertificate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# A rational dual obstruction for the full conductor-36 generator span

All twelve allowed generators (a in {2,3}, a*m dividing 36) occur below.
The dual annihilates them all; no assertion of numerical optimality is used.
The lower enclosure retains two exact progression weights. The remaining
positive tail is kept in the actual error and can only strengthen this lower bound.
-/

open scoped BigOperators
namespace RiemannResearch.RH.TwoSeedThreshold
open Pareto
open RiemannResearch.LinearAlgebra
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

/-- Two exact positive masses give a lower enclosure of each residue weight. -/
def residueLower36 (r : ℕ) : ℝ :=
  1 / ((r : ℝ) * (r + 1)) +
  1 / (((r : ℝ) + 36) * (r + 37))

def conductor36Generator (j : Fin 12) (k : ℕ) : ℝ :=
  certificateGenerator
    ((![(2 : ℕ), 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3]) j)
    ((![(1 : ℕ), 2, 3, 6, 9, 18, 1, 2, 3, 4, 6, 12]) j) k

/-- The twelve indexed generators exhaust every legal conductor-36 pair. -/
theorem conductor36Generator_exhaustive (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hm : 0 < m) (hd : a*m ∣ 36) :
    ∃ j : Fin 12, certificateGenerator a m = conductor36Generator j := by
  have ham : a*m ≤ 36 := Nat.le_of_dvd (by norm_num) hd
  rcases ha with rfl | rfl
  · have hmle : m ≤ 18 := by omega
    interval_cases m <;> norm_num at hd
    all_goals first
      | exact ⟨(0 : Fin 12), rfl⟩
      | exact ⟨(1 : Fin 12), rfl⟩
      | exact ⟨(2 : Fin 12), rfl⟩
      | exact ⟨(3 : Fin 12), rfl⟩
      | exact ⟨(4 : Fin 12), rfl⟩
      | exact ⟨(5 : Fin 12), rfl⟩
  · have hmle : m ≤ 12 := by omega
    interval_cases m <;> norm_num at hd
    all_goals first
      | exact ⟨(6 : Fin 12), rfl⟩
      | exact ⟨(7 : Fin 12), rfl⟩
      | exact ⟨(8 : Fin 12), rfl⟩
      | exact ⟨(9 : Fin 12), rfl⟩
      | exact ⟨(10 : Fin 12), rfl⟩
      | exact ⟨(11 : Fin 12), rfl⟩

def conductor36Combination (c : Fin 12 → ℝ) (k : ℕ) : ℝ :=
  ∑ j : Fin 12, c j * conductor36Generator j k

private def dualNumeratorInt36 (r : Fin 36) : ℤ :=
  let blocks : Fin 6 → Fin 6 → ℤ :=
    ![![372518, 51303, 2225, 214736, -170013, 103972],
    ![-91716, -11112, 33402, 23344, -54630, 53668],
    ![-8292, -9495, -9643, 8459, -25907, 22237],
    ![-7201, 4797, 3702, 2412, -17157, 12553],
    ![-5021, -5416, 676, 6840, -6372, 6079],
    ![-5628, -427, -712, -1131, -10231, 9410]]
  blocks
    ⟨r.val / 6, by have hr := r.isLt; omega⟩
    ⟨r.val % 6, Nat.mod_lt _ (by norm_num)⟩

private def dualNumerator36 (r : Fin 36) : ℝ :=
  (dualNumeratorInt36 r : ℝ)

private def dual36 (r : Fin 36) : ℝ :=
  dualNumerator36 r / 10000000

private def dualLowerNumerator36 (r : Fin 36) : ℝ :=
  let blocks : Fin 6 → Fin 6 → ℝ :=
    ![![71732149, 10103316, 444410, 33836002, -42525445, 16357313],
    ![-22918404, -2308184, 5718114, 4098385, -14647698, 6519884],
    ![-1774886, -2073921, -2133250, 1514654, -7036812, 2930892],
    ![-1615606, 873990, 684847, 456754, -4837090, 1698297],
    ![-1144035, -1257748, 132290, 1050143, -1568083, 931844],
    ![-1383629, -86972, -147016, -238482, -3104289, 941009]]
  blocks
    ⟨r.val / 6, by have hr := r.isLt; omega⟩
    ⟨r.val % 6, Nat.mod_lt _ (by norm_num)⟩

private def dualLowerCap36 (r : Fin 36) : ℝ :=
  dualLowerNumerator36 r / 1000000000

/-- Integer values of the unchanged real generators. -/
private def conductor36GeneratorInt (j : Fin 12) (k : ℕ) : ℤ :=
  let a : ℕ := ((![(2 : ℕ), 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3]) j)
  let m : ℕ := ((![(1 : ℕ), 2, 3, 6, 9, 18, 1, 2, 3, 4, 6, 12]) j)
  ((k % (a*m) : ℕ) : ℤ) - ((k % m : ℕ) : ℤ)

private theorem conductor36Generator_eq_int (j : Fin 12) (k : ℕ) :
    conductor36Generator j k = (conductor36GeneratorInt j k : ℝ) := by
  simp only [conductor36Generator, certificateGenerator, conductor36GeneratorInt,
    Int.cast_sub, Int.cast_natCast]

/-- A finite integer identity, checked by kernel reduction of decidable equality. -/
private theorem dualNumeratorInt36_annihilates_generator (j : Fin 12) :
    (∑ r : Fin 36, dualNumeratorInt36 r * conductor36GeneratorInt j (r.val+1)) = 0 := by
  fin_cases j <;> decide

private theorem dualNumerator36_annihilates_generator (j : Fin 12) :
    (∑ r : Fin 36, dualNumerator36 r * conductor36Generator j (r.val+1)) = 0 := by
  simp only [dualNumerator36, conductor36Generator_eq_int]
  exact_mod_cast (dualNumeratorInt36_annihilates_generator j)

private theorem dual36_annihilates_generator (j : Fin 12) :
    (∑ r : Fin 36, dual36 r * conductor36Generator j (r.val+1)) = 0 := by
  simp only [dual36, div_mul_eq_mul_div]
  rw [← Finset.sum_div, dualNumerator36_annihilates_generator, zero_div]

private theorem dual36_annihilates_combination (c : Fin 12 → ℝ) :
    (∑ r : Fin 36, dual36 r * conductor36Combination c (r.val+1)) = 0 := by
  unfold conductor36Combination
  calc
    _ = ∑ r : Fin 36, ∑ j : Fin 12,
        c j * (dual36 r * conductor36Generator j (r.val+1)) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j : Fin 12, ∑ r : Fin 36,
        c j * (dual36 r * conductor36Generator j (r.val+1)) := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin 12, c j *
        (∑ r : Fin 36, dual36 r * conductor36Generator j (r.val+1)) := by
      simp only [Finset.mul_sum]
    _ = 0 := by simp only [dual36_annihilates_generator, mul_zero, Finset.sum_const_zero]

private def dualLowerNumeratorNat36 (k : ℕ) : ℝ :=
  dualLowerNumerator36 ⟨k % 36, Nat.mod_lt _ (by norm_num)⟩

private theorem dualLowerNumeratorNat36_sum_split (offset n m : ℕ) :
    (∑ r : Fin (n+m), dualLowerNumeratorNat36 (offset+r.val)) =
      (∑ r : Fin n, dualLowerNumeratorNat36 (offset+r.val)) +
        ∑ r : Fin m, dualLowerNumeratorNat36 ((offset+n)+r.val) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_natAdd, Fin.val_castAdd, Nat.add_assoc]

private theorem dualLowerNumeratorNat36_row0 :
    (∑ r : Fin 6, dualLowerNumeratorNat36 (0+r.val)) = (89947745 : ℝ) := by
  norm_num [Fin.sum_univ_succ, dualLowerNumeratorNat36, dualLowerNumerator36]

private theorem dualLowerNumeratorNat36_row1 :
    (∑ r : Fin 6, dualLowerNumeratorNat36 (6+r.val)) = (-23537903 : ℝ) := by
  norm_num [Fin.sum_univ_succ, dualLowerNumeratorNat36, dualLowerNumerator36]

private theorem dualLowerNumeratorNat36_row2 :
    (∑ r : Fin 6, dualLowerNumeratorNat36 (12+r.val)) = (-8573323 : ℝ) := by
  norm_num [Fin.sum_univ_succ, dualLowerNumeratorNat36, dualLowerNumerator36]

private theorem dualLowerNumeratorNat36_row3 :
    (∑ r : Fin 6, dualLowerNumeratorNat36 (18+r.val)) = (-2738808 : ℝ) := by
  norm_num [Fin.sum_univ_succ, dualLowerNumeratorNat36, dualLowerNumerator36]

private theorem dualLowerNumeratorNat36_row4 :
    (∑ r : Fin 6, dualLowerNumeratorNat36 (24+r.val)) = (-1855589 : ℝ) := by
  norm_num [Fin.sum_univ_succ, dualLowerNumeratorNat36, dualLowerNumerator36]

private theorem dualLowerNumeratorNat36_row5 :
    (∑ r : Fin 6, dualLowerNumeratorNat36 (30+r.val)) = (-4019379 : ℝ) := by
  norm_num [Fin.sum_univ_succ, dualLowerNumeratorNat36, dualLowerNumerator36]

private theorem dualLowerNumerator36_sum :
    (∑ r : Fin 36, dualLowerNumerator36 r) = (49222743 : ℝ) := by
  have he : (∑ r : Fin 36, dualLowerNumerator36 r) =
      ∑ r : Fin 36, dualLowerNumeratorNat36 (0+r.val) := by
    apply Finset.sum_congr rfl
    intro r _
    unfold dualLowerNumeratorNat36
    congr 1
    apply Fin.ext
    simp [Nat.mod_eq_of_lt r.isLt]
  rw [he]
  rw [dualLowerNumeratorNat36_sum_split 0 6 30, dualLowerNumeratorNat36_row0]
  rw [dualLowerNumeratorNat36_sum_split 6 6 24, dualLowerNumeratorNat36_row1]
  rw [dualLowerNumeratorNat36_sum_split 12 6 18, dualLowerNumeratorNat36_row2]
  rw [dualLowerNumeratorNat36_sum_split 18 6 12, dualLowerNumeratorNat36_row3]
  rw [dualLowerNumeratorNat36_sum_split 24 6 6, dualLowerNumeratorNat36_row4]
  rw [dualLowerNumeratorNat36_row5]
  norm_num

private theorem dual36_lower_certificate :
    (49 : ℝ) / 1000 <
      ∑ r : Fin 36, (2 * dual36 r - (dual36 r)^2 / residueLower36 (r.val+1)) := by
  have h (r : Fin 36) : dualLowerCap36 r ≤
      2 * dual36 r - (dual36 r)^2 / residueLower36 (r.val+1) := by
    fin_cases r <;> norm_num [dualLowerCap36, dualLowerNumerator36, dual36, dualNumerator36, dualNumeratorInt36, residueLower36]
  apply lt_of_lt_of_le _ (Finset.sum_le_sum (fun r _ => h r))
  simp only [dualLowerCap36]
  rw [← Finset.sum_div, dualLowerNumerator36_sum]
  norm_num

/-- Every combination of all twelve conductor-36 legal generators has error > .049
for every true weight vector dominating the two retained progression terms. -/
theorem conductor36_error_gt_of_weights (c : Fin 12 → ℝ)
    (w : Fin 36 → ℝ) (hw : ∀ r, residueLower36 (r.val+1) ≤ w r) :
    (49 : ℝ) / 1000 <
      ∑ r : Fin 36, w r * (1-conductor36Combination c (r.val+1))^2 := by
  apply lt_of_lt_of_le dual36_lower_certificate
  apply le_trans (weighted_error_lower_of_dual
    (fun r => residueLower36 (r.val+1)) dual36
    (fun r => conductor36Combination c (r.val+1))
    (by intro r; unfold residueLower36; positivity)
    (dual36_annihilates_combination c))
  exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hw r) (sq_nonneg _)

theorem residueLower36_le_progressionWeight (r : ℕ) :
    residueLower36 r ≤ progressionWeight 36 r := by
  have he : residueLower36 r = positiveWeight r + positiveWeight (r+36) := by
    simp only [residueLower36, positiveWeight, Nat.cast_add, Nat.cast_ofNat]
    congr 1 <;> congr 1 <;> ring
  rw [he, progressionWeight_split 36 r (by norm_num),
    progressionWeight_split 36 (r+36) (by norm_num)]
  have hn := progressionWeight_nonneg 36 (r+36+36)
  linarith

theorem conductor36Generator_periodic (j : Fin 12) (k : ℕ) :
    conductor36Generator j (k+36) = conductor36Generator j k := by
  have h1 : (k+36)%1 = k%1 := by omega
  have h2 : (k+36)%2 = k%2 := by omega
  have h3 : (k+36)%3 = k%3 := by omega
  have h4 : (k+36)%4 = k%4 := by omega
  have h6 : (k+36)%6 = k%6 := by omega
  have h9 : (k+36)%9 = k%9 := by omega
  have h12 : (k+36)%12 = k%12 := by omega
  have h18 : (k+36)%18 = k%18 := by omega
  have h36 : (k+36)%36 = k%36 := by omega
  fin_cases j <;>
    simp [conductor36Generator, certificateGenerator, h1, h2, h3, h4, h6, h9, h12, h18, h36]

theorem conductor36Combination_periodic (c : Fin 12 → ℝ) :
    Function.Periodic (conductor36Combination c) 36 := by
  intro k
  simp only [conductor36Combination, conductor36Generator_periodic]

theorem conductor36Combination_error_bound (c : Fin 12 → ℝ) (k : ℕ) :
    (1-conductor36Combination c k)^2 ≤
      ∑ r : Fin 36, (1-conductor36Combination c r.val)^2 := by
  exact RiemannResearch.Analysis.periodic_square_error_bound
    (conductor36Combination c) 36 (by norm_num) (conductor36Combination_periodic c) k

theorem conductor36Combination_error_summable (c : Fin 12 → ℝ) :
    Summable (fun k : ℕ => positiveWeight (k+1) *
      (1-conductor36Combination c (k+1))^2) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k+1)) :=
    positiveWeight_summable.comp_injective (by intro a b h; exact Nat.add_right_cancel h)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (conductor36Combination_error_bound c _)
      (positiveWeight_nonneg _))
    (hw.mul_right _)

theorem conductor36Combination_add_multiple (c : Fin 12 → ℝ) (r j : ℕ) :
    conductor36Combination c (r+36*j) = conductor36Combination c r := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : r+36*(j+1) = (r+36*j)+36 := by omega
    rw [h, conductor36Combination_periodic c, ih]

theorem conductor36Combination_exact_error (c : Fin 12 → ℝ) :
    (∑' k : ℕ, positiveWeight (k+1) * (1-conductor36Combination c (k+1))^2) =
      ∑ r : Fin 36, progressionWeight 36 (r.val+1) *
        (1-conductor36Combination c (r.val+1))^2 := by
  rw [Nat.sumByResidueClasses (conductor36Combination_error_summable c) 36]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ∑' j : ℕ, positiveWeight ((r.val+1)+36*j) *
        (1-conductor36Combination c (r.val+1))^2 := by
      apply tsum_congr
      intro j
      have h : r.val+36*j+1 = (r.val+1)+36*j := by omega
      rw [h, conductor36Combination_add_multiple]
    _ = _ := by rw [tsum_mul_right]; rfl

/-- Unconditional full infinite-error lower bound for the conductor-36 legal span. -/
theorem conductor36Combination_full_error_gt (c : Fin 12 → ℝ) :
    (49 : ℝ) / 1000 <
      ∑' k : ℕ, positiveWeight (k+1) * (1-conductor36Combination c (k+1))^2 := by
  rw [conductor36Combination_exact_error]
  exact conductor36_error_gt_of_weights c _ fun r =>
    residueLower36_le_progressionWeight (r.val+1)

end
end RiemannResearch.RH.TwoSeedThreshold
