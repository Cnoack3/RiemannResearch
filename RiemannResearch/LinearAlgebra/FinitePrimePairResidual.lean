import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

An exact finite model/residual theorem, generalized to arbitrary background coefficients.
No arithmetic estimate, symmetry, positive definiteness, or zero hypothesis is used in
the decomposition. Diagonal coefficients are the actual squared centered coefficients.
-/

open scoped BigOperators

namespace RiemannResearch.LinearAlgebra

/-- A symmetric square sum splits into its exact diagonal and twice the strict
triangle. The proof uses induction only, avoiding unordered-pair infrastructure. -/
theorem symmetric_sum_range_diagonal_triangle (F : ℕ → ℕ → ℝ)
    (hF : ∀ i j, F i j = F j i) (N : ℕ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, F i j) =
      (∑ i ∈ Finset.range N, F i i) +
        2 * ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range j, F i j := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
      have hrow : (∑ i ∈ Finset.range N, F N i) =
          ∑ i ∈ Finset.range N, F i N := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hF N i
      rw [hrow, ih]
      ring

/-- The exact diagonal/strict-triangle decomposition for an arbitrary finite
ordered index set. No replacement of the set by a range is required. -/
theorem symmetric_sum_finset_diagonal_triangle {α : Type*} [LinearOrder α]
    (s : Finset α) (F : α → α → ℝ) (hF : ∀ i j, F i j = F j i) :
    (∑ i ∈ s, ∑ j ∈ s, F i j) =
      (∑ i ∈ s, F i i) +
        2 * ∑ j ∈ s, ∑ i ∈ s with i < j, F i j := by
  have hsplit : (∑ i ∈ s, ∑ j ∈ s, F i j) =
      (∑ i ∈ s, ∑ j ∈ s, if j = i then F i j else 0) +
        (∑ i ∈ s, ∑ j ∈ s, if i < j then F i j else 0) +
        (∑ i ∈ s, ∑ j ∈ s, if j < i then F i j else 0) := by
    calc
      (∑ i ∈ s, ∑ j ∈ s, F i j) =
          ∑ i ∈ s, ∑ j ∈ s,
            ((if j = i then F i j else 0) +
              (if i < j then F i j else 0) +
              (if j < i then F i j else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rcases lt_trichotomy i j with hij | hij | hji
        · simp [hij, ne_of_gt hij, not_lt_of_ge hij.le]
        · subst j
          simp
        · simp [hji, ne_of_lt hji, not_lt_of_ge hji.le]
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hdiag : (∑ i ∈ s, ∑ j ∈ s, if j = i then F i j else 0) =
      ∑ i ∈ s, F i i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.sum_ite_eq', if_pos hi]
  have hupper : (∑ i ∈ s, ∑ j ∈ s, if i < j then F i j else 0) =
      ∑ j ∈ s, ∑ i ∈ s, if i < j then F i j else 0 := Finset.sum_comm
  have hlower : (∑ i ∈ s, ∑ j ∈ s, if j < i then F i j else 0) =
      ∑ j ∈ s, ∑ i ∈ s, if i < j then F i j else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j < i
    · simp only [if_pos hji]
      exact hF i j
    · simp only [if_neg hji]
  simp only [Finset.sum_filter]
  rw [hsplit, hdiag, hupper, hlower]
  ring

section
variable {ι : Type*} [DecidableEq ι]

noncomputable def centeredKernelEnergy (s : Finset ι)
    (v b : ι → ℝ) (K : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, (v i - b i) * (v j - b j) * K i j

noncomputable def centeredKernelModel (s : Finset ι)
    (v b : ι → ℝ) (S K : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s,
    (if i = j then (v i - b i) ^ 2 else S i j - b i * b j) * K i j

noncomputable def centeredKernelResidual (s : Finset ι)
    (v b : ι → ℝ) (S K : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s,
    (if i = j then 0 else
      v i * v j - v i * b j - b i * v j + 2 * b i * b j - S i j) * K i j

theorem centered_pair_exact (v μ b c S : ℝ) :
    (v - b) * (μ - c) =
      (S - b * c) + (v * μ - v * c - b * μ + 2 * b * c - S) := by
  ring

/-- Exact cancellation with actual diagonal and both singleton terms retained.
The theorem is stronger than the symmetric unit-background specialization. -/
theorem centeredKernelEnergy_eq_model_add_residual (s : Finset ι)
    (v b : ι → ℝ) (S K : ι → ι → ℝ) :
    centeredKernelEnergy s v b K =
      centeredKernelModel s v b S K + centeredKernelResidual s v b S K := by
  simp only [centeredKernelEnergy, centeredKernelModel, centeredKernelResidual,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j
    simp [pow_two]
  · simp only [if_neg hij]
    ring

/-- Unit-background arithmetic residual: the +2 is essential. -/
theorem unitBackground_residual_coefficient (v μ S : ℝ) :
    (v - 1) * (μ - 1) - (S - 1) = v * μ - v - μ + 2 - S := by
  ring

/-- An upper estimate on the whole signed residual suffices; no pairwise absolute
estimate is required. The same assumptions also give its automatic lower estimate. -/
theorem centeredKernelResidual_upper_suffices (s : Finset ι)
    (v b : ι → ℝ) (S K : ι → ι → ℝ) (L C B : ℝ)
    (hE : 0 ≤ centeredKernelEnergy s v b K)
    (hM : |centeredKernelModel s v b S K| ≤ C * L)
    (hR : centeredKernelResidual s v b S K ≤ B * L) :
    centeredKernelEnergy s v b K ≤ (C + B) * L ∧
      -(C * L) ≤ centeredKernelResidual s v b S K := by
  have hid := centeredKernelEnergy_eq_model_add_residual s v b S K
  have hm := abs_le.mp hM
  constructor <;> nlinarith [hm.1, hm.2]

theorem centeredKernelResidual_upper_of_energy_upper (s : Finset ι)
    (v b : ι → ℝ) (S K : ι → ι → ℝ) (L C B : ℝ)
    (hM : |centeredKernelModel s v b S K| ≤ C * L)
    (hE : centeredKernelEnergy s v b K ≤ B * L) :
    centeredKernelResidual s v b S K ≤ (C + B) * L := by
  have hid := centeredKernelEnergy_eq_model_add_residual s v b S K
  have hm := abs_le.mp hM
  nlinarith [hm.1, hm.2]

/-- A negative model charge forces a positive actual residual charge,
independently of RH or any arithmetic pair estimate. -/
theorem centeredKernelResidual_lower_of_negative_model (s : Finset ι)
    (v b : ι → ℝ) (S K : ι → ι → ℝ) (L C B : ℝ)
    (hE : 0 ≤ centeredKernelEnergy s v b K)
    (hM : centeredKernelModel s v b S K ≤ -C * L + B) :
    C * L - B ≤ centeredKernelResidual s v b S K := by
  have hid := centeredKernelEnergy_eq_model_add_residual s v b S K
  nlinarith

section Gram
variable {τ : Type*} [DecidableEq τ]

noncomputable def finiteWeightedGram (r : Finset τ) (w : τ → ℝ)
    (W : ι → τ → ℝ) (i j : ι) : ℝ :=
  ∑ t ∈ r, w t * W i t * W j t

theorem finiteWeightedGram_symmetric (r : Finset τ) (w : τ → ℝ)
    (W : ι → τ → ℝ) (i j : ι) :
    finiteWeightedGram r w W i j = finiteWeightedGram r w W j i := by
  unfold finiteWeightedGram
  apply Finset.sum_congr rfl
  intro t ht
  ring

/-- The actual matrix quadratic is exactly a finite weighted sum of squares.
All matrix entries, cross terms, and centered coefficients are preserved. -/
theorem centeredKernelEnergy_weightedGram_eq (s : Finset ι) (r : Finset τ)
    (v b : ι → ℝ) (w : τ → ℝ) (W : ι → τ → ℝ) :
    centeredKernelEnergy s v b (finiteWeightedGram r w W) =
      ∑ t ∈ r, w t * (∑ i ∈ s, (v i - b i) * W i t) ^ 2 := by
  unfold centeredKernelEnergy finiteWeightedGram
  calc
    (∑ i ∈ s, ∑ j ∈ s,
        (v i - b i) * (v j - b j) *
          ∑ t ∈ r, w t * W i t * W j t) =
      ∑ i ∈ s, ∑ j ∈ s, ∑ t ∈ r,
        w t * ((v i - b i) * W i t) * ((v j - b j) * W j t) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring
    _ = ∑ i ∈ s, ∑ t ∈ r, ∑ j ∈ s,
        w t * ((v i - b i) * W i t) * ((v j - b j) * W j t) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Finset.sum_comm
    _ = ∑ t ∈ r, ∑ i ∈ s, ∑ j ∈ s,
        w t * ((v i - b i) * W i t) * ((v j - b j) * W j t) :=
          Finset.sum_comm
    _ = ∑ t ∈ r, w t * (∑ i ∈ s, (v i - b i) * W i t) ^ 2 := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [pow_two]
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring

theorem centeredKernelEnergy_weightedGram_nonnegative (s : Finset ι) (r : Finset τ)
    (v b : ι → ℝ) (w : τ → ℝ) (W : ι → τ → ℝ)
    (hw : ∀ t ∈ r, 0 ≤ w t) :
    0 ≤ centeredKernelEnergy s v b (finiteWeightedGram r w W) := by
  rw [centeredKernelEnergy_weightedGram_eq]
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (hw t ht) (sq_nonneg _)

end Gram

end
end RiemannResearch.LinearAlgebra
