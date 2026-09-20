import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Nonnegative determinant from a nonnegative real quadratic form

Elementary homotopy proof: strictly positive quadratic forms give invertibility;
the segment from the identity has positive determinant. Add epsilon times the
identity and pass to the limit for the nonstrict statement. Symmetry is not
assumed. Consumer: nonnegative exact configuration weights for DPP laws.
Source: elementary finite-dimensional argument developed for the user's DPP task;
no novelty claim is made.
-/

noncomputable section
open Filter
open scoped Topology

namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_ne_zero_of_quadratic_pos (M : Matrix n n ℝ)
    (hM : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x)) : M.det ≠ 0 := by
  intro h
  obtain ⟨x, hx, hMx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hp := hM x hx
  simp [hMx] at hp

theorem det_pos_of_quadratic_pos (M : Matrix n n ℝ)
    (hM : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x)) : 0 < M.det := by
  let A : ℝ → Matrix n n ℝ := fun t => (1 - t) • (1 : Matrix n n ℝ) + t • M
  have hA : Continuous (fun t => (A t).det) := by
    apply Continuous.matrix_det
    exact ((continuous_const.sub continuous_id).smul continuous_const).add
      (continuous_id.smul continuous_const)
  have hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (A t).det ≠ 0 := by
    intro t ht
    apply det_ne_zero_of_quadratic_pos
    intro x hx
    have hxx : 0 < x ⬝ᵥ x := by
      have hn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
      exact lt_of_le_of_ne hn (Ne.symm (dotProduct_self_eq_zero.not.mpr hx))
    have hm := hM x hx
    have he : x ⬝ᵥ ((A t) *ᵥ x) =
        (1 - t) * (x ⬝ᵥ x) + t * (x ⬝ᵥ (M *ᵥ x)) := by
      simp [A, Matrix.add_mulVec, Matrix.smul_mulVec,
        dotProduct_add, dotProduct_smul, smul_eq_mul]
    rw [he]
    have h₁ := mul_nonneg (sub_nonneg.mpr ht.2) hxx.le
    have h₂ := mul_nonneg ht.1 hm.le
    by_cases ht0 : t = 0
    · simp [ht0, hxx]
    · have hpos := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hm
      linarith
  by_contra h
  have hM0 : M.det ≤ 0 := le_of_not_gt h
  have hmem : (0 : ℝ) ∈ Set.Icc ((A 1).det) ((A 0).det) := by
    simpa [A] using (show 0 ∈ Set.Icc M.det (1 : ℝ) from ⟨hM0, by norm_num⟩)
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
    hA.continuousOn hmem
  exact hp t ht hz

theorem det_nonneg_of_quadratic_nonneg (M : Matrix n n ℝ)
    (hM : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x)) : 0 ≤ M.det := by
  have hc : Continuous (fun ε : ℝ => (M + ε • (1 : Matrix n n ℝ)).det) :=
    (continuous_const.add (continuous_id.smul continuous_const)).matrix_det
  have hlim : Tendsto (fun ε : ℝ => (M + ε • (1 : Matrix n n ℝ)).det)
      (𝓝[>] 0) (𝓝 M.det) := by
    simpa using (hc.tendsto 0).mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  apply le_of_lt
  apply det_pos_of_quadratic_pos
  intro x hx
  have hxx : 0 < x ⬝ᵥ x := by
    have hn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact lt_of_le_of_ne hn (Ne.symm (dotProduct_self_eq_zero.not.mpr hx))
  have he : x ⬝ᵥ ((M + ε • (1 : Matrix n n ℝ)) *ᵥ x) =
      x ⬝ᵥ (M *ᵥ x) + ε * (x ⬝ᵥ x) := by
    simp [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
  rw [he]
  exact add_pos_of_nonneg_of_pos (hM x) (mul_pos hε hxx)
end Matrix
