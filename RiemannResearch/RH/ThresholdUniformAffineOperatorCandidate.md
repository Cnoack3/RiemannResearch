# ThresholdUniformAffineOperator — unverified candidate

**Not verified by Lean.** No theorem in this candidate is claimed proved. See [attempt report](ThresholdOperatorComparisonAttempt.md).

```lean
import RiemannResearch.RH.ThresholdHilbertProjection

/-!
# Infinite uniform affine comparison and its orthogonal projection

Source: independently developed from Christian Noack's RH_Two_Seed_Threshold.tex
(8 September 2026), Section 11.2, which motivates the uniform comparison.
Explicit disjoint unit columns define a genuine complete-l2 isometry via
Mathlib's orthogonal-family construction. Its actual adjoint supplies the
bounded self-adjoint idempotent comparison projection. No RH input is used.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

def uniformAffineBlock (m j : ℕ) : Finset ℕ :=
  Finset.Ico (m * (j+1) - 1) (m * (j+2) - 1)

theorem uniformAffineBlock_card (m j : ℕ) (hm : 0 < m) :
    (uniformAffineBlock m j).card = m := by
  have hpos : 0 < m * (j+1) := Nat.mul_pos hm (by omega)
  simp only [uniformAffineBlock, Finset.card_Ico]
  have he : m * (j+2) = m * (j+1) + m := by ring
  rw [he]
  omega

theorem uniformAffineBlock_unique (m j k n : ℕ) (hm : 0 < m)
    (hj : n ∈ uniformAffineBlock m j)
    (hk : n ∈ uniformAffineBlock m k) : j = k := by
  have hpj : 0 < m * (j+1) := Nat.mul_pos hm (by omega)
  have hpk : 0 < m * (k+1) := Nat.mul_pos hm (by omega)
  simp only [uniformAffineBlock, Finset.mem_Ico] at hj hk
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hh := Nat.mul_le_mul_left m (show j+2 ≤ k+1 by omega)
    omega
  · have hh := Nat.mul_le_mul_left m (show k+2 ≤ j+1 by omega)
    omega

def uniformAffineColumn (m j : ℕ) : ThresholdHilbert :=
  ⟨fun n => if n ∈ uniformAffineBlock m j then 1 / Real.sqrt (m : ℝ) else 0, by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    apply summable_of_ne_finset_zero (s := uniformAffineBlock m j)
    intro n hn
    simp [hn]⟩

@[simp] theorem uniformAffineColumn_apply (m j n : ℕ) :
    uniformAffineColumn m j n =
      if n ∈ uniformAffineBlock m j then 1 / Real.sqrt (m : ℝ) else 0 := rfl

theorem uniformAffineColumn_norm_sq (m j : ℕ) (hm : 0 < m) :
    ‖uniformAffineColumn m j‖ ^ 2 = 1 := by
  rw [hilbert_norm_sq]
  rw [tsum_eq_sum (s := uniformAffineBlock m j) (fun n hn => by simp [hn])]
  have he : ∑ n ∈ uniformAffineBlock m j, (uniformAffineColumn m j n)^2 =
      (uniformAffineBlock m j).card * (1 / Real.sqrt (m : ℝ))^2 := by
    calc
      _ = ∑ _n ∈ uniformAffineBlock m j, (1 / Real.sqrt (m : ℝ))^2 := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [uniformAffineColumn_apply, hn]
      _ = _ := by simp
  rw [he, uniformAffineBlock_card m j hm, div_pow, one_pow,
    Real.sq_sqrt (Nat.cast_nonneg m)]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp

theorem uniformAffineColumn_norm (m j : ℕ) (hm : 0 < m) :
    ‖uniformAffineColumn m j‖ = 1 := by
  have h := uniformAffineColumn_norm_sq m j hm
  have hn := norm_nonneg (uniformAffineColumn m j)
  nlinarith

theorem uniformAffineColumn_inner_ne (m j k : ℕ) (hm : 0 < m) (hjk : j ≠ k) :
    inner ℝ (uniformAffineColumn m j) (uniformAffineColumn m k) = 0 := by
  rw [lp.inner_eq_tsum]
  apply tsum_eq_zero
  intro n
  by_cases hj : n ∈ uniformAffineBlock m j
  · have hk : n ∉ uniformAffineBlock m k := by
      intro hk
      exact hjk (uniformAffineBlock_unique m j k n hm hj hk)
    simp [uniformAffineColumn_apply, hk]
  · simp [uniformAffineColumn_apply, hj]

def uniformAffineColumnIsometry (m : ℕ) (hm : 0 < m) (j : ℕ) :
    ℝ →ₗᵢ[ℝ] ThresholdHilbert where
  toLinearMap :=
    { toFun := fun c => c • uniformAffineColumn m j
      map_add' := fun c d => add_smul c d _
      map_smul' := fun c d => by simp [smul_smul] }
  norm_map' c := by rw [norm_smul, uniformAffineColumn_norm m j hm, mul_one]

theorem uniformAffineOrthogonal (m : ℕ) (hm : 0 < m) :
    OrthogonalFamily ℝ (fun _ : ℕ => ℝ) (uniformAffineColumnIsometry m hm) := by
  intro j k hjk c d
  change inner ℝ (c • uniformAffineColumn m j) (d • uniformAffineColumn m k) = 0
  rw [real_inner_smul_left, real_inner_smul_right,
    uniformAffineColumn_inner_ne m j k hm hjk]
  ring

def hilbertUniformAffine (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →ₗᵢ[ℝ] ThresholdHilbert :=
  (uniformAffineOrthogonal m hm).linearIsometry

theorem hilbertUniformAffine_single (m : ℕ) (hm : 0 < m) (j : ℕ) (c : ℝ) :
    hilbertUniformAffine m hm (lp.single 2 j c) = c • uniformAffineColumn m j := by
  exact (uniformAffineOrthogonal m hm).linearIsometry_apply_single c

def hilbertUniformAffineContinuous (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (hilbertUniformAffine m hm).toContinuousLinearMap

def hilbertUniformBlockProjection (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (hilbertUniformAffineContinuous m hm).comp (hilbertUniformAffineContinuous m hm).adjoint

/-- Auxiliary coordinate functional; does not require a recent lp.evalCLM API. -/
def uniformHilbertCoordinate (n : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  ({ toFun := fun f => f n
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : ThresholdHilbert →ₗ[ℝ] ℝ).mkContinuous 1
      (fun f => by simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) f n)

theorem hilbertUniformAffine_coordinate_sum (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (n : ℕ) :
    hilbertUniformAffine m hm f n = ∑' j, f j * uniformAffineColumn m j n := by
  have hs := (uniformAffineOrthogonal m hm).summable_of_lp f
  have h := (uniformHilbertCoordinate n).map_tsum hs
  exact h

theorem hilbertUniformAffine_block_coordinate (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (j n : ℕ) (hn : n ∈ uniformAffineBlock m j) :
    hilbertUniformAffine m hm f n = f j / Real.sqrt (m : ℝ) := by
  rw [hilbertUniformAffine_coordinate_sum]
  rw [tsum_eq_single j (fun k hk => by
    have hkn : n ∉ uniformAffineBlock m k := by
      intro hkn
      exact hk (uniformAffineBlock_unique m k j n hm hkn hn)
    simp [uniformAffineColumn_apply, hkn])]
  simp [uniformAffineColumn_apply, hn, div_eq_mul_inv]

theorem hilbertUniformAffine_head_coordinate (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (n : ℕ) (hn : n+1 < m) :
    hilbertUniformAffine m hm f n = 0 := by
  rw [hilbertUniformAffine_coordinate_sum]
  apply tsum_eq_zero
  intro j
  have hh : m ≤ m*(j+1) := by
    simpa using Nat.mul_le_mul_left m (show 1 ≤ j+1 by omega)
  have hj : n ∉ uniformAffineBlock m j := by
    simp only [uniformAffineBlock, Finset.mem_Ico]
    omega
  simp [uniformAffineColumn_apply, hj]

end
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto
noncomputable section

theorem hilbertUniformAffine_adjoint_apply_self (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    (hilbertUniformAffineContinuous m hm).adjoint (hilbertUniformAffine m hm f) = f := by
  exact congrArg (fun A : ThresholdHilbert →L[ℝ] ThresholdHilbert => A f)
    (hilbertUniformAffine m hm).adjoint_comp_self

theorem hilbertUniformBlockProjection_apply (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    hilbertUniformBlockProjection m hm f =
      hilbertUniformAffine m hm ((hilbertUniformAffineContinuous m hm).adjoint f) := rfl

theorem hilbertUniformBlockProjection_on_range (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    hilbertUniformBlockProjection m hm (hilbertUniformAffine m hm f) =
      hilbertUniformAffine m hm f := by
  rw [hilbertUniformBlockProjection_apply, hilbertUniformAffine_adjoint_apply_self]

theorem hilbertUniformBlockProjection_idempotent (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    hilbertUniformBlockProjection m hm (hilbertUniformBlockProjection m hm f) =
      hilbertUniformBlockProjection m hm f := by
  rw [hilbertUniformBlockProjection_apply m hm f]
  exact hilbertUniformBlockProjection_on_range m hm _

theorem hilbertUniformBlockProjection_self_adjoint (m : ℕ) (hm : 0 < m) :
    (hilbertUniformBlockProjection m hm).adjoint = hilbertUniformBlockProjection m hm := by
  simp only [hilbertUniformBlockProjection, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem hilbertUniformBlockProjection_symmetric (m : ℕ) (hm : 0 < m)
    (f g : ThresholdHilbert) :
    inner ℝ (hilbertUniformBlockProjection m hm f) g =
      inner ℝ f (hilbertUniformBlockProjection m hm g) := by
  have h := ContinuousLinearMap.adjoint_inner_right (hilbertUniformBlockProjection m hm) f g
  rw [hilbertUniformBlockProjection_self_adjoint] at h
  exact h.symm

theorem hilbertUniformBlockProjection_orthogonal_defect (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    inner ℝ (hilbertUniformBlockProjection m hm f)
      (f - hilbertUniformBlockProjection m hm f) = 0 := by
  rw [inner_sub_right]
  have h := hilbertUniformBlockProjection_symmetric m hm
    (hilbertUniformBlockProjection m hm f) f
  rw [hilbertUniformBlockProjection_idempotent] at h
  exact sub_eq_zero.mpr h

theorem hilbertUniformBlockProjection_pythagoras (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    ‖f‖^2 = ‖hilbertUniformBlockProjection m hm f‖^2 +
      ‖f-hilbertUniformBlockProjection m hm f‖^2 := by
  have h := hilbertUniformBlockProjection_orthogonal_defect m hm f
  have h' : inner ℝ (f-hilbertUniformBlockProjection m hm f)
      (hilbertUniformBlockProjection m hm f) = 0 := by
    rw [real_inner_comm]
    exact h
  have he : f = hilbertUniformBlockProjection m hm f +
      (f-hilbertUniformBlockProjection m hm f) := by abel
  conv_lhs => rw [he]
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h, h']
  ring

end
end RiemannResearch.RH.Pareto
```
