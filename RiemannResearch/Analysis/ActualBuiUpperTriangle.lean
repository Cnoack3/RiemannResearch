/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualBuiFloreaMilinovichFrame

/-!
# Raw published upper-triangular sum for the reflected Landau operator

The source input is the sum of the three absolute off-diagonal error budgets
in Bui–Florea–Milinovich §3, after rescaling a_n = √n v_n. It contains no
operator or RH conclusion. The finite Hermitian symmetry, vanishing diagonal
and count normalization recover the actual quadratic form in Lean.
-/

noncomputable section
open Filter Set Complex Zeta23
open scoped BigOperators Topology InnerProductSpace
namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open ActualZeroOrdinate HorizontalEuclideanMoments ZeroOrdinate ContinuousLinearMap RiemannResearch.Fourier

def buiRationalError (T : ℝ) {d : ℕ} (n m : Fin d) : ℂ :=
  landauSum T (Real.log (((n.val+1:ℕ):ℝ)/((m.val+1:ℕ):ℝ))) +
    ((T*rationalLandauMain (n.val+1) (m.val+1):ℝ):ℂ)

/-- The arithmetical estimates Σ₂, Σ₃ and Σ₄ control the sum of
absolute errors, for independent finite weights. -/
def BuiUpperTriangleError : Prop :=
  ∃ A H : ℝ, 0 ≤ A ∧ 1 < H ∧ ∀ T ≥ H, ∀ d : ℕ, 2 ≤ d → ∀ v : Space d,
    (∑ n : Fin d, ∑ m : Fin d, if m.val < n.val then
      ‖buiRationalError T n m‖*‖v m‖*‖v n‖ else 0) ≤ A*(d:ℝ)*Real.log (d:ℝ)*Real.log ((d:ℝ)*T)*‖v‖^2

theorem BuiUpperTriangleError.reflected (h : BuiUpperTriangleError) : BuiFloreaMilinovichReflectedError := by
  obtain ⟨A,H,hA,hH,hb⟩ := h
  refine ⟨2*A,H,by positivity,hH,?_⟩
  intro T hT hN d hd v
  let R := actualLandauResidual T d
  let E : Matrix (Fin d) (Fin d) ℂ := fun i j => euclideanEntry R i j
  let f := fun i j : Fin d => ‖E i j‖*‖v j‖*‖v i‖
  let g := fun i j : Fin d => if j.val < i.val then f i j else 0
  have hmat : Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) E = R := by
    apply euclideanEntry_ext
    intro i j
    rw [euclideanEntry_toEuclideanCLM]
  have hpoint (i : Fin d) : ‖R v i‖ ≤ ∑ j, ‖E i j‖*‖v j‖ := by
    have he : R v i = ∑ j, E i j*v j := by
      rw [← hmat]; exact congrFun (Matrix.ofLp_toEuclideanCLM E v) i
    rw [he]
    simpa only [norm_mul] using _root_.norm_sum_le (Finset.univ : Finset (Fin d)) (fun j => E i j*v j)
  have hq : |R.reApplyInnerSelf v| ≤ ∑ i, ∑ j, f i j := by
    change |(inner ℂ (R v) v).re| ≤ _
    apply (Complex.abs_re_le_norm _).trans
    rw [PiLp.inner_apply]
    apply (_root_.norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    calc
      _ = ‖R v i‖*‖v i‖ := by
        rw [RCLike.inner_apply,norm_mul]
        change ‖v i‖*‖star (R v i)‖ = _
        rw [norm_star,mul_comm]
      _ ≤ (∑ j, ‖E i j‖*‖v j‖)*‖v i‖ :=
        mul_le_mul_of_nonneg_right (hpoint i) (norm_nonneg _)
      _ = ∑ j, f i j := by rw [Finset.sum_mul]
  have hpair (i j : Fin d) : f i j = g i j+g j i := by
    rcases lt_trichotomy j.val i.val with hij | he | hji
    · simp only [g,if_pos hij,if_neg hij.not_gt,add_zero]
    · have hEq : j=i := Fin.ext he
      subst j
      simp only [f,g,E,R,actualLandauResidual_entry_diag T d hN,norm_zero,zero_mul,
        lt_irrefl,if_false,zero_add]
    · rw [show f i j = f j i by
        dsimp [f,E,R]; rw [actualLandauResidual_entry_star T d i j,norm_star]; ring]
      simp only [g,if_pos hji,if_neg hji.not_gt,zero_add]
  have htwo : (∑ i, ∑ j, f i j) = 2*(∑ i, ∑ j, g i j) := by
    simp_rw [hpair,Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j : Fin d => g j i)]
    ring
  have hnorm : (∑ i, ∑ j, g i j) = (Ncount 0 T:ℝ)⁻¹ *
      (∑ n : Fin d, ∑ m : Fin d, if m.val < n.val then ‖buiRationalError T n m‖*‖v m‖*‖v n‖ else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [g,f,E,R]
    split_ifs with hij
    · rw [actualLandauResidual_entry_of_lt T d hN i j hij,norm_mul,norm_inv,Complex.norm_natCast]
      dsimp [buiRationalError]; ring
    · rw [mul_zero]
  apply hq.trans
  rw [htwo,hnorm]
  apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hb T hT d hd v) (by positivity)) (by norm_num : (0:ℝ)≤2)).trans_eq
  ring

end RiemannResearch.Analysis.ActualZeroPhaseMoments
