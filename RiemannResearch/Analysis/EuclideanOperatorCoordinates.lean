/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.HorizontalPhaseBootstrap

/-!
# Euclidean operator coordinates and diagonal commutators

Continuous matrix entries preserve operator sums and convergent infinite series.
Matrix realization and entry extensionality identify operators in the actual
Euclidean Hilbert norm. Diagonal coordinate multipliers have an operator norm
bound from coordinate bounds, and every iterated commutator has its exact entry
formula. All finite coordinates remain present.

Source for the representation and proof strategy: Mathlib's Euclidean basis,
matrix realization, and continuous coordinate projections, revision
51e6992efd06126df61a496bebf8f49482a4e129:
https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/InnerProductSpace/PiL2.lean
and the sibling Analysis/CStarAlgebra/Matrix.lean. The commutator algebra is the
user-provided research argument in Prime_Phases_Agenda_Proof_Attempts.tex.
-/

noncomputable section
open scoped BigOperators InnerProductSpace Matrix

namespace ContinuousLinearMap

variable {d : ℕ}

def euclideanEntry (A : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (n m : Fin d) : ℂ := (A (EuclideanSpace.single m 1)) n

def euclideanEntryCLM (n m : Fin d) :
    (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) →L[ℂ] ℂ :=
  (innerSL ℂ ((EuclideanSpace.basisFun (Fin d) ℂ) n)).comp
    (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin d))
      ((EuclideanSpace.basisFun (Fin d) ℂ) m))

@[simp] theorem euclideanEntryCLM_apply
    (A : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) (n m : Fin d) :
    euclideanEntryCLM n m A = euclideanEntry A n m := by
  change inner ℂ ((EuclideanSpace.basisFun (Fin d) ℂ) n)
    (A ((EuclideanSpace.basisFun (Fin d) ℂ) m)) = _
  rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_apply]
  rfl

@[simp] theorem euclideanEntry_toEuclideanCLM (M : Matrix (Fin d) (Fin d) ℂ)
    (n m : Fin d) :
    euclideanEntry (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M) n m = M n m := by
  change (M *ᵥ Pi.single m (1 : ℂ)) n = M n m
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem euclideanEntry_ext
    {A B : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)}
    (h : ∀ n m, euclideanEntry A n m = euclideanEntry B n m) : A = B := by
  apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm.injective
  ext n m
  have ha : euclideanEntry A n m =
      ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm A) n m := by
    calc
      _ = euclideanEntry
          (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
            ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm A)) n m := by
        rw [(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).apply_symm_apply]
      _ = _ := euclideanEntry_toEuclideanCLM _ _ _
  have hb : euclideanEntry B n m =
      ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm B) n m := by
    calc
      _ = euclideanEntry
          (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
            ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm B)) n m := by
        rw [(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).apply_symm_apply]
      _ = _ := euclideanEntry_toEuclideanCLM _ _ _
  exact ha.symm.trans ((h n m).trans hb)

@[simp] theorem euclideanEntry_add
    (A B : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) (n m : Fin d) :
    euclideanEntry (A + B) n m = euclideanEntry A n m + euclideanEntry B n m := by
  simpa only [euclideanEntryCLM_apply] using (euclideanEntryCLM n m).map_add A B

@[simp] theorem euclideanEntry_sub
    (A B : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) (n m : Fin d) :
    euclideanEntry (A - B) n m = euclideanEntry A n m - euclideanEntry B n m := by
  simpa only [euclideanEntryCLM_apply] using (euclideanEntryCLM n m).map_sub A B

@[simp] theorem euclideanEntry_real_smul
    (r : ℝ) (A : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (n m : Fin d) :
    euclideanEntry (r • A) n m = (r : ℂ) * euclideanEntry A n m := by
  change (r • A (EuclideanSpace.single m 1)) n = _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem euclideanEntry_tsum
    (f : ℕ → (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)))
    (hf : Summable f) (n m : Fin d) :
    euclideanEntry (∑' k, f k) n m = ∑' k, euclideanEntry (f k) n m := by
  simpa only [euclideanEntryCLM_apply] using (euclideanEntryCLM n m).map_tsum hf

@[simp] theorem euclideanEntry_rankOne
    (v w : EuclideanSpace ℂ (Fin d)) (n m : Fin d) :
    euclideanEntry (InnerProductSpace.rankOne ℂ v w) n m = v n * star (w m) := by
  rw [← euclideanEntryCLM_apply]
  change inner ℂ ((EuclideanSpace.basisFun (Fin d) ℂ) n)
    (inner ℂ w ((EuclideanSpace.basisFun (Fin d) ℂ) m) • v) = _
  rw [inner_smul_right, ← inner_conj_symm w ((EuclideanSpace.basisFun (Fin d) ℂ) m),
    EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner]
  simpa only [starRingEnd_apply] using mul_comm (star (w m)) (v n)

end ContinuousLinearMap

namespace EuclideanSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Diagonal coordinate multiplier, using the actual Euclidean operator norm. -/
def diagonalCLM (r : ι → ℂ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (Matrix.diagonal r)

@[simp] theorem diagonalCLM_apply (r : ι → ℂ)
    (x : EuclideanSpace ℂ ι) (i : ι) :
    diagonalCLM r x i = r i * x i := by
  have h := congrFun (Matrix.ofLp_toEuclideanCLM (Matrix.diagonal r) x) i
  simpa only [diagonalCLM, Matrix.mulVec_diagonal] using h

theorem diagonalCLM_single (r : ι → ℂ) (j : ι) :
    diagonalCLM r (EuclideanSpace.single j 1) =
      r j • EuclideanSpace.single j 1 := by
  apply WithLp.ofLp_injective 2
  funext i
  change diagonalCLM r (EuclideanSpace.single j 1) i =
    r j * (EuclideanSpace.single j 1) i
  rw [diagonalCLM_apply]
  by_cases h : i = j
  · subst i
    rfl
  · simp only [PiLp.single_apply, if_neg h, mul_zero]

/-- A coordinate bound gives a bound in the Euclidean operator norm. -/
theorem norm_diagonalCLM_le (r : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hr : ∀ i, ‖r i‖ ≤ C) :
    ‖diagonalCLM r‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hp : ∀ i, ‖diagonalCLM r x i‖ ≤ C * ‖x i‖ := by
    intro i
    rw [diagonalCLM_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hr i) (norm_nonneg _)
  have hs : ‖diagonalCLM r x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    calc
      _ = ∑ i, ‖diagonalCLM r x i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
      _ ≤ ∑ i, (C * ‖x i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).2 (hp i)
      _ = _ := by simp only [mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).1 hs

/-- The complete entry formula for every iterate of the actual diagonal commutator. -/
theorem iterComm_diagonalCLM_apply_single (r : ι → ℂ)
    (M : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (j : ℕ) (n m : ι) :
    (RiemannResearch.Analysis.HorizontalPhaseBootstrap.iterComm
      (diagonalCLM r) j M (EuclideanSpace.single m 1)) n =
      (r n - r m) ^ j * (M (EuclideanSpace.single m 1)) n := by
  induction j with
  | zero =>
    simp only [RiemannResearch.Analysis.HorizontalPhaseBootstrap.iterComm, pow_zero, one_mul]
  | succ j ih =>
    change
      diagonalCLM r
          (RiemannResearch.Analysis.HorizontalPhaseBootstrap.iterComm
            (diagonalCLM r) j M (EuclideanSpace.single m 1)) n -
        (RiemannResearch.Analysis.HorizontalPhaseBootstrap.iterComm
          (diagonalCLM r) j M
            (diagonalCLM r (EuclideanSpace.single m 1))) n = _
    rw [diagonalCLM_apply, diagonalCLM_single, map_smul]
    change r n *
        (RiemannResearch.Analysis.HorizontalPhaseBootstrap.iterComm
          (diagonalCLM r) j M (EuclideanSpace.single m 1)) n -
      r m *
        (RiemannResearch.Analysis.HorizontalPhaseBootstrap.iterComm
          (diagonalCLM r) j M (EuclideanSpace.single m 1)) n = _
    simp only [ih, pow_succ]
    ring

end EuclideanSpace
namespace ContinuousLinearMap

/-- A complete d by d entry bound in the Euclidean operator norm. -/
theorem norm_toEuclideanCLM_le_card_mul {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hM : ∀ n m, ‖M n m‖ ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M‖ ≤ (d : ℝ) * R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  let S : ℝ := ∑ j : Fin d, ‖x j‖
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hS : S ^ 2 ≤ (d : ℝ) * ‖x‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j : Fin d => ‖x j‖) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at h
    simpa only [← EuclideanSpace.norm_sq_eq, mul_comm] using h
  have hc (n : Fin d) :
      ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x) n‖ ≤ R * S := by
    change ‖∑ m : Fin d, M n m * x m‖ ≤ R * ∑ m : Fin d, ‖x m‖
    calc
      _ ≤ ∑ m : Fin d, ‖M n m * x m‖ := norm_sum_le _ _
      _ ≤ ∑ m : Fin d, R * ‖x m‖ := by
        apply Finset.sum_le_sum
        intro m hm
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hM n m) (norm_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have hs : ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x‖ ^ 2 ≤
      ((d : ℝ) * R * ‖x‖) ^ 2 := by
    calc
      _ = ∑ n : Fin d,
          ‖(Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) M x) n‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq _
      _ ≤ ∑ n : Fin d, (R * S) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR hS0)).2 (hc n)
      _ = (d : ℝ) * R ^ 2 * S ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_pow]
        ring
      _ ≤ (d : ℝ) * R ^ 2 * ((d : ℝ) * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hs


theorem norm_le_card_mul_of_euclideanEntry_le {d : ℕ}
    (A : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (R : ℝ) (hR : 0 ≤ R) (hA : ∀ n m, ‖euclideanEntry A n m‖ ≤ R) :
    ‖A‖ ≤ (d : ℝ) * R := by
  have ha : A = Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
      (Matrix.of fun n m => euclideanEntry A n m) := by
    apply euclideanEntry_ext
    intro n m
    exact (euclideanEntry_toEuclideanCLM _ n m).symm
  rw [ha]
  exact norm_toEuclideanCLM_le_card_mul _ R hR hA

@[simp] theorem euclideanEntry_one {d : ℕ} (n m : Fin d) :
    euclideanEntry (1 : EuclideanSpace ℂ (Fin d) →L[ℂ]
      EuclideanSpace ℂ (Fin d)) n m = if n = m then 1 else 0 := by
  change (EuclideanSpace.single m (1 : ℂ)) n = _
  simp only [PiLp.single_apply]

end ContinuousLinearMap
