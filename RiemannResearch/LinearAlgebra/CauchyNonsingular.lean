import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Nonsingularity of finite Cauchy matrices

Source: user-requested Ramanujan dual program, October 2026.
The proof is the elementary polynomial-numerator argument: a kernel vector
gives a polynomial of degree below the number of distinct evaluation points;
evaluation at its poles then recovers every coefficient. The concrete consumer
is the Mellin Cauchy-Gram matrix in the Ramanujan zero certificates.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.LinearAlgebra

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

def cauchyMatrix (x y : ι → K) : Matrix ι ι K :=
  fun i j => 1 / (x i + y j)

private def cauchyNumerator (y v : ι → K) : Polynomial K :=
  ∑ j, Polynomial.C (v j) *
    ∏ k ∈ Finset.univ.erase j, (Polynomial.X - Polynomial.C (-y k))

private theorem cauchyNumerator_eval (x y v : ι → K)
    (hden : ∀ i j, x i + y j ≠ 0) (i : ι) :
    Polynomial.eval (x i) (cauchyNumerator y v) =
      (∏ k : ι, (x i + y k)) * (cauchyMatrix x y).mulVec v i := by
  classical
  change (Polynomial.evalRingHom (x i)) (cauchyNumerator y v) = _
  simp only [cauchyNumerator, map_sum, map_mul, map_prod]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    sub_neg_eq_add]
  change (∑ j, v j * ∏ k ∈ Finset.univ.erase j, (x i + y k)) =
    (∏ k : ι, (x i + y k)) * ∑ j, (1 / (x i + y j)) * v j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.prod_erase_mul Finset.univ (fun k => x i + y k)
    (Finset.mem_univ j)]
  field_simp [hden i j] <;> ring

private theorem cauchyNumerator_degree_le (y v : ι → K) :
    (cauchyNumerator y v).natDegree ≤ Fintype.card ι - 1 := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  have h := Polynomial.natDegree_prod_le (Finset.univ.erase j)
    (fun k => Polynomial.X - Polynomial.C (-y k))
  simpa using h

private theorem cauchyNumerator_eval_pole (y v : ι → K) (j : ι) :
    Polynomial.eval (-y j) (cauchyNumerator y v) =
      v j * ∏ k ∈ Finset.univ.erase j, (y k - y j) := by
  classical
  change (Polynomial.evalRingHom (-y j)) (cauchyNumerator y v) = _
  simp only [cauchyNumerator, map_sum, map_mul, map_prod]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X,
    sub_neg_eq_add]
  rw [Finset.sum_eq_single j]
  · congr 1
    apply Finset.prod_congr rfl
    intro k _
    ring
  · intro k _ hkj
    have hz : (∏ l ∈ Finset.univ.erase k, (-y j + y l)) = 0 := by
      apply Finset.prod_eq_zero
        (by simp [Ne.symm hkj] : j ∈ Finset.univ.erase k)
      simp
    rw [hz, mul_zero]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Distinct rows and poles, and no zero denominator, force a trivial kernel. -/
theorem cauchyMatrix_mulVec_eq_zero_iff (x y v : ι → K)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hden : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).mulVec v = 0 ↔ v = 0 := by
  classical
  constructor
  · intro hv
    cases isEmpty_or_nonempty ι with
    | inl hempty =>
      letI := hempty
      exact funext (fun i => isEmptyElim i)
    | inr hnonempty =>
      letI := hnonempty
      have hdegree : (cauchyNumerator y v).natDegree < Fintype.card ι := by
        have h := cauchyNumerator_degree_le y v
        have hcard : 0 < Fintype.card ι := Fintype.card_pos
        omega
      have hpoly : cauchyNumerator y v = 0 :=
        Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hx
          (fun i => by rw [cauchyNumerator_eval x y v hden i, hv]; simp) hdegree
      funext j
      have he : v j * (∏ k ∈ Finset.univ.erase j, (y k - y j)) = 0 := by
        rw [← cauchyNumerator_eval_pole y v j, hpoly]
        simp
      have hp : (∏ k ∈ Finset.univ.erase j, (y k - y j)) ≠ 0 := by
        apply Finset.prod_ne_zero_iff.mpr
        intro k hk
        apply sub_ne_zero.mpr
        intro hkj
        exact (Finset.mem_erase.mp hk).1 (hy hkj)
      exact (mul_eq_zero.mp he).resolve_right hp
  · rintro rfl
    simp

theorem cauchyMatrix_mulVec_injective (x y : ι → K)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hden : ∀ i j, x i + y j ≠ 0) :
    Function.Injective (cauchyMatrix x y).mulVec := by
  intro v w hvw
  have hz : (cauchyMatrix x y).mulVec (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp ((cauchyMatrix_mulVec_eq_zero_iff x y (v - w) hx hy hden).mp hz)

theorem cauchyMatrix_det_ne_zero (x y : ι → K)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hden : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  exact Matrix.mulVec_injective_iff_isUnit.mp
    (cauchyMatrix_mulVec_injective x y hx hy hden)

theorem cauchyMatrix_det_ne_zero_iff (x y : ι → K)
    (hden : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det ≠ 0 ↔
      Function.Injective x ∧ Function.Injective y := by
  classical
  constructor
  · intro hdet
    constructor
    · intro i j hij
      by_contra hne
      apply hdet
      apply Matrix.det_zero_of_row_eq hne
      funext k
      simp only [cauchyMatrix, hij]
    · intro i j hij
      by_contra hne
      apply hdet
      apply Matrix.det_zero_of_column_eq hne
      intro k
      simp only [cauchyMatrix, hij]
  · rintro ⟨hx, hy⟩
    exact cauchyMatrix_det_ne_zero x y hx hy hden

end RiemannResearch.LinearAlgebra
