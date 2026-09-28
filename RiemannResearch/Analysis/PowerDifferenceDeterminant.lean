import Mathlib.LinearAlgebra.Vandermonde

/-!
# Power-difference determinants

The RH consumer is the exact dyadic Mellin minor in `RH/MellinDyadicVandermonde`.
Source: the algebraic derivation in this research session, using Mathlib's
standard adjacent-column elimination and Vandermonde determinant theorems.
No mathematical novelty claim is made for this general identity.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis

/-- Adjacent column elimination exposes the Vandermonde factor. -/
theorem powerDifference_det_vandermonde {R : Type*} [CommRing R]
    (n : ℕ) (a : R) (q : Fin n → R) :
    (Matrix.of (fun i j : Fin n => a^(j.val+1) - q i^(j.val+1))).det =
      (∏ i : Fin n, (a - q i)) * (Matrix.vandermonde q).det := by
  cases n with
  | zero => simp
  | succ n =>
    let A : Matrix (Fin (n+1)) (Fin (n+1)) R :=
      Matrix.of (fun i j => a^(j.val+1) - q i^(j.val+1))
    let B : Matrix (Fin (n+1)) (Fin (n+1)) R :=
      Matrix.of (fun i j => (a-q i) * q i^j.val)
    have hAB : A.det = B.det := by
      apply Matrix.det_eq_of_forall_col_eq_smul_add_pred (fun _ => a)
      · intro i
        simp [A, B]
      · intro i j
        simp only [A, B, Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
        simp only [pow_succ]
        ring
    change A.det = _
    rw [hAB]
    exact Matrix.det_mul_column (fun i => a-q i) (Matrix.vandermonde q)

/-- Exact product, with the row factors and pairwise spacing factors retained. -/
theorem powerDifference_det {R : Type*} [CommRing R]
    (n : ℕ) (a : R) (q : Fin n → R) :
    (Matrix.of (fun i j : Fin n => a^(j.val+1) - q i^(j.val+1))).det =
      (∏ i : Fin n, (a-q i)) *
        ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (q j-q i) := by
  rw [powerDifference_det_vandermonde, Matrix.det_vandermonde]

theorem powerDifference_det_ne_zero_iff {R : Type*} [CommRing R] [IsDomain R]
    (n : ℕ) (a : R) (q : Fin n → R) :
    (Matrix.of (fun i j : Fin n => a^(j.val+1) - q i^(j.val+1))).det ≠ 0 ↔
      (∀ i, a ≠ q i) ∧ Function.Injective q := by
  rw [powerDifference_det_vandermonde, mul_ne_zero_iff,
    Matrix.det_vandermonde_ne_zero_iff]
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies, sub_ne_zero]

end RiemannResearch.Analysis
