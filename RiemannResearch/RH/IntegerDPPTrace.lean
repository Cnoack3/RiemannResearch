import RiemannResearch.RH.ResidueOrthonormalCoordinates
import RiemannResearch.RH.IntegerDPPKernel
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Exact rank trace of the arithmetic DPP kernel

Source: the user's projection DPP construction, 2026-09-20.
The trace follows from the actual Gram–Schmidt residue modes and Parseval
in the counting-coordinate realization of the Pareto Hilbert space. No
ambient density or RH assumption is needed at a finite stage.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem finiteSpace_finrank (n : ℕ) : Module.finrank ℝ (finiteSpace n) = n := by
  have hi : LinearIndependent ℝ (fun i : Fin n => residueAtom i.val) :=
    residueAtom_linearIndependent.comp (fun i : Fin n => i.val) Fin.val_injective
  change Module.finrank ℝ
    (Submodule.span ℝ (Set.range (fun i : Fin n => residueAtom i.val))) = n
  rw [finrank_span_eq_card hi, Fintype.card_fin]

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram

theorem countingBasis_inner_vector (i : ℕ) (f : ThresholdHilbert) :
    inner ℝ (countingBasis i) f = f i := by
  simp [countingBasis, lp.inner_single_left]

/-- The diagonal is the squared counting-coordinate mode mass. -/
theorem integerKernel_diagonal_eq_mode_sum (n i : ℕ) :
    integerKernel n i i = ∑ j : Fin n, (residueMode j.val i) ^ 2 := by
  unfold integerKernel
  rw [real_inner_self_eq_norm_sq]
  have hn : Orthonormal ℝ (fun j : Fin n => residueMode j.val) :=
    residueMode_orthonormal.comp (fun j : Fin n => j.val) Fin.val_injective
  have h : ‖(finiteSpace n).starProjection (countingBasis i)‖ ^ 2 =
      ∑ j : Fin n, (inner ℝ (residueMode j.val) (countingBasis i)) ^ 2 := by
    simpa only [residueMode_finiteSpace] using
      projection_norm_sq_eq_orthonormal_sum hn (countingBasis i)
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  rw [real_inner_comm, countingBasis_inner_vector]

theorem integerKernel_diagonal_summable (n : ℕ) :
    Summable (fun i => integerKernel n i i) := by
  simp only [integerKernel_diagonal_eq_mode_sum]
  exact summable_sum (fun j hj => hilbert_coordinate_square_summable (residueMode j.val))

/-- Exact finite rank trace; index n has precisely n orthonormal modes. -/
theorem integerKernel_diagonal_tsum (n : ℕ) :
    (∑' i, integerKernel n i i) = (n : ℝ) := by
  simp only [integerKernel_diagonal_eq_mode_sum]
  have hs (j : Fin n) : Summable (fun i : ℕ => (residueMode j.val i) ^ 2) :=
    hilbert_coordinate_square_summable (residueMode j.val)
  have hx :
      (∑' i : ℕ, ∑ j : Fin n, (residueMode j.val i) ^ 2) =
        ∑ j : Fin n, ∑' i : ℕ, (residueMode j.val i) ^ 2 :=
    Summable.tsum_finsetSum (s := Finset.univ)
      (fun (j : Fin n) (_hj : j ∈ Finset.univ) => hs j)
  rw [hx]
  simp only [← hilbert_norm_sq, residueMode_orthonormal.norm_eq_one, one_pow]
  simp

/-- Every correlation determinant of size n+1 vanishes at stage n. -/
theorem integerKernel_principal_det_zero_of_rank (n : ℕ) (a : Fin (n + 1) → ℕ) :
    (Matrix.of (fun i j => integerKernel n (a i) (a j))).det = 0 := by
  classical
  by_contra hd
  let v : Fin (n + 1) → finiteSpace n := fun i =>
    ⟨(finiteSpace n).starProjection (countingBasis (a i)),
      (finiteSpace n).starProjection_apply_mem _⟩
  have hv : LinearIndependent ℝ v :=
    Matrix.linearIndependent_of_det_gram_ne_zero (by
      change (Matrix.of (fun i j => integerKernel n (a i) (a j))).det ≠ 0
      exact hd)
  have hc := hv.fintype_card_le_finrank
  rw [Fintype.card_fin, finiteSpace_finrank] at hc
  omega

end RiemannResearch.RH.Pareto.IntegerDPP
