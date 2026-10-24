import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Eigenvalue bounds for finite positive contractions

Source: Mathlib's Hermitian spectral theorem and positive semidefinite
conjugation. These general matrix facts are independent of probability.
Moved from DeterminantalSpectralCount without changing their declaration names.
-/

noncomputable section

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}

/-- Every eigenvalue of a positive contraction is at most one. -/
theorem PosSemidef.eigenvalues_le_one (hQ : Q.PosSemidef)
    (hI : (1 - Q).PosSemidef) (i : ι) :
    hQ.isHermitian.eigenvalues i ≤ 1 := by
  let U := hQ.isHermitian.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hQ' : Q = f (Matrix.diagonal hQ.isHermitian.eigenvalues) := by
    simpa [f, U, Function.comp_def] using hQ.isHermitian.spectral_theorem
  have he : (1 : Matrix ι ι ℝ) - Q =
      f (1 - Matrix.diagonal hQ.isHermitian.eigenvalues) := by
    rw [map_sub, map_one, ← hQ']
  rw [he] at hI
  have hd : ((1 : Matrix ι ι ℝ) - Matrix.diagonal hQ.isHermitian.eigenvalues).PosSemidef := by
    have hU : IsUnit (U : Matrix ι ι ℝ) := Unitary.isUnit_coe
    apply (Matrix.IsUnit.posSemidef_star_right_conjugate_iff hU).mp
    simpa only [f, Unitary.conjStarAlgAut_apply] using hI
  have hn := hd.diag_nonneg (i := i)
  simpa [sub_nonneg] using hn

/-- The spectral parameters of a positive contraction are Bernoulli parameters. -/
theorem PosSemidef.eigenvalues_mem_Icc (hQ : Q.PosSemidef)
    (hI : (1 - Q).PosSemidef) (i : ι) :
    hQ.isHermitian.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hQ.eigenvalues_nonneg i, hQ.eigenvalues_le_one hI i⟩

end Matrix
