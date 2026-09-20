import RiemannResearch.Probability.DeterminantalWindowGenerating
import Mathlib.Analysis.Matrix.PosDef

/-!
# Spectral factorization of finite-window determinantal counts

Source: Hough--Krishnapur--Peres--Virag, *Determinantal Processes and
Independence*, arXiv:math/0503110, Theorem 7, for the spectral count statement.
The factorization here follows from Mathlib's finite Hermitian spectral theorem.
It is proved for the actual DPP probability generating function. The parameters
lie in `[0,1]` for a positive contraction.
-/

noncomputable section
open Matrix Unitary MeasureTheory
open scoped BigOperators Classical

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {Q : Matrix ι ι ℝ}

/-- The determinant generating function factors over the real eigenvalues.
No positivity is needed for this algebraic spectral identity. -/
theorem IsHermitian.det_one_add_smul_eq_prod (hQ : Q.IsHermitian) (t : ℝ) :
    (1 + t • Q).det = ∏ i, (1 + t * hQ.eigenvalues i) := by
  let U := hQ.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
  have hQ' : Q = f (Matrix.diagonal hQ.eigenvalues) := by
    simpa [f, U, Function.comp_def] using hQ.spectral_theorem
  have hdiag : (1 : Matrix ι ι ℝ) + t • Matrix.diagonal hQ.eigenvalues =
      Matrix.diagonal (fun i => 1 + t * hQ.eigenvalues i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal, hij]
  have he : (1 : Matrix ι ι ℝ) + t • Q =
      f (Matrix.diagonal (fun i => 1 + t * hQ.eigenvalues i)) := by
    rw [← hdiag, map_add, map_one, map_smul, ← hQ']
  rw [he]
  change (Unitary.conjStarAlgAut ℝ (Matrix ι ι ℝ) U
    (Matrix.diagonal (fun i => 1 + t * hQ.eigenvalues i))).det = _
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul_comm,
    ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.det_diagonal]

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
    simpa only [f, Unitary.conjStarAlgAut_apply,
      Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff] using hI
  have hn := hd.diag_nonneg (i := i)
  simpa [sub_nonneg] using hn

/-- The spectral parameters of a positive contraction are Bernoulli parameters. -/
theorem PosSemidef.eigenvalues_mem_Icc (hQ : Q.PosSemidef)
    (hI : (1 - Q).PosSemidef) (i : ι) :
    hQ.isHermitian.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hQ.eigenvalues_nonneg i, hQ.eigenvalues_le_one hI i⟩

end Matrix

namespace RiemannResearch.Probability.DPP
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact finite DPP count PGF is a product of Bernoulli PGF factors. -/
theorem finiteLaw_count_generating_spectral (Q : Matrix ι ι ℝ)
    (hQ : Q.IsHermitian) (hpos : ∀ S, 0 ≤ exactWeight Q S) (z : ℝ) :
    (∑ S : Finset ι, z ^ S.card * ((finiteLaw Q hpos) S).toReal) =
      ∏ i, (1 - hQ.eigenvalues i + z * hQ.eigenvalues i) := by
  rw [finiteLaw_count_generating]
  have hm : Matrix.diagonal (fun _ : ι => z) * Q + (1 - Q) =
      (1 : Matrix ι ι ℝ) + (z - 1) • Q := by
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hm, hQ.det_one_add_smul_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  ring

variable {α Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → Set α} {K : α → α → ℝ}

/-- Under the actual spatial DPP law, a finite-window count has the spectral
product PGF. Its factors are Bernoulli PGFs when the compression is a positive
contraction, by `Matrix.PosSemidef.eigenvalues_mem_Icc`. -/
theorem IsDPP.window_count_generating_spectral (h : IsDPP μ X K) (e : ι ↪ α)
    (hQ : (Matrix.of (fun i j : ι => K (e i) (e j))).IsHermitian)
    (hpos : ∀ S, 0 ≤ exactWeight (Matrix.of (fun i j : ι => K (e i) (e j))) S)
    (z : ℝ) :
    (∫ ω, ∏ i : ι, if e i ∈ X ω then z else 1 ∂μ) =
      ∏ i, (1 - hQ.eigenvalues i + z * hQ.eigenvalues i) := by
  rw [h.window_count_generating e hpos, hQ.det_one_add_smul_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  ring

end RiemannResearch.Probability.DPP
