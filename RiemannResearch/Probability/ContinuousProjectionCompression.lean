import RiemannResearch.Probability.ContinuousProjectionKernel
import RiemannResearch.Analysis.PositiveSpectralPolynomial
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finite continuous projection window compressions

The compression is the actual restricted Gram matrix of the orthonormal
features. It is a positive contraction for every measurable window, without
any infinite-process assumption. The spectral determinant is the standard
finite-dimensional step in the DPP Bernoulli-count theorem.

Source: Hough--Krishnapur--Peres--Virág, *Determinantal Processes and
Independence*, Probability Surveys 3 (2006), Theorem 7, for the spectral-count
strategy. The present proofs use restricted L² Gram matrices and Mathlib's
finite Hermitian spectral theorem.
-/

noncomputable section
open MeasureTheory Matrix Unitary
open scoped BigOperators ComplexConjugate ComplexOrder

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℂ}

/-- Complex determinant factorization; the eigenvalues themselves are real. -/
theorem IsHermitian.det_one_add_smul_eq_prod_complex (hQ : Q.IsHermitian) (t : ℂ) :
    (1 + t • Q).det = ∏ i, (1 + t * (hQ.eigenvalues i : ℂ)) := by
  let U := hQ.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have hQ' : Q = f (Matrix.diagonal (fun i => (hQ.eigenvalues i : ℂ))) := by
    simpa [f, U, Function.comp_def] using hQ.spectral_theorem
  have hdiag : (1 : Matrix ι ι ℂ) + t • Matrix.diagonal (fun i => (hQ.eigenvalues i : ℂ)) =
      Matrix.diagonal (fun i => 1 + t * (hQ.eigenvalues i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal, hij]
  have he : (1 : Matrix ι ι ℂ) + t • Q =
      f (Matrix.diagonal (fun i => 1 + t * (hQ.eigenvalues i : ℂ))) := by
    rw [← hdiag, map_add, map_one, map_smul, ← hQ']
  rw [he]
  change (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
    (Matrix.diagonal (fun i => 1 + t * (hQ.eigenvalues i : ℂ)))).det = _
  rw [Unitary.conjStarAlgAut_apply, Matrix.det_mul_comm,
    ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.det_diagonal]

/-- The real eigenvalues of a complex positive contraction lie in `[0,1]`. -/
theorem PosSemidef.complex_eigenvalues_mem_Icc (hQ : Q.PosSemidef)
    (hI : (1 - Q).PosSemidef) (i : ι) :
    hQ.isHermitian.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨hQ.eigenvalues_nonneg i, ?_⟩
  let U := hQ.isHermitian.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  have hQ' : Q = f (Matrix.diagonal (fun i => (hQ.isHermitian.eigenvalues i : ℂ))) := by
    simpa [f, U, Function.comp_def] using hQ.isHermitian.spectral_theorem
  have he : (1 : Matrix ι ι ℂ) - Q =
      f (1 - Matrix.diagonal (fun i => (hQ.isHermitian.eigenvalues i : ℂ))) := by
    rw [map_sub, map_one, ← hQ']
  rw [he] at hI
  have hd : ((1 : Matrix ι ι ℂ) -
      Matrix.diagonal (fun i => (hQ.isHermitian.eigenvalues i : ℂ))).PosSemidef := by
    simpa only [f, Unitary.conjStarAlgAut_apply,
      Unitary.isUnit_coe.posSemidef_star_right_conjugate_iff] using hI
  have hn := hd.diag_nonneg (i := i)
  have hr := (RCLike.nonneg_iff.mp hn).1
  simpa [sub_nonneg] using hr

/-- Exact Hilbert--Schmidt expression for the square trace. -/
theorem IsHermitian.trace_mul_self_eq_sum_norm_sq (hQ : Q.IsHermitian) :
    (Q * Q).trace = ((∑ i, ∑ j, ‖Q i j‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hji : star (Q i j) = Q j i := congrFun (congrFun hQ j) i
  rw [← hji]
  simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using Complex.mul_conj (Q i j)

/-- Exact spectral expression for the square trace. -/
theorem IsHermitian.trace_mul_self_eq_sum_eigenvalues_sq (hQ : Q.IsHermitian) :
    (Q * Q).trace = ∑ i, (hQ.eigenvalues i : ℂ) ^ 2 := by
  let U := hQ.eigenvectorUnitary
  let f := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (hQ.eigenvalues i : ℂ))
  have hQ' : Q = f D := by
    simpa [f, U, D, Function.comp_def] using hQ.spectral_theorem
  have he : Q * Q = f (D * D) := by rw [map_mul, ← hQ']
  rw [he]
  change (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U (D * D)).trace = _
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul]
  simp [D, Matrix.diagonal_mul_diagonal, pow_two]

/-- The spectral variance is exactly the trace minus the Hilbert--Schmidt square. -/
theorem IsHermitian.trace_sub_square_eq_sum_eigenvalue_variance (hQ : Q.IsHermitian) :
    Q.trace - (Q * Q).trace =
      ((∑ i, hQ.eigenvalues i * (1 - hQ.eigenvalues i) : ℝ) : ℂ) := by
  rw [hQ.trace_eq_sum_eigenvalues, hQ.trace_mul_self_eq_sum_eigenvalues_sq,
    ← Finset.sum_sub_distrib]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one]
  apply Finset.sum_congr rfl
  intro i hi
  change (hQ.eigenvalues i : ℂ) - (hQ.eigenvalues i : ℂ) ^ 2 =
    (hQ.eigenvalues i : ℂ) * (1 - (hQ.eigenvalues i : ℂ))
  ring

theorem IsHermitian.sum_eigenvalue_variance_eq_trace_sub_hilbertSchmidt
    (hQ : Q.IsHermitian) :
    ((∑ i, hQ.eigenvalues i * (1 - hQ.eigenvalues i) : ℝ) : ℂ) =
      Q.trace - ((∑ i, ∑ j, ‖Q i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [← hQ.trace_mul_self_eq_sum_norm_sq]
  exact hQ.trace_sub_square_eq_sum_eigenvalue_variance.symm


/-- The even determinant of a positive matrix has only real zeros.
This is the finite self-adjoint step of the Hilbert--Polya proposal;
it does not identify this determinant with the completed zeta function. -/
theorem PosSemidef.det_one_sub_sq_smul_zero_im_eq_zero
    (hQ : Q.PosSemidef) (z : ℂ)
    (hz : (1 - z ^ 2 • Q).det = 0) : z.im = 0 := by
  have he : (1 - z ^ 2 • Q).det =
      ∏ i, (1 - z ^ 2 * (hQ.isHermitian.eigenvalues i : ℂ)) := by
    simpa only [sub_eq_add_neg, neg_smul, neg_mul] using
      hQ.isHermitian.det_one_add_smul_eq_prod_complex (-(z ^ 2))
  rw [he] at hz
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz
  exact RiemannResearch.Analysis.PositiveSpectralPolynomial.factor_zero_im_eq_zero
    (hQ.isHermitian.eigenvalues i) (hQ.eigenvalues_nonneg i) z hi

theorem PosSemidef.det_one_sub_sq_smul_ne_zero_of_nonreal
    (hQ : Q.PosSemidef) (z : ℂ) (hz : z.im ≠ 0) :
    (1 - z ^ 2 • Q).det ≠ 0 := by
  intro h
  exact hz (hQ.det_one_sub_sq_smul_zero_im_eq_zero z h)

end Matrix

namespace ProbabilityTheory.ContinuousProjectionDPP
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] {n : ℕ}

/-- The actual matrix obtained by restricting all orthonormal modes to a window. -/
def windowCompression (ψ : Fin n → X → ℂ) (I : Set X) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∫ x in I, conj (ψ i x) * ψ j x ∂μ

theorem windowCompression_isHermitian (ψ : Fin n → X → ℂ) (I : Set X) :
    (windowCompression μ ψ I).IsHermitian := by
  change (windowCompression μ ψ I).conjTranspose = windowCompression μ ψ I
  ext i j
  change conj (∫ x in I, conj (ψ j x) * ψ i x ∂μ) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [map_mul, Complex.conj_conj, windowCompression]
  ring

/-- A compression is the Gram matrix in the restricted L² space. -/
theorem windowCompression_posSemidef (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ) (I : Set X) :
    (windowCompression μ ψ I).PosSemidef := by
  let hr (i : Fin n) : MemLp (ψ i) 2 (μ.restrict I) :=
    (hψ i).mono_measure Measure.restrict_le_self
  let v (i : Fin n) : Lp ℂ 2 (μ.restrict I) := (hr i).toLp (ψ i)
  have he : windowCompression μ ψ I = Matrix.gram ℂ v := by
    ext i j
    rw [Matrix.gram_apply, L2.inner_def]
    change (∫ x, conj (ψ i x) * ψ j x ∂μ.restrict I) = _
    apply integral_congr_ae
    filter_upwards [(hr i).coeFn_toLp, (hr j).coeFn_toLp] with x hi hj
    simp only [v] at *
    rw [hi, hj]
    simp [RCLike.inner_apply, mul_comm]
  rw [he]
  exact Matrix.posSemidef_gram ℂ v

theorem windowCompression_compl (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ x, conj (ψ i x) * ψ j x ∂μ) = if i = j then 1 else 0)
    {I : Set X} (hI : MeasurableSet I) :
    windowCompression μ ψ Iᶜ = 1 - windowCompression μ ψ I := by
  ext i j
  change (∫ x in Iᶜ, conj (ψ i x) * ψ j x ∂μ) = _
  rw [setIntegral_compl hI (integrable_cross_of_memLp ψ hψ i j), ho]
  simp [windowCompression, Matrix.one_apply]

/-- A window compression is an actual positive contraction. -/
theorem one_sub_windowCompression_posSemidef (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ x, conj (ψ i x) * ψ j x ∂μ) = if i = j then 1 else 0)
    {I : Set X} (hI : MeasurableSet I) :
    (1 - windowCompression μ ψ I).PosSemidef := by
  rw [← windowCompression_compl μ ψ hψ ho hI]
  exact windowCompression_posSemidef μ ψ hψ Iᶜ

/-- The actual compression spectrum supplies Bernoulli parameters. -/
theorem windowCompression_eigenvalues_mem_Icc (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ x, conj (ψ i x) * ψ j x ∂μ) = if i = j then 1 else 0)
    {I : Set X} (hI : MeasurableSet I) (i : Fin n) :
    (windowCompression_isHermitian μ ψ I).eigenvalues i ∈ Set.Icc (0 : ℝ) 1 := by
  exact (windowCompression_posSemidef μ ψ hψ I).complex_eigenvalues_mem_Icc
    (one_sub_windowCompression_posSemidef μ ψ hψ ho hI) i

/-- The trace is the window integral of the actual projection kernel diagonal. -/
theorem windowCompression_trace (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ) (I : Set X) :
    (windowCompression μ ψ I).trace = ∫ x in I, kernel ψ x x ∂μ := by
  change (∑ i, ∫ x in I, conj (ψ i x) * ψ i x ∂μ) = _
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with x
    simp [kernel, Complex.star_def, mul_comm]
  · intro i hi
    exact (integrable_cross_of_memLp ψ hψ i i).integrableOn

end ProbabilityTheory.ContinuousProjectionDPP
