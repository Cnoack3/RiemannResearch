import RiemannResearch.Probability.ContinuousProjectionCompression

/-!
# Kernel Hilbert--Schmidt mass and window boundary leakage

The mixed-window Hilbert--Schmidt mass is the trace of the product of the
two actual restricted Gram matrices. For orthonormal modes the complementary
window therefore realizes exactly the spectral count variance.

Source: Hough--Krishnapur--Peres--Virág, *Determinantal Processes and
Independence*, Probability Surveys 3 (2006), Theorem 7, for the spectral-count
interpretation. The kernel identities below follow directly by integrating
finite sums, so no infinite DPP or limiting assertion is used.
-/

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate

namespace ProbabilityTheory.ContinuousProjectionDPP
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] {n : ℕ}

private theorem window_kernel_pair_expansion (ψ : Fin n → X → ℂ) (x y : X) :
    kernel ψ x y * kernel ψ y x =
      ∑ i, ∑ j, (conj (ψ i x) * ψ j x) * (conj (ψ j y) * ψ i y) := by
  simp only [kernel, Finset.sum_mul, Finset.mul_sum, Complex.star_def]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The Hermitian kernel product is the real nonnegative squared norm. -/
theorem kernel_pair_eq_norm_sq (ψ : Fin n → X → ℂ) (x y : X) :
    kernel ψ x y * kernel ψ y x = ((‖kernel ψ x y‖ ^ 2 : ℝ) : ℂ) := by
  rw [← kernel_hermitian ψ y x]
  simpa only [Complex.star_def, Complex.normSq_eq_norm_sq] using
    Complex.mul_conj (kernel ψ x y)

/-- The mixed-window kernel product is the trace of the two actual compressions.
Only finite sums and square-integrable modes are used. -/
theorem window_kernel_pair_integral (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ) (I J : Set X) :
    (∫ x in I, ∫ y in J, kernel ψ x y * kernel ψ y x ∂μ ∂μ) =
      (windowCompression μ ψ I * windowCompression μ ψ J).trace := by
  have hc (i j : Fin n) : Integrable (fun x => conj (ψ i x) * ψ j x) μ :=
    integrable_cross_of_memLp ψ hψ i j
  have he (x : X) :
      (∫ y in J, kernel ψ x y * kernel ψ y x ∂μ) =
        ∑ i, ∑ j, (conj (ψ i x) * ψ j x) * windowCompression μ ψ J j i := by
    simp_rw [window_kernel_pair_expansion]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum]
      · simp only [integral_const_mul, windowCompression]
      · intro j hj
        exact (hc j i).integrableOn.const_mul _
    · intro i hi
      apply integrable_finsetSum
      intro j hj
      exact (hc j i).integrableOn.const_mul _
  simp_rw [he]
  rw [integral_finsetSum]
  · simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · simp only [integral_mul_const, windowCompression]
    · intro j hj
      exact (hc i j).integrableOn.mul_const _
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (hc i j).integrableOn.mul_const _

/-- Mixed-window Hilbert--Schmidt mass, with the real integral made explicit. -/
theorem window_kernel_norm_sq_integral (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ) (I J : Set X) :
    ((∫ x in I, ∫ y in J, ‖kernel ψ x y‖ ^ 2 ∂μ ∂μ : ℝ) : ℂ) =
      (windowCompression μ ψ I * windowCompression μ ψ J).trace := by
  have h := window_kernel_pair_integral μ ψ hψ I J
  simp only [kernel_pair_eq_norm_sq] at h
  simp_rw [integral_complex_ofReal] at h
  exact h

/-- The finite matrix Hilbert--Schmidt square is exactly that of the actual
arithmetic kernel restricted to the same window in both variables. -/
theorem windowCompression_hilbertSchmidt_eq_kernel_integral (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ) (I : Set X) :
    (∑ i, ∑ j, ‖windowCompression μ ψ I i j‖ ^ 2) =
      ∫ x in I, ∫ y in I, ‖kernel ψ x y‖ ^ 2 ∂μ ∂μ := by
  apply Complex.ofReal_injective
  rw [window_kernel_norm_sq_integral μ ψ hψ I I]
  exact (windowCompression_isHermitian μ ψ I).trace_mul_self_eq_sum_norm_sq.symm

/-- For orthonormal modes, the cross-boundary kernel energy is the trace defect. -/
theorem window_kernel_boundary_eq_trace_defect (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ x, conj (ψ i x) * ψ j x ∂μ) = if i = j then 1 else 0)
    {I : Set X} (hI : MeasurableSet I) :
    ((∫ x in I, ∫ y in Iᶜ, ‖kernel ψ x y‖ ^ 2 ∂μ ∂μ : ℝ) : ℂ) =
      (windowCompression μ ψ I).trace -
        (windowCompression μ ψ I * windowCompression μ ψ I).trace := by
  rw [window_kernel_norm_sq_integral μ ψ hψ I Iᶜ,
    windowCompression_compl μ ψ hψ ho hI, Matrix.mul_sub, Matrix.mul_one,
    Matrix.trace_sub]

/-- Exact spectral variance as physical cross-boundary leakage. -/
theorem window_kernel_boundary_eq_eigenvalue_variance (ψ : Fin n → X → ℂ)
    (hψ : ∀ i, MemLp (ψ i) 2 μ)
    (ho : ∀ i j, (∫ x, conj (ψ i x) * ψ j x ∂μ) = if i = j then 1 else 0)
    {I : Set X} (hI : MeasurableSet I) :
    (∫ x in I, ∫ y in Iᶜ, ‖kernel ψ x y‖ ^ 2 ∂μ ∂μ) =
      ∑ i, (windowCompression_isHermitian μ ψ I).eigenvalues i *
        (1 - (windowCompression_isHermitian μ ψ I).eigenvalues i) := by
  apply Complex.ofReal_injective
  rw [window_kernel_boundary_eq_trace_defect μ ψ hψ ho hI]
  exact (windowCompression_isHermitian μ ψ I).trace_sub_square_eq_sum_eigenvalue_variance

end ProbabilityTheory.ContinuousProjectionDPP
