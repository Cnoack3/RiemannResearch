import RiemannResearch.LinearAlgebra.ConditionalSchurDecomposition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Exact Woodbury inverse and marked spectral energy

Source: user-provided argument,
`RH_Controlled_Conductor_Schur_2026-09-10.md`, Section 4.
All inverses below are genuine linear equivalences. The Schur operator is
identified with `D + A* A`; neither that identity nor invertibility is
silently attached to a formal inverse symbol. The spectral formulas retain
the squared coordinates of the actual marked vector.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.LinearAlgebra.ConditionalSchur

section Algebra

variable {H E : Type*} [AddCommGroup H] [Module ℝ H]
  [AddCommGroup E] [Module ℝ E]

/-- `I + A D⁻¹ A*`, before proving its invertibility. -/
def woodburyForward (A : E →ₗ[ℝ] H) (At : H →ₗ[ℝ] E) (D : E ≃ₗ[ℝ] E) : H →ₗ[ℝ] H :=
  LinearMap.id + A.comp (D.symm.toLinearMap.comp At)

/-- `I - A S⁻¹ A*`, the explicit candidate inverse. -/
def woodburyInverse (A : E →ₗ[ℝ] H) (At : H →ₗ[ℝ] E) (S : E ≃ₗ[ℝ] E) : H →ₗ[ℝ] H :=
  LinearMap.id - A.comp (S.symm.toLinearMap.comp At)

variable (A : E →ₗ[ℝ] H) (At : H →ₗ[ℝ] E) (D S : E ≃ₗ[ℝ] E)
  (hS : ∀ b, S b = D b + At (A b))

include hS

theorem woodbury_normal_identity (e : H) :
    At (e - A (S.symm (At e))) = D (S.symm (At e)) := by
  have h : D (S.symm (At e)) + At (A (S.symm (At e))) = At e := by
    rw [← hS, S.apply_symm_apply]
  rw [map_sub]
  exact sub_eq_iff_eq_add.mpr h.symm

theorem woodbury_forward_inverse (e : H) :
    woodburyForward A At D (woodburyInverse A At S e) = e := by
  change (e - A (S.symm (At e))) +
    A (D.symm (At (e - A (S.symm (At e))))) = e
  rw [woodbury_normal_identity A At D S hS, D.symm_apply_apply]
  abel

theorem woodbury_inverse_forward (e : H) :
    woodburyInverse A At S (woodburyForward A At D e) = e := by
  have h : S (D.symm (At e)) = At (e + A (D.symm (At e))) := by
    rw [hS, D.apply_symm_apply, map_add]
  have hi : S.symm (At (e + A (D.symm (At e)))) = D.symm (At e) := by
    rw [← h, S.symm_apply_apply]
  change e + A (D.symm (At e)) -
    A (S.symm (At (e + A (D.symm (At e))))) = e
  rw [hi]
  abel

/-- Woodbury is an actual two-sided inverse, including rectangular `A`. -/
def woodburyEquiv : H ≃ₗ[ℝ] H :=
  LinearEquiv.ofLinear (woodburyForward A At D) (woodburyInverse A At S)
    (by ext e; exact woodbury_forward_inverse A At D S hS e)
    (by ext e; exact woodbury_inverse_forward A At D S hS e)

theorem woodburyEquiv_apply (e : H) :
    woodburyEquiv A At D S hS e = e + A (D.symm (At e)) := rfl

theorem woodburyEquiv_symm_apply (e : H) :
    (woodburyEquiv A At D S hS).symm e = e - A (S.symm (At e)) := rfl

end Algebra

section Hilbert

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (A : E →ₗ[ℝ] H) (At : H →ₗ[ℝ] E) (D S : E ≃ₗ[ℝ] E)
  (hS : ∀ b, S b = D b + At (A b))
  (hAt : ∀ b e, inner ℝ (A b) e = inner ℝ b (At e))

include hAt

/-- The optimized mean error plus full covariance equals the Woodbury
resolvent energy. This uses the exact adjoint and exact Schur operator. -/
theorem woodbury_minimum_energy (e : H) :
    ‖e - A (S.symm (At e))‖ ^ 2 +
      inner ℝ (S.symm (At e)) (D (S.symm (At e))) =
        inner ℝ e ((woodburyEquiv A At D S hS).symm e) := by
  rw [woodburyEquiv_symm_apply, norm_sub_sq_real, inner_sub_right,
    real_inner_self_eq_norm_sq]
  have h := hAt (S.symm (At e)) (e - A (S.symm (At e)))
  rw [woodbury_normal_identity A At D S hS, inner_sub_right,
    real_inner_self_eq_norm_sq] at h
  have hc : inner ℝ (A (S.symm (At e))) e = inner ℝ e (A (S.symm (At e))) :=
    real_inner_comm _ _
  linarith [hc]

/-- Positive innovation covariance makes the information operator positive
on every marked vector; no bound on its size is asserted. -/
theorem information_energy_nonneg
    (hD : ∀ b, 0 ≤ inner ℝ b (D b)) (e : H) :
    0 ≤ inner ℝ e (A (D.symm (At e))) := by
  rw [real_inner_comm, hAt]
  simpa only [D.apply_symm_apply] using hD (D.symm (At e))

end Hilbert

section Spectral

variable {H E ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [AddCommGroup E] [Module ℝ E] [Fintype ι]
variable (A : E →ₗ[ℝ] H) (At : H →ₗ[ℝ] E) (D S : E ≃ₗ[ℝ] E)
  (hS : ∀ b, S b = D b + At (A b))
  (v : OrthonormalBasis ι ℝ H) (lam : ι → ℝ)
  (hlam : ∀ i, 0 ≤ lam i)
  (hEig : ∀ i, A (D.symm (At (v i))) = lam i • v i)

include hlam hEig

theorem woodbury_inverse_on_eigenvector (i : ι) :
    (woodburyEquiv A At D S hS).symm (v i) = (1 + lam i)⁻¹ • v i := by
  have hn : 1 + lam i ≠ 0 := ne_of_gt (by linarith [hlam i])
  apply (woodburyEquiv A At D S hS).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, woodburyEquiv_apply, hEig]
  rw [show v i + lam i • v i = (1 + lam i) • v i by rw [add_smul, one_smul]]
  rw [smul_smul, inv_mul_cancel₀ hn, one_smul]

theorem woodbury_inverse_coordinates (e : H) :
    (woodburyEquiv A At D S hS).symm e =
      ∑ i, (inner ℝ (v i) e / (1 + lam i)) • v i := by
  calc
    _ = (woodburyEquiv A At D S hS).symm
        (∑ i, (v.repr e).ofLp i • v i) := by rw [v.sum_repr]
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, woodbury_inverse_on_eigenvector A At D S hS v lam hlam hEig,
        smul_smul, v.repr_apply_apply, div_eq_mul_inv]

/-- Exact residual-weighted spectral formula, not an extremal-eigenvalue
replacement. Zero eigenvalues retain their entire marked mass. -/
theorem woodbury_marked_energy (e : H) :
    inner ℝ e ((woodburyEquiv A At D S hS).symm e) =
      ∑ i, (inner ℝ (v i) e) ^ 2 / (1 + lam i) := by
  rw [woodbury_inverse_coordinates A At D S hS v lam hlam hEig, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right, real_inner_comm e (v i)]
  ring

theorem woodbury_marked_gain (e : H) :
    ‖e‖ ^ 2 - inner ℝ e ((woodburyEquiv A At D S hS).symm e) =
      ∑ i, (lam i / (1 + lam i)) * (inner ℝ (v i) e) ^ 2 := by
  have hn : ‖e‖ ^ 2 = ∑ i, (inner ℝ (v i) e) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← v.sum_inner_mul_inner e e]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm e (v i)]
    ring
  rw [hn, woodbury_marked_energy A At D S hS v lam hlam hEig,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hne : 1 + lam i ≠ 0 := ne_of_gt (by linarith [hlam i])
  field_simp [hne]
  ring

end Spectral

section CanonicalSpectrum

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The information operator is symmetric because the full covariance is
symmetric. Inverting the covariance does not discard any mixed entry. -/
theorem informationOperator_isSymmetric
    (A : E →ₗ[ℝ] H) (At : H →ₗ[ℝ] E) (D : E ≃ₗ[ℝ] E)
    (hAt : ∀ b e, inner ℝ (A b) e = inner ℝ b (At e))
    (hD : ∀ b c, inner ℝ (D b) c = inner ℝ b (D c)) :
    (A.comp (D.symm.toLinearMap.comp At)).IsSymmetric := by
  intro x y
  change inner ℝ (A (D.symm (At x))) y = inner ℝ x (A (D.symm (At y)))
  calc
    _ = inner ℝ (D.symm (At x)) (At y) := hAt _ _
    _ = inner ℝ (At x) (D.symm (At y)) := by
      have h := hD (D.symm (At x)) (D.symm (At y))
      simpa only [D.apply_symm_apply] using h.symm
    _ = _ := by
      have h1 : inner ℝ (At x) (D.symm (At y)) =
          inner ℝ (D.symm (At y)) (At x) := real_inner_comm _ _
      have h2 : inner ℝ x (A (D.symm (At y))) =
          inner ℝ (A (D.symm (At y))) x := real_inner_comm _ _
      linarith [hAt (D.symm (At y)) x]

/-- A genuine orthonormal eigensystem and both marked spectral formulas
exist for every finite-dimensional coarse space. Eigenvalue positivity is
derived from the actual covariance quadratic form. -/
theorem exists_information_spectral_formula [FiniteDimensional ℝ H]
    (A : E →ₗ[ℝ] H) (At : H →ₗ[ℝ] E) (D S : E ≃ₗ[ℝ] E)
    (hS : ∀ b, S b = D b + At (A b))
    (hAt : ∀ b e, inner ℝ (A b) e = inner ℝ b (At e))
    (hDsymm : ∀ b c, inner ℝ (D b) c = inner ℝ b (D c))
    (hDpos : ∀ b, 0 ≤ inner ℝ b (D b)) :
    ∃ (v : OrthonormalBasis (Fin (Module.finrank ℝ H)) ℝ H)
      (lam : Fin (Module.finrank ℝ H) → ℝ),
      (∀ i, 0 ≤ lam i) ∧
      (∀ i, A (D.symm (At (v i))) = lam i • v i) ∧
      (∀ e, inner ℝ e ((woodburyEquiv A At D S hS).symm e) =
        ∑ i, (inner ℝ (v i) e) ^ 2 / (1 + lam i)) ∧
      (∀ e, ‖e‖ ^ 2 - inner ℝ e ((woodburyEquiv A At D S hS).symm e) =
        ∑ i, (lam i / (1 + lam i)) * (inner ℝ (v i) e) ^ 2) := by
  let R : H →ₗ[ℝ] H := A.comp (D.symm.toLinearMap.comp At)
  have hR : R.IsSymmetric := informationOperator_isSymmetric A At D hAt hDsymm
  let v := hR.eigenvectorBasis rfl
  let lam := hR.eigenvalues rfl
  have heig (i : Fin (Module.finrank ℝ H)) :
      A (D.symm (At (v i))) = lam i • v i := by
    exact hR.apply_eigenvectorBasis rfl i
  have hnonneg (i : Fin (Module.finrank ℝ H)) : 0 ≤ lam i := by
    have h := information_energy_nonneg A At D hAt hDpos (v i)
    rw [heig, real_inner_smul_right, real_inner_self_eq_norm_sq,
      v.orthonormal.norm_eq_one i] at h
    simpa only [one_pow, mul_one] using h
  refine ⟨v, lam, hnonneg, heig, ?_, ?_⟩
  · intro e
    exact woodbury_marked_energy A At D S hS v lam hnonneg heig e
  · intro e
    exact woodbury_marked_gain A At D S hS v lam hnonneg heig e

end CanonicalSpectrum

end RiemannResearch.LinearAlgebra.ConditionalSchur
