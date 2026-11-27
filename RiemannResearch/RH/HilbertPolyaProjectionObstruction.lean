import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import RiemannResearch.Analysis.ActualOrdinateAngularLaw
import RiemannResearch.Analysis.ActualZeroCauchyDensity
import RiemannResearch.RH.HilbertPolyaPositiveProduct

/-!
# An idempotent projection cannot serve as the full zeta Hamiltonian

Source: §8 of the user-provided Mellin/prime-orbit PCC handoff. The point
spectrum of an idempotent has only the possible eigenvalues zero and one.
The repository theorem `exists_high_zero_in_open_angle`, at the full circle,
gives actual zeta zeros above every height. The result obstructs the Mellin
DPP projection itself as the Hamiltonian with the usual spectral coordinate.
-/

namespace RiemannResearch.RH.HilbertPolya

open Zeta23 RiemannResearch.Analysis.ActualZeroOrdinate

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Every point eigenvalue of an idempotent linear map is zero or one. -/
theorem eigenvalue_zero_or_one_of_idempotent (P : E →ₗ[ℂ] E)
    (hP : ∀ x, P (P x) = P x) {z : ℂ} {x : E} (hx : x ≠ 0) (he : P x = z • x) :
    z = 0 ∨ z = 1 := by
  have hh : (z * z) • x = z • x := by
    calc
      (z * z) • x = P (P x) := by rw [he, map_smul, he, mul_smul]
      _ = z • x := (hP x).trans he
  have hzero : (z * z - z) • x = 0 := by rw [sub_smul, hh, sub_self]
  have hz := (smul_eq_zero.mp hzero).resolve_right hx
  have hp : z * (z - 1) = 0 := by rwa [mul_sub, mul_one]
  exact (mul_eq_zero.mp hp).imp_right sub_eq_zero.mp

/-- The actual unbounded zeta ordinates obstruct a complete identification
with the point eigenvalues of any projection, including the Mellin projection. -/
theorem idempotent_cannot_cover_zeta_zeros (P : E →ₗ[ℂ] E) (hP : ∀ x, P (P x) = P x) :
    ¬ ∀ ρ : ℂ, IsNontrivialZero ρ → ∃ x : E, x ≠ 0 ∧ P x = spectralCoordinate ρ • x := by
  intro hcover
  obtain ⟨ρ, hρ, _, hgt, _⟩ := exists_high_zero_in_open_angle
    (fixedStripConcentration_of_sublinearHorizontalEnergy sublinearHorizontalEnergy) 1
    (U := Set.univ) isOpen_univ Set.univ_nonempty
  obtain ⟨x, hx, he⟩ := hcover ρ hρ
  have hre : (spectralCoordinate ρ).re = ρ.im := by simp [spectralCoordinate, Complex.mul_re]
  rcases eigenvalue_zero_or_one_of_idempotent P hP hx he with h | h <;>
    rw [h] at hre <;> simp at hre <;> linarith

/-- Even a bounded linear operator with infinitely many eigenvalues cannot
realize the full, unrescaled zeta ordinates. The putative Hamiltonian with
this spectral coordinate must be unbounded. -/
theorem bounded_operator_cannot_cover_zeta_zeros
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (A : X →L[ℂ] X) :
    ¬ ∀ ρ : ℂ, IsNontrivialZero ρ → ∃ x : X, x ≠ 0 ∧ A x = spectralCoordinate ρ • x := by
  intro hcover
  obtain ⟨ρ, hρ, _, hgt, _⟩ := exists_high_zero_in_open_angle
    (fixedStripConcentration_of_sublinearHorizontalEnergy sublinearHorizontalEnergy) ‖A‖
    (U := Set.univ) isOpen_univ Set.univ_nonempty
  obtain ⟨x, hx, he⟩ := hcover ρ hρ
  have h := A.le_opNorm x
  rw [he, norm_smul] at h
  have hz : ‖spectralCoordinate ρ‖ ≤ ‖A‖ := (le_of_mul_le_mul_right h (norm_pos_iff.mpr hx))
  have hre : (spectralCoordinate ρ).re = ρ.im := by simp [spectralCoordinate, Complex.mul_re]
  exact (not_le_of_gt hgt) (hre ▸ ((Complex.re_le_norm _).trans hz))

end RiemannResearch.RH.HilbertPolya
