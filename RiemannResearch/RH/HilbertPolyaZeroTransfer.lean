import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Analytic.Order
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith
import RiemannResearch.RH.HilbertPolyaPositiveProduct
import RiemannResearch.RH.RiemannHypothesisStrip

/-!
# Hilbert–Pólya transfer on a specified operator domain

Source: §8 of the user-provided Mellin/prime-orbit PCC handoff. The parameter
of a complex zero is `-I * (ρ - 1/2)`, which retains its real part. A densely
defined self-adjoint Hamiltonian is symmetric on its domain; this elementary
point-spectrum argument needs only that symmetry. The correspondence between
zeta zeros and eigenspaces is an explicit hypothesis.
-/

namespace RiemannResearch.RH.HilbertPolya

open Zeta23

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {D : Submodule ℂ E}

/-- An eigenspace in the specified domain. The operator need not preserve its domain. -/
noncomputable def domainEigenspace (H : D →ₗ[ℂ] E) (z : ℂ) : Submodule ℂ D :=
  (H - z • D.subtype).ker

/-- The symmetric operator identity on the domain of definition. -/
def SymmetricOnDomain (H : D →ₗ[ℂ] E) : Prop :=
  ∀ x y : D, inner ℂ (H x) (y : E) = inner ℂ (x : E) (H y)

/-- A nonzero eigenspace of a symmetric operator has a real parameter. -/
theorem im_eq_zero_of_domainEigenspace_ne_bot {H : D →ₗ[ℂ] E}
    (hH : SymmetricOnDomain H) {z : ℂ} (hz : domainEigenspace H z ≠ ⊥) :
    z.im = 0 := by
  obtain ⟨x, hx, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hz
  change H x - z • (x : E) = 0 at hx
  have he := sub_eq_zero.mp hx
  have hxE : (x : E) ≠ 0 := fun h => hx₀ (Subtype.ext h)
  have hs := hH x x
  rw [he, inner_smul_left, inner_smul_right] at hs
  have hc : starRingEnd ℂ z = z := mul_right_cancel₀ (inner_self_ne_zero.mpr hxE) hs
  have hi := congrArg Complex.im hc
  change -z.im = z.im at hi
  linarith

/-- Point-spectrum coverage of every nontrivial zero implies mathlib's RH. -/
theorem riemannHypothesis_of_eigenspace_coverage {H : D →ₗ[ℂ] E}
    (hH : SymmetricOnDomain H)
    (hcover : ∀ ρ : ℂ, IsNontrivialZero ρ → domainEigenspace H (spectralCoordinate ρ) ≠ ⊥) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hi := im_eq_zero_of_domainEigenspace_ne_bot hH (hcover ρ ⟨hz, h0, h1⟩)
  rw [spectralCoordinate_im] at hi
  linarith

/-- Matching a zero's analytic order forces a positive eigenspace dimension. -/
theorem finrank_pos_of_matched_order {H : D →ₗ[ℂ] E} {ρ : ℂ} (hρ : IsNontrivialZero ρ)
    (horder : analyticOrderAt riemannZeta ρ =
      (Module.finrank ℂ (domainEigenspace H (spectralCoordinate ρ)) : ℕ∞)) :
    0 < Module.finrank ℂ (domainEigenspace H (spectralCoordinate ρ)) := by
  apply Nat.pos_of_ne_zero
  intro hd
  have ha : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ.not_trivial.2
  exact (ha.analyticOrderAt_ne_zero.mpr hρ.1) (by simpa [hd] using horder)

/-- A faithful multiplicity correspondence already supplies point-spectrum coverage. -/
theorem riemannHypothesis_of_spectral_orders {H : D →ₗ[ℂ] E} (hH : SymmetricOnDomain H)
    (horder : ∀ ρ : ℂ, IsNontrivialZero ρ →
      analyticOrderAt riemannZeta ρ =
        (Module.finrank ℂ (domainEigenspace H (spectralCoordinate ρ)) : ℕ∞)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_eigenspace_coverage hH
  intro ρ hρ hbot
  have hd := finrank_pos_of_matched_order hρ (horder ρ hρ)
  rw [hbot, finrank_bot] at hd
  exact Nat.lt_irrefl _ hd

/-- A faithful analytic-order correspondence and at most one-dimensional matched
eigenspaces give RH and analytic simplicity at every nontrivial zero. -/
theorem riemannHypothesis_and_simple_of_spectral_orders {H : D →ₗ[ℂ] E}
    (hH : SymmetricOnDomain H)
    (horder : ∀ ρ : ℂ, IsNontrivialZero ρ →
      analyticOrderAt riemannZeta ρ = (Module.finrank ℂ (domainEigenspace H (spectralCoordinate ρ)) : ℕ∞))
    (hdim : ∀ ρ : ℂ, IsNontrivialZero ρ →
      Module.finrank ℂ (domainEigenspace H (spectralCoordinate ρ)) ≤ 1) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ →
      analyticOrderAt riemannZeta ρ = 1 ∧ deriv riemannZeta ρ ≠ 0 := by
  refine ⟨riemannHypothesis_of_spectral_orders hH horder, ?_⟩
  intro ρ hρ
  have hζ : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ.not_trivial.2
  have hd := le_antisymm (hdim ρ hρ) (finrank_pos_of_matched_order hρ (horder ρ hρ))
  have hm : analyticOrderAt riemannZeta ρ = 1 := by simpa [hd] using horder ρ hρ
  refine ⟨hm, hζ.deriv.analyticOrderAt_eq_zero.mp ?_⟩
  simpa using analyticOrderAt_deriv_of_pos hζ (n := 0) (by simpa using hm)

end RiemannResearch.RH.HilbertPolya
