import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Residual certificates for finite nonsymmetric collocation

Source: independently derived for the user's GROW-001 investigation,
13 November 2026. A prescribed source and an arbitrary predictor yield a
rigorous signed-energy certificate. The inverse is the actual collocation
inverse, never a substituted physical Gram inverse. No division by residual
energy or capacity is used.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteCollocationCertificate

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def response (A : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → H) :
    (ι → ℝ) →ₗ[ℝ] H :=
  (Fintype.linearCombination ℝ v).comp A.symm.toLinearMap

def responseColumn (A : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → H) (i : ι) : H :=
  response A v (Pi.single i 1)

def residualRadius (A : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → H)
    (ρ : ι → ℝ) : ℝ :=
  ∑ i, |ρ i| * ‖responseColumn A v i‖

theorem response_expansion (A : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → H)
    (ρ : ι → ℝ) :
    response A v ρ = ∑ i, ρ i • responseColumn A v i := by
  have he : ρ = ∑ i, ρ i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  conv_lhs => rw [he]
  rw [map_sum]
  simp only [map_smul, responseColumn]

theorem residualRadius_nonneg (A : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → H)
    (ρ : ι → ℝ) : 0 ≤ residualRadius A v ρ := by
  unfold residualRadius
  positivity

theorem response_norm_le (A : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → H)
    (ρ : ι → ℝ) : ‖response A v ρ‖ ≤ residualRadius A v ρ := by
  rw [response_expansion]
  calc
    ‖∑ i, ρ i • responseColumn A v i‖ ≤
        ∑ i, ‖ρ i • responseColumn A v i‖ := norm_sum_le _ _
    _ = residualRadius A v ρ := by simp [residualRadius, norm_smul]

omit [DecidableEq ι] in
theorem response_residual (A : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → H)
    (β z : ι → ℝ) :
    response A v β = Fintype.linearCombination ℝ v z + response A v (β - A z) := by
  simp only [map_sub]
  have he : response A v (A z) = Fintype.linearCombination ℝ v z := by
    change Fintype.linearCombination ℝ v (A.symm (A z)) = _
    rw [A.symm_apply_apply]
  rw [he]
  abel

omit [DecidableEq ι] in
theorem signed_energy_residual (A : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → H)
    (f : H) (β z : ι → ℝ) :
    ‖f + response A v β‖ ^ 2 - ‖f‖ ^ 2 =
      2 * inner ℝ f (Fintype.linearCombination ℝ v z) +
      ‖Fintype.linearCombination ℝ v z‖ ^ 2 +
      2 * inner ℝ (f + Fintype.linearCombination ℝ v z) (response A v (β - A z)) +
      ‖response A v (β - A z)‖ ^ 2 := by
  rw [response_residual A v β z, ← add_assoc, norm_add_sq_real, norm_add_sq_real]
  ring

theorem signed_energy_le_radius (A : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → H)
    (f : H) (β z : ι → ℝ) :
    ‖f + response A v β‖ ^ 2 - ‖f‖ ^ 2 ≤
      2 * inner ℝ f (Fintype.linearCombination ℝ v z) +
      ‖Fintype.linearCombination ℝ v z‖ ^ 2 +
      2 * ‖f + Fintype.linearCombination ℝ v z‖ * residualRadius A v (β - A z) +
      residualRadius A v (β - A z) ^ 2 := by
  rw [signed_energy_residual A v f β z]
  have he := response_norm_le A v (β - A z)
  have hr := residualRadius_nonneg A v (β - A z)
  have hn := norm_nonneg (response A v (β - A z))
  have hf := norm_nonneg (f + Fintype.linearCombination ℝ v z)
  have hi := real_inner_le_norm (f + Fintype.linearCombination ℝ v z)
    (response A v (β - A z))
  have hm := mul_le_mul_of_nonneg_left he hf
  nlinarith

theorem response_eq_of_radius_zero (A : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → H)
    (β z : ι → ℝ) (hzero : residualRadius A v (β - A z) = 0) :
    response A v β = Fintype.linearCombination ℝ v z := by
  have hn := response_norm_le A v (β - A z)
  rw [hzero] at hn
  have he : response A v (β - A z) = 0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  rw [response_residual A v β z, he, add_zero]

/-- A squared-source estimate must retain the matching inverse-column cost. -/
theorem response_norm_sq_le_column_energy
    (A : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) (v : ι → H) (ρ : ι → ℝ) :
    ‖response A v ρ‖ ^ 2 ≤
      (∑ i, ρ i ^ 2) * (∑ i, ‖responseColumn A v i‖ ^ 2) := by
  have hn := response_norm_le A v ρ
  have hr := residualRadius_nonneg A v ρ
  have he := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |ρ i|) (fun i => ‖responseColumn A v i‖)
  have hh : residualRadius A v ρ ^ 2 ≤
      (∑ i, ρ i ^ 2) * (∑ i, ‖responseColumn A v i‖ ^ 2) := by
    simpa only [residualRadius, sq_abs] using he
  have hnonneg := norm_nonneg (response A v ρ)
  nlinarith

omit [DecidableEq ι] in
/-- Positive diagonal row rescaling leaves the inverse-column radius unchanged.
Residual rows multiply by a; their response columns multiply by a⁻¹. -/
theorem radius_rescaling (ρ a : ι → ℝ) (w : ι → H)
    (ha : ∀ i, 0 < a i) :
    (∑ i, |a i * ρ i| * ‖(a i)⁻¹ • w i‖) =
      ∑ i, |ρ i| * ‖w i‖ := by
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_mul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (ha i)]
  field_simp [ne_of_gt (ha i)]


end RiemannResearch.Analysis.FiniteCollocationCertificate
