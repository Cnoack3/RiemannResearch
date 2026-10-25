/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GeometricPolynomialDensity
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Total geometrically weighted monomials in square-summable coordinates

Source: the user's generating-function density argument, 25 October 2026.
Scalar exponential-moment uniqueness gives the zero-annihilator theorem;
Hilbert orthogonal-complement duality then gives actual norm density in ℓ².
No physical valuation-space or legal-closure assumption enters this theorem.
-/
noncomputable section
open scoped RealInnerProductSpace
namespace RiemannResearch.Analysis

/-- The geometric monomial sequences are square summable. -/
theorem geometricMonomial_memℓp {q : ℝ} (hq0 : 0 < q) (hqle : q ≤ 1/2)
    (m : ℕ) : Memℓp (fun k : ℕ => q^k * (k : ℝ)^m) 2 := by
  have hqn : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq0]
    linarith
  have hs := summable_pow_mul_geometric_of_norm_lt_one m hqn
  have h1 : Memℓp (fun k : ℕ => q^k * (k : ℝ)^m) 1 := by
    apply memℓp_gen
    apply hs.congr
    intro k
    rw [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact mul_comm _ _
  exact h1.of_exponent_ge (by norm_num)

/-- A geometrically weighted monomial as a vector in the complete ℓ² coordinate space. -/
def geometricMonomial (q : ℝ) (hq0 : 0 < q) (hqle : q ≤ 1/2) (m : ℕ) :
    lp (fun _ : ℕ => ℝ) 2 :=
  ⟨fun k => q^k * (k : ℝ)^m, geometricMonomial_memℓp hq0 hqle m⟩

@[simp] theorem geometricMonomial_apply (q : ℝ) (hq0 : 0 < q)
    (hqle : q ≤ 1/2) (m k : ℕ) :
    geometricMonomial q hq0 hqle m k = q^k * (k : ℝ)^m := rfl

/-- A square-summable vector annihilating every weighted monomial is zero. -/
theorem eq_zero_of_orthogonal_geometricMonomial {q : ℝ}
    (hq0 : 0 < q) (hqle : q ≤ 1/2) (x : lp (fun _ : ℕ => ℝ) 2)
    (hx : ∀ m, inner ℝ x (geometricMonomial q hq0 hqle m) = 0) : x = 0 := by
  have hb : ∀ k, ‖x k‖ ≤ ‖x‖ := fun k =>
    lp.norm_apply_le_norm (by norm_num) x k
  have hm : ∀ m, (∑' k : ℕ, (k : ℝ)^m * q^k * x k) = 0 := by
    intro m
    have h := hx m
    simp only [lp.inner_eq_tsum, Real.inner_apply, geometricMonomial_apply] at h
    simpa only [mul_comm, mul_left_comm, mul_assoc] using h
  have hz := eq_zero_of_geometric_polynomial_moments q hq0 hqle x ‖x‖ hb hm
  apply lp.ext
  funext k
  exact hz k

/-- Geometric weighting leaves the polynomial family total in the full ℓ² space. -/
theorem geometricMonomial_span_dense {q : ℝ} (hq0 : 0 < q) (hqle : q ≤ 1/2) :
    (Submodule.span ℝ (Set.range (geometricMonomial q hq0 hqle))).topologicalClosure = ⊤ := by
  let K := Submodule.span ℝ (Set.range (geometricMonomial q hq0 hqle))
  have ho : Kᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hz : x = 0 := by
      apply eq_zero_of_orthogonal_geometricMonomial hq0 hqle x
      intro m
      have h := hx _ (Submodule.subset_span ⟨m, rfl⟩)
      simpa only [real_inner_comm] using h
    simpa only [Submodule.mem_bot] using hz
  change K.topologicalClosure = ⊤
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ho,
    Submodule.bot_orthogonal_eq_top]

/-- A nonzero common normalization does not change the weighted polynomial span. -/
theorem geometricMonomial_scaled_span {q : ℝ} (hq0 : 0 < q) (hqle : q ≤ 1/2)
    {c : ℝ} (hc : c ≠ 0) :
    Submodule.span ℝ (Set.range (fun m => c • geometricMonomial q hq0 hqle m)) =
      Submodule.span ℝ (Set.range (geometricMonomial q hq0 hqle)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨m, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨m, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro y ⟨m, rfl⟩
    let K : Submodule ℝ (lp (fun _ : ℕ => ℝ) 2) :=
      Submodule.span ℝ (Set.range (fun j => c • geometricMonomial q hq0 hqle j))
    change geometricMonomial q hq0 hqle m ∈ K
    have hmem : c • geometricMonomial q hq0 hqle m ∈ K :=
      Submodule.subset_span ⟨m, rfl⟩
    have h : c⁻¹ • (c • geometricMonomial q hq0 hqle m) ∈ K :=
      K.smul_mem c⁻¹ hmem
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
    exact h

/-- The coefficients C q^k give the same complete coordinate family when C is nonzero. -/
theorem geometricMonomial_scaled_span_dense {q : ℝ} (hq0 : 0 < q) (hqle : q ≤ 1/2)
    {c : ℝ} (hc : c ≠ 0) :
    (Submodule.span ℝ (Set.range (fun m => c • geometricMonomial q hq0 hqle m))).topologicalClosure = ⊤ := by
  rw [geometricMonomial_scaled_span hq0 hqle hc]
  exact geometricMonomial_span_dense hq0 hqle

end RiemannResearch.Analysis
