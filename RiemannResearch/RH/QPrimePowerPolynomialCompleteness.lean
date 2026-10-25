/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GeometricPolynomialDensity
import RiemannResearch.RH.QPrimePowerPolynomialOrthonormal
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QPrimePowerWaveletCompleteness
import RiemannResearch.RH.QPrimePowerMonomialLift
import RiemannResearch.RH.QPrimePowerWaveletCoefficients
import RiemannResearch.RH.PrimeValuationHilbertBasis
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial completeness in the physical prime-valuation Hilbert space

Source: the user's generating-function density argument, 25 October 2026.
Geometric moment uniqueness is transferred through the already complete
prime-power wavelet basis of the physically defined valuationSpace. The
existing Gram--Schmidt span identity then proves polynomial completeness.
The constant is included explicitly. All spaces carry the actual Q norm.

This is not a legal squarefree-closure theorem. In particular the first
centered valuation mode is already known not to belong to that enlarged
legal closure, and the floor-logarithm cofactor residual remains present.

-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert PrimeValuationBasis QDivisorHilbert

/-- Orthogonality to the constant and every monomial lift forces a physical
valuation observable to vanish. -/
theorem eq_zero_of_orthogonal_primePowerMonomialLift
    (p : ℕ) (hp : p.Prime) (f : valuationSpace p)
    (hconstant : inner ℝ f.val qOne = 0)
    (hmonomial : ∀ m, inner ℝ f.val (primePowerMonomialLift p hp m) = 0) :
    f = 0 := by
  let q : ℝ := (p : ℝ)⁻¹
  let x : ℕ → ℝ := fun k => inner ℝ f.val (primePowerFrame p hp (k+1))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hqle : q ≤ (1 / 2 : ℝ) := by
    dsimp [q]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hp0).mpr
    nlinarith
  have hbound : ∀ k, ‖x k‖ ≤ ‖f.val‖ := by
    intro k
    have h : ‖inner ℝ f.val (primePowerFrame p hp (k+1))‖ ≤
        ‖f.val‖ * ‖primePowerFrame p hp (k+1)‖ := norm_inner_le_norm _ _
    simpa only [(primePowerFrame_orthonormal p hp).1,
      mul_one] using h
  have hsqrt : (Real.sqrt ((p : ℝ)^2-1))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    nlinarith
  have hm (m : ℕ) : ∑' k : ℕ, (k : ℝ)^m * q^k * x k = 0 := by
    have h := hmonomial m
    rw [inner_primePowerMonomialLift] at h
    have hterm (k : ℕ) :
        ((k : ℝ)^m * inner ℝ (qTarget p hp.one_lt)
          (primePowerFrame p hp (k+1))) *
            inner ℝ f.val (primePowerFrame p hp (k+1)) =
        (Real.sqrt ((p : ℝ)^2-1))⁻¹ * ((k : ℝ)^m * q^k * x k) := by
      rw [qTarget_inner_primePowerFrame_succ]
      dsimp [x, q]
      simp only [one_div, mul_inv_rev, inv_pow]
      ring
    simp_rw [hterm] at h
    rw [tsum_mul_left] at h
    exact (mul_eq_zero.mp h).resolve_left hsqrt
  have hx : ∀ k, x k = 0 :=
    RiemannResearch.Analysis.eq_zero_of_geometric_polynomial_moments
      q hq0 hqle x ‖f.val‖ hbound hm
  apply eq_zero_of_orthogonal_valuationWavelet p hp f
  intro k
  cases k with
  | zero =>
    change inner ℝ f.val (primePowerFrame p hp 0) = 0
    simpa only [primePowerFrame_zero] using hconstant
  | succ k =>
    change inner ℝ f.val (primePowerFrame p hp (k+1)) = 0
    exact hx k

/-- Every element of the polynomial frame lies in the physical valuation space. -/
theorem valuationPolynomialFrame_mem (p : ℕ) (hp : p.Prime) (k : ℕ) :
    valuationPolynomialFrame p hp k ∈ valuationSpace p := by
  cases k with
  | zero => exact qOne_mem_valuationSpace p hp
  | succ k => exact valuationPolynomialMode_mem p hp k

/-- The constant and all polynomial modes, regarded inside the physical subspace. -/
def valuationPolynomialBasisVector (p : ℕ) (hp : p.Prime) (k : ℕ) :
    valuationSpace p :=
  ⟨valuationPolynomialFrame p hp k, valuationPolynomialFrame_mem p hp k⟩

/-- Restricting to the physical subspace preserves the actual-Q Gram identity. -/
theorem valuationPolynomialBasisVector_orthonormal (p : ℕ) (hp : p.Prime) :
    Orthonormal ℝ (valuationPolynomialBasisVector p hp) := by
  rw [orthonormal_iff_ite]
  intro j k
  exact orthonormal_iff_ite.mp (valuationPolynomialFrame_orthonormal p hp) j k

/-- The complete polynomial frame has trivial orthogonal complement in V_p. -/
theorem eq_zero_of_orthogonal_valuationPolynomial
    (p : ℕ) (hp : p.Prime) (f : valuationSpace p)
    (hf : ∀ k, inner ℝ f (valuationPolynomialBasisVector p hp k) = 0) :
    f = 0 := by
  apply eq_zero_of_orthogonal_primePowerMonomialLift p hp f
  · exact hf 0
  · intro m
    let L := innerSL ℝ f.val
    have hs : Submodule.span ℝ (Set.range (valuationPolynomialMode p hp)) ≤ L.ker := by
      apply Submodule.span_le.mpr
      rintro y ⟨j, rfl⟩
      exact hf (j+1)
    have hm : primePowerMonomialLift p hp m ∈
        Submodule.span ℝ (Set.range (valuationPolynomialMode p hp)) := by
      rw [valuationPolynomialMode_span]
      exact Submodule.subset_span ⟨m, rfl⟩
    exact hs hm

/-- The constant and polynomial modes have dense span in all of physical V_p. -/
theorem valuationPolynomial_span_dense (p : ℕ) (hp : p.Prime) :
    (Submodule.span ℝ (Set.range (valuationPolynomialBasisVector p hp))).topologicalClosure =
      ⊤ := by
  let K := Submodule.span ℝ (Set.range (valuationPolynomialBasisVector p hp))
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm
    · intro f hf
      have hz : f = 0 := by
        apply eq_zero_of_orthogonal_valuationPolynomial p hp f
        intro k
        have he := hf _ (Submodule.subset_span ⟨k, rfl⟩)
        simpa only [real_inner_comm] using he
      simpa only [Submodule.mem_bot] using hz
    · exact bot_le
  change K.topologicalClosure = ⊤
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth,
    Submodule.bot_orthogonal_eq_top]

/-- A complete polynomial Hilbert basis of the physically defined valuation space. -/
def valuationPolynomialHilbertBasis (p : ℕ) (hp : p.Prime) :
    HilbertBasis ℕ ℝ (valuationSpace p) :=
  HilbertBasis.mk (valuationPolynomialBasisVector_orthonormal p hp)
    (by rw [valuationPolynomial_span_dense])

@[simp] theorem valuationPolynomialHilbertBasis_apply (p : ℕ) (hp : p.Prime) (k : ℕ) :
    valuationPolynomialHilbertBasis p hp k = valuationPolynomialBasisVector p hp k := by
  simp only [valuationPolynomialHilbertBasis, HilbertBasis.coe_mk]

/-- Every valuation observable has its unconditional polynomial expansion in actual Q norm. -/
theorem valuationPolynomial_hasSum (p : ℕ) (hp : p.Prime) (f : valuationSpace p) :
    HasSum (fun k => inner ℝ (valuationPolynomialFrame p hp k) f.val •
      valuationPolynomialFrame p hp k) f.val := by
  have h := ((valuationPolynomialHilbertBasis p hp).hasSum_repr f).mapL
    (valuationSpace p).subtypeL
  simp only [HilbertBasis.repr_apply_apply, valuationPolynomialHilbertBasis_apply,
    map_smul] at h
  change HasSum (fun k => inner ℝ (valuationPolynomialFrame p hp k) f.val •
    valuationPolynomialFrame p hp k) f.val at h
  exact h

/-- Complete polynomial Parseval, retaining all signed coefficient differences. -/
theorem valuationPolynomial_signed_parseval (p : ℕ) (hp : p.Prime)
    (f g : valuationSpace p) :
    (∑' k, (inner ℝ f.val (valuationPolynomialFrame p hp k) -
      inner ℝ g.val (valuationPolynomialFrame p hp k))^2) = ‖f - g‖^2 := by
  have h := (valuationPolynomialHilbertBasis p hp).tsum_inner_mul_inner (f-g) (f-g)
  have he (k : ℕ) :
      inner ℝ (f-g) (valuationPolynomialBasisVector p hp k) *
        inner ℝ (valuationPolynomialBasisVector p hp k) (f-g) =
      (inner ℝ f.val (valuationPolynomialFrame p hp k) -
        inner ℝ g.val (valuationPolynomialFrame p hp k))^2 := by
    rw [real_inner_comm (f-g) (valuationPolynomialBasisVector p hp k),
      inner_sub_left, pow_two]
    rfl
  simpa only [valuationPolynomialHilbertBasis_apply, he,
    real_inner_self_eq_norm_sq] using h

/-- The complete polynomial energy of any physical valuation observable. -/
theorem valuationPolynomial_parseval (p : ℕ) (hp : p.Prime) (f : valuationSpace p) :
    (∑' k, (inner ℝ f.val (valuationPolynomialFrame p hp k))^2) = ‖f‖^2 := by
  simpa using valuationPolynomial_signed_parseval p hp f 0

end RiemannResearch.RH.PrimePowerTarget
