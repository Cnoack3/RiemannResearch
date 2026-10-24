/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.PrimeValuationHilbertBasis
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum
/-!
# Complete prime-power wavelets on the physical valuation space

Provenance: the user's prime-power basis research program, continued in
`FpOrthonormalBasisResearch20261020.md`. This proves totality of the existing
prime-power frame by transferring annihilation to divisibility tails and then
to the complete exact-level indicator basis. All spaces use the actual Zipf-2
Q inner product. This is neither Meixner polynomial completeness nor a provider
of floor-logarithm membership in the legal squarefree closure.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimeValuationBasis
open ZetaTwoHilbert QDivisibilityDensity QDivisorHilbert

/-- Prime-power divisibility depends only on the prime valuation. -/
theorem primePowerDivisor_mem_valuationSpace (p k : ℕ) (hp : p.Prime) :
    qDivisor (p ^ k) ∈ valuationSpace p := by
  intro n hn
  rw [qSequence_qDivisor]
  simp only [positiveDivisor, hn, pow_ne_zero _ hp.ne_zero, if_false,
    hp.pow_dvd_iff_le_factorization hn,
    hp.pow_dvd_iff_le_factorization (pow_ne_zero _ hp.ne_zero)]
  simp [Nat.factorization_pow, hp.factorization]

/-- Every existing prime-power wavelet is physically valuation-only. -/
theorem primePowerFrame_mem_valuationSpace (p : ℕ) (hp : p.Prime) (k : ℕ) :
    primePowerFrame p hp k ∈ valuationSpace p := by
  cases k with
  | zero => simpa using qOne_mem_valuationSpace p hp
  | succ k =>
    unfold primePowerFrame normalizedDivisorWavelet
    apply Submodule.smul_mem
    change divisorWavelet (p ^ (k+1)) ∈ valuationSpace p
    rw [divisorWavelet_prime_pow_succ p k hp]
    exact (valuationSpace p).sub_mem
      ((valuationSpace p).smul_mem _ (primePowerDivisor_mem_valuationSpace p (k+1) hp))
      ((valuationSpace p).smul_mem _ (primePowerDivisor_mem_valuationSpace p k hp))

/-- The prime-power frame restricted to the physical valuation subspace. -/
def valuationWavelet (p : ℕ) (hp : p.Prime) (k : ℕ) : valuationSpace p :=
  ⟨primePowerFrame p hp k, primePowerFrame_mem_valuationSpace p hp k⟩

/-- Restriction preserves actual Q orthonormality. -/
theorem valuationWavelet_orthonormal (p : ℕ) (hp : p.Prime) :
    Orthonormal ℝ (valuationWavelet p hp) := by
  rw [orthonormal_iff_ite]
  intro j k
  exact orthonormal_iff_ite.mp (primePowerFrame_orthonormal p hp) j k

/-- A valuation vector annihilating the whole wavelet frame vanishes. -/
theorem eq_zero_of_orthogonal_valuationWavelet (p : ℕ) (hp : p.Prime)
    (f : valuationSpace p) (hf : ∀ k, inner ℝ f (valuationWavelet p hp k) = 0) :
    f = 0 := by
  have hw (k : ℕ) : inner ℝ f.val (divisorWavelet (p ^ k)) = 0 := by
    have he := divisorWavelet_eq_normalized_smul (⟨p ^ k, pow_pos hp.pos _⟩ : ℕ+)
    change divisorWavelet (p ^ k) = _ at he
    rw [he, real_inner_smul_right]
    change _ * inner ℝ f (valuationWavelet p hp k) = 0
    rw [hf, mul_zero]
  have hd (k : ℕ) : inner ℝ f.val (qDivisor (p ^ k)) = 0 := by
    induction k with
    | zero =>
      have he : qDivisor 1 = qOne := by
        apply qSequence_injective
        funext n
        rw [qSequence_qDivisor, qSequence_qOne]
        simp [positiveDivisor, qOneSequence]
      simpa [valuationWavelet, he] using hf 0
    | succ k ih =>
      have h := hw (k+1)
      rw [divisorWavelet_prime_pow_succ p k hp, inner_sub_right,
        real_inner_smul_right, real_inner_smul_right, ih, mul_zero, sub_zero] at h
      exact (mul_eq_zero.mp h).resolve_left
        (pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)))
  apply eq_zero_of_orthogonal_valuationUnit p hp f
  intro k
  change inner ℝ f.val ((Real.sqrt (valuationMass p k))⁻¹ • valuationLevel p k) = 0
  rw [real_inner_smul_right, valuationLevel, inner_sub_right, hd, hd, sub_self, mul_zero]

/-- The restricted wavelet frame is total in the physical valuation space. -/
theorem valuationWavelet_span_dense (p : ℕ) (hp : p.Prime) :
    (Submodule.span ℝ (Set.range (valuationWavelet p hp))).topologicalClosure = ⊤ := by
  let K := Submodule.span ℝ (Set.range (valuationWavelet p hp))
  have horth : Kᗮ = ⊥ := by
    apply le_antisymm
    · intro f hf
      have hz : f = 0 := by
        apply eq_zero_of_orthogonal_valuationWavelet p hp f
        intro k
        have he := hf _ (Submodule.subset_span ⟨k, rfl⟩)
        simpa only [real_inner_comm] using he
      simpa only [Submodule.mem_bot] using hz
    · exact bot_le
  change K.topologicalClosure = ⊤
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth,
    Submodule.bot_orthogonal_eq_top]

/-- A complete wavelet Hilbert basis of the physical valuation space. -/
def valuationWaveletBasis (p : ℕ) (hp : p.Prime) :
    HilbertBasis ℕ ℝ (valuationSpace p) :=
  HilbertBasis.mk (valuationWavelet_orthonormal p hp)
    (by rw [valuationWavelet_span_dense])

@[simp] theorem valuationWaveletBasis_apply (p : ℕ) (hp : p.Prime) (k : ℕ) :
    valuationWaveletBasis p hp k = valuationWavelet p hp k := by
  simp only [valuationWaveletBasis, HilbertBasis.coe_mk]

/-- Unconditional reconstruction in the ambient Q Hilbert space. -/
theorem valuationWavelet_hasSum (p : ℕ) (hp : p.Prime) (f : valuationSpace p) :
    HasSum (fun k => inner ℝ (primePowerFrame p hp k) f.val •
      primePowerFrame p hp k) f.val := by
  have h := ((valuationWaveletBasis p hp).hasSum_repr f).mapL
    (valuationSpace p).subtypeL
  simp only [HilbertBasis.repr_apply_apply, valuationWaveletBasis_apply, map_smul] at h
  change HasSum (fun k => inner ℝ (primePowerFrame p hp k) f.val •
    primePowerFrame p hp k) f.val at h
  exact h

/-- Complete signed Parseval error, retaining every coefficient discrepancy. -/
theorem valuationWavelet_signed_parseval (p : ℕ) (hp : p.Prime)
    (f g : valuationSpace p) :
    (∑' k, (inner ℝ f.val (primePowerFrame p hp k) -
      inner ℝ g.val (primePowerFrame p hp k))^2) = ‖f - g‖^2 := by
  have h := (valuationWaveletBasis p hp).tsum_inner_mul_inner (f-g) (f-g)
  have he (k : ℕ) :
      inner ℝ (f-g) (valuationWavelet p hp k) *
        inner ℝ (valuationWavelet p hp k) (f-g) =
      (inner ℝ f.val (primePowerFrame p hp k) -
        inner ℝ g.val (primePowerFrame p hp k))^2 := by
    rw [real_inner_comm (f-g) (valuationWavelet p hp k), inner_sub_left, pow_two]
    rfl
  simpa only [valuationWaveletBasis_apply, he, real_inner_self_eq_norm_sq] using h

end RiemannResearch.RH.PrimeValuationBasis
