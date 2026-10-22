import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact finite Gram minimization from linear independence

Source: user-provided argument, `RH_Minimal_Seeds_Continuation_20260916.md`,
Section 13, equation (13.7). The citation supports the signed Gram minimum
and its intended application to simultaneous legal tail corrections.

The Gram matrix here is formed from the actual Hilbert inner product.
Its invertibility is proved from linear independence; no inverse or
positive-definiteness hypothesis is assumed. All mixed terms are kept.
Completeness of the ambient inner-product space is unnecessary.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertGram
noncomputable section

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Actual Gram matrix as an endomorphism of finite coefficient arrays. -/
def gram (v : ι → H) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun c i := inner (𝕜 := ℝ) (v i) (Fintype.linearCombination ℝ v c)
  map_add' c d := by
    funext i
    change inner (𝕜 := ℝ) (v i) (Fintype.linearCombination ℝ v (c + d)) =
      inner (𝕜 := ℝ) (v i) (Fintype.linearCombination ℝ v c) +
      inner (𝕜 := ℝ) (v i) (Fintype.linearCombination ℝ v d)
    rw [map_add, inner_add_right]
  map_smul' r c := by
    funext i
    change inner (𝕜 := ℝ) (v i) (Fintype.linearCombination ℝ v (r • c)) =
      r * inner (𝕜 := ℝ) (v i) (Fintype.linearCombination ℝ v c)
    rw [map_smul, inner_smul_right]

/-- Entries are the complete signed pairwise inner products. -/
theorem gram_apply (v : ι → H) (c : ι → ℝ) (i : ι) :
    gram v c i = ∑ j, inner (𝕜 := ℝ) (v i) (v j) * c j := by
  change inner (𝕜 := ℝ) (v i) (Fintype.linearCombination ℝ v c) = _
  rw [Fintype.linearCombination_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_smul_right]
  ring

theorem inner_synthesis_left (v : ι → H) (c : ι → ℝ) (f : H) :
    inner (𝕜 := ℝ) (Fintype.linearCombination ℝ v c) f =
      ∑ i, c i * inner (𝕜 := ℝ) (v i) f := by
  simp only [Fintype.linearCombination_apply, sum_inner, real_inner_smul_left]

theorem gram_quadratic (v : ι → H) (c : ι → ℝ) :
    ‖Fintype.linearCombination ℝ v c‖ ^ 2 = ∑ i, c i * gram v c i := by
  rw [← real_inner_self_eq_norm_sq, inner_synthesis_left]
  <;> rfl

/-- A zero Gram direction has zero synthesis norm, and independence then
forces its coefficients to vanish. -/
theorem gram_injective {v : ι → H} (hv : LinearIndependent ℝ v) :
    Function.Injective (gram v) := by
  intro c d hcd
  have hz : gram v (c - d) = 0 := by rw [map_sub, hcd, sub_self]
  have hn : ‖Fintype.linearCombination ℝ v (c - d)‖ ^ 2 = 0 := by
    rw [gram_quadratic]
    simp only [hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have hs : Fintype.linearCombination ℝ v (c - d) = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (Fintype.linearCombination ℝ v (c - d))]
  have hc : c - d = 0 := by
    apply hv.fintypeLinearCombination_injective
    simpa only [map_zero] using hs
  exact sub_eq_zero.mp hc

/-- The actual Gram inverse exists because the coefficient space is finite. -/
def gramEquiv {v : ι → H} (hv : LinearIndependent ℝ v) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.ofInjectiveEndo (gram v) (gram_injective hv)

def cross (v : ι → H) (f : H) (i : ι) : ℝ := inner (𝕜 := ℝ) (v i) f

/-- Coefficient vector to subtract; the additive optimizer is its negative. -/
def inverseCoeff {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) : ι → ℝ :=
  (gramEquiv hv).symm (cross v f)

theorem inverseCoeff_normal {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (i : ι) :
    inner (𝕜 := ℝ) (v i) (Fintype.linearCombination ℝ v (inverseCoeff hv f)) =
      cross v f i := by
  exact congrFun ((gramEquiv hv).apply_symm_apply (cross v f)) i

theorem residual_orthogonal {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) :
    inner (𝕜 := ℝ) (f - Fintype.linearCombination ℝ v (inverseCoeff hv f))
      (Fintype.linearCombination ℝ v c) = 0 := by
  rw [real_inner_comm, inner_synthesis_left]
  apply Finset.sum_eq_zero
  intro i _
  rw [inner_sub_right, inverseCoeff_normal]
  simp only [cross, sub_self, mul_zero]

/-- The exact inverse-Gram value, with the original inner products. -/
theorem residual_schur_value {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) :
    ‖f - Fintype.linearCombination ℝ v (inverseCoeff hv f)‖ ^ 2 =
      ‖f‖ ^ 2 - ∑ i, inverseCoeff hv f i * cross v f i := by
  have hss : ‖Fintype.linearCombination ℝ v (inverseCoeff hv f)‖ ^ 2 =
      ∑ i, inverseCoeff hv f i * cross v f i := by
    rw [gram_quadratic]
    apply Finset.sum_congr rfl
    intro i _
    change inverseCoeff hv f i *
      inner (𝕜 := ℝ) (v i) (Fintype.linearCombination ℝ v (inverseCoeff hv f)) = _
    rw [inverseCoeff_normal]
  have hfs : inner (𝕜 := ℝ) f (Fintype.linearCombination ℝ v (inverseCoeff hv f)) =
      ∑ i, inverseCoeff hv f i * cross v f i := by
    rw [real_inner_comm, inner_synthesis_left]
    <;> rfl
  rw [norm_sub_sq_real, hss, hfs]
  ring

/-- Exact completion of the norm square for arbitrary simultaneous signed
coefficients. -/
theorem residual_completion {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) :
    ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ v (inverseCoeff hv f)‖ ^ 2 +
      ‖Fintype.linearCombination ℝ v (c - inverseCoeff hv f)‖ ^ 2 := by
  have he : f - Fintype.linearCombination ℝ v c =
      (f - Fintype.linearCombination ℝ v (inverseCoeff hv f)) -
      Fintype.linearCombination ℝ v (c - inverseCoeff hv f) := by
    rw [map_sub]
    abel
  rw [he, norm_sub_sq_real, residual_orthogonal]
  ring

theorem residual_minimizes {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) :
    ‖f - Fintype.linearCombination ℝ v (inverseCoeff hv f)‖ ^ 2 ≤
      ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 := by
  rw [residual_completion hv f c]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem residual_minimizer_unique {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ)
    (hc : ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖f‖ ^ 2 - ∑ i, inverseCoeff hv f i * cross v f i) :
    c = inverseCoeff hv f := by
  have he := residual_completion hv f c
  rw [residual_schur_value] at he
  have hn : ‖Fintype.linearCombination ℝ v (c - inverseCoeff hv f)‖ ^ 2 = 0 := by
    linarith
  have hs : Fintype.linearCombination ℝ v (c - inverseCoeff hv f) = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (Fintype.linearCombination ℝ v (c - inverseCoeff hv f))]
  have hz : c - inverseCoeff hv f = 0 := by
    apply hv.fintypeLinearCombination_injective
    simpa only [map_zero] using hs
  exact sub_eq_zero.mp hz

/-- Equation (13.7) in its additive-correction convention. -/
theorem additive_inverse_schur_value {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) :
    ‖f + Fintype.linearCombination ℝ v (-inverseCoeff hv f)‖ ^ 2 =
      ‖f‖ ^ 2 - ∑ i, inverseCoeff hv f i * cross v f i := by
  simpa only [map_neg, ← sub_eq_add_neg] using residual_schur_value hv f

theorem additive_minimizes {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) :
    ‖f + Fintype.linearCombination ℝ v (-inverseCoeff hv f)‖ ^ 2 ≤
      ‖f + Fintype.linearCombination ℝ v c‖ ^ 2 := by
  simpa only [map_neg, sub_neg_eq_add, ← sub_eq_add_neg] using
    residual_minimizes hv f (-c)

/-! The following bilinear identities formalize the exact screening/source
formulas in Sections 23 and 25 of the user-provided
RH_Global_Approximation_and_Resonance_Blind_Patterns_Handoff_2026-09-16(1).md.
The inverse is the already constructed actual Gram inverse. -/

theorem residual_bilinear_schur {v : ι → H} (hv : LinearIndependent ℝ v) (f g : H) :
    inner ℝ (f - Fintype.linearCombination ℝ v (inverseCoeff hv f))
      (g - Fintype.linearCombination ℝ v (inverseCoeff hv g)) =
    inner ℝ f g - ∑ i, inverseCoeff hv f i * cross v g i := by
  rw [inner_sub_right, residual_orthogonal, sub_zero, inner_sub_left,
    inner_synthesis_left]
  rfl

theorem residual_cross_source {v : ι → H} (hv : LinearIndependent ℝ v)
    (f z : H) :
    inner ℝ (f - Fintype.linearCombination ℝ v (inverseCoeff hv f)) z =
      inner ℝ f z - ∑ i, inverseCoeff hv f i * cross v z i := by
  rw [inner_sub_left, inner_synthesis_left]
  rfl

end
end RiemannResearch.Analysis.FiniteHilbertGram
