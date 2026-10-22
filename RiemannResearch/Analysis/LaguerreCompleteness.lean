import RiemannResearch.Analysis.ExponentialMomentDeterminacy
import RiemannResearch.Analysis.LaguerreMomentTransform
import RiemannResearch.Analysis.LaguerreHilbert
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Completeness criterion for ordinary Laguerre polynomials

Source: the classical exponential-moment proof of Laguerre completeness.
The finite triangular transform identifies Laguerre and polynomial annihilators;
analytic moment determinacy then proves the annihilator is zero.
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.Analysis

/-- Vanishing of all actual Laguerre integrals forces a square-integrable
function to vanish. The measure hypotheses are supplied by the exponential
weight in the Parseval application. -/
theorem ae_eq_zero_of_laguerre_integrals
    {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : MemLp f 2 μ)
    (hp : ∀ n : ℕ, MemLp (fun x : ℝ ↦ x ^ n) 2 μ)
    (he : ∀ s ∈ Ioo (-1 / 4 : ℝ) (1 / 4),
      MemLp (fun x : ℝ ↦ Real.exp (s * x)) 2 μ)
    (hL : ∀ n : ℕ, (∫ x, f x * laguerreValue n x ∂μ) = 0) :
    f =ᵐ[μ] 0 := by
  apply ae_eq_zero_of_polynomial_moments hf hp he
  have htransform :
      laguerreMomentTransform (fun n ↦ ∫ x, f x * x ^ n ∂μ) =
        laguerreMomentTransform (fun _ ↦ 0) := by
    funext n
    rw [← integral_mul_laguerreValue μ f n
      (fun j _ ↦ hf.integrable_mul (hp j)), hL n]
    simp [laguerreMomentTransform]
  intro n
  exact congrFun (laguerreMomentTransform_injective htransform) n

/-- The concrete ordinary Laguerre family has no nonzero L2 annihilator. -/
theorem laguerreVector_span_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range laguerreVector))ᗮ = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  change f = 0
  apply Lp.ext
  apply Filter.EventuallyEq.trans _ (Lp.coeFn_zero ℝ 2 laguerreMeasure).symm
  apply ae_eq_zero_of_laguerre_integrals (Lp.memLp f)
    memLp_pow_laguerreMeasure
    (fun s hs ↦ memLp_exp_mul_laguerreMeasure (by linarith [hs.2]))
  intro n
  rw [← inner_laguerreVector]
  exact Submodule.inner_left_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self n)) hf

/-- The actual ordinary Laguerre polynomials form a Hilbert basis. -/
def laguerreBasis : HilbertBasis ℕ ℝ LaguerreL2 :=
  HilbertBasis.mkOfOrthogonalEqBot laguerreVector_orthonormal
    laguerreVector_span_orthogonal_eq_bot

@[simp] theorem laguerreBasis_apply (n : ℕ) :
    laguerreBasis n = laguerreVector n := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    laguerreVector_orthonormal laguerreVector_span_orthogonal_eq_bot) n

/-- Parseval's identity with a convergent sum for the actual Laguerre vectors. -/
theorem hasSum_laguerre_inner_sq (f : LaguerreL2) :
    HasSum (fun n ↦ (inner ℝ f (laguerreVector n)) ^ 2) (‖f‖ ^ 2) := by
  simpa only [laguerreBasis_apply, real_inner_comm, ← pow_two,
    real_inner_self_eq_norm_sq] using laguerreBasis.hasSum_inner_mul_inner f f

end RiemannResearch.Analysis
