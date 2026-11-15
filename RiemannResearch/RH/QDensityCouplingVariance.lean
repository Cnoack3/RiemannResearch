import RiemannResearch.Analysis.CompressionVariance
import RiemannResearch.RH.QDensityCouplingSurjectivity
import RiemannResearch.RH.QDensityClosureTransfer
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith

/-!
# The density-coupling Gram operator as an exact variance

Source: Christian Noack's variance observation, 15 November 2026.
The abstract projection identities are in Analysis.CompressionVariance.
B is QDensityMetric.B = (I + D) / zeta(2), with physical Df(n)=f(n)/n.
V is the actual full-conductor legal closure and W = V-perp-Q.

The second-moment identity and total-variance decomposition are unconditional.
Zero variance is equivalent to V being the whole Q Hilbert space.
The implication to RH is a conditional research reduction: actual vanishing
of the variance remains Open.

The reverse Gram operator C C* has a strictly positive quadratic form on
each nonzero vector of W. A uniform positive lower bound is equivalent to
finite-dimensionality of W; neither condition is asserted here.
-/

noncomputable section
namespace RiemannResearch.RH.QDensityCouplingVariance
open ZetaTwoHilbert ZetaTwoProbability QDensityMetric QReciprocalMetric
open QDensityCouplingSurjectivity QDensityClosureTransfer

/-- The exact C* C identity with the existing, actual density coupling. -/
theorem coupling_gram_eq_second_moment :
    coupling.adjoint.comp coupling =
      V.operatorCompression (B.comp B) -
        (V.operatorCompression B).comp (V.operatorCompression B) :=
  V.compressionVariance_eq_square_defect B B_symmetric

/-- Exact law of total centered variance, valid for every scalar center. -/
theorem coupling_total_variance (v : V) (μ : ℝ) :
    ‖B (v : QHilbert) - μ • (v : QHilbert)‖ ^ 2 =
      inner ℝ ((coupling.adjoint.comp coupling) v) v +
        ‖V.operatorCompression B v - μ • v‖ ^ 2 :=
  V.compressionVariance_total B v μ

/-- Zero operator variance is equivalent to full unaugmented density. -/
theorem coupling_gram_zero_iff_fullClosure :
    coupling.adjoint.comp coupling = 0 ↔ V = ⊤ := by
  change V.compressionVariance B = 0 ↔ V = ⊤
  rw [V.compressionVariance_zero_iff_invariant]
  exact fullClosure_eq_top_iff_density_invariant.symm

/-- Conditional research reduction. Open: the actual density-coupling Gram operator vanishes. -/
theorem riemannHypothesis_of_coupling_gram_zero
    (h : coupling.adjoint.comp coupling = 0) : RiemannHypothesis := by
  apply riemannHypothesis_of_density_invariant
  exact (V.compressionVariance_zero_iff_invariant B).mp h

/-- The scalar identity part of B has zero variance; the normalization is retained. -/
theorem coupling_reciprocal_variance (v : V) :
    inner ℝ ((coupling.adjoint.comp coupling) v) v =
      (1 / zetaTwo) ^ 2 * inner ℝ (V.compressionVariance D v) v := by
  change inner ℝ (V.compressionVariance B v) v = _
  have hB : B = (1 / zetaTwo) • D +
      (1 / zetaTwo) • ContinuousLinearMap.id ℝ QHilbert := by
    unfold B
    rw [smul_add, add_comm]
  rw [hB, V.compressionVariance_affine_quadratic]

/-- Reverse variance retains the complete adjoint energy. -/
theorem reverse_gram_quadratic (w : W) :
    inner ℝ ((coupling.comp coupling.adjoint) w) w = ‖coupling.adjoint w‖ ^ 2 := by
  change inner ℝ (coupling (coupling.adjoint w)) w = _
  rw [← ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

/-- Pointwise strict positivity follows from the established injectivity of C*. -/
theorem reverse_gram_strictly_positive (w : W) (hw : w ≠ 0) :
    0 < inner ℝ ((coupling.comp coupling.adjoint) w) w := by
  rw [reverse_gram_quadratic]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  apply hw
  apply coupling_adjoint_injective
  simpa using h

/-- Conditional gap criterion. A uniform positive constant and finite dimension remain Open. -/
theorem reverse_gram_gap_iff_finiteDimensional :
    (∃ δ > 0, ∀ w : W,
      δ ^ 2 * ‖w‖ ^ 2 ≤ inner ℝ ((coupling.comp coupling.adjoint) w) w) ↔
      FiniteDimensional ℝ W := by
  rw [finiteDimensional_iff_adjoint_lower_bound]
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, ?_⟩
    intro w
    have hh := h w
    rw [reverse_gram_quadratic] at hh
    have hp := mul_nonneg hδ.le (norm_nonneg w)
    nlinarith [norm_nonneg (coupling.adjoint w)]
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, ?_⟩
    intro w
    rw [reverse_gram_quadratic]
    have hh := h w
    have hp := mul_nonneg hδ.le (norm_nonneg w)
    nlinarith [norm_nonneg (coupling.adjoint w)]

#print axioms coupling_gram_eq_second_moment
#print axioms coupling_total_variance
#print axioms coupling_gram_zero_iff_fullClosure
#print axioms riemannHypothesis_of_coupling_gram_zero
#print axioms reverse_gram_gap_iff_finiteDimensional

end RiemannResearch.RH.QDensityCouplingVariance
