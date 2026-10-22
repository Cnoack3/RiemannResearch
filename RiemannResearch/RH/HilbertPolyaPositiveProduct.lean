import RiemannResearch.Analysis.PositiveSpectralProduct
import RiemannResearch.RH.RiemannHypothesisStrip
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.XiLogDeriv
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# A positive spectral-product identity sufficient for actual RH

Source: user-provided Hilbert--Polya determinant proposal, 2026-09-20.
The representation target is restricted to the open critical strip, where
the actual completed zeta function has no pole conventions to repair. The
separate checked strip equivalence connects the conclusion to Mathlib's
`RiemannHypothesis`.

OPEN: the arithmetic spectral-product identity. No provider is asserted.
The theorem below is a conditional research reduction. It does not construct
a positive operator, prove an operator determinant identity, or establish RH
without this explicit representation hypothesis.
-/

noncomputable section
namespace RiemannResearch.RH.HilbertPolya
open RiemannResearch.Analysis.PositiveSpectralProduct

/-- If s = 1/2 + i z, this is precisely z, including nonreal z. -/
def spectralCoordinate (s : ℂ) : ℂ :=
  -Complex.I * (s - ((1 / 2 : ℝ) : ℂ))

theorem spectralCoordinate_im (s : ℂ) :
    (spectralCoordinate s).im = 1 / 2 - s.re := by
  simp [spectralCoordinate, Complex.mul_im]

/-- Explicit open arithmetic representation target. Evaluating at s=1/2
fixes the nonzero normalization c; no statement about Xi at 0 or 1 is used. -/
def StripPositiveSpectralRepresentation : Prop :=
  ∃ (τ : ℕ → ℝ) (c : ℂ),
    (∀ j, 0 ≤ τ j) ∧ Summable τ ∧ c ≠ 0 ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        s * (s - 1) * completedRiemannZeta s = c * product τ (spectralCoordinate s)

/-- The missing product identity would imply actual Mathlib RH. Summability
prevents a product from vanishing without a vanishing factor; positivity
then forces the associated spectral coordinate to be real. -/
theorem riemannHypothesis_of_strip_positive_spectral_representation
    (h : StripPositiveSpectralRepresentation) : RiemannHypothesis := by
  obtain ⟨τ, c, hτ, hs, hc, hrepresentation⟩ := h
  apply riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro s hz h0 h1
  have hcompleted : completedRiemannZeta s = 0 :=
    (Zeta23.WeilEF.completedZeta_zeros_strip h0 h1).1.mpr ⟨hz, h0, h1⟩
  have he := hrepresentation s h0 h1
  rw [hcompleted, mul_zero] at he
  have hp : product τ (spectralCoordinate s) = 0 :=
    (mul_eq_zero.mp he.symm).resolve_left hc
  have him := product_zero_im_eq_zero τ hτ hs (spectralCoordinate s) hp
  rw [spectralCoordinate_im] at him
  linarith


open Filter
open scoped Topology

/-- Open arithmetic identification through finite spectral products.
The same fixed summable spectrum is used at every truncation. -/
def StripPositiveSpectralLimit : Prop :=
  ∃ (τ : ℕ → ℝ) (c : ℂ),
    (∀ j, 0 ≤ τ j) ∧ Summable τ ∧ c ≠ 0 ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        Tendsto (fun N => c * partialProduct τ N (spectralCoordinate s))
          atTop (𝓝 (s * (s - 1) * completedRiemannZeta s))

/-- The finite-product limit target is exactly the existing representation
target, with no additional arithmetic provider asserted. -/
theorem stripPositiveSpectralLimit_iff_representation :
    StripPositiveSpectralLimit ↔ StripPositiveSpectralRepresentation := by
  constructor
  · rintro ⟨τ, c, hτ, hs, hc, hlimit⟩
    refine ⟨τ, c, hτ, hs, hc, ?_⟩
    intro s h0 h1
    exact tendsto_nhds_unique (hlimit s h0 h1)
      (tendsto_const_nhds.mul (tendsto_partialProduct τ hτ hs (spectralCoordinate s)))
  · rintro ⟨τ, c, hτ, hs, hc, hrepresentation⟩
    refine ⟨τ, c, hτ, hs, hc, ?_⟩
    intro s h0 h1
    rw [hrepresentation s h0 h1]
    exact tendsto_const_nhds.mul (tendsto_partialProduct τ hτ hs (spectralCoordinate s))

/-- Conditional research reduction: the finite-product identification remains
an explicit open hypothesis. This theorem does not construct the spectrum. -/
theorem riemannHypothesis_of_strip_positive_spectral_limit
    (h : StripPositiveSpectralLimit) : RiemannHypothesis := by
  exact riemannHypothesis_of_strip_positive_spectral_representation
    (stripPositiveSpectralLimit_iff_representation.mp h)

/-- Locally uniform identification suffices, already by its pointwise
consequence for this fixed summable spectrum. No general Hurwitz theorem
or trace-class operator representation is assumed implicitly. -/
theorem riemannHypothesis_of_strip_locallyUniform_positive_spectral_limit
    (τ : ℕ → ℝ) (c : ℂ) (hτ : ∀ j, 0 ≤ τ j)
    (hs : Summable τ) (hc : c ≠ 0)
    (hlimit : TendstoLocallyUniformlyOn
      (fun N s => c * partialProduct τ N (spectralCoordinate s))
      (fun s => s * (s - 1) * completedRiemannZeta s)
      atTop {s : ℂ | 0 < s.re ∧ s.re < 1}) : RiemannHypothesis := by
  apply riemannHypothesis_of_strip_positive_spectral_limit
  refine ⟨τ, c, hτ, hs, hc, ?_⟩
  intro s h0 h1
  exact hlimit.tendsto_at ⟨h0, h1⟩

end RiemannResearch.RH.HilbertPolya
