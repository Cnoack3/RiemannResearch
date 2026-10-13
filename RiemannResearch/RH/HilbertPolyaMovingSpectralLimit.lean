import RiemannResearch.Analysis.PositiveSpectralNonvanishing
import RiemannResearch.RH.HilbertPolyaPositiveProduct
import RiemannResearch.RH.RiemannHypothesisStrip
import RiemannResearch.RH.WeilExplicitFormula.WeilEF.XiLogDeriv
import RiemannResearch.Probability.ContinuousProjectionCompression
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Matrix.PosDef

/-!
# A moving positive spectrum criterion for RH

The spectrum may change with the approximation index. Pointwise convergence
throughout the open critical strip supplies both the putative zero and the fixed
imaginary test point needed by the positive-spectrum nonvanishing inequality.
The zeta-identification/convergence assumption remains substantive and unproved.
-/

noncomputable section
open Filter
open scoped Topology ComplexOrder
namespace RiemannResearch.RH.HilbertPolya
open RiemannResearch.Analysis.PositiveSpectralPolynomial

def StripMovingPositiveSpectralLimit : Prop :=
  ∃ (rank : ℕ → ℕ) (τ : ∀ N, Fin (rank N) → ℝ) (c : ℂ),
    (∀ N i, 0 ≤ τ N i) ∧ c ≠ 0 ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 →
        Tendsto (fun N => c * finiteProduct (τ N) (spectralCoordinate s))
          atTop (𝓝 (s * (s - 1) * completedRiemannZeta s))

theorem riemannHypothesis_of_strip_moving_positive_spectral_limit
    (h : StripMovingPositiveSpectralLimit) : RiemannHypothesis := by
  obtain ⟨rank, τ, c, hτ, hc, hlimit⟩ := h
  apply riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro s hz h0 h1
  by_contra hline
  have hnonreal : (spectralCoordinate s).im ≠ 0 := by
    rw [spectralCoordinate_im]
    intro hzero
    apply hline
    linarith
  have hcompleted : completedRiemannZeta s = 0 :=
    (Zeta23.WeilEF.completedZeta_zeros_strip h0 h1).1.mpr ⟨hz, h0, h1⟩
  have hzero := hlimit s h0 h1
  rw [hcompleted, mul_zero] at hzero
  have hquarter : spectralCoordinate (1 / 4 : ℂ) = Complex.I / 4 := by
    unfold spectralCoordinate
    norm_num <;> ring
  have htest := hlimit (1 / 4 : ℂ) (by norm_num) (by norm_num)
  rw [hquarter] at htest
  have hn := moving_scaled_limit_ne_zero_of_nonreal rank τ hτ c hc
    (spectralCoordinate s) hnonreal 0
    ((1 / 4 : ℂ) * ((1 / 4 : ℂ) - 1) * completedRiemannZeta (1 / 4 : ℂ))
    hzero htest
  exact hn rfl

theorem riemannHypothesis_of_strip_positive_matrix_limit
    (rank : ℕ → ℕ)
    (A : ∀ N, Matrix (Fin (rank N)) (Fin (rank N)) ℂ)
    (hA : ∀ N, (A N).PosSemidef) (c : ℂ) (hc : c ≠ 0)
    (hlimit : ∀ s : ℂ, 0 < s.re → s.re < 1 →
      Tendsto (fun N => c * (1 - (spectralCoordinate s) ^ 2 • A N).det)
        atTop (𝓝 (s * (s - 1) * completedRiemannZeta s))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_strip_moving_positive_spectral_limit
  refine ⟨rank, (fun N => (hA N).isHermitian.eigenvalues), c, ?_, hc, ?_⟩
  · intro N i
    exact (hA N).eigenvalues_nonneg i
  · intro s h0 h1
    have hfactor (N : ℕ) :
        (1 - (spectralCoordinate s) ^ 2 • A N).det =
          finiteProduct (hA N).isHermitian.eigenvalues (spectralCoordinate s) := by
      simpa only [finiteProduct, sub_eq_add_neg, neg_smul, neg_mul] using
        (hA N).isHermitian.det_one_add_smul_eq_prod_complex
          (-((spectralCoordinate s) ^ 2))
    simpa only [hfactor] using hlimit s h0 h1

theorem riemannHypothesis_of_strip_locallyUniform_positive_matrix_limit
    (rank : ℕ → ℕ)
    (A : ∀ N, Matrix (Fin (rank N)) (Fin (rank N)) ℂ)
    (hA : ∀ N, (A N).PosSemidef) (c : ℂ) (hc : c ≠ 0)
    (hlimit : TendstoLocallyUniformlyOn
      (fun N s => c * (1 - (spectralCoordinate s) ^ 2 • A N).det)
      (fun s => s * (s - 1) * completedRiemannZeta s)
      atTop {s : ℂ | 0 < s.re ∧ s.re < 1}) : RiemannHypothesis := by
  apply riemannHypothesis_of_strip_positive_matrix_limit rank A hA c hc
  intro s h0 h1
  exact hlimit.tendsto_at ⟨h0, h1⟩

end RiemannResearch.RH.HilbertPolya
