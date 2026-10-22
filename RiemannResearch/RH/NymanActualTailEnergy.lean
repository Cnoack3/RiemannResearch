import RiemannResearch.RH.NymanTailTransform
import RiemannResearch.RH.CompactPolarPotential
import RiemannResearch.Analysis.RemoteLaplaceTail
import RiemannResearch.Analysis.CrossCorrelationRegularity

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Actual arithmetic-tail energy cost of an off-line zero

This is equation (10.3) of the Nyman--Weil continuation, specialized to the
actual arithmetic tail from Theorem 9.1. Its support, L2 integrability,
exponentially weighted integrability, and negative transform signature are
all derived from the concrete construction. No tail interpolation condition
or transform identity is assumed.
-/

open MeasureTheory
open MeasureTheory.BilateralLaplace
open RiemannResearch.Analysis

namespace RiemannResearch.RH

/-- The actual arithmetic tail has finite ordinary Lebesgue L2 energy. -/
theorem memLp_two_nymanCompletionTail (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    MemLp (nymanCompletionTail n M hn v) 2 volume := by
  have h := smoothSuperexponentialDecay_nymanCompletionTail n M hn hv ha hb
  apply (memLp_two_iff_integrable_sq_norm h.1.continuous.aestronglyMeasurable).2
  have hi := (h.decay.integrable_crossCorrelation h.decay
    h.1.continuous h.1.continuous 0).norm
  simpa only [add_zero, norm_mul, norm_star, pow_two] using hi

/-- Every actual centered Laplace integral used in the lower bound is
absolutely integrable; no weighted-integrability premise remains. -/
theorem integrable_nymanCompletionTail_centeredIntegrand (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) (s : ℂ) :
    Integrable (fun y : ℝ => nymanCompletionTail n M hn v y *
      BilateralLaplace.kernel (s - 1 / 2) y) := by
  have h := smoothSuperexponentialDecay_nymanCompletionTail n M hn hv ha hb
  exact integrable_integrand (h.decay.hasExponentialMoments h.1.continuous) (s - 1 / 2)

/-- The literal off-line-zero lower bound for the actual completed tail.
The only spectral assumptions concern the proposed zeta zero itself. -/
theorem nymanCompletionTail_energy_lower_bound (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρpole : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    (2 * ρ.re - 1) * Real.exp ((2 * ρ.re - 1) *
        (a + Real.log (M + 1 : ℕ))) *
      ‖centeredTransform (poleCancellationOperator v) ρ‖ ^ 2 ≤
        RemoteLaplaceTail.energy (nymanCompletionTail n M hn v) := by
  apply RemoteLaplaceTail.supported_signature_energy_lower_bound
    (nymanCompletionTail n M hn v) ρ hρ (a + Real.log (M + 1 : ℕ))
    (memLp_two_nymanCompletionTail n M hn hv ha hb)
    (fun y hy => nymanCompletionTail_zero_below n M hn ha hy)
    (centeredTransform (poleCancellationOperator v) ρ)
  exact centeredTransform_nymanCompletionTail_zeta_signature n M hn hv ha hb hρpole hzero

/-- Ordinary compact polar-annihilating tests have the same bound for their
explicit arithmetic completion, since the compact potential is constructed. -/
theorem nymanPolarCompletionTail_energy_lower_bound (n M : ℕ) (hn : 2 ≤ n)
    {f : ℝ → ℂ} {a b : ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (ha : ∀ x < a, f x = 0) (hb : ∀ x > b, f x = 0)
    (h0 : centeredTransform f 0 = 0) (h1 : centeredTransform f 1 = 0)
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρpole : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0) :
    (2 * ρ.re - 1) * Real.exp ((2 * ρ.re - 1) *
        (a + Real.log (M + 1 : ℕ))) * ‖centeredTransform f ρ‖ ^ 2 ≤
      RemoteLaplaceTail.energy
        (nymanCompletionTail n M hn (compactPolarPotential a b f)) := by
  have h := nymanCompletionTail_energy_lower_bound n M hn
    (compactPolarPotential_contDiff hf a b)
    (fun y hy => compactPolarPotential_zero_below ha hy)
    (fun y hy => compactPolarPotential_zero_above ha hb h0 h1 hy)
    hρ hρpole hzero
  rwa [poleCancellationOperator_compactPolarPotential hf.continuous a b] at h

/-- A nonzero off-line signature makes the actual ordinary tail energy
strictly positive, with the exponential coefficient above unchanged. -/
theorem nymanCompletionTail_energy_pos_of_nonzero_signature (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v)
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0)
    {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρpole : ρ ≠ 1)
    (hzero : riemannZeta ρ = 0)
    (hsig : centeredTransform (poleCancellationOperator v) ρ ≠ 0) :
    0 < RemoteLaplaceTail.energy (nymanCompletionTail n M hn v) := by
  apply lt_of_lt_of_le _ (nymanCompletionTail_energy_lower_bound n M hn hv ha hb
    hρ hρpole hzero)
  have hc : 0 < 2 * ρ.re - 1 := by linarith
  exact mul_pos (mul_pos hc (Real.exp_pos _)) (pow_pos (norm_pos_iff.mpr hsig) 2)

end RiemannResearch.RH
