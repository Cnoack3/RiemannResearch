import RiemannResearch.RH.ParetoMellinLogFourierDomain
import RiemannResearch.Analysis.FourierL1L2Plancherel
import Mathlib.Tactic.LinearCombination

/-!
# The actual Pareto Mellin transform preserves the Hilbert inner product

Source: user-requested continuum Mellin DPP construction, September 20, 2026.
The change of variables is the same logarithmic substitution as the existing
`ArithmeticPlancherelProof`; Fourier Plancherel is Mathlib's actual unitary
operator. No Mellin isometry or orthonormality provider is assumed.

The pointwise Mellin features are parametrized by ordinary Fourier frequency
`ξ`, so their angular frequency is `2πξ` and their reference measure is `dξ`.
-/

noncomputable section
open MeasureTheory Set FourierTransform
open RiemannResearch.Analysis.MellinLogStep
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

theorem paretoMellinLogComplexProfile_eq_ofReal (f : ThresholdHilbert) (u : ℝ) :
    paretoMellinLogComplexProfile f u = (paretoMellinLogProfile f u : ℂ) := by
  by_cases hu : 0 ≤ u <;>
    simp [paretoMellinLogComplexProfile, paretoMellinLogProfile,
      mellinLogProfile, logarithmicStep, hu, Complex.real_smul]

theorem paretoMellinLogComplexProfile_energy (f : ThresholdHilbert) :
    (∫ u, ‖paretoMellinLogComplexProfile f u‖ ^ 2) = ‖f‖ ^ 2 := by
  have he : (fun u => ‖paretoMellinLogComplexProfile f u‖ ^ 2) =
      (Ici (0 : ℝ)).indicator
        (fun u => hilbertSequence f ⌊Real.exp u⌋₊ ^ 2 * Real.exp (-u)) := by
    funext u
    by_cases hu : 0 ≤ u
    · have hs : Real.exp (-u / 2) ^ 2 = Real.exp (-u) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [Set.indicator_of_mem (show u ∈ Ici (0 : ℝ) from hu)]
      simp only [paretoMellinLogComplexProfile, mellinLogProfile, logarithmicStep,
        if_pos hu, norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Complex.norm_real, mul_pow, sq_abs, hs]
      ring
    · simp [paretoMellinLogComplexProfile, mellinLogProfile, logarithmicStep,
        Set.indicator, hu]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have hc := integral_comp_exp_Ioi
    (fun x : ℝ => hilbertSequence f ⌊x⌋₊ ^ 2 / x ^ 2) 0
  have heq : (fun u : ℝ => Real.exp u •
      (hilbertSequence f ⌊Real.exp u⌋₊ ^ 2 / Real.exp u ^ 2)) =
      (fun u => hilbertSequence f ⌊Real.exp u⌋₊ ^ 2 * Real.exp (-u)) := by
    funext u
    rw [smul_eq_mul, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  rw [heq, Real.exp_zero] at hc
  exact hc.trans ((paretoStep_energy_identity _
    (hilbertSequence_square_summable f)).trans (hilbert_norm_weighted_sq f).symm)

/-- The actual logarithmic realization as an `L²` vector. -/
def paretoMellinLogLp (f : ThresholdHilbert) : Lp ℂ 2 (volume : Measure ℝ) :=
  (paretoMellinLogComplexProfile_memLp f).toLp (paretoMellinLogComplexProfile f)

theorem paretoMellinLogLp_ae (f : ThresholdHilbert) :
    paretoMellinLogLp f =ᵐ[volume] paretoMellinLogComplexProfile f :=
  (paretoMellinLogComplexProfile_memLp f).coeFn_toLp

private theorem lp_integral_norm_sq (u : Lp ℂ 2 (volume : Measure ℝ)) :
    (∫ x, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ) u u
  simp only [inner_self_eq_norm_sq_to_K] at h
  norm_cast at h
  exact h.symm

theorem paretoMellinLogLp_norm (f : ThresholdHilbert) :
    ‖paretoMellinLogLp f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← lp_integral_norm_sq]
  calc
    _ = ∫ u, ‖paretoMellinLogComplexProfile f u‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [paretoMellinLogLp_ae f] with u hu
      rw [hu]
    _ = _ := paretoMellinLogComplexProfile_energy f

theorem paretoMellinLogComplexProfile_add (f g : ThresholdHilbert) :
    paretoMellinLogComplexProfile (f + g) =
      paretoMellinLogComplexProfile f + paretoMellinLogComplexProfile g := by
  funext u
  have hseq := congrFun (hilbertSequenceLinear.map_add f g) ⌊Real.exp u⌋₊
  change hilbertSequence (f + g) _ = hilbertSequence f _ + hilbertSequence g _ at hseq
  by_cases hu : 0 ≤ u <;>
    simp [paretoMellinLogComplexProfile, mellinLogProfile, logarithmicStep,
      hu, hseq, smul_add]

theorem paretoMellinLogComplexProfile_smul (c : ℝ) (f : ThresholdHilbert) :
    paretoMellinLogComplexProfile (c • f) = c • paretoMellinLogComplexProfile f := by
  funext u
  have hseq := congrFun (hilbertSequenceLinear.map_smul c f) ⌊Real.exp u⌋₊
  change hilbertSequence (c • f) _ = c * hilbertSequence f _ at hseq
  by_cases hu : 0 ≤ u <;>
    simp [paretoMellinLogComplexProfile, mellinLogProfile, logarithmicStep,
      hu, hseq, Complex.real_smul] <;> ring

/-- The logarithmic step map is an actual real-linear isometric embedding. -/
def paretoMellinLogIsometry :
    ThresholdHilbert →ₗᵢ[ℝ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun := paretoMellinLogLp
  map_add' f g := by
    apply Lp.ext
    filter_upwards [paretoMellinLogLp_ae (f + g), paretoMellinLogLp_ae f,
      paretoMellinLogLp_ae g, Lp.coeFn_add (paretoMellinLogLp f) (paretoMellinLogLp g)]
      with u hfg hf hg ha
    rw [hfg, ha]
    simp only [Pi.add_apply]
    rw [hf, hg, paretoMellinLogComplexProfile_add]
    rfl
  map_smul' c f := by
    dsimp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [paretoMellinLogLp_ae (c • f), paretoMellinLogLp_ae f,
      Lp.coeFn_smul c (paretoMellinLogLp f)] with u hcf hf hc
    rw [hcf, hc]
    simp only [Pi.smul_apply]
    rw [hf, paretoMellinLogComplexProfile_smul]
    rfl
  norm_map' := paretoMellinLogLp_norm

theorem paretoMellinLogLp_inner_im (f g : ThresholdHilbert) :
    (inner ℂ (paretoMellinLogLp f) (paretoMellinLogLp g)).im = 0 := by
  rw [L2.inner_def]
  change RCLike.im (∫ u, inner ℂ (paretoMellinLogLp f u) (paretoMellinLogLp g u)) = 0
  rw [← integral_im (L2.integrable_inner (𝕜 := ℂ)
    (paretoMellinLogLp f) (paretoMellinLogLp g))]
  calc
    _ = ∫ _ : ℝ, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [paretoMellinLogLp_ae f, paretoMellinLogLp_ae g] with u hf hg
      rw [hf, hg, paretoMellinLogComplexProfile_eq_ofReal,
        paretoMellinLogComplexProfile_eq_ofReal]
      simp [RCLike.inner_apply]
    _ = 0 := integral_zero _ _

theorem paretoMellinLogLp_inner (f g : ThresholdHilbert) :
    inner ℂ (paretoMellinLogLp f) (paretoMellinLogLp g) = (inner ℝ f g : ℂ) := by
  apply Complex.ext
  · have h := paretoMellinLogIsometry.inner_map_map f g
    change inner ℝ (paretoMellinLogLp f) (paretoMellinLogLp g) = inner ℝ f g at h
    rw [L2.inner_def] at h
    rw [L2.inner_def]
    change RCLike.re (∫ u, inner ℂ (paretoMellinLogLp f u)
      (paretoMellinLogLp g u)) = inner ℝ f g
    rw [← integral_re (L2.integrable_inner (𝕜 := ℂ)
      (paretoMellinLogLp f) (paretoMellinLogLp g))]
    calc
      _ = ∫ u, inner ℝ (paretoMellinLogLp f u) (paretoMellinLogLp g u) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun u =>
          (real_inner_eq_re_inner ℂ (paretoMellinLogLp f u) (paretoMellinLogLp g u)).symm
      _ = _ := h
  · simpa using paretoMellinLogLp_inner_im f g

/-- Complex cross-Plancherel for the actual Pareto vectors. -/
theorem paretoMellinLogFourier_inner (f g : ThresholdHilbert) :
    inner ℂ (paretoMellinLogFourier f) (paretoMellinLogFourier g) =
      (inner ℝ f g : ℂ) := by
  change inner ℂ (𝓕 (paretoMellinLogLp f)) (𝓕 (paretoMellinLogLp g)) = _
  rw [Lp.inner_fourier_eq, paretoMellinLogLp_inner]

end RiemannResearch.RH.Pareto
