import RiemannResearch.RH.ParetoMellinHardyEndpoint
import RiemannResearch.RH.ThresholdRiemannHypothesis
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-!
# Independent weighted and vertical-line approximation criteria

Sources: the Mellin zero-evaluation strategy underlying the Nyman--Beurling
criterion and Manzur--Noor--Quintero, "A Hardy space approximation supporting
zero-free half-planes for the zeta-function" (2026), Proposition 3.1:
https://arxiv.org/abs/2606.16097 .
The statements below are an independent adaptation to this project's actual
Pareto Hilbert space and proved weighted Mellin transform. No novelty is claimed.

A right-hand zeta zero imposes an explicit positive weighted error floor.
Independent approximants on individual lines approaching Re(s)=1/2 suffice
for RH; no common bound or coherent family is required. The existence of
these approximants is an OPEN domain-specific hypothesis, not a conclusion
of the unconditional PNT endpoint results.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
open WeightedMellin

theorem weightedError_lower_of_zeta
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (f : ThresholdHilbert) (hf : f ∈ hilbertLegalClosure A)
    (u : ℝ) (hu : 1 ≤ u)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hus : u < 2 * s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2 * s.re - u) / ‖s‖ ^ 2 ≤
      energy (complexPhysicalStep (hilbertOne - f)) u := by
  have herrEnergy := finiteEnergy_mono
    (complexPhysicalStep_finiteEnergy (hilbertOne - f)) hu
  have hfzero := paretoMellin_zero_on_legalClosure_of_zeta A hA s hs hs1 hz hf
  have heval : paretoMellin (hilbertOne - f) s = 1 / s := by
    change paretoMellinContinuous s hs (hilbertOne - f) = _
    rw [map_sub]
    change paretoMellin hilbertOne s - paretoMellin f s = _
    rw [paretoMellin_one s hs, hfzero, sub_zero]
  have hb := transform_norm_sq_le herrEnergy (z := s) (by linarith)
  rw [complexPhysicalStep_transform, heval] at hb
  simp only [norm_div, norm_one, div_pow, one_pow] at hb
  have hm := (le_div_iff₀ (show 0 < 2 * s.re - u by linarith)).mp hb
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hm

theorem zeta_ne_zero_of_arbitrarily_small_weighted_error
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) (u : ℝ) (hu : 1 ≤ u)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ f ∈ hilbertLegalClosure A,
      energy (complexPhysicalStep (hilbertOne - f)) u < ε)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hus : u < 2 * s.re)
    (hs1 : s ≠ 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hp : 0 < (2 * s.re - u) / ‖s‖ ^ 2 :=
    div_pos (by linarith) (pow_pos (norm_pos_iff.mpr hs0) 2)
  obtain ⟨f, hf, he⟩ := happrox _ hp
  exact (not_lt_of_ge (weightedError_lower_of_zeta A hA f hf u hu s hs hus hs1 hz)) he

theorem riemannHypothesis_of_independent_weighted_approximation
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (u : ℕ → ℝ) (hu : ∀ j, 1 ≤ u j)
    (hlim : Tendsto u atTop (𝓝 1))
    (happrox : ∀ j ε, 0 < ε → ∃ f ∈ hilbertLegalClosure A,
      energy (complexPhysicalStep (hilbertOne - f)) (u j) < ε) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (show 1 < 2 * s.re by linarith))).exists
  exact zeta_ne_zero_of_arbitrarily_small_weighted_error A hA (u j) (hu j)
    (happrox j) s hs hj (by intro he; norm_num [he] at hslt)

theorem paretoMellin_line_energy (f : ThresholdHilbert)
    (σ : ℝ) (hσ : (1 / 2 : ℝ) < σ) :
    (∫ w : ℝ, ‖paretoMellin f (verticalPoint σ w)‖ ^ 2) =
      energy (complexPhysicalStep f) (2 * σ) := by
  simpa only [complexPhysicalStep_transform] using
    vertical_plancherel (complexPhysicalStep_finiteEnergy f) hσ

theorem riemannHypothesis_of_independent_line_approximation
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (σ : ℕ → ℝ) (hσ : ∀ j, (1 / 2 : ℝ) < σ j)
    (hlim : Tendsto σ atTop (𝓝 (1 / 2)))
    (happrox : ∀ j ε, 0 < ε → ∃ f ∈ hilbertLegalClosure A,
      (∫ w : ℝ, ‖paretoMellin (hilbertOne - f) (verticalPoint (σ j) w)‖ ^ 2) < ε) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_independent_weighted_approximation A hA
    (fun j => 2 * σ j) (fun j => by linarith [hσ j])
  · simpa using hlim.const_mul 2
  · intro j ε hε
    obtain ⟨f, hf, he⟩ := happrox j ε hε
    exact ⟨f, hf, by rwa [paretoMellin_line_energy _ _ (hσ j)] at he⟩

end RiemannResearch.RH.Pareto
