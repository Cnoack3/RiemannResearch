import RiemannResearch.RH.ParetoLegalApproximationClosure
import RiemannResearch.RH.ThresholdInterpolationCompleteness
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Exact mean-one approximation in the original Pareto Hilbert space

Source: user-provided argument in
`RH_Iff_Two_Seed_Approximation_20260914.md`, Sections 5 and 6.

These equivalences have no arithmetic approximation assumption. They identify
target membership, full legal density, arbitrarily small mean-one variance,
and existence of an actual sequence of finite legal packets with variance
tending to zero. They do not assert that any of these properties holds.

All positive integer dilation indices remain available in `legalSeedSpan`.
Every mean and variance below is the complete infinite Pareto quantity.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section
open Filter
open scoped Topology

/-- A legal closed space is the whole Hilbert space exactly when it contains
the target. Target-to-density uses the complete integer dilation action. -/
theorem hilbertLegalClosure_eq_top_iff_one_mem (A : Set ℕ) :
    hilbertLegalClosure A = ⊤ ↔ hilbertOne ∈ hilbertLegalClosure A := by
  constructor
  · intro h
    rw [h]
    trivial
  · exact hilbertLegalClosure_eq_top_of_one_mem A

/-- Exact target approximation can be normalized to mean one without changing
the legal family. Conversely, a mean-one packet has error equal to variance. -/
theorem hilbertOne_mem_legalClosure_iff_meanOne_variance
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    hilbertOne ∈ hilbertLegalClosure A ↔
      ∀ ε : ℝ, 0 < ε → ∃ f : ℕ → ℝ,
        f ∈ legalSeedSpan A ∧ paretoMean f = 1 ∧ paretoVariance f < ε := by
  rw [hilbertOne_mem_legalClosure_iff_noiseSignalRatio A hA]
  constructor
  · intro h ε hε
    obtain ⟨f, hf, hm, herr⟩ := h ε hε
    obtain ⟨C, hC⟩ := legalSeedSpan_bounded A hA hf
    let g : ℕ → ℝ := fun k => (paretoMean f)⁻¹ * f k
    have hg : g ∈ legalSeedSpan A := (legalSeedSpan A).smul_mem _ hf
    have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
    have hgmean : paretoMean g = 1 := by
      rw [← paretoInner_one_right]
      unfold g
      rw [paretoInner_const_mul_left hC h1, paretoInner_one_right,
        inv_mul_cancel₀ hm]
    have hgbound : ∀ k, |g k| ≤ |(paretoMean f)⁻¹| * C :=
      bounded_const_mul hC _
    have herror : paretoError g = paretoVariance g := by
      rw [paretoError_eq_variance_add_bias_sq hgbound, hgmean]
      ring
    have he : paretoError g = noiseSignalRatio f :=
      paretoError_mean_normalization hC hm
    refine ⟨g, hg, hgmean, ?_⟩
    rw [← herror, he]
    exact herr
  · intro h ε hε
    obtain ⟨f, hf, hm, herr⟩ := h ε hε
    refine ⟨f, hf, ?_, ?_⟩
    · rw [hm]
      norm_num
    · simpa [noiseSignalRatio, hm] using herr

/-- An actual sequence of finite legal mean-one packets is equivalent to the
epsilon formulation. This selection theorem does not supply the approximation
property without target membership. -/
theorem hilbertOne_mem_legalClosure_iff_meanOne_variance_sequence
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    hilbertOne ∈ hilbertLegalClosure A ↔
      ∃ F : ℕ → ℕ → ℝ,
        (∀ j, F j ∈ legalSeedSpan A) ∧
        (∀ j, paretoMean (F j) = 1) ∧
        Tendsto (fun j => paretoVariance (F j)) atTop (𝓝 0) := by
  rw [hilbertOne_mem_legalClosure_iff_meanOne_variance A hA]
  constructor
  · intro h
    have hs : ∀ j : ℕ, ∃ f : ℕ → ℝ,
        f ∈ legalSeedSpan A ∧ paretoMean f = 1 ∧
        paretoVariance f < 1 / ((j : ℝ) + 1) := by
      intro j
      exact h _ (by positivity)
    choose F hlegal hmean herr using hs
    refine ⟨F, hlegal, hmean, ?_⟩
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, ?_⟩
    intro n hn
    have hncast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hN' : 1 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hN
    have hprod : (N : ℝ) * ε ≤ (n : ℝ) * ε :=
      mul_le_mul_of_nonneg_right hncast hε.le
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hsmall : 1 / ((n : ℝ) + 1) < ε := by
      apply (div_lt_iff₀ hden).mpr
      nlinarith
    simpa [Real.dist_eq, abs_of_nonneg (paretoVariance_nonneg (F n))] using
      (herr n).trans hsmall
  · rintro ⟨F, hlegal, hmean, hvar⟩ ε hε
    obtain ⟨n, hn⟩ := (hvar.eventually_lt_const hε).exists
    exact ⟨F n, hlegal n, hmean n, hn⟩

end
end RiemannResearch.RH.Pareto
