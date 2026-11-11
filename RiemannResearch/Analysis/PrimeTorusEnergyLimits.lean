/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualPrimeTorusEnergy
import RiemannResearch.Analysis.PrimeTorusCenteredMeasure
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Centered weak limits and nonconstant Fourier limits

Source: Section 7, Proposition 9 and Section 8 Fourth of the user's FRZ note.
The candidate limit is constructed rather than assumed. The equivalence holds
at real height atTop with only an eventual mass bound. It does not prove the
missing nonconstant mode limits for actual zeta zeros.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace RiemannResearch.Analysis.PrimeTorusEnergyLimits
open ActualPrimeTorusEnergy PrimeTorusCenteredMeasure PrimeTorusHaar

theorem centeredIntegral_tendsto_of_weak {P : Finset ℕ}
    {μ : ℕ → FiniteMeasure (Torus P)} {ν : FiniteMeasure (Torus P)}
    (hμ : Tendsto μ atTop (𝓝 ν)) (f : C(Torus P, ℂ)) :
    Tendsto (fun n => centeredIntegral (μ n) f) atTop (𝓝 (centeredIntegral ν f)) := by
  have hm : Tendsto (fun n => (((μ n).mass : ℝ) : ℂ)) atTop
      (𝓝 ((ν.mass : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp
      ((NNReal.continuous_coe.tendsto _).comp hμ.mass)
  simpa only [centeredIntegral_apply] using
    (integral_tendsto_of_weak hμ f).sub (hm.mul_const (haarIntegral f))

/-- For bounded positive measures, convergence of every nonconstant Fourier
coefficient is equivalent to weak convergence of the centered measures.
The full positive mass may vary or retain a nonzero Haar component. -/
theorem centered_weak_iff_nonconstant_fourier (P : Finset ℕ)
    (μ : ℕ → FiniteMeasure (Torus P)) (ν : FiniteMeasure (Torus P))
    (C : ℝ≥0) (hbound : ∀ n, (μ n).mass ≤ C) :
    (∀ f : C(Torus P, ℂ),
      Tendsto (fun n => centeredIntegral (μ n) f) atTop (𝓝 (centeredIntegral ν f))) ↔
    (∀ k : P → ℤ, k ≠ 0 →
      Tendsto (fun n => ∫ x, character k x ∂(μ n : Measure (Torus P))) atTop
        (𝓝 (∫ x, character k x ∂(ν : Measure (Torus P))))) := by
  constructor
  · intro h k hk
    simpa only [centeredIntegral_character _ k hk] using h (character k)
  · intro h f
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨η, ms, hms, hη⟩ :=
      exists_weakly_convergent_subsequence P (fun n => μ (ns n)) C
        (fun n => hbound (ns n))
    have heq : centeredIntegral η = centeredIntegral ν := by
      apply centeredIntegral_ext
      intro k hk
      exact tendsto_nhds_unique (integral_tendsto_of_weak hη (character k))
        (((h k hk).comp hns).comp hms.tendsto_atTop)
    refine ⟨ms, ?_⟩
    simpa only [heq, Function.comp_apply] using
      centeredIntegral_tendsto_of_weak hη f


/-- Exact existence form: the candidate centered limit is constructed from
one weakly convergent subsequence, rather than assumed in advance. -/
theorem exists_centered_weak_limit_iff_nonconstant_fourier_limits (P : Finset ℕ)
    (μ : ℕ → FiniteMeasure (Torus P)) (C : ℝ≥0)
    (hbound : ∀ n, (μ n).mass ≤ C) :
    (∀ k : P → ℤ, k ≠ 0 → ∃ z : ℂ,
      Tendsto (fun n => ∫ x, character k x ∂(μ n : Measure (Torus P))) atTop (𝓝 z)) ↔
    (∃ ν : FiniteMeasure (Torus P), ∀ f : C(Torus P, ℂ),
      Tendsto (fun n => centeredIntegral (μ n) f) atTop (𝓝 (centeredIntegral ν f))) := by
  constructor
  · intro h
    obtain ⟨ν, φ, hφ, hν⟩ := exists_weakly_convergent_subsequence P μ C hbound
    refine ⟨ν, (centered_weak_iff_nonconstant_fourier P μ ν C hbound).mpr ?_⟩
    intro k hk
    obtain ⟨z, hz⟩ := h k hk
    have heq := tendsto_nhds_unique (hz.comp hφ.tendsto_atTop)
      (integral_tendsto_of_weak hν (character k))
    simpa only [heq] using hz
  · rintro ⟨ν, hν⟩ k hk
    exact ⟨_, (centered_weak_iff_nonconstant_fourier P μ ν C hbound).mp hν k hk⟩


/-- The centered criterion works for every countably generated filter, with
only an eventual mass bound. In particular it applies to real height atTop. -/
theorem centered_tendsto_iff_nonconstant_fourier {δ : Type*} (l : Filter δ)
    [l.IsCountablyGenerated] (P : Finset ℕ)
    (μ : δ → FiniteMeasure (Torus P)) (ν : FiniteMeasure (Torus P))
    (C : ℝ≥0) (hbound : ∀ᶠ n in l, (μ n).mass ≤ C) :
    (∀ f : C(Torus P, ℂ),
      Tendsto (fun n => centeredIntegral (μ n) f) l (𝓝 (centeredIntegral ν f))) ↔
    (∀ k : P → ℤ, k ≠ 0 →
      Tendsto (fun n => ∫ x, character k x ∂(μ n : Measure (Torus P))) l
        (𝓝 (∫ x, character k x ∂(ν : Measure (Torus P))))) := by
  constructor
  · intro h k hk
    simpa only [centeredIntegral_character _ k hk] using h (character k)
  · intro h f
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hns.eventually hbound)
    have hshift : StrictMono (fun n : ℕ => n + N) :=
      fun i j hij => Nat.add_lt_add_right hij N
    refine ⟨fun n => n + N, ?_⟩
    refine (centered_weak_iff_nonconstant_fourier P
      (fun n => μ (ns (n+N))) ν C (fun n => hN _ (by omega))).mpr ?_ f
    intro k hk
    exact ((h k hk).comp hns).comp hshift.tendsto_atTop

/-- Full real-height existence form. Uniform mass and all nonconstant
Fourier limits construct a centered weak limit without a candidate premise. -/
theorem exists_real_centered_limit_iff_nonconstant_fourier_limits (P : Finset ℕ)
    (μ : ℝ → FiniteMeasure (Torus P)) (C : ℝ≥0)
    (hbound : ∀ᶠ T : ℝ in atTop, (μ T).mass ≤ C) :
    (∀ k : P → ℤ, k ≠ 0 → ∃ z : ℂ,
      Tendsto (fun T => ∫ x, character k x ∂(μ T : Measure (Torus P))) atTop (𝓝 z)) ↔
    (∃ ν : FiniteMeasure (Torus P), ∀ f : C(Torus P, ℂ),
      Tendsto (fun T => centeredIntegral (μ T) f) atTop (𝓝 (centeredIntegral ν f))) := by
  constructor
  · intro h
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hbound
    let τ : ℕ → ℝ := fun n => (n : ℝ) + T₀
    have hτ : Tendsto τ atTop atTop := by
      apply tendsto_atTop.2
      intro b
      obtain ⟨N, hN⟩ := exists_nat_ge (b - T₀)
      filter_upwards [eventually_ge_atTop N] with n hn
      change b ≤ (n : ℝ) + T₀
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hb : ∀ n, (μ (τ n)).mass ≤ C := by
      intro n
      apply hT₀
      dsimp [τ]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨ν, φ, hφ, hν⟩ := exists_weakly_convergent_subsequence P (μ ∘ τ) C hb
    refine ⟨ν, (centered_tendsto_iff_nonconstant_fourier atTop P μ ν C hbound).mpr ?_⟩
    intro k hk
    obtain ⟨z, hz⟩ := h k hk
    have heq := tendsto_nhds_unique ((hz.comp hτ).comp hφ.tendsto_atTop)
      (integral_tendsto_of_weak hν (character k))
    simpa only [heq] using hz
  · rintro ⟨ν, hν⟩ k hk
    exact ⟨_, (centered_tendsto_iff_nonconstant_fourier atTop P μ ν C hbound).mp hν k hk⟩

/-- The actual density estimate supplies the eventual bound required by the
full real-height centered Fourier criterion. -/
theorem actual_centered_limit_iff (P : Finset ℕ)
    (a : ℝ) (ha : 0 < a) (hD : ActualZeroOrdinate.UniformSelbergDensity a) :
    (∀ k : P → ℤ, k ≠ 0 → ∃ z : ℂ,
      Tendsto (fun T : ℝ => ∫ x, character k x ∂energyMeasure P T) atTop (𝓝 z)) ↔
    (∃ ν : FiniteMeasure (Torus P), ∀ f : C(Torus P, ℂ),
      Tendsto (fun T : ℝ => centeredIntegral (finiteEnergyMeasure P T) f)
        atTop (𝓝 (centeredIntegral ν f))) := by
  obtain ⟨C, T₀, hC, hT₀, hden⟩ := hD
  apply exists_real_centered_limit_iff_nonconstant_fourier_limits P
    (fun T => finiteEnergyMeasure P T) ⟨4*C/a^2, by positivity⟩
  filter_upwards [eventually_ge_atTop T₀] with T hT
  change ((finiteEnergyMeasure P T).mass : ℝ) ≤ 4*C/a^2
  exact energyMeasure_mass_le P T C a (hT₀.trans_le hT) hC ha (hden T hT)

end RiemannResearch.Analysis.PrimeTorusEnergyLimits
