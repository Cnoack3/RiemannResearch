/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimeTorusCenteredMeasure
import RiemannResearch.Analysis.ActualRationalThirdCoefficient
import RiemannResearch.Analysis.ActualPrimeTorusFMZ
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Actual positive prime-torus horizontal-energy measures

Source: Section 7 of the user's FRZ strengthening note (2026-11-10).
The exact finite atomic measures retain every analytic zero multiplicity.
Selberg density is an explicit provider hypothesis. Compactness produces one
weak subsequence for all continuous tests, without any full-height limit claim.
-/

noncomputable section
open MeasureTheory Filter Zeta23
open scoped BigOperators Topology NNReal ENNReal
namespace RiemannResearch.Analysis.ActualPrimeTorusEnergy
open ActualZeroOrdinate PrimeTorusHaar ActualPrimeTorusFMZ PrimePhaseTorus

/-- The actual positive horizontal energy measure; multiplicities are counted
exactly once through the finite type of copies. -/
def energyMeasure (P : Finset ℕ) (T : ℝ) : Measure (Torus P) :=
  ∑ c : Copies T, ENNReal.ofReal ((Real.log T / T) *
    (c.1.1.re - 1 / 2) ^ 2) • Measure.dirac (primeOrbit P c.1.1.im)

instance energyMeasure_isFiniteMeasure (P : Finset ℕ) (T : ℝ) :
    IsFiniteMeasure (energyMeasure P T) := by
  constructor
  simp [energyMeasure, Measure.finsetSum_apply, Measure.smul_apply]

theorem integral_energyMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (P : Finset ℕ) (T : ℝ)
    (hT : 1 < T) (f : Torus P → E) :
    (∫ x, f x ∂energyMeasure P T) =
      ∑ c : Copies T, ((Real.log T / T) * (c.1.1.re - 1 / 2)^2) •
        f (primeOrbit P c.1.1.im) := by
  have hnonneg (c : Copies T) :
      0 ≤ Real.log T / T * (c.1.1.re - 1 / 2)^2 :=
    mul_nonneg (div_nonneg (Real.log_pos hT).le (by linarith)) (sq_nonneg _)
  unfold energyMeasure
  rw [integral_finsetSum_measure (fun c _ =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (hnonneg _)]

theorem energyMeasure_mass (P : Finset ℕ) (T : ℝ) (hT : 1 < T) :
    (energyMeasure P T).real Set.univ =
      Real.log T / T * horizontalEnergy T := by
  have h := integral_energyMeasure P T hT (fun _ => (1 : ℝ))
  simpa [horizontalEnergy, realSum_eq_copies, smul_eq_mul,
    Finset.mul_sum] using h

theorem energyMeasure_mass_le (P : Finset ℕ) (T C a : ℝ)
    (hT : 1 < T) (hC : 0 ≤ C) (ha : 0 < a)
    (hD : SelbergDensityBound T C a) :
    (energyMeasure P T).real Set.univ ≤ 4 * C / a^2 := by
  rw [energyMeasure_mass P T hT]
  calc
    _ = Real.log T * (horizontalEnergy T / T) := by ring
    _ ≤ Real.log T * (4 * C / (a^2 * Real.log T)) :=
      mul_le_mul_of_nonneg_left
        (horizontalEnergy_div_height_le_log_rate T C a hT hC ha hD)
        (Real.log_pos hT).le
    _ = _ := by field_simp [ne_of_gt (Real.log_pos hT)]

theorem integral_character_energyMeasure (P : Finset ℕ) (T : ℝ)
    (hT : 1 < T) (k : ℕ → ℤ) :
    (∫ x, character (fun p : P => k p) x ∂energyMeasure P T) =
      (Real.log T : ℂ) *
        (evenHorizontalMoment T (primeFrequency P k) 1 / (T : ℂ)) := by
  rw [integral_energyMeasure P T hT]
  simp only [character_primeOrbit_eq_phase, evenHorizontalMoment,
    sum_eq_copies, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow]
  ring

def finiteEnergyMeasure (P : Finset ℕ) (T : ℝ) : FiniteMeasure (Torus P) :=
  ⟨energyMeasure P T, inferInstance⟩

theorem finiteEnergyMeasure_mass (P : Finset ℕ) (T : ℝ) :
    ((finiteEnergyMeasure P T).mass : ℝ) = (energyMeasure P T).real Set.univ := rfl

theorem isCompact_energyMeasure_mass_bound (P : Finset ℕ) (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure (Torus P) | μ.mass ≤ C} :=
  isCompact_setOfPred_finiteMeasure_le_of_compactSpace (Torus P) C


/-- A single subsequence works for every continuous test simultaneously.
Normalization is allowed even at zero mass. -/
theorem exists_weakly_convergent_subsequence (P : Finset ℕ)
    (μ : ℕ → FiniteMeasure (Torus P)) (C : ℝ≥0)
    (hμ : ∀ n, (μ n).mass ≤ C) :
    ∃ ν : FiniteMeasure (Torus P), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  letI : CompactSpace (Set.Icc (0 : ℝ≥0) C) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let q : ℕ → Set.Icc (0 : ℝ≥0) C × ProbabilityMeasure (Torus P) :=
    fun n => (⟨(μ n).mass, ⟨zero_le, hμ n⟩⟩, (μ n).normalize)
  obtain ⟨v, φ, hφ, hv⟩ := CompactSpace.tendsto_subseq q
  refine ⟨v.1.1 • v.2.toFiniteMeasure, φ, hφ, ?_⟩
  have hm := ((continuous_subtype_val.comp continuous_fst).tendsto v).comp hv
  have hp := ((ProbabilityMeasure.toFiniteMeasure_continuous.comp continuous_snd).tendsto v).comp hv
  have h := hm.smul hp
  change Tendsto (fun n => (μ (φ n)).mass • (μ (φ n)).normalize.toFiniteMeasure)
    atTop (𝓝 (v.1.1 • v.2.toFiniteMeasure)) at h
  simpa only [← FiniteMeasure.self_eq_mass_smul_normalize, Function.comp_def] using h

/-- Weak convergence gives all continuous complex test limits with the same
subsequence; there is no dependence of the subsequence on the test. -/
theorem integral_tendsto_of_weak {P : Finset ℕ} {μ : ℕ → FiniteMeasure (Torus P)}
    {ν : FiniteMeasure (Torus P)}
    (hμ : Tendsto μ atTop (𝓝 ν)) (f : C(Torus P, ℂ)) :
    Tendsto (fun n => ∫ x, f x ∂(μ n : Measure (Torus P))) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure (Torus P)))) :=
  (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hμ
    (BoundedContinuousFunction.mkOfCompact f)

/-- The classical density premise gives a genuine simultaneous weakly
convergent subsequence of the actual positive energy measures. -/
theorem actual_energy_subsequence (P : Finset ℕ) (T : ℕ → ℝ) (C a : ℝ)
    (hC : 0 ≤ C) (ha : 0 < a) (hT : ∀ n, 1 < T n)
    (hD : ∀ n, SelbergDensityBound (T n) C a) :
    ∃ ν : FiniteMeasure (Torus P), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => finiteEnergyMeasure P (T (φ n))) atTop (𝓝 ν) := by
  apply exists_weakly_convergent_subsequence P (fun n => finiteEnergyMeasure P (T n))
    ⟨4 * C / a^2, by positivity⟩
  intro n
  change ((finiteEnergyMeasure P (T n)).mass : ℝ) ≤ 4 * C / a^2
  exact energyMeasure_mass_le P (T n) C a (hT n) hC ha (hD n)


/-- The density premise need only hold eventually. Every divergent sequence
of actual heights has one subsequence for all continuous prime-torus tests. -/
theorem actual_energy_subsequence_of_uniformSelberg (P : Finset ℕ)
    (a : ℝ) (ha : 0 < a) (hD : UniformSelbergDensity a)
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop atTop) :
    ∃ ν : FiniteMeasure (Torus P), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (fun n => finiteEnergyMeasure P (τ (φ n))) atTop (𝓝 ν) := by
  obtain ⟨C, T₀, hC, hT₀, hden⟩ := hD
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hτ.eventually (eventually_ge_atTop T₀))
  obtain ⟨ν, φ, hφ, hν⟩ := actual_energy_subsequence P (fun n => τ (n+N)) C a
    hC ha (fun n => hT₀.trans_le (hN (n+N) (by omega)))
    (fun n => hden _ (hN (n+N) (by omega)))
  exact ⟨ν, fun n => φ n+N, fun i j hij => Nat.add_lt_add_right (hφ hij) N, hν⟩


/-- Exact exchange with an absolutely convergent continuous Fourier series. -/
theorem integral_fourierSeries_energyMeasure {κ : Type*} (P : Finset ℕ)
    (T : ℝ) (hT : 1 < T) (a : κ → ℂ) (k : κ → ℕ → ℤ)
    (ha : Summable (fun i => ‖a i‖)) :
    (∫ x, fourierSeries a (fun i (p : P) => k i p) x ∂energyMeasure P T) =
      ∑' i, a i * ((Real.log T : ℂ) *
        (evenHorizontalMoment T (primeFrequency P (k i)) 1 / (T : ℂ))) := by
  change PrimeTorusCenteredMeasure.integralCLM (finiteEnergyMeasure P T)
    (fourierSeries a (fun i (p : P) => k i p)) = _
  rw [fourierSeries, (PrimeTorusCenteredMeasure.integralCLM
    (finiteEnergyMeasure P T)).map_tsum
      (summable_fourierSeries a (fun i (p : P) => k i p) ha)]
  apply tsum_congr
  intro i
  rw [map_smul, smul_eq_mul, PrimeTorusCenteredMeasure.integralCLM_apply]
  exact congrArg (a i * ·) (integral_character_energyMeasure P T hT (k i))


/-- All rational prime modes have horizontal-energy limits along one
subsequence. The subsequence is independent of the mode. -/
theorem actual_all_modes_subsequence (P : Finset ℕ)
    (a : ℝ) (ha : 0 < a) (hD : UniformSelbergDensity a)
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop atTop) :
    ∃ ν : FiniteMeasure (Torus P), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ k : ℕ → ℤ,
        Tendsto (fun n => (Real.log (τ (φ n)) : ℂ) *
          (evenHorizontalMoment (τ (φ n)) (primeFrequency P k) 1 / (τ (φ n) : ℂ)))
          atTop (𝓝 (∫ x, character (fun p : P => k p) x ∂(ν : Measure (Torus P)))) := by
  obtain ⟨ν, φ, hφ, hν⟩ := actual_energy_subsequence_of_uniformSelberg P a ha hD τ hτ
  refine ⟨ν, φ, hφ, ?_⟩
  intro k
  have h := integral_tendsto_of_weak hν (character (fun p : P => k p))
  apply h.congr'
  filter_upwards [(hτ.comp hφ.tendsto_atTop).eventually (eventually_gt_atTop (1 : ℝ))]
    with n hn
  exact integral_character_energyMeasure P (τ (φ n)) hn k

end RiemannResearch.Analysis.ActualPrimeTorusEnergy
