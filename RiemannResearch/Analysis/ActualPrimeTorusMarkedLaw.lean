/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualPrimeTorusEnergy
import RiemannResearch.Analysis.MarkedEnergyUniformIntegrability

/-!
# Actual empirical prime-torus marked laws

The joint law assigns equal mass to every analytic zero copy and records
its prime phase and logarithmically scaled signed horizontal displacement.
The exact energy measure is N(T)/(T log T) times its quadratic phase marginal.
Selberg density remains an explicit provider hypothesis. The already proved
zero-count normalization supplies an eventual common exponential tail and
uniformly vanishing quadratic tails. Passing these empirical laws through
a weak limit and identifying the resulting energy measure remains separate.
-/

noncomputable section
open MeasureTheory Filter Zeta23 Set
open scoped BigOperators Topology NNReal ENNReal
namespace RiemannResearch.Analysis.ActualPrimeTorusMarkedLaw
open ActualZeroOrdinate PrimeTorusHaar ActualPrimeTorusFMZ PrimePhaseTorus
def markedLaw (P : Finset ℕ) (T : ℝ) : Measure (Torus P × ℝ) :=
  ∑ c : Copies T, ENNReal.ofReal ((Ncount 0 T : ℝ)⁻¹) •
    Measure.dirac (primeOrbit P c.1.1.im,
      Real.log T * (c.1.1.re - 1/2))
theorem markedLaw_isProbability (P : Finset ℕ) (T : ℝ)
    (hN : 0 < Ncount 0 T) : IsProbabilityMeasure (markedLaw P T) := by
  constructor
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by positivity
  simp only [markedLaw, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one,
    Finset.sum_const, Finset.card_univ, card_copies, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  simp [hn]

/-- Computing a quadratic phase marginal of a finite atomic law. -/
theorem energyMarginal_atoms {ι Ω X : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (w : ι → ℝ≥0∞) (z : ι → Ω) (θ : Ω → X) (Y : Ω → ℝ)
    (hθ : Measurable θ) :
    MarkedEnergyMarginal.energyMarginal (∑ i, w i • Measure.dirac (z i)) θ Y =
      ∑ i, (w i * ENNReal.ofReal ((Y (z i))^2)) • Measure.dirac (θ (z i)) := by
  unfold MarkedEnergyMarginal.energyMarginal
  rw [← Measure.sum_fintype, withDensity_sum, Measure.map_sum hθ.aemeasurable,
    Measure.sum_fintype]
  simp_rw [withDensity_smul_measure, dirac_withDensity, Measure.map_smul,
    Measure.map_dirac, smul_smul]

/-- The actual finite energy measure is precisely the quadratic-mark marginal
of the actual empirical phase/displacement law, with its exact normalization. -/
theorem energyMeasure_eq_scaled_markedLaw (P : Finset ℕ) (T : ℝ)
    (hT : 1 < T) (hN : 0 < Ncount 0 T) :
    ActualPrimeTorusEnergy.energyMeasure P T =
      ENNReal.ofReal ((Ncount 0 T : ℝ) / (T * Real.log T)) •
        MarkedEnergyMarginal.energyMarginal (markedLaw P T) Prod.fst Prod.snd := by
  rw [markedLaw, energyMarginal_atoms _ _ _ _ measurable_fst,
    ActualPrimeTorusEnergy.energyMeasure, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [smul_smul]
  congr 1
  have hn : (Ncount 0 T : ℝ) ≠ 0 := by positivity
  have hL : 0 < Real.log T := Real.log_pos hT
  have hTpos : 0 < T := by linarith
  have hl : Real.log T ≠ 0 := hL.ne'
  have ht : T ≠ 0 := by linarith
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (Ncount 0 T : ℝ)⁻¹),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (Ncount 0 T : ℝ) / (T * Real.log T))]
  congr 1
  dsimp
  field_simp [hn, hl, ht]
  <;> ring

/-- Exact normalized count for the logarithmically scaled displacement mark. -/
theorem markedLaw_abs_mark_tail (P : Finset ℕ) (T t : ℝ) (hT : 1 < T) :
    markedLaw P T {z | t < |z.2|} =
      ENNReal.ofReal (strictTail T (t / Real.log T) / (Ncount 0 T : ℝ)) := by
  classical
  have hL : 0 < Real.log T := Real.log_pos hT
  rw [markedLaw, Measure.finsetSum_apply, strictTail_eq_realSum,
    realSum_eq_copies, Finset.sum_div, ENNReal.ofReal_sum_of_nonneg
      (fun c _ => div_nonneg (by split_ifs <;> norm_num) (Nat.cast_nonneg _))]
  apply Finset.sum_congr rfl
  intro c hc
  have heq : (t < |Real.log T * (c.1.1.re - 1/2)|) ↔
      t / Real.log T < |c.1.1.re - 1/2| := by
    rw [abs_mul, abs_of_pos hL, div_lt_iff₀ hL, mul_comm]
  rw [Measure.smul_apply, Measure.dirac_apply]
  change ENNReal.ofReal ((Ncount 0 T : ℝ)⁻¹) *
    (if t < |Real.log T * (c.1.1.re - 1/2)| then 1 else 0) =
    ENNReal.ofReal ((if t / Real.log T < |c.1.1.re - 1/2| then 1 else 0) /
      (Ncount 0 T : ℝ))
  by_cases hh : t / Real.log T < |c.1.1.re - 1/2|
  · rw [if_pos (heq.mpr hh), if_pos hh]
    simp only [mul_one, one_div]
  · rw [if_neg (mt heq.mp hh), if_neg hh]
    simp

/-- Uniform Selberg strip control transfers to the actual empirical mark law
with any explicit positive zero-count normalization. -/
theorem markedLaw_exponential_tail (P : Finset ℕ) (T C a c : ℝ)
    (hT : 1 < T) (hC : 0 ≤ C) (hc : 0 < c)
    (hD : SelbergDensityBound T C a)
    (hN : c * T * Real.log T ≤ (Ncount 0 T : ℝ)) :
    ∀ t > 0, markedLaw P T {z | t < |z.2|} ≤
      ENNReal.ofReal ((2*C/c) * Real.exp (-a * t)) := by
  intro t ht
  rw [markedLaw_abs_mark_tail P T t hT]
  apply ENNReal.ofReal_le_ofReal
  have hL : 0 < Real.log T := Real.log_pos hT
  by_cases hcut : t / Real.log T ≤ 1/2
  · have h := normalized_strictTail_of_selbergDensity T C a
      (t / Real.log T) c hT hC hc ⟨(div_pos ht hL).le, hcut⟩ hD hN
    convert h using 1
    congr 2
    field_simp
  · have hzero : strictTail T (t / Real.log T) = 0 := by
      rw [strictTail_eq_realSum, realSum_eq_copies]
      apply Finset.sum_eq_zero
      intro d hd
      rw [if_neg]
      exact not_lt.mpr ((displacement_lt_half d.1.2).le.trans (le_of_not_ge hcut))
    rw [hzero, zero_div]
    positivity

/-- The density provider and the proved zero-count lower bound yield one
exponential-tail constant for all sufficiently large actual marked laws. -/
theorem eventually_uniform_mark_tail (P : Finset ℕ) (a : ℝ)
    (hD : UniformSelbergDensity a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop,
      IsProbabilityMeasure (markedLaw P T) ∧
      ∀ t > 0, markedLaw P T {z | t < |z.2|} ≤
        ENNReal.ofReal (K * Real.exp (-a * t)) := by
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hD
  let c : ℝ := 1 / (16 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨2*C/c, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T₀, eventually_count_ge_log] with T hT hN
  have hT1 : 1 < T := hT₀.trans_le hT
  have hL : 0 < Real.log T := Real.log_pos hT1
  have hTpos : 0 < T := by linarith
  have hNpos : 0 < Ncount 0 T := by
    have hn : 0 < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hN
    exact_mod_cast hn
  exact ⟨markedLaw_isProbability P T hNpos,
    markedLaw_exponential_tail P T C a c hT1 hC hc (hD T hT) hN⟩

/-- Actual empirical quadratic marks are uniformly integrable in the
large-height range, with the cutoff chosen independently of height. -/
theorem eventually_uniform_quadratic_tail (P : Finset ℕ) (a : ℝ)
    (ha : 0 < a) (hD : UniformSelbergDensity a) :
    ∀ ε > 0, ∃ R₀ > 0, ∀ᶠ T : ℝ in atTop, ∀ R ≥ R₀,
      (∫⁻ z in {z : Torus P × ℝ | R < |z.2|}, ENNReal.ofReal (z.2^2)
        ∂markedLaw P T) ≤ ENNReal.ofReal ε := by
  obtain ⟨K, hK, htail⟩ := eventually_uniform_mark_tail P a hD
  intro ε hε
  obtain ⟨A, hA⟩ := eventually_atTop.mp
    ((MarkedEnergyUniformIntegrability.quadratic_tail_envelope_tendsto_zero K a ha).eventually
      (eventually_lt_nhds hε))
  refine ⟨max 1 A, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  filter_upwards [htail] with T hT
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  exact (MarkedEnergyUniformIntegrability.square_tail_lintegral_le
    (markedLaw P T) Prod.snd measurable_snd K a R hK ha hRpos hT.2).trans
      (ENNReal.ofReal_le_ofReal (hA R ((le_max_right _ _).trans hR)).le)

end RiemannResearch.Analysis.ActualPrimeTorusMarkedLaw
