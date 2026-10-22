import RiemannResearch.Analysis.LogarithmicGrowth
import RiemannResearch.RH.AnnularSubpowerEnergy

-- This private project has no Mathlib Apache license header.
set_option linter.style.header false in
/-!
# Actual annular energy growth and the complete signed residual

For the actual prime signal, centered energy, and complete signed residual,
the exact identity is E_A = E_U + T and E_U = M + R.
The signed lattice cross term and square remain in T.

The actual energy exponent is in [0,1] unconditionally. Every off-line zero
of real part beta forces an exponent at least 2 beta - 1.
Subpower control of the absolute model makes the residual exponent equal
to both actual energy exponents; this model estimate remains Open.
Zero exponent implies RH, but no arithmetic zero-exponent bound is proved.

Source: user-provided annular record, Section 13.5, continued using the
proved actual Mellin and cofinal-growth dependencies. NIST DLMF 2.5(i),
https://dlmf.nist.gov/2.5, supports the Mellin background only.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.RH.AnnularEnergyGrowth
open RiemannResearch.Analysis.LogarithmicGrowth
open RiemannResearch.Analysis.SignedLatticeEnergy
open RiemannResearch.RH.AnnularPrimePair
open RiemannResearch.RH.AnnularCriticalEnergy
open RiemannResearch.RH.AnnularSubpowerEnergy

/-- The full centered and lattice identities, before any estimate. -/
theorem actualPrime_energy_eq_complete_residual (X : ℝ) :
    criticalEnergy actualPrimeSignal X = actualModel X + actualResidual X +
      signedCorrectionCutoff actualCentered actualLatticeCorrection X := by
  rw [actualPrimeSignal_energy_eq_signedCorrection,
    actualIntegralEnergy_eq_model_add_residual]

theorem actualPrimeSubpowerEnergy_iff_subpower :
    ActualPrimeSubpowerEnergy ↔ SubpowerUpperBound (criticalEnergy actualPrimeSignal) := by
  constructor
  · intro h p hp
    obtain ⟨C, X₀, hC⟩ := h p hp
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop X₀] with X hX hX₀
    exact hC X hX hX₀
  · intro h p hp
    obtain ⟨C, hC⟩ := h p hp
    obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hC
    exact ⟨C, X₀, fun X _ hX => hX₀ X hX⟩

theorem actualPrimeSubpowerEnergy_iff_growthExponent_zero :
    ActualPrimeSubpowerEnergy ↔ exponent (criticalEnergy actualPrimeSignal) = 0 :=
  actualPrimeSubpowerEnergy_iff_subpower.trans
    (subpower_iff_exponent_zero (criticalEnergy actualPrimeSignal))

/-- This preserves the complete signed correction, rather than assuming it
vanishes or discarding its cross term. -/
theorem actualPrime_growthExponent_eq_centered :
    exponent (criticalEnergy actualPrimeSignal) = exponent actualIntegralEnergy := by
  apply exponent_eq_of_subpower_difference
  apply subpower_of_eventually_bounded
  exact Eventually.of_forall actualPrimeSignal_energy_difference_abs_le

theorem actualCenteredSubpowerEnergy_iff_growthExponent_zero :
    ActualCenteredSubpowerEnergy ↔ exponent actualIntegralEnergy = 0 := by
  rw [← actualPrimeSubpowerEnergy_iff_actualCenteredSubpowerEnergy,
    actualPrimeSubpowerEnergy_iff_growthExponent_zero,
    actualPrime_growthExponent_eq_centered]

/-- An actual arithmetic zero-exponent hypothesis suffices; no model or
independent local identity premise is used. -/
theorem riemannHypothesis_of_actualPrime_growthExponent_zero
    (h : exponent (criticalEnergy actualPrimeSignal) = 0) : RiemannHypothesis :=
  riemannHypothesis_of_actualPrimeSubpowerEnergy
    (actualPrimeSubpowerEnergy_iff_growthExponent_zero.mpr h)

/-- The paper's limsup obstruction, with no simplicity assumption and no
claim of a pointwise lower bound at every cutoff. -/
theorem actualPrime_growthExponent_ge_of_zero {z : ℂ}
    (hz1 : z.re < 1) (hzero : riemannZeta z = 0) :
    ((2 * z.re - 1 : ℝ) : EReal) ≤ exponent (criticalEnergy actualPrimeSignal) := by
  apply exponent_ge_of_cofinal_power
  intro p hp hpz X₀
  simpa only [one_mul] using
    actualPrime_energy_cofinal_growth_of_zero hz1 hzero hp hpz 1 X₀

/-- Any proved exponent bound gives its precise zero-free threshold. -/
theorem zeta_ne_zero_of_actualPrime_growthExponent_bound {q : ℝ} {z : ℂ}
    (hbound : exponent (criticalEnergy actualPrimeSignal) ≤ (q : EReal))
    (hz1 : z.re < 1) (hqz : q < 2 * z.re - 1) :
    riemannZeta z ≠ 0 := by
  intro hzero
  have hle := (actualPrime_growthExponent_ge_of_zero hz1 hzero).trans hbound
  exact (not_le_of_gt hqz) (by exact_mod_cast hle)

theorem actualCentered_growthExponent_ge_of_zero {z : ℂ}
    (hz1 : z.re < 1) (hzero : riemannZeta z = 0) :
    ((2 * z.re - 1 : ℝ) : EReal) ≤ exponent actualIntegralEnergy := by
  rw [← actualPrime_growthExponent_eq_centered]
  exact actualPrime_growthExponent_ge_of_zero hz1 hzero

/-- Only the model's absolute subpower bound is needed for the exponent
transfer. This remains a substantive arithmetic premise. -/
theorem actualCentered_growthExponent_eq_residual
    (hmodel : SubpowerUpperBound (fun X => |actualModel X|)) :
    exponent actualIntegralEnergy = exponent actualResidual := by
  apply exponent_eq_of_subpower_difference
  simpa only [actualIntegralEnergy_eq_model_add_residual, add_sub_cancel_right] using hmodel

theorem actualModel_subpower_of_log_bound (hmodel : ActualModelLogBound) :
    SubpowerUpperBound (fun X => |actualModel X|) := by
  obtain ⟨B, hB⟩ := hmodel
  apply subpower_of_eventual_log_bound
  exact (eventually_ge_atTop (2 : ℝ)).mono (fun X hX => hB X hX)

theorem actualResidual_subpower_iff_primeSubpower
    (hmodel : SubpowerUpperBound (fun X => |actualModel X|)) :
    SubpowerUpperBound actualResidual ↔ ActualPrimeSubpowerEnergy := by
  rw [subpower_iff_exponent_zero, actualPrimeSubpowerEnergy_iff_growthExponent_zero,
    actualPrime_growthExponent_eq_centered, actualCentered_growthExponent_eq_residual hmodel]

/-- Conditional research reduction: both actual subpower estimates are Open.
All signed prime-pair terms of the original residual are retained. -/
theorem riemannHypothesis_of_actualResidual_subpower
    (hmodel : SubpowerUpperBound (fun X => |actualModel X|))
    (hresidual : SubpowerUpperBound actualResidual) : RiemannHypothesis :=
  riemannHypothesis_of_actualPrimeSubpowerEnergy
    ((actualResidual_subpower_iff_primeSubpower hmodel).mp hresidual)

theorem actualResidual_growthExponent_ge_of_zero
    (hmodel : SubpowerUpperBound (fun X => |actualModel X|))
    {z : ℂ} (hz1 : z.re < 1) (hzero : riemannZeta z = 0) :
    ((2 * z.re - 1 : ℝ) : EReal) ≤ exponent actualResidual := by
  rw [← actualCentered_growthExponent_eq_residual hmodel]
  exact actualCentered_growthExponent_ge_of_zero hz1 hzero

/-- Unconditional finite-prefix envelope from the actual coefficient bound,
not an estimate of the signed prime-pair cancellation. -/
theorem actualCentered_energy_le_log_envelope {X : ℝ} (hX : 1 ≤ X) :
    actualIntegralEnergy X ≤ (7 / 24 : ℝ) ^ 2 * X * (1 + Real.log X) ^ 2 := by
  let K : ℝ := (7 / 24 : ℝ) ^ 2 * (1 + Real.log X) ^ 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hconst : IntegrableOn (fun _x : ℝ => K) (Icc (1 : ℝ) X) :=
    continuousOn_const.integrableOn_Icc
  have hbound : actualIntegralEnergy X ≤ ∫ x in Icc (1 : ℝ) X, K := by
    apply integral_mono_ae (actualEnergyDensity_integrableOn X) hconst
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hx0 : 0 < x := zero_lt_one.trans_le hx.1
    have hlog : Real.log x ≤ Real.log X := Real.log_le_log hx0 hx.2
    have hU : |actualCentered x| ≤ (7 / 24 : ℝ) * x * (1 + Real.log X) :=
      (actualCentered_growth hx.1).trans
        (mul_le_mul_of_nonneg_left (by linarith : 1 + Real.log x ≤ 1 + Real.log X)
          (by positivity))
    have hZ : 0 ≤ (7 / 24 : ℝ) * x * (1 + Real.log X) := by
      have hlogX := Real.log_nonneg hX
      positivity
    have hsquare : actualCentered x ^ 2 ≤
        ((7 / 24 : ℝ) * x * (1 + Real.log X)) ^ 2 := by
      have hs := mul_le_mul hU hU (abs_nonneg _) hZ
      simpa only [← pow_two, sq_abs] using hs
    apply (div_le_iff₀ (sq_pos_of_pos hx0)).2
    dsimp [K]
    nlinarith [hsquare]
  calc
    actualIntegralEnergy X ≤ ∫ x in Icc (1 : ℝ) X, K := hbound
    _ = (X - 1) * K := by
      simp [sub_nonneg.mpr hX]
    _ ≤ X * K := by nlinarith
    _ = _ := by dsimp [K]; ring

theorem actualCentered_power_bound_of_one_lt {p : ℝ} (hp : 1 < p) :
    PowerUpperBound actualIntegralEnergy p := by
  let δ : ℝ := (p - 1) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let C : ℝ := (7 / 24 : ℝ) ^ 2 * (1 + 1 / δ) ^ 2
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  have hX0 : 0 < X := zero_lt_one.trans_le hX
  have hL : 0 ≤ 1 + Real.log X := by linarith [Real.log_nonneg hX]
  have hP : 0 ≤ (1 + 1 / δ) * X ^ δ := by positivity
  have hLbound : 1 + Real.log X ≤ (1 + 1 / δ) * X ^ δ := by
    have hone := Real.one_le_rpow hX hδ.le
    have hlog := Real.log_le_rpow_div hX0.le hδ
    calc
      1 + Real.log X ≤ X ^ δ + X ^ δ / δ := add_le_add hone hlog
      _ = (1 + 1 / δ) * X ^ δ := by ring
  have hs := mul_le_mul hLbound hLbound hL hP
  have hsquare : (1 + Real.log X) ^ 2 ≤ ((1 + 1 / δ) * X ^ δ) ^ 2 := by
    simpa only [← pow_two] using hs
  have hxp : X * (X ^ δ) ^ 2 = X ^ p := by
    calc
      X * (X ^ δ) ^ 2 = X ^ (1 : ℝ) * (X ^ δ * X ^ δ) := by
        rw [Real.rpow_one, pow_two]
      _ = X ^ (1 + (δ + δ)) := by rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
      _ = X ^ p := by congr 1; dsimp [δ]; ring
  calc
    actualIntegralEnergy X ≤ (7 / 24 : ℝ) ^ 2 * X * (1 + Real.log X) ^ 2 :=
      actualCentered_energy_le_log_envelope hX
    _ ≤ (7 / 24 : ℝ) ^ 2 * X * ((1 + 1 / δ) * X ^ δ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ = C * X ^ p := by
      dsimp [C]
      calc
        _ = (7 / 24 : ℝ) ^ 2 * (1 + 1 / δ) ^ 2 * (X * (X ^ δ) ^ 2) := by ring
        _ = _ := by rw [hxp]

/-- The actual limsup is finite, so no boundedness assumption is hidden in
the growth statistic or the zero obstruction. -/
theorem actualPrime_growthExponent_mem_Icc :
    exponent (criticalEnergy actualPrimeSignal) ∈ Icc (0 : EReal) 1 := by
  refine ⟨exponent_nonneg _, ?_⟩
  rw [actualPrime_growthExponent_eq_centered]
  by_contra hn
  have hlt : (1 : EReal) < exponent actualIntegralEnergy := lt_of_not_ge hn
  obtain ⟨p, hp, hpE⟩ := EReal.exists_between_coe_real hlt
  have hp' : 1 < p := by exact_mod_cast hp
  exact (not_le_of_gt hpE) (exponent_le_of_power (by linarith : 0 ≤ p)
    (actualCentered_power_bound_of_one_lt hp'))

end RiemannResearch.RH.AnnularEnergyGrowth
