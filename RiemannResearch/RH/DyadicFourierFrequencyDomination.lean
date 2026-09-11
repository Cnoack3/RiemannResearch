import RiemannResearch.RH.DyadicFourierZeroDamping
import RiemannResearch.RH.DyadicSignedBoundaryTightness
import RiemannResearch.RH.DyadicTentFourierSummability
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Frequency domination for the actual signed arithmetic row

Source: independently developed continuation of the user-provided
`FourierSignedBridgeVerification20260911(2).md`. The unconditional moment
estimate uses the previously proved actual inverse-square tent-coefficient
bound and Mathlib's integer p-series theorem. The limiting argument uses
Mathlib's Tannery theorem (dominated convergence for sums).

The square-root multiplier estimate below is an explicit open analytic
obligation. It is not asserted here. If supplied, it permits passage from the
unconditional fixed-frequency limits to the actual boundary-coordinate limit.
The resulting coordinate limit alone gives no uniform boundary-energy bound.
-/

namespace RiemannResearch.RH.Pareto
open Filter
open scoped BigOperators
noncomputable section

/-- Actual tent coefficients have a half-order frequency moment, for each
fixed boundary coordinate. The constant in inverse-square decay depends on `i`. -/
theorem summable_norm_dyadicTentMellinCoefficient_mul_half_rpow (i : ℕ) :
    Summable (fun h : ℤ =>
      ‖dyadicTentMellinCoefficient i h‖ * |(h : ℝ)| ^ (1 / 2 : ℝ)) := by
  let K : ℝ := 4 * (2 * (i + 1) + 1 : ℝ) * Real.log 2 / (2 * Real.pi) ^ 2
  have hp : Summable (fun h : ℤ => |(h : ℝ)| ^ (-(3 / 2 : ℝ))) :=
    Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 3 / 2)
  apply (hp.mul_left K).of_norm_bounded
  intro h
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hh : h = 0
  · subst h
    simp
  · have hcast : (h : ℝ) ≠ 0 := by exact_mod_cast hh
    have habs : 0 < |(h : ℝ)| := abs_pos.mpr hcast
    calc
      _ ≤ (K / (h : ℝ) ^ 2) * |(h : ℝ)| ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (norm_dyadicTentMellinCoefficient_le_inv_sq i hh) (by positivity)
      _ = K * |(h : ℝ)| ^ (-(3 / 2 : ℝ)) := by
        have hsquare : (h : ℝ) ^ 2 = |(h : ℝ)| ^ (2 : ℝ) := by
          rw [Real.rpow_two, sq_abs]
        rw [hsquare, div_eq_mul_inv, mul_assoc,
          ← Real.rpow_neg (le_of_lt habs), ← Real.rpow_add habs]
        norm_num

/-- Restriction of the unconditional half-order moment to the actual nonzero
frequency domain used by the full signed arithmetic bridge. -/
theorem summable_norm_dyadicTentMellinCoefficient_nonzero_mul_half_rpow (i : ℕ) :
    Summable (fun h : DyadicNonzeroFourierFrequency =>
      ‖dyadicTentMellinCoefficient i h.1‖ * |(h.1 : ℝ)| ^ (1 / 2 : ℝ)) := by
  exact (summable_norm_dyadicTentMellinCoefficient_mul_half_rpow i).comp_injective
    Subtype.val_injective

/-- Open sufficient frequency-tail bound, uniform in small positive damping.
The entire signed zeta ratio and Abel numerator remain in the multiplier. -/
def DyadicUniformSignedFourierMultiplierSqrtBound : Prop :=
  ∃ B : ℝ, 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    ∀ h : DyadicNonzeroFourierFrequency,
      ‖dyadicSignedFourierMultiplier ε h‖ ≤ B * |(h.1 : ℝ)| ^ (1 / 2 : ℝ)

/-- The proposed uniform multiplier growth controls an absolutely summable
majorant for each fixed-coordinate signed Fourier row. This is a conditional
research reduction: the growth bound remains an explicit hypothesis. -/
theorem dyadicSignedFourierTerm_eventually_norm_le_of_sqrt_bound
    (hbound : DyadicUniformSignedFourierMultiplierSqrtBound) (i : ℕ) :
    ∃ b : DyadicNonzeroFourierFrequency → ℝ, Summable b ∧
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ∀ h, ‖dyadicSignedFourierTerm ε i h‖ ≤ b h := by
  rcases hbound with ⟨B, _, hB⟩
  refine ⟨fun h =>
    (‖dyadicTentMellinCoefficient i h.1‖ * |(h.1 : ℝ)| ^ (1 / 2 : ℝ)) * B,
    (summable_norm_dyadicTentMellinCoefficient_nonzero_mul_half_rpow i).mul_right B, ?_⟩
  have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    eventually_mem_nhdsWithin
  have hhalf : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono inf_le_left
  filter_upwards [hpos, hhalf] with ε hε hεhalf h
  rw [dyadicSignedFourierTerm, norm_mul]
  calc
    _ ≤ ‖dyadicTentMellinCoefficient i h.1‖ *
        (B * |(h.1 : ℝ)| ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hB ε hε hεhalf.le h) (norm_nonneg _)
    _ = _ := by ring

/-- Conditional justified passage through the complete signed frequency sum.
Every complex sign and mixed frequency contribution remains in the sum. -/
theorem dyadicSignedFourierRow_tendsto_zero_of_sqrt_bound
    (hbound : DyadicUniformSignedFourierMultiplierSqrtBound) (i : ℕ) :
    Tendsto (fun ε : ℝ => ∑' h, dyadicSignedFourierTerm ε i h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℂ)) := by
  rcases dyadicSignedFourierTerm_eventually_norm_le_of_sqrt_bound hbound i with
    ⟨b, hb, hmajor⟩
  simpa only [tsum_zero] using
    (tendsto_tsum_of_dominated_convergence hb
      (fun h => dyadicSignedFourierTerm_tendsto_zero i h) hmajor)

/-- Under the explicitly open frequency growth bound, the actual arithmetic
boundary coordinate tends to zero. The actual full Fourier bridge is proved. -/
theorem dyadicNormalizationBoundaryCoefficient_tendsto_zero_of_sqrt_bound
    (hbound : DyadicUniformSignedFourierMultiplierSqrtBound) (i : ℕ) :
    Tendsto (fun ε : ℝ => dyadicNormalizationBoundaryCoefficient ε i)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
  have heq : (fun ε : ℝ =>
      (∑' h, dyadicSignedFourierTerm ε i h).re) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun ε => dyadicNormalizationBoundaryCoefficient ε i) := by
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    rw [(dyadicSignedFourierBridge_proved ε hε i).tsum_eq]
    simp
  simpa only [Complex.zero_re] using
    ((Complex.continuous_re.tendsto 0).comp
      (dyadicSignedFourierRow_tendsto_zero_of_sqrt_bound hbound i)).congr' heq


/-- With the frequency-growth provider supplied, the remaining condition for
strong actual energy decay is exactly tightness in the boundary index.
Both the frequency-growth provider and this tail control remain open. -/
theorem dyadicNormalizationRemainder_energy_tendsto_zero_iff_tail_tight_of_sqrt_bound
    (hbound : DyadicUniformSignedFourierMultiplierSqrtBound) :
    Tendsto (fun ε : ℝ => ‖dyadicNormalizationRemainder ε‖ ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ↔
      RiemannResearch.Analysis.NonnegativeSeriesTailTightAt
        dyadicSignedFourierBoundaryEnergy (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  exact dyadicNormalizationRemainder_energy_tendsto_zero_iff_tail_tight
    (fun ε : ℝ => ε) eventually_mem_nhdsWithin
    (dyadicNormalizationBoundaryCoefficient_tendsto_zero_of_sqrt_bound hbound)

end
end RiemannResearch.RH.Pareto
