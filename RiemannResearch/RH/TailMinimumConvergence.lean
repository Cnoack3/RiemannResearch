import RiemannResearch.RH.CanonicalTailCapacityGeometry

/-!
# Strong convergence of the actual finite tail certificates

Source: user-provided argument,
`RH_Obstruction_Compact_Frequency_Rigidity_2026-09-21.md`, Section 2,
for the uniform-capacity criterion and quantitative error bound.
The finite Pythagorean identity and canonical convergence are already provided
by `ParetoTailCapacityDuality` and `CanonicalTailCapacityGeometry`.
No uniform arithmetic bound or RH-to-density provider is asserted here.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.ExhaustiveWalk

private theorem pointDualResidual_ne_zero_of_uniform_capacity
    {B : ℝ} (hB : ∀ n : ℕ, tailCapacity n ≤ B) :
    pointDualResidual ≠ 0 := by
  intro hz
  have hp : paretoPointHilbert 0 =
      closedSpace.starProjection (paretoPointHilbert 0) := sub_eq_zero.mp hz
  have he : paretoPointHilbert 0 ∈ closedSpace :=
    hp.symm ▸ closedSpace.starProjection_apply_mem (paretoPointHilbert 0)
  have herr : Tendsto pointError atTop (𝓝 0) :=
    (walkError_tendsto_zero_iff residueAtom id Function.surjective_id
      (paretoPointHilbert 0)).mpr he
  have ht := tailCapacity_tendsto_iff.mpr herr
  have hev : ∀ᶠ n in atTop, B + 1 ≤ tailCapacity n :=
    (tendsto_atTop.1 ht) (B + 1)
  obtain ⟨n, hn⟩ := eventually_atTop.1 hev
  linarith [hn n le_rfl, hB n]

/-- Any strong limit bounds every finite minimum energy from above. -/
theorem tailCapacity_le_strong_limit_energy {z : ThresholdHilbert}
    (hz : Tendsto tailMinimum atTop (𝓝 z)) (n : ℕ) :
    tailCapacity n ≤ ‖z‖ ^ 2 := by
  have ht : Tendsto tailCapacity atTop (𝓝 (‖z‖ ^ 2)) := by
    simpa only [tailMinimum_norm_sq] using hz.norm.pow 2
  apply ge_of_tendsto ht
  filter_upwards [eventually_ge_atTop n] with m hm
  exact tailCapacity_monotone hm

/-- Convergence of the actual finite minimum vectors is equivalent to the
uniform capacity bound; this does not assert that either condition holds. -/
theorem tailMinimum_converges_iff_capacity_bounded :
    (∃ z : ThresholdHilbert, Tendsto tailMinimum atTop (𝓝 z)) ↔
      ∃ B : ℝ, ∀ n : ℕ, tailCapacity n ≤ B := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨‖z‖ ^ 2, tailCapacity_le_strong_limit_energy hz⟩
  · rintro ⟨B, hB⟩
    exact ⟨canonicalTailCertificate,
      tailMinimum_tendsto_canonical
        (pointDualResidual_ne_zero_of_uniform_capacity hB)⟩

/-- Every strong limit is the actual canonical certificate, rather than an
unspecified weakly selected subsequential limit. -/
theorem tailMinimum_strong_limit_eq_canonical {z : ThresholdHilbert}
    (hz : Tendsto tailMinimum atTop (𝓝 z)) :
    z = canonicalTailCertificate := by
  have hr := pointDualResidual_ne_zero_of_uniform_capacity
    (tailCapacity_le_strong_limit_energy hz)
  exact tendsto_nhds_unique hz (tailMinimum_tendsto_canonical hr)

/-- A supplied uniform upper bound yields the canonical certificate, strong
convergence, and a quantitative squared-distance bound at every finite stage. -/
theorem tailMinimum_uniform_capacity_conclusion {B : ℝ}
    (hB : ∀ n : ℕ, tailCapacity n ≤ B) :
    IsResidueTailCertificate canonicalTailCertificate ∧
      Tendsto tailMinimum atTop (𝓝 canonicalTailCertificate) ∧
      ‖canonicalTailCertificate‖ ^ 2 ≤ B ∧
      ∀ n : ℕ,
        ‖canonicalTailCertificate - tailMinimum n‖ ^ 2 =
          ‖canonicalTailCertificate‖ ^ 2 - tailCapacity n ∧
        ‖canonicalTailCertificate - tailMinimum n‖ ^ 2 ≤ B - tailCapacity n := by
  have hr := pointDualResidual_ne_zero_of_uniform_capacity hB
  have hc := canonicalTailCertificate_isCertificate hr
  have hnorm : ‖canonicalTailCertificate‖ ^ 2 ≤ B :=
    le_of_tendsto (tailCapacity_tendsto_canonical_energy hr)
      (Filter.Eventually.of_forall hB)
  refine ⟨hc, tailMinimum_tendsto_canonical hr, hnorm, ?_⟩
  intro n
  have hsplit := tailCertificate_energy_completion canonicalTailCertificate hc n
  constructor <;> linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
