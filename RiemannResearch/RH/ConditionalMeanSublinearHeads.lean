import RiemannResearch.RH.CanonicalMobiusPNT
import RiemannResearch.RH.ConditionalMeanEndpointEquivalences
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Unconditional sublinear conditional energy and its logarithmic gap

Source: the user's November 13, 2026 request to establish an RH
equivalence. The arithmetic input is the existing PNT-backed theorem
`canonicalMobiusHilbert_sublinear`. The actual weighted Cesaro contraction
transfers it to the complete conditional energy, and mean repair preserves
the rate. No unproved arithmetic or RH premise is introduced.

The result is `E(F_Y) = o(Y)`, not subpolynomial energy. The scalar power
example below proves that this growth bound alone cannot imply the
logarithmic criterion. It is not asserted to be a legal residue energy.
No mathematical novelty is claimed for these consequences.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis.Cesaro

/-- Contraction controls the complete energy of the actual finite witness. -/
theorem canonicalMobiusHead_energy_le_full_norm_sq (N : ℕ) :
    conditionalMeanSquare (canonicalMobiusHead N) ≤ ‖canonicalMobiusHilbert N‖ ^ 2 := by
  have he := cesaroOperator_norm_sq_eq_conditionalMeanSquare (canonicalMobiusHilbert N)
  simp only [canonicalMobiusHilbert_sequence] at he
  rw [← he]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (hilbertCesaro_norm_le (canonicalMobiusHilbert N))

/-- PNT yields sublinear conditional energy without an RH hypothesis. -/
theorem canonicalMobiusHead_energy_sublinear :
    Tendsto (fun N => conditionalMeanSquare (canonicalMobiusHead N) / (N : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero
    (fun N => div_nonneg (conditionalMeanSquare_nonneg _) (Nat.cast_nonneg N))
    (fun N => div_le_div_of_nonneg_right (canonicalMobiusHead_energy_le_full_norm_sq N)
      (Nat.cast_nonneg N))
    canonicalMobiusHilbert_sublinear

/-- The actual unrestricted infimum is sublinear in the head length. -/
theorem conditionalHeadMinimum_sublinear :
    Tendsto (fun N => conditionalHeadMinimum N / (N : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun N => div_nonneg (conditionalHeadMinimum_nonneg N) (Nat.cast_nonneg N))
    (fun N => div_le_div_of_nonneg_right
      (conditionalHeadMinimum_le N (canonicalMobiusHead_mem_class N))
      (Nat.cast_nonneg N))
    canonicalMobiusHead_energy_sublinear

/-- The zero-period-mean restriction preserves the unconditional rate. -/
theorem zeroMeanConditionalHeadMinimum_sublinear :
    Tendsto (fun N => zeroMeanConditionalHeadMinimum N / (N : ℝ)) atTop (𝓝 0) := by
  simpa only [zeroMeanConditionalHeadMinimum_eq] using conditionalHeadMinimum_sublinear

/-- Genuine finite exact heads with zero period mean and sublinear full energy. -/
theorem exists_zeroMean_conditionalHeads_sublinear :
    ∃ F : ℕ → ℕ → ℝ,
      (∀ N, F N ∈ zeroMeanConditionalHeadClass N) ∧
      Tendsto (fun N => conditionalMeanSquare (F N) / (N : ℝ)) atTop (𝓝 0) := by
  choose F hF hE using fun N =>
    exists_zeroMean_conditionalHead_near N (canonicalMobiusHead_mem_class N) 1 (by norm_num)
  refine ⟨F, hF, ?_⟩
  have hu : Tendsto
      (fun N => conditionalMeanSquare (canonicalMobiusHead N) / (N : ℝ) + 1 / (N : ℝ))
      atTop (𝓝 0) := by
    simpa using canonicalMobiusHead_energy_sublinear.add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply squeeze_zero
    (fun N => div_nonneg (conditionalMeanSquare_nonneg _) (Nat.cast_nonneg N))
    (fun N => ?_) hu
  simpa only [add_div] using
    div_le_div_of_nonneg_right (hE N).le (Nat.cast_nonneg N)


namespace EnergyGrowth

/-- Scalar power growth is sublinear for exponents below one. -/
theorem power_sublinear (α : ℝ) (hα : α < 1) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ α / (N : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 - α))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show -(1 - α) = α - 1 by ring, Real.rpow_sub hpos, Real.rpow_one]

/-- The logarithmic exponent of a scalar power is its positive exponent. -/
theorem power_logarithmic_growth (α : ℝ) (hα : 0 < α) :
    Tendsto (fun N : ℕ => Real.log (1 + (N : ℝ) ^ α) / Real.log (N : ℝ))
      atTop (𝓝 α) := by
  have hden : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => α + Real.log 2 / Real.log (N : ℝ))
      atTop (𝓝 α) := by
    simpa using (tendsto_const_nhds (x := α)).add
      ((tendsto_const_nhds (x := Real.log 2)).div_atTop hden)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := α)) hu
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hp : (0 : ℝ) < N := by linarith
    have hl : 0 < Real.log (N : ℝ) := Real.log_pos hn
    have hr : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hp α
    have hx : Real.log ((N : ℝ) ^ α) ≤ Real.log (1 + (N : ℝ) ^ α) :=
      Real.log_le_log hr (by linarith)
    rw [Real.log_rpow hp] at hx
    exact (le_div_iff₀ hl).mpr hx
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hp : (0 : ℝ) < N := by linarith
    have hl : 0 < Real.log (N : ℝ) := Real.log_pos hn
    have hr : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hp α
    have hone : 1 ≤ (N : ℝ) ^ α := Real.one_le_rpow hn.le hα.le
    have hx : Real.log (1 + (N : ℝ) ^ α) ≤ Real.log (2 * (N : ℝ) ^ α) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hr.ne', Real.log_rpow hp] at hx
    calc
      _ ≤ (Real.log 2 + α * Real.log (N : ℝ)) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right hx hl.le
      _ = _ := by field_simp; ring

/-- This scalar counterexample has no claim of finite residue legality.
It rules out upgrading sublinearity to the logarithmic criterion by
growth estimates alone. -/
theorem sublinear_not_logarithmic :
    ∃ e : ℕ → ℝ, (∀ N, 0 ≤ e N) ∧
      Tendsto (fun N => e N / (N : ℝ)) atTop (𝓝 0) ∧
      ¬ Tendsto (fun N => Real.log (1 + e N) / Real.log (N : ℝ)) atTop (𝓝 0) := by
  refine ⟨fun N => (N : ℝ) ^ (1 / 2 : ℝ),
    fun N => Real.rpow_nonneg (Nat.cast_nonneg N) _, power_sublinear _ (by norm_num), ?_⟩
  intro h
  have he := tendsto_nhds_unique (power_logarithmic_growth (1 / 2) (by norm_num)) h
  norm_num at he

end EnergyGrowth
end RiemannResearch.RH.Pareto

/-- info: 'RiemannResearch.RH.Pareto.canonicalMobiusHead_energy_sublinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.canonicalMobiusHead_energy_sublinear

/-- info: 'RiemannResearch.RH.Pareto.conditionalHeadMinimum_sublinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.conditionalHeadMinimum_sublinear

/-- info: 'RiemannResearch.RH.Pareto.zeroMeanConditionalHeadMinimum_sublinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.zeroMeanConditionalHeadMinimum_sublinear

/-- info: 'RiemannResearch.RH.Pareto.exists_zeroMean_conditionalHeads_sublinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.exists_zeroMean_conditionalHeads_sublinear

/-- info: 'RiemannResearch.RH.Pareto.EnergyGrowth.power_logarithmic_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.EnergyGrowth.power_logarithmic_growth

/-- info: 'RiemannResearch.RH.Pareto.EnergyGrowth.sublinear_not_logarithmic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RiemannResearch.RH.Pareto.EnergyGrowth.sublinear_not_logarithmic
