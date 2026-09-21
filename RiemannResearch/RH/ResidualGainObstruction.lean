import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.RHFalseTailConstraints
import RiemannResearch.Analysis.ResidualGainProduct
import RiemannResearch.Analysis.LogarithmicResidualBarrier

/-!
# Exact finite gain budgets under failure of RH

Source: user-provided stringent-condition catalogue, conditions 4 and 14,
2026-09-21. The source supplies the statements and telescoping proof strategy.
The sequences below are the actual residue-span projections and actual
minimum-energy tail certificates. No positive limiting gap is assumed in place
of an arithmetic proof: it is obtained from `¬ RiemannHypothesis` using the
existing RH implication. All summability claims retain the entire gain.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The actual fraction of squared residual energy captured by the next
residue generator. -/
def projectionRelativeGain (n : ℕ) : ℝ :=
  (energy n - energy (n + 1)) / energy n

theorem energy_pos_of_not_RH (hRH : ¬ RiemannHypothesis) (n : ℕ) :
    0 < energy n := by
  rw [energy_eq_limit_add]
  exact add_pos_of_pos_of_nonneg (not_RH_limitEnergy_pos hRH) (sq_nonneg _)

theorem projectionRelativeGain_nonneg (n : ℕ) :
    0 ≤ projectionRelativeGain n := by
  apply div_nonneg
  · exact sub_nonneg.mpr (energy_antitone (Nat.le_succ n))
  · exact sq_nonneg _

theorem projectionRelativeGain_lt_one_of_not_RH
    (hRH : ¬ RiemannHypothesis) (n : ℕ) :
    projectionRelativeGain n < 1 := by
  apply (div_lt_one (energy_pos_of_not_RH hRH n)).mpr
  linarith [energy_pos_of_not_RH hRH (n + 1)]

theorem energy_relativeGain_recurrence (hRH : ¬ RiemannHypothesis) (n : ℕ) :
    energy (n + 1) = energy n * (1 - projectionRelativeGain n) := by
  unfold projectionRelativeGain
  field_simp [ne_of_gt (energy_pos_of_not_RH hRH n)]
  ring

/-- Under failure of RH the entire actual relative-gain sequence is summable.
This is stronger than merely refuting one proposed harmonic lower bound. -/
theorem not_RH_projectionRelativeGain_summable (hRH : ¬ RiemannHypothesis) :
    Summable projectionRelativeGain := by
  by_contra hs
  have hz : Tendsto energy atTop (𝓝 0) :=
    (RiemannResearch.Analysis.ResidualGain.residual_tendsto_zero_iff_not_summable
      (energy_pos_of_not_RH hRH 0) projectionRelativeGain_nonneg
      (projectionRelativeGain_lt_one_of_not_RH hRH)
      (energy_relativeGain_recurrence hRH)).mpr hs
  have he : limitEnergy = 0 := tendsto_nhds_unique energy_tendsto hz
  exact (ne_of_gt (not_RH_limitEnergy_pos hRH)) he

/-- Exact logarithmic budget, including all infinitely many gains. -/
theorem not_RH_logarithmic_gain_hasSum (hRH : ¬ RiemannHypothesis) :
    HasSum (fun n => -Real.log (1 - projectionRelativeGain n))
      (Real.log (energy 0 / limitEnergy)) := by
  have hs :=
    (RiemannResearch.Analysis.ResidualGain.summable_neg_log_one_sub_iff
      projectionRelativeGain_nonneg
      (projectionRelativeGain_lt_one_of_not_RH hRH)).mpr
        (not_RH_projectionRelativeGain_summable hRH)
  have hlim : Tendsto (fun n => Real.log (energy 0 / energy n)) atTop
      (𝓝 (Real.log (energy 0 / limitEnergy))) :=
    (Real.continuousAt_log (ne_of_gt
      (div_pos (energy_pos_of_not_RH hRH 0) (not_RH_limitEnergy_pos hRH)))).tendsto.comp
        (tendsto_const_nhds.div energy_tendsto
          (ne_of_gt (not_RH_limitEnergy_pos hRH)))
  have he (N : ℕ) :
      (∑ n ∈ Finset.range N, -Real.log (1 - projectionRelativeGain n)) =
        Real.log (energy 0 / energy N) :=
    RiemannResearch.Analysis.LogarithmicResidualBarrier.log_gain_telescope
      energy (energy_pos_of_not_RH hRH) N
  have ht : Tendsto (fun N =>
      ∑ n ∈ Finset.range N, -Real.log (1 - projectionRelativeGain n)) atTop
      (𝓝 (Real.log (energy 0 / limitEnergy))) := by
    simpa only [he] using hlim
  have htotal := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat ht
  exact htotal ▸ hs.hasSum

/-- The sum of relative gains has the exact logarithmic budget as an upper
bound; its finiteness does not force termination at any finite stage. -/
theorem not_RH_relativeGain_tsum_le_log_budget (hRH : ¬ RiemannHypothesis) :
    (∑' n, projectionRelativeGain n) ≤ Real.log (energy 0 / limitEnergy) := by
  have hg := not_RH_projectionRelativeGain_summable hRH
  have hl := not_RH_logarithmic_gain_hasSum hRH
  rw [← hl.tsum_eq]
  exact Summable.tsum_le_tsum
    (fun n => RiemannResearch.Analysis.ResidualGain.gain_le_neg_log_one_sub
      (projectionRelativeGain_lt_one_of_not_RH hRH n)) hg hl.summable

/-- Scales with gain at least `c/(n+1)` have finite harmonic mass. -/
theorem not_RH_harmonic_gain_scales (hRH : ¬ RiemannHypothesis)
    (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℕ =>
      if c / ((n : ℝ) + 1) ≤ projectionRelativeGain n
      then 1 / ((n : ℝ) + 1) else 0) := by
  apply Summable.of_nonneg_of_le
    (fun n => by split_ifs <;> positivity)
    (fun n => ?_)
    ((not_RH_projectionRelativeGain_summable hRH).div_const c)
  split_ifs with hn
  · apply (le_div_iff₀ hc).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hn
  · exact div_nonneg (projectionRelativeGain_nonneg n) hc.le

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

/-- The complete sequence of capacity improvements is summable with its
exact endpoint. This packages the previous partial-sum limit as `HasSum`. -/
theorem not_RH_capacity_gain_hasSum (hRH : ¬ RiemannHypothesis) :
    HasSum (fun n => tailCapacity (n + 1) - tailCapacity n)
      (‖canonicalTailCertificate‖ ^ 2 - tailCapacity 0) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => sub_nonneg.mpr (tailCapacity_monotone (Nat.le_succ n)))
    (‖canonicalTailCertificate‖ ^ 2 - tailCapacity 0)).mpr
  exact not_RH_accumulated_capacity_gain hRH

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
