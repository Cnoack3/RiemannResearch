import RiemannResearch.RH.CenteredMeanDigammaSection
import RiemannResearch.RH.ScreenedParityNegativeMass

/-!
# Negative mass of the original digamma mean ladder

The finite section is the original mean-one packet optimizer.  Its coordinates
are computed by the digamma Gram recurrence in `CenteredMeanDigammaSection`.
For any physical head tending to infinity, the finite Pareto-weighted negative
mass converges to the complete negative mass of the screened vector.  Hence
vanishing of these entirely finite signed sums is equivalent to RH.

The complete-period negative coordinate already seen at conductor 11 is
retained: no pointwise or stagewise positivity assumption is used.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection

open CoefficientStabilization RamanujanCanonicalOptimizer PacketGramBoundary
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.PrimePowerSchur.ScreenedParityNegativeMass

/-- Finite Pareto negative mass of the original digamma section.  Every term is
an explicit inverse-Gram coordinate obtained from the digamma recurrence. -/
def digammaNegativeMassHead (n K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K,
    paretoWeight k * max (-sectionCoordinate (n + 1) (k + 1)) 0

/-- Identification with the Hilbert-space head statistic. -/
theorem digammaNegativeMassHead_eq (n K : ℕ) :
    digammaNegativeMassHead n K = negativeMassHead K (packetUnitMean n) := by
  rw [digammaNegativeMassHead, negativeMassHead_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [sectionCoordinate_eq]

/-- Along any growing physical head, the finite digamma negative masses converge
to the complete negative mass of the screened vector.  The omitted Pareto tail
is bounded by the section norm divided by `sqrt (K+1)`. -/
theorem digammaNegativeMassHead_tendsto (K : ℕ → ℕ)
    (hK : Tendsto K atTop atTop) :
    Tendsto (fun n => digammaNegativeMassHead n (K n)) atTop
      (𝓝 (hilbertNegativeMass normalizedScreenedTwo)) := by
  rw [show (fun n => digammaNegativeMassHead n (K n)) =
      (fun n => negativeMassHead (K n) (packetUnitMean n)) by
    funext n
    exact digammaNegativeMassHead_eq n (K n)]
  have hpt : Tendsto packetUnitMean atTop (𝓝 normalizedScreenedTwo) := by
    simpa only [packetUnitMeanLimit_eq_screened] using packetUnitMean_tendsto
  have hm : Tendsto (fun n => hilbertNegativeMass (packetUnitMean n)) atTop
      (𝓝 (hilbertNegativeMass normalizedScreenedTwo)) :=
    hilbertNegativeMass_continuous.continuousAt.tendsto.comp hpt
  have hr : Tendsto (fun n => Real.sqrt (1 / ((K n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hK)
  have hl : Tendsto (fun n => hilbertNegativeMass (packetUnitMean n) -
      ‖packetUnitMean n‖ * Real.sqrt (1 / ((K n : ℝ) + 1))) atTop
      (𝓝 (hilbertNegativeMass normalizedScreenedTwo)) := by
    simpa only [mul_zero, sub_zero] using hm.sub (hpt.norm.mul hr)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hm
    (fun n => by
      linarith only [negativeMassHead_truncation_upper (K n) (packetUnitMean n)])
    (fun n => negativeMassHead_le (K n) (packetUnitMean n))

/-- Exact arithmetic reformulation: for every chosen head growth law, vanishing
of the finite digamma negative mass is equivalent to RH. -/
theorem digammaNegativeMassHead_zero_iff_rh (K : ℕ → ℕ)
    (hK : Tendsto K atTop atTop) :
    Tendsto (fun n => digammaNegativeMassHead n (K n)) atTop (𝓝 0) ↔
      RiemannHypothesis := by
  have ht := digammaNegativeMassHead_tendsto K hK
  constructor
  · intro hz
    exact screened_negativeMass_zero_iff_rh.mp (tendsto_nhds_unique ht hz)
  · intro h
    rw [screened_negativeMass_zero_iff_rh.mpr h] at ht
    exact ht

/-- A single concrete obligation: take the same index for the conductor stage
and the physical head. -/
theorem digammaDiagonalNegativeMass_zero_iff_rh :
    Tendsto (fun n => digammaNegativeMassHead n n) atTop (𝓝 0) ↔
      RiemannHypothesis := by
  simpa only using digammaNegativeMassHead_zero_iff_rh (fun n : ℕ => n) tendsto_id

#print axioms digammaNegativeMassHead_eq
#print axioms digammaNegativeMassHead_tendsto
#print axioms digammaNegativeMassHead_zero_iff_rh
#print axioms digammaDiagonalNegativeMass_zero_iff_rh

end RiemannResearch.RH.Pareto.PrimePowerSchur.CenteredMeanSnake.DigammaSection
