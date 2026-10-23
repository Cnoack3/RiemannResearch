import RiemannResearch.RH.RamanujanCoefficientLimits
import RiemannResearch.RH.ResidueSchurLimits
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Cofinal saturation, exact gains, and Ramanujan RH equivalences

Source: user-requested duality program, 23 October 2026.
The full error, inverse packet Gram mass, Mobius multiple-coordinate limits,
gain saturation, and relative-gain divergence are equivalent zero-defect tests.
The first three remain equivalent along every cofinal map on a nontrivial
filter. Exact gains and products retain the limiting error.

Every saturation test implies Mathlib's RiemannHypothesis.
The reverse RH implication explicitly requires the existing, unformalized
Baez-Duarte analytic provider: RH implies NaturalApproximation.
Reference for that classical implication: https://arxiv.org/abs/math/0202141.
No arithmetic saturation assertion is supplied here.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanCanonicalOptimizer
open Pareto Pareto.CoefficientStabilization
open Pareto.CoefficientStabilization.ProjectionSchur

def packetGain (n : ℕ) : ℝ := packetMass (n+1) - packetMass n
def packetRelativeGain (n : ℕ) : ℝ := packetGain n / (1 - packetMass n)

theorem packetMass_eq_captured (n : ℕ) : packetMass n = captured n := by
  rw [← packet_energy, packetCandidate_eq_projection, captured_eq_norm_sq]

theorem packetMass_tendsto :
    Tendsto packetMass atTop (𝓝 (1 - limitEnergy)) := by
  rw [show packetMass = captured from funext packetMass_eq_captured]
  exact captured_tendsto

theorem packetMass_monotone : Monotone packetMass := by
  intro m n hmn
  have h := energy_antitone hmn
  rw [packet_energy_eq_original, packet_energy_eq_original] at h
  linarith

theorem packetMass_bounds (n : ℕ) : 0 ≤ packetMass n ∧ packetMass n < 1 := by
  constructor
  · rw [← packet_energy]
    exact sq_nonneg _
  · have h := finite_energy_pos n
    rw [packet_energy_eq_original] at h
    linarith

theorem packetGain_eq_schur (n : ℕ) :
    packetGain n = (schurEta n)^2 / schurSigma n := by
  unfold packetGain
  rw [packetMass_eq_captured, packetMass_eq_captured, captured_schur_step]
  ring

theorem packetGain_hasSum : HasSum packetGain (1 - limitEnergy) := by
  simpa only [← packetGain_eq_schur] using schur_gain_hasSum

theorem packetRelativeGain_eq (n : ℕ) :
    packetRelativeGain n = projectionRelativeGain n := by
  unfold packetRelativeGain packetGain projectionRelativeGain
  rw [packet_energy_eq_original, packet_energy_eq_original]
  ring

theorem packet_error_product (n : ℕ) :
    1 - packetMass n = ∏ j ∈ Finset.range n, (1 - packetRelativeGain j) := by
  have h := energy_relativeGain_product n
  rw [packet_energy_eq_original, packet_energy_eq_original] at h
  simpa only [← packetRelativeGain_eq, packetMass, Fin.sum_univ_zero,
    sub_zero, one_mul] using h

theorem packetMultipleCoefficient_total_variation (m : ℕ) (hm : 1 < m) :
    Summable (fun n =>
      ‖packetMultipleCoefficient (n+1) m - packetMultipleCoefficient n m‖) := by
  simpa only [packetMultipleCoefficient_eq _ m hm] using
    coefficient_total_variation_summable m

theorem packet_cofinal_mass_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => packetMass (N i)) l (𝓝 1) ↔ limitEnergy = 0 := by
  have ht : Tendsto (fun i => packetMass (N i)) l (𝓝 (1 - limitEnergy)) :=
    packetMass_tendsto.comp hN
  constructor
  · intro h
    have he := tendsto_nhds_unique ht h
    linarith
  · intro h
    simpa only [h, sub_zero] using ht

theorem packet_cofinal_norm_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => ‖hilbertOne - packetCandidate (N i)‖) l (𝓝 0) ↔
      limitEnergy = 0 := by
  have ht : Tendsto (fun i => ‖hilbertOne - packetCandidate (N i)‖) l
      (𝓝 ‖limitResidual‖) := by
    simpa only [Function.comp_def, packetCandidate_eq_projection] using
      projection_norm_error_tendsto.comp hN
  constructor
  · intro h
    exact limitResidual_zero_iff_energy_zero.mp
      (norm_eq_zero.mp (tendsto_nhds_unique ht h))
  · intro h
    have hz := limitResidual_zero_iff_energy_zero.mpr h
    simpa only [hz, norm_zero] using ht

theorem packet_cofinal_coefficients_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    (∀ m : ℕ, 1 < m →
      Tendsto (fun i => packetMultipleCoefficient (N i) m) l
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔ limitEnergy = 0 := by
  constructor
  · intro h
    apply limitResidual_zero_iff_energy_zero.mp
    apply limitCoefficients_eq_mobius_iff_residual_zero.mp
    intro m hm
    exact tendsto_nhds_unique
      ((packetMultipleCoefficient_tendsto m hm).comp hN) (h m hm)
  · intro h m hm
    have hz := limitResidual_zero_iff_energy_zero.mpr h
    have hc := limitCoefficients_eq_mobius_iff_residual_zero.mpr hz m hm
    simpa only [Function.comp_def, hc] using (packetMultipleCoefficient_tendsto m hm).comp hN

theorem packet_gain_saturation_iff :
    (∑' n, packetGain n) = 1 ↔ limitEnergy = 0 := by
  rw [packetGain_hasSum.tsum_eq]
  constructor <;> intro h <;> linarith

theorem packet_relativeGain_not_summable_iff :
    ¬ Summable packetRelativeGain ↔ limitEnergy = 0 := by
  have he : Tendsto energy atTop (𝓝 0) ↔ limitEnergy = 0 := by
    constructor
    · exact fun h => tendsto_nhds_unique energy_tendsto h
    · intro h
      simpa only [h] using energy_tendsto
  rw [show packetRelativeGain = projectionRelativeGain from funext packetRelativeGain_eq]
  exact energy_zero_iff_relativeGain_not_summable.symm.trans he

theorem packet_riemannHypothesis_of_saturation
    (h : Tendsto packetMass atTop (𝓝 1)) : RiemannHypothesis := by
  have he := (packet_cofinal_mass_iff id tendsto_id).mp h
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_mem.mpr (limitEnergy_zero_iff_mem.mp he))

theorem packet_saturation_equivalences :
    (Tendsto packetMass atTop (𝓝 1) ↔
      Tendsto (fun n => ‖hilbertOne - packetCandidate n‖) atTop (𝓝 0)) ∧
    (Tendsto packetMass atTop (𝓝 1) ↔
      ∀ m : ℕ, 1 < m → Tendsto (fun n => packetMultipleCoefficient n m) atTop
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ∧
    (Tendsto packetMass atTop (𝓝 1) ↔ (∑' n, packetGain n) = 1) ∧
    (Tendsto packetMass atTop (𝓝 1) ↔ ¬ Summable packetRelativeGain) := by
  have hm := packet_cofinal_mass_iff id tendsto_id
  exact ⟨hm.trans (packet_cofinal_norm_iff id tendsto_id).symm,
    hm.trans (packet_cofinal_coefficients_iff id tendsto_id).symm,
    hm.trans packet_gain_saturation_iff.symm,
    hm.trans packet_relativeGain_not_summable_iff.symm⟩

theorem packet_cofinal_rh_equivalences
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l] (N : α → ℕ)
    (hN : Tendsto N l atTop) :
    (Tendsto (fun i => packetMass (N i)) l (𝓝 1) ↔ RiemannHypothesis) ∧
    (Tendsto (fun i => ‖hilbertOne - packetCandidate (N i)‖) l (𝓝 0) ↔
      RiemannHypothesis) ∧
    ((∀ m : ℕ, 1 < m → Tendsto (fun i => packetMultipleCoefficient (N i) m) l
      (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) ↔ RiemannHypothesis) ∧
    ((∑' n, packetGain n) = 1 ↔ RiemannHypothesis) ∧
    (¬ Summable packetRelativeGain ↔ RiemannHypothesis) := by
  have he : limitEnergy = 0 ↔ RiemannHypothesis :=
    limitEnergy_zero_iff_mem.trans
      (projection_norm_tendsto_zero_iff_mem.symm.trans
        (projection_norm_iff_riemannHypothesis_of_baez_duarte hBaezDuarte))
  exact ⟨(packet_cofinal_mass_iff N hN).trans he,
    (packet_cofinal_norm_iff N hN).trans he,
    (packet_cofinal_coefficients_iff N hN).trans he,
    packet_gain_saturation_iff.trans he, packet_relativeGain_not_summable_iff.trans he⟩
end RiemannResearch.RH.RamanujanCanonicalOptimizer
