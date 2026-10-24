import RiemannResearch.RH.RamanujanMellinMovingProbes
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.QRamanujanSaturationCriteria
import RiemannResearch.RH.RamanujanZeroBudgetLimits

/-!
# Complete Mellin exhaustion of the actual Ramanujan residuals

Source: the complete physical Mellin innovation series and independently
cofinal observation theorem, 24 October 2026. Both actual Pareto and Q
optimizers are retained. RH equivalences explicitly assume the project's
still-open RH-to-Baez--Duarte implication. Vanishing of the unobserved energy
is never asserted. At actual zeros it equals the previously unresolved
product gap, with the exact measure correction on the Q side.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.RamanujanMellinExhaustion
open Pareto Pareto.CoefficientStabilization ZetaTwoHilbert ZetaTwoProbability
open ZetaTwoParetoTransfer QParetoMetric QMellinTransfer
open RamanujanZeroCertificates QRamanujanMellinCertificates

def qResidualLimit : QHilbert :=
  qOne - QFullResidueProjection.closure.starProjection qOne

variable {α : Type*} {l : Filter α}

theorem pareto_packetResidual_tendsto (K : α → ℕ) (hK : Tendsto K l atTop) :
    Tendsto (fun i => hilbertOne - RamanujanCanonicalOptimizer.packetCandidate (K i))
      l (𝓝 limitResidual) := by
  simpa only [RamanujanCanonicalOptimizer.packetCandidate_eq_projection,
    Function.comp_apply, limitResidual] using
    tendsto_const_nhds.sub (projection_tendsto.comp hK)

theorem q_packetResidual_tendsto (K : α → ℕ) (hK : Tendsto K l atTop) :
    Tendsto (fun i => qOne - QRamanujanCanonicalOptimizer.packetCandidate (K i))
      l (𝓝 qResidualLimit) :=
  tendsto_const_nhds.sub (QRamanujanCanonicalOptimizer.packetCandidate_tendsto_projection.comp hK)

/-- The full canonical Pareto obstruction splits into captured and unobserved energy. -/
theorem pareto_limit_energy_mellin_exact (z : ℕ → ℂ) :
    limitEnergy = mellinCapacityLimit limitResidual z +
      mellinUnobservedEnergy limitResidual z :=
  mellin_infinite_energy_exact limitResidual z

/-- The actual Q obstruction has its own residual and exact positive measure correction. -/
theorem q_limit_energy_mellin_exact (z : ℕ → ℂ) :
    zetaTwo * QRamanujanCanonicalOptimizer.packetLimitEnergy =
      mellinCapacityLimit (toPareto qResidualLimit) z +
      mellinUnobservedEnergy (toPareto qResidualLimit) z + metricCorrection qResidualLimit :=
  qMellin_infinite_energy_exact qResidualLimit z

/-- Saturation of the genuine Q optimizer is exactly the two-part physical Mellin criterion.
The reverse norm comparison makes the complete-sequence transfer faithful. -/
theorem q_energy_zero_iff_mellin_energies_zero (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) :
    QRamanujanCanonicalOptimizer.packetLimitEnergy = 0 ↔
      mellinCapacityLimit (toPareto qResidualLimit) z = 0 ∧
      mellinUnobservedEnergy (toPareto qResidualLimit) z = 0 := by
  rw [← mellin_zero_iff_both_energies_zero (toPareto qResidualLimit) z hz hinj]
  constructor
  · intro he
    change ‖qResidualLimit‖ ^ 2 = 0 at he
    have hq : qResidualLimit = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp he)
    change toParetoLinear qResidualLimit = 0
    rw [hq, map_zero]
  · intro hp
    have h := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq qResidualLimit
    rw [hp, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
    change ‖qResidualLimit‖ ^ 2 = 0
    nlinarith [zetaTwo_pos, sq_nonneg ‖qResidualLimit‖]

/-- Actual legal packet stage and Mellin depth may exhaust independently. -/
theorem pareto_packet_moving_mellin_limits (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z)
    (N K : α → ℕ) (hN : Tendsto N l atTop) (hK : Tendsto K l atTop) :
    Tendsto (fun i => mellinPrefixCapacity z (fun j => paretoMellin
      (hilbertOne - RamanujanCanonicalOptimizer.packetCandidate (K i)) (z j)) (N i))
      l (𝓝 (mellinCapacityLimit limitResidual z)) ∧
    Tendsto (fun i => mellinProjectionRemainder
      (hilbertOne - RamanujanCanonicalOptimizer.packetCandidate (K i))
      (fun j : Fin (N i) => z j.val)) l (𝓝 (mellinUnobservedEnergy limitResidual z)) :=
  ⟨mellinPrefixCapacity_moving_tendsto _ _ (pareto_packetResidual_tendsto K hK) z hz hinj N hN,
    mellinProjectionRemainder_moving_tendsto _ _ (pareto_packetResidual_tendsto K hK) z hz hinj N hN⟩

theorem q_packet_moving_mellin_limits (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z)
    (N K : α → ℕ) (hN : Tendsto N l atTop) (hK : Tendsto K l atTop) :
    Tendsto (fun i => mellinPrefixCapacity z (fun j => qMellin
      (qOne - QRamanujanCanonicalOptimizer.packetCandidate (K i)) (z j)) (N i))
      l (𝓝 (mellinCapacityLimit (toPareto qResidualLimit) z)) ∧
    Tendsto (fun i => mellinProjectionRemainder
      (toPareto (qOne - QRamanujanCanonicalOptimizer.packetCandidate (K i)))
      (fun j : Fin (N i) => z j.val))
      l (𝓝 (mellinUnobservedEnergy (toPareto qResidualLimit) z)) :=
  qMellin_moving_observations_tendsto _ _ (q_packetResidual_tendsto K hK) z hz hinj N hN

/-- A full RH chain on the two actual Ramanujan sides; no probe completeness is hidden. -/
theorem mellin_limit_rh_equivalences
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (z : ℕ → ℂ) (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) :
    ((mellinCapacityLimit limitResidual z = 0 ∧
      mellinUnobservedEnergy limitResidual z = 0) ↔ RiemannHypothesis) ∧
    ((mellinCapacityLimit (toPareto qResidualLimit) z = 0 ∧
      mellinUnobservedEnergy (toPareto qResidualLimit) z = 0) ↔ RiemannHypothesis) := by
  have hp := (RamanujanCanonicalOptimizer.packet_cofinal_mass_iff id tendsto_id).symm.trans
    (RamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1
  have hq := (QRamanujanCanonicalOptimizer.packet_cofinal_mass_iff id tendsto_id).symm.trans
    (QRamanujanCanonicalOptimizer.packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1
  exact ⟨(mellin_zero_iff_both_energies_zero limitResidual z hz hinj).symm.trans
    (limitResidual_zero_iff_energy_zero.trans hp),
    (q_energy_zero_iff_mellin_energies_zero z hz hinj).symm.trans hq⟩

/-- Independent cofinal legal stages and observation depths give the same RH criterion. -/
theorem pareto_packet_moving_mellin_iff_rh [NeBot l]
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (z : ℕ → ℂ) (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z)
    (N K : α → ℕ) (hN : Tendsto N l atTop) (hK : Tendsto K l atTop) :
    (Tendsto (fun i => mellinPrefixCapacity z (fun j => paretoMellin
        (hilbertOne - RamanujanCanonicalOptimizer.packetCandidate (K i)) (z j)) (N i))
        l (𝓝 0) ∧
      Tendsto (fun i => mellinProjectionRemainder
        (hilbertOne - RamanujanCanonicalOptimizer.packetCandidate (K i))
        (fun j : Fin (N i) => z j.val)) l (𝓝 0)) ↔ RiemannHypothesis := by
  have he := mellin_zero_iff_moving_observations_vanish _ _
    (pareto_packetResidual_tendsto K hK) z hz hinj N hN
  exact he.symm.trans ((mellin_zero_iff_both_energies_zero limitResidual z hz hinj).trans
    (mellin_limit_rh_equivalences hBaezDuarte z hz hinj).1)

/-- Genuine Q has the same complete criterion with its own inverse-Gram optimizer. -/
theorem q_packet_moving_mellin_iff_rh [NeBot l]
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (z : ℕ → ℂ) (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z)
    (N K : α → ℕ) (hN : Tendsto N l atTop) (hK : Tendsto K l atTop) :
    (Tendsto (fun i => mellinPrefixCapacity z (fun j => qMellin
        (qOne - QRamanujanCanonicalOptimizer.packetCandidate (K i)) (z j)) (N i))
        l (𝓝 0) ∧
      Tendsto (fun i => mellinProjectionRemainder
        (toPareto (qOne - QRamanujanCanonicalOptimizer.packetCandidate (K i)))
        (fun j : Fin (N i) => z j.val)) l (𝓝 0)) ↔ RiemannHypothesis := by
  have ht := q_packet_moving_mellin_limits z hz hinj N K hN hK
  have he :
      (Tendsto (fun i => mellinPrefixCapacity z (fun j => qMellin
          (qOne - QRamanujanCanonicalOptimizer.packetCandidate (K i)) (z j)) (N i)) l (𝓝 0) ∧
        Tendsto (fun i => mellinProjectionRemainder
          (toPareto (qOne - QRamanujanCanonicalOptimizer.packetCandidate (K i)))
          (fun j : Fin (N i) => z j.val)) l (𝓝 0)) ↔
      (mellinCapacityLimit (toPareto qResidualLimit) z = 0 ∧
        mellinUnobservedEnergy (toPareto qResidualLimit) z = 0) := by
    constructor
    · rintro ⟨hc, hr⟩
      exact ⟨tendsto_nhds_unique ht.1 hc, tendsto_nhds_unique ht.2 hr⟩
    · rintro ⟨hc, hr⟩
      exact ⟨hc ▸ ht.1, hr ▸ ht.2⟩
  exact he.trans (mellin_limit_rh_equivalences hBaezDuarte z hz hinj).2

/-- Every actual right-half-plane zero has the exact limiting Pareto signature. -/
theorem pareto_limitResidual_mellin_at_zero (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hzero : riemannZeta s = 0) :
    paretoMellin limitResidual s = 1 / s := by
  have ht : Tendsto (fun n : ℕ => paretoMellin
      (hilbertOne - RamanujanCanonicalOptimizer.packetCandidate n) s) atTop
      (𝓝 (paretoMellin limitResidual s)) :=
    ((paretoMellinContinuous s hs).continuous.tendsto limitResidual).comp
      (pareto_packetResidual_tendsto id tendsto_id)
  have he (n : ℕ) : paretoMellin
      (hilbertOne - RamanujanCanonicalOptimizer.packetCandidate n) s = 1 / s := by
    rw [paretoMellin_packetCandidate_error_signature n s hs, canonicalMellinCorrection,
      packetMellinCorrection_eq_zeta n _ s (by linarith) hs1, hzero]
    simp
  have ht' : Tendsto (fun _ : ℕ => 1 / s) atTop (𝓝 (paretoMellin limitResidual s)) := by
    simpa only [he] using ht
  exact tendsto_nhds_unique ht' tendsto_const_nhds

/-- The genuine Q limiting signature is identical at zeros, although its optimizer differs. -/
theorem qResidualLimit_mellin_at_zero (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) (hzero : riemannZeta s = 0) :
    qMellin qResidualLimit s = 1 / s := by
  have ht : Tendsto (fun n : ℕ => qMellin
      (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) s) atTop
      (𝓝 (qMellin qResidualLimit s)) :=
    ((qMellinContinuous s hs).continuous.tendsto qResidualLimit).comp
      (q_packetResidual_tendsto id tendsto_id)
  have he (n : ℕ) : qMellin
      (qOne - QRamanujanCanonicalOptimizer.packetCandidate n) s = 1 / s := by
    rw [qMellin_packetCandidate_error_signature n s hs,
      qCanonicalMellinCorrection_eq_zeta n s (by linarith) hs1, hzero]
    simp
  have ht' : Tendsto (fun _ : ℕ => 1 / s) atTop (𝓝 (qMellin qResidualLimit s)) := by
    simpa only [he] using ht
  exact tendsto_nhds_unique ht' tendsto_const_nhds

/-- The infinite captured energy is the exact complementary zero product,
for any physical vector with the complete zero signature. -/
theorem mellinCapacityLimit_zero_signature (f : ThresholdHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z)
    (hsig : ∀ n, paretoMellin f (z n) = 1 / z n) :
    mellinCapacityLimit f z = 1 - mellinZeroProductLimit z := by
  have he (N : ℕ) : mellinPrefixCapacity z (fun j => paretoMellin f (z j)) N =
      1 - mellinZeroProduct (fun i : Fin N => z i.val) := by
    unfold mellinPrefixCapacity
    simp_rw [hsig]
    exact mellinInverseCapacity_zeroSource_product _ (fun i => hz i.val)
      (hinj.comp Fin.val_injective)
  have hfun : mellinPrefixCapacity z (fun j => paretoMellin f (z j)) =
      fun N => 1 - mellinZeroProduct (fun i : Fin N => z i.val) := funext he
  have hc := mellinPrefixCapacity_physical_tendsto f z hz hinj
  rw [hfun] at hc
  exact tendsto_nhds_unique hc
    (tendsto_const_nhds.sub (mellinZeroProduct_prefix_tendsto z hz hinj))

/-- The previously unresolved product gap is precisely the unobserved energy
of the canonical limiting residual, not merely an upper or lower bound. -/
theorem zeroProductResidualGap_eq_unobserved (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z)
    (hz1 : ∀ n, z n ≠ 1) (hzero : ∀ n, riemannZeta (z n) = 0) :
    zeroProductResidualGap z = mellinUnobservedEnergy limitResidual z := by
  have hc := mellinCapacityLimit_zero_signature limitResidual z hz hinj
    (fun n => pareto_limitResidual_mellin_at_zero (z n) (hz n) (hz1 n) (hzero n))
  unfold mellinUnobservedEnergy
  rw [hc]
  change mellinZeroProductLimit z - (1 - limitEnergy) =
    limitEnergy - (1 - mellinZeroProductLimit z)
  ring

/-- The genuine Q product gap contains the full unobserved energy and the
entire positive change-of-measure correction. -/
theorem q_zero_product_gap_exact (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z)
    (hz1 : ∀ n, z n ≠ 1) (hzero : ∀ n, riemannZeta (z n) = 0) :
    zetaTwo * QRamanujanCanonicalOptimizer.packetLimitEnergy -
      (1 - mellinZeroProductLimit z) =
      mellinUnobservedEnergy (toPareto qResidualLimit) z + metricCorrection qResidualLimit := by
  have hc := mellinCapacityLimit_zero_signature (toPareto qResidualLimit) z hz hinj
    (fun n => qResidualLimit_mellin_at_zero (z n) (hz n) (hz1 n) (hzero n))
  have he := q_limit_energy_mellin_exact z
  rw [hc] at he
  linarith

end RiemannResearch.RH.RamanujanMellinExhaustion
