import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.MixedConductorRankOne
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ParetoInitialIntervalCertificates
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Full mixed-conductor capture from legal approximation

The rank-one screened norm determines the *whole* mixed capture of parity.
An explicit legal trial under either probability law therefore controls this
projection without computing a mixed-packet Gram matrix.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur

open CoefficientStabilization
open RiemannResearch.RH ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer

/-- The complete period-5040 physical residual bounds the limiting error. -/
theorem limitEnergy_lt_period5040_bound : limitEnergy < (39 : ℝ) / 1000 := by
  have hd := one_infDist_lt_of_period5040
  rw [closedSpace.infDist_eq_norm_sub_starProjection] at hd
  change ‖hilbertOne - closedSpace.starProjection hilbertOne‖ ^ 2 < _
  have hs := (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hd
  rwa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 39 / 1000)] at hs

/-- Exact squared norm of the screened conductor-two packet with mean one. -/
theorem normalizedScreenedTwo_norm_sq :
    ‖normalizedScreenedTwo‖ ^ 2 = 1 / (1 - limitEnergy) := by
  have hden : 1 - limitEnergy ≠ 0 := one_sub_limitEnergy_pos.ne'
  have he := normalizedScreenedTwo_error_sq_eq_limitEnergy
  rw [norm_sub_sq_real, normalizedScreenedTwo_mean, hilbertOne_norm_sq] at he
  field_simp [hden] at he ⊢
  nlinarith

theorem one_le_norm_normalizedScreenedTwo : 1 ≤ ‖normalizedScreenedTwo‖ := by
  have hOne : ‖hilbertOne‖ = 1 := by nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  simpa only [normalizedScreenedTwo_mean, hOne, mul_one] using
    real_inner_le_norm normalizedScreenedTwo hilbertOne

theorem normalizedScreenedTwo_norm_eq_one_iff :
    ‖normalizedScreenedTwo‖ = 1 ↔ limitEnergy = 0 := by
  have he := normalizedScreenedTwo_norm_sq
  constructor
  · intro hu
    rw [hu, one_pow, one_div] at he
    linarith only [inv_eq_one.mp he.symm]
  · intro hE
    rw [hE, sub_zero, div_one] at he
    nlinarith [norm_nonneg normalizedScreenedTwo]

theorem one_lt_norm_normalizedScreenedTwo_iff :
    1 < ‖normalizedScreenedTwo‖ ↔ 0 < limitEnergy := by
  have hE : 0 ≤ limitEnergy := sq_nonneg ‖limitResidual‖
  constructor
  · intro hu
    exact lt_of_le_of_ne hE fun h =>
      hu.ne' (normalizedScreenedTwo_norm_eq_one_iff.mpr h.symm)
  · intro he
    exact lt_of_le_of_ne one_le_norm_normalizedScreenedTwo fun h =>
      he.ne' (normalizedScreenedTwo_norm_eq_one_iff.mp h.symm)

/-- The complete period-5040 trial gives a strict upper bound on the squared norm. -/
theorem normalizedScreenedTwo_norm_sq_lt_period5040 :
    ‖normalizedScreenedTwo‖ ^ 2 < (1000 : ℝ) / 961 := by
  rw [normalizedScreenedTwo_norm_sq]
  apply (div_lt_iff₀ one_sub_limitEnergy_pos).mpr
  linarith only [limitEnergy_lt_period5040_bound]

theorem limitProjection_eq_inv_norm_sq_smul_screenedTwo :
    limitProjection = (‖normalizedScreenedTwo‖ ^ 2)⁻¹ • normalizedScreenedTwo := by
  rw [normalizedScreenedTwo_norm_sq, one_div, inv_inv]
  exact limitProjection_eq_scaled_screenedTwo

theorem limitProjection_inner_normalizedScreenedTwo :
    inner ℝ limitProjection normalizedScreenedTwo = 1 := by
  have h : ‖normalizedScreenedTwo‖ ^ 2 ≠ 0 :=
    (sq_pos_of_pos (zero_lt_one.trans_le one_le_norm_normalizedScreenedTwo)).ne'
  rw [limitProjection_eq_inv_norm_sq_smul_screenedTwo, real_inner_smul_left,
    real_inner_self_eq_norm_sq, inv_mul_cancel₀ h]

theorem normalizedScreenedTwo_norm_eq_one_iff_naturalApproximation :
    ‖normalizedScreenedTwo‖ = 1 ↔ BaezDuarte.NaturalApproximation :=
  normalizedScreenedTwo_norm_eq_one_iff.trans
    (limitEnergy_zero_iff_mem.trans BaezDuarte.naturalApproximation_iff_one_mem.symm)

theorem riemannHypothesis_of_normalizedScreenedTwo_norm_eq_one
    (hu : ‖normalizedScreenedTwo‖ = 1) : RiemannHypothesis :=
  riemannHypothesis_of_normalizedScreenedTwo
    (one_mem_closedSpace_iff_normalizedScreenedTwo.mp
      (limitEnergy_zero_iff_mem.mp (normalizedScreenedTwo_norm_eq_one_iff.mp hu)))

theorem one_lt_norm_normalizedScreenedTwo_of_not_riemannHypothesis
    (h : ¬ RiemannHypothesis) : 1 < ‖normalizedScreenedTwo‖ :=
  lt_of_le_of_ne one_le_norm_normalizedScreenedTwo fun hu =>
    h (riemannHypothesis_of_normalizedScreenedTwo_norm_eq_one hu.symm)

/-- Báez-Duarte's Theorem 1.1 supplies the analytic implication in the reverse direction. -/
theorem normalizedScreenedTwo_norm_eq_one_iff_riemannHypothesis
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    ‖normalizedScreenedTwo‖ = 1 ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_normalizedScreenedTwo_norm_eq_one,
    fun hRH => normalizedScreenedTwo_norm_eq_one_iff_naturalApproximation.mpr (hBaezDuarte hRH)⟩

theorem one_lt_norm_normalizedScreenedTwo_iff_not_riemannHypothesis
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    1 < ‖normalizedScreenedTwo‖ ↔ ¬ RiemannHypothesis :=
  ⟨fun hu hRH => hu.ne'
      ((normalizedScreenedTwo_norm_eq_one_iff_riemannHypothesis hBaezDuarte).mpr hRH),
    one_lt_norm_normalizedScreenedTwo_of_not_riemannHypothesis⟩

/-- Exact conversion of the best legal error into full mixed parity capture. -/
theorem full_mixed_capture_eq_limitEnergy :
    ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 =
      Real.log 2 - (Real.log 2) ^ 2 / (1 - limitEnergy) := by
  let z := ramanujanPacketHilbert 2
  let p := mixedClosure.starProjection z
  have hp : inner ℝ p (z - p) = 0 :=
    (mixedClosure.mem_orthogonal _).mp (mixedClosure.sub_starProjection_mem_orthogonal z) p
      (mixedClosure.starProjection_apply_mem z)
  rw [inner_sub_right, real_inner_self_eq_norm_sq, sub_eq_zero] at hp
  have hz : z - p = Real.log 2 • normalizedScreenedTwo := by
    change fullScreening (ramanujanPacketHilbert 2) = _
    simpa only [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two, Nat.cast_ofNat] using
      fullScreening_packet_eq_mangoldt_smul 2 (by decide)
  have hp' : inner ℝ z p = ‖p‖ ^ 2 := (real_inner_comm _ _).trans hp
  have hs : ‖z - p‖ ^ 2 = Real.log 2 - ‖p‖ ^ 2 := by
    rw [norm_sub_sq_real, hp']
    change ‖ramanujanPacketHilbert 2‖ ^ 2 - _ + _ = _
    rw [ramanujanPacketHilbert_two_norm_sq]
    ring
  rw [hz, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, normalizedScreenedTwo_norm_sq] at hs
  change ‖p‖ ^ 2 = _
  rw [div_eq_mul_inv] at hs ⊢
  simp only [one_mul] at hs
  linarith only [hs]

/-- A strict upper bound on the best unrestricted legal error gives a strict
lower bound on the full mixed projection, with the exact denominator. -/
theorem full_mixed_capture_lower_of_limitEnergy_lt {d : ℝ}
    (he : limitEnergy < d) (hd : d < 1) :
    Real.log 2 - (Real.log 2) ^ 2 / (1 - d) <
      ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 := by
  rw [full_mixed_capture_eq_limitEnergy]
  apply sub_lt_sub_left
  exact div_lt_div_of_pos_left (sq_pos_of_pos (Real.log_pos (by norm_num)))
    (by linarith) (by linarith)

/-- A complete legal squarefree Q trial controls the best P error. -/
theorem limitEnergy_le_zetaTwo_mul_legal_qError {f : QHilbert}
    (hf : f ∈ ZetaTwoOptimizerStage.closure) :
    limitEnergy ≤ zetaTwo * ‖qOne - f‖ ^ 2 := by
  have hd := Metric.infDist_le_dist_of_mem (x := hilbertOne) (toPareto_mem_closedSpace hf)
  rw [closedSpace.infDist_eq_norm_sub_starProjection, dist_eq_norm] at hd
  have hm : toPareto (qOne - f) = hilbertOne - toPareto f := by
    simpa only [toParetoCLM_apply, toPareto_qOne] using toParetoCLM.map_sub qOne f
  have hc := toPareto_norm_sq_le (qOne - f)
  rw [hm] at hc
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hd).trans hc

/-- A rational or analytic Q error certificate transfers to full mixed capture. -/
theorem full_mixed_capture_lower_of_legal_qError {f : QHilbert}
    (hf : f ∈ ZetaTwoOptimizerStage.closure) {q : ℝ} (hq : ‖qOne - f‖ ^ 2 < q)
    (hsmall : zetaTwo * q < 1) :
    Real.log 2 - (Real.log 2) ^ 2 / (1 - zetaTwo * q) <
      ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 := by
  exact full_mixed_capture_lower_of_limitEnergy_lt
    ((limitEnergy_le_zetaTwo_mul_legal_qError hf).trans_lt
      (mul_lt_mul_of_pos_left hq zetaTwo_pos)) hsmall

/-- Explicit unconditional lower bound from the two-seed period-5040 trial. -/
theorem full_mixed_capture_lower_period5040 :
    Real.log 2 - (1000 / 961 : ℝ) * (Real.log 2) ^ 2 <
      ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2 := by
  have h := full_mixed_capture_lower_of_limitEnergy_lt limitEnergy_lt_period5040_bound
    (by norm_num)
  convert h using 1
  ring

/-- Every strict bound on the full capture already holds throughout the tail
of the increasing sequence of physical mixed-conductor windows. -/
theorem eventually_mixed_capture_gt_of_lt_full {b : ℝ}
    (hb : b < ‖mixedClosure.starProjection (ramanujanPacketHilbert 2)‖ ^ 2) :
    ∀ᶠ N : ℕ in atTop, b <
      ‖(mixedSpace (Finset.Icc 2 N)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 := by
  have hm : Monotone (fun N : ℕ => mixedSpace (Finset.Icc 2 N)) :=
    fun _ _ h => mixedSpace_mono (Finset.Icc_subset_Icc le_rfl h)
  exact ((Submodule.starProjection_tendsto_closure_iSup
    (fun N => mixedSpace (Finset.Icc 2 N)) hm (ramanujanPacketHilbert 2)).norm.pow 2).eventually
    (lt_mem_nhds hb)

/-- The verified global period-5040 trial also certifies a cofinal mixed-window bound. -/
theorem eventually_mixed_capture_gt_period5040 :
    ∀ᶠ N : ℕ in atTop, Real.log 2 - (1000 / 961 : ℝ) * (Real.log 2) ^ 2 <
      ‖(mixedSpace (Finset.Icc 2 N)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 :=
  eventually_mixed_capture_gt_of_lt_full full_mixed_capture_lower_period5040

end RiemannResearch.RH.Pareto.PrimePowerSchur
