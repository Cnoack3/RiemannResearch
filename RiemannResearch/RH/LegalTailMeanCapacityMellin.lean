import RiemannResearch.RH.LegalTailMeanCapacity
import RiemannResearch.RH.ParetoFiniteHeadDilation
import RiemannResearch.RH.ParetoMellinDilation
import RiemannResearch.RH.LocalizedMellinObstruction
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A zero imposes a uniform gap in normalized legal tail-mean capacity

The continuous Mellin symbol of the Pareto tail indicator is explicit.
Its residual after projection onto the legal zero-head kernel is supported
on the same physical tail. The localized Cauchy inequality therefore gives
the same normalized deficit at every integer scale.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization

/-- Mellin symbol of the complete physical tail after K. -/
theorem paretoTail_mellin (K : ℕ) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (paretoTail K) s = ((K+1 : ℕ) : ℂ)^(-s) / s := by
  have htail : paretoTail K = (((K+1 : ℕ) : ℝ)⁻¹) •
      hilbertDilation (K+1) (Nat.succ_pos _) hilbertOne := by
    change hilbertOne - finiteHeadIndicator K = _
    rw [finiteHeadIndicator_eq_dilation_difference]
    abel
  have hm : ((K+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_pos _).ne'
  rw [htail, paretoMellin_smul, paretoMellin_dilation, paretoMellin_one s hs,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, sub_eq_add_neg,
    Complex.cpow_add _ _ hm, Complex.cpow_one]
  field_simp [hm] <;> ring

namespace PrimePowerSchur
open FiniteHeadRepair RiemannResearch.Analysis.SingleObservationProjection

private theorem tail_mellin_weight_cancel {m : ℝ} (hm : 0 < m) (σ : ℝ) :
    (m^(-σ))^2 * m^(2*σ-1) * m = 1 := by
  calc
    _ = m^((-σ)*2) * m^(2*σ-1) * m^(1 : ℝ) := by rw [Real.rpow_mul hm.le, Real.rpow_two, Real.rpow_one]
    _ = m^((-σ)*2 + (2*σ-1) + 1) := by rw [Real.rpow_add hm, Real.rpow_add hm]
    _ = 1 := by rw [show (-σ)*2+(2*σ-1)+1=0 by ring, Real.rpow_zero]

/-- Every actual right zero enforces a scale-independent deficit after the
tail capacity is normalized by the reciprocal remaining Pareto mass. -/
theorem legalTailMeanCapacity_zero_gap (K : ℕ) (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    ((K : ℝ)+1) * legalTailMeanCapacity K ≤ 1 - (2*s.re-1)/‖s‖^2 := by
  let S := legalHeadKernel K
  let t := paretoTail K
  let v := S.starProjection t
  let m : ℝ := ((K+1 : ℕ) : ℝ)
  have hmem : v ∈ legalHeadKernel K := S.starProjection_apply_mem t
  have hv := paretoMellin_zero_on_legalClosure_of_zeta {j : ℕ | 0 < j}
    (fun _ hj => hj) s hs hs1 hz (closedSpace_le_legalClosure hmem.1)
  have hval : paretoMellin (t-v) s = ((K+1 : ℕ) : ℂ)^(-s) / s := by
    change paretoMellinContinuous s hs (t-v) = _
    rw [map_sub]
    change paretoMellin (paretoTail K) s - paretoMellin v s = _
    rw [paretoTail_mellin K s hs, hv, sub_zero]
  have hhead (j : ℕ) (hj : 0 < j) (hjK : j < K+1) : hilbertSequence (t-v) j = 0 := by
    cases j with
    | zero => omega
    | succ i =>
      have hi : i < K := by omega
      have hh := congrFun (show headMap K v = 0 from hmem.2) (⟨i,hi⟩ : Fin K)
      rw [headMap_apply] at hh
      rw [hilbertSequence_sub, Pi.sub_apply, show hilbertSequence v (i+1) = 0 from hh, sub_zero,
        ← hilbertGibbsPhysical_eq, show t = paretoTail K from rfl, paretoTail_physical, if_pos hi]
  have hl := mellin_zero_head_lower (t-v) (K+1) (Nat.succ_pos _) hhead s hs
  rw [hval, norm_div, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos _), Complex.neg_re,
    div_pow] at hl
  have hm : 0 < m := by dsimp [m]; positivity
  have hc := mul_le_mul_of_nonneg_right hl hm.le
  have hnorm : ‖t-v‖^2 = 1/m - legalTailMeanCapacity K := by
    rw [show ‖t-v‖^2 = ‖t‖^2 - ‖v‖^2 from projection_defect_energy S t,
      show ‖t‖^2 = 1/((K : ℝ)+1) from paretoTail_norm_sq K]
    simp only [m, Nat.cast_add, Nat.cast_one, v, t, S, legalTailMeanCapacity]
  have hlow : (2*s.re-1)/‖s‖^2 ≤ (1/m-legalTailMeanCapacity K)*m := by
    calc
      (2*s.re-1)/‖s‖^2 =
          (2*s.re-1)/‖s‖^2 * ((m^(-s.re))^2*m^(2*s.re-1)*m) := by
            rw [tail_mellin_weight_cancel hm, mul_one]
      _ = (2*s.re-1) * ((m^(-s.re))^2 / ‖s‖^2) * m^(2*s.re-1) * m := by ring
      _ ≤ _ := by simpa only [hnorm] using hc
  rw [sub_mul, div_mul_cancel₀ _ hm.ne'] at hlow
  change ((K : ℝ)+1) * legalTailMeanCapacity K ≤ _
  have hcast : m = (K : ℝ)+1 := by simp [m]
  rw [hcast] at hlow
  linarith only [hlow]

/-- Arbitrarily close saturation of the normalized capacity at any scales
excludes every zero in the open right half-strip. -/
theorem riemannHypothesis_of_legalTailMeanCapacity_saturation
    (h : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, 1-ε < ((K : ℝ)+1)*legalTailMeanCapacity K) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hlt hz
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hlt
  have hc : 0 < (2*s.re-1)/‖s‖^2 := div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr hs0))
  obtain ⟨K, hK⟩ := h _ hc
  exact (not_lt_of_ge (legalTailMeanCapacity_zero_gap K s hs hs1 hz)) hK

end PrimePowerSchur
end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.Pareto.PrimePowerSchur

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.legalTailMeanCapacity_zero_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms legalTailMeanCapacity_zero_gap

end RiemannResearch.RH.Pareto.PrimePowerSchur

namespace RiemannResearch.RH.Pareto.PrimePowerSchur

/--
info: 'RiemannResearch.RH.Pareto.PrimePowerSchur.riemannHypothesis_of_legalTailMeanCapacity_saturation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_of_legalTailMeanCapacity_saturation

end RiemannResearch.RH.Pareto.PrimePowerSchur
