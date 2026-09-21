import RiemannResearch.RH.ParetoExactHeadResidual
import RiemannResearch.RH.IntegerDPPMellinObstruction

/-!
# Polynomial energy obstruction for exact first-point heads

Source: user-provided `ParetoCapacityFormalization20260921_Continued_ParityClosure (1).md`,
supplement on the exact-head Mobius family and its uniform-bound target.
This module retains the full Mellin factor of the first physical point.
Every lower bound explicitly assumes a right-half-plane zeta zero; no such
zero is asserted to exist. The consequences concern complete Hilbert norms.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open TailCapacity

/-- Matching the first N coordinates amplifies a Mellin separator by the
exact power (N+1)^(2 Re(s)-1). The target can be any actual Hilbert vector. -/
theorem matching_head_mellin_distance_lower_bound
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (x f : ThresholdHilbert) (hf : f ∈ closedSpace)
    {N : ℕ} (hhead : ∀ k, 0 < k → k ≤ N →
      hilbertSequence f k = hilbertSequence x k) :
    (2 * s.re - 1) * ‖paretoMellin x s‖ ^ 2 *
        ((N : ℝ) + 1) ^ (2 * s.re - 1) ≤ ‖x - f‖ ^ 2 := by
  have hr : ∀ k, 0 < k → k ≤ N → hilbertSequence (x - f) k = 0 := by
    intro k hk hkN
    change hilbertSequenceLinear (x - f) k = 0
    rw [map_sub]
    change hilbertSequence x k - hilbertSequence f k = 0
    rw [hhead k hk hkN, sub_self]
  have hf0 := paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
    (fun _ hn => hn) s hs hs1 hz (closedSpace_le_legalClosure hf)
  have hm : paretoMellin (x - f) s = paretoMellin x s := by
    change paretoMellinContinuous s hs (x - f) = _
    rw [map_sub]
    change paretoMellin x s - paretoMellin f s = _
    rw [hf0, sub_zero]
  have h := paretoMellin_zero_head_norm_sq_le hr s hs
  rw [hm] at h
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hb : 0 < (N : ℝ) + 1 := by positivity
  have hp : 0 < ((N : ℝ) + 1) ^ (2 * s.re - 1) :=
    Real.rpow_pos_of_pos hb _
  have he : ((N : ℝ) + 1) ^ (2 * s.re - 1) *
      ((N : ℝ) + 1) ^ (1 - 2 * s.re) = 1 := by
    rw [← Real.rpow_add hb]
    have hexp : 2 * s.re - 1 + (1 - 2 * s.re) = 0 := by ring
    rw [hexp, Real.rpow_zero]
  have hh := mul_le_mul_of_nonneg_left h (mul_nonneg hd.le hp.le)
  have hcancel : (2 * s.re - 1) * ((N : ℝ) + 1) ^ (2 * s.re - 1) *
      (‖x - f‖ ^ 2 *
        (((N : ℝ) + 1) ^ (1 - 2 * s.re) / (2 * s.re - 1))) =
      ‖x - f‖ ^ 2 := by
    calc
      _ = ‖x - f‖ ^ 2 *
          (((N : ℝ) + 1) ^ (2 * s.re - 1) *
            ((N : ℝ) + 1) ^ (1 - 2 * s.re)) := by field_simp [ne_of_gt hd]
      _ = _ := by rw [he, mul_one]
  rw [hcancel] at hh
  nlinarith only [hh]

/-- The exact first-point head separates off its fixed energy a²/2.
The remaining norm must grow at the explicit zero-dependent power. -/
theorem firstPoint_matching_head_energy_lower_bound
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) {a : ℝ} {f : ThresholdHilbert}
    (hf : f ∈ closedSpace) {N : ℕ} (hN : 1 ≤ N)
    (hhead : ∀ k, 0 < k → k ≤ N →
      hilbertSequence f k = hilbertSequence (a • paretoPointHilbert 0) k) :
    a ^ 2 / 2 + a ^ 2 * (2 * s.re - 1) *
      ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 / ‖s‖ ^ 2 *
        ((N : ℝ) + 1) ^ (2 * s.re - 1) ≤ ‖f‖ ^ 2 := by
  have h := matching_head_mellin_distance_lower_bound s hs hs1 hz
    (a • paretoPointHilbert 0) f hf hhead
  have hv : anchoredEvaluationCLM 1 f = a := by
    rw [anchoredEvaluationCLM_apply, hhead 1 (by omega) hN]
    rw [← anchoredEvaluationCLM_apply]
    simp only [map_smul, firstPoint_evaluation, smul_eq_mul, mul_one]
  have he : a • paretoPointHilbert 0 - f = -(tailMap f) := by
    change a • paretoPointHilbert 0 - f =
      -(f - (anchoredEvaluationCLM 1 f) • paretoPointHilbert 0)
    rw [hv]
    abel
  rw [he, norm_neg, tailMap_norm_sq, hv] at h
  have hm : ‖paretoMellin (a • paretoPointHilbert 0) s‖ ^ 2 =
      a ^ 2 * (‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 / ‖s‖ ^ 2) := by
    change ‖paretoMellinContinuous s hs (a • paretoPointHilbert 0)‖ ^ 2 = _
    rw [map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    change a ^ 2 * ‖paretoMellin (paretoPointHilbert 0) s‖ ^ 2 = _
    rw [IntegerDPP.firstPoint_mellin s hs, norm_div, div_pow]
  rw [hm] at h
  simp only [div_eq_mul_inv] at h ⊢
  nlinarith only [h]

/-- A finite full-energy upper bound below the displayed threshold rules out
an actual zero at s; no limit or missing tail estimate is suppressed. -/
theorem zeta_ne_zero_of_firstPoint_matching_head_energy_lt
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    {a : ℝ} {f : ThresholdHilbert} (hf : f ∈ closedSpace)
    {N : ℕ} (hN : 1 ≤ N)
    (hhead : ∀ k, 0 < k → k ≤ N →
      hilbertSequence f k = hilbertSequence (a • paretoPointHilbert 0) k)
    (henergy : ‖f‖ ^ 2 < a ^ 2 / 2 + a ^ 2 * (2 * s.re - 1) *
      ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 / ‖s‖ ^ 2 *
        ((N : ℝ) + 1) ^ (2 * s.re - 1)) : riemannZeta s ≠ 0 := by
  intro hz
  exact not_lt_of_ge
    (firstPoint_matching_head_energy_lower_bound s hs hs1 hz hf hN hhead) henergy

end RiemannResearch.RH.Pareto.CoefficientStabilization
