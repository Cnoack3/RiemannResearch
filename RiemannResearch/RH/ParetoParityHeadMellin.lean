import RiemannResearch.RH.ParetoParityAdjointHeads
import RiemannResearch.RH.ParetoMellinDilation
import RiemannResearch.RH.ParetoMellinTail
import RiemannResearch.RH.ResidualMellinZeroConditions

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

private theorem headIncrement_nonneg (j : ℕ) : 0 ≤ parityAdjointIncrement j := by
  rw [parityAdjointIncrement_eq]
  positivity

private theorem headIncrement_sum_le (N : ℕ) :
    ∑ j ∈ Finset.range N, parityAdjointIncrement j ≤ 1 / 6 := by
  have h (n : ℕ) :
      ∑ j ∈ Finset.range n, parityAdjointIncrement j = 1 / 6 - 1 / (4 * (n : ℝ) + 6) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, parityAdjointIncrement_eq]
      push_cast
      field_simp
      ring
  rw [h]
  exact sub_le_self _ (by positivity)

private def mellinPacketTerm (j : ℕ) : ThresholdHilbert :=
  parityAdjointIncrement j • hilbertTail (j + 2) (by omega)

private theorem mellinPacketTerm_summable : Summable mellinPacketTerm := by
  apply Summable.of_norm_bounded
    (summable_of_sum_range_le headIncrement_nonneg headIncrement_sum_le)
  intro j
  have hone : ‖hilbertOne‖ = 1 := by
    nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  let m := j + 2
  have hm : 0 < m := by dsimp [m]; omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : Real.sqrt (m : ℝ) ≤ m := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) m), Real.sqrt_nonneg (m : ℝ),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sub_nonneg.mpr hmR)]
  have hb : ‖hilbertTail m hm‖ ≤ 1 := by
    rw [hilbertTail, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      hilbertDilation_norm, hone, mul_one, one_div, ← div_eq_inv_mul]
    exact (div_le_one (by positivity)).mpr hs
  rw [mellinPacketTerm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (headIncrement_nonneg j)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (headIncrement_nonneg j)

private theorem tailMellin_formula (m : ℕ) (hm : 0 < m) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin (hilbertTail m hm) s = (m : ℂ) ^ (-s) * (1 / s) := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hilbertTail, paretoMellin_smul, paretoMellin_dilation, paretoMellin_one s hs,
    show (1 : ℂ) - s = 1 + (-s) by ring, Complex.cpow_add 1 (-s) hmC, Complex.cpow_one]
  change (((1 / (m : ℝ) : ℝ) : ℂ) * _) = _
  push_cast
  field_simp [hmC]

private theorem tailMellin_norm_le (m : ℕ) (hm : 0 < m) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    ‖paretoMellin (hilbertTail m hm) s‖ ≤ 1 / ‖s‖ := by
  rw [tailMellin_formula m hm s hs, norm_mul]
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : ‖(m : ℂ) ^ (-s)‖ ≤ 1 := by
    change ‖((m : ℝ) : ℂ) ^ (-s)‖ ≤ 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hmpos, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hmR (by linarith)
  simpa [norm_div] using mul_le_mul_of_nonneg_right hb (norm_nonneg (1 / s))

/-- The Mellin transform of the dyadic adjoint is separated from zero on each
point of the Hilbert half-plane. -/
theorem parityAdjointPacket_mellin_norm_lower (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    (1 / 6 : ℝ) * (1 / ‖s‖) ≤ ‖paretoMellin parityAdjointPacket s‖ := by
  let F := paretoMellinContinuous s hs
  let p (N : ℕ) := (1/3 : ℝ) • hilbertOne + ∑ j ∈ Finset.range N, mellinPacketTerm j
  have ht : Tendsto p atTop (𝓝 parityAdjointPacket) := by
    rw [parityAdjointPacket_expansion]
    exact tendsto_const_nhds.add mellinPacketTerm_summable.hasSum.tendsto_sum_nat
  have hlim := (F.continuous.continuousAt.tendsto.comp ht).norm
  apply ge_of_tendsto' hlim
  intro N
  have hb (j : ℕ) : ‖F (mellinPacketTerm j)‖ ≤ parityAdjointIncrement j * (1 / ‖s‖) := by
    rw [mellinPacketTerm, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (headIncrement_nonneg j)]
    exact mul_le_mul_of_nonneg_left (tailMellin_norm_le (j+2) (by omega) s hs) (headIncrement_nonneg j)
  have hsum : ‖∑ j ∈ Finset.range N, F (mellinPacketTerm j)‖ ≤ (1/6 : ℝ) * (1/‖s‖) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N, ‖F (mellinPacketTerm j)‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range N, parityAdjointIncrement j * (1 / ‖s‖) :=
        Finset.sum_le_sum fun j _ => hb j
      _ ≤ (1 / 6 : ℝ) * (1 / ‖s‖) := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (headIncrement_sum_le N) (by positivity)
  change (1 / 6 : ℝ) * (1 / ‖s‖) ≤ ‖F (p N)‖
  simp only [p, map_add, map_sum]
  have hfirst : ‖F ((1/3 : ℝ) • hilbertOne)‖ = (1/3 : ℝ) * (1 / ‖s‖) := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    change _ * ‖paretoMellin hilbertOne s‖ = _
    rw [paretoMellin_one s hs, norm_div, norm_one]
  have hh := norm_sub_le (F ((1/3 : ℝ) • hilbertOne) + ∑ j ∈ Finset.range N, F (mellinPacketTerm j))
    (∑ j ∈ Finset.range N, F (mellinPacketTerm j))
  rw [add_sub_cancel_right, hfirst] at hh
  linarith

theorem parityAdjointPacket_mellin_ne_zero (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    paretoMellin parityAdjointPacket s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  exact norm_pos_iff.mp (lt_of_lt_of_le (mul_pos (by norm_num)
    (one_div_pos.mpr (norm_pos_iff.mpr hs0))) (parityAdjointPacket_mellin_norm_lower s hs))

/-- A zero in the right Hilbert half-plane forces a polynomial lower bound on
the full squared error of every legal vector agreeing with the adjoint through N. -/
theorem parityAdjointPacket_exact_head_power_lower (s : ℂ) (hs : (1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (N : ℕ) (hN : 1 ≤ N) (v : ThresholdHilbert) (hv : v ∈ closedSpace)
    (hhead : ∀ n ≤ N, hilbertSequence v n = hilbertSequence parityAdjointPacket n) :
    ((1 / 6 : ℝ) * (1 / ‖s‖))^2 * (2 * s.re - 1) * (N : ℝ)^(2 * s.re - 1) ≤
      ‖parityAdjointPacket - v‖^2 := by
  have hH (n : ℕ) (hn : n ≤ N) : hilbertSequence (parityAdjointPacket - v) n = 0 := by
    rw [hilbertSequence_sub, Pi.sub_apply, hhead n hn, sub_self]
  have hnull := paretoMellin_zero_on_legalClosure_of_zeta {n : ℕ | 0 < n}
    (fun _ hn => hn) s hs hs1 hz (closedSpace_le_legalClosure hv)
  have hM : paretoMellin (parityAdjointPacket - v) s = paretoMellin parityAdjointPacket s := by
    change paretoMellinContinuous s hs (parityAdjointPacket - v) = _
    rw [map_sub]
    change paretoMellin parityAdjointPacket s - paretoMellin v s = _
    rw [hnull, sub_zero]
  have h := paretoMellin_norm_sq_le_of_head_zero (parityAdjointPacket - v) s hs N hN hH
  rw [hM] at h
  have hlow := parityAdjointPacket_mellin_norm_lower s hs
  have hb : ((1 / 6 : ℝ) * (1 / ‖s‖))^2 ≤ ‖paretoMellin parityAdjointPacket s‖^2 := by
    exact pow_le_pow_left₀ (by positivity) hlow 2
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hd : 0 < 2 * s.re - 1 := by linarith
  have hp : 0 < (N : ℝ)^(2 * s.re - 1) := Real.rpow_pos_of_pos hn _
  have hmul := hb.trans h
  rw [show 1 - 2*s.re = -(2*s.re - 1) by ring, Real.rpow_neg hn.le] at hmul
  apply (le_div_iff₀ hp).mp
  apply (le_div_iff₀ hd).mp
  simpa only [div_eq_mul_inv, mul_assoc] using hmul

end RiemannResearch.RH.Pareto.PrimePowerSchur
