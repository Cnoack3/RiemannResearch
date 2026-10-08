/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PhysicalSourceLimits

/-!
# Quantitative unconditional physical source bounds

For a legal physical packet set containing a prime p, the mean dual and the
actual projection bound control the logarithmic charge and the complete shifted
mixed-source square by explicit prime-dependent bounds. The sharper estimates
retain p/(p-1)^2; simpler estimates use 1/p.

The exact signed identity being estimated is the previously established
definition shiftedDeterminant = A*C - (2*pi+B)^2. Its square is retained here.
These rates do not give a rate for the normalized signed correction, whose
denominator -A is also tending to zero, and do not identify the charge endpoint.

Source: independently developed quantitative consequences of the verified
PhysicalSourceLimits.determinant_prime_bound and
PhysicalSourceProjection.logarithmicCharge_control.
-/

noncomputable section
open Matrix Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.PhysicalSourceRates
open PhysicalPacketCore PhysicalSchurCoupling PhysicalSourceProjection PhysicalSourceLimits

theorem logarithmicCharge_prime_bound (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ q ∈ s, q.Prime ∧ 2 < q)
    (p : ℕ) (hp : p.Prime) (hps : p ∈ s) :
    -logarithmicCharge s <
      4 * (-inverseCharge s) * (p : ℝ) / (3 * ((p : ℝ) - 1) ^ 2) := by
  have hp1 : 0 < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hp.one_lt)
  calc
    -logarithmicCharge s ≤ shiftedDeterminant s / (4 * Real.pi) :=
      (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mpr
        (by nlinarith only [logarithmicCharge_control s hs ho])
    _ < (16 * Real.pi * (-inverseCharge s) * (p : ℝ) /
        (3 * ((p : ℝ) - 1) ^ 2)) / (4 * Real.pi) :=
      div_lt_div_of_pos_right (determinant_prime_bound s hs ho p hp hps) (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero, ne_of_gt hp1]; ring

theorem logarithmicCharge_prime_inv_bound (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ q ∈ s, q.Prime ∧ 2 < q)
    (p : ℕ) (hp : p.Prime) (hps : p ∈ s) :
    -logarithmicCharge s < 16 * (-inverseCharge s) / (3 * (p : ℝ)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  calc
    -logarithmicCharge s ≤ shiftedDeterminant s / (4 * Real.pi) :=
      (le_div_iff₀ (by positivity : 0 < 4 * Real.pi)).mpr
        (by nlinarith only [logarithmicCharge_control s hs ho])
    _ < (64 * Real.pi * (-inverseCharge s) / (3 * (p : ℝ))) /
        (4 * Real.pi) :=
      div_lt_div_of_pos_right (determinant_prime_inv_bound s hs ho p hp hps) (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero, ne_of_gt hpR]; ring

theorem mixedCharge_prime_bound (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ q ∈ s, q.Prime ∧ 2 < q)
    (p : ℕ) (hp : p.Prime) (hps : p ∈ s) :
    (2 * Real.pi + mixedCharge s) ^ 2 <
      4 * inverseCharge s ^ 2 * (p : ℝ) / (3 * ((p : ℝ) - 1) ^ 2) := by
  have hC := inverseCharge_neg s hs ho
  have hT := shiftedDeterminant_pos s hs ho
  unfold shiftedDeterminant at hT
  calc
    (2 * Real.pi + mixedCharge s) ^ 2 <
        (-logarithmicCharge s) * (-inverseCharge s) := by nlinarith only [hT]
    _ < (4 * (-inverseCharge s) * (p : ℝ) /
        (3 * ((p : ℝ) - 1) ^ 2)) * (-inverseCharge s) :=
      mul_lt_mul_of_pos_right (logarithmicCharge_prime_bound s hs ho p hp hps)
        (neg_pos.mpr hC)
    _ = _ := by ring

theorem mixedCharge_prime_inv_bound (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (ho : ∃ q ∈ s, q.Prime ∧ 2 < q)
    (p : ℕ) (hp : p.Prime) (hps : p ∈ s) :
    (2 * Real.pi + mixedCharge s) ^ 2 <
      16 * inverseCharge s ^ 2 / (3 * (p : ℝ)) := by
  have hC := inverseCharge_neg s hs ho
  have hT := shiftedDeterminant_pos s hs ho
  unfold shiftedDeterminant at hT
  calc
    (2 * Real.pi + mixedCharge s) ^ 2 <
        (-logarithmicCharge s) * (-inverseCharge s) := by nlinarith only [hT]
    _ < (16 * (-inverseCharge s) / (3 * (p : ℝ))) * (-inverseCharge s) :=
      mul_lt_mul_of_pos_right (logarithmicCharge_prime_inv_bound s hs ho p hp hps)
        (neg_pos.mpr hC)
    _ = _ := by ring

theorem prime_mem_primorialPackets (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n + 3) :
    p ∈ primorialPackets n := by
  change p ∈ divisorPackets (SquarefreeStageExhaustion.primorialPeriod n)
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_divisors.mpr ⟨?_,
    ne_of_gt (SquarefreeStageExhaustion.primorialPeriod_pos n)⟩, hp.one_lt⟩
  exact dvd_trans hp.squarefree.dvd_primorial (primorial_dvd_primorial hpn)

theorem primorial_logarithmicCharge_prime_inv_bound (n p : ℕ)
    (hp : p.Prime) (hps : p ∈ primorialPackets n) :
    -logarithmicCharge (primorialPackets n) <
      128 * Real.sqrt 3 / (3 * (p : ℝ)) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  calc
    -logarithmicCharge (primorialPackets n) <
        16 * (-inverseCharge (primorialPackets n)) / (3 * (p : ℝ)) :=
      logarithmicCharge_prime_inv_bound _ (primorialPackets_legal n)
        (primorialPackets_odd n) p hp hps
    _ ≤ 16 * (8 * Real.sqrt 3) / (3 * (p : ℝ)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (primorialPackets_charge_bound n) (by norm_num))
        (by positivity)
    _ = _ := by ring

theorem primorial_charge_sq_le (n : ℕ) :
    inverseCharge (primorialPackets n) ^ 2 ≤ 192 := by
  have hC := inverseCharge_neg _ (primorialPackets_legal n) (primorialPackets_odd n)
  have hbound := primorialPackets_charge_bound n
  have hmul := mul_le_mul hbound hbound (neg_nonneg.mpr hC.le)
    (by positivity : 0 ≤ 8 * Real.sqrt 3)
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith only [hmul, hsqrt]

theorem primorial_mixedCharge_prime_inv_bound (n p : ℕ)
    (hp : p.Prime) (hps : p ∈ primorialPackets n) :
    (2 * Real.pi + mixedCharge (primorialPackets n)) ^ 2 < 1024 / (p : ℝ) := by
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  calc
    (2 * Real.pi + mixedCharge (primorialPackets n)) ^ 2 <
        16 * inverseCharge (primorialPackets n) ^ 2 / (3 * (p : ℝ)) :=
      mixedCharge_prime_inv_bound _ (primorialPackets_legal n)
        (primorialPackets_odd n) p hp hps
    _ ≤ 16 * 192 / (3 * (p : ℝ)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (primorial_charge_sq_le n) (by norm_num)) (by positivity)
    _ = _ := by field_simp [ne_of_gt hpR]; ring

/-- Actual primorial application: legalness, inertia, uniform charge bounds,
and prime membership are discharged internally from finite arithmetic input. -/
theorem primorial_source_rates (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n + 3) :
    0 < -logarithmicCharge (primorialPackets n) ∧
      -logarithmicCharge (primorialPackets n) < 128 * Real.sqrt 3 / (3 * (p : ℝ)) ∧
      (2 * Real.pi + mixedCharge (primorialPackets n)) ^ 2 < 1024 / (p : ℝ) := by
  have hps := prime_mem_primorialPackets n p hp hpn
  exact ⟨neg_pos.mpr (logarithmicCharge_neg _
    (primorialPackets_legal n) (primorialPackets_odd n)),
    primorial_logarithmicCharge_prime_inv_bound n p hp hps,
    primorial_mixedCharge_prime_inv_bound n p hp hps⟩

end RiemannResearch.RH.Pareto.PhysicalSourceRates
