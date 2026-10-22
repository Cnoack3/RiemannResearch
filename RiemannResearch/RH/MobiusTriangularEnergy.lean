/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.MobiusTriangularCharge
import RiemannResearch.RH.MobiusReciprocalChargeBridge
import RiemannResearch.Analysis.TriangularOverlapKernel
import RiemannResearch.Analysis.QuotientFiberRamps
import RiemannResearch.Analysis.FiniteKernelEnergy
import RiemannResearch.Analysis.BoundedSquareEnergy
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Strong triangular reciprocal-dual convergence

Source: extension derived from Michel Balazard, arXiv:1812.04309,
Propositions 6--7, with the full argument in
BalazardTriangularResearch20261019.md. The paper supplies the dual
system and its weak convergence; the finite ramp proof here establishes
the triangular strong limit and its exact variance remainder.

All overlap and arithmetic providers are proved. The only asymptotic
input is the established unconditional reciprocal-Mobius limit, imported
through MobiusTriangularCharge. No RH or approximation-energy bound is
assumed. The actual squarefree Q application is in QTriangularCharge.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

theorem triangularChargeRiesz_sequence_ramps (N k : ℕ) (hk : 0 < k) :
    hilbertSequence (triangularChargeRiesz N) k =
      (k : ℝ) * ((k : ℝ) + 1) / (N : ℝ) *
        ∑ j ∈ Finset.range N,
          (unitRamp j ((N : ℝ) / k) - unitRamp j ((N : ℝ) / ((k : ℝ) + 1))) *
            mobiusReciprocalSum j := by
  rw [← anchoredEvaluationCLM_apply]
  simp only [triangularChargeRiesz, map_smul, map_sum, smul_eq_mul,
    anchoredEvaluationCLM_apply]
  simp_rw [reciprocalChargeRiesz_sequence _ k hk]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.sum_div]
  rw [sum_range_quotient_ramps N k hk mobiusReciprocalSum,
    sum_range_quotient_ramps N (k + 1) (by omega) mobiusReciprocalSum]
  simp only [Nat.cast_add, Nat.cast_one]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  have hk1R : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [mul_div_cancel_left₀ _ hkR, mul_div_cancel_left₀ _ hk1R]
  ring

end RiemannResearch.RH.Pareto



noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Pareto

/-- The triangular average has no physical coordinates at or beyond its cutoff. -/
theorem triangularChargeRiesz_sequence_zero_of_le (N k : ℕ) (hNk : N ≤ k) :
    hilbertSequence (triangularChargeRiesz N) k = 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  rw [← anchoredEvaluationCLM_apply]
  simp only [triangularChargeRiesz, map_smul, map_sum, smul_eq_mul,
    anchoredEvaluationCLM_apply]
  have hz : (∑ j ∈ Finset.range N,
      hilbertSequence (reciprocalChargeRiesz j) k) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j < k := lt_of_lt_of_le (Finset.mem_range.mp hj) hNk
    have hjk1 : j < k + 1 := by omega
    rw [reciprocalChargeRiesz_sequence j k (Nat.pos_of_ne_zero hk)]
    simp [Nat.div_eq_of_lt hjk, Nat.div_eq_of_lt hjk1, mobiusReciprocalSum]
  rw [hz, mul_zero]

/-- Complete Hilbert energy equals the finite physical head energy. -/
theorem triangularChargeRiesz_norm_sq_eq_fin (n : ℕ) :
    ‖triangularChargeRiesz (n + 1)‖ ^ 2 =
      ∑ i : Fin n, positiveWeight (i.val + 1) *
        hilbertSequence (triangularChargeRiesz (n + 1)) (i.val + 1) ^ 2 := by
  rw [hilbert_norm_weighted_sq]
  rw [tsum_eq_sum (s := Finset.Icc 1 n) (by
    intro k hk
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hnk : n + 1 ≤ k := by
        have hn : ¬ (1 ≤ k ∧ k ≤ n) := by
          simpa only [Finset.mem_Icc] using hk
        omega
      rw [triangularChargeRiesz_sequence_zero_of_le (n + 1) k hnk]
      simp)]
  refine Finset.sum_bij
    (fun k hk => (⟨k - 1, by have := Finset.mem_Icc.mp hk; omega⟩ : Fin n))
    (by intros; simp) ?_ ?_ ?_
  · intro k hk l hl hkl
    have he := congrArg Fin.val hkl
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hl1 := (Finset.mem_Icc.mp hl).1
    dsimp at he
    omega
  · intro i hi
    refine ⟨i.val + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    apply Fin.ext
    simp
  · intro k hk
    have hsucc : k - 1 + 1 = k := by
      have := (Finset.mem_Icc.mp hk).1
      omega
    simp only [hsucc]

/-- The zero reciprocal Möbius value contributes no endpoint term. -/
theorem reciprocalMobiusCesaroEnergy_eq_fin (n : ℕ) :
    reciprocalMobiusCesaroEnergy (n + 1) =
      ∑ j : Fin n, (1 / ((n + 1 : ℕ) : ℝ)) *
        mobiusReciprocalSum (j.val + 1) ^ 2 := by
  unfold reciprocalMobiusCesaroEnergy
  rw [Finset.sum_range_succ']
  have hz : mobiusReciprocalSum 0 = 0 := by simp [mobiusReciprocalSum]
  simp only [hz, zero_pow (by decide : 2 ≠ 0), add_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [one_div, Finset.mul_sum]

/-- Exact energy identity, ready to consume the concrete overlap mean bridge.
The kernel marginals and nonnegativity are supplied by the overlap module. -/
private theorem triangularChargeRiesz_energy_identity_of_kernel
    (n : ℕ) (ℓ : Fin n → Fin n → ℝ)
    (hrow : ∀ i, ∑ j, ℓ i j = positiveWeight (i.val + 1))
    (hcol : ∀ j, ∑ i, ℓ i j = 1 / ((n + 1 : ℕ) : ℝ))
    (hmean : ∀ i, ∑ j, ℓ i j * mobiusReciprocalSum (j.val + 1) =
      positiveWeight (i.val + 1) *
        hilbertSequence (triangularChargeRiesz (n + 1)) (i.val + 1)) :
    reciprocalMobiusCesaroEnergy (n + 1) =
      ‖triangularChargeRiesz (n + 1)‖ ^ 2 +
        ∑ i, ∑ j, ℓ i j *
          (mobiusReciprocalSum (j.val + 1) -
            hilbertSequence (triangularChargeRiesz (n + 1)) (i.val + 1)) ^ 2 := by
  rw [reciprocalMobiusCesaroEnergy_eq_fin, triangularChargeRiesz_norm_sq_eq_fin]
  exact RiemannResearch.Analysis.finite_kernel_variance_identity ℓ
    (fun i => positiveWeight (i.val + 1))
    (fun _ => 1 / ((n + 1 : ℕ) : ℝ))
    (fun i => hilbertSequence (triangularChargeRiesz (n + 1)) (i.val + 1))
    (fun j => mobiusReciprocalSum (j.val + 1)) hrow hcol hmean

/-- Norm bound from the exact finite identity, with no omitted tail. -/
private theorem triangularChargeRiesz_norm_sq_le_of_kernel
    (n : ℕ) (ℓ : Fin n → Fin n → ℝ)
    (hℓ : ∀ i j, 0 ≤ ℓ i j)
    (hrow : ∀ i, ∑ j, ℓ i j = positiveWeight (i.val + 1))
    (hcol : ∀ j, ∑ i, ℓ i j = 1 / ((n + 1 : ℕ) : ℝ))
    (hmean : ∀ i, ∑ j, ℓ i j * mobiusReciprocalSum (j.val + 1) =
      positiveWeight (i.val + 1) *
        hilbertSequence (triangularChargeRiesz (n + 1)) (i.val + 1)) :
    ‖triangularChargeRiesz (n + 1)‖ ^ 2 ≤
      reciprocalMobiusCesaroEnergy (n + 1) := by
  rw [reciprocalMobiusCesaroEnergy_eq_fin, triangularChargeRiesz_norm_sq_eq_fin]
  exact RiemannResearch.Analysis.finite_kernel_energy_le ℓ
    (fun i => positiveWeight (i.val + 1))
    (fun _ => 1 / ((n + 1 : ℕ) : ℝ))
    (fun i => hilbertSequence (triangularChargeRiesz (n + 1)) (i.val + 1))
    (fun j => mobiusReciprocalSum (j.val + 1)) hℓ hrow hcol hmean

/-- The arithmetic majorant implies actual strong convergence. -/
private theorem triangularChargeRiesz_tendsto_zero_of_bound
    (hbound : ∀ N, ‖triangularChargeRiesz N‖ ^ 2 ≤
      reciprocalMobiusCesaroEnergy N) :
    Tendsto triangularChargeRiesz atTop (𝓝 (0 : ThresholdHilbert)) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact RiemannResearch.Analysis.BoundedSquareEnergy.tendsto_zero_of_square_le
    (fun N => ‖triangularChargeRiesz N‖) reciprocalMobiusCesaroEnergy
    reciprocalMobiusCesaroEnergy_tendsto_zero hbound

/-- Bounded moving vectors need no convergence hypothesis once the dual is strong-null. -/
private theorem triangularChargeRiesz_inner_moving_tendsto_zero_of_strong
    (hstrong : Tendsto triangularChargeRiesz atTop (𝓝 (0 : ThresholdHilbert)))
    (f : ℕ → ThresholdHilbert) (C : ℝ)
    (hf : ∀ N, ‖f N‖ ≤ C) :
    Tendsto (fun N => inner ℝ (triangularChargeRiesz N) (f N))
      atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => ‖triangularChargeRiesz N‖ * C)
      atTop (𝓝 0) := by
    simpa only [norm_zero, zero_mul] using hstrong.norm.mul_const C
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hupper
  intro N
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
    (mul_le_mul_of_nonneg_left (hf N) (norm_nonneg _))

/-- Square form of the explicit bound avoids unnecessary square-root algebra. -/
private theorem triangularChargeRiesz_inner_sq_le_of_bound
    (hbound : ∀ N, ‖triangularChargeRiesz N‖ ^ 2 ≤
      reciprocalMobiusCesaroEnergy N) (N : ℕ) (f : ThresholdHilbert) :
    (inner ℝ (triangularChargeRiesz N) f) ^ 2 ≤
      reciprocalMobiusCesaroEnergy N * ‖f‖ ^ 2 := by
  have hCS := norm_inner_le_norm (𝕜 := ℝ) (triangularChargeRiesz N) f
  rw [Real.norm_eq_abs] at hCS
  have hCS2 := (sq_le_sq₀ (abs_nonneg (inner ℝ (triangularChargeRiesz N) f))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hCS
  rw [sq_abs, mul_pow] at hCS2
  exact hCS2.trans (mul_le_mul_of_nonneg_right (hbound N) (sq_nonneg _))

-- Concrete final assembly, after importing the arithmetic/kernel modules.
open RiemannResearch.Analysis

theorem reciprocalOverlap_triangular_mean (n : ℕ) (i : Fin n) :
    (∑ j : Fin n, reciprocalOverlap n i j * mobiusReciprocalSum (j.val + 1)) =
      positiveWeight (i.val + 1) *
        hilbertSequence (triangularChargeRiesz (n + 1)) (i.val + 1) := by
  rw [triangularChargeRiesz_sequence_ramps (n + 1) (i.val + 1) (by omega)]
  rw [Finset.sum_range_succ']
  have hz : mobiusReciprocalSum 0 = 0 := by simp [mobiusReciprocalSum]
  simp only [hz, mul_zero, add_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  unfold reciprocalOverlap decreasingRampKernel reciprocalCut positiveWeight
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hi : (((i.val + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hi' : (((i.val + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  simp only [Nat.add_assoc]
  push_cast at *
  field_simp [hn, hi, hi']; ring

def triangularChargeVariance (n : ℕ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, reciprocalOverlap n i j *
    (mobiusReciprocalSum (j.val + 1) -
      hilbertSequence (triangularChargeRiesz (n + 1)) (i.val + 1)) ^ 2

theorem triangularChargeRiesz_energy_identity (n : ℕ) :
    reciprocalMobiusCesaroEnergy (n + 1) =
      ‖triangularChargeRiesz (n + 1)‖ ^ 2 + triangularChargeVariance n := by
  apply triangularChargeRiesz_energy_identity_of_kernel n (reciprocalOverlap n)
  · intro i
    rw [reciprocalOverlap_row]
    unfold positiveWeight
    push_cast
    ring
  · exact reciprocalOverlap_col n
  · exact reciprocalOverlap_triangular_mean n

theorem triangularChargeVariance_nonneg (n : ℕ) : 0 ≤ triangularChargeVariance n := by
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (reciprocalOverlap_nonneg n i j) (sq_nonneg _)

theorem triangularChargeRiesz_norm_sq_le (N : ℕ) :
    ‖triangularChargeRiesz N‖ ^ 2 ≤ reciprocalMobiusCesaroEnergy N := by
  cases N with
  | zero => simp [triangularChargeRiesz, reciprocalMobiusCesaroEnergy]
  | succ n =>
      have hid := triangularChargeRiesz_energy_identity n
      have hv := triangularChargeVariance_nonneg n
      linarith

theorem triangularChargeRiesz_tendsto_zero :
    Tendsto triangularChargeRiesz atTop (𝓝 (0 : ThresholdHilbert)) :=
  triangularChargeRiesz_tendsto_zero_of_bound triangularChargeRiesz_norm_sq_le

theorem triangularChargeRiesz_inner_moving_tendsto_zero
    (f : ℕ → ThresholdHilbert) (C : ℝ) (hf : ∀ N, ‖f N‖ ≤ C) :
    Tendsto (fun N => inner ℝ (triangularChargeRiesz N) (f N))
      atTop (𝓝 0) :=
  triangularChargeRiesz_inner_moving_tendsto_zero_of_strong
    triangularChargeRiesz_tendsto_zero f C hf

theorem mobiusDifference_triangular_moving_tendsto_zero
    (f : ℕ → ThresholdHilbert) (C : ℝ) (hf : ∀ N, ‖f N‖ ≤ C) :
    Tendsto (fun N : ℕ => ∑ d ∈ Finset.Icc 1 N,
      (1 - (d : ℝ) / (N : ℝ)) * mobiusDifferenceCLM d (f N) / (d : ℝ))
      atTop (𝓝 0) := by
  simpa only [triangularChargeRiesz_inner] using
    triangularChargeRiesz_inner_moving_tendsto_zero f C hf

/-- Even unbounded moving tests are permitted when their energy growth is
absorbed by the proved arithmetic decay. -/
theorem triangularChargeRiesz_inner_moving_tendsto_zero_of_energy
    (f : ℕ → ThresholdHilbert)
    (hf : Tendsto (fun N => reciprocalMobiusCesaroEnergy N * ‖f N‖ ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun N => inner ℝ (triangularChargeRiesz N) (f N))
      atTop (𝓝 0) := by
  apply RiemannResearch.Analysis.BoundedSquareEnergy.tendsto_zero_of_square_le
    (fun N => inner ℝ (triangularChargeRiesz N) (f N))
    (fun N => reciprocalMobiusCesaroEnergy N * ‖f N‖ ^ 2) hf
  intro N
  exact triangularChargeRiesz_inner_sq_le_of_bound triangularChargeRiesz_norm_sq_le N (f N)

end RiemannResearch.RH.Pareto
