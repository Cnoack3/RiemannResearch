/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusCapacityDensity
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.CanonicalMobiusCapacityBounds
import RiemannResearch.RH.ResidueClosureDensity

/-!
# Finite-head dilation and quantitative residual positivity

Source: user-provided Exact Schur Continuation handoff, Section 13,
for the finite head indicator and capacity problem. The proof extends the
project's first-coordinate dilation argument to every finite positive head.
No density, RH, or asymptotic arithmetic hypothesis is assumed.
-/

noncomputable section
open Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem finiteHeadIndicator_eq_dilation_difference (N : ℕ) :
    finiteHeadIndicator N = hilbertOne -
      (((N + 1 : ℕ) : ℝ)⁻¹) • hilbertDilation (N + 1) (by omega) hilbertOne := by
  apply hilbertSequence_injective
  funext k
  change hilbertSequence (finiteHeadIndicator N) k = hilbertSequenceLinear (_ - _) k
  rw [map_sub]
  change hilbertSequence (finiteHeadIndicator N) k = hilbertSequence hilbertOne k -
    hilbertSequence ((((N + 1 : ℕ) : ℝ)⁻¹) •
      hilbertDilation (N + 1) (by omega) hilbertOne) k
  rw [hilbertSequence_smul, hilbertDilation_sequence, hilbertOne_sequence]
  have hB : (N : ℝ) + 1 ≠ 0 := by positivity
  cases k with
  | zero => simp [hilbertSequence_zero, dilation, zeroAnchor]
  | succ n =>
    rw [finiteHeadIndicator_sequence_succ]
    by_cases hn : n < N
    · have hdiv : (n + 1) / (N + 1) = 0 := Nat.div_eq_of_lt (by omega)
      simp [dilation, zeroAnchor, hn, hdiv]
    · have hdiv : (n + 1) / (N + 1) ≠ 0 :=
        Nat.ne_of_gt (Nat.div_pos (by omega) (by omega))
      simp [dilation, zeroAnchor, hn, hdiv, hB]

theorem finiteHead_residual_inner_identity (N : ℕ) :
    inner ℝ limitResidual (finiteHeadIndicator N) = limitEnergy -
      (((N + 1 : ℕ) : ℝ)⁻¹) *
        inner ℝ limitResidual (hilbertDilation (N + 1) (by omega) limitResidual) := by
  rw [finiteHeadIndicator_eq_dilation_difference, inner_sub_right, inner_smul_right,
    limitResidual_inner_one, limitResidual_inner_dilation_one]

theorem finiteHead_residual_inner_bounds (N : ℕ) :
    (((N + 1 : ℕ) : ℝ) - Real.sqrt (N + 1 : ℕ)) * limitEnergy ≤
      ((N + 1 : ℕ) : ℝ) * inner ℝ limitResidual (finiteHeadIndicator N) ∧
    ((N + 1 : ℕ) : ℝ) * inner ℝ limitResidual (finiteHeadIndicator N) ≤
      (((N + 1 : ℕ) : ℝ) + Real.sqrt (N + 1 : ℕ)) * limitEnergy := by
  have h := norm_inner_le_norm (𝕜 := ℝ) limitResidual
    (hilbertDilation (N + 1) (by omega) limitResidual)
  rw [hilbertDilation_norm, Real.norm_eq_abs] at h
  have hb : |inner ℝ limitResidual
      (hilbertDilation (N + 1) (by omega) limitResidual)| ≤
      Real.sqrt (N + 1 : ℕ) * limitEnergy := by
    calc
      _ ≤ ‖limitResidual‖ * (Real.sqrt (N + 1 : ℕ) * ‖limitResidual‖) := h
      _ = Real.sqrt (N + 1 : ℕ) * ‖limitResidual‖ ^ 2 := by ring
      _ = _ := rfl
  have hB : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have he : ((N + 1 : ℕ) : ℝ) * inner ℝ limitResidual (finiteHeadIndicator N) =
      ((N + 1 : ℕ) : ℝ) * limitEnergy -
        inner ℝ limitResidual (hilbertDilation (N + 1) (by omega) limitResidual) := by
    rw [finiteHead_residual_inner_identity]
    field_simp
  constructor <;> nlinarith [(abs_le.mp hb).1, (abs_le.mp hb).2]

theorem finiteHeadIndicator_mem_iff_one_mem (N : ℕ) (hN : 0 < N) :
    finiteHeadIndicator N ∈ closedSpace ↔ hilbertOne ∈ closedSpace := by
  constructor
  · intro hmem
    have ho := (closedSpace.mem_orthogonal _).mp limitResidual_mem_orthogonal _ hmem
    rw [real_inner_comm] at ho
    have hb := (finiteHead_residual_inner_bounds N).1
    rw [ho, mul_zero] at hb
    have hB : (1 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < N + 1)
    have hs : Real.sqrt (N + 1 : ℕ) < ((N + 1 : ℕ) : ℝ) := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg (N + 1)), Real.sqrt_nonneg (N + 1 : ℕ)]
    have he : 0 ≤ limitEnergy := sq_nonneg _
    have hz : limitEnergy = 0 := by nlinarith
    exact limitEnergy_zero_iff_mem.mp hz
  · intro hmem
    rw [finiteHeadIndicator_eq_dilation_difference]
    exact closedSpace.sub_mem hmem
      (closedSpace.smul_mem _ (closedSpace_dilation hmem (N + 1) (by omega)))

theorem finiteHeadIndicator_mem_iff_density (N : ℕ) (hN : 0 < N) :
    finiteHeadIndicator N ∈ closedSpace ↔ closedSpace = ⊤ :=
  (finiteHeadIndicator_mem_iff_one_mem N hN).trans closedSpace_eq_top_iff_one_mem.symm

theorem finiteHead_residual_inner_eq_pairing (N : ℕ) :
    inner ℝ limitResidual (finiteHeadIndicator N) = residualHeadPairing N := by
  unfold finiteHeadIndicator residualHeadPairing
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [inner_paretoPoint]
  change paretoWeight n * (limitResidual n / Real.sqrt (paretoWeight n)) =
    limitResidual n * (Real.sqrt (paretoWeight n) * zeroAnchor (fun _ => (1 : ℝ)) (n + 1))
  simp only [zeroAnchor, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, mul_one]
  have hw := Real.sq_sqrt (le_of_lt (paretoWeight_pos n))
  have hs : Real.sqrt (paretoWeight n) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (paretoWeight_pos n))
  calc
    _ = limitResidual n * (Real.sqrt (paretoWeight n) ^ 2) / Real.sqrt (paretoWeight n) := by
      rw [hw]
      ring
    _ = _ := by field_simp

theorem residualHeadPairing_pos (N : ℕ) (hN : 0 < N) (hpos : 0 < limitEnergy) :
    0 < residualHeadPairing N := by
  have hb := (finiteHead_residual_inner_bounds N).1
  rw [finiteHead_residual_inner_eq_pairing] at hb
  have hB : (1 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < N + 1)
  have hs : Real.sqrt (N + 1 : ℕ) < ((N + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (N + 1)), Real.sqrt_nonneg (N + 1 : ℕ)]
  have hmul : 0 < ((N + 1 : ℕ) : ℝ) * residualHeadPairing N :=
    lt_of_lt_of_le (mul_pos (sub_pos.mpr hs) hpos) hb
  nlinarith

namespace SignedCovariance
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Every positive head, with an explicit constant and no eventual cutoff. -/
theorem capacity_fixed_head_residual_bound (N : ℕ) (hN : 0 < N)
    (hpos : 0 < limitEnergy) (k : ι → ℕ) (hk : ∀ i, 0 < k i)
    (hindex : ∀ i, N ≤ k i) :
    capacity N k hk ≤
      (((N + 1 : ℕ) : ℝ) ^ 2 * residualTailEnergy N) /
        ((((N + 1 : ℕ) : ℝ) - Real.sqrt (N + 1 : ℕ)) * limitEnergy) ^ 2 := by
  have hB : (1 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < N + 1)
  have hs : Real.sqrt (N + 1 : ℕ) < ((N + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (N + 1)), Real.sqrt_nonneg (N + 1 : ℕ)]
  have hlo : 0 < (((N + 1 : ℕ) : ℝ) - Real.sqrt (N + 1 : ℕ)) * limitEnergy :=
    mul_pos (sub_pos.mpr hs) hpos
  have hb := (finiteHead_residual_inner_bounds N).1
  rw [finiteHead_residual_inner_eq_pairing] at hb
  have hsq : ((((N + 1 : ℕ) : ℝ) - Real.sqrt (N + 1 : ℕ)) * limitEnergy) ^ 2 ≤
      (((N + 1 : ℕ) : ℝ) * residualHeadPairing N) ^ 2 :=
    (sq_le_sq₀ hlo.le (hlo.le.trans hb)).mpr hb
  have hc := capacity_mul_residual_head_sq_le N k hk hindex
  have hmul : capacity N k hk *
      ((((N + 1 : ℕ) : ℝ) - Real.sqrt (N + 1 : ℕ)) * limitEnergy) ^ 2 ≤
        ((N + 1 : ℕ) : ℝ) ^ 2 * residualTailEnergy N := by
    calc
      _ ≤ capacity N k hk * (((N + 1 : ℕ) : ℝ) * residualHeadPairing N) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (capacity_pos N k hk).le
      _ = ((N + 1 : ℕ) : ℝ) ^ 2 * (capacity N k hk * residualHeadPairing N ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
  exact (le_div_iff₀ (sq_pos_of_pos hlo)).mpr hmul

end SignedCovariance

end RiemannResearch.RH.Pareto.CoefficientStabilization
