/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.BalazardReciprocalCharge
import RiemannResearch.RH.CanonicalMobiusTriangular
import RiemannResearch.RH.CanonicalMobiusSingleHeadCapacity

/-!
# Reciprocal charges dual to adjacent residue innovations

Source: the exact Mobius/residue coefficient identities and Balazard bound
already formalized in this repository, combined with elementary orthogonal
projection and Cauchy--Schwarz. This directed continuation is dated
24 September 2026; no novelty claim is made.

A reciprocal charge pairs to one with its adjacent residue step and to zero
with the preceding legal span. The uniform charge energy bound of 42 gives
a lower bound 1/42 for the FULL-SPACE innovation energy. This is not a
lower bound for the different tail-screened capacity denominator.
No target source-divergence or unconditional RH theorem is asserted.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

theorem reciprocalChargeRiesz_inner_residue (K d : ℕ) (hK : 0 < K) (hd : 2 ≤ d) :
    inner ℝ (reciprocalChargeRiesz K) (normalizedResidueHilbert d (by omega)) =
      (if d ≤ K then 0 else (1 / (d : ℝ))) := by
  rw [reciprocalChargeRiesz_inner]
  have hterm (m : ℕ) (hm : m ∈ Finset.Icc 1 K) :
      mobiusDifferenceCLM m (normalizedResidueHilbert d (by omega)) / (m : ℝ) =
      (if m = 1 then 1 / (d : ℝ) else 0) -
        (if m = d then 1 / (d : ℝ) else 0) := by
    by_cases h1 : m = 1
    · subst m
      simp [mobiusDifferenceCLM_apply, mobiusDifference,
        normalizedResidueHilbert_sequence, residueFraction, Nat.mod_eq_of_lt (by omega : 1 < d),
        show (1 : ℕ) ≠ d by omega]
    · rw [mobius_normalizedResidue m d (by have := (Finset.mem_Icc.mp hm).1; omega)]
      by_cases hmd : m = d
      · subst m
        simp [h1, div_eq_mul_inv]
      · simp [hmd, h1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_Icc]
  have h1K : 1 ≤ K := hK
  by_cases hdK : d ≤ K
  · simp [hdK, h1K, show 1 ≤ d by omega]
  · simp [hdK, h1K]

theorem reciprocalChargeRiesz_inner_consecutive (M : ℕ) (hM : 1 ≤ M) :
    inner ℝ (reciprocalChargeRiesz (M + 1)) (consecutiveResidueHilbert M) = 1 := by
  rw [consecutiveResidueHilbert, inner_sub_right, inner_smul_right, inner_smul_right,
    reciprocalChargeRiesz_inner_residue (M + 1) (M + 2) (by omega) (by omega),
    reciprocalChargeRiesz_inner_residue (M + 1) (M + 1) (by omega) (by omega)]
  simp only [show ¬ M + 2 ≤ M + 1 by omega, if_false, le_refl, if_true,
    mul_zero, sub_zero]
  field_simp

theorem reciprocalChargeRiesz_consecutive_biorthogonal
    (K M : ℕ) (hK : 0 < K) (hM : 1 ≤ M) :
    inner ℝ (reciprocalChargeRiesz K) (consecutiveResidueHilbert M) =
      if K = M + 1 then 1 else 0 := by
  by_cases he : K = M + 1
  · subst K
    simpa using reciprocalChargeRiesz_inner_consecutive M hM
  rw [if_neg he, consecutiveResidueHilbert, inner_sub_right,
    inner_smul_right, inner_smul_right,
    reciprocalChargeRiesz_inner_residue K (M + 2) hK (by omega),
    reciprocalChargeRiesz_inner_residue K (M + 1) hK (by omega)]
  by_cases hhi : M + 2 ≤ K
  · simp [hhi, show M + 1 ≤ K by omega]
  · simp only [if_neg hhi, if_neg (show ¬ M + 1 ≤ K by omega)]
    have h1 : ((M + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have h2 : ((M + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    norm_num

end RiemannResearch.RH.Pareto
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

theorem reciprocalChargeRiesz_mem_finiteSpace_orthogonal
    (K M : ℕ) (hKM : M + 1 ≤ K) :
    reciprocalChargeRiesz K ∈ (finiteSpace M)ᗮ := by
  apply ((finiteSpace M).mem_orthogonal _).mpr
  intro x hx
  rw [real_inner_comm]
  obtain ⟨a, rfl⟩ := finiteSpace_expansion M x hx
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [inner_smul_right, residueAtom,
    reciprocalChargeRiesz_inner_residue K (i.val + 2) (by omega) (by omega),
    if_pos (by have := i.isLt; omega), mul_zero]

/-- The full-space innovation of an adjacent step has a uniform positive energy. -/
theorem consecutiveResidue_full_innovation_energy_lower (M : ℕ) (hM : 1 ≤ M) :
    (1 / 42 : ℝ) ≤
      ‖consecutiveResidueHilbert M -
        (finiteSpace M).starProjection (consecutiveResidueHilbert M)‖ ^ 2 := by
  let z := consecutiveResidueHilbert M -
    (finiteSpace M).starProjection (consecutiveResidueHilbert M)
  have ho : inner ℝ (reciprocalChargeRiesz (M + 1))
      ((finiteSpace M).starProjection (consecutiveResidueHilbert M)) = 0 := by
    rw [real_inner_comm]
    exact ((finiteSpace M).mem_orthogonal _).mp
      (reciprocalChargeRiesz_mem_finiteSpace_orthogonal (M + 1) M le_rfl) _
      ((finiteSpace M).starProjection_apply_mem _)
  have he : inner ℝ (reciprocalChargeRiesz (M + 1)) z = 1 := by
    dsimp [z]
    rw [inner_sub_right, reciprocalChargeRiesz_inner_consecutive M hM, ho, sub_zero]
  have hc := real_inner_mul_inner_self_le (reciprocalChargeRiesz (M + 1)) z
  rw [he, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hc
  have hb := reciprocalChargeRiesz_norm_sq_le (M + 1)
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖z‖)
  change (1 / 42 : ℝ) ≤ ‖z‖ ^ 2
  nlinarith

end RiemannResearch.RH.Pareto.CoefficientStabilization
