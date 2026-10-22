/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QDivisibilityDensity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Infinite-conductor limits in the actual Q norm

Source: user-provided `Squarefree_Infinite_CRT_Continuation_2026-10-16`,
Sections 4--5, for the atom and reflected-atom limit statements. The proof
uses dominated convergence for the complete inverse-square weighted series.
No Haar measure is substituted for Q and no legality is inferred from an
ambient limit. Squarefreeness is unnecessary for these limits.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.ZetaTwoHilbert
open ZetaTwoProbability ArithmeticCumulative QDivisibilityDensity

/-- Uniformly bounded physical sequences converging pointwise to zero
converge in the complete Q norm. -/
theorem qNorm_tendsto_zero_of_bounded_pointwise
    (u : ℕ → QHilbert) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ j k, |qSequence (u j) k| ≤ C)
    (hp : ∀ k, Tendsto (fun j => qSequence (u j) k) atTop (𝓝 0)) :
    Tendsto (fun j => ‖u j‖) atTop (𝓝 0) := by
  have hs : Tendsto (fun j => ‖u j‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [qNorm_weighted_sq]
    have h := tendsto_tsum_of_dominated_convergence
      (positiveQWeight_summable.mul_right (C ^ 2))
      (fun k => by
        simpa using ((hp k).pow 2).const_mul (positiveQWeight k))
      (Filter.Eventually.of_forall (fun j k => by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg _))]
        apply mul_le_mul_of_nonneg_left _ (positiveQWeight_nonneg k)
        have hh := mul_le_mul (hb j k) (hb j k) (abs_nonneg _) hC
        simpa only [← pow_two, sq_abs] using hh))
    simpa using h
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

/-- Unscaled residue atoms with conductors tending to infinity converge
strongly to zero under Q, irrespective of squarefreeness. -/
theorem qResidue_tendsto_zero (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => qResidue (d j)) atTop (𝓝 0) := by
  have hb (j k : ℕ) : |qSequence (qResidue (d j)) k| ≤ 1 := by
    rw [qSequence_qResidue]
    by_cases hz : d j = 0
    · simp [residueFraction, hz]
    · have hdR : (0 : ℝ) < d j := by exact_mod_cast Nat.pos_of_ne_zero hz
      unfold residueFraction
      rw [abs_of_nonneg (by positivity)]
      apply (div_le_iff₀ hdR).mpr
      simpa using (show ((k % d j : ℕ) : ℝ) ≤ d j by
        exact_mod_cast (Nat.mod_lt k (Nat.pos_of_ne_zero hz)).le)
  have hp (k : ℕ) : Tendsto (fun j => qSequence (qResidue (d j)) k)
      atTop (𝓝 0) := by
    have h := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hd).const_mul (k : ℝ)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [hd.eventually (eventually_gt_atTop k)] with j hj
    simp [qSequence_qResidue, residueFraction, Nat.mod_eq_of_lt hj, div_eq_mul_inv,
      mul_comm]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using
    qNorm_tendsto_zero_of_bounded_pointwise _ 1 zero_le_one hb hp

/-- Divisibility indicators also vanish strongly when their conductors escape. -/
theorem qDivisor_tendsto_zero (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => qDivisor (d j)) atTop (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply qNorm_tendsto_zero_of_bounded_pointwise _ 1 zero_le_one
  · intro j k
    simpa only [qSequence_qDivisor] using positiveDivisor_abs_le_one (d j) k
  · intro k
    apply tendsto_const_nhds.congr'
    filter_upwards [hd.eventually (eventually_gt_atTop k)] with j hj
    by_cases hk : k = 0
    · simp [hk]
    · simp [qSequence_qDivisor, positiveDivisor, hk,
        Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hk) hj]

/-- Actual Q vector of the reflected fractional part, with zero anchor. -/
def qReflected (d : ℕ) : QHilbert := qOne - qResidue d - qDivisor d

theorem qReflected_sequence (d k : ℕ) :
    qSequence (qReflected d) k =
      qOneSequence k - residueFraction d k - positiveDivisor d k := by
  change qSequenceLinear (_ - _ - _) k = _
  simp only [map_sub, Pi.sub_apply]
  change qSequence qOne k - qSequence (qResidue d) k - qSequence (qDivisor d) k = _
  rw [qSequence_qOne, qSequence_qResidue, qSequence_qDivisor]

/-- The reflected ambient vectors converge strongly to the constant one.
This statement contains no assertion of squarefree legal membership. -/
theorem qReflected_tendsto_one (d : ℕ → ℕ) (hd : Tendsto d atTop atTop) :
    Tendsto (fun j => qReflected (d j)) atTop (𝓝 qOne) := by
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => qOne) atTop (𝓝 qOne)).sub
    (qResidue_tendsto_zero d hd)).sub
    (qDivisor_tendsto_zero d hd)
  simpa only [qReflected, sub_zero] using h

end RiemannResearch.RH.ZetaTwoHilbert
