import RiemannResearch.RH.QFloorEulerCandidates
import RiemannResearch.RH.PrimeSievePrimitiveEscape
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Undamped finite Euler residue candidates escape in full Q norm

Source: user-directed Euler-operator research, 13 October 2026.
The exact signed decomposition is proved before estimating it. The complete
Pareto dilation is a scaled isometry, making T_m - I/m bounded below for m>1.
The previously proved primitive-sieve escape therefore forces these literal
finite Euler candidates to escape too. No prime number theorem is used.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QFloorEulerCandidates
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QFloorDilation Pareto

def residueSieve (P : ℕ) : QHilbert :=
  ∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) • qResidue d

/-- Exact floor-dilation identity, including its reciprocal-density correction. -/
theorem floorDilation_residueSieve (P m : ℕ) (hm : 0 < m) :
    floorDilation m hm (residueSieve P) =
      (∑ d ∈ P.divisors, (ArithmeticFunction.moebius d : ℝ) • qResidue (m * d)) -
        sieveReciprocal P • qResidue m := by
  unfold residueSieve
  rw [map_sum]
  calc
    (∑ d ∈ P.divisors, floorDilation m hm
      ((ArithmeticFunction.moebius d : ℝ) • qResidue d)) =
        ∑ d ∈ P.divisors,
          ((ArithmeticFunction.moebius d : ℝ) • qResidue (m * d) -
            ((ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) • qResidue m) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [map_smul, floorDilation_qResidue m d hm (Nat.pos_of_mem_divisors hd)]
      simp only [smul_sub, smul_smul, div_eq_mul_inv, one_mul]
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
      rfl

theorem candidate_floor_decomposition (P m : ℕ) (hm : 0 < m) :
    candidate P m =
      floorDilation m hm (residueSieve P) - (1 / (m : ℝ)) • residueSieve P +
        sieveReciprocal P • qResidue m := by
  rw [floorDilation_residueSieve]
  unfold candidate residueSieve
  abel

theorem residueSieve_factorial_toPareto (Y : ℕ) :
    toPareto (residueSieve Y.factorial) = -derivativeSieveHilbert Y := by
  apply hilbertSequence_injective
  rw [toPareto_sequence]
  change qSequence (residueSieve Y.factorial) =
    hilbertSequenceLinear (-derivativeSieveHilbert Y)
  rw [map_neg]
  change qSequence (residueSieve Y.factorial) = -hilbertSequence (derivativeSieveHilbert Y)
  rw [derivativeSieveHilbert_sequence]
  change qSequenceLinear (residueSieve Y.factorial) = _
  unfold residueSieve
  rw [map_sum]
  simp only [map_smul]
  funext n
  have hq (d : ℕ) : qSequenceLinear (qResidue d) =
      ArithmeticCumulative.residueFraction d := qSequence_qResidue d
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply,
    hq, derivativeSievePrimitive, neg_neg, sieveResidue, Nat.one_mul]

/-- Complete transferred identity; none of its signed terms is discarded. -/
theorem candidate_factorial_toPareto (Y m : ℕ) (hm : 0 < m) :
    toPareto (candidate Y.factorial m) =
      (1 / (m : ℝ)) • derivativeSieveHilbert Y -
        (1 / (m : ℝ)) • hilbertDilation m hm (derivativeSieveHilbert Y) +
          sieveReciprocal Y.factorial • toPareto (qResidue m) := by
  rw [candidate_floor_decomposition _ m hm]
  change toParetoLinear
    (floorDilation m hm (residueSieve Y.factorial) -
      (1 / (m : ℝ)) • residueSieve Y.factorial +
      sieveReciprocal Y.factorial • qResidue m) = _
  rw [map_add, map_sub, map_smul, map_smul]
  change toPareto (floorDilation m hm (residueSieve Y.factorial)) -
    (1 / (m : ℝ)) • toPareto (residueSieve Y.factorial) +
    sieveReciprocal Y.factorial • toPareto (qResidue m) = _
  rw [toPareto_floorDilation, residueSieve_factorial_toPareto]
  have hneg : hilbertDilation m hm (-derivativeSieveHilbert Y) =
      -hilbertDilation m hm (derivativeSieveHilbert Y) :=
    (hilbertDilationLinear m hm).map_neg _
  rw [hneg]
  simp only [smul_neg]
  abel

/-- Reverse triangle inequality preserves a strictly positive dilation gap. -/
theorem candidate_factorial_norm_lower (Y m : ℕ) (hm : 0 < m) :
    ((Real.sqrt (m : ℝ) - 1) / (m : ℝ)) * ‖derivativeSieveHilbert Y‖ ≤
      Real.sqrt zetaTwo * ‖candidate Y.factorial m‖ + ‖toPareto (qResidue m)‖ := by
  let D := derivativeSieveHilbert Y
  let R := toPareto (qResidue m)
  let a : ℝ := sieveReciprocal Y.factorial
  let B := (1 / (m : ℝ)) • D - (1 / (m : ℝ)) • hilbertDilation m hm D
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have ha0 : 0 ≤ a := (sieveReciprocal_pos Y.factorial (Nat.factorial_pos Y)).le
  have ha1 : a ≤ 1 := sieveReciprocal_le_one Y.factorial (Nat.factorial_pos Y)
  have hcorr : ‖a • R‖ ≤ ‖R‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 (norm_nonneg R)
  have hbase : ‖B‖ ≤ ‖toPareto (candidate Y.factorial m)‖ + ‖R‖ := by
    have he : B = toPareto (candidate Y.factorial m) - a • R := by
      rw [candidate_factorial_toPareto Y m hm]
      change B = B + a • R - a • R
      abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hcorr)
  have hreverse := norm_sub_norm_le
    ((1 / (m : ℝ)) • hilbertDilation m hm D) ((1 / (m : ℝ)) • D)
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (m : ℝ)), hilbertDilation_norm] at hreverse
  rw [norm_sub_rev] at hreverse
  change (1 / (m : ℝ)) * (Real.sqrt (m : ℝ) * ‖D‖) -
    (1 / (m : ℝ)) * ‖D‖ ≤ ‖B‖ at hreverse
  have htransfer := toPareto_norm_le (candidate Y.factorial m)
  have he : ((Real.sqrt (m : ℝ) - 1) / (m : ℝ)) * ‖D‖ =
      (1 / (m : ℝ)) * (Real.sqrt (m : ℝ) * ‖D‖) -
        (1 / (m : ℝ)) * ‖D‖ := by ring
  change ((Real.sqrt (m : ℝ) - 1) / (m : ℝ)) * ‖D‖ ≤
    Real.sqrt zetaTwo * ‖candidate Y.factorial m‖ + ‖R‖
  rw [he]
  linarith

/-- The actual undamped factorial-prime Euler candidates diverge in full Q norm. -/
theorem candidate_factorial_norm_tendsto_atTop (m : ℕ) (hm : 1 < m) :
    Tendsto (fun Y : ℕ => ‖candidate Y.factorial m‖) atTop atTop := by
  have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  have hroot : 1 < Real.sqrt (m : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg m), Real.sqrt_nonneg (m : ℝ)]
  have hc : 0 < (Real.sqrt (m : ℝ) - 1) / (m : ℝ) :=
    div_pos (sub_pos.mpr hroot) (lt_trans zero_lt_one hmR)
  have hZ : 0 < Real.sqrt zetaTwo := Real.sqrt_pos.mpr zetaTwo_pos
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_atTop.1 derivativeSieveHilbert_norm_tendsto_atTop)
    ((Real.sqrt zetaTwo * b + ‖toPareto (qResidue m)‖) /
      ((Real.sqrt (m : ℝ) - 1) / (m : ℝ)))] with Y hY
  have hmul := (div_le_iff₀ hc).mp hY
  have hlower := candidate_factorial_norm_lower Y m hm0
  have he : Real.sqrt zetaTwo * b ≤
      Real.sqrt zetaTwo * ‖candidate Y.factorial m‖ := by nlinarith
  exact le_of_mul_le_mul_left he hZ

end RiemannResearch.RH.QFloorEulerCandidates
