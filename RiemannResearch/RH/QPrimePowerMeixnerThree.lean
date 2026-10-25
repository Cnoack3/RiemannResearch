/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerPolynomialOrthonormal
import RiemannResearch.RH.QPrimePowerMonomialLift
import RiemannResearch.RH.QPrimePowerMeixnerTwo
import RiemannResearch.RH.QPrimePowerInfiniteProjection
import RiemannResearch.RH.QPrimePowerValuationProjection
import RiemannResearch.RH.QPrimePowerCofactorResidual
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.QPrimePowerWaveletCoefficients
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Module
import Lean.Elab.Tactic.Omega

/-!
# The explicit normalized cubic valuation mode

Source: user-provided valuation/Meixner direction and
FpOrthonormalBasisResearch20261020.md. The proof derives the needed geometric
moments from Mathlib's binomial-geometric HasSum theorem, then computes the
actual Hilbert Gram-Schmidt innovation with both signed lower-degree terms.
For d=p^2-1 and v=v_p(n), the normalized cubic is
(d^3*v*(v-1)*(v-2)/6 - 3*d^2*v*(v-1)/2 + 3*d*v - 1)/p^3.
Its sign agrees with the general Gram-Schmidt family.

The floor-log target F_p=Nat.log p n has zero coefficient at this mode.
The signed error through the cubic retains the full cofactor residual,
the mean and linear discrepancies, and both higher coefficient squares.
This is not polynomial/tensor completeness or legal-closure membership.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert QDivisorHilbert InnerProductSpace

private theorem choose_two_real (n : ℕ) :
    (((n+2).choose 2 : ℕ) : ℝ) = ((n : ℝ)^2+3*n+2)/2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega, Nat.choose_succ_succ]
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    rw [ih]
    ring

private theorem choose_three_real (n : ℕ) :
    (((n+3).choose 3 : ℕ) : ℝ) = ((n : ℝ)^3+6*(n : ℝ)^2+11*n+6)/6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n+1+3 = (n+3)+1 by omega, Nat.choose_succ_succ]
    push_cast
    rw [show n+3 = (n+1)+2 by omega, choose_two_real]
    rw [show (n+1)+2 = n+3 by omega, ih]
    push_cast
    ring

private theorem choose_four_real (n : ℕ) :
    (((n+4).choose 4 : ℕ) : ℝ) =
      ((n : ℝ)^4+10*(n : ℝ)^3+35*(n : ℝ)^2+50*n+24)/24 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [show n+1+4 = (n+4)+1 by omega, Nat.choose_succ_succ]
    push_cast
    rw [show n+4 = (n+1)+3 by omega, choose_three_real]
    rw [show (n+1)+3 = n+4 by omega, ih]
    push_cast
    ring

private theorem coefficient_binomial_hasSum (p : ℕ) (hp : p.Prime) (m : ℕ) :
    HasSum (fun k : ℕ => (((k+m).choose m : ℕ) : ℝ) *
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2)
      (((p : ℝ)^2-1)⁻¹ * (1 / (1-((p : ℝ)^2)⁻¹)^(m+1))) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr : ‖((p : ℝ)^2)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
    exact (inv_lt_one₀ (by positivity)).mpr (by nlinarith)
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one m hr).mul_left
    (((p : ℝ)^2-1)⁻¹)
  have he : (fun k : ℕ => (((k+m).choose m : ℕ) : ℝ) *
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) =
      (fun k : ℕ => ((p : ℝ)^2-1)⁻¹ *
        ((((k+m).choose m : ℕ) : ℝ) * (((p : ℝ)^2)⁻¹)^k)) := by
    funext k
    rw [qTarget_inner_primePowerFrame_succ, div_pow, mul_pow,
      Real.sq_sqrt (by nlinarith : 0 ≤ (p : ℝ)^2-1)]
    simp [one_div, ← pow_mul, mul_comm, mul_assoc]
  rw [he]
  exact h

/-- The exact cubic moment of the squared same-prime wavelet coefficients. -/
theorem primePower_coefficient_third_moment (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, (k : ℝ)^3 *
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) =
      (p : ℝ)^2 * ((p : ℝ)^4+4*(p : ℝ)^2+1) / ((p : ℝ)^2-1)^5 := by
  have h0 := coefficient_binomial_hasSum p hp 0
  simp only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add] at h0
  have h1 := (primePower_coefficient_moment_summable p 1 hp).hasSum
  simp only [pow_one, primePower_coefficient_first_moment] at h1
  have h2 := (primePower_coefficient_moment_summable p 2 hp).hasSum
  rw [primePower_coefficient_second_moment] at h2
  have h := ((((coefficient_binomial_hasSum p hp 3).mul_left (6:ℝ)).sub
    (h2.mul_left 6)).sub (h1.mul_left 11)).sub (h0.mul_left 6)
  have he : (fun k : ℕ => 6 * ((((k+3).choose 3 : ℕ) : ℝ) *
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) -
      6*((k : ℝ)^2 * (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) -
      11*((k : ℝ) * (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) -
      6*(inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) =
      (fun k : ℕ => (k : ℝ)^3 * (inner ℝ (qTarget p hp.one_lt)
        (primePowerFrame p hp (k+1)))^2) := by
    funext k
    rw [choose_three_real]
    ring
  rw [he] at h
  rw [h.tsum_eq]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  have heq : 1-((p : ℝ)^2)⁻¹ = ((p : ℝ)^2-1)/(p : ℝ)^2 := by
    field_simp
  simp only [heq]
  field_simp [hp0, hd]
  ring_nf
  field_simp [hp0]
  ring

/-- The exact quartic moment of the squared same-prime wavelet coefficients. -/
theorem primePower_coefficient_fourth_moment (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, (k : ℝ)^4 *
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) =
      (p : ℝ)^2 * ((p : ℝ)^6+11*(p : ℝ)^4+11*(p : ℝ)^2+1) /
        ((p : ℝ)^2-1)^6 := by
  have h0 := coefficient_binomial_hasSum p hp 0
  simp only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, zero_add] at h0
  have h1 := (primePower_coefficient_moment_summable p 1 hp).hasSum
  simp only [pow_one, primePower_coefficient_first_moment] at h1
  have h2 := (primePower_coefficient_moment_summable p 2 hp).hasSum
  rw [primePower_coefficient_second_moment] at h2
  have h3 := (primePower_coefficient_moment_summable p 3 hp).hasSum
  rw [primePower_coefficient_third_moment] at h3
  have h := (((((coefficient_binomial_hasSum p hp 4).mul_left (24:ℝ)).sub
    (h3.mul_left 10)).sub (h2.mul_left 35)).sub (h1.mul_left 50)).sub (h0.mul_left 24)
  have he : (fun k : ℕ => 24 * ((((k+4).choose 4 : ℕ) : ℝ) *
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) -
      10*((k : ℝ)^3 * (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) -
      35*((k : ℝ)^2 * (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) -
      50*((k : ℝ) * (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) -
      24*(inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) =
      (fun k : ℕ => (k : ℝ)^4 * (inner ℝ (qTarget p hp.one_lt)
        (primePowerFrame p hp (k+1)))^2) := by
    funext k
    rw [choose_four_real]
    ring
  rw [he] at h
  rw [h.tsum_eq]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  have heq : 1-((p : ℝ)^2)⁻¹ = ((p : ℝ)^2-1)/(p : ℝ)^2 := by
    field_simp
  simp only [heq]
  field_simp [hp0, hd]
  ring_nf
  field_simp [hp0]
  ring

private theorem monomial_zero (p : ℕ) (hp : p.Prime) :
    primePowerMonomialLift p hp 0 = primePowerProjection p hp := by
  simp [primePowerMonomialLift, primePowerProjection]

private theorem monomial_one (p : ℕ) (hp : p.Prime) :
    primePowerMonomialLift p hp 1 = primePowerWeightedProjection p hp := by
  simp [primePowerMonomialLift, primePowerWeightedProjection]

private theorem projection_inner_monomial_two (p : ℕ) (hp : p.Prime) :
    inner ℝ (primePowerProjection p hp) (primePowerMonomialLift p hp 2) =
      (p : ℝ)^2 * ((p : ℝ)^2+1) / ((p : ℝ)^2-1)^4 := by
  rw [← monomial_zero, primePowerMonomialLift_gram]
  exact primePower_coefficient_second_moment p hp

private theorem weighted_inner_monomial_two (p : ℕ) (hp : p.Prime) :
    inner ℝ (primePowerWeightedProjection p hp) (primePowerMonomialLift p hp 2) =
      (p : ℝ)^2 * ((p : ℝ)^4+4*(p : ℝ)^2+1) / ((p : ℝ)^2-1)^5 := by
  rw [← monomial_one, primePowerMonomialLift_gram]
  exact primePower_coefficient_third_moment p hp

private theorem monomial_two_norm_sq (p : ℕ) (hp : p.Prime) :
    ‖primePowerMonomialLift p hp 2‖^2 =
      (p : ℝ)^2 * ((p : ℝ)^6+11*(p : ℝ)^4+11*(p : ℝ)^2+1) /
        ((p : ℝ)^2-1)^6 := by
  rw [← real_inner_self_eq_norm_sq, primePowerMonomialLift_gram]
  exact primePower_coefficient_fourth_moment p hp

/-- The cubic innovation retains both signed lower-degree corrections. -/
def primeMeixnerThreeRaw (p : ℕ) (hp : p.Prime) : QHilbert :=
  primePowerMonomialLift p hp 2 -
    (1+4/((p : ℝ)^2-1)) • primePowerWeightedProjection p hp +
    (2/((p : ℝ)^2-1)^2) • primePowerProjection p hp

/-- Exact norm before the positive cubic normalization. -/
theorem primeMeixnerThreeRaw_norm_sq (p : ℕ) (hp : p.Prime) :
    ‖primeMeixnerThreeRaw p hp‖^2 = 4*(p : ℝ)^6/((p : ℝ)^2-1)^6 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  unfold primeMeixnerThreeRaw
  rw [norm_add_sq_real, norm_sub_sq_real]
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    inner_sub_left, real_inner_smul_left, real_inner_smul_right]
  have hST := (real_inner_comm (primePowerMonomialLift p hp 2)
    (primePowerWeightedProjection p hp)).symm.trans (weighted_inner_monomial_two p hp)
  have hSP := (real_inner_comm (primePowerMonomialLift p hp 2)
    (primePowerProjection p hp)).symm.trans (projection_inner_monomial_two p hp)
  have hTP := (real_inner_comm (primePowerWeightedProjection p hp)
    (primePowerProjection p hp)).symm.trans (projection_inner_primePowerWeightedProjection p hp)
  rw [hST, hSP, hTP, primePowerProjection_norm_sq,
    primePowerWeightedProjection_norm_sq, monomial_two_norm_sq]
  field_simp
  ring

/-- The explicit positive normalized cubic valuation mode. -/
def primeMeixnerThree (p : ℕ) (hp : p.Prime) : QHilbert :=
  (((p : ℝ)^2-1)^3 / (2*(p : ℝ)^3)) • primeMeixnerThreeRaw p hp

/-- The explicit cubic has unit Q norm for every prime. -/
theorem primeMeixnerThree_norm_sq (p : ℕ) (hp : p.Prime) :
    ‖primeMeixnerThree p hp‖^2 = 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  rw [primeMeixnerThree, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    primeMeixnerThreeRaw_norm_sq]
  field_simp
  ring

/-- The third unnormalized Gram-Schmidt innovation is the explicit cubic residual. -/
theorem valuationPolynomial_gramSchmidt_two (p : ℕ) (hp : p.Prime) :
    gramSchmidt ℝ (primePowerMonomialLift p hp) 2 = primeMeixnerThreeRaw p hp := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  have hP : (ℝ ∙ primePowerProjection p hp).starProjection
      (primePowerMonomialLift p hp 2) =
      (((p : ℝ)^2+1)/((p : ℝ)^2-1)^2) • primePowerProjection p hp := by
    rw [Submodule.starProjection_singleton, projection_inner_monomial_two,
      primePowerProjection_norm_sq]
    congr 1
    change ((p : ℝ)^2*((p : ℝ)^2+1)/((p : ℝ)^2-1)^4) /
      ((p : ℝ)^2/((p : ℝ)^2-1)^2) = _
    field_simp
  have hT : (ℝ ∙ (primePowerWeightedProjection p hp -
      (1/((p : ℝ)^2-1)) • primePowerProjection p hp)).starProjection
      (primePowerMonomialLift p hp 2) =
      (1+4/((p : ℝ)^2-1)) • (primePowerWeightedProjection p hp -
        (1/((p : ℝ)^2-1)) • primePowerProjection p hp) := by
    have hTP := (real_inner_comm (primePowerWeightedProjection p hp)
      (primePowerProjection p hp)).symm.trans (projection_inner_primePowerWeightedProjection p hp)
    rw [Submodule.starProjection_singleton, inner_sub_left, real_inner_smul_left,
      weighted_inner_monomial_two, projection_inner_monomial_two,
      norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_smul_right, hTP,
      primePowerWeightedProjection_norm_sq, primePowerProjection_norm_sq]
    congr 1
    change (((p : ℝ)^2*((p : ℝ)^4+4*(p : ℝ)^2+1)/((p : ℝ)^2-1)^5) -
      (1/((p : ℝ)^2-1))*((p : ℝ)^2*((p : ℝ)^2+1)/((p : ℝ)^2-1)^4)) /
      ((p : ℝ)^2*((p : ℝ)^2+1)/((p : ℝ)^2-1)^4 -
        2*((1/((p : ℝ)^2-1))*((p : ℝ)^2/((p : ℝ)^2-1)^3)) +
        (1/((p : ℝ)^2-1))^2*((p : ℝ)^2/((p : ℝ)^2-1)^2)) = _
    have hn : (p : ℝ)^2*((p : ℝ)^2+1)/((p : ℝ)^2-1)^4 -
        2*((1/((p : ℝ)^2-1))*((p : ℝ)^2/((p : ℝ)^2-1)^3)) +
        (1/((p : ℝ)^2-1))^2*((p : ℝ)^2/((p : ℝ)^2-1)^2) =
        (p : ℝ)^4/((p : ℝ)^2-1)^4 := by field_simp; ring
    rw [hn]
    field_simp
    ring
  rw [gramSchmidt_def]
  simp only [show Finset.Iio (2 : ℕ) = {0,1} by decide,
    Finset.sum_insert, show (0 : ℕ) ∉ ({1} : Finset ℕ) by decide, not_false_eq_true,
    Finset.sum_singleton]
  rw [show gramSchmidt ℝ (primePowerMonomialLift p hp) 0 =
    primePowerMonomialLift p hp 0 from gramSchmidt_bot _ _,
    monomial_zero, valuationPolynomial_gramSchmidt_one, hP, hT]
  unfold primeMeixnerThreeRaw
  have hc : (1+4/((p : ℝ)^2-1))*(1/((p : ℝ)^2-1)) -
      ((p : ℝ)^2+1)/((p : ℝ)^2-1)^2 = 2/((p : ℝ)^2-1)^2 := by
    field_simp
    ring
  rw [← hc]
  module

/-- The third Gram-Schmidt mode has the explicit positive cubic normalization. -/
theorem valuationPolynomialMode_two (p : ℕ) (hp : p.Prime) :
    valuationPolynomialMode p hp 2 = primeMeixnerThree p hp := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have ha : (0 : ℝ) < ((p : ℝ)^2-1)^3/(2*(p : ℝ)^3) := by
    have hd : (0 : ℝ) < (p : ℝ)^2-1 := by nlinarith
    positivity
  have hn : ‖primeMeixnerThree p hp‖ = 1 := by
    have h := primeMeixnerThree_norm_sq p hp
    nlinarith [norm_nonneg (primeMeixnerThree p hp)]
  rw [primeMeixnerThree, norm_smul, Real.norm_eq_abs, abs_of_pos ha] at hn
  have hne : ‖primeMeixnerThreeRaw p hp‖ ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hn
    norm_num at hn
  have hi : ‖primeMeixnerThreeRaw p hp‖⁻¹ =
      ((p : ℝ)^2-1)^3/(2*(p : ℝ)^3) := by
    apply mul_right_cancel₀ hne
    rw [inv_mul_cancel₀ hne]
    exact hn.symm
  unfold valuationPolynomialMode gramSchmidtNormed
  rw [valuationPolynomial_gramSchmidt_two]
  change ‖primeMeixnerThreeRaw p hp‖⁻¹ • primeMeixnerThreeRaw p hp = _
  rw [hi]
  rfl

/-- Physical cubic coordinates, with all alternating lower-degree terms retained. -/
theorem primeMeixnerThree_sequence (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    qSequence (primeMeixnerThree p hp) n =
      (((p : ℝ)^2-1)^3 * (n.factorization p : ℝ) *
        ((n.factorization p : ℝ)-1)*((n.factorization p : ℝ)-2)/6 -
       3*((p : ℝ)^2-1)^2 * (n.factorization p : ℝ) *
        ((n.factorization p : ℝ)-1)/2 +
       3*((p : ℝ)^2-1)*(n.factorization p : ℝ)-1) / (p : ℝ)^3 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  unfold primeMeixnerThree primeMeixnerThreeRaw
  change qSequenceLinear (_ • _) n = _
  rw [map_smul, map_add, map_sub, map_smul, map_smul]
  change (((p : ℝ)^2-1)^3/(2*(p : ℝ)^3)) *
    (qSequence (primePowerMonomialLift p hp 2) n -
      (1+4/((p : ℝ)^2-1))*qSequence (primePowerWeightedProjection p hp) n +
      (2/((p : ℝ)^2-1)^2)*qSequence (primePowerProjection p hp) n) = _
  rw [primePowerMonomialLift_two_sequence p hp n hn,
    primePowerWeightedProjection_sequence p n hp hn,
    primePowerProjection_sequence p n hp hn]
  field_simp
  ring

/-- The cubic mode has exactly zero floor-log target coefficient for every prime. -/
theorem qTarget_inner_primeMeixnerThree (p : ℕ) (hp : p.Prime) :
    inner ℝ (qTarget p hp.one_lt) (primeMeixnerThree p hp) = 0 := by
  rw [← valuationPolynomialMode_two]
  exact qTarget_inner_valuationPolynomialMode_succ p hp 1

/-- Complete signed error through the explicit cubic, including the full cofactor residual. -/
theorem qTarget_meixner_three_signed_error (p : ℕ) (hp : p.Prime)
    (mu b c a : ℝ) :
    ‖qTarget p hp.one_lt - (mu • qOne + b • primePowerProjectionUnit p hp +
      (c • primeMeixnerTwo p hp + a • primeMeixnerThree p hp))‖^2 =
      ‖primeCofactorResidual p hp‖^2 +
      (inner ℝ (qTarget p hp.one_lt) qOne-mu)^2 +
      ((p : ℝ)/((p : ℝ)^2-1)-b)^2 + (c^2+a^2) := by
  have h := qTarget_valuationPolynomial_signed_error p hp {0,1}
    (fun j => if j=0 then c else a) mu b
  simpa [valuationPolynomialMode_zero, valuationPolynomialMode_one,
    valuationPolynomialMode_two] using h

end RiemannResearch.RH.PrimePowerTarget
