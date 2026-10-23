/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.QPrimePowerWaveletCoefficients
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.PrimePowerTargetMellin
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QPrimePowerValuationProjection
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Push
import RiemannResearch.RH.QPrimePowerInfiniteProjection
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
/-!
# The second Meixner valuation mode in the actual Zipf Hilbert space

Source: user-provided valuation/Meixner research direction, 20 October 2026,
and the polynomial normalization in FpOrthonormalBasisResearch20261020.md.
This module proves its degree-two case by summing weighted adjacent-tail
wavelets. With x = p^2, d = x - 1 and v = v_p(n), the new unit vector is
(d^2 * v * (v - 1) / 2 - 2 * d * v + 1) / x.
The constant, first and second modes are orthonormal in actual QHilbert.
The floor-logarithm target F_p = Nat.log p n has coefficient zero at this
second mode. Its full residual remains present in the signed error identity.

This is a finite orthonormal family, not a completeness theorem, a replacement
of F_p by v_p, or a provider of membership in closureWithConstants.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert QDivisorHilbert

private theorem prime_inv_norm_lt_one (p : ℕ) (hp : p.Prime) :
    ‖(p : ℝ)⁻¹‖ < 1 := by
  have h0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h0)]
  exact (inv_lt_one₀ h0).mpr h1

private theorem prime_sq_inv_norm_lt_one (p : ℕ) (hp : p.Prime) :
    ‖((p : ℝ)^2)⁻¹‖ < 1 := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h2 : (1 : ℝ) < (p : ℝ)^2 := by nlinarith
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]
  exact (inv_lt_one₀ (by positivity)).mpr h2

private theorem coefficient_sq_geometric (p k : ℕ) (hp : p.Prime) :
    (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2 =
      ((p : ℝ)^2-1)⁻¹ * (((p : ℝ)^2)⁻¹)^k := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [qTarget_inner_primePowerFrame_succ, div_pow, mul_pow,
    Real.sq_sqrt (by nlinarith : 0 ≤ (p : ℝ)^2-1)]
  simp [one_div, ← pow_mul, mul_comm]

/-- All polynomial moments of the squared same-prime coefficients are summable. -/
theorem primePower_coefficient_moment_summable (p m : ℕ) (hp : p.Prime) :
    Summable (fun k : ℕ => (k : ℝ)^m *
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) := by
  simp_rw [coefficient_sq_geometric p _ hp, ← mul_assoc]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    (summable_pow_mul_geometric_of_norm_lt_one m
      (prime_sq_inv_norm_lt_one p hp)).mul_left (((p : ℝ)^2-1)⁻¹)

/-- The exact first moment of the squared wavelet coefficients. -/
theorem primePower_coefficient_first_moment (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, (k : ℝ) *
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) =
      (p : ℝ)^2 / ((p : ℝ)^2-1)^3 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  simp_rw [coefficient_sq_geometric p _ hp, mul_left_comm ( _ : ℝ) (((p : ℝ)^2-1)⁻¹)]
  rw [tsum_mul_left, tsum_coe_mul_geometric_of_norm_lt_one
    (prime_sq_inv_norm_lt_one p hp)]
  field_simp


private theorem quadratic_geometric_sum (r : ℝ) (hr : ‖r‖ < 1) :
    (∑' n : ℕ, (n : ℝ)^2 * r^n) = r*(1+r)/(1-r)^3 := by
  have hc (n : ℕ) : (((n+2).choose 2 : ℕ) : ℝ) =
      ((n : ℝ)^2 + 3*(n : ℝ) + 2)/2 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show n+1+2 = (n+2)+1 by omega, Nat.choose_succ_succ]
      simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      rw [ih]
      ring
  have hs : Summable (fun n : ℕ => (n : ℝ)*r^n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h1 : HasSum (fun n : ℕ => (n : ℝ)*r^n) (r/(1-r)^2) := by
    simpa only [tsum_coe_mul_geometric_of_norm_lt_one hr] using hs.hasSum
  have h := ((hasSum_choose_mul_geometric_of_norm_lt_one 2 hr).mul_left (2:ℝ)).sub
    (h1.mul_left 3)
  have hh := h.sub ((hasSum_geometric_of_norm_lt_one hr).mul_left (2:ℝ))
  have he : (fun n : ℕ =>
      2 * ((↑((n+2).choose 2) : ℝ) * r^n) - 3*((n : ℝ)*r^n) - 2*r^n) =
      (fun n : ℕ => (n : ℝ)^2*r^n) := by
    funext n
    rw [hc]
    ring
  rw [he] at hh
  rw [hh.tsum_eq]
  have hne : 1-r ≠ 0 := by
    have hlt : r < 1 := (le_abs_self r).trans_lt (by simpa [Real.norm_eq_abs] using hr)
    linarith
  field_simp
  ring

/-- The exact second moment of the squared wavelet coefficients. -/
theorem primePower_coefficient_second_moment (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, (k : ℝ)^2 *
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2) =
      (p : ℝ)^2 * ((p : ℝ)^2+1) / ((p : ℝ)^2-1)^4 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  simp_rw [coefficient_sq_geometric p _ hp, mul_left_comm ( _ : ℝ) (((p : ℝ)^2-1)⁻¹)]
  rw [tsum_mul_left, quadratic_geometric_sum _
    (prime_sq_inv_norm_lt_one p hp)]
  field_simp

/-- The linearly weighted wavelet series converges absolutely in Q norm. -/
theorem primePower_weighted_summable (p : ℕ) (hp : p.Prime) :
    Summable (fun k : ℕ =>
      ((k : ℝ) * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) •
        primePowerFrame p hp (k+1)) := by
  apply Summable.of_norm
  apply ((summable_pow_mul_geometric_of_norm_lt_one 1
    (prime_inv_norm_lt_one p hp)).mul_left (Real.sqrt ((p : ℝ)^2-1))⁻¹).congr
  intro k
  rw [norm_smul, (primePowerFrame_orthonormal p hp).1, mul_one,
    qTarget_inner_primePowerFrame_succ, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp [one_div, mul_comm, mul_left_comm, mul_assoc]

/-- Weighted sum of the already computed floor-logarithm wavelet coefficients. -/
def primePowerWeightedProjection (p : ℕ) (hp : p.Prime) : QHilbert :=
  ∑' k : ℕ,
    ((k : ℝ) * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) •
      primePowerFrame p hp (k+1)

/-- Every wavelet coordinate of the weighted sum is its prescribed coefficient. -/
theorem primePowerWeightedProjection_inner_frame (p : ℕ) (hp : p.Prime) (j : ℕ) :
    inner ℝ (primePowerFrame p hp (j+1)) (primePowerWeightedProjection p hp) =
      (j : ℝ) * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (j+1)) := by
  change (innerSL ℝ (primePowerFrame p hp (j+1))) (∑' k : ℕ, _) = _
  rw [(innerSL ℝ (primePowerFrame p hp (j+1))).map_tsum
    (primePower_weighted_summable p hp)]
  change (∑' k : ℕ, inner ℝ (primePowerFrame p hp (j+1))
    (((k : ℝ) * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) •
      primePowerFrame p hp (k+1))) = _
  simp only [real_inner_smul_right,
    (orthonormal_iff_ite.mp (primePowerFrame_orthonormal p hp))]
  simp

/-- Pairing with the weighted sum retains the entire convergent scalar series. -/
theorem inner_primePowerWeightedProjection (p : ℕ) (hp : p.Prime) (f : QHilbert) :
    inner ℝ f (primePowerWeightedProjection p hp) =
      ∑' k : ℕ, ((k : ℝ) *
        inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) *
        inner ℝ f (primePowerFrame p hp (k+1)) := by
  change (innerSL ℝ f) (∑' k : ℕ, _) = _
  rw [(innerSL ℝ f).map_tsum (primePower_weighted_summable p hp)]
  change (∑' k : ℕ, inner ℝ f
    (((k : ℝ) * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) •
      primePowerFrame p hp (k+1))) = _
  simp only [real_inner_smul_right]

/-- The weighted wavelet sum is centered. -/
theorem qOne_inner_primePowerWeightedProjection (p : ℕ) (hp : p.Prime) :
    inner ℝ qOne (primePowerWeightedProjection p hp) = 0 := by
  rw [inner_primePowerWeightedProjection]
  have hi (k : ℕ) : inner ℝ qOne (primePowerFrame p hp (k+1)) = 0 := by
    rw [← primePowerFrame_zero p hp]
    exact (primePowerFrame_orthonormal p hp).2 (by omega)
  simp [hi]

/-- The exact target pairing with the weighted wavelet sum. -/
theorem qTarget_inner_primePowerWeightedProjection (p : ℕ) (hp : p.Prime) :
    inner ℝ (qTarget p hp.one_lt) (primePowerWeightedProjection p hp) =
      (p : ℝ)^2 / ((p : ℝ)^2-1)^3 := by
  rw [inner_primePowerWeightedProjection]
  simpa only [pow_two, mul_assoc] using primePower_coefficient_first_moment p hp

/-- The first valuation projection has the same pairing as the floor-log target. -/
theorem projection_inner_primePowerWeightedProjection (p : ℕ) (hp : p.Prime) :
    inner ℝ (primePowerProjection p hp) (primePowerWeightedProjection p hp) =
      (p : ℝ)^2 / ((p : ℝ)^2-1)^3 := by
  rw [inner_primePowerWeightedProjection]
  have hi (k : ℕ) :
      inner ℝ (primePowerProjection p hp) (primePowerFrame p hp (k+1)) =
        inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)) :=
    (real_inner_comm _ _).trans (primePowerProjection_inner_frame p hp k)
  simp_rw [hi]
  simpa only [pow_two, mul_assoc] using primePower_coefficient_first_moment p hp

/-- The exact squared norm of the weighted wavelet sum. -/
theorem primePowerWeightedProjection_norm_sq (p : ℕ) (hp : p.Prime) :
    ‖primePowerWeightedProjection p hp‖^2 =
      (p : ℝ)^2 * ((p : ℝ)^2+1) / ((p : ℝ)^2-1)^4 := by
  rw [← real_inner_self_eq_norm_sq, inner_primePowerWeightedProjection]
  have hi (k : ℕ) :
      inner ℝ (primePowerWeightedProjection p hp) (primePowerFrame p hp (k+1)) =
        (k : ℝ) * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)) :=
    (real_inner_comm _ _).trans (primePowerWeightedProjection_inner_frame p hp k)
  simp_rw [hi]
  convert primePower_coefficient_second_moment p hp using 1
  apply tsum_congr
  intro k
  ring

/-- The normalized degree-two Meixner polynomial in the prime valuation. -/
def primeMeixnerTwo (p : ℕ) (hp : p.Prime) : QHilbert :=
  (((p : ℝ)^2-1)^2 / (p : ℝ)^2) •
    (primePowerWeightedProjection p hp -
      (1 / ((p : ℝ)^2-1)) • primePowerProjection p hp)

/-- The second Meixner mode has mean zero. -/
theorem qOne_inner_primeMeixnerTwo (p : ℕ) (hp : p.Prime) :
    inner ℝ qOne (primeMeixnerTwo p hp) = 0 := by
  simp [primeMeixnerTwo, inner_sub_right, real_inner_smul_right,
    qOne_inner_primePowerWeightedProjection, qOne_inner_primePowerProjection]

/-- The second mode is orthogonal to the centered valuation projection. -/
theorem projection_inner_primeMeixnerTwo (p : ℕ) (hp : p.Prime) :
    inner ℝ (primePowerProjection p hp) (primeMeixnerTwo p hp) = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  rw [primeMeixnerTwo, real_inner_smul_right, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    primePowerProjection_norm_sq, projection_inner_primePowerWeightedProjection]
  field_simp
  ring

/-- The actual floor-logarithm target has zero second Meixner coefficient. -/
theorem qTarget_inner_primeMeixnerTwo (p : ℕ) (hp : p.Prime) :
    inner ℝ (qTarget p hp.one_lt) (primeMeixnerTwo p hp) = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  rw [primeMeixnerTwo, real_inner_smul_right, inner_sub_right,
    real_inner_smul_right, qTarget_inner_primePowerProjection,
    qTarget_inner_primePowerWeightedProjection]
  field_simp
  ring

/-- The second Meixner mode has unit squared norm. -/
theorem primeMeixnerTwo_norm_sq (p : ℕ) (hp : p.Prime) :
    ‖primeMeixnerTwo p hp‖^2 = 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  rw [primeMeixnerTwo, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, real_inner_comm (primePowerProjection p hp)
      (primePowerWeightedProjection p hp), projection_inner_primePowerWeightedProjection,
    primePowerProjection_norm_sq, primePowerWeightedProjection_norm_sq]
  field_simp
  ring


/-- Physical coordinates of the weighted partial sum stabilize after the valuation cutoff. -/
theorem primePower_weighted_partial_sequence (p n N : ℕ) (hp : p.Prime)
    (hn : n ≠ 0) (hN : n.factorization p < N) :
    qSequence (∑ k ∈ Finset.range N,
      ((k : ℝ) * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) •
        primePowerFrame p hp (k+1)) n =
      (n.factorization p : ℝ) * ((n.factorization p : ℝ)-1)/2 -
        (n.factorization p : ℝ) / ((p : ℝ)^2-1) := by
  let v := n.factorization p
  let f : ℕ → ℝ := fun k => (k : ℝ) *
    (((p : ℝ)^2 * (if k+1 ≤ v then 1 else 0) -
      (if k ≤ v then 1 else 0)) / ((p : ℝ)^2-1))
  have hd : (p : ℝ)^2-1 ≠ 0 := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    nlinarith
  have hsmall (k : ℕ) (hk : k ∈ Finset.range v) : f k = (k : ℝ) := by
    have hkv := Finset.mem_range.mp hk
    simp [f, hkv, show k ≤ v by omega, hd]
  have hend : f v = -(v : ℝ) / ((p : ℝ)^2-1) := by
    simp [f]
    ring
  have hzero (k : ℕ) (hk : v+1 ≤ k) : f k = 0 := by
    simp [f, show ¬k < v by omega, show ¬k ≤ v by omega]
  have hsumid (m : ℕ) : (∑ k ∈ Finset.range m, (k : ℝ)) =
      (m : ℝ)*((m : ℝ)-1)/2 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hsum : ∑ k ∈ Finset.range (v+1), f k =
      (v : ℝ)*((v : ℝ)-1)/2 - (v : ℝ)/((p : ℝ)^2-1) := by
    rw [Finset.sum_range_succ, hend, Finset.sum_congr rfl hsmall, hsumid]
    ring
  have hsub : ∑ k ∈ Finset.range (v+1), f k = ∑ k ∈ Finset.range N, f k := by
    apply Finset.sum_subset (Finset.range_mono (by dsimp [v]; omega))
    intro k hk hnot
    exact hzero k (by simpa using hnot)
  have hterm (k : ℕ) :
      qSequence (((k : ℝ) * inner ℝ (qTarget p hp.one_lt)
        (primePowerFrame p hp (k+1))) • primePowerFrame p hp (k+1)) n = f k := by
    rw [mul_smul]
    change qSequenceLinear ((k : ℝ) • _) n = _
    rw [map_smul]
    change (k : ℝ) * qSequence
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)) •
        primePowerFrame p hp (k+1)) n = _
    rw [primePower_projection_term_sequence p k n hp hn]
  change qSequenceLinear (∑ k ∈ Finset.range N, _) n = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  change (∑ k ∈ Finset.range N, qSequence (_) n) = _
  simp_rw [hterm]
  rw [← hsub]
  exact hsum

/-- The weighted Hilbert sum is a quadratic polynomial in the actual valuation. -/
theorem primePowerWeightedProjection_sequence (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    qSequence (primePowerWeightedProjection p hp) n =
      (n.factorization p : ℝ)*((n.factorization p : ℝ)-1)/2 -
        (n.factorization p : ℝ)/((p : ℝ)^2-1) := by
  have ht := (SquarefreeRadicalDifference.continuous_qSequence n).tendsto
    (primePowerWeightedProjection p hp)
  have hlim := ht.comp (primePower_weighted_summable p hp).hasSum.tendsto_sum_nat
  have he : (fun N => qSequence (∑ k ∈ Finset.range N,
      ((k : ℝ) * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) •
        primePowerFrame p hp (k+1)) n) =ᶠ[Filter.atTop]
      (fun _ => (n.factorization p : ℝ)*((n.factorization p : ℝ)-1)/2 -
        (n.factorization p : ℝ)/((p : ℝ)^2-1)) := by
    filter_upwards [Filter.eventually_ge_atTop (n.factorization p+1)] with N hN
    exact primePower_weighted_partial_sequence p n N hp hn (by omega)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)

/-- The second Meixner vector has the prescribed normalized quadratic coordinates. -/
theorem primeMeixnerTwo_sequence (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    qSequence (primeMeixnerTwo p hp) n =
      (((p : ℝ)^2-1)^2 * (n.factorization p : ℝ) *
        ((n.factorization p : ℝ)-1)/2 -
        2*((p : ℝ)^2-1)*(n.factorization p : ℝ)+1) / (p : ℝ)^2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  unfold primeMeixnerTwo
  change qSequenceLinear (_ • _) n = _
  rw [map_smul, map_sub, map_smul]
  change (((p : ℝ)^2-1)^2 / (p : ℝ)^2) *
    (qSequence (primePowerWeightedProjection p hp) n -
      (1 / ((p : ℝ)^2-1)) * qSequence (primePowerProjection p hp) n) = _
  rw [primePowerWeightedProjection_sequence p n hp hn,
    primePowerProjection_sequence p n hp hn]
  field_simp
  ring

/-- The first and second normalized Meixner modes are orthogonal. -/
theorem primeMeixnerOne_inner_two (p : ℕ) (hp : p.Prime) :
    inner ℝ (primePowerProjectionUnit p hp) (primeMeixnerTwo p hp) = 0 := by
  rw [primePowerProjectionUnit, real_inner_smul_left,
    projection_inner_primeMeixnerTwo, mul_zero]

/-- The first three Meixner valuation modes, including the constant. -/
def primeMeixnerTriple (p : ℕ) (hp : p.Prime) : Fin 3 → QHilbert :=
  ![qOne, primePowerProjectionUnit p hp, primeMeixnerTwo p hp]

/-- Actual Zipf orthonormality of the constant, linear and quadratic valuation modes. -/
theorem primeMeixnerTriple_orthonormal (p : ℕ) (hp : p.Prime) :
    Orthonormal ℝ (primeMeixnerTriple p hp) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [primeMeixnerTriple, qOne_norm_sq,
      primePowerProjectionUnit_norm_sq, primeMeixnerTwo_norm_sq,
      primePowerProjectionUnit_inner_qOne, qOne_inner_primeMeixnerTwo,
      primeMeixnerOne_inner_two, real_inner_comm qOne (primeMeixnerTwo p hp),
      real_inner_comm (primePowerProjectionUnit p hp) (primeMeixnerTwo p hp),
      real_inner_comm qOne (primePowerProjectionUnit p hp)]

/-- Every signed trial coefficient incurs its full square in addition to the existing residual. -/
theorem qTarget_meixner_two_signed_error (p : ℕ) (hp : p.Prime) (a : ℝ) :
    ‖qTarget p hp.one_lt -
      (inner ℝ (qTarget p hp.one_lt) qOne • qOne + primePowerProjection p hp +
        a • primeMeixnerTwo p hp)‖^2 =
      ‖qTarget p hp.one_lt -
        inner ℝ (qTarget p hp.one_lt) qOne • qOne - primePowerProjection p hp‖^2 +
        a^2 := by
  have he : qTarget p hp.one_lt -
      (inner ℝ (qTarget p hp.one_lt) qOne • qOne + primePowerProjection p hp +
        a • primeMeixnerTwo p hp) =
      (qTarget p hp.one_lt -
        inner ℝ (qTarget p hp.one_lt) qOne • qOne - primePowerProjection p hp) -
        a • primeMeixnerTwo p hp := by abel
  rw [he, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    primeMeixnerTwo_norm_sq, real_inner_smul_right, inner_sub_left, inner_sub_left,
    real_inner_smul_left, qTarget_inner_primeMeixnerTwo,
    qOne_inner_primeMeixnerTwo, projection_inner_primeMeixnerTwo]
  ring

end RiemannResearch.RH.PrimePowerTarget
