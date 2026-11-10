/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QCRTCarry
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.QPrimeCarryProjection
import RiemannResearch.RH.SquarefreeMobiusProjection
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Absolute Hilbert summation along Euclid's carry ray

Source: *Squarefree projection displacement and infinite CRT carries*,
9 November 2026, Proposition 5 and Section 12.3. The least prime factor of
`D + 1` gives a deterministic extension of every squarefree conductor.
Both weighted branches converge in the complete Q and Pareto norms.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.QEuclidCarryRay

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QPrimeCarryProjection SquarefreeMobiusProjection

/-- The conductor after appending a new prime divisor of the previous conductor plus one. -/
def conductor (r : ℕ) : ℕ → ℕ
  | 0 => r
  | k + 1 => conductor r k * (conductor r k + 1).minFac

def radix (r k : ℕ) : ℕ := (conductor r k + 1).minFac

def multiplier (r k : ℕ) : ℕ := (conductor r k + 1) / radix r k

theorem conductor_succ (r k : ℕ) : conductor r (k + 1) = conductor r k * radix r k :=
  rfl

theorem radix_dvd (r k : ℕ) : radix r k ∣ conductor r k + 1 :=
  Nat.minFac_dvd _

theorem conductor_two_le (r : ℕ) (hr : 2 ≤ r) (k : ℕ) : 2 ≤ conductor r k := by
  induction k with
  | zero => exact hr
  | succ k ih =>
      have hp : (radix r k).Prime := Nat.minFac_prime (by omega : conductor r k + 1 ≠ 1)
      rw [conductor_succ]
      exact ih.trans (by simpa using Nat.mul_le_mul_left (conductor r k) hp.one_lt.le)

theorem radix_prime (r : ℕ) (hr : 2 ≤ r) (k : ℕ) : (radix r k).Prime := by
  have h := conductor_two_le r hr k
  exact Nat.minFac_prime (by omega : conductor r k + 1 ≠ 1)

theorem radix_fresh (r : ℕ) (hr : 2 ≤ r) (k : ℕ) : ¬radix r k ∣ conductor r k := by
  intro h
  have he := Nat.dvd_sub (radix_dvd r k) h
  have he' : radix r k ∣ 1 := by simpa using he
  exact (radix_prime r hr k).not_dvd_one he'

theorem conductor_squarefree (r : ℕ) (hr : 2 ≤ r) (hs : Squarefree r) (k : ℕ) :
    Squarefree (conductor r k) := by
  induction k with
  | zero => exact hs
  | succ k ih =>
      have hp := radix_prime r hr k
      have hc := (Nat.coprime_or_dvd_of_prime hp (conductor r k)).resolve_right
        (radix_fresh r hr k)
      rw [conductor_succ, Nat.squarefree_mul hc.symm]
      exact ⟨ih, hp.squarefree⟩

theorem conductor_growth (r : ℕ) (hr : 2 ≤ r) (k : ℕ) : 2 ^ k * r ≤ conductor r k := by
  induction k with
  | zero => simp [conductor]
  | succ k ih =>
      rw [pow_succ, conductor_succ]
      calc
        2 ^ k * 2 * r = (2 ^ k * r) * 2 := by ring
        _ ≤ conductor r k * radix r k := Nat.mul_le_mul ih (radix_prime r hr k).two_le

/-- The weight recursion is multiplication by the reciprocal Bezout coefficient. -/
def weight (r : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => weight r k * ((radix r k : ℝ) / ((conductor r k : ℝ) + 1))

private theorem radix_ratio (r k : ℕ) : 0 ≤ (radix r k : ℝ) / ((conductor r k : ℝ) + 1) ∧
    (radix r k : ℝ) / ((conductor r k : ℝ) + 1) ≤ 1 := by
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity)).mpr
    simpa only [one_mul, Nat.cast_one, Nat.cast_add] using
      (show (radix r k : ℝ) ≤ ((conductor r k + 1 : ℕ) : ℝ) by
        exact_mod_cast Nat.le_of_dvd (by omega : 0 < conductor r k + 1) (radix_dvd r k))

theorem weight_nonneg_le_one (r k : ℕ) : 0 ≤ weight r k ∧ weight r k ≤ 1 := by
  induction k with
  | zero => simp [weight]
  | succ k ih =>
      rw [weight]
      exact ⟨mul_nonneg ih.1 (radix_ratio r k).1,
        (mul_le_mul_of_nonneg_right ih.2 (radix_ratio r k).1).trans
          (by simpa only [one_mul] using (radix_ratio r k).2)⟩

theorem multiplier_mul_radix (r k : ℕ) :
    (multiplier r k : ℝ) * (radix r k : ℝ) = (conductor r k : ℝ) + 1 := by
  exact_mod_cast Nat.div_mul_cancel (radix_dvd r k)

theorem weight_normalize (r k : ℕ) :
    weight r (k + 1) * (multiplier r k : ℝ) = weight r k := by
  rw [weight, mul_assoc]
  have he : ((radix r k : ℝ) / ((conductor r k : ℝ) + 1)) *
      (multiplier r k : ℝ) = 1 := by
    rw [div_mul_eq_mul_div, mul_comm (radix r k : ℝ), multiplier_mul_radix, div_self]
    positivity
  rw [he, mul_one]

def boundary (r k : ℕ) : QHilbert := weight r k • qResidue (conductor r k)

def primeBranch (r k : ℕ) : QHilbert := weight r (k + 1) • qResidue (radix r k)

def carryBranch (r k : ℕ) : QHilbert := boundary r k - primeBranch r k - boundary r (k + 1)

theorem carryBranch_eq (r k : ℕ) :
    carryBranch r k = weight r (k + 1) • ((multiplier r k : ℝ) • qResidue (conductor r k) -
      qResidue (radix r k) - qResidue (conductor r (k + 1))) := by
  rw [smul_sub, smul_sub, smul_smul, weight_normalize]
  rfl

/-- The normalized carry is the actual floor-defined CRT vector. -/
theorem carryBranch_eq_weighted_floor (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    carryBranch r k = weight r (k + 1) •
      QCRTCarry.qCarry (conductor r k) (radix r k) (multiplier r k : ℤ) (-1) := by
  have hd : 0 < conductor r k := by have := conductor_two_le r hr k; omega
  have he := QCRTCarry.qCarry_eq_linear (conductor r k) (radix r k) (multiplier r k : ℤ)
    (-1) 0 hd (radix_prime r hr k).pos (by
      push_cast
      have h := multiplier_mul_radix r k
      linarith only [h])
  rw [carryBranch_eq, he, conductor_succ]
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_one, neg_one_smul, sub_eq_add_neg]

theorem sum_branches (r N : ℕ) :
    (∑ k ∈ Finset.range N, primeBranch r k) +
      (∑ k ∈ Finset.range N, carryBranch r k) + boundary r N = qResidue r := by
  induction N with
  | zero => simp [boundary, conductor, weight]
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih, carryBranch]
      abel

/-- A uniform geometric envelope with the root dependence needed to pool branches. -/
def envelope (r k : ℕ) : ℝ :=
  Real.sqrt (2 / (zetaTwo * (r : ℝ))) * (Real.sqrt (1 / 2)) ^ k

private theorem norm_le_envelope (r : ℕ) (hr : 2 ≤ r) (k : ℕ) (x : QHilbert)
    (hx : ‖x‖ ^ 2 ≤ 2 / (zetaTwo * (conductor r k : ℝ))) :
    ‖x‖ ≤ envelope r k := by
  have hd : (2 : ℝ) ^ k * (r : ℝ) ≤ conductor r k := by
    exact_mod_cast conductor_growth r hr k
  have hr' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hd' : 0 < zetaTwo * ((2 : ℝ) ^ k * (r : ℝ)) :=
    mul_pos zetaTwo_pos (mul_pos (pow_pos (by norm_num) _) hr')
  have hg : 0 ≤ 2 / (zetaTwo * (r : ℝ)) :=
    div_nonneg (by norm_num) (mul_nonneg zetaTwo_pos.le hr'.le)
  have he : ((Real.sqrt (1 / 2)) ^ k) ^ 2 = (1 / 2 : ℝ) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, Real.sq_sqrt (by norm_num)]
  apply (sq_le_sq₀ (norm_nonneg x) (by unfold envelope; positivity)).mp
  calc
    ‖x‖ ^ 2 ≤ 2 / (zetaTwo * (conductor r k : ℝ)) := hx
    _ ≤ 2 / (zetaTwo * ((2 : ℝ) ^ k * (r : ℝ))) :=
      div_le_div_of_nonneg_left (by norm_num) hd'
        (mul_le_mul_of_nonneg_left hd zetaTwo_pos.le)
    _ = (envelope r k) ^ 2 := by
      rw [envelope, mul_pow, Real.sq_sqrt hg, he, div_pow, one_pow]
      field_simp [zetaTwo_pos.ne', hr'.ne', pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)] <;> ring

theorem boundary_norm_le (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    ‖boundary r k‖ ≤ envelope r k := by
  apply norm_le_envelope r hr
  rw [boundary, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg_le_one r k).1]
  have h := mul_le_mul_of_nonneg_right (weight_nonneg_le_one r k).2
    (norm_nonneg (qResidue (conductor r k)))
  have hn : weight r k * ‖qResidue (conductor r k)‖ ≤ ‖qResidue (conductor r k)‖ := by
    simpa only [one_mul] using h
  have hnonneg : 0 ≤ weight r k * ‖qResidue (conductor r k)‖ :=
    mul_nonneg (weight_nonneg_le_one r k).1 (norm_nonneg _)
  exact ((sq_le_sq₀ hnonneg (norm_nonneg _)).mpr hn).trans
    (qResidue_norm_sq_le_two_div _ (conductor_two_le r hr k))

theorem primeBranch_norm_le (r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    ‖primeBranch r k‖ ≤ envelope r k := by
  let p : ℝ := radix r k
  let D : ℝ := conductor r k
  let t : ℝ := p / (D + 1)
  have hp : 0 < p := by
    change 0 < (radix r k : ℝ)
    exact_mod_cast (radix_prime r hr k).pos
  have hD : 0 < D := by
    change 0 < (conductor r k : ℝ)
    exact_mod_cast (show 0 < conductor r k by
      have := conductor_two_le r hr k
      omega)
  have hD1 : 0 < D + 1 := by positivity
  have ht : 0 ≤ t ∧ t ≤ 1 := radix_ratio r k
  have hnorm : ‖primeBranch r k‖ ≤ t * ‖qResidue (radix r k)‖ := by
    rw [primeBranch, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg_le_one r _).1]
    change (weight r k * t) * ‖qResidue (radix r k)‖ ≤ _
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (weight_nonneg_le_one r k).2 ht.1
  apply norm_le_envelope r hr
  calc
    ‖primeBranch r k‖ ^ 2 ≤ (t * ‖qResidue (radix r k)‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ht.1 (norm_nonneg _))).mpr hnorm
    _ ≤ t ^ 2 * (2 / (zetaTwo * p)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left
        (qResidue_norm_sq_le_two_div _ (radix_prime r hr k).two_le) (sq_nonneg _)
    _ = t * (2 / (zetaTwo * (D + 1))) := by
      dsimp only [t]
      field_simp [hp.ne', hD1.ne', zetaTwo_pos.ne'] <;> ring
    _ ≤ 2 / (zetaTwo * (D + 1)) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2
        (div_nonneg (by norm_num) (mul_nonneg zetaTwo_pos.le hD1.le))
    _ ≤ 2 / (zetaTwo * D) := div_le_div_of_nonneg_left (by norm_num)
      (mul_pos zetaTwo_pos hD) (mul_le_mul_of_nonneg_left (by linarith) zetaTwo_pos.le)

theorem envelope_summable (r : ℕ) : Summable (envelope r) := by
  have hlt : Real.sqrt (1 / 2 : ℝ) < 1 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (1 / 2 : ℝ)]
  exact (summable_geometric_of_lt_one (Real.sqrt_nonneg _) hlt).mul_left _

theorem boundary_norm_summable (r : ℕ) (hr : 2 ≤ r) :
    Summable (fun k => ‖boundary r k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (boundary_norm_le r hr)
    (envelope_summable r)

theorem primeBranch_norm_summable (r : ℕ) (hr : 2 ≤ r) :
    Summable (fun k => ‖primeBranch r k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (primeBranch_norm_le r hr)
    (envelope_summable r)

theorem carryBranch_norm_summable (r : ℕ) (hr : 2 ≤ r) :
    Summable (fun k => ‖carryBranch r k‖) := by
  have hb := boundary_norm_summable r hr
  have hs := (summable_nat_add_iff 1).mpr hb
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((hb.add
    (primeBranch_norm_summable r hr)).add hs)
  intro k
  unfold carryBranch
  exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)

theorem boundary_tendsto (r : ℕ) (hr : 2 ≤ r) : Tendsto (boundary r) atTop (𝓝 0) :=
  (boundary_norm_summable r hr).of_norm.tendsto_atTop_zero

/-- The infinite Euclid identity in complete Q norm, including its root. -/
theorem sum_infinite_branches (r : ℕ) (hr : 2 ≤ r) :
    (∑' k, primeBranch r k) + (∑' k, carryBranch r k) = qResidue r := by
  have hp := (primeBranch_norm_summable r hr).of_norm.hasSum.tendsto_sum_nat
  have hc := (carryBranch_norm_summable r hr).of_norm.hasSum.tendsto_sum_nat
  have ht := (hp.add hc).add (boundary_tendsto r hr)
  rw [add_zero] at ht
  have hh : Tendsto (fun N => (∑ k ∈ Finset.range N, primeBranch r k) +
      (∑ k ∈ Finset.range N, carryBranch r k) + boundary r N) atTop (𝓝 (qResidue r)) :=
    tendsto_const_nhds.congr' (Eventually.of_forall (fun N => (sum_branches r N).symm))
  exact tendsto_nhds_unique ht hh

theorem branches_pareto_norm_summable (r : ℕ) (hr : 2 ≤ r) :
    Summable (fun k => ‖toPareto (primeBranch r k)‖) ∧
      Summable (fun k => ‖toPareto (carryBranch r k)‖) := by
  constructor
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => toParetoCLM.le_opNorm _)
      ((primeBranch_norm_summable r hr).mul_left ‖toParetoCLM‖)
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => toParetoCLM.le_opNorm _)
      ((carryBranch_norm_summable r hr).mul_left ‖toParetoCLM‖)


/-- The projected carry sum recovers the projected root. -/
theorem projected_carry_sum (r : ℕ) (hr : 2 ≤ r) :
    carryClosure.starProjection (∑' k, carryBranch r k) =
      carryClosure.starProjection (qResidue r) := by
  have hz (k : ℕ) : carryClosure.starProjection (primeBranch r k) = 0 := by
    have h := qResidue_mem_primeClosure (radix r k) (radix_prime r hr k)
    rw [primeBranch, map_smul, carry_projection_eq]
    change weight r (k + 1) •
      (ZetaTwoOptimizerStage.closure.starProjection (qResidue (radix r k)) -
        primeClosure.starProjection (qResidue (radix r k))) = 0
    rw [ZetaTwoOptimizerStage.closure.starProjection_eq_self_iff.mpr
      (primeClosure_le_optimizerClosure h), primeClosure.starProjection_eq_self_iff.mpr h,
      sub_self, smul_zero]
  have hprime := (carryClosure.starProjection.continuous.tendsto _).comp
    (primeBranch_norm_summable r hr).of_norm.hasSum.tendsto_sum_nat
  have hzero : Tendsto (fun N => carryClosure.starProjection
      (∑ k ∈ Finset.range N, primeBranch r k)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun N => by simp only [map_sum, hz, Finset.sum_const_zero]
  have hp := tendsto_nhds_unique hprime hzero
  have ht := congrArg carryClosure.starProjection (sum_infinite_branches r hr)
  rw [map_add, hp, zero_add] at ht
  exact ht

/-- Composite roots cannot lie in the closed prime span, by the continuous
Möbius coefficient functional at the root. -/
theorem composite_root_not_mem_primeClosure (r : ℕ) (hr : 2 ≤ r) (hnp : ¬r.Prime) :
    qResidue r ∉ primeClosure := by
  have hspan : QSimultaneousCRT.primeSpan ≤ (qCoefficientCLM r).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    change qCoefficientCLM r (qResidue p.val) = 0
    have hi := q_coordinate_biorthogonal (r - 2) (p.val - 2)
    have hne : r - 2 ≠ p.val - 2 := by
      have hp := p.property.two_le
      intro he
      have hp' : r = p.val := by omega
      exact hnp (hp' ▸ p.property)
    simpa only [if_neg hne, Nat.sub_add_cancel hr, Nat.sub_add_cancel p.property.two_le] using hi
  have hclosed : ((qCoefficientCLM r).ker).topologicalClosure = (qCoefficientCLM r).ker := by
    apply SetLike.coe_injective
    exact (qCoefficientCLM r).isClosed_ker.closure_eq
  intro h
  have hker := Submodule.topologicalClosure_mono hspan h
  rw [hclosed] at hker
  change qCoefficientCLM r (qResidue r) = 0 at hker
  have hi := SquarefreeMobiusProjection.q_coordinate_biorthogonal (r - 2) (r - 2)
  simp only [Nat.sub_add_cancel hr] at hi
  rw [hi] at hker
  norm_num at hker

/-- A squarefree composite root leaves a nonzero projected carry sum. -/
theorem projected_carry_sum_ne_zero (r : ℕ) (hr : 2 ≤ r) (hsf : Squarefree r)
    (hnp : ¬r.Prime) :
    carryClosure.starProjection (∑' k, carryBranch r k) ≠ 0 := by
  have hv : qResidue r ∈ ZetaTwoOptimizerStage.closure := by
    rw [QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
    exact qSquarefreeCRTSpan.le_topologicalClosure
      (Submodule.subset_span ⟨⟨r, hr, hsf⟩, rfl⟩)
  rw [projected_carry_sum r hr, carry_projection_eq]
  change ZetaTwoOptimizerStage.closure.starProjection (qResidue r) -
    primeClosure.starProjection (qResidue r) ≠ 0
  rw [ZetaTwoOptimizerStage.closure.starProjection_eq_self_iff.mpr hv]
  intro he
  exact composite_root_not_mem_primeClosure r hr hnp
    ((sub_eq_zero.mp he).symm ▸ primeClosure.starProjection_apply_mem (qResidue r))

end RiemannResearch.RH.QEuclidCarryRay
