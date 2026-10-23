/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.DenseProjectionTesting
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A uniform dual bound for nonnegative Q tests

Source: elementary geometric-conductor construction developed while following
the user's uniform-dual-bound request, 22 October 2026. No novelty is claimed.

The exact physical sequence of the finite legal vector
B_K = 4 sum_{k<K} g_{4^(k+1)} precedes its pointwise bound. Its complete Q norm
is at most 4 sqrt(2 / zeta(2)), and it dominates one for 0 < n < 4^K.
Cauchy--Schwarz therefore gives a support-independent bound for nonnegative
tests against the actual full-legal-space orthogonal projection.

The sign restriction is substantive. These are majorants, not exact heads.
No uniform bound for arbitrary signed tests or unconditional RH proof follows.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QNonnegativeDualBound
open ZetaTwoHilbert QFiniteSupportDualCriterion
open RiemannResearch.Analysis.DenseProjectionTesting

private theorem qOne_coordinate (n : ℕ) : qOne n = Real.sqrt (qWeight n) := by
  change Real.sqrt (qWeight n) * qOneSequence (n + 1) = _
  simp [qOneSequence]

/-- A legal majorant controls nonnegative tests; the sign hypothesis is essential. -/
theorem nonnegative_test_bound_of_majorant (M : ℕ) (a b : QHilbert)
    (ha : ∀ n < M, 0 ≤ a n)
    (hb : b ∈ QFullResidueProjection.closure)
    (hmajor : ∀ n, 0 < n → n ≤ M → 1 ≤ qSequence b n) :
    |inner ℝ qOne (finiteHead M a)| ≤
      ‖b‖ * ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖ := by
  have hcoord (n : ℕ) (hn : n < M) : qOne n ≤ b n := by
    rw [qOne_coordinate]
    have h := hmajor (n + 1) (by omega) (by omega)
    rw [qSequence_succ] at h
    have hs := Real.sqrt_pos.mpr (qWeight_pos n)
    simpa using (le_div_iff₀ hs).mp h
  have hpos : 0 ≤ inner ℝ qOne (finiteHead M a) := by
    rw [inner_finiteHead_eq_sum]
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (ha n (Finset.mem_range.mp hn))
      (by rw [qOne_coordinate]; exact Real.sqrt_nonneg _)
  rw [abs_of_nonneg hpos]
  calc
    inner ℝ qOne (finiteHead M a) ≤ inner ℝ b (finiteHead M a) := by
      rw [inner_finiteHead_eq_sum, inner_finiteHead_eq_sum]
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (hcoord n (Finset.mem_range.mp hn))
        (ha n (Finset.mem_range.mp hn))
    _ = inner ℝ b (QFullResidueProjection.closure.starProjection (finiteHead M a)) :=
      inner_eq_projected_test _ hb _
    _ ≤ |inner ℝ b (QFullResidueProjection.closure.starProjection (finiteHead M a))| :=
      le_abs_self _
    _ ≤ _ := abs_real_inner_le_norm _ _

open ZetaTwoProbability ArithmeticCumulative

private theorem exists_four_power_interval (K n : ℕ) (hn : 0 < n)
    (hNK : n < 4 ^ K) :
    ∃ k < K, 4 ^ k ≤ n ∧ n < 4 ^ (k + 1) := by
  induction K generalizing n with
  | zero => simp only [pow_zero] at hNK; omega
  | succ K ih =>
    by_cases h : n < 4 ^ K
    · obtain ⟨k, hk, hlo, hhi⟩ := ih n hn h
      exact ⟨k, lt_trans hk (Nat.lt_succ_self K), hlo, hhi⟩
    · exact ⟨K, Nat.lt_succ_self K, Nat.le_of_not_gt h, hNK⟩

private theorem four_pow_ge_two (k : ℕ) : 2 ≤ (4 : ℕ) ^ (k + 1) := by
  rw [pow_succ]
  have hp : 0 < (4 : ℕ) ^ k := by positivity
  omega

theorem qResidue_four_pow_norm_le (k : ℕ) :
    ‖qResidue (4 ^ (k + 1))‖ ≤
      Real.sqrt (2 / zetaTwo) * (1 / 2 : ℝ) ^ (k + 1) := by
  have hZ := zetaTwo_pos
  have hb := qResidue_norm_sq_le_two_div (4 ^ (k + 1)) (four_pow_ge_two k)
  have hpow : ((1 / 2 : ℝ) ^ (k + 1)) ^ 2 =
      1 / (4 : ℝ) ^ (k + 1) := by
    calc
      _ = ((1 / 2 : ℝ) ^ 2) ^ (k + 1) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
      _ = _ := by norm_num [one_div_pow]
  have he : (Real.sqrt (2 / zetaTwo) * (1 / 2 : ℝ) ^ (k + 1)) ^ 2 =
      2 / (zetaTwo * ((4 ^ (k + 1) : ℕ) : ℝ)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 / zetaTwo), hpow]
    push_cast
    field_simp [ne_of_gt zetaTwo_pos]
  have hp : 0 ≤ Real.sqrt (2 / zetaTwo) * (1 / 2 : ℝ) ^ (k + 1) := by
    positivity
  nlinarith [norm_nonneg (qResidue (4 ^ (k + 1)))]

/-- A finite legal majorant built from geometrically spaced conductors. -/
def fourMajorant (K : ℕ) : QHilbert :=
  (4 : ℝ) • ∑ k ∈ Finset.range K, qResidue (4 ^ (k + 1))

/-- A uniform bound in the complete Q norm, including all periodic tails. -/
theorem fourMajorant_norm_le (K : ℕ) :
    ‖fourMajorant K‖ ≤ 4 * Real.sqrt (2 / zetaTwo) := by
  have hs (J : ℕ) :
      ‖∑ k ∈ Finset.range J, qResidue (4 ^ (k + 1))‖ ≤
        Real.sqrt (2 / zetaTwo) * (1 - (1 / 2 : ℝ) ^ J) := by
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ]
      calc
        _ ≤ ‖∑ k ∈ Finset.range J, qResidue (4 ^ (k + 1))‖ +
            ‖qResidue (4 ^ (J + 1))‖ := norm_add_le _ _
        _ ≤ Real.sqrt (2 / zetaTwo) * (1 - (1 / 2 : ℝ) ^ J) +
            Real.sqrt (2 / zetaTwo) * (1 / 2 : ℝ) ^ (J + 1) :=
          add_le_add ih (qResidue_four_pow_norm_le J)
        _ = _ := by rw [pow_succ]; ring
  rw [fourMajorant, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  have hp : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
  have hc := Real.sqrt_nonneg (2 / zetaTwo)
  nlinarith [hs K]

theorem fourMajorant_mem_legalSpan (K : ℕ) :
    fourMajorant K ∈ QFullResidueProjection.legalSpan := by
  apply QFullResidueProjection.legalSpan.smul_mem
  apply QFullResidueProjection.legalSpan.sum_mem
  intro k hk
  apply Submodule.subset_span
  refine ⟨4 ^ (k + 1) - 2, ?_⟩
  have hd := four_pow_ge_two k
  have he : 4 ^ (k + 1) - 2 + 2 = 4 ^ (k + 1) := by omega
  change qResidue (4 ^ (k + 1) - 2 + 2) = qResidue (4 ^ (k + 1))
  rw [he]

theorem fourMajorant_sequence (K n : ℕ) :
    qSequence (fourMajorant K) n =
      4 * ∑ k ∈ Finset.range K, residueFraction (4 ^ (k + 1)) n := by
  change qSequenceLinear (fourMajorant K) n = _
  unfold fourMajorant
  simp only [map_smul, map_sum]
  change ((4 : ℝ) • ∑ k ∈ Finset.range K,
    qSequence (qResidue (4 ^ (k + 1)))) n = _
  simp only [qSequence_qResidue, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]

/-- Every positive coordinate below the cutoff is dominated by one covering atom. -/
theorem fourMajorant_majorizes (K n : ℕ) (hn : 0 < n) (hNK : n < 4 ^ K) :
    1 ≤ qSequence (fourMajorant K) n := by
  obtain ⟨k, hk, hlo, hhi⟩ := exists_four_power_interval K n hn hNK
  have hnonneg (j : ℕ) : 0 ≤ residueFraction (4 ^ (j + 1)) n := by
    unfold residueFraction
    positivity
  have hsum : residueFraction (4 ^ (k + 1)) n ≤
      ∑ j ∈ Finset.range K, residueFraction (4 ^ (j + 1)) n :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_range.mpr hk)
  have hfrac : (1 / 4 : ℝ) ≤ residueFraction (4 ^ (k + 1)) n := by
    unfold residueFraction
    rw [Nat.mod_eq_of_lt hhi]
    apply (le_div_iff₀ (by positivity : 0 < ((4 ^ (k + 1) : ℕ) : ℝ))).mpr
    have hlo' : ((4 ^ k : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlo
    push_cast at hlo' ⊢
    rw [pow_succ]
    nlinarith
  rw [fourMajorant_sequence]
  linarith

private theorem lt_four_pow_succ (M : ℕ) : M < 4 ^ (M + 1) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [pow_succ]
    have hp : 0 < (4 : ℕ) ^ (M + 1) := by positivity
    omega

/-- Uniform in the support and test, subject to coordinate nonnegativity. -/
theorem nonnegative_finite_test_uniform_dual_bound (M : ℕ) (a : QHilbert)
    (ha : ∀ n < M, 0 ≤ a n) :
    |inner ℝ qOne (finiteHead M a)| ≤
      (4 * Real.sqrt (2 / zetaTwo)) *
        ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖ := by
  have hb := QFullResidueProjection.legalSpan.le_topologicalClosure
    (fourMajorant_mem_legalSpan (M + 1))
  have hm (n : ℕ) (hn : 0 < n) (hnM : n ≤ M) :
      1 ≤ qSequence (fourMajorant (M + 1)) n :=
    fourMajorant_majorizes (M + 1) n hn (lt_of_le_of_lt hnM (lt_four_pow_succ M))
  exact (nonnegative_test_bound_of_majorant M a (fourMajorant (M + 1))
    ha hb hm).trans
      (mul_le_mul_of_nonneg_right (fourMajorant_norm_le (M + 1)) (norm_nonneg _))

/-- Continuity extends the bound to every nonnegative Q test, without finite support. -/
theorem nonnegative_uniform_dual_bound (a : QHilbert) (ha : ∀ n, 0 ≤ a n) :
    |inner ℝ qOne a| ≤
      (4 * Real.sqrt (2 / zetaTwo)) *
        ‖QFullResidueProjection.closure.starProjection a‖ := by
  have hl : Tendsto (fun M => |inner ℝ qOne (finiteHead M a)|)
      atTop (𝓝 |inner ℝ qOne a|) :=
    (tendsto_const_nhds.inner (finiteHead_tendsto a)).abs
  have hr : Tendsto
      (fun M => (4 * Real.sqrt (2 / zetaTwo)) *
        ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖)
      atTop (𝓝 ((4 * Real.sqrt (2 / zetaTwo)) *
        ‖QFullResidueProjection.closure.starProjection a‖)) :=
    ((QFullResidueProjection.closure.starProjection.continuous.tendsto a).comp
      (finiteHead_tendsto a)).norm.const_mul _
  exact le_of_tendsto_of_tendsto hl hr
    (Filter.Eventually.of_forall (fun M =>
      nonnegative_finite_test_uniform_dual_bound M a (fun n _ => ha n)))


end RiemannResearch.RH.QNonnegativeDualBound
