/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.MertensImplicitTruncation
import RiemannResearch.RH.MertensFullDisplacement
import RiemannResearch.RH.QSquarefreeDisplacementRegularity
import RiemannResearch.Analysis.DyadicBlockSummability
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dyadic scalar tests for projection displacement

Lee and Leong, arXiv:2208.06141v5, Theorem 1.1, supply the ordinary
Mertens estimate used by the full-profile moment theorem. Here a decrease
of its positive displacement margin absorbs arbitrary polynomial growth
of the dyadic block masses. The signed tests use the actual residual.
-/

noncomputable section
open Filter
open scoped BigOperators
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis ZetaTwoHilbert QSquarefreeDisplacementRigidity
open QSquarefreeClosedKernel QSquarefreeDisplacementRegularity QShiftedReciprocal

/-- Finite sign tests realize the weighted absolute mass exactly. Repeated sites
are allowed, so the same statement applies to offset-indexed dyadic windows. -/
theorem displacement_block_isGreatest {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    IsGreatest (Set.range (fun σ : ι → Bool => inner ℝ pResidual
      (∑ i ∈ s, ((if σ i then a i else -(a i)) • B (closedKernel (m i))))))
      (∑ i ∈ s, a i * |qSequence displacement (m i)|) := by
  classical
  constructor
  · refine ⟨fun i => decide (0 ≤ qSequence displacement (m i)), ?_⟩
    dsimp only
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_smul_right, ← displacement_eq_smoothed_kernel_pairing]
    by_cases h : 0 ≤ qSequence displacement (m i)
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (lt_of_not_ge h)]
  · rintro y ⟨σ, rfl⟩
    dsimp only
    rw [inner_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [real_inner_smul_right, ← displacement_eq_smoothed_kernel_pairing]
    cases hs : σ i
    · simpa using mul_le_mul_of_nonneg_left (neg_le_abs (qSequence displacement (m i))) (ha i hi)
    · simpa using mul_le_mul_of_nonneg_left (le_abs_self (qSequence displacement (m i))) (ha i hi)

/-- Normalized physical full-profile summand; its arithmetic weight equals
`exp (-Hδ(n)) / (ζ(2) * n)` on positive sites. -/
def fullMomentTerm (δ : ℝ) (n : ℕ) : ℝ :=
  positiveQWeight n * ((n : ℝ) * Real.exp (-(leeLeongFullDisplacementExponent δ n))) *
    |qSequence displacement n|

/-- Full-profile moment on the physical sites from `2^j` through `2^(j+1)-1`. -/
def fullMomentDyadicBlock (δ : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ j), fullMomentTerm δ (2 ^ j + i)

private theorem fullMomentTerm_nonneg (δ : ℝ) (n : ℕ) : 0 ≤ fullMomentTerm δ n := by
  unfold fullMomentTerm
  exact mul_nonneg (mul_nonneg (positiveQWeight_nonneg n)
    (mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le)) (abs_nonneg _)

private theorem fullMomentDyadicBlock_nonneg (δ : ℝ) (j : ℕ) :
    0 ≤ fullMomentDyadicBlock δ j := Finset.sum_nonneg (fun _ _ => fullMomentTerm_nonneg _ _)

private theorem fullMomentTerm_log_pow_gain (δ η : ℝ) (h : η < δ) (p : ℕ) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ)) ^ p * fullMomentTerm η n ≤ fullMomentTerm δ n := by
  let c := (δ - η) / (p : ℝ)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp
  have hc : 0 < c := div_pos (sub_pos.mpr h) hp'
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually (vkProfile_dominates_logLog_sq (c ^ 2) (sq_pos_of_pos hc)),
    hnat.eventually (vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ))),
    eventually_ge_atTop (2 : ℕ)] with n hn hV hn2
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hl : Real.log (Real.log (n : ℝ)) ≤ c * Real.sqrt (vkProfile n) := by
    apply le_of_sq_le_sq _ (mul_nonneg hc.le (Real.sqrt_nonneg _))
    simpa only [mul_pow, Real.sq_sqrt hV] using hn
  have hpc : (p : ℝ) * c = δ - η := by dsimp [c]; field_simp [hp'.ne']
  have hgap := mul_le_mul_of_nonneg_left hl hp'.le
  rw [← mul_assoc, hpc] at hgap
  have he : (Real.log (n : ℝ)) ^ p * Real.exp (-(leeLeongFullDisplacementExponent η n)) ≤
      Real.exp (-(leeLeongFullDisplacementExponent δ n)) := by
    calc
      _ = Real.exp ((p : ℝ) * Real.log (Real.log (n : ℝ)) -
          leeLeongFullDisplacementExponent η n) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log (Real.log_pos hn1)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        unfold leeLeongFullDisplacementExponent
        linarith only [hgap])
  unfold fullMomentTerm
  calc
    _ = (positiveQWeight n * (n : ℝ) * |qSequence displacement n|) *
      ((Real.log (n : ℝ)) ^ p * Real.exp (-(leeLeongFullDisplacementExponent η n))) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left he (mul_nonneg
      (mul_nonneg (positiveQWeight_nonneg n) (Nat.cast_nonneg n)) (abs_nonneg _))).trans_eq
        (by ring)

private theorem dyadic_log_gain (δ η : ℝ) (h : η < δ) (p : ℕ) (hp : 0 < p) :
    ∀ᶠ j : ℕ in atTop, ((j : ℝ) * Real.log 2) ^ p * fullMomentDyadicBlock η j ≤
      fullMomentDyadicBlock δ j := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 (fullMomentTerm_log_pow_gain δ η h p hp)
  filter_upwards [eventually_ge_atTop N] with j hj
  have hpow : j ≤ 2 ^ j := Nat.lt_two_pow_self.le
  unfold fullMomentDyadicBlock
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hji : 2 ^ j ≤ 2 ^ j + i := Nat.le_add_right _ _
  have hlog : (j : ℝ) * Real.log 2 ≤ Real.log ((2 ^ j + i : ℕ) : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast hji
  apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _)
    (Real.log_nonneg (by norm_num))) hlog p) (fullMomentTerm_nonneg _ _)).trans
  exact hN _ ((hj.trans hpow).trans hji)

/-- Any decrease in the margin absorbs arbitrary polynomial growth of the
dyadic blocks. This comparison is independent of the arithmetic premise. -/
theorem summable_full_moment_of_polynomial_dyadic (δ η : ℝ) (hη : η < δ)
    (k : ℕ) (C : ℝ)
    (hblock : ∀ᶠ j : ℕ in atTop, fullMomentDyadicBlock δ j ≤ C * (j : ℝ) ^ k) :
    Summable (fullMomentTerm η) := by
  have hs : Summable (fun j : ℕ => ((j : ℝ) ^ 2)⁻¹) := by
    simpa only [Real.rpow_two] using (Real.summable_nat_rpow_inv (p := 2)).2 (by norm_num)
  have hsum : Summable (fullMomentDyadicBlock η) := by
    apply (hs.mul_left (C / (Real.log 2) ^ (k + 2))).of_norm_bounded_eventually_nat
    filter_upwards [dyadic_log_gain δ η hη (k + 2) (by omega),
      hblock, eventually_ge_atTop (1 : ℕ)] with j hg hb hj
    rw [Real.norm_eq_abs, abs_of_nonneg (fullMomentDyadicBlock_nonneg _ _)]
    have hj' : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hden : 0 < ((j : ℝ) * Real.log 2) ^ (k + 2) := by positivity
    calc
      fullMomentDyadicBlock η j ≤ C * (j : ℝ)^k / (((j : ℝ) * Real.log 2) ^ (k + 2)) := by
        apply (le_div_iff₀ hden).2
        simpa only [mul_comm] using hg.trans hb
      _ = _ := by
        rw [mul_pow, pow_add (j : ℝ)]
        field_simp [ne_of_gt hj', ne_of_gt hl]
  exact DyadicWeightedContrast.summable_of_dyadic_block_majorant _ _
    (fullMomentTerm_nonneg _) (fullMomentDyadicBlock_nonneg _) hsum (fun _ => le_rfl)

/-- At one positive margin the dyadic masses may grow as any fixed polynomial.
Halving that margin makes their sum converge. The remaining arithmetic input
is the displayed block estimate, in addition to the cited Mertens theorem. -/
theorem riemannHypothesis_of_polynomial_dyadic_full_moment (hLL : LeeLeongMertensEstimate)
    (δ : ℝ) (hδ : 0 < δ) (k : ℕ) (C : ℝ)
    (hblock : ∀ᶠ j : ℕ in atTop, fullMomentDyadicBlock δ j ≤ C * (j : ℝ) ^ k) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_leeLeong_full_moment hLL (δ / 2) (by linarith)
  exact summable_full_moment_of_polynomial_dyadic δ (δ / 2) (by linarith) k C hblock

/-- At every fixed signed margin, eventual polynomial growth of the dyadic
masses of the actual displacement implies RH under the implicit truncation. -/
theorem riemannHypothesis_of_implicitTruncation_polynomial_dyadic
    (h : LeeLeongImplicitTruncation) (δ : ℝ) (k : ℕ) (C : ℝ)
    (hblock : ∀ᶠ j : ℕ in atTop, fullMomentDyadicBlock δ j ≤ C * (j : ℝ) ^ k) :
    RiemannHypothesis := by
  have hη : -(|δ| + 1) < δ := by linarith [neg_abs_le δ]
  apply riemannHypothesis_of_implicitTruncation_moment h (|δ| + 1) (by positivity)
  refine (summable_full_moment_of_polynomial_dyadic δ _ hη k C hblock).congr ?_
  intro n
  simp only [fullMomentTerm, leeLeongFullDisplacementExponent, neg_mul, sub_neg_eq_add]

end RiemannResearch.RH.QMertensFirstMoment
