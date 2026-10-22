import RiemannResearch.RH.QResidueRefinement
import RiemannResearch.RH.QPrimeSieve
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Exact weighted refinement energy and the frozen greedy head

Source: user-requested continuation of the Q-prime research record at
commit 916ac4e34fc39271aea3084e284f6b18399e93b3. The line-search algebra is
standard Hilbert geometry. Existing actual Q vectors and arithmetic refinement
identities are reused. The arithmetic application shows that the canonical
greedy prime-two step has zero reciprocal mass, freezing the error at 2 under
all later multipliers greater than 2, even with arbitrary real weights.
No claim about RH or convergence of a repaired family is made.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.QWeightedRefinementEnergy
open ArithmeticCumulative ZetaTwoHilbert ZetaTwoProbability QResidueRefinement QPrimeSieve

theorem energy_quadratic (R A : QHilbert) (u : ℝ) :
    ‖R - u • A‖ ^ 2 = ‖R‖ ^ 2 - 2*u*inner ℝ R A + u ^ 2*‖A‖ ^ 2 := by
  simp only [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  ring

theorem energy_complete_square (R A : QHilbert) (u : ℝ) (hA : ‖A‖ ^ 2 ≠ 0) :
    ‖R - u • A‖ ^ 2 =
      ‖R‖ ^ 2 - (inner ℝ R A) ^ 2 / ‖A‖ ^ 2 +
        ‖A‖ ^ 2 * (u - inner ℝ R A / ‖A‖ ^ 2) ^ 2 := by
  rw [energy_quadratic]
  have hn : ‖A‖ ≠ 0 := fun h => hA (by simp [h])
  field_simp [hn]
  ring

theorem optimal_energy (R A : QHilbert) (hA : ‖A‖ ^ 2 ≠ 0) :
    ‖R - (inner ℝ R A / ‖A‖ ^ 2) • A‖ ^ 2 =
      ‖R‖ ^ 2 - (inner ℝ R A) ^ 2 / ‖A‖ ^ 2 := by
  rw [energy_complete_square R A _ hA]
  ring

theorem optimal_minimizes (R A : QHilbert) (u : ℝ) (hA : ‖A‖ ^ 2 ≠ 0) :
    ‖R - (inner ℝ R A / ‖A‖ ^ 2) • A‖ ^ 2 ≤ ‖R - u • A‖ ^ 2 := by
  rw [optimal_energy R A hA, energy_complete_square R A u hA]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem zero_direction_energy (R A : QHilbert) (hA : ‖A‖ ^ 2 = 0) (u : ℝ) :
    ‖R - u • A‖ ^ 2 = ‖R‖ ^ 2 := by
  have hn : ‖A‖ = 0 := by nlinarith [norm_nonneg A]
  have hz : A = 0 := norm_eq_zero.mp hn
  simp [hz]

theorem energy_quadratic_tsum (R A : QHilbert) (u : ℝ) :
    ‖R - u • A‖ ^ 2 =
      (∑' k, positiveQWeight k * (qSequence R k) ^ 2) -
      2*u*(∑' k, positiveQWeight k*qSequence R k*qSequence A k) +
      u ^ 2*(∑' k, positiveQWeight k * (qSequence A k) ^ 2) := by
  rw [energy_quadratic, qNorm_weighted_sq R, qInner_weighted R A, qNorm_weighted_sq A]

theorem two_inner : inner ℝ qOne (qResidue 2) = 2 * ‖qResidue 2‖ ^ 2 := by
  rw [qInner_weighted, qNorm_weighted_sq, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [qSequence_qOne, qSequence_qResidue]
  by_cases hn : n = 0
  · simp [hn, qOneSequence, residueFraction]
  · have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hm with hm | hm <;> norm_num [qOneSequence, hn, residueFraction, hm]
    ring

theorem two_norm_sq_pos : 0 < ‖qResidue 2‖ ^ 2 := by
  have hn : qResidue 2 ≠ 0 := by
    intro h
    have hh := congrArg (fun f : QHilbert => qSequence f 1) h
    rw [qSequence_qResidue] at hh
    norm_num [residueFraction, qSequence] at hh
  exact sq_pos_of_pos (norm_pos_iff.mpr hn)

theorem first_step_complete_square (u : ℝ) :
    ‖qOne - u • qResidue 2‖ ^ 2 =
      ‖qOne - (2:ℝ) • qResidue 2‖ ^ 2 + (u-2) ^ 2*‖qResidue 2‖ ^ 2 := by
  rw [energy_quadratic, energy_quadratic, two_inner]
  ring

theorem first_step_unique_minimum (u : ℝ) :
    ‖qOne - u • qResidue 2‖ ^ 2 ≤ ‖qOne - (2:ℝ) • qResidue 2‖ ^ 2 ↔ u = 2 := by
  rw [first_step_complete_square]
  constructor
  · intro h
    have hp := two_norm_sq_pos
    have hsq := sq_nonneg (u-2)
    have hz : (u-2) ^ 2 = 0 := by nlinarith
    nlinarith
  · intro h
    simp [h]

theorem zero_reciprocal_freezes_head (S : Finset ℕ) (w : ℕ → ℝ)
    (p n : ℕ) (u : ℝ) (hp : 0 < p) (hn : n < p)
    (hS : ∀ d ∈ S, 0 < d) (hα : reciprocalCoefficient S w = 0) :
    pairedResidueExtension S w p u n = weightedResidue S w n := by
  rw [pairedResidueExtension_below S w p u n hp hn hS, hα]
  ring

def frozenRefinements (p : ℕ → ℕ) (u : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => 2 * residueFraction 2 n
  | j+1, n => frozenRefinements p u j n -
      u j * frozenRefinements p u j (n / p j)

theorem frozen_zero (p : ℕ → ℕ) (u : ℕ → ℝ) (j : ℕ) :
    frozenRefinements p u j 0 = 0 := by
  induction j with
  | zero => norm_num [frozenRefinements, residueFraction]
  | succ j ih => simp [frozenRefinements, ih]

theorem frozen_two (p : ℕ → ℕ) (u : ℕ → ℝ) (hp : ∀ j, 2 < p j) (j : ℕ) :
    frozenRefinements p u j 2 = 0 := by
  induction j with
  | zero => norm_num [frozenRefinements, residueFraction]
  | succ j ih =>
    simp [frozenRefinements, Nat.div_eq_of_lt (hp j), frozen_zero, ih]

theorem frozen_bounded (p : ℕ → ℕ) (u : ℕ → ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |frozenRefinements p u j n| ≤ C := by
  induction j with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro n
    have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hm with hm | hm <;> norm_num [frozenRefinements, residueFraction, hm]
  | succ j ih =>
    obtain ⟨C, hC, hb⟩ := ih
    refine ⟨C + |u j| * C, by positivity, ?_⟩
    intro n
    calc
      |frozenRefinements p u (j + 1) n| ≤
          |frozenRefinements p u j n| + |u j * frozenRefinements p u j (n/p j)| :=
        by
          simpa only [frozenRefinements, sub_eq_add_neg, abs_neg] using
            abs_add_le (frozenRefinements p u j n)
              (-(u j * frozenRefinements p u j (n / p j)))
      _ ≤ C + |u j| * C := by
        rw [abs_mul]
        exact add_le_add (hb n) (mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _))

theorem frozen_fullError_lower (p : ℕ → ℕ) (u : ℕ → ℝ)
    (hp : ∀ j, 2 < p j) (j : ℕ) :
    1 / (4*zetaTwo) ≤ fullError (frozenRefinements p u j) := by
  obtain ⟨C, _, hb⟩ := frozen_bounded p u j
  have hs := fullError_summable_of_abs_le _ C hb
  have hZ := zetaTwo_pos
  have h := Summable.sum_le_tsum ({1}:Finset ℕ)
    (fun k _ => show 0 ≤ (1-frozenRefinements p u j (k+1)) ^ 2 /
      (zetaTwo*((k+1:ℕ):ℝ) ^ 2) by positivity) hs
  norm_num [fullError, frozen_two p u hp j, mul_comm] at h ⊢
  exact h

theorem frozen_not_tendsto_zero (p : ℕ → ℕ) (u : ℕ → ℝ)
    (hp : ∀ j, 2 < p j) :
    ¬ Tendsto (fun j => fullError (frozenRefinements p u j)) atTop (𝓝 0) := by
  intro ht
  have hZ := zetaTwo_pos
  have hpos : (0:ℝ) < 1/(4*zetaTwo) := by positivity
  obtain ⟨j, hj⟩ := ((tendsto_order.mp ht).2 _ hpos).exists
  exact (not_lt_of_ge (frozen_fullError_lower p u hp j)) hj

/-- All cross terms in the actual downscaled/refinement direction. -/
theorem signed_direction_terms (R B G : QHilbert) (α : ℝ) :
    inner ℝ R (α • G - B) = α * inner ℝ R G - inner ℝ R B ∧
    ‖α • G - B‖ ^ 2 = ‖B‖ ^ 2 - 2*α*inner ℝ B G + α ^ 2*‖G‖ ^ 2 := by
  constructor
  · simp only [inner_sub_right, real_inner_smul_right]
  · simp only [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, real_inner_smul_left]
    rw [real_inner_comm G B]
    ring

/-- The zero direction also satisfies the drop formula, with 0/0 = 0. -/
theorem optimal_energy_total (R A : QHilbert) :
    ‖R - (inner ℝ R A / ‖A‖ ^ 2) • A‖ ^ 2 =
      ‖R‖ ^ 2 - (inner ℝ R A) ^ 2 / ‖A‖ ^ 2 := by
  by_cases h : ‖A‖ ^ 2 = 0
  · simp [h]
  · exact optimal_energy R A h

/-- Telescoping exact greedy drops; no orthogonality between steps is assumed. -/
theorem optimized_telescoping (R A : ℕ → QHilbert)
    (hstep : ∀ j, R (j + 1) = R j -
      (inner ℝ (R j) (A j) / ‖A j‖ ^ 2) • A j) (m : ℕ) :
    ‖R m‖ ^ 2 = ‖R 0‖ ^ 2 -
      ∑ j ∈ Finset.range m, (inner ℝ (R j) (A j)) ^ 2 / ‖A j‖ ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [hstep, optimal_energy_total, ih, Finset.sum_range_succ]
    ring

/-- The standard initial pair after its unique greedy prime-two step. -/
theorem greedy_seed :
    (∀ n, weightedResidue {1, 2} (fun d => if d = 1 then 1 else -2) n =
      2 * residueFraction 2 n) ∧
    reciprocalCoefficient {1, 2} (fun d => if d = 1 then 1 else -2) = 0 := by
  constructor
  · intro n
    simp [weightedResidue, residueFraction, Nat.mod_one]
  · norm_num [reciprocalCoefficient]

/-- The existing exact Euler factor shows zero reciprocal mass is absorbing. -/
theorem zero_reciprocal_preserved (S : Finset ℕ) (w : ℕ → ℝ)
    (p : ℕ) (u : ℝ) (hα : reciprocalCoefficient S w = 0) :
    (∑ d ∈ S, (w d / (d : ℝ) - u*w d / ((d*p:ℕ):ℝ))) = 0 := by
  rw [paired_reciprocalCoefficient, hα]
  ring

/-- The literal full Q error agrees with the existing Hilbert realization. -/
theorem hilbert_fullError (F : QHilbert) :
    ‖qOne - F‖ ^ 2 = fullError (qSequence F) := by
  have he : qSequence (qOne - F) = qOneSequence - qSequence F := by
    exact (qSequenceLinear.map_sub qOne F).trans
      (by rw [show qSequenceLinear qOne = qOneSequence from qSequence_qOne]; rfl)
  rw [qNorm_weighted_sq, (qSequence_square_summable (qOne - F)).tsum_eq_zero_add]
  simp only [qSequence_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
  unfold fullError
  apply tsum_congr
  intro k
  rw [he]
  simp only [Pi.sub_apply]
  simp [qOneSequence, positiveQWeight, div_eq_mul_inv]
  ring

/-- Finite residue coefficients are encoded using the existing actual atoms. -/
theorem sequence_weighted (S : Finset ℕ) (w : ℕ → ℝ) :
    qSequence (-(∑ d ∈ S, w d • qResidue d)) = weightedResidue S w := by
  change qSequenceLinear (-(∑ d ∈ S, w d • qResidue d)) = _
  rw [map_neg, map_sum]
  simp only [map_smul]
  ext n
  simp [weightedResidue, qSequenceLinear, qSequence_qResidue]

/-- The direction has precisely the signed floor-dilation formula in the
published refinement module. -/
theorem sequence_refinement_direction (S : Finset ℕ) (w : ℕ → ℝ)
    (p n : ℕ) (hp : 0 < p) (hS : ∀ d ∈ S, 0 < d) :
    qSequence (∑ d ∈ S, w d • qResidue (d*p)) n =
      -weightedResidue S w (n/p) +
        reciprocalCoefficient S w * residueFraction p n := by
  have he : qSequence (∑ d ∈ S, w d • qResidue (d*p)) n =
      ∑ d ∈ S, w d * residueFraction (d*p) n := by
    change qSequenceLinear (∑ d ∈ S, w d • qResidue (d*p)) n = _
    rw [map_sum]
    simp [qSequenceLinear, qSequence_qResidue]
  rw [he, weighted_refinement_sum S w p n hp hS]

/-- Encoding the published paired update, including coincident conductors. -/
theorem sequence_paired (S : Finset ℕ) (w : ℕ → ℝ) (p : ℕ) (u : ℝ) :
    qSequence (-(∑ d ∈ S, w d • qResidue d) +
      u • (∑ d ∈ S, w d • qResidue (d*p))) =
        pairedResidueExtension S w p u := by
  change qSequenceLinear (-(∑ d ∈ S, w d • qResidue d) +
    u • (∑ d ∈ S, w d • qResidue (d*p))) = _
  rw [map_add, map_neg, map_sum, map_smul, map_sum]
  simp only [map_smul]
  ext n
  simp [qSequenceLinear, qSequence_qResidue, pairedResidueExtension, weightedResidue]

/-- The exact complete squared-error update for the actual finite arithmetic
refinement, without any truncated Gram matrix or omitted tail. -/
theorem paired_fullError_quadratic (S : Finset ℕ) (w : ℕ → ℝ)
    (p : ℕ) (u : ℝ) :
    let R := qOne - (-(∑ d ∈ S, w d • qResidue d))
    let A := ∑ d ∈ S, w d • qResidue (d*p)
    fullError (pairedResidueExtension S w p u) =
      ‖R‖ ^ 2 - 2*u*inner ℝ R A + u ^ 2*‖A‖ ^ 2 := by
  dsimp only
  rw [← sequence_paired, ← hilbert_fullError]
  rw [← sub_sub, energy_quadratic]

end RiemannResearch.RH.QWeightedRefinementEnergy
