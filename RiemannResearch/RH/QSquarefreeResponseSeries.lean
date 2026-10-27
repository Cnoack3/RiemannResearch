import RiemannResearch.RH.QCanonicalInnovation
import RiemannResearch.RH.ZetaTwoParitySignal
import RiemannResearch.RH.QShiftedReciprocalBessel
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.Analysis.ProjectionInnovationSeries
import RiemannResearch.Analysis.InfiniteResponseSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Infinite canonical squarefree response variation
Source: the user's SquarefreeMomentBudgetResearch20261027.md.
Both signed series, all zero innovations, and all complete Q tails are retained.
No regularity sufficient for RH is assumed or discharged here.
-/

noncomputable section
namespace RiemannResearch.RH.QCanonicalInnovation
open ZetaTwoHilbert ZetaTwoOptimizerStage ZetaTwoParitySignal
open QSquarefreeSmoothedProjection QShiftedReciprocal
open RiemannResearch.Analysis.ExhaustiveWalk

theorem stage_one : stage 1 = Submodule.span ℝ ({qResidue 2} : Set QHilbert) := by
  simp [stage, walkSpan, squarefreeAtom, Nat.prime_two.squarefree]

theorem optimizer_one : optimizer 1 = qOdd := by
  change (stage 1).starProjection qOne = qOdd
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [stage_one]
    exact Submodule.smul_mem _ 2 (Submodule.subset_span (by simp))
  · intro y hy
    rw [stage_one] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        have he : y = qResidue 2 := by simpa using hy
        subst y
        have h := qEven_inner_qOdd
        change inner ℝ (qOne - qOdd) ((2 : ℝ) • qResidue 2) = 0 at h
        rw [real_inner_smul_right] at h
        linarith
    | zero => simp
    | add y z hy hz hiy hiz => simp [inner_add_right, hiy, hiz]
    | smul c y hy hiy => simp [real_inner_smul_right, hiy]

theorem residual_one : residual 1 = qEven := by
  simp only [ZetaTwoOptimizerStage.residual, optimizer_one, qEven]

theorem error_one : error 1 = (1 / 4 : ℝ) := by
  rw [error, residual_one, qEven_norm_sq]

theorem error_le_quarter (N : ℕ) (hN : 1 ≤ N) : error N ≤ (1 / 4 : ℝ) := by
  have h := walkError_antitone squarefreeAtom id qOne hN
  change error N ≤ error 1 at h
  rwa [error_one] at h

theorem movingCorrection_zero : movingCorrection 0 = 0 := by
  simp [movingCorrection, stage, walkSpan]

theorem B_even_inner_odd : inner ℝ (B qEven) qOdd = 0 := by
  rw [qInner_weighted]
  calc
    _ = ∑' _n : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro n
      rw [qSequence_B, qSequence_qEven, qSequence_qOdd]
      by_cases hd : 2 ∣ n <;> simp [hd]
    _ = 0 := by simp

theorem movingCorrection_one : movingCorrection 1 = 0 := by
  change (stage 1).starProjection (B (residual 1)) = 0
  rw [residual_one]
  apply (Submodule.starProjection_apply_eq_zero_iff (stage 1)).mpr
  apply (Submodule.mem_orthogonal _ _).mpr
  intro y hy
  rw [stage_one] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      have he : y = qResidue 2 := by simpa using hy
      subst y
      have h := B_even_inner_odd
      change inner ℝ (B qEven) ((2 : ℝ) • qResidue 2) = 0 at h
      rw [real_inner_smul_right, real_inner_comm] at h
      linarith
  | zero => simp
  | add y z hy hz hiy hiz => simp [inner_add_left, hiy, hiz]
  | smul c y hy hiy => simp [real_inner_smul_left, hiy]

theorem increment_le_quarter_B (N : ℕ) :
    ‖movingCorrection (N + 1) - movingCorrection N‖ ^ 2 ≤
      (1 / 4 : ℝ) * ‖B (direction N)‖ ^ 2 := by
  by_cases hN : N = 0
  · subst N
    rw [movingCorrection_zero, show 0 + 1 = 1 from rfl, movingCorrection_one]
    simp only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity
  · exact (movingCorrection_increment_norm_sq_le N).trans
      (mul_le_mul_of_nonneg_right (error_le_quarter N (Nat.one_le_iff_ne_zero.mpr hN))
        (sq_nonneg _))

end RiemannResearch.RH.QCanonicalInnovation



namespace RiemannResearch.RH.QCanonicalInnovation
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal ZetaTwoProbability
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionVariation
open RiemannResearch.Analysis.ProjectionInnovationSeries
open scoped BigOperators

theorem B_direction_finite_budget (s : Finset ℕ) :
    (∑ n ∈ s, ‖B (direction n)‖ ^ 2) ≤ zetaTwo - 1 := by
  classical
  have h := orthonormal_B_norm_sq_sum_le
    (fun i : Active => direction i) active_orthonormal
    (s.subtype (fun n => direction n ≠ 0))
  have he (n : ℕ) :
      (if direction n ≠ 0 then ‖B (direction n)‖ ^ 2 else 0) =
        ‖B (direction n)‖ ^ 2 := by
    by_cases hn : direction n = 0 <;> simp [hn]
  have hs := Finset.sum_subtype_eq_sum_filter
    (s := s) (p := fun n => direction n ≠ 0)
    (fun n : ℕ => ‖B (direction n)‖ ^ 2)
  have hf : (∑ n ∈ s with direction n ≠ 0, ‖B (direction n)‖ ^ 2) ≤ zetaTwo - 1 :=
    hs.symm.trans_le h
  simpa only [Finset.sum_filter, he] using hf

theorem B_direction_sq_summable : Summable (fun n => ‖B (direction n)‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) B_direction_finite_budget

theorem B_direction_tsum_le : (∑' n, ‖B (direction n)‖ ^ 2) ≤ zetaTwo - 1 :=
  Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) B_direction_finite_budget

theorem targetCoefficient_sq_eq_increment (N : ℕ) :
    (targetCoefficient N) ^ 2 = ‖increment squarefreeAtom id qOne N‖ ^ 2 := by
  have he : increment squarefreeAtom id qOne N =
      targetCoefficient N • direction N := by
    change (stage (N + 1)).starProjection qOne - (stage N).starProjection qOne = _
    rw [projection_succ]
    change (stage N).starProjection qOne + targetCoefficient N • direction N -
      (stage N).starProjection qOne = _
    abel
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  by_cases hN : direction N = 0
  · simp [targetCoefficient, hN]
  · rw [direction_norm N hN]
    simp

theorem targetCoefficient_sq_summable : Summable (fun n => (targetCoefficient n) ^ 2) := by
  simpa only [targetCoefficient_sq_eq_increment, Nat.add_zero] using
    increment_energy_summable squarefreeAtom id qOne 0

theorem error_le_one (N : ℕ) : error N ≤ 1 := by
  have hn := RiemannResearch.Analysis.SingleDirectionProjection.residual_norm_le (stage N) qOne
  rw [qOne_norm] at hn
  change ‖qOne - (stage N).starProjection qOne‖ ^ 2 ≤ 1
  nlinarith [norm_nonneg (qOne - (stage N).starProjection qOne)]

theorem responseCoefficient_sq_le_B (N : ℕ) :
    (responseCoefficient N) ^ 2 ≤ ‖B (direction N)‖ ^ 2 := by
  have hs := movingCorrection_increment_norm_sq_le N
  rw [movingCorrection_increment_norm_sq] at hs
  have hp := mul_nonneg (sq_nonneg (targetCoefficient N))
    (sq_nonneg ‖(stage N).starProjection (B (direction N))‖)
  have he := mul_le_mul_of_nonneg_right (error_le_one N)
    (sq_nonneg ‖B (direction N)‖)
  nlinarith

theorem responseCoefficient_sq_summable : Summable (fun n => (responseCoefficient n) ^ 2) :=
  B_direction_sq_summable.of_nonneg_of_le (fun _ => sq_nonneg _) responseCoefficient_sq_le_B

theorem orthogonalTerm_norm_sq (N : ℕ) :
    ‖orthogonalTerm N‖ ^ 2 = (responseCoefficient N) ^ 2 := by
  rw [orthogonalTerm, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  by_cases hN : direction N = 0
  · simp [responseCoefficient, hN]
  · rw [direction_norm N hN]
    simp

theorem orthogonalTerm_summable : Summable orthogonalTerm := by
  let f : ∀ n, innovationSpace squarefreeAtom id n := fun n =>
    ⟨orthogonalTerm n, ⟨
      (stage (n + 1)).smul_mem _ (direction_mem_succ n),
      ((stage n)ᗮ).smul_mem _ (direction_mem_orthogonal n)⟩⟩
  have hf (n : ℕ) : ‖f n‖ ^ 2 = (responseCoefficient n) ^ 2 := by
    rw [Submodule.coe_norm]
    exact orthogonalTerm_norm_sq n
  have hs : Summable (fun n => ‖f n‖ ^ 2) := by
    simpa only [hf] using responseCoefficient_sq_summable
  exact ((innovationSpace_orthogonal squarefreeAtom id).summable_iff_norm_sq_summable f).mpr hs

theorem correctionTerm_norm_le (N : ℕ) :
    ‖correctionTerm N‖ ≤
      ((targetCoefficient N) ^ 2 + ‖B (direction N)‖ ^ 2) / 2 := by
  rw [correctionTerm, norm_smul, Real.norm_eq_abs]
  have hp := Submodule.norm_starProjection_apply_le (stage N) (B (direction N))
  have hmul := mul_le_mul_of_nonneg_left hp (abs_nonneg (targetCoefficient N))
  nlinarith [sq_nonneg (|targetCoefficient N| - ‖B (direction N)‖),
    sq_abs (targetCoefficient N)]

theorem correctionTerm_norm_summable : Summable (fun n => ‖correctionTerm n‖) :=
  ((targetCoefficient_sq_summable.add B_direction_sq_summable).div_const 2).of_nonneg_of_le (fun _ => norm_nonneg _) correctionTerm_norm_le

theorem correctionTerm_summable : Summable correctionTerm :=
  correctionTerm_norm_summable.of_norm

theorem movingCorrection_increment_summable :
    Summable (fun n => QSquarefreeSmoothedProjection.movingCorrection (n + 1) -
      QSquarefreeSmoothedProjection.movingCorrection n) := by
  simpa only [movingCorrection_increment] using
    orthogonalTerm_summable.sub correctionTerm_summable

end RiemannResearch.RH.QCanonicalInnovation

namespace RiemannResearch.RH.QCanonicalInnovation
open ZetaTwoHilbert ZetaTwoOptimizerStage ZetaTwoProbability QShiftedReciprocal
open QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.InfiniteResponseSeries
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.ProjectionInnovationSeries
open Filter
open scoped Topology BigOperators

/-- The complete infinite variation is summable, with the exact requested cap. -/
theorem movingCorrection_variation :
    Summable (fun n => ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) ∧
    (∑' n, ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) ≤
      (zetaTwo - 1) / 4 := by
  simpa only [one_div_mul_eq_div] using
    variation_summable_and_tsum_le
      (fun n => movingCorrection (n + 1) - movingCorrection n)
      (fun n => ‖B (direction n)‖) (1 / 4) (zetaTwo - 1) (by norm_num)
      B_direction_sq_summable B_direction_tsum_le increment_le_quarter_B

/-- The exact two nonnegative energies survive passage to the infinite sum. -/
theorem movingCorrection_variation_exact :
    (∑' n, ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) =
      (∑' n, (responseCoefficient n) ^ 2) +
      ∑' n, (targetCoefficient n) ^ 2 *
        ‖(stage n).starProjection (B (direction n))‖ ^ 2 := by
  have ht : Summable (fun n => (targetCoefficient n) ^ 2 *
      ‖(stage n).starProjection (B (direction n))‖ ^ 2) := by
    apply movingCorrection_variation.1.of_nonneg_of_le
      (fun n => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    intro n
    rw [movingCorrection_increment_norm_sq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  simpa only [movingCorrection_increment_norm_sq] using
    responseCoefficient_sq_summable.tsum_add ht

/-- Every complete tail has the stated unconditional sum. -/
theorem movingCorrection_tail_hasSum (N : ℕ) :
    HasSum (fun j => movingCorrection (j + N + 1) - movingCorrection (j + N))
      (correction - movingCorrection N) :=
  response_tail_hasSum movingCorrection correction movingCorrection_increment_summable
    movingCorrection_tendsto N

theorem movingCorrection_increment_hasSum :
    HasSum (fun n => movingCorrection (n + 1) - movingCorrection n) correction := by
  simpa only [Nat.add_zero, movingCorrection_zero, sub_zero] using movingCorrection_tail_hasSum 0

/-- Bounded arbitrary signs preserve unconditional convergence. -/
theorem signed_movingCorrection_increment_summable (ε : ℕ → ℝ)
    (hε : ∀ n, |ε n| ≤ 1) :
    Summable (fun n => ε n • (movingCorrection (n + 1) - movingCorrection n)) := by
  have hs : Summable (fun n => ‖orthogonalTerm n‖ ^ 2) := by
    simpa only [orthogonalTerm_norm_sq] using responseCoefficient_sq_summable
  have hmem (n : ℕ) : orthogonalTerm n ∈ innovationSpace squarefreeAtom id n :=
    ⟨(stage (n + 1)).smul_mem _ (direction_mem_succ n),
      ((stage n)ᗮ).smul_mem _ (direction_mem_orthogonal n)⟩
  have h := bounded_signed_parts_summable (innovationSpace squarefreeAtom id)
    (innovationSpace_orthogonal squarefreeAtom id) orthogonalTerm correctionTerm hmem hs
    correctionTerm_norm_summable ε hε
  simpa only [movingCorrection_increment] using h.2.2

/-- Tail Hilbert--Schmidt mass: complete physical and canonical-stage sums. -/
def smoothingTail (N : ℕ) : ℝ := ∑' j, ‖B (direction (j + N))‖ ^ 2

theorem B_direction_tail_summable (N : ℕ) :
    Summable (fun j => ‖B (direction (j + N))‖ ^ 2) :=
  B_direction_sq_summable.comp_injective (i := fun j : ℕ => j + N)
    (fun i j h => Nat.add_right_cancel h)

/-- The actual residual energy sharpens every infinite variation tail. -/
theorem movingCorrection_variation_tail_le (N : ℕ) :
    (∑' j, ‖movingCorrection (j + N + 1) - movingCorrection (j + N)‖ ^ 2) ≤
      error N * smoothingTail N := by
  have hr (j : ℕ) : error (j + N) ≤ error N :=
    walkError_antitone squarefreeAtom id qOne (Nat.le_add_left N j)
  have h := variation_summable_and_tsum_le
    (fun j => movingCorrection (j + N + 1) - movingCorrection (j + N))
    (fun j => ‖B (direction (j + N))‖) (error N) (smoothingTail N)
    (sq_nonneg _) (B_direction_tail_summable N) le_rfl
    (fun j => (movingCorrection_increment_norm_sq_le (j + N)).trans
      (mul_le_mul_of_nonneg_right (hr j) (sq_nonneg _)))
  exact h.2

/-- Since the parity response is zero, its strictly positive smoothing mass
can be removed from the global budget. -/
theorem movingCorrection_variation_excluding_parity :
    (∑' n, ‖movingCorrection (n + 1) - movingCorrection n‖ ^ 2) ≤
      (zetaTwo - 1 - ‖B (direction 0)‖ ^ 2) / 4 := by
  have he := movingCorrection_variation.1.tsum_eq_zero_add
  have hd := B_direction_sq_summable.tsum_eq_zero_add
  have ht := movingCorrection_variation_tail_le 1
  rw [error_one] at ht
  simp only [Nat.zero_add, movingCorrection_one, movingCorrection_zero,
    sub_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] at he
  change (∑' j, ‖movingCorrection (j + 1 + 1) - movingCorrection (j + 1)‖ ^ 2) ≤
    1 / 4 * (∑' j, ‖B (direction (j + 1))‖ ^ 2) at ht
  rw [he]
  nlinarith [B_direction_tsum_le]

end RiemannResearch.RH.QCanonicalInnovation



namespace RiemannResearch.RH.QCanonicalInnovation
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal
open QSquarefreeSmoothedProjection
open RiemannResearch.Analysis.InfiniteResponseSeries

/-- Applying the actual Hilbert--Schmidt multiplier once more makes the
orthogonal response series absolutely summable in the complete Q norm. -/
theorem B_orthogonalTerm_norm_summable :
    Summable (fun n => ‖B (orthogonalTerm n)‖) := by
  apply correction_norm_summable responseCoefficient
    (fun n => ‖B (direction n)‖) (fun n => B (orthogonalTerm n))
    responseCoefficient_sq_summable B_direction_sq_summable
  intro n
  simp only [orthogonalTerm, map_smul, norm_smul, Real.norm_eq_abs, le_refl]

/-- The already absolutely summable correction remains so after B. -/
theorem B_correctionTerm_norm_summable :
    Summable (fun n => ‖B (correctionTerm n)‖) :=
  correctionTerm_norm_summable.of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => B_norm_le (correctionTerm n))

/-- The original signed increments are unconditionally summable; their
additional B smoothing is absolutely summable in Hilbert norm. -/
theorem B_movingCorrection_increment_norm_summable :
    Summable (fun n =>
      ‖B (movingCorrection (n + 1) - movingCorrection n)‖) := by
  apply (B_orthogonalTerm_norm_summable.add B_correctionTerm_norm_summable).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [movingCorrection_increment, map_sub]
  exact norm_sub_le _ _

/-- Unconditional Hilbert summability gives absolute convergence at each
physical site, using the complete Q evaluation map. -/
theorem movingCorrection_increment_physical_abs_summable (k : ℕ) :
    Summable (fun n =>
      |qSequence (movingCorrection (n + 1) - movingCorrection n) k|) := by
  have h := movingCorrection_increment_summable.map (qEvalCLM k) (qEvalCLM k).continuous
  simpa only [Function.comp_def, qEvalCLM_apply] using h.abs

end RiemannResearch.RH.QCanonicalInnovation
