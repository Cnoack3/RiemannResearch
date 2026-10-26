/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.TriangularWeightedBessel
import RiemannResearch.RH.QSquarefreeSmoothedProjection
import RiemannResearch.Analysis.ResidualizedProjectionKernel
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.RH.QFiniteSupportDualCriterion
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Weighted Bessel estimates after head orthogonalization

Source: elementary orthogonal-family and finite-layer summation developed
in continuation of the user's odd-radical projection handoff, 25 October 2026.

Onsets are zero-based Lean coordinates. Thus onset j has first possible
positive physical site j+1, and the reciprocal multiplier weight is j+2.
The family may be incomplete; zero vectors are allowed. No finite-tail
truncation occurs in the energy estimate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QTriangularWeightedBessel
open ZetaTwoHilbert QShiftedReciprocal QAnnihilatorTailEscape
open QFiniteSupportDualCriterion
open RiemannResearch.Analysis.TriangularWeightedBessel

def onsetIncrement (k : ℕ) : ℝ := if k = 0 then 4 else 2 * (k : ℝ) + 3

theorem onsetIncrement_nonneg (k : ℕ) : 0 ≤ onsetIncrement k := by
  unfold onsetIncrement
  split_ifs <;> positivity

theorem onsetIncrement_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), onsetIncrement k) = ((n : ℝ) + 2) ^ 2 := by
  induction n with
  | zero => norm_num [onsetIncrement]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, onsetIncrement,
      if_neg (by omega : n + 1 ≠ 0)]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem onsetIncrement_selected_eq (M n : ℕ) (hn : n < M) :
    (∑ k : Fin M, if (k : ℕ) ≤ n then onsetIncrement k else 0) =
      ((n : ℝ) + 2) ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range
    (f := fun k : ℕ => if k ≤ n then onsetIncrement k else 0) (n := M)]
  rw [← Finset.sum_filter]
  have he : (Finset.range M).filter (fun k => k ≤ n) = Finset.range (n + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he, onsetIncrement_sum]

theorem onsetIncrement_selected_le (M n : ℕ) :
    (∑ k : Fin M, if (k : ℕ) ≤ n then onsetIncrement k else 0) ≤
      ((n : ℝ) + 2) ^ 2 := by
  by_cases hn : n < M
  · exact (onsetIncrement_selected_eq M n hn).le
  · cases M with
    | zero => simpa using sq_nonneg ((n : ℝ) + 2)
    | succ M =>
      have he : (∑ k : Fin (M + 1), if (k : ℕ) ≤ n then onsetIncrement k else 0) =
          ∑ k : Fin (M + 1), onsetIncrement k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [if_pos (by have := k.isLt; omega)]
      rw [he, Fin.sum_univ_eq_sum_range, onsetIncrement_sum]
      have hMn : (M : ℝ) ≤ n := by exact_mod_cast (show M ≤ n by omega)
      nlinarith [Nat.cast_nonneg (α := ℝ) M]

theorem tail_pairing_of_onset (f u : QHilbert) (k : ℕ)
    (hu : ∀ n : ℕ, n < k → u n = 0) :
    inner ℝ (tail k f) u = inner ℝ f u := by
  have hz : inner ℝ (finiteHead k f) u = 0 := by
    rw [real_inner_comm, inner_finiteHead_eq_sum]
    apply Finset.sum_eq_zero
    intro n hn
    rw [hu n (Finset.mem_range.mp hn), mul_zero]
  rw [tail, inner_sub_left, hz, sub_zero]

/-- The complete weighted sum of reciprocal-multiplier tail energies is at
most the input norm. The finite layer count does not truncate any tail. -/
theorem reciprocal_layer_energy_le (f : QHilbert) (M : ℕ) :
    (∑ k : Fin M, onsetIncrement k * ‖tail k (B f)‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  have happ (k : Fin M) (n : ℕ) :
      tail k (B f) n = if (k : ℕ) ≤ n then f n / ((n : ℝ) + 2) else 0 := by
    change B f n - finiteHead k (B f) n = _
    by_cases hkn : (k : ℕ) ≤ n
    · rw [finiteHead_apply_eq_zero _ _ _ hkn, sub_zero, B_apply, if_pos hkn]
    · rw [finiteHead_apply_of_lt _ _ _ (by omega), sub_self, if_neg hkn]
  have hpoint (n : ℕ) :
      (∑ k : Fin M, onsetIncrement k * (tail k (B f) n) ^ 2) ≤ (f n) ^ 2 := by
    have he : (∑ k : Fin M, onsetIncrement k * (tail k (B f) n) ^ 2) =
        (∑ k : Fin M, if (k : ℕ) ≤ n then onsetIncrement k else 0) *
          (f n / ((n : ℝ) + 2)) ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [happ]
      by_cases hkn : (k : ℕ) ≤ n <;> simp [hkn]
    rw [he]
    calc
      _ ≤ ((n : ℝ) + 2) ^ 2 * (f n / ((n : ℝ) + 2)) ^ 2 :=
        mul_le_mul_of_nonneg_right (onsetIncrement_selected_le M n) (sq_nonneg _)
      _ = (f n) ^ 2 := by
        have hd : (n : ℝ) + 2 ≠ 0 := ne_of_gt (by positivity)
        field_simp
  have hnonneg (n : ℕ) :
      0 ≤ ∑ k : Fin M, onsetIncrement k * (tail k (B f) n) ^ 2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (onsetIncrement_nonneg k) (sq_nonneg _))
  have hs : Summable (fun n : ℕ =>
      ∑ k : Fin M, onsetIncrement k * (tail k (B f) n) ^ 2) :=
    Summable.of_nonneg_of_le hnonneg hpoint (qCoordinate_square_summable f)
  calc
    _ = ∑ k : Fin M, ∑' n : ℕ, onsetIncrement k * (tail k (B f) n) ^ 2 := by
      simp_rw [qNorm_sq, tsum_mul_left]
    _ = ∑' n : ℕ, ∑ k : Fin M, onsetIncrement k * (tail k (B f) n) ^ 2 := by
      exact (Summable.tsum_finsetSum (s := Finset.univ) (fun (k : Fin M) _ =>
        (qCoordinate_square_summable (tail k (B f))).mul_left (onsetIncrement k))).symm
    _ ≤ ∑' n : ℕ, (f n) ^ 2 :=
      Summable.tsum_le_tsum hpoint hs (qCoordinate_square_summable f)
    _ = ‖f‖ ^ 2 := (qNorm_sq f).symm

/-- Exact constant-one weighted Bessel bound for a finite orthogonal family
with specified coordinate onsets. It applies after Gram--Schmidt, not merely
to raw residue forcing before the normal solve. -/
theorem reciprocal_onset_bessel {ι : Type*} [Fintype ι]
    (f : QHilbert) (M : ℕ) (u : ι → QHilbert) (onset : ι → Fin M)
    (ho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (hn : ∀ i, ‖u i‖ ^ 2 ≤ 1)
    (hu : ∀ i n, n < (onset i : ℕ) → u i n = 0) :
    (∑ i, (((onset i : ℕ) : ℝ) + 2) ^ 2 *
      (inner ℝ (B f) (u i)) ^ 2) ≤ ‖f‖ ^ 2 := by
  classical
  have h := layered_bessel (B f) u (fun k : Fin M => tail k (B f))
    (fun k i => (k : ℕ) ≤ (onset i : ℕ)) (fun k => onsetIncrement k)
    (fun k => onsetIncrement_nonneg k) ho hn (by
      intro k i hki
      apply tail_pairing_of_onset
      intro n hn
      exact hu i n (lt_of_lt_of_le hn hki))
  have he (i : ι) :
      (∑ k : Fin M, if (k : ℕ) ≤ (onset i : ℕ) then onsetIncrement k else 0) =
        (((onset i : ℕ) : ℝ) + 2) ^ 2 :=
    onsetIncrement_selected_eq M (onset i) (onset i).isLt
  simp only [he] at h
  exact h.trans (reciprocal_layer_energy_le f M)

/-- The weighted estimate for actual moving-correction coordinates, after
orthogonalization within the squarefree stage. -/
theorem movingCorrection_onset_bessel {ι : Type*} [Fintype ι]
    (N M : ℕ) (u : ι → QHilbert) (onset : ι → Fin M)
    (ho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (hn : ∀ i, ‖u i‖ ^ 2 ≤ 1)
    (hu : ∀ i n, n < (onset i : ℕ) → u i n = 0)
    (hv : ∀ i, u i ∈ ZetaTwoOptimizerStage.stage N) :
    (∑ i, (((onset i : ℕ) : ℝ) + 2) ^ 2 *
      (inner ℝ (QSquarefreeSmoothedProjection.movingCorrection N) (u i)) ^ 2) ≤
        ZetaTwoOptimizerStage.error N := by
  have he (i : ι) :
      inner ℝ (QSquarefreeSmoothedProjection.movingCorrection N) (u i) =
        inner ℝ (B (ZetaTwoOptimizerStage.residual N)) (u i) := by
    change inner ℝ ((ZetaTwoOptimizerStage.stage N).starProjection
      (B (ZetaTwoOptimizerStage.residual N))) (u i) = _
    rw [RiemannResearch.Analysis.ResidualizedProjectionKernel.projection_inner,
      Submodule.starProjection_eq_self_iff.mpr (hv i)]
  simp_rw [he]
  exact reciprocal_onset_bessel (ZetaTwoOptimizerStage.residual N) M u onset ho hn hu

/-- Tail truncation leaves the smoothed pairing unchanged against a vector
whose onset is beyond the cutoff. -/
theorem inner_B_tail_of_onset (f u : QHilbert) (H : ℕ)
    (hu : ∀ n : ℕ, n < H → u n = 0) :
    inner ℝ (B (tail H f)) u = inner ℝ (B f) u := by
  rw [B_symmetric, B_symmetric]
  apply tail_pairing_of_onset
  intro n hn
  rw [B_apply, hu n hn, zero_div]

/-- Weighted high-onset coordinates are controlled by the input's complete tail. -/
theorem reciprocal_onset_tail_bessel {ι : Type*} [Fintype ι]
    (f : QHilbert) (H M : ℕ) (u : ι → QHilbert) (onset : ι → Fin M)
    (ho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (hn : ∀ i, ‖u i‖ ^ 2 ≤ 1)
    (hu : ∀ i n, n < (onset i : ℕ) → u i n = 0)
    (hH : ∀ i, H ≤ (onset i : ℕ)) :
    (∑ i, (((onset i : ℕ) : ℝ) + 2) ^ 2 *
      (inner ℝ (B f) (u i)) ^ 2) ≤ ‖tail H f‖ ^ 2 := by
  have he (i : ι) : inner ℝ (B (tail H f)) (u i) = inner ℝ (B f) (u i) :=
    inner_B_tail_of_onset f (u i) H (fun n hn => hu i n (lt_of_lt_of_le hn (hH i)))
  simpa only [he] using reciprocal_onset_bessel (tail H f) M u onset ho hn hu

/-- The sharper complete-tail estimate for actual legal-stage response coordinates. -/
theorem movingCorrection_onset_tail_bessel {ι : Type*} [Fintype ι]
    (N H M : ℕ) (u : ι → QHilbert) (onset : ι → Fin M)
    (ho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (hn : ∀ i, ‖u i‖ ^ 2 ≤ 1)
    (hu : ∀ i n, n < (onset i : ℕ) → u i n = 0)
    (hH : ∀ i, H ≤ (onset i : ℕ))
    (hv : ∀ i, u i ∈ ZetaTwoOptimizerStage.stage N) :
    (∑ i, (((onset i : ℕ) : ℝ) + 2) ^ 2 *
      (inner ℝ (QSquarefreeSmoothedProjection.movingCorrection N) (u i)) ^ 2) ≤
        ‖tail H (ZetaTwoOptimizerStage.residual N)‖ ^ 2 := by
  have he (i : ι) :
      inner ℝ (QSquarefreeSmoothedProjection.movingCorrection N) (u i) =
        inner ℝ (B (ZetaTwoOptimizerStage.residual N)) (u i) := by
    change inner ℝ ((ZetaTwoOptimizerStage.stage N).starProjection
      (B (ZetaTwoOptimizerStage.residual N))) (u i) = _
    rw [RiemannResearch.Analysis.ResidualizedProjectionKernel.projection_inner,
      Submodule.starProjection_eq_self_iff.mpr (hv i)]
  simp_rw [he]
  exact reciprocal_onset_tail_bessel (ZetaTwoOptimizerStage.residual N) H M u onset ho hn hu hH

/-- Complete-tail residual-direction energy; zero tails contribute zero. -/
def residualLayerGain (f : QHilbert) (k : ℕ) : ℝ :=
  (inner ℝ (tail k (B f)) (tail k f)) ^ 2 / ‖tail k f‖ ^ 2

theorem residualLayerGain_nonneg (f : QHilbert) (k : ℕ) :
    0 ≤ residualLayerGain f k := by
  unfold residualLayerGain
  positivity

/-- Residual orthogonality supplies a nonnegative subtraction in every onset layer. -/
theorem reciprocal_onset_screened_bessel {ι : Type*} [Fintype ι]
    (f : QHilbert) (M : ℕ) (u : ι → QHilbert) (onset : ι → Fin M)
    (ho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (hn : ∀ i, ‖u i‖ ^ 2 ≤ 1)
    (hu : ∀ i n, n < (onset i : ℕ) → u i n = 0)
    (hf : ∀ i, inner ℝ f (u i) = 0) :
    (∑ i, (((onset i : ℕ) : ℝ) + 2) ^ 2 *
      (inner ℝ (B f) (u i)) ^ 2) +
      (∑ k : Fin M, onsetIncrement k * residualLayerGain f k) ≤ ‖f‖ ^ 2 := by
  classical
  have h := layered_screened_bessel (B f) u
    (fun k : Fin M => tail k (B f)) (fun k : Fin M => tail k f)
    (fun k i => (k : ℕ) ≤ (onset i : ℕ)) (fun k => onsetIncrement k)
    (fun k => onsetIncrement_nonneg k) ho hn
    (by
      intro k i hki
      exact tail_pairing_of_onset (B f) (u i) k
        (fun n hn => hu i n (lt_of_lt_of_le hn hki)))
    (by
      intro k i hki
      rw [tail_pairing_of_onset f (u i) k
        (fun n hn => hu i n (lt_of_lt_of_le hn hki)), hf i])
  have he (i : ι) :
      (∑ k : Fin M, if (k : ℕ) ≤ (onset i : ℕ) then onsetIncrement k else 0) =
        (((onset i : ℕ) : ℝ) + 2) ^ 2 :=
    onsetIncrement_selected_eq M (onset i) (onset i).isLt
  simp only [he] at h
  have hg : (∑ k : Fin M, onsetIncrement k *
      (inner ℝ (tail k (B f)) (tail k f)) ^ 2 / ‖tail k f‖ ^ 2) =
      ∑ k : Fin M, onsetIncrement k * residualLayerGain f k := by
    apply Finset.sum_congr rfl
    intro k _
    unfold residualLayerGain
    ring
  rw [hg] at h
  exact h.trans (reciprocal_layer_energy_le f M)

/-- The refined weighted energy bound for the actual squarefree response. -/
theorem movingCorrection_onset_screened_bessel {ι : Type*} [Fintype ι]
    (N M : ℕ) (u : ι → QHilbert) (onset : ι → Fin M)
    (ho : ∀ i j, i ≠ j → inner ℝ (u i) (u j) = 0)
    (hn : ∀ i, ‖u i‖ ^ 2 ≤ 1)
    (hu : ∀ i n, n < (onset i : ℕ) → u i n = 0)
    (hv : ∀ i, u i ∈ ZetaTwoOptimizerStage.stage N) :
    (∑ i, (((onset i : ℕ) : ℝ) + 2) ^ 2 *
      (inner ℝ (QSquarefreeSmoothedProjection.movingCorrection N) (u i)) ^ 2) +
      (∑ k : Fin M, onsetIncrement k *
        residualLayerGain (ZetaTwoOptimizerStage.residual N) k) ≤
        ZetaTwoOptimizerStage.error N := by
  have he (i : ι) :
      inner ℝ (QSquarefreeSmoothedProjection.movingCorrection N) (u i) =
        inner ℝ (B (ZetaTwoOptimizerStage.residual N)) (u i) := by
    change inner ℝ ((ZetaTwoOptimizerStage.stage N).starProjection
      (B (ZetaTwoOptimizerStage.residual N))) (u i) = _
    rw [RiemannResearch.Analysis.ResidualizedProjectionKernel.projection_inner,
      Submodule.starProjection_eq_self_iff.mpr (hv i)]
  simp_rw [he]
  apply reciprocal_onset_screened_bessel _ M u onset ho hn hu
  intro i
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal (hv i)
    (ZetaTwoOptimizerStage.residual_mem_orthogonal N)

end RiemannResearch.RH.QTriangularWeightedBessel
